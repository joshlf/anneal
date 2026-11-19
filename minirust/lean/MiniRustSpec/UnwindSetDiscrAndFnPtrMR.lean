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
   multi-frame big-step (`1` Trusted step) vs. `k + 1` MiniRust `ResumeUnwind`
   steps (across all four terminal outcomes), `.unreachable` UB, `.terminate`
   abort, and explicit root-frame divergence
   `unwindResume_root_panic_vs_ub_divergence` (Trusted `.halted .panic` vs.
   MiniRust `BottomOfStack` UB), plus composed
   `StartUnwind -> ResumeUnwind^k -> StopUnwind` on `Mach` and `MachTB`.
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
   projection across reads, writes, deref chains, and `Rvalue.len`
   (`splitLastDeref?`), matched by MiniRust zero-offset field-0 wrapper
   projection and `Transmute` on `Mach` and `MachTB`, plus `translatePlace =
   none` and dead-local UB.
10. **`C10` (`AggregateKind.closure`)**: 0-capture ZST closures and
    multi-capture scalar/pointer closures relating Trusted `.aggregate 0 vals`
    to MiniRust `ValueExpr.Tuple` on `Mach` and `MachTB`, including
    left-to-right operand evaluation and dead/uninit upvar UB propagation.
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
@[reducible] def mkSt (k : MirAst.StatementKind) : MirAst.Statement := { kind := k, span := dummySpan }
@[reducible] def mkTm (k : MirAst.TerminatorKind) : MirAst.Terminator := { kind := k, span := dummySpan }
@[reducible] def mkBb (stmts : List MirAst.Statement) (term : MirAst.TerminatorKind)
    (isCleanup : Bool := false) : MirAst.BasicBlockData :=
  { statements := stmts, terminator := mkTm term, isCleanup }
@[reducible] def u8MirTy : MirAst.Ty := { kind := .uint .u8, layoutIdx := 0 }
@[reducible] def u32MirTy : MirAst.Ty := { kind := .uint .u32, layoutIdx := 0 }
@[reducible] def i32MirTy : MirAst.Ty := { kind := .int .i32, layoutIdx := 0 }
@[reducible] def u64MirTy : MirAst.Ty := { kind := .uint .u64, layoutIdx := 0 }
@[reducible] def usizeMirTy : MirAst.Ty := { kind := .uint .usize, layoutIdx := 0 }
@[reducible] def boolMirTy : MirAst.Ty := { kind := .bool, layoutIdx := 0 }
@[reducible] def unitMirTy : MirAst.Ty := { kind := .tuple [], layoutIdx := 0 }
@[reducible] def rawConstUnitMirTy : MirAst.Ty := { kind := .rawPtr .not (.tuple []), layoutIdx := 0 }
@[reducible] def rawConstU32MirTy : MirAst.Ty := { kind := .rawPtr .not (.uint .u32), layoutIdx := 0 }
@[reducible] def rawMutU32MirTy : MirAst.Ty := { kind := .rawPtr .mut (.uint .u32), layoutIdx := 0 }
@[reducible] def refMutU32MirTy : MirAst.Ty := { kind := .ref .mut (.uint .u32), layoutIdx := 0 }
@[reducible] def arr2U32MirTy : MirAst.Ty := { kind := .array (.uint .u32) 2, layoutIdx := 0 }
@[reducible] def rawMutArr2U32MirTy : MirAst.Ty := { kind := .rawPtr .mut (.array (.uint .u32) 2), layoutIdx := 0 }
@[reducible] def rawConstArr2U32MirTy : MirAst.Ty := { kind := .rawPtr .not (.array (.uint .u32) 2), layoutIdx := 0 }
@[reducible] def rawMutSliceU32MirTy : MirAst.Ty := { kind := .rawPtr .mut (.slice (.uint .u32)), layoutIdx := 0 }
@[reducible] def rawConstSliceU32MirTy : MirAst.Ty := { kind := .rawPtr .not (.slice (.uint .u32)), layoutIdx := 0 }
@[reducible] def rawMutDynMirTy : MirAst.Ty := { kind := .rawPtr .mut (.dynamic "ep2::Tr"), layoutIdx := 0 }
@[reducible] def rawConstDynMirTy : MirAst.Ty := { kind := .rawPtr .not (.dynamic "ep2::Tr"), layoutIdx := 0 }
@[reducible] def fnPtrSafeU32MirTy : MirAst.Ty := { kind := .fnPtr [.uint .u32] (.uint .u32) .safe .rust, layoutIdx := 0 }
@[reducible] def fnPtrUnsafeU32MirTy : MirAst.Ty := { kind := .fnPtr [.uint .u32] (.uint .u32) .unsafe_ .rust, layoutIdx := 0 }
@[reducible] def fnPtrIntrinsicU32MirTy : MirAst.Ty :=
  { kind := .fnPtr [.uint .u32] (.uint .u32) .safe .rustIntrinsic, layoutIdx := 0 }
@[reducible] def fnDefU32MirTy (dp : String) : MirAst.Ty := { kind := .fnDef dp [], layoutIdx := 0 }
@[reducible] def closureZstMirTy (dp : String) : MirAst.Ty := { kind := .closure dp [], layoutIdx := 0 }
@[reducible] def closureCapMirTy (dp : String) : MirAst.Ty :=
  { kind := .closure dp [.uint .u32, .rawPtr .not (.uint .u32)], layoutIdx := 0 }
@[reducible] def mkDecl (ty : MirAst.Ty) : MirAst.LocalDecl := { mutability := .mut, ty, debugName := none }
@[reducible] def locPlace (i : Nat) (proj : List MirAst.ProjectionElem := []) : MirAst.Place := { local_ := i, projection := proj }
@[reducible] def constU8 (n : Nat) : MirAst.Operand := .constant { ty := u8MirTy, val := .scalar (.int ⟨n, 1⟩) }
@[reducible] def constU32 (n : Nat) : MirAst.Operand := .constant { ty := u32MirTy, val := .scalar (.int ⟨n, 4⟩) }
@[reducible] def constZst (ty : MirAst.Ty) : MirAst.Operand := .constant { ty, val := .zeroSized }
@[reducible] def u8MrTy : Gen.Type := .Int ⟨.Unsigned, ⟨1⟩⟩
@[reducible] def u32MrTy : Gen.Type := .Int u32
@[reducible] def i32MrTy : Gen.Type := .Int ⟨.Signed, ⟨4⟩⟩
@[reducible] def u64MrTy : Gen.Type := .Int ⟨.Unsigned, ⟨8⟩⟩
@[reducible] def usizeMrTy : Gen.Type := .Int IntType.usize_ty
@[reducible] def wideSlicePtrMrTy : Gen.Type := .Ptr (.Raw .ElementCount)
@[reducible] def traitNameOf (idx : Nat) : Gen.TraitName := ⟨⟨idx⟩⟩
@[reducible] def wideDynPtrMrTy (idx : Nat := 0) : Gen.Type := .Ptr (.Raw (.VTablePointer (traitNameOf idx)))
/-- Dummy non-null return-value pointer placeholder for frames whose caller
ignores the return place during unwind tests. -/
@[reducible] def dummyRetPtr : Ptr := { addr := 1, provenance := none }
/-- Build a minimal `CapturedMir` body in `Runtime(PostCleanup)` phase. -/
def mkMirBody (defPath : String) (decls : List MirAst.LocalDecl) (argCount : Nat)
    (blocks : List MirAst.BasicBlockData) (layouts : LayoutTable := emptyLayoutTable) :
    MirAst.CapturedMir :=
  { defPath, phase := .runtimePostCleanup, role := .subject, argCount, localDecls := decls,
    basicBlocks := blocks, layouts, allocations := [],
    fnAbi := { args := [], ret := { layout := i8Layout, mode := .direct },
               conv := .rust, canUnwind := true } }
/-- Build a MiniRust `Gen.Function` with `minimize`'s default
`implicit_writes := true`. -/
def mkMrFn (locals : List (Gen.LocalName × Gen.Type)) (args : List Gen.LocalName)
    (ret : Gen.LocalName) (blocks : List (Gen.BbName × Gen.BasicBlock)) (start : Gen.BbName := bbName 0) : Gen.Function :=
  { locals := ⟨locals⟩, args, ret, calling_convention := .Rust, blocks := ⟨blocks⟩, start, implicit_writes := true }
/-- Build a minimal `Gen.Program` from an association list of functions. -/
def mkMrProg (fns : List (Gen.FnName × Gen.Function)) (start : Gen.FnName := fnName 0) :
    Gen.Program := { functions := ⟨fns⟩, start, globals := ⟨[]⟩, traits := ⟨[]⟩, vtables := ⟨[]⟩ }
/-- Build a single-thread `BasicMemory` MiniRust machine (`Mach`). -/
def mkMrMach (prog : Gen.Program) (allocs : List Gen.Allocation) (stack : List Frame)
    (fnPtrs : List (Gen.FnName × Ptr) := []) (globalPtrs : List (Gen.GlobalName × Ptr) := [])
    (unwindPayloads : List Ptr := []) : Mach :=
  { prog, mem := { memory := { allocations := allocs, _phantom := {} }, accesses := [] },
    intptrcast := ⟨⟨[]⟩⟩, threads := [{ stack, state := .Enabled, unwind_payloads := unwindPayloads }],
    active_thread := 0, synchronized_threads := ⟨[]⟩, locks := [],
    global_ptrs := ⟨globalPtrs⟩, fn_ptrs := ⟨fnPtrs⟩, vtable_ptrs := ⟨[]⟩, stdout := ⟨[]⟩, stderr := ⟨[]⟩ }
/-- Build a `BasicMemory` stack allocation at `addr` with bytes `data`. -/
def mkStackAlloc (addr : Int) (data : List Byte) (align : Nat := 8) : Gen.Allocation :=
  { addr, data, align := ⟨align⟩, kind := .Stack, live := true, extra := () }
/-- Build a `BasicMemory` function allocation at `addr` (size 0, align 1). -/
def mkFnAlloc (addr : Int) : Gen.Allocation := { addr, data := [], align := ⟨1⟩, kind := .Function, live := true, extra := () }
/-- Build a root `BasicMemory` `Frame` (`BottomOfStack`). -/
def mkRootFrame (fn : Gen.Function) (locs : List (Gen.LocalName × Ptr))
    (nextBb : Gen.BbName := bbName 0) (nextStmt : Int := 0) : Frame :=
  { func := fn, locals := ⟨locs⟩, stack_pop_action := .BottomOfStack, next_block := nextBb, next_stmt := nextStmt, extra := () }
/-- Extract the return value of a clean event-free `runA` execution. -/
def runAVal (body : CapturedMir) (fuel : Nat) (s : MachineState) : Option MirSemantics.Value :=
  match runA body fuel s with | some ([], .normal (v, _)) => some v | _ => none
/-- Decidable UB-message projection for `Interp α`. -/
def interpUbMsg {α : Type} : Interp α → Option String
  | .error (.ub msg) => some msg | _ => none
/-- Decidable `.abort` check for `Interp α`. -/
def interpIsAbort {α : Type} : Interp α → Bool
  | .error .abort => true | _ => false
theorem eq_error_ub_of_interpUbMsg {α : Type} {r : Interp α} {msg : String}
    (h : interpUbMsg r = some msg) : r = .error (.ub msg) := by
  cases r with
  | ok _ => simp [interpUbMsg] at h
  | error e => cases e <;> simp [interpUbMsg] at h; subst h; rfl
theorem eq_error_abort_of_interpIsAbort {α : Type} {r : Interp α} (h : interpIsAbort r = true) : r = .error .abort := by
  cases r with
  | ok _ => simp [interpIsAbort] at h
  | error e => cases e <;> simp [interpIsAbort] at h; rfl
theorem ok_of_map_toOption {α β : Type} {r : Interp α} {f : α → β} {b : β}
    (h : r.toOption.map f = some b) : ∃ a, r = .ok a ∧ f a = b := by
  cases r with
  | error _ => simp [Except.toOption] at h
  | ok a => simp [Except.toOption] at h; exact ⟨a, rfl, h⟩
theorem ok_stepTB_wfLive {β : Type} {m : Mach} {f : MachTB → β} {b : β}
    (h : (Interp.stepTB (liftMachToTB m)).toOption.map f = some b) :
    ∃ m', Interp.stepTB (liftMachToTB m) = .ok m' ∧ MachTB.wfLive m' ∧ f m' = b := by
  obtain ⟨m', hm', hOut⟩ := ok_of_map_toOption h
  exact ⟨m', hm', stepTB_wfLive (liftMachToTB_wfLive _) hm', hOut⟩
theorem ok_stepsTB_wfLive {β : Type} {n : Nat} {m : Mach} {f : MachTB → β} {b : β}
    (h : (Interp.stepsTB n (liftMachToTB m)).toOption.map f = some b) :
    ∃ m', Interp.stepsTB n (liftMachToTB m) = .ok m' ∧ MachTB.wfLive m' ∧ f m' = b := by
  obtain ⟨m', hm', hOut⟩ := ok_of_map_toOption h
  exact ⟨m', hm', liftMachToTB_stepsTB_wfLive hm', hOut⟩
theorem listSet_of_listIndex {T : Type} {xs : List T} {i : Int} {y : T} {w1 : String}
    (x : T) (w2 : String) (h : listIndex xs i w1 = .ok y) :
    listSet xs i x w2 = .ok (xs.set i.toNat x) ∧ ∀ w3, listIndex (xs.set i.toNat x) i w3 = .ok x := by
  unfold listIndex at h
  split at h
  · rename_i h0
    cases hGet : xs[i.toNat]? with
    | none => simp [hGet, specPanic] at h
    | some v =>
      have hLt : i.toNat < xs.length := (List.getElem?_eq_some_iff.mp hGet).1
      refine ⟨by unfold listSet; simp [h0, hLt, pure, Except.pure], fun w3 => ?_⟩
      unfold listIndex; simp [h0, List.getElem?_set_self hLt, pure, Except.pure]
  · simp [specPanic] at h
theorem getLast?_dropLast_snoc {α : Type} : ∀ (ps : List α) (x : α), (ps ++ [x]).getLast? = some x ∧ (ps ++ [x]).dropLast = ps
  | [], x => ⟨rfl, rfl⟩
  | a :: rest, x => by
    obtain ⟨h1, h2⟩ := getLast?_dropLast_snoc rest x
    cases rest with
    | nil => exact ⟨rfl, rfl⟩
    | cons b rs => exact ⟨h1, congrArg (a :: ·) h2⟩
theorem get?_length_eq_none {α : Type} : ∀ (xs : List α), get? xs (length xs) = none
  | [] => rfl
  | _ :: rest => get?_length_eq_none rest
private theorem size_ne_self_ite_local {α : Type} (s : LibSpecr.Size) (a b : α) : (if s ≠ s then a else b) = b := by simp
/-- Polymorphic helper: `evalPlaceM` on `unitPlace` succeeds on any `Machine
M`, returning the aligned pointer at address `1` with `unitType`. -/
theorem evalPlaceM_unitPlace {M : Type} [Gen.Memory M] [MemoryOps M] (m : Machine M) : evalPlaceM m unitPlace =
      .ok (({ ptr := ThinPointer.widen { addr := 1, provenance := none } none, aligned := true }, Interp.unitType), m) := rfl
/-- Polymorphic helper (`Classical.choice`-free): `encodePtrBytesM` data
round-trip. -/
theorem encodePtrBytesM_data {M : Type} [Gen.Memory M] (prov : Option (Gen.Memory.Provenance M)) (i : Nat) (data : List UInt8) :
    (encodePtrBytesM (M := M) prov i data).mapM AbstractByte.dataM = some data := by
  induction data generalizing i with
  | nil => rfl
  | cons b rest ih => simp [encodePtrBytesM, AbstractByte.dataM, ih]
/-- Polymorphic helper (`Classical.choice`-free): `decodePtrProvenanceM`
recovers consistent provenance fragments across `encodePtrBytesM`. -/
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
theorem firstProvenanceM_encode {M : Type} [Gen.Memory M] (prov : Option (Gen.Memory.Provenance M)) (b : UInt8) (rest : List UInt8) :
    firstProvenanceM (M := M) (encodePtrBytesM (M := M) prov 0 (b :: rest)) = prov := by
  cases prov <;> simp [encodePtrBytesM, firstProvenanceM, AbstractByte.provenance_fragM]
/-- Polymorphic helper (`Classical.choice`-free): length of
`encodePtrBytesM`. -/
theorem encodePtrBytesM_length {M : Type} [Gen.Memory M] (prov : Option (Gen.Memory.Provenance M)) (i : Nat) (data : List UInt8) :
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
    simp only [Nat.pow_succ, Int.natCast_mul, Int.pow_succ, ih]; rfl
/-- `Classical.choice`-free `inBounds` proof for `addr < 2 ^ 64` at `usize`. -/
theorem inBounds_usize_cf (addr : Nat) (h : addr < 2 ^ 64) : inBounds (addr : Int) .Unsigned x86_64.PTR_SIZE = true := by
  rw [inBounds_usize, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  exact ⟨Int.natCast_nonneg addr, lt_two_pow_64_int h⟩
/-- `Classical.choice`-free `Endianness.encode` for 64-bit unsigned pointers. -/
theorem encode_usize_cf (addr : Nat) (h : addr < 2 ^ 64) :
    Endianness.encode x86_64.ENDIANNESS .Unsigned x86_64.PTR_SIZE (addr : Int) = some (leBytes addr 8) := by
  have hlt := lt_two_pow_64_int h
  have h0 : (0 : Int) ≤ (addr : Int) := Int.natCast_nonneg addr
  have hin := inBounds_usize_cf addr h
  have hmod : ((addr : Int) % (2 : Int) ^ Interp.Size.bits x86_64.PTR_SIZE).toNat = addr := by
    rw [two_pow_ptrBits, Int.emod_eq_of_lt h0 hlt]; exact Int.toNat_natCast addr
  unfold Endianness.encode; rw [hin]; dsimp only [↓reduceIte]; rw [hmod]; rfl
/-- `Classical.choice`-free base-256 remainder-splitting identity shared by
both MiniRust `leValue_leBytes_cf` and Trusted
`decodeLittleEndianBytes_encode`. -/
theorem mod_256_succ (v n : Nat) : v % 256 + 256 * (v / 256 % 256 ^ n) = v % 256 ^ (n + 1) := by
  rw [Nat.pow_succ']
  have h1 := Nat.mod_add_div v 256
  have h2 := Nat.mod_add_div (v / 256) (256 ^ n)
  have hlt1 : v % 256 < 256 := Nat.mod_lt v (by decide)
  have hlt2 : v / 256 % 256 ^ n < 256 ^ n := Nat.mod_lt _ (Nat.pow_pos (by decide))
  have hlt : v % 256 + 256 * (v / 256 % 256 ^ n) < 256 * 256 ^ n := by
    have hmul : 256 * (v / 256 % 256 ^ n + 1) ≤ 256 * 256 ^ n := Nat.mul_le_mul_left 256 hlt2
    have hmul' : 256 * (v / 256 % 256 ^ n) + 256 ≤ 256 * 256 ^ n := by
      simpa [Nat.mul_add] using hmul
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_right hlt1 _) (by rw [Nat.add_comm]; exact hmul')
  have heq : v = (v % 256 + 256 * (v / 256 % 256 ^ n)) + (256 * 256 ^ n) * (v / 256 / 256 ^ n) := by
    calc v = v % 256 + 256 * (v / 256) := h1.symm
      _ = v % 256 + 256 * (v / 256 % 256 ^ n + 256 ^ n * (v / 256 / 256 ^ n)) := by rw [h2]
      _ = (v % 256 + 256 * (v / 256 % 256 ^ n)) + (256 * 256 ^ n) * (v / 256 / 256 ^ n) := by
        rw [Nat.mul_add, ← Nat.add_assoc, ← Nat.mul_assoc]
  conv => rhs; rw [heq]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
/-- `Classical.choice`-free little-endian decode/encode round-trip. -/
theorem leValue_leBytes_cf (v : Nat) : ∀ n, leValue (leBytes v n) = v % 256 ^ n
  | 0 => by simp [leBytes, leValue, Nat.mod_one]
  | n + 1 => by
    simp only [leBytes, leValue, UInt8.toNat_ofNat', leValue_leBytes_cf (v / 256) n]
    rw [show (2 : Nat) ^ 8 = 256 by decide, Nat.mod_mod]; exact mod_256_succ v n
/-- `Classical.choice`-free `inBounds` proof for `intFromBits bits it`. -/
theorem inBounds_intFromBits_cf (it : Gen.IntType) (hsz : 0 < it.size.bytes) (bits : Nat) (hb : bits < 2 ^ (8 * it.size.bytes)) :
    inBounds (intFromBits bits it) it.signed it.size = true := by
  rcases it with ⟨signed, sz⟩
  cases signed with
  | Unsigned =>
    unfold inBounds intFromBits; dsimp only []; rw [Bool.and_eq_true]
    refine ⟨decide_eq_true (Int.natCast_nonneg bits), decide_eq_true ?_⟩
    change (bits : Int) < (2 : Int) ^ (8 * sz.bytes)
    rw [← two_pow_int_cf]; exact Int.ofNat_lt.mpr hb
  | Signed =>
    unfold inBounds intFromBits; dsimp only []
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
        exact Int.le_trans (Int.neg_nonpos_of_nonneg (by rw [← two_pow_int_cf]; exact Int.natCast_nonneg _)) (Int.natCast_nonneg bits)
      · change (bits : Int) < (2 : Int) ^ (8 * sz.bytes - 1)
        rw [← two_pow_int_cf]; exact Int.ofNat_lt.mpr hlt
    · next hge =>
      have hge' : 2 ^ (8 * sz.bytes - 1) ≤ bits := Nat.le_of_not_lt hge
      rw [Bool.and_eq_true]
      refine ⟨decide_eq_true ?_, decide_eq_true ?_⟩
      · change -((2 : Int) ^ (8 * sz.bytes - 1)) ≤ (bits : Int) - (2 : Int) ^ (8 * sz.bytes)
        rw [← two_pow_int_cf, ← two_pow_int_cf]
        have hsum : 2 ^ (8 * sz.bytes) ≤ 2 ^ (8 * sz.bytes - 1) + bits := by
          rw [hsplit]; exact Nat.add_le_add_left hge' _
        have hsumI : ((2 ^ (8 * sz.bytes) : Nat) : Int) ≤ ((2 ^ (8 * sz.bytes - 1) : Nat) : Int) + (bits : Int) := by
          rw [← Int.natCast_add]; exact Int.ofNat_le.mpr hsum
        have h1 := Int.add_le_add_left hsumI (-((2 ^ (8 * sz.bytes - 1) : Nat) : Int))
        rw [← Int.add_assoc, Int.add_left_neg, Int.zero_add] at h1
        have h2 := Int.sub_le_sub_right h1 ((2 ^ (8 * sz.bytes) : Nat) : Int)
        rw [Int.add_sub_cancel] at h2; exact h2
      · change (bits : Int) - (2 : Int) ^ (8 * sz.bytes) < (2 : Int) ^ (8 * sz.bytes - 1)
        rw [← two_pow_int_cf, ← two_pow_int_cf]
        have hltI : (bits : Int) < ((2 ^ (8 * sz.bytes) : Nat) : Int) := Int.ofNat_lt.mpr hb
        have hsub_neg : (bits : Int) - ((2 ^ (8 * sz.bytes) : Nat) : Int) < 0 := by
          have := Int.sub_lt_sub_right hltI ((2 ^ (8 * sz.bytes) : Nat) : Int)
          rwa [Int.sub_self] at this
        exact Int.lt_of_lt_of_le hsub_neg (Int.natCast_nonneg _)
/-- Polymorphic helper (`Classical.choice`-free): `encodePtrM` from an
explicit `Endianness.encode` witness (avoids unfolding `2 ^ 64` in the
kernel). -/
theorem encodePtrM_of_encode {M : Type} [Gen.Memory M] (ptr : ThinPointer (Gen.Memory.Provenance M)) (data : List UInt8)
    (henc : Endianness.encode x86_64.ENDIANNESS .Unsigned x86_64.PTR_SIZE ptr.addr = some data) :
    encodePtrM (M := M) ptr = .ok (encodePtrBytesM (M := M) ptr.provenance 0 data) := by
  unfold encodePtrM; rw [henc]; rfl
/-- Polymorphic thin-pointer encode (`Classical.choice`-free) across `Mach`
and `MachTB`. -/
theorem encodePtrM_eq {M : Type} [Gen.Memory M] (addr : Nat) (h : addr < 2 ^ 64) (prov : Option (Gen.Memory.Provenance M)) :
    encodePtrM (M := M) { addr := addr, provenance := prov } = .ok (encodePtrBytesM (M := M) prov 0 (leBytes addr 8)) :=
  encodePtrM_of_encode { addr, provenance := prov } (leBytes addr 8) (encode_usize_cf addr h)
/-- Polymorphic thin-pointer decode (`Classical.choice`-free) across `Mach`
and `MachTB`. -/
theorem decodePtrM_encodePtrBytesM {M : Type} [Gen.Memory M] [MemoryOps M]
    (addr : Nat) (h : addr < 2 ^ 64) (prov : Option (Gen.Memory.Provenance M)) :
    decodePtrM (M := M) (encodePtrBytesM (M := M) prov 0 (leBytes addr 8)) = .ok (some { addr := addr, provenance := prov }) := by
  have hlen : (encodePtrBytesM (M := M) prov 0 (leBytes addr 8)).length = x86_64.PTR_SIZE.bytes := by
    rw [encodePtrBytesM_length, leBytes_length]; rfl
  have h256 : addr < 256 ^ 8 := by rw [show (256 : Nat) ^ 8 = 2 ^ 64 by decide]; exact h
  have hval : Endianness.decode x86_64.ENDIANNESS .Unsigned (leBytes addr 8) = (addr : Int) := by
    simp only [Endianness.decode, x86_64.ENDIANNESS, leValue_leBytes_cf, Nat.mod_eq_of_lt h256]
  have hfirst : firstProvenanceM (M := M) (encodePtrBytesM (M := M) prov 0 (leBytes addr 8)) = prov :=
    firstProvenanceM_encode prov _ _
  unfold decodePtrM; rw [ite_eq_right_iff.mpr (fun hn => absurd hlen hn), encodePtrBytesM_data]
  dsimp only; rw [hval, hfirst, decodePtrProvenanceM_encode]; rfl
/-- Polymorphic helper (`Classical.choice`-free): `transmuteM` on
`thinRawPtrTy` from explicit `inBounds`, `encodeM`, and `decodeM` witnesses. -/
theorem transmuteM_thinRawPtr_of_codec {M : Type} [Gen.Memory M] [MemoryOps M] (addr : Int) (prov : Option (Gen.Memory.Provenance M))
    (bs : List (AbstractByte (Gen.Memory.Provenance M))) (m : Option (Machine M))
    (hin : inBounds addr .Unsigned x86_64.PTR_SIZE = true) (henc : Type.encodeM (M := M) thinRawPtrTy
      (.Ptr (ThinPointer.widen { addr := addr, provenance := prov } none)) = .ok bs)
    (hdec : Type.decodeM (M := M) thinRawPtrTy bs = .ok (some (.Ptr (ThinPointer.widen { addr := addr, provenance := prov } none)))) :
    let p : Gen.Pointer (Gen.Memory.Provenance M) := ThinPointer.widen { addr := addr, provenance := prov } none
    transmuteM (M := M) (.Ptr p) thinRawPtrTy thinRawPtrTy m = .ok (.Ptr p) := by
  intro p; unfold transmuteM; rw [layout_thinRawPtr]
  simp only [ok_bind, expect_size_sized, size_ne_self_ite_local]
  rw [show Type.encodeM (M := M) thinRawPtrTy (.Ptr p) = .ok bs from henc, ok_bind,
    show Type.decodeM (M := M) thinRawPtrTy bs = .ok (some (.Ptr p)) from hdec, ok_bind]
  dsimp only []; unfold checkValueM checkPtrM
  simp only [thinRawPtrTy, p, ThinPointer.widen, ensureElseUb, hin, ↓reduceIte,
    PtrType.meta_kind, checkPtrMetadataM, PtrType.safe_pointee, pure, Except.pure, bind, Except.bind]
  rfl
/-- Polymorphic `transmuteM` identity for thin raw pointers across EVERY
`Memory M` (`Mach` and `MachTB`), strictly `Classical.choice`-free. -/
theorem transmuteM_thinRawPtr_id {M : Type} [Gen.Memory M] [MemoryOps M]
    (addr : Nat) (h : addr < 2 ^ 64) (prov : Option (Gen.Memory.Provenance M)) (m : Option (Machine M)) :
    let p : Gen.Pointer (Gen.Memory.Provenance M) := ThinPointer.widen { addr := addr, provenance := prov } none
    transmuteM (M := M) (.Ptr p) thinRawPtrTy thinRawPtrTy m = .ok (.Ptr p) := by
  intro p
  have henc : Type.encodeM (M := M) thinRawPtrTy (.Ptr p) = .ok (encodePtrBytesM (M := M) prov 0 (leBytes addr 8)) := by
    simp only [thinRawPtrTy, Type.encodeM, PtrType.as_wide_pair, PtrType.meta_kind, p,
      ThinPointer.widen]; exact encodePtrM_eq addr h prov
  have hdec : Type.decodeM (M := M) thinRawPtrTy (encodePtrBytesM (M := M) prov 0 (leBytes addr 8)) = .ok (some (.Ptr p)) := by
    simp only [thinRawPtrTy, Type.decodeM, PtrType.as_wide_pair, PtrType.meta_kind, p,
      ThinPointer.widen]; rw [decodePtrM_encodePtrBytesM addr h prov, ok_bind]; rfl
  exact transmuteM_thinRawPtr_of_codec (addr : Int) prov _ m (inBounds_usize_cf addr h) henc hdec
theorem evalCastOpM_transmute_thinRawPtr_of_transmute {M : Type} [Gen.Memory M] [MemoryOps M]
    (p : Gen.Pointer (Gen.Memory.Provenance M)) (m : Option (Machine M))
    (ht : transmuteM (M := M) (.Ptr p) thinRawPtrTy thinRawPtrTy m = .ok (.Ptr p)) :
    evalCastOpM (M := M) (.Transmute thinRawPtrTy) (.Ptr p, thinRawPtrTy) m = .ok (.Ptr p, thinRawPtrTy) := by
  unfold evalCastOpM; dsimp only []; rw [layout_thinRawPtr]
  simp only [ok_bind, expect_size_sized, size_ne_self_ite_local, ht, pure, Except.pure, bind, Except.bind]
/-- Polymorphic `evalCastOpM` identity for thin raw pointers across `Mach`
and `MachTB` (`Classical.choice`-free). -/
theorem evalCastOpM_transmute_thinRawPtr_id {M : Type} [Gen.Memory M] [MemoryOps M]
    (addr : Nat) (h : addr < 2 ^ 64) (prov : Option (Gen.Memory.Provenance M)) (m : Option (Machine M)) :
    let p : Gen.Pointer (Gen.Memory.Provenance M) := ThinPointer.widen { addr := addr, provenance := prov } none
    evalCastOpM (M := M) (.Transmute thinRawPtrTy) (.Ptr p, thinRawPtrTy) m = .ok (.Ptr p, thinRawPtrTy) :=
  evalCastOpM_transmute_thinRawPtr_of_transmute _ m (transmuteM_thinRawPtr_id addr h prov m)
theorem evalCastOp_transmute_thinRawPtr_of_codec (addr : Int) (prov : Option Prov) (bs : List Byte) (m : Option Mach)
    (hin : inBounds addr .Unsigned x86_64.PTR_SIZE = true) (henc : Type.encode thinRawPtrTy
      (.Ptr (ThinPointer.widen { addr := addr, provenance := prov } none)) = .ok bs)
    (hdec : Type.decode thinRawPtrTy bs = .ok (some (.Ptr (ThinPointer.widen { addr := addr, provenance := prov } none)))) :
    let p : Gen.Pointer Prov := ThinPointer.widen { addr := addr, provenance := prov } none
    evalCastOp (.Transmute thinRawPtrTy) (.Ptr p, thinRawPtrTy) m = .ok (.Ptr p, thinRawPtrTy) := by
  intro p; unfold evalCastOp transmute; dsimp only []; rw [layout_thinRawPtr]
  simp only [ok_bind, expect_size_sized, size_ne_self_ite_local]
  rw [show Type.encode thinRawPtrTy (.Ptr p) = .ok bs from henc, ok_bind,
    show Type.decode thinRawPtrTy bs = .ok (some (.Ptr p)) from hdec, ok_bind]
  dsimp only []; unfold checkValue checkPtr
  simp only [thinRawPtrTy, p, ThinPointer.widen, ensureElseUb, hin, ↓reduceIte,
    PtrType.meta_kind, checkPtrMetadata, PtrType.safe_pointee, pure, Except.pure, bind, Except.bind]
  rfl
theorem encode_thinRawPtr_cf (addr : Nat) (h : addr < 2 ^ 64) (prov : Option Prov) :
    Type.encode thinRawPtrTy (.Ptr (ThinPointer.widen { addr := addr, provenance := prov } none)) = .ok (ptrBytes addr prov) := by
  simp only [thinRawPtrTy, Type.encode, PtrType.as_wide_pair, PtrType.meta_kind, ThinPointer.widen]
  exact encodePtr_of_encode { addr, provenance := prov } (leBytes addr 8) (encode_usize_cf addr h)
theorem decode_thinRawPtr_cf (addr : Nat) (h : addr < 2 ^ 64) (prov : Option Prov) : Type.decode thinRawPtrTy (ptrBytes addr prov) =
      .ok (some (.Ptr (ThinPointer.widen { addr := addr, provenance := prov } none))) := by
  have h256 : addr < 256 ^ 8 := by rw [show (256 : Nat) ^ 8 = 2 ^ 64 by decide]; exact h
  have hval : Endianness.decode x86_64.ENDIANNESS .Unsigned (leBytes addr 8) = (addr : Int) := by
    simp only [Endianness.decode, x86_64.ENDIANNESS, leValue_leBytes_cf, Nat.mod_eq_of_lt h256]
  have hlen : (ptrBytes addr prov).length = x86_64.PTR_SIZE.bytes := ptrBytes_length addr prov
  have hfirst : firstProvenance (ptrBytes addr prov) = prov := firstProvenance_encodePtrBytes prov _ _
  simp only [thinRawPtrTy, Type.decode, PtrType.as_wide_pair, PtrType.meta_kind]; unfold decodePtr
  rw [ite_eq_right_iff.mpr (fun hn => absurd hlen hn), hfirst]
  unfold ptrBytes; rw [encodePtrBytes_data]; simp only [hval, decodePtrProvenance_encode]; rfl
theorem evalCastOp_transmute_thinRawPtr_id (addr : Nat) (h : addr < 2 ^ 64) (prov : Option Prov) (m : Option Mach) :
    let p : Gen.Pointer Prov := ThinPointer.widen { addr := addr, provenance := prov } none
    evalCastOp (.Transmute thinRawPtrTy) (.Ptr p, thinRawPtrTy) m = .ok (.Ptr p, thinRawPtrTy) :=
  evalCastOp_transmute_thinRawPtr_of_codec (addr : Int) prov (ptrBytes addr prov) m
    (inBounds_usize_cf addr h) (encode_thinRawPtr_cf addr h prov) (decode_thinRawPtr_cf addr h prov)
/-- `Classical.choice`-free polymorphic little-endian integer encode bridge. -/
theorem encodeIntM_intFromBits {M : Type} [Gen.Memory M]
    (it : Gen.IntType) (hsz : 0 < it.size.bytes) (bits : Nat) (hb : bits < 2 ^ (8 * it.size.bytes)) :
    Type.encodeIntM (M := M) it (.Int (intFromBits bits it)) = .ok ((leBytes bits it.size.bytes).map (fun b => .Init b none)) := by
  have hbits : Interp.Size.bits it.size = 8 * it.size.bytes := rfl
  have hin := inBounds_intFromBits_cf it hsz bits hb
  have hmod : (intFromBits bits it % (2 : Int) ^ Interp.Size.bits it.size).toNat = bits := by
    rw [hbits, intFromBits_emod bits it hb]; rfl
  unfold Type.encodeIntM Endianness.encode; simp only [hin, ↓reduceIte, hmod, x86_64.ENDIANNESS, pure, Except.pure]
theorem mapM_dataM_initNone {M : Type} [Gen.Memory M] (bs : List UInt8) :
    (bs.map (fun b => (AbstractByte.Init b none : AbstractByte (Gen.Memory.Provenance M)))).mapM AbstractByte.dataM = some bs := by
  induction bs with | nil => rfl | cons _ _ ih => simp [AbstractByte.dataM, ih]
/-- `Classical.choice`-free polymorphic integer decode of `leBytes`. -/
theorem decodeIntM_leBytes {M : Type} [Gen.Memory M]
    (it : Gen.IntType) (hsz : 0 < it.size.bytes) (bits : Nat) (hb : bits < 2 ^ (8 * it.size.bytes)) :
    Type.decodeIntM (M := M) it ((leBytes bits it.size.bytes).map (fun b => .Init b none)) =
      .ok (some (.Int (intFromBits bits it))) := by
  rcases it with ⟨signed, sz⟩
  have hlen : ((leBytes bits sz.bytes).map (fun b => (AbstractByte.Init b none : AbstractByte (Gen.Memory.Provenance M)))).length =
      sz.bytes := by simp [leBytes_length]
  have h256 : 256 ^ sz.bytes = 2 ^ (8 * sz.bytes) := by
    rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul]
  have hle : leValue (leBytes bits sz.bytes) = bits := by
    rw [leValue_leBytes_cf, h256, Nat.mod_eq_of_lt hb]
  have hdec : Endianness.decode x86_64.ENDIANNESS signed (leBytes bits sz.bytes) = intFromBits bits ⟨signed, sz⟩ := by
    cases signed with
    | Unsigned => simp only [Endianness.decode, x86_64.ENDIANNESS, hle, intFromBits]
    | Signed =>
      have hlenNat : (leBytes bits sz.bytes).length = sz.bytes := leBytes_length bits _
      simp only [Endianness.decode, x86_64.ENDIANNESS, hle, intFromBits, hlenNat]
      if hlt : bits < 2 ^ (8 * sz.bytes - 1) then
        have hltI : (bits : Int) < (2 : Int) ^ (8 * sz.bytes - 1) := by
          rw [← two_pow_int_cf]; exact Int.ofNat_lt.mpr hlt
        rw [ite_eq_left_iff.mpr (fun hn => absurd hlt hn), ite_eq_left_iff.mpr (fun hn => absurd hltI hn)]
      else
        have hgeI : ¬ ((bits : Int) < (2 : Int) ^ (8 * sz.bytes - 1)) := by
          rw [← two_pow_int_cf]; intro hlt'; exact hlt (Int.ofNat_lt.mp hlt')
        rw [ite_eq_right_iff.mpr (fun hy => absurd hy hlt), ite_eq_right_iff.mpr (fun hy => absurd hy hgeI)]
  unfold Type.decodeIntM; dsimp only []
  rw [ite_eq_right_iff.mpr (fun hn => absurd hlen hn), mapM_dataM_initNone]; dsimp only; rw [hdec]; rfl
/-- `Classical.choice`-free polymorphic `transmuteM` between any two
same-size integer types across BOTH `Mach` and `MachTB`. -/
theorem transmuteM_int_sameSize {M : Type} [Gen.Memory M] [MemoryOps M]
    (srcIt dstIt : Gen.IntType) (hEq : srcIt.size = dstIt.size) (hsz : 0 < srcIt.size.bytes)
    (al : LibSpecr.Align) (hlay1 : Type.layout (.Int srcIt) = .ok (.Sized srcIt.size al))
    (hlay2 : Type.layout (.Int dstIt) = .ok (.Sized dstIt.size al))
    (bits : Nat) (hb : bits < 2 ^ (8 * srcIt.size.bytes)) (m : Option (Machine M)) :
    transmuteM (M := M) (.Int (intFromBits bits srcIt)) (.Int srcIt) (.Int dstIt) m = .ok (.Int (intFromBits bits dstIt)) := by
  have hdstSz : 0 < dstIt.size.bytes := by rw [← hEq]; exact hsz
  have hdstBits : bits < 2 ^ (8 * dstIt.size.bytes) := by rw [← hEq]; exact hb
  have hwinDst := inBounds_intFromBits_cf dstIt hdstSz bits hdstBits
  unfold transmuteM
  rw [hlay1, ok_bind, expect_size_sized, ok_bind, hlay2, ok_bind, expect_size_sized, ok_bind, hEq, size_ne_self_ite_local]
  simp only [Type.encodeM, Type.decodeM]
  rw [encodeIntM_intFromBits srcIt hsz bits hb, ok_bind, hEq, decodeIntM_leBytes dstIt hdstSz bits hdstBits, ok_bind]
  simp only [checkValueM, IntType.can_represent, ensureElseUb, hwinDst, ↓reduceIte, pure, Except.pure, bind, Except.bind]; rfl
/-- MiniRust transparent single-field wrapper `#[repr(transparent)] struct
Binder(T)`: offset-0 field 0 with identical size and alignment to `inner`. -/
@[reducible] def mrBinderWrapperTy (inner : Gen.Type)
    (sz : LibSpecr.Size) (al : LibSpecr.Align) : Gen.Type := .Tuple [(⟨0⟩, inner)] ⟨sz, al, none⟩ none
/-- `Classical.choice`-free polymorphic wide-slice raw pointer (`*const [T]`
/ `*mut [T]`) codecs across `Mach` and `MachTB`. -/
theorem encodeUsizeIntM_of_encode {M : Type} [Gen.Memory M] (len : Int) (data : List UInt8)
    (henc : Endianness.encode x86_64.ENDIANNESS .Unsigned x86_64.PTR_SIZE len = some data) :
    Type.encodeIntM (M := M) IntType.usize_ty (.Int len) = .ok (data.map (fun b => .Init b none)) := by
  unfold Type.encodeIntM; dsimp only [IntType.usize_ty]; rw [henc]; rfl
theorem encodeWideSliceRawPtrM_of_encode {M : Type} [Gen.Memory M] (addr len : Int) (prov : Option (Gen.Memory.Provenance M))
    (thinBs metaBs : List (AbstractByte (Gen.Memory.Provenance M)))
    (hPtrEnc : encodePtrM (M := M) { addr := addr, provenance := prov } = .ok thinBs)
    (hMetaEnc : Type.encodeIntM (M := M) IntType.usize_ty (.Int len) = .ok metaBs) :
    Type.encodeM (M := M) wideSlicePtrMrTy (mrWidePtrValM { addr := addr, provenance := prov } len) = .ok (thinBs ++ metaBs) := by
  change encodeWidePtrM (M := M) .ElementCount (ThinPointer.widen { addr, provenance := prov } (some (.ElementCount len))) = _
  unfold encodeWidePtrM PointerMetaKind.encode_as_valueM ThinPointer.widen
  dsimp only [pure, Except.pure, bind, Except.bind]; rw [hPtrEnc, hMetaEnc]
theorem encodeWideSliceRawPtrM_eq {M : Type} [Gen.Memory M] (addr len : Nat) (hAddr : addr < 2 ^ 64) (hLen : len < 2 ^ 64)
    (prov : Option (Gen.Memory.Provenance M)) :
    Type.encodeM (M := M) wideSlicePtrMrTy (mrWidePtrValM { addr := addr, provenance := prov } (len : Int)) =
      .ok (encodePtrBytesM (M := M) prov 0 (leBytes addr 8) ++ (leBytes len 8).map (fun b => .Init b none)) :=
  encodeWideSliceRawPtrM_of_encode (addr : Int) (len : Int) prov _ _ (encodePtrM_eq addr hAddr prov)
    (encodeUsizeIntM_of_encode (len : Int) (leBytes len 8) (encode_usize_cf len hLen))
theorem decodeWideSliceRawPtrM_eq {M : Type} [Gen.Memory M] [MemoryOps M]
    (addr len : Nat) (hAddr : addr < 2 ^ 64) (hLen : len < 2 ^ 64) (prov : Option (Gen.Memory.Provenance M)) :
    Type.decodeM (M := M) wideSlicePtrMrTy (encodePtrBytesM (M := M) prov 0 (leBytes addr 8) ++
          (leBytes len 8).map (fun b => .Init b none)) =
      .ok (some (mrWidePtrValM { addr := addr, provenance := prov } (len : Int))) := by
  let thinBs := encodePtrBytesM (M := M) prov 0 (leBytes addr 8)
  let metaBs : List (AbstractByte (Gen.Memory.Provenance M)) := (leBytes len 8).map (fun b => .Init b none)
  have hLenThin : thinBs.length = 8 := by dsimp only [thinBs]; rw [encodePtrBytesM_length, leBytes_length]
  have hLenMeta : metaBs.length = 8 := by dsimp only [metaBs]; rw [List.length_map, leBytes_length]
  have hLenAll : (thinBs ++ metaBs).length = 2 * x86_64.PTR_SIZE.bytes := by
    rw [List.length_append, hLenThin, hLenMeta]; rfl
  have hTake : (thinBs ++ metaBs).take x86_64.PTR_SIZE.bytes = thinBs := by
    change (thinBs ++ metaBs).take 8 = thinBs; rw [← hLenThin, List.take_left]
  have hDrop : (thinBs ++ metaBs).drop x86_64.PTR_SIZE.bytes = metaBs := by
    change (thinBs ++ metaBs).drop 8 = metaBs; rw [← hLenThin, List.drop_left]
  have hMetaDec : Type.decodeIntM (M := M) IntType.usize_ty metaBs = .ok (some (.Int (len : Int))) :=
    decodeIntM_leBytes (M := M) IntType.usize_ty (by decide) len hLen
  simp only [wideSlicePtrMrTy, Type.decodeM, PtrType.as_wide_pair, PtrType.meta_kind]; unfold decodeWidePtrM
  rw [ite_eq_right_iff.mpr (fun hn => absurd hLenAll hn), hTake, hDrop, decodePtrM_encodePtrBytesM addr hAddr prov, ok_bind]
  dsimp only [decodeMetaFieldM]; rw [hMetaDec, ok_bind]; rfl
theorem transmuteM_wideSliceRawPtr_of_codec {M : Type} [Gen.Memory M] [MemoryOps M]
    (addr len : Int) (prov : Option (Gen.Memory.Provenance M))
    (bs : List (AbstractByte (Gen.Memory.Provenance M))) (m : Option (Machine M))
    (hinAddr : inBounds addr .Unsigned x86_64.PTR_SIZE = true) (hinLen : inBounds len .Unsigned x86_64.PTR_SIZE = true)
    (henc : Type.encodeM (M := M) wideSlicePtrMrTy (mrWidePtrValM { addr := addr, provenance := prov } len) = .ok bs)
    (hdec : Type.decodeM (M := M) wideSlicePtrMrTy bs = .ok (some (mrWidePtrValM { addr := addr, provenance := prov } len))) :
    let v := mrWidePtrValM { addr := addr, provenance := prov } len
    transmuteM (M := M) v wideSlicePtrMrTy wideSlicePtrMrTy m = .ok v := by
  intro v; have hlay : Type.layout wideSlicePtrMrTy = .ok (.Sized ⟨16⟩ ⟨8⟩) := rfl
  have hCanRep : IntType.can_represent IntType.usize_ty len = true := hinLen
  unfold transmuteM; rw [hlay]; simp only [ok_bind, expect_size_sized, size_ne_self_ite_local]
  rw [show Type.encodeM (M := M) wideSlicePtrMrTy v = .ok bs from henc, ok_bind,
      show Type.decodeM (M := M) wideSlicePtrMrTy bs = .ok (some v) from hdec, ok_bind]
  dsimp only [v, mrWidePtrValM]; unfold checkValueM checkPtrM
  simp only [wideSlicePtrMrTy, ThinPointer.widen, ensureElseUb, hinAddr, ↓reduceIte,
    PtrType.meta_kind, checkPtrMetadataM, hCanRep, PtrType.safe_pointee,
    Bool.not_true, Bool.false_eq_true, pure, Except.pure, bind, Except.bind]
theorem transmuteM_wideSliceRawPtr_id {M : Type} [Gen.Memory M] [MemoryOps M]
    (addr len : Nat) (hAddr : addr < 2 ^ 64) (hLen : len < 2 ^ 64)
    (prov : Option (Gen.Memory.Provenance M)) (m : Option (Machine M)) :
    let v := mrWidePtrValM { addr := addr, provenance := prov } (len : Int)
    transmuteM (M := M) v wideSlicePtrMrTy wideSlicePtrMrTy m = .ok v :=
  transmuteM_wideSliceRawPtr_of_codec (addr : Int) (len : Int) prov _ m (inBounds_usize_cf addr hAddr) (inBounds_usize_cf len hLen)
    (encodeWideSliceRawPtrM_eq addr len hAddr hLen prov) (decodeWideSliceRawPtrM_eq addr len hAddr hLen prov)
theorem evalCastOpM_transmute_wideSliceRawPtr_of_transmute {M : Type} [Gen.Memory M] [MemoryOps M]
    (v : Gen.Value M) (m : Option (Machine M)) (ht : transmuteM (M := M) v wideSlicePtrMrTy wideSlicePtrMrTy m = .ok v) :
    evalCastOpM (M := M) (.Transmute wideSlicePtrMrTy) (v, wideSlicePtrMrTy) m = .ok (v, wideSlicePtrMrTy) := by
  have hlay : Type.layout wideSlicePtrMrTy = .ok (.Sized ⟨16⟩ ⟨8⟩) := rfl
  unfold evalCastOpM; dsimp only []; rw [hlay]
  simp only [ok_bind, expect_size_sized, size_ne_self_ite_local, ht, pure, Except.pure, bind, Except.bind]
theorem evalCastOpM_transmute_wideSliceRawPtr_id {M : Type} [Gen.Memory M] [MemoryOps M]
    (addr len : Nat) (hAddr : addr < 2 ^ 64) (hLen : len < 2 ^ 64)
    (prov : Option (Gen.Memory.Provenance M)) (m : Option (Machine M)) :
    let v := mrWidePtrValM { addr := addr, provenance := prov } (len : Int)
    evalCastOpM (M := M) (.Transmute wideSlicePtrMrTy) (v, wideSlicePtrMrTy) m =
      .ok (v, wideSlicePtrMrTy) := evalCastOpM_transmute_wideSliceRawPtr_of_transmute _ m
    (transmuteM_wideSliceRawPtr_id addr len hAddr hLen prov m)
/-- `Classical.choice`-free polymorphic encoder/decoder & bidirectional
`transmuteM` identity for `mrBinderWrapperTy inner sz al` (`Binder(T) ↔ T`). -/
theorem transmuteM_binderWrapper_roundtrip {M : Type} [Gen.Memory M] [MemoryOps M]
    (inner : Gen.Type) (sz : LibSpecr.Size) (al : LibSpecr.Align)
    (v : Gen.Value M) (bs : List (AbstractByte (Gen.Memory.Provenance M))) (m : Option (Machine M))
    (hInnerLay : Type.layout inner = .ok (.Sized sz al)) (hHead : TupleHeadLayout.head_size_and_align ⟨sz, al, none⟩ = (sz, al))
    (hEnc : Type.encodeM (M := M) inner v = .ok bs) (hLen : bs.length = sz.bytes)
    (hDec : Type.decodeM (M := M) inner bs = .ok (some v)) (hChk : checkValueM (M := M) v inner m = .ok ()) :
    Type.encodeM (M := M) (mrBinderWrapperTy inner sz al) (.Tuple [v]) = .ok bs ∧
    Type.decodeM (M := M) (mrBinderWrapperTy inner sz al) bs = .ok (some (.Tuple [v])) ∧
    transmuteM (M := M) (.Tuple [v]) (mrBinderWrapperTy inner sz al) inner m = .ok v ∧
    transmuteM (M := M) v inner (mrBinderWrapperTy inner sz al) m = .ok (.Tuple [v]) := by
  have hLayWrap : Type.layout (mrBinderWrapperTy inner sz al) = .ok (.Sized sz al) := by
    simp only [mrBinderWrapperTy, Type.layout, hHead, pure, Except.pure]
  have hWrite0 : writeSubsliceAtIndex (List.replicate sz.bytes (AbstractByte.Uninit : AbstractByte (Gen.Memory.Provenance M)))
      0 bs = .ok bs := by
    have hCond : (0 : Int) ≤ 0 ∧ (0 : Int) + (bs.length : Int) ≤ ((List.replicate sz.bytes
            (AbstractByte.Uninit : AbstractByte (Gen.Memory.Provenance M))).length : Int) := by
      simp [hLen]
    unfold writeSubsliceAtIndex; rw [ite_eq_left_iff.mpr (fun hn => absurd hCond hn)]; simp [hLen]
  have hSub0 : subsliceWithLength bs 0 sz.bytes = .ok bs := by
    have hCond : (0 : Int) ≤ 0 ∧ (0 : Int) ≤ (sz.bytes : Int) ∧
        (0 : Int) + (sz.bytes : Int) ≤ (bs.length : Int) := by simp [hLen, Int.natCast_nonneg]
    unfold subsliceWithLength; rw [ite_eq_left_iff.mpr (fun hn => absurd hCond hn)]
    have hToNat : (sz.bytes : Int).toNat = bs.length := by rw [Int.toNat_natCast, hLen]
    simp [hToNat]
  have hEncWrap : Type.encodeM (M := M) (mrBinderWrapperTy inner sz al) (.Tuple [v]) = .ok bs := by
    simp only [mrBinderWrapperTy, Type.encodeM, hHead, List.length, ne_eq, not_true_eq_false, ↓reduceIte, Type.encodeFieldsM]
    rw [hEnc, ok_bind, show ((0 : Nat) : Int) = 0 from rfl, hWrite0, ok_bind]; rfl
  have hDecWrap : Type.decodeM (M := M) (mrBinderWrapperTy inner sz al) bs = .ok (some (.Tuple [v])) := by
    simp only [mrBinderWrapperTy, Type.decodeM, hHead, hLen, ne_eq, not_true_eq_false, ↓reduceIte, Type.decodeFieldsM]
    rw [hInnerLay, ok_bind, expect_size_sized, ok_bind,
        show ((0 : Nat) : Int) = 0 from rfl, hSub0, ok_bind, hDec, ok_bind]; rfl
  have hChkWrap : checkValueM (M := M) (.Tuple [v]) (mrBinderWrapperTy inner sz al) m = .ok () := by
    simp only [mrBinderWrapperTy, checkValueM, ensureElseUb, beq_self_eq_true, ↓reduceIte,
      Bool.not_true, Bool.false_eq_true, checkFieldsM]; rw [hChk, ok_bind]; rfl
  refine ⟨hEncWrap, hDecWrap, ?_, ?_⟩
  · unfold transmuteM
    rw [hLayWrap, ok_bind, expect_size_sized, ok_bind, hInnerLay, ok_bind,
        expect_size_sized, ok_bind, size_ne_self_ite_local, hEncWrap, ok_bind, hDec, ok_bind]
    dsimp only []; rw [hChk, ok_bind]; rfl
  · unfold transmuteM
    rw [hInnerLay, ok_bind, expect_size_sized, ok_bind, hLayWrap, ok_bind,
        expect_size_sized, ok_bind, size_ne_self_ite_local, hEnc, ok_bind, hDecWrap, ok_bind]
    dsimp only []; rw [hChkWrap, ok_bind]; rfl
/-- `Classical.choice`-free byte-0 overwrite frame law for
`writeSubsliceAtIndex`: overwriting `[new0]` at offset `0` updates ONLY byte
`0` and preserves the entire tail `rest` verbatim. -/
theorem writeSubsliceAtIndex_byte0 {α : Type} (old0 new0 : α) (rest : List α) :
    writeSubsliceAtIndex (old0 :: rest) 0 [new0] = .ok (new0 :: rest) := by
  have hCond : (0 : Int) ≤ 0 ∧ (0 : Int) + (([new0] : List α).length : Int) ≤ (((old0 :: rest) : List α).length : Int) :=
    ⟨Int.le_refl 0, by
      simp only [List.length_cons, List.length_nil, Int.zero_add]
      exact Int.ofNat_le.mpr (Nat.succ_le_succ (Nat.zero_le _))⟩
  unfold writeSubsliceAtIndex; rw [ite_eq_left_iff.mpr (fun hn => absurd hCond hn)]
  rfl
/-- Byte-0 tag-write frame law for `BM.store` and `TreeBorrowsMemory.store`
(`Classical.choice`-free): storing `[new0]` at offset `0` of an allocation
whose bytes are `old0 :: rest` updates ONLY byte `0` to `new0` (and on
`MachTB`, runs `Node.access` solely on `[0, 1)`) while preserving all
trailing bytes `rest` verbatim. -/
theorem bm_store_byte0_frame (mem : BM) (ptr : Ptr) (old0 new0 : Byte) (rest : List Byte)
    (id : Gen.AllocId) (alloc : Gen.Allocation) (allocs' : List Gen.Allocation)
    (hCheck : BM.check_ptr mem ptr ⟨1⟩ = .ok (some (id, (), ⟨0⟩)))
    (hIdx : listIndex mem.allocations id._0 "self.allocations[id.0]" = .ok alloc) (hData : alloc.data = old0 :: rest)
    (hSet : listSet mem.allocations id._0 { alloc with data := new0 :: rest } "set" = .ok allocs') :
    BM.store mem ptr [new0] ⟨1⟩ = .ok { mem with allocations := allocs' } := by
  have hAl : Align.is_aligned ⟨1⟩ ptr.addr = true := by
    show (ptr.addr % (1 : Int) == 0) = true; rw [Int.emod_one]; rfl
  unfold BM.store; rw [hAl]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.length_singleton, hCheck, ok_bind, hIdx, hData]
  rw [show (({ bytes := 0 } : Gen.Offset).bytes : Int) = 0 from rfl, writeSubsliceAtIndex_byte0]
  simp only [hSet, bind, Except.bind, pure, Except.pure]
theorem tbm_store_byte0_frame (tbm : TBM) (ptr : ThinPointer TreeBorrowsProvenance)
    (old0 new0 : AbstractByte TreeBorrowsProvenance) (rest : List (AbstractByte TreeBorrowsProvenance))
    (id : Gen.AllocId) (path : Gen.Path) (alloc : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra) (root' : Gen.Node)
    (allocs' : List (Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra))
    (hCheck : BasicMemory.check_ptr tbm.mem ptr ⟨1⟩ = .ok (some (id, path, ⟨0⟩)))
    (hIdx : listIndex tbm.mem.allocations id._0 "self.allocations[id.0]" = .ok alloc)
    (hNode : Node.access alloc.extra.root (some path) .Write ⟨0⟩ ⟨1⟩ = .ok root') (hData : alloc.data = old0 :: rest)
    (hSet : listSet tbm.mem.allocations id._0 { alloc with data := new0 :: rest, extra := { root := root' } } "set" = .ok allocs') :
    TreeBorrowsMemory.store tbm ptr [new0] ⟨1⟩ = .ok { tbm with mem := { tbm.mem with allocations := allocs' } } := by
  have hAl : Align.is_aligned ⟨1⟩ ptr.addr = true := by
    show (ptr.addr % (1 : Int) == 0) = true; rw [Int.emod_one]; rfl
  unfold TreeBorrowsMemory.store BasicMemory.store; dsimp only [List.length_singleton]; rw [hAl]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hCheck, ok_bind, hIdx, hNode, hData]
  rw [show (({ bytes := 0 } : Gen.Offset).bytes : Int) = 0 from rfl, writeSubsliceAtIndex_byte0]
  simp only [hSet, bind, Except.bind, pure, Except.pure]
/-- `Classical.choice`-free Trusted little-endian byte codec lemmas backing
hypothesis-free universal `C7` `evalByteCast` correspondence. -/
theorem mergeByteProvenance_self (prov : Option (Nat × Nat)) : mergeByteProvenance prov prov = prov := by
  cases prov with
  | none => rfl
  | some p => rcases p with ⟨a, t⟩; simp [mergeByteProvenance]
theorem decodeLittleEndianBytes_encode (v : Nat) :
    ∀ n (prov : Option (Nat × Nat)), decodeLittleEndianBytes (encodeLittleEndianBytes v n prov) =
        some (v % 256 ^ n, if n = 0 then none else prov)
  | 0, _ => by simp [decodeLittleEndianBytes, Nat.mod_one]
  | n + 1, prov => by
    have ih := decodeLittleEndianBytes_encode (Nat.div v 256) n prov
    have hByte : (UInt8.ofNat v).toBitVec.toNat = v % 256 := by
      change (UInt8.ofNat v).toNat = v % 256; exact UInt8.toNat_ofNat'
    have hProv : mergeByteProvenance prov (if n = 0 then none else prov) = prov := by
      cases n with | zero => cases prov <;> rfl | succ _ => exact mergeByteProvenance_self prov
    change (match decodeLittleEndianBytes (encodeLittleEndianBytes (Nat.div v 256) n prov) with
      | some (highBits, restProv) => some (Nat.add (UInt8.ofNat v).toBitVec.toNat (Nat.mul 256 highBits),
              mergeByteProvenance prov restProv)
      | none => none) = some (v % 256 ^ (n + 1), prov)
    rw [ih]
    change some ((UInt8.ofNat v).toBitVec.toNat + 256 * (v / 256 % 256 ^ n),
      mergeByteProvenance prov (if n = 0 then none else prov)) = some (v % 256 ^ (n + 1), prov)
    rw [hByte, mod_256_succ v n, hProv]
theorem abstractBytesAllProvAux_encode (a t v : Nat) :
    ∀ n, abstractBytesAllProvAux a t (encodeLittleEndianBytes v n (some (a, t))) = true
  | 0 => rfl
  | n + 1 => by
    change (Bool.and (Nat.beq a a) (Nat.beq t t) &&
      abstractBytesAllProvAux a t (encodeLittleEndianBytes (Nat.div v 256) n (some (a, t)))) = true
    rw [Nat.beq_refl, Nat.beq_refl, abstractBytesAllProvAux_encode a t (Nat.div v 256) n]; rfl
theorem encodeLittleEndianBytes_len (v : Nat) : ∀ n prov, Trusted.Sequence.length (encodeLittleEndianBytes v n prov) = n
  | 0, _ => rfl
  | n + 1, prov => by
    change Trusted.Sequence.length (encodeLittleEndianBytes (Nat.div v 256) n prov) + 1 = n + 1
    rw [encodeLittleEndianBytes_len (Nat.div v 256) n prov]

/-! ## §1 (`C1`): `StatementKind.setDiscriminant` (`Mach` & `MachTB`) -/
/-- Variant table of `twoVarEnumMrTy`. -/
def twoVarEnumVariants : Map Int Gen.Variant :=
  let vTy : Gen.Type := .Tuple [(⟨4⟩, u32MrTy)] ⟨⟨8⟩, ⟨4⟩, none⟩ none
  ⟨[(0, ⟨vTy, ⟨[(⟨0⟩, (⟨.Unsigned, ⟨1⟩⟩, 0))]⟩⟩), (1, ⟨vTy, ⟨[(⟨0⟩, (⟨.Unsigned, ⟨1⟩⟩, 1))]⟩⟩)]⟩
/-- Direct-tagged two-variant Rust enum layout (`#[repr(u8)] enum TwoVar {
A(u32) = 0, B(u32) = 1 }`): 8 bytes, align 4, tag `u8` at offset 0 (`0 | 1`),
payload `u32` at offset 4. -/
def twoVarEnumMrTy : Gen.Type := .Enum twoVarEnumVariants ⟨.Unsigned, ⟨1⟩⟩
    (.Branch ⟨0⟩ ⟨.Unsigned, ⟨1⟩⟩ .Invalid ⟨[((0, 1), .Known 0), ((1, 2), .Known 1)]⟩)
    ⟨8⟩ ⟨4⟩
/-- Anneal MIR type for `TwoVar` (`RigidTy.adt "ep2::TwoVar" []`). -/
@[reducible] def twoVarMirTy : MirAst.Ty := { kind := .adt "ep2::TwoVar" [], layoutIdx := 0 }
/-- Anneal `TypeLayout` for `TwoVar` (8 bytes, align 4, direct `u8` tag). -/
def twoVarMirLayout : TypeLayout :=
  { size := ⟨8⟩, align := ⟨4⟩, backendRepr := .memory, fields := .arbitrary [⟨0⟩] [0],
    variants := .multiple (.initialized (.int 8 false) ⟨0, 1⟩) 0 [], isUninhabited := false }
def twoVarLayouts : LayoutTable := { pointerBits := 64, isLittleEndian := true, entries := [twoVarMirLayout] }
/-- **C1 Universal Fragment Boundary
(`translateStatement_setDiscriminant_none`)**: `Translate.translateStatement`
returns `none` for every `StatementKind.setDiscriminant`. -/
theorem translateStatement_setDiscriminant_none
    (decls : List MirAst.LocalDecl) (p : MirAst.Place) (v : Nat) (span : String) (layouts : LayoutTable) :
    translateStatement decls { kind := .setDiscriminant p v, span := span } layouts = none := rfl
/-- **C1 Trusted Local Step Law
(`trusted_setDiscriminant_local_preserves_payload`)**: Executing
`StatementKind.setDiscriminant ⟨loc, []⟩ newVar` on an initialized enum local
`.aggregate oldVar fields` (with no active protectors) updates ONLY the
variant tag to `newVar`, preserves every payload field `fields` verbatim,
advances `stmtIdx` by 1, and invalidates conflicting borrows of `loc`. -/
theorem trusted_setDiscriminant_local_preserves_payload
    (s : MachineState) (loc oldVar newVar : Nat) (fields : List MirSemantics.Value)
    (locals' : List LocalSlot) (span : String) (decls : List MirAst.LocalDecl) (layouts : LayoutTable)
    (hget : get? s.frame.locals loc = some (.init (.aggregate oldVar fields)))
    (hset : set? s.frame.locals loc (.init (.aggregate newVar fields)) = some locals') (hprot : s.memory.activeProtectors = []) :
    evalStmt s { kind := .setDiscriminant (locPlace loc) newVar, span := span } decls layouts =
      MirStepNode.step (advanceStmt s locals' { s.memory with
            borrows := invalidateConflictingBorrows s.memory.borrows loc .none (length s.memory.callStack) }) := by
  simp only [evalStmt, locPlace, hget, evalSetDiscriminantLocal, hset, hprot]
/-- **C1 Trusted Active-Protector Conflict UB & Field-Projected
`SetDiscriminant` Law (`trusted_setDiscriminant_protector_and_field_proj`)**:
(1) Non-empty `activeProtectors` on a whole local faults with `.fail .ub` when
`hasProtectedWriteConflict = true` and steps otherwise; (2) field-projected
local `SetDiscriminant` checks resolved-projection protector conflicts and
updates the target field via `writePlaceValue`. -/
theorem trusted_setDiscriminant_protector_and_field_proj (s : MachineState) (loc idx oldVar newVar : Nat) (fty : MirAst.Ty)
    (rest : List MirAst.ProjectionElem) (fields : List MirSemantics.Value)
    (locals' locals₁ locals₂ : List LocalSlot) (ph : Nat) (pt : List Nat)
    (span : String) (decls : List MirAst.LocalDecl) (layouts : LayoutTable) :
    let depth := length s.memory.callStack
    let p : MirAst.Place := ⟨loc, .field idx fty :: rest⟩
    let resProj := resolveBorrowWriteLocalProj decls layouts locals₁ loc (.field idx fty :: rest)
    (get? s.frame.locals loc = some (.init (.aggregate oldVar fields)) →
      set? s.frame.locals loc (.init (.aggregate newVar fields)) = some locals' → s.memory.activeProtectors = ph :: pt →
      (hasProtectedWriteConflict s.memory.borrows (ph :: pt) loc .none [] 0 0 depth = true →
        evalStmt s { kind := .setDiscriminant (locPlace loc) newVar, span := span } decls layouts = MirStepNode.fail .ub) ∧
      (hasProtectedWriteConflict s.memory.borrows (ph :: pt) loc .none [] 0 0 depth = false →
        evalStmt s { kind := .setDiscriminant (locPlace loc) newVar, span := span } decls layouts =
          MirStepNode.step (advanceStmt s locals'
            { s.memory with borrows := invalidateConflictingBorrows s.memory.borrows loc .none depth }))) ∧
    (evalOperand s.frame.locals (.copy p) s.memory.borrows s.memory.globals layouts
        s.memory.callerLocals decls s.memory.callStack = .ok (.aggregate oldVar fields) locals₁ →
      (hasProtectedWriteConflict s.memory.borrows s.memory.activeProtectors loc .none resProj
          0 0 depth = true → evalStmt s { kind := .setDiscriminant p newVar, span := span } decls layouts = MirStepNode.fail .ub) ∧
      (hasProtectedWriteConflict s.memory.borrows s.memory.activeProtectors loc .none resProj 0 0 depth = false →
        writePlaceValue locals₁ s.memory.borrows p (.aggregate newVar fields) decls layouts s.memory.callStack = .ok locals₂ →
        evalStmt s { kind := .setDiscriminant p newVar, span := span } decls layouts =
          MirStepNode.step (advanceStmt s locals₂ { s.memory with
              borrows := invalidateConflictingBorrowsAtProj s.memory.borrows loc .none resProj 0 0 depth }))) := by
  intro depth p resProj
  refine ⟨?_, ?_⟩
  · intro hget hset hprot
    constructor <;> intro hConf <;>
      simp only [evalStmt, locPlace, hget, evalSetDiscriminantLocal, hset, hprot, depth, hConf]
  · intro hOp
    refine ⟨?_, ?_⟩
    · intro hConf; simp only [evalStmt, p, hOp, depth, resProj, hConf]
    · intro hNoConf hWr; simp only [evalStmt, p, hOp, depth, resProj, hNoConf, hWr]
/-- **C1 Trusted Dead/OOB Local UB Law
(`trusted_setDiscriminant_dead_or_oob_ub`)**: Executing
`StatementKind.setDiscriminant ⟨loc, []⟩ v` on a `.dead` or out-of-bounds
local faults with `MirStepNode.fail .ub`. -/
theorem trusted_setDiscriminant_dead_or_oob_ub
    (s : MachineState) (loc v : Nat) (span : String) (decls : List MirAst.LocalDecl) (layouts : LayoutTable)
    (hdead : get? s.frame.locals loc = some .dead ∨ get? s.frame.locals loc = none) :
    evalStmt s { kind := .setDiscriminant (locPlace loc) v, span := span } decls layouts = MirStepNode.fail .ub := by
  rcases hdead with h | h <;> simp [evalStmt, locPlace, h]
/-- **C1 Trusted `.uninit` Shell Behavior
(`setDiscriminant_uninit_shell_behavior`)**: On an `.uninit` whole local `loc`,
`evalStmt` delegates to `evalSetDiscriminantLocal s loc newVar .nil` when
`setDiscriminantUninitDeclOk decls loc = true` (enum/ADT declaration) and
returns `.unsupported` otherwise. -/
theorem setDiscriminant_uninit_shell_behavior (s : MachineState) (loc newVar : Nat) (span : String)
    (decls : List MirAst.LocalDecl) (layouts : LayoutTable) (huninit : get? s.frame.locals loc = some .uninit) :
    (setDiscriminantUninitDeclOk decls loc = true →
      evalStmt s { kind := .setDiscriminant (locPlace loc) newVar, span := span } decls layouts =
        evalSetDiscriminantLocal s loc newVar .nil) ∧ (setDiscriminantUninitDeclOk decls loc = false →
      evalStmt s { kind := .setDiscriminant (locPlace loc) newVar, span := span } decls layouts = MirStepNode.unsupported) := by
  constructor <;> intro h <;> simp [evalStmt, locPlace, huninit, h]
/-- **C1 MiniRust Polymorphic Dead-Local & Misaligned-Pointer UB Laws**
across BOTH `BasicMemory` (`Mach`) and `TreeBorrowsMemory` (`MachTB`). -/
theorem minirust_setDiscriminantM_dead_local_ub {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Machine M) (fr : StackFrame M) (ln : Gen.LocalName) (ty : Gen.Type) (v : Int) (hcur : curFrameM m = .ok fr)
    (hty : mapIndex fr.func.locals ln "self.cur_frame().func.locals[name]" = .ok ty) (hdead : mapGet fr.locals ln = none) :
    evalSetDiscriminantM m (.Local ln) v = .error (.ub "access to a dead local") := by
  unfold evalSetDiscriminantM evalPlaceM; simp only [hcur, hty, hdead, bind, Except.bind, ub]
theorem minirust_setDiscriminantM_misaligned_ub {M : Type} [Gen.Memory M] [MemoryOps M]
    (m m1 : Machine M) (dst : Gen.PlaceExpr) (place : Gen.Place M)
    (variants : Map Int Gen.Variant) (dty : Gen.IntType) (disc : Gen.Discriminator)
    (sz : LibSpecr.Size) (al : LibSpecr.Align) (v : Int) (hp : evalPlaceM m dst = .ok ((place, .Enum variants dty disc sz al), m1))
    (hmis : place.aligned = false) :
    evalSetDiscriminantM m dst v = .error (.ub "setting the discriminant of a place based on a misaligned pointer") := by
  unfold evalSetDiscriminantM; simp only [hp, hmis, Bool.not_false, ↓reduceIte, bind, Except.bind, ub]
/-- **C1 MiniRust Invalid-Discriminant & Non-Enum WF `specPanic` Boundary**:
Whereas Trusted faults with `.fail .ub` on a non-aggregate pointee, MiniRust
`evalSetDiscriminantM` treats missing variants and non-enum place types as
well-formedness violations (`specPanic`). -/
theorem minirust_setDiscriminantM_wf_panic {M : Type} [Gen.Memory M] [MemoryOps M]
    (m m1 : Machine M) (dst : Gen.PlaceExpr) (place : Gen.Place M) (v : Int) :
    (∀ variants dty disc sz al, evalPlaceM m dst = .ok ((place, .Enum variants dty disc sz al), m1) →
      place.aligned = true → mapGet variants v = none →
      evalSetDiscriminantM m dst v = .error (.specPanic s!"setting an invalid discriminant ({v})")) ∧
    (∀ it, evalPlaceM m dst = .ok ((place, .Int it), m1) → evalSetDiscriminantM m dst v =
        .error (.specPanic "setting the discriminant type of a non-enum contradicts well-formedness")) := by
  refine ⟨fun _ _ _ _ _ hp hal hnone => ?_, fun _ hp => ?_⟩
  · unfold evalSetDiscriminantM
    simp only [hp, hal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hnone, bind, Except.bind, specPanic]
  · unfold evalSetDiscriminantM; simp only [hp, bind, Except.bind, specPanic]
/-- `Classical.choice`-free polymorphic decode bridge for `twoVarEnumMrTy`
across `Mach` and `MachTB`: after byte 0 is overwritten to `tag ∈ {0, 1}` with
arbitrary padding bytes `p1, p2, p3` (including `.Uninit`) and `u32` payload
`bits < 2 ^ 32` at offsets `4..8`, `Type.decodeM` recovers `.Variant tag
(.Tuple [.Int (intFromBits bits u32)])`. -/
theorem decodeM_twoVarEnumMrTy {M : Type} [Gen.Memory M] [MemoryOps M]
    (tag bits : Nat) (htag : tag = 0 ∨ tag = 1) (hBits : bits < 2 ^ 32) (p1 p2 p3 : AbstractByte (Gen.Memory.Provenance M)) :
    let bs : List (AbstractByte (Gen.Memory.Provenance M)) :=
      [.Init (UInt8.ofNat tag) none, p1, p2, p3] ++ (leBytes bits 4).map (fun b => .Init b none)
    Type.decodeM (M := M) twoVarEnumMrTy bs = .ok (some (.Variant (Int.ofNat tag) (.Tuple [.Int (intFromBits bits u32)]))) := by
  intro bs
  have hDecU32 : Type.decodeIntM (M := M) u32 ((leBytes bits 4).map (fun b => .Init b none)) =
      .ok (some (.Int (intFromBits bits u32))) :=
    decodeIntM_leBytes (M := M) u32 (by decide) bits hBits
  have hSub4 : subsliceWithLength bs 4 4 = .ok ((leBytes bits 4).map (fun b => .Init b none)) := rfl
  have hBsLen : bs.length = 8 := rfl
  rcases htag with rfl | rfl <;> (
    unfold twoVarEnumMrTy Type.decodeM; rw [ite_eq_right_iff.mpr (fun hn => absurd hBsLen hn)]
    dsimp only [decodeDiscriminantM, decodeDiscriminantChildrenM, twoVarEnumVariants,
      Type.decodeVariantM, Type.decodeFieldsM, TupleHeadLayout.head_size_and_align,
      Type.layout, LayoutStrategy.expect_size, u32MrTy, bs, bind, Except.bind, pure, Except.pure]
    change (do
      let valOpt ← Type.decodeIntM (M := M) u32 ((leBytes bits 4).map (fun b => .Init b none))
      match valOpt with
      | some v => pure (some (Gen.Value.Variant _ (.Tuple [v])))
      | none => pure none) = _
    rw [hDecU32]; rfl)
/-- **C1 Polymorphic Direct-Tagged `twoVarEnumMrTy` Tag-Write Law (`Mach` &
`MachTB`)**: For any `tag ∈ {0, 1}`, `evalSetDiscriminantM` on
`twoVarEnumMrTy` performs a single 1-byte store of `[.Init (UInt8.ofNat tag)
none]` at offset `0`, leaving offsets `1..7` (including the `u32` payload at
`4..8`) untouched. -/
theorem minirust_setDiscriminantM_twoVar_tagStore {M : Type} [Gen.Memory M] [MemoryOps M]
    (m m1 : Machine M) (dst : Gen.PlaceExpr) (place : Gen.Place M) (tag : Nat) (htag : tag = 0 ∨ tag = 1)
    (hp : evalPlaceM m dst = .ok ((place, twoVarEnumMrTy), m1)) (hal : place.aligned = true)
    (ptr0 : ThinPointer (Gen.Memory.Provenance M))
    (hoff : ptrOffsetInboundsM m1 place.ptr.thin_pointer 0 = .ok ptr0) (cm' : Gen.ConcurrentMemory M)
    (hst : ConcurrentMemory.store m1.mem ptr0 [.Init (UInt8.ofNat tag) none] ⟨1⟩ .None = .ok cm') :
    evalSetDiscriminantM m dst (Int.ofNat tag) = .ok { m1 with mem := cm' } := by
  have hAux : ∀ (t : Nat), Type.encodeIntM (M := M) ⟨.Unsigned, ⟨1⟩⟩ (.Int (Int.ofNat t)) = .ok [.Init (UInt8.ofNat t) none] →
      mapGet twoVarEnumVariants (Int.ofNat t) =
        some ⟨.Tuple [(⟨4⟩, u32MrTy)] ⟨⟨8⟩, ⟨4⟩, none⟩ none, ⟨[(⟨0⟩, (⟨.Unsigned, ⟨1⟩⟩, Int.ofNat t))]⟩⟩ →
      ConcurrentMemory.store m1.mem ptr0 [.Init (UInt8.ofNat t) none] ⟨1⟩ .None = .ok cm' →
      evalSetDiscriminantM m dst (Int.ofNat t) = .ok { m1 with mem := cm' } := by
    intro t hEnc hMap hSt; unfold evalSetDiscriminantM; rw [hp, ok_bind]; dsimp only [twoVarEnumMrTy]
    rw [hal]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hMap, encodeDiscriminantM,
      List.foldlM_cons, List.foldlM_nil, ok_bind, pure, Except.pure, bind, Except.bind]
    rw [hEnc]; dsimp only []; rw [show ((0 : Nat) : Int) = 0 from rfl, hoff]; dsimp only []; rw [hSt]
  rcases htag with rfl | rfl
  · exact hAux 0 rfl rfl hst
  · exact hAux 1 rfl rfl hst
/-- **C1 Universal Deref Step, `.uninit` Deref, & Dangling/OOB UB Law
(`trusted_setDiscriminant_deref_step_and_ub`)**: Invoking real `evalStmt` and
`evalSetDiscriminantDerefWrite` on `p = ⟨ptrLoc, .deref :: rest⟩`: (1) valid
deref updates tag preserving payload; (2) `.uninit` active-frame deref writes a
tag shell; (3) non-aggregate pointees fault with `.ub`; (4) unbacked/OOB
pointers fault with `.ub`. -/
theorem trusted_setDiscriminant_deref_step_and_ub (s : MachineState) (ptrLoc oldVar newVar : Nat)
    (rest : List MirAst.ProjectionElem) (fields : List MirSemantics.Value) (locals₁ locals₂ : List LocalSlot) (span : String)
    (decls : List MirAst.LocalDecl) (layouts : LayoutTable) :
    let p : MirAst.Place := ⟨ptrLoc, .deref :: rest⟩
    -- (1) Valid deref SetDiscriminant preserves payload via
    -- evalSetDiscriminantDerefWrite
    (evalOperand s.frame.locals (.copy p) s.memory.borrows s.memory.globals layouts
        s.memory.callerLocals decls s.memory.callStack = .ok (.aggregate oldVar fields) locals₁ →
      evalStmt s { kind := .setDiscriminant p newVar, span := span } decls layouts =
        evalSetDiscriminantDerefWrite s locals₁ p rest (.aggregate newVar fields) decls layouts) ∧
    (evalPlaceWrite locals₁ s.memory.borrows p (.aggregate newVar fields)
        s.memory.activeProtectors decls layouts s.memory.callStack = .ok locals₂ →
      derefWriteTreeUB locals₁ s.memory.borrows p = false → derefWriteUnionProtectorUB decls layouts locals₁ s.memory.borrows
        s.memory.activeProtectors p rest s.memory.callStack = false →
      evalSetDiscriminantDerefWrite s locals₁ p rest (.aggregate newVar fields) decls layouts =
        MirStepNode.step (advanceStmt s locals₂ { s.memory with
              borrows := invalidateDerefWriteBorrowsWithLayouts decls layouts locals₁ s.memory.borrows p rest s.memory.callStack })) ∧
    -- (2) `.uninit` active-frame deref initializes tag shell via
    -- evalSetDiscriminantDerefWrite
    (∀ ptrVal sz entry, evalOperand s.frame.locals (.copy ⟨ptrLoc, [.deref]⟩) s.memory.borrows s.memory.globals
        layouts s.memory.callerLocals decls s.memory.callStack = .ub →
      get? s.frame.locals ptrLoc = some (.init (.ptr ptrVal sz)) →
      lookupBorrow s.memory.borrows ptrVal.tag = some entry → entry.perm = .active →
      entry.targetProjection = [] → ptrVal.offsetBytes = 0 → activeFrameSlot? s.frame.locals s.memory.callStack entry.targetFrameDepth
        entry.targetLocal = some .uninit →
      placeTyResolved decls layouts ⟨ptrLoc, [.deref]⟩ = some twoVarMirTy →
      setDiscriminantUninitDeclOk decls entry.targetLocal = true →
      evalStmt s { kind := .setDiscriminant ⟨ptrLoc, [.deref]⟩ newVar, span := span } decls layouts =
        evalSetDiscriminantDerefWrite s s.frame.locals ⟨ptrLoc, [.deref]⟩ [] (.aggregate newVar []) decls layouts) ∧
    -- (3) Non-aggregate pointee faults with UB
    (∀ sc, evalOperand s.frame.locals (.copy p) s.memory.borrows s.memory.globals layouts
        s.memory.callerLocals decls s.memory.callStack = .ok (.scalar sc) locals₁ →
      evalStmt s { kind := .setDiscriminant p newVar, span := span } decls layouts = MirStepNode.fail .ub) ∧
    -- (4) Unbacked/OOB pointer (`lookupBorrow = none` & `evalOperand = .ub`)
    -- faults with UB
    (∀ ptrVal sz, evalOperand s.frame.locals (.copy ⟨ptrLoc, [.deref]⟩) s.memory.borrows s.memory.globals
        layouts s.memory.callerLocals decls s.memory.callStack = .ub →
      get? s.frame.locals ptrLoc = some (.init (.ptr ptrVal sz)) → lookupBorrow s.memory.borrows ptrVal.tag = none →
      evalStmt s { kind := .setDiscriminant ⟨ptrLoc, [.deref]⟩ newVar, span := span } decls layouts = MirStepNode.fail .ub) := by
  intro p
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hOp; simp only [evalStmt, p, hOp]
  · intro hWr hTree hUnion
    unfold evalSetDiscriminantDerefWrite; simp only [hWr, hTree, hUnion, Bool.or_self]
  · intro ptrVal sz entry hUb hSlot hB hPerm hProj hOff hAct hPtTy hDeclOk
    simp only [evalStmt, hUb, hSlot, hB, hPerm, hProj, hOff, Nat.beq_refl, hAct, hPtTy, twoVarMirTy, hDeclOk, Bool.and_self]
  · intro sc hOp; simp only [evalStmt, p, hOp]
  · intro ptrVal sz hUb hSlot hNoB; simp only [evalStmt, hUb, hSlot, hNoB]
/-- **C1 Coupled Two-Sided Step Simulation, Symmetric Byte-Level Payload
Preservation on BOTH `Mach` & `MachTB`, & `MachTB.wfLive`
(`setDiscriminant_twoVar_coupled_lockstep_and_wfLive`)**: Simultaneously
relates Trusted `evalStmt` (`evalSetDiscriminantLocal`), MiniRust
`BasicMemory` `Interp.evalStatement` (`Mach`), AND MiniRust
`TreeBorrowsMemory` `evalStatementM` (`MachTB`): on BOTH `Mach`
(`bm_store_byte0_frame`) AND `MachTB` (`tbm_store_byte0_frame`), ONLY byte
`0` becomes `.Init (UInt8.ofNat tag) none`, trailing bytes `payloadTail` /
`payloadTailTB` at `1..7` remain byte-for-byte identical, `MachTB` accesses
`extra.root` solely on `[0, 1)`, and `MachTB.wfLive` is preserved! -/
theorem setDiscriminant_twoVar_coupled_lockstep_and_wfLive
    (s : MachineState) (loc oldVar tag : Nat) (fields : List MirSemantics.Value)
    (locals' : List LocalSlot) (span : String) (decls : List MirAst.LocalDecl) (layouts : LayoutTable)
    (mBM mBM1 : Mach) (dst : Gen.PlaceExpr) (placeBM : Gen.Place BM) (ptrBM0 : Ptr) (idBM : Gen.AllocId) (allocBM : Gen.Allocation)
    (oldByte0 : Byte) (payloadTail : List Byte) (allocsBM' : List Gen.Allocation) (mTB mTB1 : MachTB) (placeTB : Gen.Place TBM)
    (ptrTB0 : ThinPointer TreeBorrowsProvenance) (idTB : Gen.AllocId) (pathTB : Gen.Path)
    (allocTB : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra) (rootTB' : Gen.Node)
    (oldByteTB0 : AbstractByte TreeBorrowsProvenance) (payloadTailTB : List (AbstractByte TreeBorrowsProvenance))
    (allocsTB' : List (Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra)) (htag : tag = 0 ∨ tag = 1)
    (hget : get? s.frame.locals loc = some (.init (.aggregate oldVar fields)))
    (hset : set? s.frame.locals loc (.init (.aggregate tag fields)) = some locals') (hprot : s.memory.activeProtectors = [])
    (hpBM : evalPlaceM mBM dst = .ok ((placeBM, twoVarEnumMrTy), mBM1)) (halBM : placeBM.aligned = true)
    (hoffBM : ptrOffsetInboundsM mBM1 placeBM.ptr.thin_pointer 0 = .ok ptrBM0)
    (hChkBM : BM.check_ptr mBM1.mem.memory ptrBM0 ⟨1⟩ = .ok (some (idBM, (), ⟨0⟩)))
    (hIdxBM : listIndex mBM1.mem.memory.allocations idBM._0 "self.allocations[id.0]" = .ok allocBM)
    (hDataBM : allocBM.data = oldByte0 :: payloadTail) (hSetBM : listSet mBM1.mem.memory.allocations idBM._0
      { allocBM with data := .Init (UInt8.ofNat tag) none :: payloadTail } "set" = .ok allocsBM')
    (hwfTB : MachTB.wfLive mTB) (hpTB : evalPlaceM mTB dst = .ok ((placeTB, twoVarEnumMrTy), mTB1)) (halTB : placeTB.aligned = true)
    (hoffTB : ptrOffsetInboundsM mTB1 placeTB.ptr.thin_pointer 0 = .ok ptrTB0)
    (hChkTB : BasicMemory.check_ptr mTB1.mem.memory.mem ptrTB0 ⟨1⟩ = .ok (some (idTB, pathTB, ⟨0⟩)))
    (hIdxTB : listIndex mTB1.mem.memory.mem.allocations idTB._0 "self.allocations[id.0]" = .ok allocTB)
    (hNodeTB : Node.access allocTB.extra.root (some pathTB) .Write ⟨0⟩ ⟨1⟩ = .ok rootTB')
    (hDataTB : allocTB.data = oldByteTB0 :: payloadTailTB) (hSetTB : listSet mTB1.mem.memory.mem.allocations idTB._0
      { allocTB with data := .Init (UInt8.ofNat tag) none :: payloadTailTB, extra := { root := rootTB' } } "set" = .ok allocsTB') :
    let accBM : Gen.Access := ⟨.Store, .None, ptrBM0.addr, ⟨1⟩⟩
    let accTB : Gen.Access := ⟨.Store, .None, ptrTB0.addr, ⟨1⟩⟩
    let cmTB' : Gen.ConcurrentMemory TBM :=
      { memory := { mTB1.mem.memory with mem := { mTB1.mem.memory.mem with allocations := allocsTB' } },
        accesses := mTB1.mem.accesses ++ [accTB] }
    evalStmt s { kind := .setDiscriminant (locPlace loc) tag, span := span } decls layouts =
      MirStepNode.step (advanceStmt s locals' { s.memory with
          borrows := invalidateConflictingBorrows s.memory.borrows loc .none (length s.memory.callStack) }) ∧
    Interp.evalStatement mBM (.SetDiscriminant dst (Int.ofNat tag)) =
      .ok { mBM1 with
            mem := { memory := { mBM1.mem.memory with allocations := allocsBM' }, accesses := mBM1.mem.accesses ++ [accBM] } } ∧
    evalStatementM mTB (.SetDiscriminant dst (Int.ofNat tag)) = .ok { mTB1 with mem := cmTB' } ∧
    MachTB.wfLive { mTB1 with mem := cmTB' } := by
  intro accBM accTB cmTB'
  have hMemBM := bm_store_byte0_frame mBM1.mem.memory ptrBM0 oldByte0 (.Init (UInt8.ofNat tag) none)
    payloadTail idBM allocBM allocsBM' hChkBM hIdxBM hDataBM hSetBM
  have hStoreBM : ConcurrentMemory.store mBM1.mem ptrBM0 [.Init (UInt8.ofNat tag) none] ⟨1⟩ .None =
      .ok { memory := { mBM1.mem.memory with allocations := allocsBM' }, accesses := mBM1.mem.accesses ++ [accBM] } := by
    change (do
      let memory ← BM.store mBM1.mem.memory ptrBM0 [.Init (UInt8.ofNat tag) none] ⟨1⟩
      pure ({ memory, accesses := mBM1.mem.accesses ++ [accBM] } : Gen.ConcurrentMemory BM)) = _
    rw [hMemBM]; rfl
  have hMemTB := tbm_store_byte0_frame mTB1.mem.memory ptrTB0 oldByteTB0
    (.Init (UInt8.ofNat tag) none) payloadTailTB idTB pathTB allocTB rootTB' allocsTB'
    hChkTB hIdxTB hNodeTB hDataTB hSetTB
  have hStoreTB : ConcurrentMemory.store mTB1.mem ptrTB0 [.Init (UInt8.ofNat tag) none] ⟨1⟩ .None = .ok cmTB' := by
    change (do
      let memory ← TreeBorrowsMemory.store mTB1.mem.memory ptrTB0 [.Init (UInt8.ofNat tag) none] ⟨1⟩
      pure ({ memory, accesses := mTB1.mem.accesses ++ [accTB] } : Gen.ConcurrentMemory TBM)) = _
    rw [hMemTB]; rfl
  have hBM : evalStatementM mBM (.SetDiscriminant dst (Int.ofNat tag)) =
      .ok { mBM1 with
            mem := { memory := { mBM1.mem.memory with allocations := allocsBM' }, accesses := mBM1.mem.accesses ++ [accBM] } } :=
    minirust_setDiscriminantM_twoVar_tagStore mBM mBM1 dst placeBM tag htag hpBM halBM ptrBM0 hoffBM _ hStoreBM
  have hTB : evalStatementM mTB (.SetDiscriminant dst (Int.ofNat tag)) = .ok { mTB1 with mem := cmTB' } :=
    minirust_setDiscriminantM_twoVar_tagStore mTB mTB1 dst placeTB tag htag hpTB halTB ptrTB0 hoffTB cmTB' hStoreTB
  refine ⟨trusted_setDiscriminant_local_preserves_payload s loc oldVar tag fields locals'
            span decls layouts hget hset hprot, ?_, hTB, evalStatementM_tb_wfLive hwfTB hTB⟩
  rw [← evalStatementM_bm_eq]; exact hBM

/-! ### C1 Concrete Positive, Deref, `.uninit`, and Fault Witnesses (`Mach` &
`MachTB`) -/
def c1SetDiscrLocalMir : MirAst.CapturedMir := mkMirBody "ep2::c1_set_discr_local" [mkDecl twoVarMirTy, mkDecl twoVarMirTy] 1
    [mkBb [mkSt (.setDiscriminant (locPlace 1) 1)] .return_] twoVarLayouts
def c1SetDiscrLocalMrFn : Gen.Function :=
  mkMrFn [(localName 0, twoVarEnumMrTy), (localName 1, twoVarEnumMrTy)] [localName 1] (localName 0)
    [(bbName 0, ⟨[.SetDiscriminant (.Local (localName 1)) 1], .Return, .Regular⟩)]
def c1SetDiscrLocalProg : Gen.Program := mkMrProg [(fnName 0, c1SetDiscrLocalMrFn)]
def c1LocalInitBytes : List Byte := [.Init 0 none, .Uninit, .Uninit, .Uninit, .Init 42 none, .Init 0 none, .Init 0 none, .Init 0 none]
def c1LocalExpectedBytes : List Byte :=
  [.Init 1 none, .Uninit, .Uninit, .Uninit, .Init 42 none, .Init 0 none, .Init 0 none, .Init 0 none]
def c1LocalMach : Mach := mkMrMach c1SetDiscrLocalProg
    [mkStackAlloc 128 (List.replicate 8 .Uninit) 4, mkStackAlloc 256 c1LocalInitBytes 4]
    [mkRootFrame c1SetDiscrLocalMrFn [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })]]
/-- **C1 Positive Witness (`c1_setDiscriminant_local_three_way_witness`)**:
On `stepMirFn`, `Interp.step`, and `Interp.stepTB` (with `MachTB.wfLive`),
`SetDiscriminant` updates ONLY tag (`0 → 1`) while preserving payload `42`. -/
theorem c1_setDiscriminant_local_three_way_witness :
    let s0 : MachineState := initMachineState c1SetDiscrLocalMir [.aggregate 0 [.scalar ⟨42, 4⟩]]
    (match stepMirFn c1SetDiscrLocalMir s0 with
     | .tau (.running s1) =>
       s1.frame.stmtIdx = 1 ∧ get? s1.frame.locals 1 = some (.init (.aggregate 1 [.scalar ⟨42, 4⟩]))
     | _ => False) ∧
    (∃ m1, Interp.step c1LocalMach = .ok m1 ∧ (m1.mem.memory.allocations[1]?.map (·.data),
       m1.threads[0]?.bind (fun t => t.stack[0]?.map (·.next_stmt))) =
      (some c1LocalExpectedBytes, some 1)) ∧
    (∃ m1, Interp.stepTB (liftMachToTB c1LocalMach) = .ok m1 ∧ MachTB.wfLive m1 ∧
      (m1.mem.memory.mem.allocations[1]?.map (fun a => a.data.map projByteTB),
       m1.threads[0]?.bind (fun t => t.stack[0]?.map (·.next_stmt))) =
      (some (c1LocalExpectedBytes.map (projByteTB ∘ liftByteTB)), some 1)) :=
  ⟨⟨rfl, rfl⟩, ok_of_map_toOption (by decide +kernel), ok_stepTB_wfLive (by decide +kernel)⟩
/-- Concrete deref `SetDiscriminant` witness (`(*_2) = variant 1`) across
Trusted, `Mach`, and `MachTB` (with payload preservation & `MachTB.wfLive`). -/
def c1DerefMir : MirAst.CapturedMir := mkMirBody "ep2::c1_set_discr_deref" [mkDecl twoVarMirTy, mkDecl twoVarMirTy,
     mkDecl { kind := .rawPtr .mut twoVarMirTy.kind, layoutIdx := 0 }] 1
    [mkBb [mkSt (.storageLive 2), mkSt (.assign (locPlace 2) (.rawPtr .mut (locPlace 1))),
           mkSt (.setDiscriminant (locPlace 2 [.deref]) 1)] .return_] twoVarLayouts
def c1DerefMrFn : Gen.Function := mkMrFn [(localName 0, twoVarEnumMrTy), (localName 1, twoVarEnumMrTy), (localName 2, thinRawPtrTy)]
    [localName 1] (localName 0) [(bbName 0, ⟨[.Assign (.Local (localName 2)) (.AddrOf (.Local (localName 1)) (.Raw .None)),
        .SetDiscriminant (.Deref (.Load (.Local (localName 2))) twoVarEnumMrTy) 1], .Return, .Regular⟩)]
def c1DerefMach : Mach := mkMrMach (mkMrProg [(fnName 0, c1DerefMrFn)])
    [mkStackAlloc 128 (List.replicate 8 .Uninit) 4, mkStackAlloc 256 c1LocalInitBytes 4,
     mkStackAlloc 384 (List.replicate 8 .Uninit) 8]
    [mkRootFrame c1DerefMrFn [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) }), (localName 2, { addr := 384, provenance := some (⟨2⟩, ()) })]]
theorem c1_setDiscriminant_deref_three_way_witness :
    let s0 := initMachineState c1DerefMir [.aggregate 0 [.scalar ⟨42, 4⟩]]
    (match stepMirFn c1DerefMir s0 with
     | .tau (.running s1) => (match stepMirFn c1DerefMir s1 with
       | .tau (.running s2) => (match stepMirFn c1DerefMir s2 with
         | .tau (.running s3) =>
           s3.frame.stmtIdx = 3 ∧ get? s3.frame.locals 1 = some (.init (.aggregate 1 [.scalar ⟨42, 4⟩]))
         | _ => False) | _ => False) | _ => False) ∧
    (∃ m2, Interp.steps 2 c1DerefMach = .ok m2 ∧ m2.mem.memory.allocations[1]?.map (·.data) = some c1LocalExpectedBytes) ∧
    (∃ m2, Interp.stepsTB 2 (liftMachToTB c1DerefMach) = .ok m2 ∧ MachTB.wfLive m2 ∧
      m2.mem.memory.mem.allocations[1]?.map (fun a => a.data.map projByteTB) =
        some (c1LocalExpectedBytes.map (projByteTB ∘ liftByteTB))) :=
  ⟨⟨rfl, rfl⟩, ok_of_map_toOption (by decide +kernel), ok_stepsTB_wfLive (by decide +kernel)⟩
/-- Concrete `.uninit` shell C1 witness across Trusted, `Mach`, and `MachTB`. -/
def c1UninitMach : Mach := mkMrMach c1SetDiscrLocalProg
    [mkStackAlloc 128 (List.replicate 8 .Uninit) 4, mkStackAlloc 256 (List.replicate 8 .Uninit) 4]
    [mkRootFrame c1SetDiscrLocalMrFn [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })]]
theorem c1_setDiscriminant_uninit_shell_witness :
    let s0 : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] },
        memory := (initMachineState c1SetDiscrLocalMir []).memory }
    (match stepMirFn c1SetDiscrLocalMir s0 with
     | .tau (.running s1) => get? s1.frame.locals 1 = some (.init (.aggregate 1 [])) | _ => False) ∧
    (∃ m1, Interp.step c1UninitMach = .ok m1 ∧
      m1.mem.memory.allocations[1]?.map (·.data) = some (.Init 1 none :: List.replicate 7 .Uninit)) ∧
    Type.decode twoVarEnumMrTy (.Init 1 none :: List.replicate 7 .Uninit) = .ok none ∧
    (∃ m1, Interp.stepTB (liftMachToTB c1UninitMach) = .ok m1 ∧ MachTB.wfLive m1 ∧
      m1.mem.memory.mem.allocations[1]?.map (fun a => a.data.map projByteTB) =
        some (TBByteOutcome.initNoProv 1 :: List.replicate 7 TBByteOutcome.uninit)) :=
  ⟨rfl, ok_of_map_toOption (by decide +kernel), rfl, ok_stepTB_wfLive (by decide +kernel)⟩
/-- Concrete dead-local UB C1 witness across Trusted, `Mach`, and `MachTB`. -/
def c1DeadLocalMach : Mach := mkMrMach c1SetDiscrLocalProg [mkStackAlloc 128 (List.replicate 8 .Uninit) 4]
    [mkRootFrame c1SetDiscrLocalMrFn [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) })]]
theorem c1_setDiscriminant_dead_local_ub_witness :
    let s0 : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .dead] },
        memory := (initMachineState c1SetDiscrLocalMir []).memory }
    stepMirFn c1SetDiscrLocalMir s0 = MirStepNode.fail .ub ∧ Interp.step c1DeadLocalMach = .error (.ub "access to a dead local") ∧
    Interp.stepTB (liftMachToTB c1DeadLocalMach) = .error (.ub "access to a dead local") :=
  ⟨rfl, eq_error_ub_of_interpUbMsg (by decide +kernel), eq_error_ub_of_interpUbMsg (by decide +kernel)⟩
/-- Concrete misaligned-pointer, OOB-deref, & frozen-borrow UB witness for C1
across Trusted, `Mach`, and `MachTB` (including `Mach` vs `MachTB` `Frozen`
shared-reference `SetDiscriminant` UB contrast!). -/
def c1MisalignedMach : Mach :=
  let fn := mkMrFn [(localName 0, twoVarEnumMrTy), (localName 1, thinRawPtrTy)] [] (localName 0)
    [(bbName 0, ⟨[.SetDiscriminant (.Deref (.Constant (.PointerWithoutProvenance 257) thinRawPtrTy)
        twoVarEnumMrTy) 1], .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)]) [mkStackAlloc 128 (List.replicate 8 .Uninit) 4, mkStackAlloc 256 c1LocalInitBytes 4]
    [mkRootFrame fn [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) })]]
def c1FrozenRefMach : Mach :=
  let ptInfo : Gen.PointeeInfo :=
    { layout := .Sized ⟨8⟩ ⟨4⟩, inhabited := true, unsafe_cells := .Sized [], freeze := true, unpin := true }
  let sharedTwoVarRefPt : Gen.PtrType := .Ref (translateMutbl .not) ptInfo
  let fn := mkMrFn [(localName 0, twoVarEnumMrTy), (localName 1, twoVarEnumMrTy),
     (localName 2, .Ptr sharedTwoVarRefPt)] [] (localName 0)
    [(bbName 0, ⟨[.Assign (.Local (localName 2)) (.AddrOf (.Local (localName 1)) sharedTwoVarRefPt),
        .Validate (.Local (localName 2)) false,
        .SetDiscriminant (.Deref (.Load (.Local (localName 2))) twoVarEnumMrTy) 1], .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)]) [mkStackAlloc 128 (List.replicate 8 .Uninit) 4, mkStackAlloc 256 c1LocalInitBytes 4,
     mkStackAlloc 384 (List.replicate 8 .Uninit) 8]
    [mkRootFrame fn [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
       (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) }), (localName 2, { addr := 384, provenance := some (⟨2⟩, ()) })]]
theorem c1_setDiscriminant_misaligned_and_frozen_ub_witness :
    let sFrozen : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 2, locals := [.uninit, .init (.aggregate 0 [.scalar ⟨42, 4⟩]),
                              .init (.ptr { allocId := 1, offsetBytes := 0 } 8)] }
        memory := { (initMachineState c1DerefMir []).memory with
                    borrows := [{ tag := 1, targetLocal := 1, targetProjection := [], perm := .frozen, targetFrameDepth := 0 }] } }
    let sOob : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 2, locals := [.uninit, .init (.aggregate 0 [.scalar ⟨42, 4⟩]),
                              .init (.ptr { allocId := 99, offsetBytes := 16 } 8)] }
        memory := (initMachineState c1DerefMir []).memory }
    let oobMach : Mach :=
      let fn := mkMrFn [(localName 0, twoVarEnumMrTy), (localName 1, thinRawPtrTy)] [] (localName 0)
        [(bbName 0, ⟨[.SetDiscriminant (.Deref (.Load (.Local (localName 1))) twoVarEnumMrTy) 1], .Return, .Regular⟩)]
      mkMrMach (mkMrProg [(fnName 0, fn)]) [mkStackAlloc 128 (List.replicate 8 .Uninit) 4, mkStackAlloc 256 c1LocalInitBytes 4,
         mkStackAlloc 384 (ptrBytes 264 (some (⟨1⟩, ()))) 8]
        [mkRootFrame fn [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
                         (localName 1, { addr := 384, provenance := some (⟨2⟩, ()) })]]
    stepMirFn c1DerefMir sFrozen = MirStepNode.fail .ub ∧ (∃ m3, Interp.steps 3 c1FrozenRefMach = .ok m3 ∧
      m3.mem.memory.allocations[1]?.map (·.data) = some c1LocalExpectedBytes) ∧
    Interp.stepsTB 3 (liftMachToTB c1FrozenRefMach) = .error (.ub "Tree Borrows: local write of Frozen reference") ∧
    stepMirFn c1DerefMir sOob = MirStepNode.fail .ub ∧ Interp.step c1MisalignedMach =
      .error (.ub "setting the discriminant of a place based on a misaligned pointer") ∧
    Interp.stepTB (liftMachToTB c1MisalignedMach) = .error (.ub "setting the discriminant of a place based on a misaligned pointer") ∧
    Interp.step oobMach = .error (.ub "dereferencing pointer outside the bounds of its allocation") ∧
    Interp.stepTB (liftMachToTB oobMach) = .error (.ub "dereferencing pointer outside the bounds of its allocation") :=
  ⟨rfl, ok_of_map_toOption (by decide +kernel), eq_error_ub_of_interpUbMsg (by decide +kernel), rfl,
   eq_error_ub_of_interpUbMsg (by decide +kernel), eq_error_ub_of_interpUbMsg (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel), eq_error_ub_of_interpUbMsg (by decide +kernel)⟩

/-! ## §2 (`C2`): `TerminatorKind.unwindResume` (`Mach` & `MachTB`) -/
/-- **C2 Fragment Boundary (`translateTerminator_unwindResume_none`)**:
`Translate.translateTerminator` rejects `.unwindResume`. -/
theorem translateTerminator_unwindResume_none (layouts : LayoutTable) (decls : List MirAst.LocalDecl) (span : String) :
    translateTerminator layouts decls { kind := .unwindResume, span := span } = none := rfl
/-- **C2a Trusted `.cleanup` Step Law**: popping a callee whose caller
registered `.cleanup cleanupBb` restores `caller.frame` at `(cleanupBb, 0)`,
restores `caller`'s protectors, and disables callee-frame borrows above
`length rest`. -/
theorem trusted_unwindResume_cleanup_step (s : MachineState) (caller : SavedCallerFrame) (rest : List SavedCallerFrame)
    (cleanupBb : Nat) (span : String) (curBody : Option CapturedMir)
    (hStack : s.memory.callStack = caller :: rest) (hAction : caller.returnUnwind = .cleanup cleanupBb) :
    MirSemantics.evalTerminator s { kind := .unwindResume, span := span } curBody = MirStepNode.step
        { frame := { caller.frame with blockIdx := cleanupBb, stmtIdx := 0 },
          memory := { s.memory with
                      callStack := rest, activeCallee := .some caller.callerBody, activeProtectors := restoreCallerProtectors caller,
                      borrows := disableFramesAbove s.memory.borrows (length rest) } } := by
  simp only [MirSemantics.evalTerminator, hStack, unwindFromCallStack, hAction]
/-- Closed-form memory state produced by popping `conts` consecutive
`UnwindAction.continue_` caller frames in `unwindFromCallStack`. -/
def unwindContinueChainMem : List SavedCallerFrame → List SavedCallerFrame → MirSemantics.Memory → MirSemantics.Memory
  | [], _, mem => mem
  | caller :: rest, tail, mem =>
    unwindContinueChainMem rest tail
      { mem with
        callStack := rest ++ tail, activeCallee := .some caller.callerBody, activeProtectors := restoreCallerProtectors caller }
/-- **C2b Exact Closed-Form `.continue_` Multi-Frame Big-Step Law & Coupled
`1 : k + 1` MiniRust Step Induction (`Mach` & `MachTB`)**. -/
theorem trusted_unwindFromCallStack_continue_chain :
    ∀ (conts : List SavedCallerFrame) (tail : List SavedCallerFrame) (mem : MirSemantics.Memory),
      (∀ c ∈ conts, c.returnUnwind = .continue_) → unwindFromCallStack (conts ++ tail) mem =
        unwindFromCallStack tail (unwindContinueChainMem conts tail mem)
  | [], _, _, _ => rfl
  | c :: cs, tail, mem, hcont => by
    have hc : c.returnUnwind = .continue_ := hcont c (List.mem_cons_self ..)
    have hcs : ∀ x ∈ cs, x.returnUnwind = .continue_ := fun x hx => hcont x (List.mem_cons_of_mem c hx)
    simp only [List.cons_append, unwindFromCallStack, hc, unwindContinueChainMem]
    exact trusted_unwindFromCallStack_continue_chain cs tail _ hcs
/-- Bundled witness that `m` takes a genuine MiniRust `.ResumeUnwind` step to
`mAfter` (`deallocAllM` + `ConcurrentMemory.end_call` + frame pop +
`jumpToBlockM ubBb` + data-race check). -/
structure ResumeUnwindStepM {M : Type} [Gen.Memory M] [MemoryOps M]
    (m mAfter : Machine M) : Type where
  t : Gen.Thread M
  fr : StackFrame M
  fr1 : StackFrame M
  blk : Gen.BasicBlock
  threads' : List (Gen.Thread M)
  cm1 : Gen.ConcurrentMemory M
  cm2 : Gen.ConcurrentMemory M
  nextBlock : Option Gen.BbName
  ubBb : Gen.BbName
  retPtr : ThinPointer (Gen.Memory.Provenance M)
  hEnabled : m.threads.any (fun th => decide (th.state = .Enabled)) = true
  hPick : pickActiveThreadM { m with mem := { m.mem with accesses := [] } } = .ok m.active_thread
  hTid : activeThreadM { m with mem := { m.mem with accesses := [] } } = .ok t
  hLast : t.stack.getLast? = some fr
  hBlk : mapIndex fr.func.blocks fr.next_block "frame.func.blocks[frame.next_block]" = .ok blk
  hStmt : fr.next_stmt = (blk.statements.length : Int)
  hTerm : blk.terminator = .ResumeUnwind
  hSet : listSet m.threads m.active_thread { t with stack := t.stack.dropLast } "pop" = .ok threads'
  hDealloc : deallocAllM fr.locals.entries.length fr { m.mem with accesses := [] } = .ok (fr1, cm1)
  hEnd : ConcurrentMemory.end_call cm1 fr1.extra = .ok cm2
  hAct : fr1.stack_pop_action = .BackToCaller nextBlock (some ubBb) retPtr
  hJump : jumpToBlockM { { { m with mem := { m.mem with accesses := [] } } with threads := threads' } with
      mem := cm2 } ubBb = .ok mAfter
  hRace : ConcurrentMemory.check_data_races mAfter.mem mAfter.active_thread
    (setInsert m.synchronized_threads m.active_thread, m.mem.accesses) = .ok ()
/-- **C2 Single-Step `.ResumeUnwind` Execution & Thread/Payload Frame Law**. -/
theorem length_dropLast_of_getLast?_some {α : Type} :
    ∀ (xs : List α) (y : α), xs.getLast? = some y → xs.dropLast.length + 1 = xs.length
  | [], _, h => by cases h
  | [_], _, _ => rfl
  | _ :: b :: rs, y, h => by
    simp [List.dropLast, length_dropLast_of_getLast?_some (b :: rs) y h]
theorem stepM_resumeUnwind {M : Type} [Gen.Memory M] [MemoryOps M] {m mAfter : Machine M} (w : ResumeUnwindStepM m mAfter) :
    stepM m = .ok mAfter := by
  have hCur : curFrameM { m with mem := { m.mem with accesses := [] } } = .ok w.fr := by
    unfold curFrameM; simp only [w.hTid, w.hLast, bind, Except.bind, pure, Except.pure]
  unfold stepM
  simp only [w.hEnabled, Bool.not_true, Bool.false_eq_true, ↓reduceIte, resetDataRaceTrackingM,
    w.hPick, hCur, w.hBlk, w.hStmt, w.hTerm, evalTerminatorM, evalResumeUnwindM, w.hTid, w.hLast,
    w.hSet, w.hDealloc, w.hEnd, w.hAct, w.hJump, w.hRace, bind, Except.bind, pure, Except.pure]
theorem ResumeUnwindStepM.thread_invariants {M : Type} [Gen.Memory M] [MemoryOps M]
    {m mAfter : Machine M} (w : ResumeUnwindStepM m mAfter) :
    activeThreadM m = .ok w.t ∧ ∃ tAfter callerFr, activeThreadM mAfter = .ok tAfter ∧
      tAfter.unwind_payloads = w.t.unwind_payloads ∧ w.t.stack.dropLast.getLast? = some callerFr ∧
      tAfter.stack = w.t.stack.dropLast.dropLast ++ [{ callerFr with next_block := w.ubBb, next_stmt := 0 }] ∧
      tAfter.stack.length + 1 = w.t.stack.length := by
  have hTid0 : activeThreadM m = .ok w.t := w.hTid
  obtain ⟨hSet1, hIdx1⟩ := listSet_of_listIndex { w.t with stack := w.t.stack.dropLast } "pop" hTid0
  have hThEq : w.threads' = m.threads.set m.active_thread.toNat { w.t with stack := w.t.stack.dropLast } := by
    rw [w.hSet] at hSet1; exact Except.ok.inj hSet1
  let mMid : Machine M := { { { m with mem := { m.mem with accesses := [] } } with threads := w.threads' } with mem := w.cm2 }
  have hTidMid : activeThreadM mMid = .ok { w.t with stack := w.t.stack.dropLast } := by
    unfold activeThreadM; dsimp only [mMid]; rw [hThEq]; exact hIdx1 _
  have hJump := w.hJump
  unfold jumpToBlockM mutateCurFrameM at hJump; rw [hTidMid, ok_bind] at hJump; dsimp only [] at hJump
  cases hCaller : w.t.stack.dropLast.getLast? with
  | none => simp [hCaller, specPanic] at hJump
  | some callerFr =>
    rw [hCaller] at hJump; dsimp only [] at hJump
    obtain ⟨hSet2, hIdx2⟩ := listSet_of_listIndex ({ w.t with stack := w.t.stack.dropLast.dropLast ++
          [{ callerFr with next_block := w.ubBb, next_stmt := 0 }] }) "mutate_at" hTidMid
    rw [hSet2, ok_bind] at hJump
    let tAfter : Gen.Thread M := { w.t with stack := w.t.stack.dropLast.dropLast ++
          [{ callerFr with next_block := w.ubBb, next_stmt := 0 }] }
    have hmAfter : mAfter = { mMid with threads := mMid.threads.set mMid.active_thread.toNat tAfter } := (Except.ok.inj hJump).symm
    refine ⟨hTid0, tAfter, callerFr, ?_, rfl, rfl, rfl, ?_⟩
    · rw [hmAfter]; exact hIdx2 _
    · have h1 := length_dropLast_of_getLast?_some w.t.stack w.fr w.hLast
      have h2 := length_dropLast_of_getLast?_some w.t.stack.dropLast callerFr hCaller
      simp only [tAfter, List.length_append, List.length_singleton]; rw [h2, h1]
/-- Inductive `k`-step MiniRust `.ResumeUnwind` chain where EVERY single step
executes a `.ResumeUnwind` terminator (`ResumeUnwindStepM`). -/
inductive ResumeUnwindChainM {M : Type} [Gen.Memory M] [MemoryOps M] :
    Nat → Machine M → Machine M → Prop
  | zero (m : Machine M) : ResumeUnwindChainM 0 m m
  | step {k : Nat} {m m1 m2 : Machine M} :
      ResumeUnwindStepM m m1 → ResumeUnwindChainM k m1 m2 → ResumeUnwindChainM (k + 1) m m2
theorem stepsM_add {M : Type} [Gen.Memory M] [MemoryOps M] :
    ∀ (a b : Nat) (m m1 : Machine M), stepsM a m = .ok m1 → stepsM (a + b) m = stepsM b m1
  | 0, _, _, _, h => by cases Except.ok.inj h; simp [stepsM]
  | a + 1, b, m, m1, h => by
    simp only [Nat.succ_add, stepsM] at h ⊢
    cases hs : stepM m with
    | error e => simp [hs, bind, Except.bind] at h
    | ok m' => simp only [hs, ok_bind] at h ⊢; exact stepsM_add a b m' m1 h
theorem stepM_of_evalTerminatorM {M : Type} [Gen.Memory M] [MemoryOps M]
    {m mAfter : Machine M} (fr : StackFrame M) (blk : Gen.BasicBlock)
    (hEn : m.threads.any (fun th => decide (th.state = .Enabled)) = true)
    (hPick : pickActiveThreadM { m with mem := { m.mem with accesses := [] } } = .ok m.active_thread)
    (hCur : curFrameM { m with mem := { m.mem with accesses := [] } } = .ok fr)
    (hBlk : mapIndex fr.func.blocks fr.next_block "frame.func.blocks[frame.next_block]" = .ok blk)
    (hStmt : fr.next_stmt = (blk.statements.length : Int))
    (hEval : evalTerminatorM { m with mem := { m.mem with accesses := [] } } blk.terminator = .ok mAfter)
    (hRace : ConcurrentMemory.check_data_races mAfter.mem mAfter.active_thread
      (setInsert m.synchronized_threads m.active_thread, m.mem.accesses) = .ok ()) :
    stepM m = .ok mAfter := by
  unfold stepM
  simp only [hEn, Bool.not_true, Bool.false_eq_true, ↓reduceIte, resetDataRaceTrackingM,
    hPick, hCur, hBlk, hStmt, hEval, hRace, bind, Except.bind, pure, Except.pure]
theorem stepM_error_of_evalTerminatorM {M : Type} [Gen.Memory M] [MemoryOps M]
    {m : Machine M} {e : Stop} (fr : StackFrame M) (blk : Gen.BasicBlock)
    (hEn : m.threads.any (fun th => decide (th.state = .Enabled)) = true)
    (hPick : pickActiveThreadM { m with mem := { m.mem with accesses := [] } } = .ok m.active_thread)
    (hCur : curFrameM { m with mem := { m.mem with accesses := [] } } = .ok fr)
    (hBlk : mapIndex fr.func.blocks fr.next_block "frame.func.blocks[frame.next_block]" = .ok blk)
    (hStmt : fr.next_stmt = (blk.statements.length : Int))
    (hEval : evalTerminatorM { m with mem := { m.mem with accesses := [] } } blk.terminator = .error e) :
    stepM m = .error e := by
  unfold stepM
  simp only [hEn, Bool.not_true, Bool.false_eq_true, ↓reduceIte, resetDataRaceTrackingM,
    hPick, hCur, hBlk, hStmt, hEval, bind, Except.bind]
theorem ResumeUnwindChainM.to_stepsM {M : Type} [Gen.Memory M] [MemoryOps M]
    {k : Nat} {m m' : Machine M} (h : ResumeUnwindChainM k m m') :
    stepsM k m = .ok m' := by
  induction h with
  | zero _ => rfl
  | step w _ ih => simp only [stepsM, stepM_resumeUnwind w, bind, Except.bind]; exact ih
theorem ResumeUnwindChainM.thread_invariants {M : Type} [Gen.Memory M] [MemoryOps M]
    {k : Nat} {m m' : Machine M} (h : ResumeUnwindChainM k m m') :
    ∀ t, activeThreadM m = .ok t → ∃ t', activeThreadM m' = .ok t' ∧ t'.unwind_payloads = t.unwind_payloads ∧
        t'.stack.length + k = t.stack.length := by
  induction h with
  | zero _ => intro t ht; exact ⟨t, ht, rfl, Nat.add_zero _⟩
  | @step k m m1 m2 w _ ih =>
    intro t ht
    obtain ⟨hTid0, t1, _, ht1, hPay1, _, _, hLen1⟩ := w.thread_invariants
    rw [ht] at hTid0; cases Except.ok.inj hTid0
    obtain ⟨t2, ht2, hPay2, hLen2⟩ := ih t1 ht1
    refine ⟨t2, ht2, hPay2.trans hPay1, ?_⟩
    rw [← Nat.add_assoc, hLen2, hLen1]
/-- **C2b All-Terminal Multi-Frame `.continue_` Propagation (`Mach` &
`MachTB`)**: Composes `conts` Trusted `.continue_` pops with `conts.length`
MiniRust `ResumeUnwind` steps across ALL four terminal outcomes: `.cleanup`
(with exact caller target block `(ubBb, 0)` + `MachTB.wfLive`), `.unreachable`
(lockstep UB), `.terminate` (lockstep `.abort`), and root `[]` (Trusted
`.panic` vs. MiniRust `BottomOfStack` UB divergence). -/
theorem unwindResume_continue_chain_coupled_steps_and_wfLive
    (s : MachineState) (conts : List SavedCallerFrame) (caller : SavedCallerFrame)
    (rest : List SavedCallerFrame) (cleanupBb : Nat) (span : String) (curBody : Option CapturedMir)
    (mBM mBMk mBMf : Mach) (mTB mTBk mTBf : MachTB) (hStack : s.memory.callStack = conts ++ (caller :: rest))
    (hCont : ∀ c ∈ conts, c.returnUnwind = .continue_) (hClean : caller.returnUnwind = .cleanup cleanupBb)
    (hChainBM : ResumeUnwindChainM conts.length mBM mBMk) (wLastBM : ResumeUnwindStepM mBMk mBMf)
    (hBbBM : wLastBM.ubBb = bbName cleanupBb) (hwfTB : MachTB.wfLive mTB)
    (hChainTB : ResumeUnwindChainM conts.length mTB mTBk) (wLastTB : ResumeUnwindStepM mTBk mTBf)
    (hBbTB : wLastTB.ubBb = bbName cleanupBb) :
    let memMid := unwindContinueChainMem conts (caller :: rest) s.memory
    MirSemantics.evalTerminator s { kind := .unwindResume, span := span } curBody = MirStepNode.step
        { frame := { caller.frame with blockIdx := cleanupBb, stmtIdx := 0 },
          memory := { memMid with
                      callStack := rest, activeCallee := .some caller.callerBody, activeProtectors := restoreCallerProtectors caller,
                      borrows := disableFramesAbove memMid.borrows (length rest) } } ∧
    Interp.steps (conts.length + 1) mBM = .ok mBMf ∧ Interp.stepsTB (conts.length + 1) mTB = .ok mTBf ∧
    MachTB.wfLive mTBf ∧ (∀ tBM, activeThreadM mBM = .ok tBM →
      ∃ tBMf, activeThreadM mBMf = .ok tBMf ∧ tBMf.unwind_payloads = tBM.unwind_payloads ∧
        tBMf.stack.length + (conts.length + 1) = tBM.stack.length ∧
        tBMf.stack.getLast?.map (fun fr => (fr.next_block, fr.next_stmt)) = some (bbName cleanupBb, 0)) ∧
    (∀ tTB, activeThreadM mTB = .ok tTB → ∃ tTBf, activeThreadM mTBf = .ok tTBf ∧ tTBf.unwind_payloads = tTB.unwind_payloads ∧
        tTBf.stack.length + (conts.length + 1) = tTB.stack.length ∧
        tTBf.stack.getLast?.map (fun fr => (fr.next_block, fr.next_stmt)) = some (bbName cleanupBb, 0)) := by
  intro memMid
  have hStepsBM : Interp.steps (conts.length + 1) mBM = .ok mBMf := by
    rw [← stepsM_bm_eq, stepsM_add conts.length 1 mBM mBMk hChainBM.to_stepsM]
    simp only [stepsM, stepM_resumeUnwind wLastBM, ok_bind, pure, Except.pure]
  have hStepsTB : Interp.stepsTB (conts.length + 1) mTB = .ok mTBf := by
    change stepsM (conts.length + 1) mTB = .ok mTBf
    rw [stepsM_add conts.length 1 mTB mTBk hChainTB.to_stepsM]
    simp only [stepsM, stepM_resumeUnwind wLastTB, ok_bind, pure, Except.pure]
  refine ⟨?_, hStepsBM, hStepsTB, stepsTB_wfLive hwfTB hStepsTB, ?_, ?_⟩
  · simp only [MirSemantics.evalTerminator, hStack,
      trusted_unwindFromCallStack_continue_chain conts (caller :: rest) s.memory hCont, unwindFromCallStack, hClean, memMid]
  · intro tBM htBM
    obtain ⟨tK, htK, hPayK, hLenK⟩ := hChainBM.thread_invariants tBM htBM
    obtain ⟨hTidK, tF, cFr, htF, hPayF, _, hStkF, hLenF⟩ := wLastBM.thread_invariants
    rw [htK] at hTidK; cases Except.ok.inj hTidK
    refine ⟨tF, htF, hPayF.trans hPayK, ?_, ?_⟩
    · rw [Nat.add_comm conts.length 1, ← Nat.add_assoc, hLenF, hLenK]
    · rw [hStkF, (getLast?_dropLast_snoc _ _).1, hBbBM]; rfl
  · intro tTB htTB
    obtain ⟨tK, htK, hPayK, hLenK⟩ := hChainTB.thread_invariants tTB htTB
    obtain ⟨hTidK, tF, cFr, htF, hPayF, _, hStkF, hLenF⟩ := wLastTB.thread_invariants
    rw [htK] at hTidK; cases Except.ok.inj hTidK
    refine ⟨tF, htF, hPayF.trans hPayK, ?_, ?_⟩
    · rw [Nat.add_comm conts.length 1, ← Nat.add_assoc, hLenF, hLenK]
    · rw [hStkF, (getLast?_dropLast_snoc _ _).1, hBbTB]; rfl
theorem unwindResume_continue_chain_fault_and_root_terminals {M : Type} [Gen.Memory M] [MemoryOps M]
    (s : MachineState) (conts : List SavedCallerFrame) (span : String) (curBody : Option CapturedMir)
    (m mK : Machine M) (hCont : ∀ c ∈ conts, c.returnUnwind = .continue_) (hChain : ResumeUnwindChainM conts.length m mK) :
    (∀ caller rest eMsg, s.memory.callStack = conts ++ (caller :: rest) →
      caller.returnUnwind = .unreachable → stepM mK = .error (.ub eMsg) →
      MirSemantics.evalTerminator s { kind := .unwindResume, span := span } curBody = MirStepNode.fail .ub ∧
      stepsM (conts.length + 1) m = .error (.ub eMsg)) ∧
    (∀ caller rest, s.memory.callStack = conts ++ (caller :: rest) → caller.returnUnwind = .terminate → stepM mK = .error .abort →
      MirSemantics.evalTerminator s { kind := .unwindResume, span := span } curBody =
        MirStepNode.retOutcome .abort ∧ stepsM (conts.length + 1) m = .error .abort) ∧
    (s.memory.callStack = conts → stepM mK = .error (.ub "the function at the bottom of the stack must not unwind") →
      MirSemantics.evalTerminator s { kind := .unwindResume, span := span } curBody = MirStepNode.retOutcome .panic ∧
      stepsM (conts.length + 1) m = .error (.ub "the function at the bottom of the stack must not unwind")) := by
  refine ⟨fun caller rest eMsg hStk hUnr hErr => ⟨?_, ?_⟩, fun caller rest hStk hTerm hErr => ⟨?_, ?_⟩, fun hStk hErr => ⟨?_, ?_⟩⟩
  · simp only [MirSemantics.evalTerminator, hStk,
      trusted_unwindFromCallStack_continue_chain conts (caller :: rest) s.memory hCont, unwindFromCallStack, hUnr]
  · rw [stepsM_add conts.length 1 m mK hChain.to_stepsM]; simp only [stepsM, hErr, bind, Except.bind]
  · simp only [MirSemantics.evalTerminator, hStk,
      trusted_unwindFromCallStack_continue_chain conts (caller :: rest) s.memory hCont, unwindFromCallStack, hTerm]
  · rw [stepsM_add conts.length 1 m mK hChain.to_stepsM]; simp only [stepsM, hErr, bind, Except.bind]
  · have hApp : conts = conts ++ [] := (List.append_nil conts).symm
    simp only [MirSemantics.evalTerminator, hStk]
    rw [hApp, trusted_unwindFromCallStack_continue_chain conts [] s.memory hCont]; rfl
  · rw [stepsM_add conts.length 1 m mK hChain.to_stepsM]; simp only [stepsM, hErr, bind, Except.bind]
/-- **C2 Universal Polymorphic `StartUnwind -> ResumeUnwind^k -> StopUnwind`
Lifecycle & Empty-Payload UB Law (`minirust_unwind_payload_lifecycle_M`)**:
Across EVERY `Machine M` (`Mach` & `MachTB`): (1) `StartUnwind` pushes payload
`p.thin_pointer` and jumps to `ubBb`; (2) `StopUnwind` pops the top payload and
jumps to `catchBb`; (3) `StopUnwind` on empty `unwind_payloads` faults with
`"StopUnwind: the payload stack is empty"`; (4) the companion theorem
`minirust_start_resume_stop_unwind_stepsM` composes `StartUnwind` (1 step) +
`ResumeUnwindChainM k` (`k` steps) + `StopUnwind` (1 step) into
`stepsM (1 + k + 1)` preserving original payloads and popping `k` frames. -/
theorem minirust_unwind_payload_lifecycle_M {M : Type} [Gen.Memory M] [MemoryOps M]
    (m m1 : Machine M) (t1 : Gen.Thread M) (fr1 : StackFrame M)
    (payloadExpr : Gen.ValueExpr) (p : Gen.Pointer (Gen.Memory.Provenance M)) (ubBb catchBb : Gen.BbName) :
    (evalValueM m payloadExpr = .ok ((.Ptr p, .Ptr (.Raw .None)), m1) → activeThreadM m1 = .ok t1 → t1.stack.getLast? = some fr1 →
      ∃ mStart tStart, evalTerminatorM m (.StartUnwind payloadExpr ubBb) = .ok mStart ∧ activeThreadM mStart = .ok tStart ∧
        tStart.unwind_payloads = t1.unwind_payloads ++ [p.thin_pointer] ∧
        tStart.stack = t1.stack.dropLast ++ [{ fr1 with next_block := ubBb, next_stmt := 0 }]) ∧
    (∀ ps topPtr, activeThreadM m1 = .ok t1 → t1.unwind_payloads = ps ++ [topPtr] →
      t1.stack.getLast? = some fr1 → ∃ mStop tStop, evalTerminatorM m1 (.StopUnwind catchBb) = .ok mStop ∧
        activeThreadM mStop = .ok tStop ∧ tStop.unwind_payloads = ps ∧
        tStop.stack = t1.stack.dropLast ++ [{ fr1 with next_block := catchBb, next_stmt := 0 }]) ∧
    (activeThreadM m1 = .ok t1 → t1.unwind_payloads = [] → evalTerminatorM m1 (.StopUnwind catchBb) =
        .error (.ub "StopUnwind: the payload stack is empty")) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hVal hTid hLast
    let tMid : Gen.Thread M := { t1 with unwind_payloads := t1.unwind_payloads ++ [p.thin_pointer] }
    let mMid : Machine M := { m1 with threads := m1.threads.set m1.active_thread.toNat tMid }
    obtain ⟨hSet1, hIdx1⟩ := listSet_of_listIndex tMid "mutate_at" hTid
    have hTid2 : activeThreadM mMid = .ok tMid := hIdx1 _
    let tStart : Gen.Thread M := { tMid with stack := t1.stack.dropLast ++ [{ fr1 with next_block := ubBb, next_stmt := 0 }] }
    let mStart : Machine M := { mMid with threads := mMid.threads.set mMid.active_thread.toNat tStart }
    obtain ⟨hSet2, hIdx2⟩ := listSet_of_listIndex tStart "mutate_at" hTid2
    have hActStart : activeThreadM mStart = .ok tStart := hIdx2 _
    refine ⟨mStart, tStart, ?_, hActStart, rfl, rfl⟩
    simp only [evalTerminatorM, mutateActiveThreadM, jumpToBlockM, mutateCurFrameM,
      hVal, hTid, hSet1, hTid2, hLast, hSet2, tMid, mMid, tStart, mStart, pure, Except.pure, bind, Except.bind]
  · intro ps topPtr hTid hPay hLast
    obtain ⟨hGetL, hDropL⟩ := getLast?_dropLast_snoc ps topPtr
    let tMid : Gen.Thread M := { t1 with unwind_payloads := ps }
    let mMid : Machine M := { m1 with threads := m1.threads.set m1.active_thread.toNat tMid }
    obtain ⟨hSet1, hIdx1⟩ := listSet_of_listIndex tMid "mutate_at" hTid
    have hTid2 : activeThreadM mMid = .ok tMid := hIdx1 _
    let tStop : Gen.Thread M := { tMid with stack := t1.stack.dropLast ++ [{ fr1 with next_block := catchBb, next_stmt := 0 }] }
    let mStop : Machine M := { mMid with threads := mMid.threads.set mMid.active_thread.toNat tStop }
    obtain ⟨hSet2, hIdx2⟩ := listSet_of_listIndex tStop "mutate_at" hTid2
    have hActStop : activeThreadM mStop = .ok tStop := hIdx2 _
    refine ⟨mStop, tStop, ?_, hActStop, rfl, rfl⟩
    simp only [evalTerminatorM, mutateActiveThreadM, jumpToBlockM, mutateCurFrameM,
      hTid, hPay, hGetL, hDropL, hSet1, hTid2, hLast, hSet2, tMid, mMid, tStop, mStop, pure, Except.pure, bind, Except.bind]
  · intro hTid hEmpty
    dsimp only [evalTerminatorM, mutateActiveThreadM]; rw [hTid, ok_bind]; simp [hEmpty, List.getLast?, ub, bind, Except.bind]
/-- End-to-end polymorphic `StartUnwind -> ResumeUnwind^k -> StopUnwind`
multi-step composition across BOTH `Mach` and `MachTB` (and `MachTB.wfLive`). -/
theorem minirust_start_resume_stop_unwind_stepsM {M : Type} [Gen.Memory M] [MemoryOps M]
    (m0 m1 mStart mMid : Machine M) (t1 : Gen.Thread M) (fr0 fr1 frStop : StackFrame M)
    (blk0 blkStop : Gen.BasicBlock) (payloadExpr : Gen.ValueExpr)
    (p : Gen.Pointer (Gen.Memory.Provenance M)) (ubBb catchBb : Gen.BbName) (k : Nat)
    (hEn0 : m0.threads.any (fun th => decide (th.state = .Enabled)) = true)
    (hPick0 : pickActiveThreadM { m0 with mem := { m0.mem with accesses := [] } } = .ok m0.active_thread)
    (hCur0 : curFrameM { m0 with mem := { m0.mem with accesses := [] } } = .ok fr0)
    (hBlk0 : mapIndex fr0.func.blocks fr0.next_block "frame.func.blocks[frame.next_block]" = .ok blk0)
    (hStmt0 : fr0.next_stmt = (blk0.statements.length : Int)) (hTerm0 : blk0.terminator = .StartUnwind payloadExpr ubBb)
    (hVal : evalValueM { m0 with mem := { m0.mem with accesses := [] } } payloadExpr = .ok ((.Ptr p, .Ptr (.Raw .None)), m1))
    (hTid1 : activeThreadM m1 = .ok t1) (hLast1 : t1.stack.getLast? = some fr1)
    (hEvalStart : evalTerminatorM { m0 with mem := { m0.mem with accesses := [] } } (.StartUnwind payloadExpr ubBb) = .ok mStart)
    (hRace0 : ConcurrentMemory.check_data_races mStart.mem mStart.active_thread
      (setInsert m0.synchronized_threads m0.active_thread, m0.mem.accesses) = .ok ())
    (hChain : ResumeUnwindChainM k mStart mMid) (hEnS : mMid.threads.any (fun th => decide (th.state = .Enabled)) = true)
    (hPickS : pickActiveThreadM { mMid with mem := { mMid.mem with accesses := [] } } = .ok mMid.active_thread)
    (hCurS : curFrameM { mMid with mem := { mMid.mem with accesses := [] } } = .ok frStop)
    (hBlkS : mapIndex frStop.func.blocks frStop.next_block "frame.func.blocks[frame.next_block]" = .ok blkStop)
    (hStmtS : frStop.next_stmt = (blkStop.statements.length : Int)) (hTermS : blkStop.terminator = .StopUnwind catchBb)
    (hRaceS : ∀ mEnd, evalTerminatorM { mMid with mem := { mMid.mem with accesses := [] } } (.StopUnwind catchBb) = .ok mEnd →
      ConcurrentMemory.check_data_races mEnd.mem mEnd.active_thread
        (setInsert mMid.synchronized_threads mMid.active_thread, mMid.mem.accesses) = .ok ()) :
    ∃ mEnd tEnd, stepsM (1 + k + 1) m0 = .ok mEnd ∧ activeThreadM mEnd = .ok tEnd ∧
      tEnd.unwind_payloads = t1.unwind_payloads ∧ tEnd.stack.length + k = t1.stack.length ∧
      tEnd.stack.getLast?.map (fun fr => (fr.next_block, fr.next_stmt)) = some (catchBb, 0) := by
  obtain ⟨mS, tS, hEvS, hActS, hPayS, hStkS⟩ := (minirust_unwind_payload_lifecycle_M { m0 with mem := { m0.mem with accesses := [] } }
      m1 t1 fr1 payloadExpr p ubBb catchBb).1 hVal hTid1 hLast1
  rw [hEvalStart] at hEvS; cases Except.ok.inj hEvS
  have hStep0 : stepM m0 = .ok mStart :=
    stepM_of_evalTerminatorM fr0 blk0 hEn0 hPick0 hCur0 hBlk0 hStmt0 (by rw [hTerm0]; exact hEvalStart) hRace0
  obtain ⟨tMid, hActMid, hPayMid, hLenMid⟩ := hChain.thread_invariants tS hActS
  have hActMid0 : activeThreadM { mMid with mem := { mMid.mem with accesses := [] } } = .ok tMid := hActMid
  have hLastMid : tMid.stack.getLast? = some frStop := by
    unfold curFrameM at hCurS; rw [hActMid0, ok_bind] at hCurS
    cases hL : tMid.stack.getLast? with
    | none => simp [hL, specPanic] at hCurS
    | some f => simp [hL, pure, Except.pure] at hCurS; subst hCurS; rfl
  obtain ⟨mEnd, tEnd, hEvEnd, hActEnd, hPayEnd, hStkEnd⟩ :=
    (minirust_unwind_payload_lifecycle_M { mMid with mem := { mMid.mem with accesses := [] } }
      { mMid with mem := { mMid.mem with accesses := [] } }
      tMid frStop payloadExpr p ubBb catchBb).2.1 t1.unwind_payloads p.thin_pointer hActMid0
      (hPayMid.trans hPayS) hLastMid
  have hStepEnd : stepM mMid = .ok mEnd := stepM_of_evalTerminatorM frStop blkStop hEnS hPickS hCurS hBlkS hStmtS
      (by rw [hTermS]; exact hEvEnd) (hRaceS mEnd hEvEnd)
  have hSteps0k : stepsM (1 + k) m0 = .ok mMid := by
    rw [stepsM_add 1 k m0 mStart (by simp [stepsM, hStep0, bind, Except.bind, pure, Except.pure])]; exact hChain.to_stepsM
  have hFull : stepsM (1 + k + 1) m0 = .ok mEnd := by
    rw [stepsM_add (1 + k) 1 m0 mMid hSteps0k]; simp [stepsM, hStepEnd, bind, Except.bind, pure, Except.pure]
  have hLenS : tS.stack.length = t1.stack.length := by
    rw [hStkS, List.length_append, List.length_singleton]
    exact length_dropLast_of_getLast?_some t1.stack fr1 hLast1
  have hLenEnd : tEnd.stack.length = tMid.stack.length := by
    rw [hStkEnd, List.length_append, List.length_singleton]
    exact length_dropLast_of_getLast?_some tMid.stack frStop hLastMid
  refine ⟨mEnd, tEnd, hFull, hActEnd, hPayEnd, ?_, ?_⟩
  · rw [hLenEnd, hLenMid, hLenS]
  · rw [hStkEnd, (getLast?_dropLast_snoc _ _).1]; rfl
/-- **C2c Trusted `.unreachable` UB Law**: unwinding into `.unreachable`
faults with `MirStepNode.fail .ub`. -/
theorem trusted_unwindResume_unreachable_ub (s : MachineState) (caller : SavedCallerFrame) (rest : List SavedCallerFrame)
    (span : String) (curBody : Option CapturedMir) (hStack : s.memory.callStack = caller :: rest)
    (hAction : caller.returnUnwind = .unreachable) :
    MirSemantics.evalTerminator s { kind := .unwindResume, span := span } curBody = MirStepNode.fail .ub := by
  simp only [MirSemantics.evalTerminator, hStack, unwindFromCallStack, hAction]
/-- **C2d Trusted `.terminate` Abort Law**: unwinding into `.terminate` halts
with `MirStepNode.retOutcome .abort`. -/
theorem trusted_unwindResume_terminate_abort (s : MachineState) (caller : SavedCallerFrame) (rest : List SavedCallerFrame)
    (span : String) (curBody : Option CapturedMir) (hStack : s.memory.callStack = caller :: rest)
    (hAction : caller.returnUnwind = .terminate) :
    MirSemantics.evalTerminator s { kind := .unwindResume, span := span } curBody = MirStepNode.retOutcome .abort := by
  simp only [MirSemantics.evalTerminator, hStack, unwindFromCallStack, hAction]
/-- **C2e Root-Frame Explicit Divergence
(`unwindResume_root_panic_vs_ub_divergence`)**: At the root frame (`callStack
= []` in Trusted; `stack_pop_action = .BottomOfStack` in MiniRust), Trusted
terminates with `MirStepNode.retOutcome .panic`, whereas MiniRust faults with
`"the function at the bottom of the stack must not unwind"` across both `Mach`
and `MachTB`. -/
theorem unwindResume_root_panic_vs_ub_divergence {M : Type} [Gen.Memory M] [MemoryOps M]
    (s : MachineState) (span : String) (curBody : Option CapturedMir) (hRoot : s.memory.callStack = [])
    (m : Machine M) (t : Gen.Thread M) (fr fr1 : StackFrame M)
    (threads' : List (Gen.Thread M)) (cm1 cm2 : Gen.ConcurrentMemory M) (ht : activeThreadM m = .ok t)
    (hlast : t.stack.getLast? = some fr)
    (hset : listSet m.threads m.active_thread { t with stack := t.stack.dropLast } "pop" = .ok threads')
    (hdealloc : deallocAllM fr.locals.entries.length fr m.mem = .ok (fr1, cm1))
    (hend : ConcurrentMemory.end_call cm1 fr1.extra = .ok cm2) (hbot : fr1.stack_pop_action = .BottomOfStack) :
    MirSemantics.evalTerminator s { kind := .unwindResume, span := span } curBody =
      MirStepNode.retOutcome .panic ∧ evalResumeUnwindM m =
      .error (.ub "the function at the bottom of the stack must not unwind") := by
  constructor
  · simp only [MirSemantics.evalTerminator, hRoot, unwindFromCallStack]
  · unfold evalResumeUnwindM
    simp only [ht, hlast, hset, hdealloc, hend, hbot, pure, Except.pure, bind, Except.bind, ub]
/-- **C2 MiniRust Polymorphic `BackToCaller` Law (`Mach` & `MachTB`)**: When
popping a callee frame with `BackToCaller nextBlock unwindBlock retPtr`,
`evalResumeUnwindM` jumps to `ubBb` when `unwindBlock = some ubBb` and faults
with UB when `unwindBlock = none`. -/
theorem minirust_evalResumeUnwindM_backToCaller {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Machine M) (t : Gen.Thread M) (fr fr1 : StackFrame M) (threads' : List (Gen.Thread M)) (cm1 cm2 : Gen.ConcurrentMemory M)
    (nextBlock : Option Gen.BbName) (unwindBlock : Option Gen.BbName)
    (retPtr : ThinPointer (Gen.Memory.Provenance M)) (ht : activeThreadM m = .ok t) (hlast : t.stack.getLast? = some fr)
    (hset : listSet m.threads m.active_thread { t with stack := t.stack.dropLast } "pop" = .ok threads')
    (hdealloc : deallocAllM fr.locals.entries.length fr m.mem = .ok (fr1, cm1))
    (hend : ConcurrentMemory.end_call cm1 fr1.extra = .ok cm2)
    (hact : fr1.stack_pop_action = .BackToCaller nextBlock unwindBlock retPtr) :
    (∀ ubBb, unwindBlock = some ubBb → evalResumeUnwindM m = jumpToBlockM { { m with threads := threads' } with mem := cm2 } ubBb) ∧
    (unwindBlock = none → evalResumeUnwindM m =
        .error (.ub "unwinding from a function where the caller did not specify an unwind_block")) := by
  constructor
  · intro ubBb hEq
    unfold evalResumeUnwindM; simp only [ht, hlast, hset, hdealloc, hend, hact, hEq, pure, Except.pure, bind, Except.bind]
  · intro hEq
    unfold evalResumeUnwindM; simp only [ht, hlast, hset, hdealloc, hend, hact, hEq, pure, Except.pure, bind, Except.bind, ub]
/-- **`Translate.translateUnwindAction` Lowering Spec**: connects every MIR
`UnwindAction` constructor directly to its MiniRust cleanup-block terminator. -/
theorem translateUnwindAction_cases (nextCleanup : Nat) (cb : Nat) : translateUnwindAction nextCleanup .continue_ =
      (bbName nextCleanup, nextCleanup + 1, [(bbName nextCleanup, ⟨[], .ResumeUnwind, .Cleanup⟩)]) ∧
    translateUnwindAction nextCleanup .unreachable =
      (bbName nextCleanup, nextCleanup + 1, [(bbName nextCleanup, ⟨[], .Unreachable, .Cleanup⟩)]) ∧
    translateUnwindAction nextCleanup .terminate =
      (bbName nextCleanup, nextCleanup + 1, [(bbName nextCleanup, ⟨[], buildAbort, .Cleanup⟩)]) ∧
    translateUnwindAction nextCleanup (.cleanup cb) = (bbName cb, nextCleanup, []) := ⟨rfl, rfl, rfl, rfl⟩

/-! ### C2 Concrete Witnesses: `.cleanup`, `.continue_` Multi-Frame,
`.unreachable`, `.terminate`, Root Divergence,
`StartUnwind -> ResumeUnwind -> StopUnwind`, and `MachTB` Protector Release -/
def c2LeafMir : MirAst.CapturedMir := mkMirBody "ep2::c2_leaf" [mkDecl unitMirTy] 0 [mkBb [] .unwindResume true]
def c2CallerMir : MirAst.CapturedMir := mkMirBody "ep2::c2_caller" [mkDecl u32MirTy] 0
    [mkBb [] (.goto 1), mkBb [mkSt (.assign (locPlace 0) (.use (constU32 77)))] .return_ true]
def c2LeafMrFn : Gen.Function := mkMrFn [] [] (localName 0) [(bbName 0, ⟨[], .ResumeUnwind, .Cleanup⟩)]
def c2MidContinueMrFn : Gen.Function := mkMrFn [] [] (localName 0) [(bbName 0, ⟨[], .ResumeUnwind, .Cleanup⟩)]
def c2CallerMrFn : Gen.Function := mkMrFn [(localName 0, u32MrTy)] [] (localName 0) [(bbName 0, ⟨[], .Goto (bbName 1), .Regular⟩),
     (bbName 1, ⟨[.Assign (.Local (localName 0)) (.Constant (.Int 77) u32MrTy)], .Return, .Cleanup⟩),
     (bbName 2, ⟨[], .Unreachable, .Cleanup⟩), (bbName 3, ⟨[], buildAbort, .Cleanup⟩)]
def c2Prog : Gen.Program := mkMrProg [(fnName 0, c2CallerMrFn), (fnName 1, c2MidContinueMrFn), (fnName 2, c2LeafMrFn)]
def c2MkStackMach (unwindActionBb : Option Gen.BbName) (withMidContinue : Bool := false) (payloads : List Ptr := []) : Mach :=
  let rootFr := mkRootFrame c2CallerMrFn [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) })]
  let midFr : Frame :=
    { func := c2MidContinueMrFn, locals := ⟨[]⟩, stack_pop_action := .BackToCaller none unwindActionBb dummyRetPtr,
      next_block := bbName 0, next_stmt := 0, extra := () }
  let leafFr : Frame :=
    { func := c2LeafMrFn, locals := ⟨[]⟩,
      stack_pop_action := .BackToCaller none (if withMidContinue then some (bbName 0) else unwindActionBb)
        dummyRetPtr, next_block := bbName 0, next_stmt := 0, extra := () }
  mkMrMach c2Prog [mkStackAlloc 128 (List.replicate 4 .Uninit) 4]
    (if withMidContinue then [rootFr, midFr, leafFr] else [rootFr, leafFr]) [] [] payloads
/-- **C2 Concrete Witness covering ALL 5 regimes on Trusted, `Mach`, and
`MachTB`**. -/
theorem c2_unwindResume_all_five_regimes_witness :
    let callerBase (ua : UnwindAction) : SavedCallerFrame :=
      { callerBody := c2CallerMir, frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit] },
        destination := locPlace 0, returnTarget := 0, returnUnwind := ua }
    let sWith (cs : List SavedCallerFrame) : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit] },
        memory := { (initMachineState c2LeafMir []).memory with callStack := cs } }
    let rootLeafMach := mkMrMach c2Prog [] [mkRootFrame c2LeafMrFn []]
    -- (a) .cleanup 1
    (match stepMirFn c2LeafMir (sWith [callerBase (.cleanup 1)]) with
     | .tau (.running s1) => s1.frame.blockIdx = 1 ∧ s1.memory.callStack = [] | _ => False) ∧
    (∃ m1, Interp.step (c2MkStackMach (some (bbName 1))) = .ok m1 ∧
      m1.threads[0]?.map (fun t => (t.stack.length, t.stack[0]?.map (·.next_block))) = some (1, some (bbName 1))) ∧
    (∃ m1, Interp.stepTB (liftMachToTB (c2MkStackMach (some (bbName 1)))) = .ok m1 ∧ MachTB.wfLive m1 ∧
      m1.threads[0]?.map (fun t => (t.stack.length, t.stack[0]?.map (·.next_block))) = some (1, some (bbName 1))) ∧
    -- (b) .continue_ chain (1 Trusted step ↔ 2 MiniRust steps)
    (match stepMirFn c2LeafMir (sWith [callerBase .continue_, callerBase (.cleanup 1)]) with
     | .tau (.running s1) => s1.frame.blockIdx = 1 ∧ s1.memory.callStack = [] | _ => False) ∧
    (∃ m2, Interp.steps 2 (c2MkStackMach (some (bbName 1)) true) = .ok m2 ∧
      m2.threads[0]?.map (fun t => (t.stack.length, t.stack[0]?.map (·.next_block))) = some (1, some (bbName 1))) ∧
    (∃ m2, Interp.stepsTB 2 (liftMachToTB (c2MkStackMach (some (bbName 1)) true)) = .ok m2 ∧ MachTB.wfLive m2 ∧
      m2.threads[0]?.map (fun t => (t.stack.length, t.stack[0]?.map (·.next_block))) = some (1, some (bbName 1))) ∧
    -- (c) .unreachable UB (direct none & synthetic Unreachable block)
    stepMirFn c2LeafMir (sWith [callerBase .unreachable]) = MirStepNode.fail .ub ∧ Interp.step (c2MkStackMach none) =
      .error (.ub "unwinding from a function where the caller did not specify an unwind_block") ∧
    Interp.stepTB (liftMachToTB (c2MkStackMach none)) =
      .error (.ub "unwinding from a function where the caller did not specify an unwind_block") ∧
    Interp.steps 2 (c2MkStackMach (some (bbName 2))) = .error (.ub "reached unreachable code") ∧
    Interp.stepsTB 2 (liftMachToTB (c2MkStackMach (some (bbName 2)))) = .error (.ub "reached unreachable code") ∧
    -- (d) .terminate abort
    stepMirFn c2LeafMir (sWith [callerBase .terminate]) = MirStepNode.retOutcome .abort ∧
    Interp.steps 2 (c2MkStackMach (some (bbName 3))) = .error .abort ∧
    Interp.stepsTB 2 (liftMachToTB (c2MkStackMach (some (bbName 3)))) = .error .abort ∧
    -- (e) Root-frame divergence: Trusted .panic vs MiniRust BottomOfStack UB
    stepMirFn c2LeafMir (sWith []) = MirStepNode.retOutcome .panic ∧ Interp.step rootLeafMach =
      .error (.ub "the function at the bottom of the stack must not unwind") ∧
    Interp.stepTB (liftMachToTB rootLeafMach) = .error (.ub "the function at the bottom of the stack must not unwind") :=
  ⟨⟨rfl, rfl⟩, ok_of_map_toOption (by decide +kernel), ok_stepTB_wfLive (by decide +kernel),
   ⟨rfl, rfl⟩, ok_of_map_toOption (by decide +kernel), ok_stepsTB_wfLive (by decide +kernel),
   rfl, eq_error_ub_of_interpUbMsg (by decide +kernel), eq_error_ub_of_interpUbMsg (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel), eq_error_ub_of_interpUbMsg (by decide +kernel),
   rfl, eq_error_abort_of_interpIsAbort (by decide +kernel), eq_error_abort_of_interpIsAbort (by decide +kernel), rfl,
   eq_error_ub_of_interpUbMsg (by decide +kernel), eq_error_ub_of_interpUbMsg (by decide +kernel)⟩
/-- **C2 `StartUnwind -> ResumeUnwind -> StopUnwind` Composition Witness** on
both `Mach` and `MachTB` (plus empty-stack `StopUnwind` UB witness). -/
def c2UnwindLifecycleMach : Mach :=
  let calleeFn := mkMrFn [] [] (localName 0) [(bbName 0, ⟨[], .StartUnwind (.Constant (.PointerWithoutProvenance 4096) thinRawPtrTy)
      (bbName 1), .Regular⟩), (bbName 1, ⟨[], .ResumeUnwind, .Cleanup⟩)]
  let callerFn := mkMrFn [] [] (localName 0) [(bbName 0, ⟨[], .Goto (bbName 0), .Regular⟩),
     (bbName 1, ⟨[], .StopUnwind (bbName 2), .Cleanup⟩), (bbName 2, ⟨[], .Return, .Regular⟩)]
  let calleeFr : Frame :=
    { func := calleeFn, locals := ⟨[]⟩, stack_pop_action := .BackToCaller (some (bbName 0)) (some (bbName 1)) dummyRetPtr,
      next_block := bbName 0, next_stmt := 0, extra := () }
  mkMrMach (mkMrProg [(fnName 0, callerFn), (fnName 1, calleeFn)]) [] [mkRootFrame callerFn [], calleeFr]
def c2StopUnwindEmptyMach : Mach :=
  let fn := mkMrFn [] [] (localName 0) [(bbName 0, ⟨[], .StopUnwind (bbName 1), .Cleanup⟩), (bbName 1, ⟨[], .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)]) [] [mkRootFrame fn []]
theorem c2_start_resume_stop_unwind_composition_witness : (∃ m1, Interp.step c2UnwindLifecycleMach = .ok m1 ∧
      m1.threads[0]?.map (fun t => (t.stack.length, t.unwind_payloads.map (·.addr))) = some (2, [4096])) ∧
    (∃ m2, Interp.steps 2 c2UnwindLifecycleMach = .ok m2 ∧ m2.threads[0]?.map (fun t =>
        (t.stack.length, t.stack[0]?.map (·.next_block), t.unwind_payloads.map (·.addr))) =
        some (1, some (bbName 1), [4096])) ∧ (∃ m3, Interp.steps 3 c2UnwindLifecycleMach = .ok m3 ∧
      m3.threads[0]?.map (fun t =>
        (t.stack.length, t.stack[0]?.map (·.next_block), t.unwind_payloads.length)) = some (1, some (bbName 2), 0)) ∧
    (∃ m3, Interp.stepsTB 3 (liftMachToTB c2UnwindLifecycleMach) = .ok m3 ∧ MachTB.wfLive m3 ∧ m3.threads[0]?.map (fun t =>
        (t.stack.length, t.stack[0]?.map (·.next_block), t.unwind_payloads.length)) = some (1, some (bbName 2), 0)) ∧
    Interp.step c2StopUnwindEmptyMach = .error (.ub "StopUnwind: the payload stack is empty") ∧
    Interp.stepTB (liftMachToTB c2StopUnwindEmptyMach) = .error (.ub "StopUnwind: the payload stack is empty") :=
  ⟨ok_of_map_toOption (by decide +kernel), ok_of_map_toOption (by decide +kernel),
   ok_of_map_toOption (by decide +kernel), ok_stepsTB_wfLive (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel), eq_error_ub_of_interpUbMsg (by decide +kernel)⟩
/-- **C2 `MachTB` Protector Release on `ResumeUnwind` Witness**: Callee runs
`Validate (.Local 1) true` (installing a Tree Borrows protector on the
caller's `u32` allocation via `&mut u32` arg `_1`), then unwinds via
`ResumeUnwind`; `end_call` releases the callee's protector so caller cleanup
writes `99` without protector UB. -/
def c2TbProtectorUnwindMach : Mach :=
  let calleeFn := mkMrFn [(localName 0, unitType), (localName 1, refTy .mut u32)] [localName 1] (localName 0)
    [(bbName 0, ⟨[.Validate (.Local (localName 1)) true], .ResumeUnwind, .Regular⟩)]
  let callerFn := mkMrFn [(localName 0, u32MrTy)] [] (localName 0) [(bbName 0, ⟨[], .Goto (bbName 1), .Regular⟩),
     (bbName 1, ⟨[.Assign (.Local (localName 0)) (.Constant (.Int 99) u32MrTy)], .Return, .Cleanup⟩)]
  let callerFr := mkRootFrame callerFn [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) })]
  let calleeFr : Frame :=
    { func := calleeFn, locals := ⟨[(localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })]⟩,
      stack_pop_action := .BackToCaller (some (bbName 0)) (some (bbName 1)) dummyRetPtr,
      next_block := bbName 0, next_stmt := 0, extra := () }
  mkMrMach (mkMrProg [(fnName 0, callerFn), (fnName 1, calleeFn)])
    [mkStackAlloc 128 (scalarBytes u32 5) 4, mkStackAlloc 256 (ptrBytes 128 (some (⟨0⟩, ()))) 8] [callerFr, calleeFr]
theorem c2_machTB_protector_release_on_resumeUnwind_witness :
    -- (a) Non-vacuous contrast: step 1 (`Validate`) installs 1 protector on
    -- `calleeFr` so a pre-`ResumeUnwind` caller write to `alloc0` triggers
    -- Tree Borrows protector UB!
    (∃ m1, Interp.stepTB (liftMachToTB c2TbProtectorUnwindMach) = .ok m1 ∧
      m1.threads[0]?.bind (fun t => t.stack[1]?.map (fun (fr : StackFrame TBM) =>
        fr.extra.protectors.length)) = some 1 ∧
      ConcurrentMemory.store m1.mem { addr := 128, provenance := some (⟨0⟩, []) } ((scalarBytes u32 99).map liftByteTB) ⟨4⟩ .None =
        .error (.ub "Tree Borrows: foreign read of protected Unique reference")) ∧
    -- (b) Positive: step 2 (`ResumeUnwind`) runs `end_call`, releasing the
    -- callee protector so step 3's caller write of `99` succeeds with `wfLive`
    (∃ m3, Interp.stepsTB 3 (liftMachToTB c2TbProtectorUnwindMach) = .ok m3 ∧ MachTB.wfLive m3 ∧
      (m3.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB)),
       m3.mem.memory.mem.allocations[1]?.map (·.live)) =
      (some (true, (scalarBytes u32 99).map (projByteTB ∘ liftByteTB)), some false)) ∧
    -- (c) Trusted non-vacuous borrow disabling & protector restore on cleanup
    (let callerSaved : SavedCallerFrame :=
       { callerBody := c2CallerMir, frame := { blockIdx := 0, stmtIdx := 0, locals := [.init (.scalar ⟨5, 4⟩)] },
         destination := locPlace 0, returnTarget := 0, returnUnwind := .cleanup 1, calleeProtectors := [7] }
     let calleeBorrow : BorrowEntry :=
       { tag := 11, targetLocal := 0, targetProjection := [], perm := .reservedFrz false, targetFrameDepth := 1 }
     let callerBorrow : BorrowEntry :=
       { tag := 10, targetLocal := 0, targetProjection := [], perm := .reservedFrz false, targetFrameDepth := 0 }
     let sCallee : MachineState :=
       { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit] },
         memory := { (initMachineState c2LeafMir []).memory with
                     callStack := [callerSaved], activeProtectors := [99], borrows := [calleeBorrow, callerBorrow] } }
     match stepMirFn c2LeafMir sCallee with
     | .tau (.running sAfter) => sAfter.frame.blockIdx = 1 ∧ sAfter.memory.activeProtectors = [7] ∧
       (lookupBorrow sAfter.memory.borrows 11).map (·.perm) = some .disabled ∧
       (lookupBorrow sAfter.memory.borrows 10).map (·.perm) = some (.reservedFrz false)
     | _ => False) := by
  refine ⟨?_, ok_stepsTB_wfLive (by decide +kernel), ⟨rfl, rfl, rfl, rfl⟩⟩
  obtain ⟨m1, hm1, hProt⟩ := ok_of_map_toOption (r := Interp.stepTB (liftMachToTB c2TbProtectorUnwindMach)) (f := fun m1 =>
        (m1.threads[0]?.bind (fun t => t.stack[1]?.map (fun (fr : StackFrame TBM) =>
          fr.extra.protectors.length)),
         interpUbMsg (ConcurrentMemory.store m1.mem { addr := 128, provenance := some (⟨0⟩, []) }
           ((scalarBytes u32 99).map liftByteTB) ⟨4⟩ .None)))
      (b := (some 1, some "Tree Borrows: foreign read of protected Unique reference"))
      (by decide +kernel)
  exact ⟨m1, hm1, congrArg Prod.fst hProt, eq_error_ub_of_interpUbMsg (congrArg Prod.snd hProt)⟩

/-! ## §3 (`C3`): `TerminatorKind.unwindTerminate` (`Mach` & `MachTB`) -/
/-- **C3 Fragment Boundary (`translateTerminator_unwindTerminate_none`)**:
`Translate.translateTerminator` rejects `.unwindTerminate`. -/
theorem translateTerminator_unwindTerminate_none (layouts : LayoutTable) (decls : List MirAst.LocalDecl) (span : String) :
    translateTerminator layouts decls { kind := .unwindTerminate, span := span } = none := rfl
/-- **C3 Universal Lockstep Abort Simulation (`Mach` & `MachTB`)**: For EVERY
Trusted state `s` and EVERY MiniRust `Machine M` (covering both `Mach` and
`MachTB` unconditionally): - Trusted `evalTerminator`, `stepMirFn`, and
`mirTree` on `.unwindTerminate` halt with `MirOutcome.abort`. - MiniRust
`evalTerminatorM m buildAbort` and `stepM m` (`Interp.step` /
`Interp.stepTB`) halt with `.error .abort` (`Stop.abort`). -/
theorem unwindTerminate_lockstep_abort_M {M : Type} [Gen.Memory M] [MemoryOps M]
    (s : MachineState) (span : String) (curBody : Option CapturedMir) (m : Machine M) :
    MirSemantics.evalTerminator s { kind := .unwindTerminate, span := span } curBody = MirStepNode.retOutcome .abort ∧
    evalTerminatorM m buildAbort = .error .abort := by
  refine ⟨rfl, ?_⟩
  unfold evalTerminatorM buildAbort abortTerminator; dsimp only []; rw [evalPlaceM_unitPlace, ok_bind]; rfl
theorem unwindTerminate_step_lockstep_M {M : Type} [Gen.Memory M] [MemoryOps M]
    (body : CapturedMir) (bb : BasicBlockData) (s : MachineState) (span : String)
    (m : Machine M) (fr : StackFrame M) (blk : Gen.BasicBlock)
    (hPhase : (s.memory.activeCallee.getD body).phase = .runtimePostCleanup)
    (hBb : get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx = some bb)
    (hEnd : s.frame.stmtIdx = length bb.statements) (hTerm : bb.terminator = { kind := .unwindTerminate, span := span })
    (hEn : m.threads.any (fun th => decide (th.state = .Enabled)) = true)
    (hPick : pickActiveThreadM { m with mem := { m.mem with accesses := [] } } = .ok m.active_thread)
    (hCur : curFrameM { m with mem := { m.mem with accesses := [] } } = .ok fr)
    (hBlk : mapIndex fr.func.blocks fr.next_block "frame.func.blocks[frame.next_block]" = .ok blk)
    (hMStmt : fr.next_stmt = (blk.statements.length : Int)) (hMTerm : blk.terminator = buildAbort) :
    stepMirFn body s = MirStepNode.retOutcome .abort ∧ (mirTree body s).observe = .ret .abort ∧ stepM m = .error .abort := by
  have hStepT : stepMirFn body s = MirStepNode.retOutcome .abort := by
    unfold stepMirFn
    simp only [hPhase, hBb, hEnd, get?_length_eq_none, beq_self_eq_true, ↓reduceIte, hTerm, MirSemantics.evalTerminator]
  refine ⟨hStepT, by rw [mirTree_observe, hStepT]; rfl, stepM_error_of_evalTerminatorM fr blk hEn hPick hCur hBlk hMStmt
      (by rw [hMTerm]; exact (unwindTerminate_lockstep_abort_M s span none _).2)⟩
/-- **C3 `BasicMemory` (`Mach`) & `TreeBorrowsMemory` (`MachTB`)
Specialization**. -/
theorem unwindTerminate_lockstep_abort_mach_and_tb
    (s : MachineState) (span : String) (curBody : Option CapturedMir) (m : Mach) (mtb : MachTB) :
    MirSemantics.evalTerminator s { kind := .unwindTerminate, span := span } curBody =
      MirStepNode.retOutcome .abort ∧ Interp.evalTerminator m buildAbort = .error .abort ∧
    evalTerminatorM mtb buildAbort = .error .abort := by
  refine ⟨rfl, ?_, (unwindTerminate_lockstep_abort_M s span curBody mtb).2⟩
  rw [← evalTerminatorM_bm_eq]; exact (unwindTerminate_lockstep_abort_M s span curBody m).2
/-- Concrete C3 witness across `stepMirFn`, `Interp.step`, and
`Interp.stepTB`. -/
def c3UnwindTerminateMir : MirAst.CapturedMir :=
  mkMirBody "ep2::c3_unwind_terminate" [mkDecl unitMirTy] 0 [mkBb [] .unwindTerminate true]
def c3AbortMach : Mach :=
  let fn := mkMrFn [] [] (localName 0) [(bbName 0, ⟨[], buildAbort, .Cleanup⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)]) [] [mkRootFrame fn []]
theorem c3_unwindTerminate_three_way_witness : stepMirFn c3UnwindTerminateMir (initMachineState c3UnwindTerminateMir []) =
      MirStepNode.retOutcome .abort ∧ Interp.step c3AbortMach = .error .abort ∧
    Interp.stepTB (liftMachToTB c3AbortMach) = .error .abort :=
  ⟨rfl, eq_error_abort_of_interpIsAbort (by decide +kernel), eq_error_abort_of_interpIsAbort (by decide +kernel)⟩

/-! ## §4 (`C4`): `StatementKind.coverage` (Stuttering Equivalence on `Mach`
& `MachTB`) -/
/-- **C4 Fragment Boundary (`translateStatement_coverage_none`)**:
`Translate.translateStatement` returns `none` on `StatementKind.coverage`. -/
theorem translateStatement_coverage_none (decls : List MirAst.LocalDecl) (span : String) (layouts : LayoutTable) :
    translateStatement decls { kind := .coverage, span := span } layouts = none := rfl
/-- **C4 Universal `stepMirFn` & `mirTree` Stuttering Equivalence
(`coverage_stuttering_step`)**: `minimize` drops `StatementKind::Coverage`
(`0` MiniRust statements emitted). -/
theorem coverage_stuttering_step (body : CapturedMir) (bb : BasicBlockData)
    (s : MachineState) (span : String) (decls : List MirAst.LocalDecl) (layouts : LayoutTable) (m : Mach) (mtb : MachTB)
    (hPhase : (s.memory.activeCallee.getD body).phase = .runtimePostCleanup)
    (hBb : get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx = some bb)
    (hSt : get? bb.statements s.frame.stmtIdx = some { kind := .coverage, span := span }) :
    evalStmt s { kind := .coverage, span := span } decls layouts = MirStepNode.step (advanceStmt s s.frame.locals) ∧
    stepMirFn body s = .tau (.running (advanceStmt s s.frame.locals)) ∧
    (mirTree body s).observe = .tau (mirTree body (advanceStmt s s.frame.locals)) ∧
    (advanceStmt s s.frame.locals).frame.locals = s.frame.locals ∧
    (advanceStmt s s.frame.locals).memory = s.memory ∧ Interp.steps 0 m = .ok m ∧ Interp.stepsTB 0 mtb = .ok mtb := by
  have hStep : stepMirFn body s = .tau (.running (advanceStmt s s.frame.locals)) := by
    unfold stepMirFn; simp only [hPhase, hBb, hSt, evalStmt, MirStepNode.step]
  exact ⟨rfl, hStep, by rw [mirTree_observe, hStep]; rfl, rfl, rfl, rfl, rfl⟩
def c4CoverageMir : MirAst.CapturedMir := mkMirBody "ep2::c4_coverage" [mkDecl u32MirTy] 0
    [mkBb [mkSt .coverage, mkSt (.assign (locPlace 0) (.use (constU32 17)))] .return_]
def c4ErasedMir : MirAst.CapturedMir := mkMirBody "ep2::c4_erased" [mkDecl u32MirTy] 0
    [mkBb [mkSt (.assign (locPlace 0) (.use (constU32 17)))] .return_]
theorem c4_coverage_stuttering_three_way_witness :
    let s0 := initMachineState c4CoverageMir []
    (match stepMirFn c4CoverageMir s0 with
     | .tau (.running s1) =>
       s1.frame.stmtIdx = 1 ∧ s1.frame.locals = s0.frame.locals ∧ s1.memory = s0.memory ∧
       runAVal c4CoverageMir 4 s0 = some (.scalar ⟨17, 4⟩)
     | _ => False) ∧
    retAfter c4ErasedMir [] 3 = some (some (mkStackAlloc 64 (scalarBytes u32 17) 4), [1]) ∧
    retAfterTB c4ErasedMir [] 3 = tbRetU32 17 :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, by decide +kernel, by decide +kernel⟩

/-! ## §5 (`C5`): `StatementKind.backwardIncompatibleDropHint` (`Mach` &
`MachTB`) -/
/-- **C5 Fragment Boundary
(`translateStatement_backwardIncompatibleDropHint_none`)**:
`Translate.translateStatement` returns `none` on
`backwardIncompatibleDropHint`. -/
theorem translateStatement_backwardIncompatibleDropHint_none
    (decls : List MirAst.LocalDecl) (p : MirAst.Place) (span : String) (layouts : LayoutTable) :
    translateStatement decls { kind := .backwardIncompatibleDropHint p, span := span } layouts = none := rfl
/-- **C5 Universal Unconditional `stepMirFn` & `mirTree` Stuttering
Equivalence**: `evalStmt`, `stepMirFn`, and `mirTree` on
`.backwardIncompatibleDropHint p` unconditionally advance `stmtIdx` via a
silent `.tau` transition with identical `locals` and `memory` without ever
reading, dereferencing, or checking `p` (even on `.dead`, `.uninit`, or OOB
places), matching `0` MiniRust steps on `Mach` and `MachTB`. -/
theorem backwardIncompatibleDropHint_stuttering_step
    (body : CapturedMir) (bb : BasicBlockData) (s : MachineState) (p : MirAst.Place) (span : String)
    (decls : List MirAst.LocalDecl) (layouts : LayoutTable) (m : Mach) (mtb : MachTB)
    (hPhase : (s.memory.activeCallee.getD body).phase = .runtimePostCleanup)
    (hBb : get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx = some bb) (hSt : get? bb.statements s.frame.stmtIdx =
      some { kind := .backwardIncompatibleDropHint p, span := span }) :
    evalStmt s { kind := .backwardIncompatibleDropHint p, span := span } decls layouts =
      MirStepNode.step (advanceStmt s s.frame.locals) ∧
    stepMirFn body s = .tau (.running (advanceStmt s s.frame.locals)) ∧
    (mirTree body s).observe = .tau (mirTree body (advanceStmt s s.frame.locals)) ∧
    (advanceStmt s s.frame.locals).frame.locals = s.frame.locals ∧
    (advanceStmt s s.frame.locals).memory = s.memory ∧ Interp.steps 0 m = .ok m ∧ Interp.stepsTB 0 mtb = .ok mtb := by
  have hStep : stepMirFn body s = .tau (.running (advanceStmt s s.frame.locals)) := by
    unfold stepMirFn; simp only [hPhase, hBb, hSt, evalStmt, MirStepNode.step]
  exact ⟨rfl, hStep, by rw [mirTree_observe, hStep]; rfl, rfl, rfl, rfl, rfl⟩
/-- **C4 + C5 Multi-Statement Trace Stuttering Composition
(`erasedNoopStmt_chain_stuttering`)**: Any contiguous sequence `noops` of
`.coverage` and `.backwardIncompatibleDropHint` statements steps in
`noops.length` silent `.tau` steps (`TauSteps`) with identical `locals` and
`memory`, preserves `runA` and `faultsA` traces identically (`runA body (fuel
+ noops.length) s = runA body fuel s'`), and matches `0` MiniRust steps
(`stepsM 0 m = .ok m`) across `Mach` and `MachTB`! -/
inductive IsErasedNoopStmt : MirAst.StatementKind → Prop
  | coverage : IsErasedNoopStmt .coverage
  | dropHint (p : MirAst.Place) : IsErasedNoopStmt (.backwardIncompatibleDropHint p)
inductive TauSteps (body : CapturedMir) : Nat → MachineState → MachineState → Prop
  | zero (s : MachineState) : TauSteps body 0 s s
  | step {k : Nat} {s s1 s2 : MachineState} :
      stepMirFn body s = .tau (.running s1) → TauSteps body k s1 s2 → TauSteps body (k + 1) s s2
theorem TauSteps.runA_and_faultsA {body : CapturedMir} {k : Nat} {s s' : MachineState} (h : TauSteps body k s s') (fuel : Nat) :
    runA body (fuel + k) s = runA body fuel s' ∧ faultsA body (fuel + k) s = faultsA body fuel s' := by
  induction h generalizing fuel with
  | zero _ => exact ⟨rfl, rfl⟩
  | @step k s s1 s2 hStep _ ih =>
    have hEq : fuel + (k + 1) = (fuel + k) + 1 := Nat.add_assoc fuel k 1
    rw [hEq]; simp only [runA, faultsA, hStep]; exact ih fuel
private theorem get?_append_mid {α : Type} : ∀ (pre : List α) (x : α) (rest : List α), get? (pre ++ x :: rest) (length pre) = some x
  | [], _, _ => rfl
  | _ :: ps, x, rest => get?_append_mid ps x rest
private theorem seq_length_snoc {α : Type} : ∀ (xs : List α) (x : α), length (xs ++ [x]) = length xs + 1
  | [], _ => rfl
  | _ :: rs, x => congrArg (· + 1) (seq_length_snoc rs x)
theorem erasedNoopStmt_chain_stuttering {M : Type} [Gen.Memory M] [MemoryOps M]
    (body : CapturedMir) (bb : BasicBlockData) (m : Machine M) :
    ∀ (noops pre post : List MirAst.Statement) (s : MachineState), (∀ st ∈ noops, IsErasedNoopStmt st.kind) →
      (s.memory.activeCallee.getD body).phase = .runtimePostCleanup →
      get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx = some bb →
      bb.statements = pre ++ noops ++ post → s.frame.stmtIdx = length pre →
      let sAfter : MachineState := { s with frame := { s.frame with stmtIdx := length pre + noops.length } }
      TauSteps body noops.length s sAfter ∧ (∀ fuel, runA body (fuel + noops.length) s = runA body fuel sAfter ∧
        faultsA body (fuel + noops.length) s = faultsA body fuel sAfter) ∧
      stepsM 0 m = .ok m := by
  intro noops; induction noops with
  | nil =>
    intro pre post s _ _ _ _ hIdx sAfter
    have hs : sAfter = s := by
      dsimp only [sAfter, List.length_nil]
      cases s with | mk fr mem => cases fr; simp at hIdx; subst hIdx; rfl
    rw [hs]; exact ⟨.zero s, fun _ => ⟨rfl, rfl⟩, rfl⟩
  | cons st rest ih =>
    intro pre post s hAll hPhase hBb hStmts hIdx
    have hStKind := hAll st (List.mem_cons_self ..)
    have hRestKind : ∀ x ∈ rest, IsErasedNoopStmt x.kind := fun x hx => hAll x (List.mem_cons_of_mem st hx)
    have hGet : get? bb.statements s.frame.stmtIdx = some st := by
      rw [hStmts, hIdx, List.append_assoc]; exact get?_append_mid pre st (rest ++ post)
    have hStep1 : stepMirFn body s = .tau (.running (advanceStmt s s.frame.locals)) := by
      rcases st with ⟨k, sp⟩; dsimp only [] at hStKind
      cases hStKind <;> (unfold stepMirFn; simp only [hPhase, hBb, hGet, evalStmt, MirStepNode.step])
    let pre1 := pre ++ [st]
    have hStmts1 : bb.statements = pre1 ++ rest ++ post := by
      simp only [pre1, List.append_assoc, List.singleton_append, hStmts]
    have hIdx1 : (advanceStmt s s.frame.locals).frame.stmtIdx = length pre1 := by
      simp only [advanceStmt, hIdx, pre1, seq_length_snoc]
    obtain ⟨hTauRest, _, _⟩ := ih pre1 post (advanceStmt s s.frame.locals) hRestKind hPhase hBb hStmts1 hIdx1
    have hAfterEq : { advanceStmt s s.frame.locals with
        frame := { (advanceStmt s s.frame.locals).frame with stmtIdx := length pre1 + rest.length } } =
        { s with frame := { s.frame with stmtIdx := length pre + (st :: rest).length } } := by
      simp only [advanceStmt, pre1, seq_length_snoc, List.length_cons]
      have hArith : (length pre + 1) + rest.length = length pre + (rest.length + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 rest.length]
      rw [hArith]
    rw [hAfterEq] at hTauRest
    have hFull : TauSteps body (st :: rest).length s
        { s with frame := { s.frame with stmtIdx := length pre + (st :: rest).length } } :=
      .step hStep1 hTauRest
    exact ⟨hFull, hFull.runA_and_faultsA, rfl⟩
def c5DropHintMir : MirAst.CapturedMir := mkMirBody "ep2::c5_drop_hint" [mkDecl u32MirTy, mkDecl rawMutU32MirTy] 0
    [mkBb [mkSt (.storageDead 1), mkSt .coverage, mkSt (.backwardIncompatibleDropHint (locPlace 1 [.deref])),
           mkSt (.backwardIncompatibleDropHint (locPlace 99)), mkSt (.backwardIncompatibleDropHint (locPlace 0)),
           mkSt (.assign (locPlace 0) (.use (constU32 23)))] .return_]
def c5ErasedMir : MirAst.CapturedMir := mkMirBody "ep2::c5_erased" [mkDecl u32MirTy] 0
    [mkBb [mkSt (.assign (locPlace 0) (.use (constU32 23)))] .return_]
theorem c5_backwardIncompatibleDropHint_dead_place_no_ub_witness :
    let s0 := initMachineState c5DropHintMir []
    runAVal c5DropHintMir 8 s0 = some (.scalar ⟨23, 4⟩) ∧
    retAfter c5ErasedMir [] 3 = some (some (mkStackAlloc 64 (scalarBytes u32 23) 4), [1]) ∧
    retAfterTB c5ErasedMir [] 3 = tbRetU32 23 :=
  ⟨rfl, by decide +kernel, by decide +kernel⟩

/-! ## §6 (`C6`): `CastKind.fnPtrToPtr` (`Mach` & `MachTB`) -/
/-- **C6 Fragment Boundary (`translateRvalue_fnPtrToPtr_none`)**:
`Translate.translateRvalue` rejects `.cast .fnPtrToPtr`. -/
theorem translateRvalue_fnPtrToPtr_none (layouts : LayoutTable) (decls : List MirAst.LocalDecl) (targetTy : Option MirAst.Ty)
    (op : MirAst.Operand) (dstTy : MirAst.Ty) :
    translateRvalue layouts decls targetTy (.cast .fnPtrToPtr op dstTy) = none := rfl
/-- Explicit function-pointer entry relation coupling Trusted `(mem, p)` with
a MiniRust `Machine M` function-pointer table entry `(fnNm, addr, prov)`:
`p.offsetBytes = 0`, `lookupBorrow mem.borrows p.tag = none`, `addr < 2 ^
64`, and `m.fn_ptrs[fnNm] = { addr, provenance := prov }`. -/
def FnPtrEntryRel {M : Type} [Gen.Memory M]
    (mem : MirSemantics.Memory) (p : ProvenancePtr) (m : Machine M) (fnNm : Gen.FnName) (addr : Nat)
    (prov : Option (Gen.Memory.Provenance M)) : Prop := p.offsetBytes = 0 ∧
  lookupBorrow mem.borrows p.tag = none ∧ addr < 2 ^ 64 ∧
  mapIndex m.fn_ptrs fnNm "self.fn_ptrs[fn_name]" = .ok { addr := addr, provenance := prov }
/-- **C6 Universal Coupled Lockstep Simulation
(`fnPtrToPtr_lockstep_mach_and_tb`)**: When `(mem, p)` and MiniRust `(mBM,
fnNm, addr, provBM)` / `(mTB, fnNm, addr, provTB)` satisfy `FnPtrEntryRel`
(an 8-byte function pointer at `offsetBytes = 0`, non-stack,
non-`rustIntrinsic` ABI) cast via `CastKind.fnPtrToPtr` to a thin raw pointer
`dstTy`, Trusted `evalRvalue` preserves `.ptr p 8` in lockstep with MiniRust
`evalConstantM (.FnPointer fnNm)` and `Transmute thinRawPtrTy` on both `Mach`
and `MachTB`. -/
theorem fnPtrToPtr_lockstep_mach_and_tb (locals locals' : List LocalSlot) (op : MirAst.Operand) (dstTy : MirAst.Ty)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (layouts : LayoutTable)
    (p : ProvenancePtr) (fnNm : Gen.FnName) (addr : Nat)
    (provBM : Option Prov) (provTB : Option TreeBorrowsProvenance) (mBM : Mach) (mTB : MachTB)
    (hRelBM : FnPtrEntryRel mem p mBM fnNm addr provBM) (hRelTB : FnPtrEntryRel mem p mTB fnNm addr provTB)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals decls mem.callStack = .ok (.ptr p 8) locals')
    (hDst : isThinRawPtrTy dstTy = true) (hSrc : (match operandTy decls layouts op with
             | .none => true
             | .some { kind := .fnPtr _ _ _ abi, .. } => Bool.not (callConvEq abi .rustIntrinsic)
             | .some _ => false) = true)
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
    evalRvalue locals (.cast .fnPtrToPtr op dstTy) mem decls layouts = .ok (.ptr p 8) locals' mem ∧
    evalConstantM mBM (.FnPointer fnNm) = .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none)) ∧
    evalConstantM mTB (.FnPointer fnNm) = .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none)) ∧
    evalCastOp (.Transmute thinRawPtrTy) (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy)
      (some mBM) = .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy) ∧
    evalCastOpM (M := TBM) (.Transmute thinRawPtrTy)
      (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy)
      (some mTB) = .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy) := by
  rcases hRelBM with ⟨hOff, hNoBorrow, hAddr, hMapBM⟩
  rcases hRelTB with ⟨_, _, _, hMapTB⟩
  refine ⟨?_, ?_, ?_, evalCastOp_transmute_thinRawPtr_id addr hAddr provBM (some mBM),
    evalCastOpM_transmute_thinRawPtr_id (M := TBM) addr hAddr provTB (some mTB)⟩
  · show evalFnPtrToPtr locals op dstTy mem decls layouts = _
    unfold evalFnPtrToPtr; simp only [hOp, hDst, hOff, hNoBorrow, Nat.beq_refl]
    have hBool : ∀ (a b : Bool), a = true → b = true → (match Bool.and true (Bool.and a (Bool.and true (Bool.and true b))) with
         | true => RvalueEvalResult.ok (.ptr p 8) locals' mem
         | false => .ub) = .ok (.ptr p 8) locals' mem := by
      intro a b ha hb; subst ha; subst hb; rfl
    exact hBool _ _ hSrc hFnAlloc
  · unfold evalConstantM
    simp only [hMapBM, bind, Except.bind, pure, Except.pure]
  · unfold evalConstantM
    simp only [hMapTB, bind, Except.bind, pure, Except.pure]
/-- **C6 Explicit Characterization of Trusted Extra Checks vs. MiniRust
`Transmute` (`fnPtrToPtr_extra_checks_divergence`)**: Trusted `evalFnPtrToPtr`
faults with `.ub` on nonzero `offsetBytes`, stack-backed borrows,
`rustIntrinsic` ABI (source type or `entry.fnSig`), missing `mem.fnPtrs` entry,
non-fn-ptr `AllocId` when `mem.fnPtrs = []`, non-thin targets, or `.scalar`
operands, whereas MiniRust `Transmute thinRawPtrTy` succeeds on `Mach` &
`MachTB`. -/
theorem fnPtrToPtr_extra_checks_divergence (locals locals' : List LocalSlot) (op : MirAst.Operand) (dstTy : MirAst.Ty)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (layouts : LayoutTable)
    (p : ProvenancePtr) (addr : Nat) (hAddr : addr < 2 ^ 64) (provBM : Option Prov) (provTB : Option TreeBorrowsProvenance)
    (mBM : Option Mach) (mTB : Option MachTB) (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals decls
      mem.callStack = .ok (.ptr p 8) locals') :
    (p.offsetBytes ≠ 0 → evalRvalue locals (.cast .fnPtrToPtr op dstTy) mem decls layouts = .ub) ∧
    (∀ entry, lookupBorrow mem.borrows p.tag = some entry → evalRvalue locals (.cast .fnPtrToPtr op dstTy) mem decls layouts = .ub) ∧
    (∀ ins out saf, operandTy decls layouts op = some { kind := .fnPtr ins out saf .rustIntrinsic, layoutIdx := 0 } →
      evalRvalue locals (.cast .fnPtrToPtr op dstTy) mem decls layouts = .ub) ∧
    (mem.fnPtrs = [] → isFnPtrAllocId p.allocId = false → evalRvalue locals (.cast .fnPtrToPtr op dstTy) mem decls layouts = .ub) ∧
    (∀ fpHead fpTail, mem.fnPtrs = fpHead :: fpTail → lookupFnPtr mem.fnPtrs p.allocId = none →
      evalRvalue locals (.cast .fnPtrToPtr op dstTy) mem decls layouts = .ub) ∧
    (∀ fpHead fpTail entry ins out saf, mem.fnPtrs = fpHead :: fpTail → lookupFnPtr mem.fnPtrs p.allocId = some entry →
      entry.fnSig = some (.fnPtr ins out saf .rustIntrinsic) →
      evalRvalue locals (.cast .fnPtrToPtr op dstTy) mem decls layouts = .ub) ∧
    (isThinRawPtrTy dstTy = false → evalRvalue locals (.cast .fnPtrToPtr op dstTy) mem decls layouts = .ub) ∧
    (∀ opSc sc, evalOperand locals opSc mem.borrows mem.globals layouts mem.callerLocals decls
        mem.callStack = .ok (.scalar sc) locals' →
      evalRvalue locals (.cast .fnPtrToPtr opSc dstTy) mem decls layouts = .ub) ∧
    evalCastOp (.Transmute thinRawPtrTy) (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy) mBM =
      .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy) ∧
    evalCastOpM (M := TBM) (.Transmute thinRawPtrTy)
      (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy) mTB =
      .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, evalCastOp_transmute_thinRawPtr_id addr hAddr provBM mBM,
    evalCastOpM_transmute_thinRawPtr_id (M := TBM) addr hAddr provTB mTB⟩
  · intro hNe
    have hBeq : Nat.beq p.offsetBytes 0 = false := by
      cases ho : p.offsetBytes with | zero => exact absurd ho hNe | succ _ => rfl
    show evalFnPtrToPtr locals op dstTy mem decls layouts = .ub; unfold evalFnPtrToPtr; simp [hOp, hBeq]
  · intro entry hB; show evalFnPtrToPtr locals op dstTy mem decls layouts = .ub
    unfold evalFnPtrToPtr; simp [hOp, hB]
  · intro ins out saf hIntr; show evalFnPtrToPtr locals op dstTy mem decls layouts = .ub
    unfold evalFnPtrToPtr; simp [hOp, hIntr, callConvEq]
  · intro hNil hNotFn; show evalFnPtrToPtr locals op dstTy mem decls layouts = .ub
    unfold evalFnPtrToPtr
    cases hB : lookupBorrow mem.borrows p.tag <;> simp [hOp, hNil, hNotFn, hB, Bool.and_false]
  · intro fpHead fpTail hFps hMiss
    have hMiss' : lookupFnPtr (fpHead :: fpTail) p.allocId = none := by simpa [hFps] using hMiss
    show evalFnPtrToPtr locals op dstTy mem decls layouts = .ub; unfold evalFnPtrToPtr
    cases hB : lookupBorrow mem.borrows p.tag <;> simp [hOp, hFps, hMiss', hB, Bool.and_false]
  · intro fpHead fpTail entry ins out saf hFps hHit hSig
    have hHit' : lookupFnPtr (fpHead :: fpTail) p.allocId = some entry := by simpa [hFps] using hHit
    show evalFnPtrToPtr locals op dstTy mem decls layouts = .ub; unfold evalFnPtrToPtr
    cases hB : lookupBorrow mem.borrows p.tag <;>
      simp [hOp, hFps, hHit', hSig, hB, callConvEq, Bool.and_false]
  · intro hNotThin; show evalFnPtrToPtr locals op dstTy mem decls layouts = .ub
    unfold evalFnPtrToPtr; simp [hOp, hNotThin]
  · intro opSc sc hOpSc; show evalFnPtrToPtr locals opSc dstTy mem decls layouts = .ub
    unfold evalFnPtrToPtr; simp [hOpSc]
/-- Concrete C6 positive, dead-operand UB, and extra-check divergence
witnesses across `stepMirFn`, `Interp.step`, and `Interp.stepTB`. -/
def c6FnPtrToPtrMir : MirAst.CapturedMir := mkMirBody "ep2::c6_fn_ptr_to_ptr" [mkDecl rawConstUnitMirTy, mkDecl fnPtrSafeU32MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0) (.cast .fnPtrToPtr (.copy (locPlace 1)) rawConstUnitMirTy))] .return_]
def c6FnPtrToPtrMrFn : Gen.Function := mkMrFn [(localName 0, thinRawPtrTy), (localName 1, thinRawPtrTy)] [localName 1] (localName 0)
    [(bbName 0, ⟨[.Assign (.Local (localName 0))
        (.UnOp (.Cast (.Transmute thinRawPtrTy)) (.Load (.Local (localName 1))))], .Return, .Regular⟩)]
def c6FnPtrMach (local1Live : Bool := true) (local1Init : Bool := true) : Mach :=
  let alloc1 := mkStackAlloc 256 (if local1Init then ptrBytes 4096 (some (⟨0⟩, ())) else List.replicate 8 .Uninit) 8
  let locs : List (Gen.LocalName × Ptr) := (localName 0, { addr := 128, provenance := some (⟨1⟩, ()) }) ::
      (if local1Live then [(localName 1, { addr := 256, provenance := some (⟨2⟩, ()) })] else [])
  mkMrMach (mkMrProg [(fnName 0, c6FnPtrToPtrMrFn)]) [mkFnAlloc 4096, mkStackAlloc 128 (List.replicate 8 .Uninit) 8, alloc1]
    [mkRootFrame c6FnPtrToPtrMrFn locs] [(fnName 0, { addr := 4096, provenance := some (⟨0⟩, ()) })]
theorem c6_fnPtrToPtr_three_way_and_ub_witness :
    let fnPtr : ProvenancePtr := { allocId := fnPtrAllocBase, offsetBytes := 0 }
    let sOk := initMachineState c6FnPtrToPtrMir [.ptr fnPtr 8]
    let sDead : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .dead] }, memory := (initMachineState c6FnPtrToPtrMir []).memory }
    let sUninit : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] },
        memory := (initMachineState c6FnPtrToPtrMir []).memory }
    let sNonzero := initMachineState c6FnPtrToPtrMir [.ptr { allocId := fnPtrAllocBase, offsetBytes := 1 } 8]
    (match stepMirFn c6FnPtrToPtrMir sOk with
     | .tau (.running s1) => get? s1.frame.locals 0 = some (.init (.ptr fnPtr 8)) | _ => False) ∧
    (∃ m1, Interp.step (c6FnPtrMach true) = .ok m1 ∧
      m1.mem.memory.allocations[1]?.map (·.data) = some (ptrBytes 4096 (some (⟨0⟩, ())))) ∧
    (∃ m1, Interp.stepTB (liftMachToTB (c6FnPtrMach true)) = .ok m1 ∧ MachTB.wfLive m1 ∧
      m1.mem.memory.mem.allocations[1]?.map (fun a => a.data.map projByteTB) =
        some ((ptrBytes 4096 (some (⟨0⟩, ()))).map (projByteTB ∘ liftByteTB))) ∧
    stepMirFn c6FnPtrToPtrMir sDead = MirStepNode.fail .ub ∧ Interp.step (c6FnPtrMach false) = .error (.ub "access to a dead local") ∧
    Interp.stepTB (liftMachToTB (c6FnPtrMach false)) = .error (.ub "access to a dead local") ∧
    stepMirFn c6FnPtrToPtrMir sUninit = MirStepNode.fail .ub ∧ Interp.step (c6FnPtrMach true false) =
      .error (.ub "load at type but the data in memory violates the language invariant") ∧
    Interp.stepTB (liftMachToTB (c6FnPtrMach true false)) =
      .error (.ub "load at type but the data in memory violates the language invariant") ∧
    stepMirFn c6FnPtrToPtrMir sNonzero = MirStepNode.fail .ub :=
  ⟨rfl, ok_of_map_toOption (by decide +kernel), ok_stepTB_wfLive (by decide +kernel),
   rfl, eq_error_ub_of_interpUbMsg (by decide +kernel), eq_error_ub_of_interpUbMsg (by decide +kernel),
   rfl, eq_error_ub_of_interpUbMsg (by decide +kernel), eq_error_ub_of_interpUbMsg (by decide +kernel), rfl⟩

/-! ## §7 (`C7`): `CastKind.subtype` (`Mach` & `MachTB`) -/
/-- **C7 Fragment Boundary (`translateRvalue_subtype_none`)**:
`Translate.translateRvalue` rejects `.cast .subtype` (even though it accepts
`.cast .transmute` on fragment types). -/
theorem translateRvalue_subtype_none (layouts : LayoutTable) (decls : List MirAst.LocalDecl) (targetTy : Option MirAst.Ty)
    (op : MirAst.Operand) (dstTy : MirAst.Ty) :
    translateRvalue layouts decls targetTy (.cast .subtype op dstTy) = none := rfl
/-- **C7 Trusted Identity with `.transmute`
(`evalRvalue_subtype_eq_transmute`)**: In `Trusted.MirSemantics`,
`CastKind.subtype` and `CastKind.transmute` both reduce definitionally to
`evalByteCast`. -/
theorem evalRvalue_subtype_eq_transmute (locals : List LocalSlot) (op : MirAst.Operand) (dstTy : MirAst.Ty)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (layouts : LayoutTable) :
    evalRvalue locals (.cast .subtype op dstTy) mem decls layouts = evalRvalue locals (.cast .transmute op dstTy) mem decls layouts ∧
    evalRvalue locals (.cast .subtype op dstTy) mem decls layouts = evalByteCast locals op dstTy mem decls layouts := ⟨rfl, rfl⟩
/-- `Classical.choice`-free polymorphic `u32 ↔ i32` transmute (`Mach` &
`MachTB`). -/
theorem transmuteM_u32_to_i32 {M : Type} [Gen.Memory M] [MemoryOps M] (bits : Nat) (hb : bits < 2 ^ 32) (m : Option (Machine M)) :
    transmuteM (M := M) (.Int (intFromBits bits u32)) u32MrTy i32MrTy m = .ok (.Int (intFromBits bits ⟨.Signed, ⟨4⟩⟩)) :=
  transmuteM_int_sameSize u32 ⟨.Signed, ⟨4⟩⟩ rfl (by decide) ⟨4⟩ rfl rfl bits hb m
/-- `Classical.choice`-free polymorphic `u8 → bool` transmute
characterization across `Mach` and `MachTB`. -/
theorem transmuteM_u8_to_bool {M : Type} [Gen.Memory M] [MemoryOps M] (b : Nat) (hb : b < 256) (m : Option (Machine M)) :
    (b = 0 → transmuteM (M := M) (.Int 0) u8MrTy .Bool m = .ok (.Bool false)) ∧
    (b = 1 → transmuteM (M := M) (.Int 1) u8MrTy .Bool m = .ok (.Bool true)) ∧
    (2 ≤ b → transmuteM (M := M) (.Int (Int.ofNat b)) u8MrTy .Bool m = .error (.ub "transmuted value is not valid at new type")) := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun hge => ?_⟩
  have hlt256 : b < 2 ^ (8 * (⟨.Unsigned, ⟨1⟩⟩ : Gen.IntType).size.bytes) := by simpa using hb
  have hU8Ne0 : UInt8.ofNat (b % 256) ≠ 0 := by
    intro h0; have := congrArg UInt8.toNat h0
    simp only [UInt8.toNat_ofNat', UInt8.toNat_zero, Nat.mod_eq_of_lt hb,
      show (2 : Nat) ^ 8 = 256 by decide] at this
    exact Nat.not_le_of_lt (by decide : 0 < 2) (by rw [← this]; exact hge)
  have hU8Ne1 : UInt8.ofNat (b % 256) ≠ 1 := by
    intro h1; have := congrArg UInt8.toNat h1
    simp only [UInt8.toNat_ofNat', UInt8.toNat_one, Nat.mod_eq_of_lt hb,
      show (2 : Nat) ^ 8 = 256 by decide] at this
    exact Nat.not_le_of_lt (by decide : 1 < 2) (by rw [← this]; exact hge)
  unfold transmuteM
  have hlay1 : Type.layout u8MrTy = .ok (.Sized ⟨1⟩ ⟨1⟩) := rfl
  have hlay2 : Type.layout .Bool = .ok (.Sized ⟨1⟩ ⟨1⟩) := rfl
  rw [hlay1, ok_bind, expect_size_sized, ok_bind, hlay2, ok_bind, expect_size_sized, ok_bind, size_ne_self_ite_local]
  have henc : Type.encodeM (M := M) u8MrTy (.Int (Int.ofNat b)) = .ok [.Init (UInt8.ofNat (b % 256)) none] := by
    simpa [u8MrTy, Type.encodeM, intFromBits, leBytes] using encodeIntM_intFromBits (M := M) ⟨.Unsigned, ⟨1⟩⟩ (by decide) b hlt256
  have hDecNone : ∀ (x : UInt8), x ≠ 0 → x ≠ 1 → Type.decodeM (M := M) .Bool [.Init x none] = .ok none := by
    intro x hx0 hx1; unfold Type.decodeM; simp only [List.length, ne_eq, not_true_eq_false, ↓reduceIte]
    split
    · rename_i heq; cases heq; exact absurd rfl hx0
    · rename_i heq; cases heq; exact absurd rfl hx1
    · rfl
  rw [henc, ok_bind, hDecNone _ hU8Ne0 hU8Ne1, ok_bind]; rfl
/-- Full niche-constrained `NonZeroU8` MiniRust `Type.Enum` accepting ALL `1
≤ b ≤ 255` (`[((1, 256), .Known 0)]`) and rejecting byte `0` (`.Invalid`),
matching Rust's `#[rustc_layout_scalar_valid_range_start(1)]` and
`nonZeroU8MirLayout`. -/
def nonZeroU8MrTy : Gen.Type := .Enum ⟨[(0, ⟨u8MrTy, ⟨[]⟩⟩)]⟩ ⟨.Unsigned, ⟨1⟩⟩
    (.Branch ⟨0⟩ ⟨.Unsigned, ⟨1⟩⟩ .Invalid ⟨[((1, 256), .Known 0)]⟩) ⟨1⟩ ⟨1⟩
/-- `NonZeroU8` Anneal `TypeLayout` (1-field struct enforcing `validRange :=
⟨1, 255⟩`). -/
def nonZeroU8MirLayout : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩, backendRepr := .scalar (.initialized (.int 8 false) ⟨1, 255⟩),
    fields := .arbitrary [⟨0⟩] [0], variants := .single 0, isUninhabited := false }
def nonZeroU8Layouts : LayoutTable := { pointerBits := 64, isLittleEndian := true, entries := [nonZeroU8MirLayout] }
@[reducible] def nonZeroU8MirTy : MirAst.Ty := { kind := .adt "core::num::nonzero::NonZero" [.uint .u8], layoutIdx := 0 }
theorem checkValueM_int_of_inBounds {M : Type} [Gen.Memory M] [MemoryOps M]
    (i : Int) (it : Gen.IntType) (m : Option (Machine M)) (hin : inBounds i it.signed it.size = true) :
    checkValueM (M := M) (.Int i) (.Int it) m = .ok () := by
  unfold checkValueM IntType.can_represent ensureElseUb; rw [hin]; rfl
/-- `Classical.choice`-free polymorphic `u8 → NonZeroU8` transmute across ALL
`b < 256` on `Mach` & `MachTB`: `b = 0` faults with UB; every `1 ≤ b < 256`
succeeds returning `.Variant 0 (.Int b)`. -/
theorem transmuteM_u8_to_nonZeroU8 {M : Type} [Gen.Memory M] [MemoryOps M] (b : Nat) (hb : b < 256) (m : Option (Machine M)) :
    (b = 0 → transmuteM (M := M) (.Int 0) u8MrTy nonZeroU8MrTy m = .error (.ub "transmuted value is not valid at new type")) ∧
    (1 ≤ b → transmuteM (M := M) (.Int (Int.ofNat b)) u8MrTy nonZeroU8MrTy m = .ok (.Variant 0 (.Int (Int.ofNat b)))) := by
  refine ⟨fun _ => rfl, fun h1 => ?_⟩
  have hlt256 : b < 2 ^ (8 * (⟨.Unsigned, ⟨1⟩⟩ : Gen.IntType).size.bytes) := by simpa using hb
  have hInt : intFromBits b ⟨.Unsigned, ⟨1⟩⟩ = Int.ofNat b := rfl
  let bs : List (AbstractByte (Gen.Memory.Provenance M)) := (leBytes b 1).map (fun x => .Init x none)
  have hlay1 : Type.layout u8MrTy = .ok (.Sized ⟨1⟩ ⟨1⟩) := rfl
  have hlay2 : Type.layout nonZeroU8MrTy = .ok (.Sized ⟨1⟩ ⟨1⟩) := rfl
  have henc : Type.encodeM (M := M) u8MrTy (.Int (Int.ofNat b)) = .ok bs := by
    simpa [u8MrTy, Type.encodeM, hInt, bs] using encodeIntM_intFromBits (M := M) ⟨.Unsigned, ⟨1⟩⟩ (by decide) b hlt256
  have hDecInt : Type.decodeIntM (M := M) ⟨.Unsigned, ⟨1⟩⟩ bs = .ok (some (.Int (Int.ofNat b))) := by
    simpa [hInt, bs] using decodeIntM_leBytes (M := M) ⟨.Unsigned, ⟨1⟩⟩ (by decide) b hlt256
  have hRange : (1 : Int) ≤ Int.ofNat b ∧ Int.ofNat b < 256 := ⟨Int.ofNat_le.mpr h1, Int.ofNat_lt.mpr hb⟩
  have hSub : subsliceWithLength bs 0 ((1 : Nat) : Int) = .ok bs := rfl
  have hDecNz : Type.decodeM (M := M) nonZeroU8MrTy bs = .ok (some (.Variant 0 (.Int (Int.ofNat b)))) := by
    unfold nonZeroU8MrTy Type.decodeM
    have hBsLen : bs.length = 1 := rfl
    rw [ite_eq_right_iff.mpr (fun hn => absurd hBsLen hn)]; dsimp only [decodeDiscriminantM, bind, Except.bind, pure, Except.pure]
    rw [show ((0 : Nat) : Int) = 0 from rfl, hSub]; dsimp only []; rw [hDecInt]; dsimp only [decodeDiscriminantChildrenM]
    rw [ite_eq_left_iff.mpr (fun hn => absurd hRange hn)]
    dsimp only [decodeDiscriminantM, Type.decodeVariantM, ↓reduceIte, u8MrTy, Type.decodeM]
    rw [hDecInt]; rfl
  have hChk : checkValueM (M := M) (.Variant 0 (.Int (Int.ofNat b))) nonZeroU8MrTy m = .ok () := by
    simp only [nonZeroU8MrTy, checkValueM, checkVariantM, ↓reduceIte, u8MrTy]
    exact checkValueM_int_of_inBounds _ ⟨.Unsigned, ⟨1⟩⟩ m (inBounds_intFromBits_cf ⟨.Unsigned, ⟨1⟩⟩ (by decide) b hlt256)
  unfold transmuteM
  rw [hlay1, ok_bind, expect_size_sized, ok_bind, hlay2, ok_bind, expect_size_sized, ok_bind,
    size_ne_self_ite_local, henc, ok_bind, hDecNz, ok_bind]
  dsimp only []; rw [hChk, ok_bind]; rfl
/-- **C7 Hypothesis-Free Coupled Two-Sided Thin-Pointer, Integer, Bool, &
`NonZeroU8` `CastKind.subtype` Simulation
(`subtype_thinPtr_and_u32_coupled_lockstep`)**: Using our
`Classical.choice`-free Trusted and MiniRust byte codecs (ZERO unproved codec
hypotheses!), proves universal lockstep between Trusted `evalRvalue ...
(.cast .subtype ...)` (`evalByteCast`) and MiniRust `evalCastOp` (`Mach`) +
`evalCastOpM` / `transmuteM` (`MachTB`) across: 1. `*mut u32 → *const u32`
for EVERY `p` with `p.offsetBytes < 2 ^ 64`, 2. `u32 → i32` for EVERY `bits <
2 ^ 32`, 3. `u8 → bool` for EVERY `b < 256` (BOTH positive `b ∈ {0, 1}` AND
invalid `2 ≤ b` lockstep UB!), and 4. `u8 → NonZeroU8` for EVERY `b < 256`
(`b = 0` lockstep UB AND `1 ≤ b < 256` positive lockstep across
`nonZeroU8Layouts` & `nonZeroU8MrTy`!). -/
theorem subtype_thinPtr_and_u32_coupled_lockstep (locals locals' : List LocalSlot) (op : MirAst.Operand) (mem : MirSemantics.Memory)
    (p : ProvenancePtr) (hpOff : p.offsetBytes < 2 ^ 64)
    (addr bits b : Nat) (hAddr : addr < 2 ^ 64) (hBits : bits < 2 ^ 32) (hb : b < 256)
    (provBM : Option Prov) (provTB : Option TreeBorrowsProvenance) (mBM : Option Mach) (mTB : Option MachTB) :
    let declsPtr := [mkDecl rawConstU32MirTy, mkDecl rawMutU32MirTy]
    let declsInt := [mkDecl i32MirTy, mkDecl u32MirTy]
    let declsBool := [mkDecl boolMirTy, mkDecl u8MirTy]
    let declsNz := [mkDecl nonZeroU8MirTy, mkDecl u8MirTy]
    -- (1) Universal thin pointer subtyping (*mut u32 -> *const u32)
    (evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals declsPtr mem.callStack = .ok (.ptr p 8) locals' →
      operandTy declsPtr emptyLayoutTable op = some rawMutU32MirTy →
      evalRvalue locals (.cast .subtype op rawConstU32MirTy) mem declsPtr emptyLayoutTable =
        .ok (.ptr p 8) locals' mem ∧ evalCastOp (.Transmute thinRawPtrTy)
        (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy) mBM =
        .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy) ∧
      evalCastOpM (M := TBM) (.Transmute thinRawPtrTy)
        (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy) mTB =
        .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy)) ∧
    -- (2) Universal int reinterpretation (u32 -> i32) on Trusted, Mach, MachTB
    (evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals declsInt
        mem.callStack = .ok (.scalar ⟨bits, 4⟩) locals' →
      operandTy declsInt emptyLayoutTable op = some u32MirTy →
      evalRvalue locals (.cast .subtype op i32MirTy) mem declsInt emptyLayoutTable = .ok (.scalar ⟨bits, 4⟩) locals' mem ∧
      transmuteM (M := BM) (.Int (intFromBits bits u32)) u32MrTy i32MrTy mBM = .ok (.Int (intFromBits bits ⟨.Signed, ⟨4⟩⟩)) ∧
      transmuteM (M := TBM) (.Int (intFromBits bits u32)) u32MrTy i32MrTy mTB = .ok (.Int (intFromBits bits ⟨.Signed, ⟨4⟩⟩))) ∧
    -- (3a) Positive u8 -> bool (b = 0 or b = 1) on Trusted, Mach, MachTB
    ((b = 0 ∨ b = 1) → evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals declsBool
        mem.callStack = .ok (.scalar ⟨b, 1⟩) locals' →
      operandTy declsBool emptyLayoutTable op = some u8MirTy →
      evalRvalue locals (.cast .subtype op boolMirTy) mem declsBool emptyLayoutTable = .ok (.scalar ⟨b, 1⟩) locals' mem ∧
      transmuteM (M := BM) (.Int (Int.ofNat b)) u8MrTy .Bool mBM = .ok (.Bool (b == 1)) ∧
      transmuteM (M := TBM) (.Int (Int.ofNat b)) u8MrTy .Bool mTB = .ok (.Bool (b == 1))) ∧
    -- (3b) Universal invalid-bool UB (u8 b >= 2 -> bool), Trusted/Mach/MachTB
    (2 ≤ b → evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals declsBool
        mem.callStack = .ok (.scalar ⟨b, 1⟩) locals' →
      operandTy declsBool emptyLayoutTable op = some u8MirTy →
      evalRvalue locals (.cast .subtype op boolMirTy) mem declsBool emptyLayoutTable = .ub ∧
      transmuteM (M := BM) (.Int (Int.ofNat b)) u8MrTy .Bool mBM = .error (.ub "transmuted value is not valid at new type") ∧
      transmuteM (M := TBM) (.Int (Int.ofNat b)) u8MrTy .Bool mTB = .error (.ub "transmuted value is not valid at new type")) ∧
    -- (4) Universal u8 -> NonZeroU8 (b = 0 UB vs 1 <= b < 256 valid)
    (evalOperand locals op mem.borrows mem.globals nonZeroU8Layouts mem.callerLocals declsNz
        mem.callStack = .ok (.scalar ⟨0, 1⟩) locals' →
      operandTy declsNz nonZeroU8Layouts op = some u8MirTy →
      evalRvalue locals (.cast .subtype op nonZeroU8MirTy) mem declsNz nonZeroU8Layouts = .ub ∧
      transmuteM (M := BM) (.Int 0) u8MrTy nonZeroU8MrTy mBM = .error (.ub "transmuted value is not valid at new type") ∧
      transmuteM (M := TBM) (.Int 0) u8MrTy nonZeroU8MrTy mTB = .error (.ub "transmuted value is not valid at new type")) ∧
    (1 ≤ b → evalOperand locals op mem.borrows mem.globals nonZeroU8Layouts mem.callerLocals declsNz
        mem.callStack = .ok (.scalar ⟨b, 1⟩) locals' →
      operandTy declsNz nonZeroU8Layouts op = some u8MirTy →
      evalRvalue locals (.cast .subtype op nonZeroU8MirTy) mem declsNz nonZeroU8Layouts =
        .ok (.aggregate 0 [.scalar ⟨b, 1⟩]) locals' mem ∧
      transmuteM (M := BM) (.Int (Int.ofNat b)) u8MrTy nonZeroU8MrTy mBM = .ok (.Variant 0 (.Int (Int.ofNat b))) ∧
      transmuteM (M := TBM) (.Int (Int.ofNat b)) u8MrTy nonZeroU8MrTy mTB = .ok (.Variant 0 (.Int (Int.ofNat b)))) := by
  intro declsPtr declsInt declsBool declsNz
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hOp hSrcTy
    refine ⟨?_, evalCastOp_transmute_thinRawPtr_id addr hAddr provBM mBM,
      evalCastOpM_transmute_thinRawPtr_id (M := TBM) addr hAddr provTB mTB⟩
    have hEnc : encodeByteCastSourceBytes emptyLayoutTable rawMutU32MirTy (.ptr p 8) =
        some (encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))) := rfl
    have hLen : length (encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))) = 8 :=
      encodeLittleEndianBytes_len p.offsetBytes 8 _
    have h256 : p.offsetBytes < 256 ^ 8 := by
      rw [show (256 : Nat) ^ 8 = 2 ^ 64 by decide]; exact hpOff
    have hDecAux : ∀ bs, length bs = 8 → decodeLittleEndianBytes bs = some (p.offsetBytes, some (p.allocId, p.tag)) →
        abstractBytesUniformProv bs = true → decodePtrBytesNoForge false (.uint .u32) 8 bs = some (.ptr p 8) := by
      intro bs hl hd hu; unfold decodePtrBytesNoForge decodeScalarBytes; simp [hl, hd, hu]
    have hDec : decodeTypedValueFromBytes defaultCodecFuel emptyLayoutTable rawConstU32MirTy
        (encodeLittleEndianBytes p.offsetBytes 8 (some (p.allocId, p.tag))) = some (.ptr p 8) :=
      hDecAux _ hLen (by rw [decodeLittleEndianBytes_encode, Nat.mod_eq_of_lt h256]; rfl)
        (abstractBytesAllProvAux_encode p.allocId p.tag (Nat.div p.offsetBytes 256) 7)
    have hRD : resolveTyWithLocalDecls declsPtr emptyLayoutTable rawConstU32MirTy = rawConstU32MirTy := rfl
    have hRS : resolveTyWithLocalDecls declsPtr emptyLayoutTable rawMutU32MirTy = rawMutU32MirTy := rfl
    have hSD : tyByteSize declsPtr emptyLayoutTable rawConstU32MirTy = some 8 := rfl
    have hSS : tyByteSize declsPtr emptyLayoutTable rawMutU32MirTy = some 8 := rfl
    show evalByteCast locals op rawConstU32MirTy mem declsPtr emptyLayoutTable = _
    unfold evalByteCast; simp only [hOp, hRD, hSD, hSrcTy, hRS, hSS, hEnc, hLen, hDec, Nat.beq_refl]
  · intro hOp hSrcTy
    refine ⟨?_, transmuteM_u32_to_i32 bits hBits mBM, transmuteM_u32_to_i32 bits hBits mTB⟩
    have hEnc : encodeByteCastSourceBytes emptyLayoutTable u32MirTy (.scalar ⟨bits, 4⟩) =
        some (encodeLittleEndianBytes bits 4 none) := rfl
    have hLen : length (encodeLittleEndianBytes bits 4 none) = 4 := encodeLittleEndianBytes_len bits 4 none
    have h256 : bits < 256 ^ 4 := by rw [show (256 : Nat) ^ 4 = 2 ^ 32 by decide]; exact hBits
    have hDecAux : ∀ bs, length bs = 4 → decodeLittleEndianBytes bs = some (bits, none) →
        decodeValueFromBytes 16 emptyLayoutTable i32MirTy bs = some (.scalar ⟨bits, 4⟩) := by
      intro bs hl hd; unfold decodeValueFromBytes decodeScalarBytes; simp [i32MirTy, hl, hd]; rfl
    have hDec : decodeTypedValueFromBytes defaultCodecFuel emptyLayoutTable i32MirTy
        (encodeLittleEndianBytes bits 4 none) = some (.scalar ⟨bits, 4⟩) :=
      hDecAux _ hLen (by rw [decodeLittleEndianBytes_encode, Nat.mod_eq_of_lt h256]; rfl)
    have hRD : resolveTyWithLocalDecls declsInt emptyLayoutTable i32MirTy = i32MirTy := rfl
    have hRS : resolveTyWithLocalDecls declsInt emptyLayoutTable u32MirTy = u32MirTy := rfl
    have hSD : tyByteSize declsInt emptyLayoutTable i32MirTy = some 4 := rfl
    have hSS : tyByteSize declsInt emptyLayoutTable u32MirTy = some 4 := rfl
    show evalByteCast locals op i32MirTy mem declsInt emptyLayoutTable = _
    unfold evalByteCast; simp only [hOp, hRD, hSD, hSrcTy, hRS, hSS, hEnc, hLen, hDec, Nat.beq_refl]
  · intro hb01 hOp hSrcTy
    rcases hb01 with rfl | rfl <;> (
      refine ⟨?_, rfl, rfl⟩
      show evalByteCast locals op boolMirTy mem declsBool emptyLayoutTable = _
      unfold evalByteCast; simp only [hOp, hSrcTy]; rfl)
  · intro hGe hOp hSrcTy
    refine ⟨?_, (transmuteM_u8_to_bool b hb mBM).2.2 hGe, (transmuteM_u8_to_bool b hb mTB).2.2 hGe⟩
    have hB : (UInt8.ofNat b).toBitVec.toNat = b := by
      change (UInt8.ofNat b).toNat = b; rw [UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt hb
    have hDec : decodeTypedValueFromBytes defaultCodecFuel emptyLayoutTable boolMirTy (encodeLittleEndianBytes b 1 none) = none := by
      change (match (UInt8.ofNat b).toBitVec.toNat.beq 0 with
        | true => some (MirSemantics.Value.scalar ⟨0, 1⟩)
        | false => match (UInt8.ofNat b).toBitVec.toNat.beq 1 with
          | true => some (MirSemantics.Value.scalar ⟨1, 1⟩) | false => none) = none
      rw [hB]; cases b with
      | zero => exact absurd hGe (by decide)
      | succ k => cases k with | zero => exact absurd hGe (by decide) | succ _ => rfl
    have hRD : resolveTyWithLocalDecls declsBool emptyLayoutTable boolMirTy = boolMirTy := rfl
    have hRS : resolveTyWithLocalDecls declsBool emptyLayoutTable u8MirTy = u8MirTy := rfl
    have hSD : tyByteSize declsBool emptyLayoutTable boolMirTy = some 1 := rfl
    have hSS : tyByteSize declsBool emptyLayoutTable u8MirTy = some 1 := rfl
    have hEnc : encodeByteCastSourceBytes emptyLayoutTable u8MirTy (.scalar ⟨b, 1⟩) = some (encodeLittleEndianBytes b 1 none) := rfl
    have hLen : length (encodeLittleEndianBytes b 1 none) = 1 := rfl
    show evalByteCast locals op boolMirTy mem declsBool emptyLayoutTable = .ub
    unfold evalByteCast; simp only [hOp, hRD, hSD, hSrcTy, hRS, hSS, hEnc, hLen, hDec, Nat.beq_refl]
  · intro hOp hSrcTy
    refine ⟨?_, rfl, rfl⟩
    show evalByteCast locals op nonZeroU8MirTy mem declsNz nonZeroU8Layouts = .ub
    unfold evalByteCast; simp only [hOp, hSrcTy]; rfl
  · intro h1 hOp hSrcTy
    refine ⟨?_, (transmuteM_u8_to_nonZeroU8 b hb mBM).2 h1, (transmuteM_u8_to_nonZeroU8 b hb mTB).2 h1⟩
    have hLe1 : Nat.ble 1 b = true := Nat.ble_eq.mpr h1
    have hLe255 : Nat.ble b 255 = true := Nat.ble_eq.mpr (Nat.le_of_lt_succ hb)
    have hScAux : ∀ bs, length bs = 1 → abstractBytesHaveProv bs = false → decodeLittleEndianBytes bs = some (b, none) →
        decodeScalarLayoutBytesNoForge (.initialized (.int 8 false) ⟨1, 255⟩) bs = some (.scalar ⟨b, 1⟩) := by
      intro bs hl hp hd; unfold decodeScalarLayoutBytesNoForge scalarLayoutByteWidth primitiveKindByteWidth
        decodeScalarBytes wrappingRangeContains
      simp [hl, hp, hd, hLe1, hLe255]; rfl
    have hSc : decodeScalarLayoutBytesNoForge (.initialized (.int 8 false) ⟨1, 255⟩)
        (encodeLittleEndianBytes b 1 none) = some (.scalar ⟨b, 1⟩) :=
      hScAux _ rfl rfl (by
        rw [decodeLittleEndianBytes_encode, show 256 ^ 1 = 256 from rfl, Nat.mod_eq_of_lt hb]; rfl)
    have hDec : decodeTypedValueFromBytes defaultCodecFuel nonZeroU8Layouts nonZeroU8MirTy
        (encodeLittleEndianBytes b 1 none) = some (.aggregate 0 [.scalar ⟨b, 1⟩]) := by
      unfold decodeTypedValueFromBytes
      dsimp only [defaultCodecFuel, normalizeCodecTy, nonZeroU8MirTy, nonZeroU8Layouts,
        nonZeroU8MirLayout, LayoutTable.lookup, get?, scalarLayoutByteWidth, primitiveKindByteWidth,
        sliceAbstractBytes, takeAbstractBytes, dropAbstractBytes, encodeLittleEndianBytes, length,
        Nat.beq_refl, Bool.not_true, Bool.or_false]
      change (match decodeScalarLayoutBytesNoForge (.initialized (.int 8 false) ⟨1, 255⟩) (encodeLittleEndianBytes b 1 none) with
        | some v0 => some (MirSemantics.Value.aggregate 0 [v0])
        | none => none) = _
      rw [hSc]
    have hRD : resolveTyWithLocalDecls declsNz nonZeroU8Layouts nonZeroU8MirTy = nonZeroU8MirTy := rfl
    have hRS : resolveTyWithLocalDecls declsNz nonZeroU8Layouts u8MirTy = u8MirTy := rfl
    have hSD : tyByteSize declsNz nonZeroU8Layouts nonZeroU8MirTy = some 1 := rfl
    have hSS : tyByteSize declsNz nonZeroU8Layouts u8MirTy = some 1 := rfl
    have hEnc : encodeByteCastSourceBytes nonZeroU8Layouts u8MirTy (.scalar ⟨b, 1⟩) = some (encodeLittleEndianBytes b 1 none) := rfl
    have hLen : length (encodeLittleEndianBytes b 1 none) = 1 := rfl
    show evalByteCast locals op nonZeroU8MirTy mem declsNz nonZeroU8Layouts = _
    unfold evalByteCast; simp only [hOp, hRD, hSD, hSrcTy, hRS, hSS, hEnc, hLen, hDec, Nat.beq_refl]
/-- **C7 Size-Mismatch Boundary (`subtype_size_mismatch_boundary_M`)**: On
mismatched sizes (`u32` 4 bytes → `u8` 1 byte), Trusted `evalByteCast` returns
`.unsupported`, MiniRust `evalCastOpM (.Transmute u8MrTy)` faults with `.ub`,
and `transmuteM` raises `specPanic` across both `Mach` and `MachTB`. -/
theorem subtype_size_mismatch_boundary_M {M : Type} [Gen.Memory M] [MemoryOps M]
    (locals locals' : List LocalSlot) (op : MirAst.Operand) (vT : MirSemantics.Value)
    (mem : MirSemantics.Memory) (vM : Gen.Value M) (m : Option (Machine M)) :
    let decls := [mkDecl u8MirTy, mkDecl u32MirTy]
    (evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls mem.callStack = .ok vT locals' →
      operandTy decls emptyLayoutTable op = some u32MirTy →
      evalRvalue locals (.cast .subtype op u8MirTy) mem decls emptyLayoutTable = .unsupported) ∧
    evalCastOpM (M := M) (.Transmute u8MrTy) (vM, u32MrTy) m = .error (.ub "transmute between types of different size") ∧
    transmuteM (M := M) vM u32MrTy u8MrTy m = .error (.specPanic "assertion failed: transmute between types of different size") := by
  intro decls; refine ⟨fun hOp hSrc => ?_, rfl, rfl⟩
  show evalByteCast locals op u8MirTy mem decls emptyLayoutTable = .unsupported
  unfold evalByteCast; simp only [hOp, hSrc]; rfl
def c7SubtypeU32ToI32Mir : MirAst.CapturedMir := mkMirBody "ep2::c7_subtype_u32_i32" [mkDecl i32MirTy, mkDecl u32MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0) (.cast .subtype (.copy (locPlace 1)) i32MirTy))] .return_]
def c7SubtypeU8ToBoolMir : MirAst.CapturedMir := mkMirBody "ep2::c7_subtype_u8_bool" [mkDecl boolMirTy, mkDecl u8MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0) (.cast .subtype (.copy (locPlace 1)) boolMirTy))] .return_]
def c7SubtypeU8ToNzMir : MirAst.CapturedMir := mkMirBody "ep2::c7_subtype_u8_nz" [mkDecl nonZeroU8MirTy, mkDecl u8MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0) (.cast .subtype (.copy (locPlace 1)) nonZeroU8MirTy))] .return_]
    nonZeroU8Layouts
def c7SubtypePtrMir : MirAst.CapturedMir := mkMirBody "ep2::c7_subtype_ptr" [mkDecl rawConstU32MirTy, mkDecl rawMutU32MirTy] 1
    [mkBb [mkSt (.assign (locPlace 0) (.cast .subtype (.copy (locPlace 1)) rawConstU32MirTy))] .return_]
def c7MkTransmuteMach (srcTy dstTy : Gen.Type) (srcBytes : List Byte) (sz : Nat) : Mach :=
  let fn := mkMrFn [(localName 0, dstTy), (localName 1, srcTy)] [localName 1] (localName 0)
    [(bbName 0, ⟨[.Assign (.Local (localName 0))
        (.UnOp (.Cast (.Transmute dstTy)) (.Load (.Local (localName 1))))], .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)]) [mkStackAlloc 128 (List.replicate sz .Uninit) sz, mkStackAlloc 256 srcBytes sz]
    [mkRootFrame fn [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
                     (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })]]
/-- **C7 Concrete Positive & Invalid-Bit-Pattern UB Witness (`Mach` & `MachTB`
with `MachTB.wfLive`)**: `u32(4294967295)→i32(-1)`, `*mut u32→*const u32`,
`u8(1)→bool(true)` vs. `u8(2)→bool` UB, and `u8(2), u8(7)→NonZeroU8` vs.
`u8(0)→NonZeroU8` UB. -/
theorem c7_subtype_positive_and_invalid_ub_three_way_witness :
    let ptrB := ptrBytes 256 (some (⟨1⟩, ()))
    let negB := scalarBytes u32 4294967295
    runAVal c7SubtypeU32ToI32Mir 4 (initMachineState c7SubtypeU32ToI32Mir [.scalar ⟨4294967295, 4⟩]) =
      some (.scalar ⟨4294967295, 4⟩) ∧
    (∃ m1, Interp.step (c7MkTransmuteMach u32MrTy i32MrTy negB 4) = .ok m1 ∧ m1.mem.memory.allocations[0]?.map (·.data) = some negB) ∧
    (∃ m1, Interp.stepTB (liftMachToTB (c7MkTransmuteMach u32MrTy i32MrTy negB 4)) = .ok m1 ∧
      MachTB.wfLive m1 ∧ m1.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some (negB.map (projByteTB ∘ liftByteTB))) ∧
    runAVal c7SubtypePtrMir 4 (initMachineState c7SubtypePtrMir [.ptr { allocId := 5, offsetBytes := 0 } 8]) =
      some (.ptr { allocId := 5, offsetBytes := 0 } 8) ∧
    (∃ m1, Interp.step (c7MkTransmuteMach thinRawPtrTy thinRawPtrTy ptrB 8) = .ok m1 ∧
      m1.mem.memory.allocations[0]?.map (·.data) = some ptrB) ∧
    (∃ m1, Interp.stepTB (liftMachToTB (c7MkTransmuteMach thinRawPtrTy thinRawPtrTy ptrB 8)) = .ok m1 ∧
      MachTB.wfLive m1 ∧ m1.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some (ptrB.map (projByteTB ∘ liftByteTB))) ∧
    runAVal c7SubtypeU8ToBoolMir 4 (initMachineState c7SubtypeU8ToBoolMir [.scalar ⟨1, 1⟩]) = some (.scalar ⟨1, 1⟩) ∧
    (∃ m1, Interp.step (c7MkTransmuteMach u8MrTy .Bool [.Init 1 none] 1) = .ok m1 ∧
      m1.mem.memory.allocations[0]?.map (·.data) = some [.Init 1 none]) ∧
    (∃ m1, Interp.stepTB (liftMachToTB (c7MkTransmuteMach u8MrTy .Bool [.Init 1 none] 1)) = .ok m1 ∧
      MachTB.wfLive m1 ∧ m1.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) = some [.initNoProv 1]) ∧
    stepMirFn c7SubtypeU8ToBoolMir (initMachineState c7SubtypeU8ToBoolMir [.scalar ⟨2, 1⟩]) =
      MirStepNode.fail .ub ∧ Interp.step (c7MkTransmuteMach u8MrTy .Bool [.Init 2 none] 1) =
      .error (.ub "transmuted value is not valid at new type") ∧
    Interp.stepTB (liftMachToTB (c7MkTransmuteMach u8MrTy .Bool [.Init 2 none] 1)) =
      .error (.ub "transmuted value is not valid at new type") ∧
    runAVal c7SubtypeU8ToNzMir 4 (initMachineState c7SubtypeU8ToNzMir [.scalar ⟨2, 1⟩]) = some (.aggregate 0 [.scalar ⟨2, 1⟩]) ∧
    (∃ m1, Interp.step (c7MkTransmuteMach u8MrTy nonZeroU8MrTy [.Init 2 none] 1) = .ok m1 ∧
      m1.mem.memory.allocations[0]?.map (·.data) = some [.Init 2 none]) ∧
    (∃ m1, Interp.stepTB (liftMachToTB (c7MkTransmuteMach u8MrTy nonZeroU8MrTy [.Init 2 none] 1)) = .ok m1 ∧ MachTB.wfLive m1 ∧
      m1.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) = some [.initNoProv 2]) ∧
    runAVal c7SubtypeU8ToNzMir 4 (initMachineState c7SubtypeU8ToNzMir [.scalar ⟨7, 1⟩]) = some (.aggregate 0 [.scalar ⟨7, 1⟩]) ∧
    (∃ m1, Interp.step (c7MkTransmuteMach u8MrTy nonZeroU8MrTy [.Init 7 none] 1) = .ok m1 ∧
      m1.mem.memory.allocations[0]?.map (·.data) = some [.Init 7 none]) ∧
    (∃ m1, Interp.stepTB (liftMachToTB (c7MkTransmuteMach u8MrTy nonZeroU8MrTy [.Init 7 none] 1)) = .ok m1 ∧ MachTB.wfLive m1 ∧
      m1.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) = some [.initNoProv 7]) ∧
    stepMirFn c7SubtypeU8ToNzMir (initMachineState c7SubtypeU8ToNzMir [.scalar ⟨0, 1⟩]) =
      MirStepNode.fail .ub ∧ Interp.step (c7MkTransmuteMach u8MrTy nonZeroU8MrTy [.Init 0 none] 1) =
      .error (.ub "transmuted value is not valid at new type") ∧
    Interp.stepTB (liftMachToTB (c7MkTransmuteMach u8MrTy nonZeroU8MrTy [.Init 0 none] 1)) =
      .error (.ub "transmuted value is not valid at new type") :=
  ⟨rfl, ok_of_map_toOption (by decide +kernel), ok_stepTB_wfLive (by decide +kernel),
   rfl, ok_of_map_toOption (by decide +kernel), ok_stepTB_wfLive (by decide +kernel),
   rfl, ok_of_map_toOption (by decide +kernel), ok_stepTB_wfLive (by decide +kernel),
   rfl, eq_error_ub_of_interpUbMsg (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel), rfl, ok_of_map_toOption (by decide +kernel),
   ok_stepTB_wfLive (by decide +kernel), rfl, ok_of_map_toOption (by decide +kernel),
   ok_stepTB_wfLive (by decide +kernel), rfl, eq_error_ub_of_interpUbMsg (by decide +kernel),
   eq_error_ub_of_interpUbMsg (by decide +kernel)⟩

/-! ## §8 (`C8`): Exhaustive 5 Non-`Unsize` `CastKind.pointerCoercion` Kinds -/
/-- **C8 Universal Fragment Boundary
(`translateRvalue_pointerCoercion_none`)**: `Translate.translateRvalue`
returns `none` for EVERY `CastKind.pointerCoercion`. -/
theorem translateRvalue_pointerCoercion_none (layouts : LayoutTable) (decls : List MirAst.LocalDecl) (targetTy : Option MirAst.Ty)
    (coercionKind : String) (op : MirAst.Operand) (dstTy : MirAst.Ty) :
    translateRvalue layouts decls targetTy (.cast (.pointerCoercion coercionKind) op dstTy) = none := rfl
/-- **C8.1 & C8.2 (`ReifyFnPointer` & `ClosureFnPointer`) Universal Two-Sided
Lockstep & Strict-Check UB Law (`Mach` & `MachTB`)**: Couples Trusted
`evalRvalue ... (.cast (.pointerCoercion ck) op targetTy)`
(`evalReifyFnPointer` + `internFnPtr` across ALL 6 reify/closure coercion
tags, for BOTH `fnDef` ZST values `.unit` AND 0-capture closure values
`.aggregate 0 []`!) directly with MiniRust `evalConstantM` / `evalValueM` on
`Constant.FnPointer fnNm` (`Mach` & `MachTB`), plus universal `.ub`
characterization for safety mismatches (`"ReifyFnPointer(Safe)"` →
`.unsafe_`), `.rustIntrinsic` ABI targets, and capturing closures. -/
theorem reify_and_closure_fnPointer_lockstep_M {M : Type} [Gen.Memory M] [MemoryOps M]
    (locals locals' : List LocalSlot) (op : MirAst.Operand)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (layouts : LayoutTable)
    (ck : String) (dp : DefPath) (targs : List RigidTy) (fnIns : List RigidTy) (fnOut : RigidTy) (fnSaf : Safety) (fnAbi : CallConv)
    (m : Machine M) (fnNm : Gen.FnName) (mrPtr : ThinPointer (Gen.Memory.Provenance M)) :
    let targetTy : MirAst.Ty := { kind := .fnPtr fnIns fnOut fnSaf fnAbi, layoutIdx := 0 }
    -- (1) Positive two-sided lockstep for BOTH `.unit` (fnDef) and
    -- `.aggregate 0 []` (0-capture closure)
    (∀ zstVal, (zstVal = .unit ∨ zstVal = .aggregate 0 []) → isReifyFnPointerCoercion ck = true →
      stringEq ck "UnsafeFnPointer" = false → evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals
        (callStack := mem.callStack) = .ok zstVal locals' → callConvEq fnAbi .rustIntrinsic = false →
      reifyCoercionSafetyCompatible ck fnSaf = true → extractReifyCoercionTarget? ck (operandTy decls layouts op) = some (dp, targs) →
      checkCalleeSig mem.callees dp fnIns fnOut fnAbi targs mem.traitImpls = true →
      mapIndex m.fn_ptrs fnNm "self.fn_ptrs[fn_name]" = .ok mrPtr →
      let (allocId, mem') := internFnPtr mem dp targs (some targetTy.kind)
      evalRvalue locals (.cast (.pointerCoercion ck) op targetTy) mem decls layouts =
        .ok (.ptr { allocId := allocId, offsetBytes := 0 } 8) locals' mem' ∧
      evalConstantM m (.FnPointer fnNm) = .ok (.Ptr (ThinPointer.widen mrPtr none)) ∧
      evalValueM m (.Constant (.FnPointer fnNm) thinRawPtrTy) = .ok ((.Ptr (ThinPointer.widen mrPtr none), thinRawPtrTy), m)) ∧
    -- (2) Safety mismatch UB (`ReifyFnPointer(Safe)` to `unsafe fn`)
    (evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals (callStack := mem.callStack) = .ok .unit locals' →
      evalRvalue locals (.cast (.pointerCoercion "ReifyFnPointer(Safe)") op fnPtrUnsafeU32MirTy) mem decls layouts = .ub) ∧
    -- (3) `.rustIntrinsic` ABI target UB
    (evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals (callStack := mem.callStack) = .ok .unit locals' →
      evalRvalue locals (.cast (.pointerCoercion "ReifyFnPointer") op fnPtrIntrinsicU32MirTy) mem decls layouts = .ub) ∧
    -- (4) Capturing closure UB (`ClosureFnPointer` on non-empty capture list)
    (∀ v0 vs, evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals
        (callStack := mem.callStack) = .ok (.aggregate 0 (v0 :: vs)) locals' →
      evalRvalue locals (.cast (.pointerCoercion "ClosureFnPointer") op targetTy) mem decls layouts = .ub) := by
  intro targetTy
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro zstVal hZst hReify hNotUnsafe hOp hAbi hSaf hExt hSig hLookup
    refine ⟨?_, ?_⟩
    · show evalReifyFnPointer locals op targetTy mem decls layouts ck = _
      unfold evalReifyFnPointer
      rcases hZst with rfl | rfl <;>
        simp only [hReify, hNotUnsafe, hOp, targetTy, hAbi, Bool.not_false, hSaf, Bool.and_self, hExt, hSig]
    · unfold evalValueM evalConstantM
      simp only [hLookup, bind, Except.bind, pure, Except.pure, and_self]
  · intro hOp
    show evalReifyFnPointer locals op fnPtrUnsafeU32MirTy mem decls layouts "ReifyFnPointer(Safe)" = .ub
    unfold evalReifyFnPointer
    simp only [show isReifyFnPointerCoercion "ReifyFnPointer(Safe)" = true from rfl,
      show stringEq "ReifyFnPointer(Safe)" "UnsafeFnPointer" = false from rfl, hOp,
      fnPtrUnsafeU32MirTy, show reifyCoercionSafetyCompatible "ReifyFnPointer(Safe)" .unsafe_ = false from rfl, Bool.and_false]
  · intro hOp
    show evalReifyFnPointer locals op fnPtrIntrinsicU32MirTy mem decls layouts "ReifyFnPointer" = .ub
    unfold evalReifyFnPointer
    simp only [show isReifyFnPointerCoercion "ReifyFnPointer" = true from rfl,
      show stringEq "ReifyFnPointer" "UnsafeFnPointer" = false from rfl, hOp,
      fnPtrIntrinsicU32MirTy, show callConvEq .rustIntrinsic .rustIntrinsic = true from rfl, Bool.not_true, Bool.false_and]
  · intro v0 vs hOp
    show evalReifyFnPointer locals op targetTy mem decls layouts "ClosureFnPointer" = .ub
    unfold evalReifyFnPointer
    simp only [show isReifyFnPointerCoercion "ClosureFnPointer" = true from rfl,
      show stringEq "ClosureFnPointer" "UnsafeFnPointer" = false from rfl, hOp]
/-- **C8.3 (`UnsafeFnPointer`) Coupled Positive Lockstep & Strict-Check
Divergences (`Mach` & `MachTB`)**: (1) Coupled via `FnPtrEntryRel` across both
empty and populated `mem.fnPtrs`, safe-to-unsafe coercion returns `.ok (.ptr p
8)` in lockstep with MiniRust `evalConstantM` and `Transmute thinRawPtrTy` on
`Mach` & `MachTB`; (2) Trusted faults with `.ub` on `.safe` targets,
already-`.unsafe_` sources, and `.rustIntrinsic` targets while MiniRust
type-erased `Transmute` succeeds; (3) unknown tags return `.unsupported`. -/
theorem unsafeFnPointer_ground_truth_and_divergences (locals locals' : List LocalSlot) (op : MirAst.Operand)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (layouts : LayoutTable)
    (p : ProvenancePtr) (fnNm : Gen.FnName) (addr : Nat)
    (provBM : Option Prov) (provTB : Option TreeBorrowsProvenance) (mBM : Mach) (mTB : MachTB)
    (hRelBM : FnPtrEntryRel mem p mBM fnNm addr provBM) (hRelTB : FnPtrEntryRel mem p mTB fnNm addr provTB)
    (hOp : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals decls mem.callStack = .ok (.ptr p 8) locals') :
    isReifyFnPointerCoercion "UnsafeFnPointer" = true ∧
    evalRvalue locals (.cast (.pointerCoercion "UnsafeFnPointer") op fnPtrUnsafeU32MirTy)
      mem decls layouts = evalUnsafeFnPointer locals op fnPtrUnsafeU32MirTy mem decls layouts ∧
    -- Positive safe -> unsafe lockstep (both empty AND populated mem.fnPtrs!)
    (operandTy decls layouts op = some fnPtrSafeU32MirTy → (match mem.fnPtrs with
       | [] => isFnPtrAllocId p.allocId
       | _ :: _ =>
         match lookupFnPtr mem.fnPtrs p.allocId with
         | none => false
         | some e =>
           match e.fnSig with
           | none => true
           | some (.fnPtr ins out .safe abi) =>
             callConvEq abi .rust && rigidTyListEq ins [.uint .u32] && rigidTyEq out (.uint .u32)
           | some _ => false) = true →
      evalRvalue locals (.cast (.pointerCoercion "UnsafeFnPointer") op fnPtrUnsafeU32MirTy)
        mem decls layouts = .ok (.ptr p 8) locals' mem) ∧
    -- Strict-check UB (safe target, already-unsafe source, intrinsic target)
    evalRvalue locals (.cast (.pointerCoercion "UnsafeFnPointer") op fnPtrSafeU32MirTy)
      mem decls layouts = .ub ∧ (operandTy decls layouts op = some fnPtrUnsafeU32MirTy →
      evalRvalue locals (.cast (.pointerCoercion "UnsafeFnPointer") op fnPtrUnsafeU32MirTy)
        mem decls layouts = .ub) ∧ evalRvalue locals (.cast (.pointerCoercion "UnsafeFnPointer") op
        { kind := .fnPtr [.uint .u32] (.uint .u32) .unsafe_ .rustIntrinsic, layoutIdx := 0 })
      mem decls layouts = .ub ∧
    -- MiniRust fn_ptrs lookup & type-erased Transmute succeed on Mach & MachTB
    evalConstantM mBM (.FnPointer fnNm) = .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none)) ∧
    evalConstantM mTB (.FnPointer fnNm) = .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none)) ∧
    evalCastOp (.Transmute thinRawPtrTy) (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy)
      (some mBM) = .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy) ∧
    evalCastOpM (M := TBM) (.Transmute thinRawPtrTy)
      (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy)
      (some mTB) = .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy) ∧
    evalRvalue locals (.cast (.pointerCoercion "UnsafeFnPointer(Unsafe)") op fnPtrUnsafeU32MirTy)
      mem decls layouts = .unsupported := by
  rcases hRelBM with ⟨hOff, hNoB, hAddr, hMapBM⟩
  rcases hRelTB with ⟨_, _, _, hMapTB⟩
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_,
    by unfold evalConstantM; simp only [hMapBM, bind, Except.bind, pure, Except.pure],
    by unfold evalConstantM; simp only [hMapTB, bind, Except.bind, pure, Except.pure],
    evalCastOp_transmute_thinRawPtr_id addr hAddr provBM (some mBM),
    evalCastOpM_transmute_thinRawPtr_id (M := TBM) addr hAddr provTB (some mTB), rfl⟩
  · intro hSrc hFnAlloc
    show evalUnsafeFnPointer locals op fnPtrUnsafeU32MirTy mem decls layouts = _
    unfold evalUnsafeFnPointer
    simp only [hOp, hSrc, hOff, hNoB, fnPtrUnsafeU32MirTy, fnPtrSafeU32MirTy, callConvEq, rigidTyListEq, rigidTyEq, Nat.beq_refl]
    have hB : ∀ b : Bool, b = true → (match Bool.and true (Bool.and true (Bool.and true b)) with
         | true => RvalueEvalResult.ok (.ptr p 8) locals' mem
         | false => .ub) = .ok (.ptr p 8) locals' mem := by
      intro b hb; subst hb; rfl
    apply hB
    cases hF : mem.fnPtrs with
    | nil => simpa [hF] using hFnAlloc
    | cons fh ft =>
      rw [hF] at hFnAlloc; dsimp only [] at hFnAlloc ⊢; cases hL : lookupFnPtr (fh :: ft) p.allocId with
      | none => simp [hL] at hFnAlloc
      | some e =>
        rw [hL] at hFnAlloc; dsimp only [] at hFnAlloc ⊢; cases hS : e.fnSig with
        | none => simp [hS]
        | some rty =>
          rw [hS] at hFnAlloc; cases rty with
          | fnPtr ins out saf abi =>
            cases saf with
            | safe =>
              simpa [hS, callConvEq, rigidTyListEq, rigidTyEq, Bool.and_assoc] using hFnAlloc
            | unsafe_ => simp at hFnAlloc
          | _ => simp at hFnAlloc
  · show evalUnsafeFnPointer locals op fnPtrSafeU32MirTy mem decls layouts = .ub
    unfold evalUnsafeFnPointer; simp [hOp, fnPtrSafeU32MirTy]
  · intro hAlreadyUnsafe
    show evalUnsafeFnPointer locals op fnPtrUnsafeU32MirTy mem decls layouts = .ub
    unfold evalUnsafeFnPointer; simp [hOp, hAlreadyUnsafe, fnPtrUnsafeU32MirTy, callConvEq]
  · show evalUnsafeFnPointer locals op
      { kind := .fnPtr [.uint .u32] (.uint .u32) .unsafe_ .rustIntrinsic, layoutIdx := 0 }
      mem decls layouts = .ub
    unfold evalUnsafeFnPointer; simp [hOp, callConvEq]
/-- **C8 + C6 Universal Composed Function-Pointer Pipeline (`ReifyFnPointer` /
`ClosureFnPointer` → `UnsafeFnPointer` → `FnPtrToPtr`)**: When a fresh
`internFnPtr` allocates `(aid, mem')` for a `.safe` `fn(u32) -> u32`, `mem'`
satisfies `FnPtrEntryRel` and chains directly through `UnsafeFnPointer` and
`FnPtrToPtr` in lockstep with MiniRust `Constant.FnPointer` → `Transmute` on
BOTH `Mach` and `MachTB`. -/
theorem reify_unsafe_fnPtrToPtr_pipeline (locals locals1 locals2 locals3 : List LocalSlot) (opReify opUnsafe opRaw : MirAst.Operand)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (layouts : LayoutTable)
    (ck : String) (dp : DefPath) (targs : List RigidTy) (zstVal : MirSemantics.Value)
    (fnNm : Gen.FnName) (addr : Nat) (hAddr : addr < 2 ^ 64)
    (provBM : Option Prov) (provTB : Option TreeBorrowsProvenance) (mBM : Mach) (mTB : MachTB)
    (hZst : zstVal = .unit ∨ zstVal = .aggregate 0 [])
    (hReify : isReifyFnPointerCoercion ck = true) (hNotUnsafe : stringEq ck "UnsafeFnPointer" = false)
    (hSaf : reifyCoercionSafetyCompatible ck .safe = true)
    (hExt : extractReifyCoercionTarget? ck (operandTy decls layouts opReify) = some (dp, targs))
    (hSig : checkCalleeSig mem.callees dp [.uint .u32] (.uint .u32) .rust targs mem.traitImpls = true)
    (hFresh : findFnPtrEntry? mem.fnPtrs dp targs (some fnPtrSafeU32MirTy.kind) = none)
    (hNoB : lookupBorrow mem.borrows (nextFnPtrAllocId mem.fnPtrs) = none)
    (hMapBM : mapIndex mBM.fn_ptrs fnNm "self.fn_ptrs[fn_name]" = .ok { addr := addr, provenance := provBM })
    (hMapTB : mapIndex mTB.fn_ptrs fnNm "self.fn_ptrs[fn_name]" = .ok { addr := addr, provenance := provTB })
    (hOp1 : evalOperand locals opReify mem.borrows mem.globals layouts mem.callerLocals
      (callStack := mem.callStack) = .ok zstVal locals1) :
    let (aid, mem') := internFnPtr mem dp targs (some fnPtrSafeU32MirTy.kind)
    let p : ProvenancePtr := { allocId := aid, offsetBytes := 0 }
    evalRvalue locals (.cast (.pointerCoercion ck) opReify fnPtrSafeU32MirTy) mem decls layouts = .ok (.ptr p 8) locals1 mem' ∧
    FnPtrEntryRel mem' p mBM fnNm addr provBM ∧ FnPtrEntryRel mem' p mTB fnNm addr provTB ∧
    (evalOperand locals1 opUnsafe mem'.borrows mem'.globals layouts mem'.callerLocals decls mem'.callStack = .ok (.ptr p 8) locals2 →
      operandTy decls layouts opUnsafe = some fnPtrSafeU32MirTy →
      evalRvalue locals1 (.cast (.pointerCoercion "UnsafeFnPointer") opUnsafe fnPtrUnsafeU32MirTy)
        mem' decls layouts = .ok (.ptr p 8) locals2 mem') ∧
    (evalOperand locals2 opRaw mem'.borrows mem'.globals layouts mem'.callerLocals decls mem'.callStack = .ok (.ptr p 8) locals3 →
      operandTy decls layouts opRaw = some fnPtrUnsafeU32MirTy →
      evalRvalue locals2 (.cast .fnPtrToPtr opRaw rawConstUnitMirTy) mem' decls layouts = .ok (.ptr p 8) locals3 mem') ∧
    evalConstantM mBM (.FnPointer fnNm) = .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none)) ∧
    evalConstantM mTB (.FnPointer fnNm) = .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none)) ∧
    evalCastOp (.Transmute thinRawPtrTy)
      (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy) (some mBM) =
      .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy) ∧
    evalCastOpM (M := TBM) (.Transmute thinRawPtrTy)
      (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy) (some mTB) =
      .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy) := by
  have hStep1 := (reify_and_closure_fnPointer_lockstep_M (M := BM) locals locals1 opReify mem decls
    layouts ck dp targs [.uint .u32] (.uint .u32) .safe .rust mBM fnNm
    { addr := addr, provenance := provBM }).1 zstVal hZst hReify hNotUnsafe hOp1 rfl hSaf hExt hSig hMapBM
  have hInt : internFnPtr mem dp targs (some fnPtrSafeU32MirTy.kind) =
      (nextFnPtrAllocId mem.fnPtrs, { mem with fnPtrs :=
        { allocId := nextFnPtrAllocId mem.fnPtrs, defPath := dp, typeArgs := targs,
          fnSig := some fnPtrSafeU32MirTy.kind } :: mem.fnPtrs }) := by
    unfold internFnPtr; simp [hFresh]
  rw [hInt]; dsimp only []
  let aid := nextFnPtrAllocId mem.fnPtrs
  let mem' : MirSemantics.Memory := { mem with fnPtrs :=
    { allocId := aid, defPath := dp, typeArgs := targs, fnSig := some fnPtrSafeU32MirTy.kind } :: mem.fnPtrs }
  let p : ProvenancePtr := { allocId := aid, offsetBytes := 0 }
  have hRelBM : FnPtrEntryRel mem' p mBM fnNm addr provBM := ⟨rfl, hNoB, hAddr, hMapBM⟩
  have hRelTB : FnPtrEntryRel mem' p mTB fnNm addr provTB := ⟨rfl, hNoB, hAddr, hMapTB⟩
  refine ⟨by rw [hInt] at hStep1; exact hStep1.1, hRelBM, hRelTB, ?_, ?_, hStep1.2.1,
    by unfold evalConstantM; simp only [hMapTB, bind, Except.bind, pure, Except.pure],
    evalCastOp_transmute_thinRawPtr_id addr hAddr provBM (some mBM),
    evalCastOpM_transmute_thinRawPtr_id (M := TBM) addr hAddr provTB (some mTB)⟩
  · intro hOp2 hTy2
    have hU := unsafeFnPointer_ground_truth_and_divergences locals1 locals2 opUnsafe mem' decls
      layouts p fnNm addr provBM provTB mBM mTB hRelBM hRelTB hOp2
    exact hU.2.2.1 hTy2 (by simp [mem', p, lookupFnPtr, Nat.beq_refl, fnPtrSafeU32MirTy, callConvEq, rigidTyListEq, rigidTyEq])
  · intro hOp3 hTy3
    have hF := fnPtrToPtr_lockstep_mach_and_tb locals2 locals3 opRaw rawConstUnitMirTy mem' decls
      layouts p fnNm addr provBM provTB mBM mTB hRelBM hRelTB hOp3 rfl
      (by simp [hTy3, fnPtrUnsafeU32MirTy, callConvEq])
      (by simp [mem', p, lookupFnPtr, Nat.beq_refl, fnPtrSafeU32MirTy, callConvEq])
    exact hF.1
/-- **C8.3 (`UnsafeFnPointer`) Exhaustive Signature-Mismatch, Nonzero-Offset,
Stack-Borrow, & Scalar-Operand UB Laws (`unsafeFnPointer_ptr_and_sig_ub`)**:
Without assuming `FnPtrEntryRel`, characterizes the remaining
`evalUnsafeFnPointer` fault arms (`Places.lean:13522-13556`): arity/signature
mismatch, nonzero `offsetBytes`, stack-backed `lookupBorrow = some _`, and
`.scalar` operands. -/
theorem unsafeFnPointer_ptr_and_sig_ub (locals locals' : List LocalSlot) (op : MirAst.Operand)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (layouts : LayoutTable) (p : ProvenancePtr) :
    (evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals decls
        mem.callStack = .ok (.ptr p 8) locals' → (operandTy decls layouts op =
          some { kind := .fnPtr [] (.uint .u32) .safe .rust, layoutIdx := 0 } →
        evalRvalue locals (.cast (.pointerCoercion "UnsafeFnPointer") op fnPtrUnsafeU32MirTy)
          mem decls layouts = .ub) ∧ (p.offsetBytes ≠ 0 →
        evalRvalue locals (.cast (.pointerCoercion "UnsafeFnPointer") op fnPtrUnsafeU32MirTy)
          mem decls layouts = .ub) ∧ (∀ entry, lookupBorrow mem.borrows p.tag = some entry →
        evalRvalue locals (.cast (.pointerCoercion "UnsafeFnPointer") op fnPtrUnsafeU32MirTy) mem decls layouts = .ub)) ∧
    (∀ sc, evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals decls mem.callStack = .ok (.scalar sc) locals' →
      evalRvalue locals (.cast (.pointerCoercion "UnsafeFnPointer") op fnPtrUnsafeU32MirTy) mem decls layouts = .ub) := by
  refine ⟨fun hOp => ⟨?_, ?_, ?_⟩, fun sc hSc => ?_⟩
  · intro hBadSig
    show evalUnsafeFnPointer locals op fnPtrUnsafeU32MirTy mem decls layouts = .ub
    unfold evalUnsafeFnPointer; simp [hOp, hBadSig, fnPtrUnsafeU32MirTy, callConvEq, rigidTyListEq]
  · intro hNe
    have hBeq : Nat.beq p.offsetBytes 0 = false := by
      cases ho : p.offsetBytes with | zero => exact absurd ho hNe | succ _ => rfl
    show evalUnsafeFnPointer locals op fnPtrUnsafeU32MirTy mem decls layouts = .ub
    unfold evalUnsafeFnPointer; simp [hOp, hBeq, fnPtrUnsafeU32MirTy, callConvEq, Bool.and_false]
  · intro entry hB
    show evalUnsafeFnPointer locals op fnPtrUnsafeU32MirTy mem decls layouts = .ub
    unfold evalUnsafeFnPointer; simp [hOp, hB, fnPtrUnsafeU32MirTy, callConvEq, Bool.and_false]
  · show evalUnsafeFnPointer locals op fnPtrUnsafeU32MirTy mem decls layouts = .ub
    unfold evalUnsafeFnPointer; simp [hSc]
private theorem mutToConst_dispatch_flags :
    isReifyFnPointerCoercion "MutToConstPointer" = false ∧ stringEq "MutToConstPointer" "Unsize" = false ∧
    stringEq "MutToConstPointer" "ArrayToPointer" = false ∧
    stringEq "MutToConstPointer" "MutToConstPointer" = true := ⟨rfl, rfl, rfl, rfl⟩
private theorem arrayToPtr_dispatch_flags :
    isReifyFnPointerCoercion "ArrayToPointer" = false ∧ stringEq "ArrayToPointer" "Unsize" = false ∧
    stringEq "ArrayToPointer" "ArrayToPointer" = true := ⟨rfl, rfl, rfl⟩
/-- **C8.4 (`MutToConstPointer`) Coupled Two-Sided Exhaustive Shape
Preservation (`Mach` & `MachTB`) & Bidirectional Shape-Mismatch UB**: Couples
Trusted `evalRvalue` on `.pointerCoercion "MutToConstPointer"` across ALL 6
runtime value shapes (thin `.ptr`, thin `.scalar`, wide slice `.ptr`,
provenance-free wide slice, wide dyn `.ptr`+`.ptr`, AND mixed scalar-addr +
`.ptr`-vtable wide dyn) with MiniRust `evalCastOpM (.Transmute ...)` on
`Mach` & `MachTB`, plus thin-to-wide AND wide-to-thin shape-mismatch UB. -/
theorem mutToConstPointer_all_shapes_and_ub (locals locals' : List LocalSlot) (op : MirAst.Operand)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl)
    (p vt : ProvenancePtr) (addr len : Nat) (hAddr : addr < 2 ^ 64) (hLen : len < 2 ^ 64)
    (provBM : Option Prov) (provTB : Option TreeBorrowsProvenance) (mBM : Option Mach) (mTB : Option MachTB) :
    (evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls
        mem.callStack = .ok (.ptr p 8) locals' → operandTy decls emptyLayoutTable op = some rawMutU32MirTy →
      evalRvalue locals (.cast (.pointerCoercion "MutToConstPointer") op rawConstU32MirTy)
        mem decls emptyLayoutTable = .ok (.ptr p 8) locals' mem ∧ evalCastOp (.Transmute thinRawPtrTy)
        (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy) mBM =
        .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy) ∧
      evalCastOpM (M := TBM) (.Transmute thinRawPtrTy)
        (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy) mTB =
        .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy)) ∧
    (evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls
        mem.callStack = .ok (.scalar ⟨addr, 8⟩) locals' →
      operandTy decls emptyLayoutTable op = some rawMutU32MirTy →
      evalRvalue locals (.cast (.pointerCoercion "MutToConstPointer") op rawConstU32MirTy)
        mem decls emptyLayoutTable = .ok (.scalar ⟨wrapScalarBits addr (scalarModulus 8), 8⟩) locals' mem) ∧
    (evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls
        mem.callStack = .ok (annealWidePtrVal p len 8) locals' →
      operandTy decls emptyLayoutTable op = some rawMutSliceU32MirTy →
      evalRvalue locals (.cast (.pointerCoercion "MutToConstPointer") op rawConstSliceU32MirTy)
        mem decls emptyLayoutTable = .ok (annealWidePtrVal p len 8) locals' mem ∧
      evalCastOpM (M := BM) (.Transmute wideSlicePtrMrTy)
        (mrWidePtrValM { addr := addr, provenance := provBM } (len : Int), wideSlicePtrMrTy) mBM =
        .ok (mrWidePtrValM { addr := addr, provenance := provBM } (len : Int), wideSlicePtrMrTy) ∧
      evalCastOpM (M := TBM) (.Transmute wideSlicePtrMrTy)
        (mrWidePtrValM { addr := addr, provenance := provTB } (len : Int), wideSlicePtrMrTy) mTB =
        .ok (mrWidePtrValM { addr := addr, provenance := provTB } (len : Int), wideSlicePtrMrTy)) ∧
    (evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls
        mem.callStack = .ok (.aggregate 0 [.scalar ⟨addr, 8⟩, .scalar ⟨len, 8⟩]) locals' →
      operandTy decls emptyLayoutTable op = some rawMutSliceU32MirTy →
      evalRvalue locals (.cast (.pointerCoercion "MutToConstPointer") op rawConstSliceU32MirTy)
        mem decls emptyLayoutTable = .ok (.aggregate 0 [.scalar ⟨wrapScalarBits addr (scalarModulus 8), 8⟩,
                           .scalar ⟨wrapScalarBits len (scalarModulus 8), 8⟩]) locals' mem) ∧
    (evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls
        mem.callStack = .ok (.aggregate 0 [.ptr p 8, .ptr vt 8]) locals' →
      operandTy decls emptyLayoutTable op = some rawMutDynMirTy →
      evalRvalue locals (.cast (.pointerCoercion "MutToConstPointer") op rawConstDynMirTy)
        mem decls emptyLayoutTable = .ok (.aggregate 0 [.ptr p 8, .ptr vt 8]) locals' mem) ∧
    (evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls
        mem.callStack = .ok (.aggregate 0 [.scalar ⟨addr, 8⟩, .ptr vt 8]) locals' →
      operandTy decls emptyLayoutTable op = some rawMutDynMirTy →
      evalRvalue locals (.cast (.pointerCoercion "MutToConstPointer") op rawConstDynMirTy) mem decls emptyLayoutTable =
        .ok (.aggregate 0 [.scalar ⟨wrapScalarBits addr (scalarModulus 8), 8⟩, .ptr vt 8]) locals' mem) ∧
    (evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls mem.callStack = .ok (.ptr p 8) locals' →
      evalRvalue locals (.cast (.pointerCoercion "MutToConstPointer") op rawConstSliceU32MirTy) mem decls emptyLayoutTable = .ub ∧
      evalCastOpM (M := BM) (.Transmute wideSlicePtrMrTy)
        (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy) mBM =
        .error (.ub "transmute between types of different size") ∧
      evalCastOpM (M := TBM) (.Transmute wideSlicePtrMrTy)
        (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy) mTB =
        .error (.ub "transmute between types of different size")) ∧
    (evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls
        mem.callStack = .ok (annealWidePtrVal p len 8) locals' →
      evalRvalue locals (.cast (.pointerCoercion "MutToConstPointer") op rawConstU32MirTy) mem decls emptyLayoutTable = .ub ∧
      evalCastOpM (M := BM) (.Transmute thinRawPtrTy)
        (mrWidePtrValM { addr := addr, provenance := provBM } (len : Int), wideSlicePtrMrTy) mBM =
        .error (.ub "transmute between types of different size") ∧
      evalCastOpM (M := TBM) (.Transmute thinRawPtrTy)
        (mrWidePtrValM { addr := addr, provenance := provTB } (len : Int), wideSlicePtrMrTy) mTB =
        .error (.ub "transmute between types of different size")) ∧
    (PtrType.as_wide_pair (.Raw (.VTablePointer (traitNameOf 0))) =
      some (.Tuple [(⟨0⟩, thinRawPtrTy), (x86_64.PTR_SIZE, .Ptr (.VTablePtr (traitNameOf 0)))]
        ⟨⟨16⟩, ⟨8⟩, none⟩ none) ∧ ∀ (vtThin : ThinPointer TreeBorrowsProvenance),
      checkPtrMetadataM (some (.VTablePointer vtThin)) (.VTablePointer (traitNameOf 0)) = .error (.unsupported
          "check_ptr_metadata for vtable pointer metadata (Machine::vtable_from_ptr)")) := by
  obtain ⟨h1, h2, h3, h4⟩ := mutToConst_dispatch_flags
  have hL8 : layoutPointerBytes emptyLayoutTable = 8 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨rfl, fun _ => rfl⟩⟩
  · intro hOp hTy
    have hSh : mutToConstTargetShape? (some rawMutU32MirTy) rawConstU32MirTy = some none := rfl
    refine ⟨?_, evalCastOp_transmute_thinRawPtr_id addr hAddr provBM mBM,
      evalCastOpM_transmute_thinRawPtr_id (M := TBM) addr hAddr provTB mTB⟩
    show evalReifyFnPointer locals op rawConstU32MirTy mem decls emptyLayoutTable "MutToConstPointer" = _
    unfold evalReifyFnPointer; simp only [h1, h2, h3, h4, hL8, hOp, hTy, hSh, Nat.beq_refl]
  · intro hOp hTy
    have hSh : mutToConstTargetShape? (some rawMutU32MirTy) rawConstU32MirTy = some none := rfl
    show evalReifyFnPointer locals op rawConstU32MirTy mem decls emptyLayoutTable "MutToConstPointer" = _
    unfold evalReifyFnPointer; simp only [h1, h2, h3, h4, hL8, hOp, hTy, hSh, Nat.beq_refl]
  · intro hOp hTy
    have hSh : mutToConstTargetShape? (some rawMutSliceU32MirTy) rawConstSliceU32MirTy = some (some false) := rfl
    refine ⟨?_, evalCastOpM_transmute_wideSliceRawPtr_id (M := BM) addr len hAddr hLen provBM mBM,
      evalCastOpM_transmute_wideSliceRawPtr_id (M := TBM) addr len hAddr hLen provTB mTB⟩
    show evalReifyFnPointer locals op rawConstSliceU32MirTy mem decls emptyLayoutTable "MutToConstPointer" = _
    unfold evalReifyFnPointer; simp only [h1, h2, h3, h4, hL8, hOp, hTy, hSh, annealWidePtrVal, Nat.beq_refl, Bool.and_self]
  · intro hOp hTy
    have hSh : mutToConstTargetShape? (some rawMutSliceU32MirTy) rawConstSliceU32MirTy = some (some false) := rfl
    show evalReifyFnPointer locals op rawConstSliceU32MirTy mem decls emptyLayoutTable "MutToConstPointer" = _
    unfold evalReifyFnPointer; simp only [h1, h2, h3, h4, hL8, hOp, hTy, hSh, Nat.beq_refl, Bool.and_self]
  · intro hOp hTy
    have hSh : mutToConstTargetShape? (some rawMutDynMirTy) rawConstDynMirTy = some (some true) := rfl
    show evalReifyFnPointer locals op rawConstDynMirTy mem decls emptyLayoutTable "MutToConstPointer" = _
    unfold evalReifyFnPointer; simp only [h1, h2, h3, h4, hL8, hOp, hTy, hSh, Nat.beq_refl, Bool.and_self]
  · intro hOp hTy
    have hSh : mutToConstTargetShape? (some rawMutDynMirTy) rawConstDynMirTy = some (some true) := rfl
    show evalReifyFnPointer locals op rawConstDynMirTy mem decls emptyLayoutTable "MutToConstPointer" = _
    unfold evalReifyFnPointer; simp only [h1, h2, h3, h4, hL8, hOp, hTy, hSh, Nat.beq_refl, Bool.and_self]
  · intro hOp
    refine ⟨?_, rfl, rfl⟩
    have hShape : ∀ s, mutToConstTargetShape? s rawConstSliceU32MirTy ≠ some none := by
      intro s; cases s with
      | none => decide
      | some ty => cases ty with
        | mk kind _ =>
          cases kind <;> simp [mutToConstTargetShape?, rawConstSliceU32MirTy, isWideRawPtrTy]
          all_goals split <;> simp
    show evalReifyFnPointer locals op rawConstSliceU32MirTy mem decls emptyLayoutTable "MutToConstPointer" = .ub
    unfold evalReifyFnPointer; simp only [h1, h2, h3, h4, hL8, hOp]
    cases hS : mutToConstTargetShape? (operandTy decls emptyLayoutTable op) rawConstSliceU32MirTy with
    | none => rfl
    | some o => cases o with | none => exact absurd hS (hShape _) | some _ => rfl
  · intro hOp
    refine ⟨?_, rfl, rfl⟩
    have hShape : ∀ s b, mutToConstTargetShape? s rawConstU32MirTy ≠ some (some b) := by
      intro s b; cases s with
      | none => intro h; cases h
      | some ty => cases ty with
        | mk kind _ =>
          cases kind <;> simp [mutToConstTargetShape?, rawConstU32MirTy, isWideRawPtrTy]
          all_goals split <;> simp
    show evalReifyFnPointer locals op rawConstU32MirTy mem decls emptyLayoutTable "MutToConstPointer" = .ub
    unfold evalReifyFnPointer; simp only [h1, h2, h3, h4, hL8, hOp, annealWidePtrVal, Nat.beq_refl, Bool.and_self]
    cases hS : mutToConstTargetShape? (operandTy decls emptyLayoutTable op) rawConstU32MirTy with
    | none => rfl
    | some o => cases o with | none => rfl | some b => exact absurd hS (hShape _ b)
private theorem exactByteDivAux_ge_acc : ∀ fuel rem stride acc k, exactByteDivAux fuel rem stride acc = some k → acc ≤ k
  | 0, rem, _, acc, k, h => by
    cases rem with
    | zero => cases Option.some.inj h; exact Nat.le_refl _
    | succ _ => cases h
  | fuel + 1, rem, stride, acc, k, h => by
    cases rem with
    | zero => cases Option.some.inj h; exact Nat.le_refl _
    | succ r =>
      unfold exactByteDivAux at h
      cases hb : Nat.ble stride (r + 1) with
      | false => simp [hb] at h
      | true =>
        simp only [hb] at h
        exact Nat.le_trans (Nat.le_succ acc) (exactByteDivAux_ge_acc fuel _ stride (acc + 1) k h)
private theorem byteOffsetToElemIdx?_pos_of_ne_zero (off elemSz k : Nat)
    (hne : off ≠ 0) (h : byteOffsetToElemIdx? off elemSz = some k) : 1 ≤ k := by
  cases off with
  | zero => exact absurd rfl hne
  | succ n =>
    unfold byteOffsetToElemIdx? at h
    cases he : Nat.beq elemSz 0 with
    | true => simp [he, Nat.beq] at h
    | false =>
      simp only [he, Nat.beq] at h; unfold exactByteDivAux at h
      cases hb : Nat.ble elemSz (n + 1) with
      | false => simp [hb] at h
      | true => simp only [hb] at h; exact exactByteDivAux_ge_acc n _ elemSz 1 k h
/-- **C8.5 (`ArrayToPointer`) Coupled Two-Sided Preservation (Global,
Stack-Borrow `deriveStackElemThinPtr` Fresh-Tag Minting + `alreadySubslice`
Identity + `.disabled` / Universal Nonzero-Offset UB, Scalar) & Const-to-Mut
UB**: Couples Trusted `ArrayToPointer` with MiniRust `Transmute thinRawPtrTy`
on `Mach` & `MachTB`, proving: (1) global/raw pointer lockstep; (2) stack-borrow
`deriveStackElemThinPtr` minting a fresh `[.subslice 0 2 false]` tag at offset
`0`, preserving already-subslice tags, and faulting on `.disabled` OR ANY
nonzero `p.offsetBytes ≠ 0`; (3) scalar address wrap; (4) const-to-mut UB. -/
theorem arrayToPointer_global_stack_scalar_and_ub (locals locals' : List LocalSlot) (op : MirAst.Operand)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (p : ProvenancePtr) (addr : Nat) (hAddr : addr < 2 ^ 64)
    (provBM : Option Prov) (provTB : Option TreeBorrowsProvenance) (mBM : Option Mach) (mTB : Option MachTB) :
    (evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls mem.callStack = .ok (.ptr p 8) locals' →
      operandTy decls emptyLayoutTable op = some rawMutArr2U32MirTy → lookupBorrow mem.borrows p.tag = none →
      evalRvalue locals (.cast (.pointerCoercion "ArrayToPointer") op rawMutU32MirTy)
        mem decls emptyLayoutTable = .ok (.ptr p 8) locals' mem ∧ evalCastOp (.Transmute thinRawPtrTy)
        (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy) mBM =
        .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provBM } none), thinRawPtrTy) ∧
      evalCastOpM (M := TBM) (.Transmute thinRawPtrTy)
        (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy) mTB =
        .ok (.Ptr (ThinPointer.widen { addr := addr, provenance := provTB } none), thinRawPtrTy)) ∧
    (∀ parentEntry, evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls
        mem.callStack = .ok (.ptr p 8) locals' →
      operandTy decls emptyLayoutTable op = some rawMutArr2U32MirTy → lookupBorrow mem.borrows p.tag = some parentEntry →
      evalRvalue locals (.cast (.pointerCoercion "ArrayToPointer") op rawMutU32MirTy)
        mem decls emptyLayoutTable = deriveStackElemThinPtr locals' mem p parentEntry (some 2) 8 ∧
      (parentEntry.perm = .disabled → deriveStackElemThinPtr locals' mem p parentEntry (some 2) 8 = .ub) ∧
      (∀ v0 v1, parentEntry.perm ≠ .disabled → parentEntry.targetFrameDepth = length mem.callStack →
        get? locals' parentEntry.targetLocal = some (.init (.aggregate 0 [.scalar ⟨v0, 4⟩, .scalar ⟨v1, 4⟩])) →
        (parentEntry.targetProjection = [] → p.offsetBytes = 0 →
          let subEntry : BorrowEntry :=
            { tag := mem.nextTag, targetLocal := parentEntry.targetLocal,
              targetFrameDepth := parentEntry.targetFrameDepth, allocDead := parentEntry.allocDead,
              targetProjection := [.subslice 0 2 false], perm := parentEntry.perm }
          deriveStackElemThinPtr locals' mem p parentEntry (some 2) 8 =
            .ok (.ptr { allocId := mem.nextTag, offsetBytes := 0 } 8) locals'
              { mem with borrows := subEntry :: mem.borrows, nextTag := mem.nextTag + 1 }) ∧
        (parentEntry.targetProjection = [.subslice 0 2 false] → p.offsetBytes = 0 →
          deriveStackElemThinPtr locals' mem p parentEntry (some 2) 8 = .ok (.ptr p 8) locals' mem) ∧
        (parentEntry.targetProjection = [] → p.offsetBytes ≠ 0 →
          deriveStackElemThinPtr locals' mem p parentEntry (some 2) 8 = .ub))) ∧
    (evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls
        mem.callStack = .ok (.scalar ⟨addr, 8⟩) locals' →
      operandTy decls emptyLayoutTable op = some rawMutArr2U32MirTy →
      evalRvalue locals (.cast (.pointerCoercion "ArrayToPointer") op rawMutU32MirTy)
        mem decls emptyLayoutTable = .ok (.scalar ⟨wrapScalarBits addr (scalarModulus 8), 8⟩) locals' mem) ∧
    (evalOperand locals op mem.borrows mem.globals emptyLayoutTable mem.callerLocals decls mem.callStack = .ok (.ptr p 8) locals' →
      operandTy decls emptyLayoutTable op = some rawConstArr2U32MirTy →
      evalRvalue locals (.cast (.pointerCoercion "ArrayToPointer") op rawMutU32MirTy) mem decls emptyLayoutTable = .ub) := by
  obtain ⟨h1, h2, h3⟩ := arrayToPtr_dispatch_flags
  have hL8 : layoutPointerBytes emptyLayoutTable = 8 := rfl
  have hArrOk : arrayToPointerElemLen? (some rawMutArr2U32MirTy) rawMutU32MirTy = some (some 2) := rfl
  have hArrBad : arrayToPointerElemLen? (some rawConstArr2U32MirTy) rawMutU32MirTy = none := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hOp hTy hNoB
    refine ⟨?_, evalCastOp_transmute_thinRawPtr_id addr hAddr provBM mBM,
      evalCastOpM_transmute_thinRawPtr_id (M := TBM) addr hAddr provTB mTB⟩
    show evalReifyFnPointer locals op rawMutU32MirTy mem decls emptyLayoutTable "ArrayToPointer" = _
    unfold evalReifyFnPointer; simp only [h1, h2, h3, hL8, hOp, hTy, hArrOk, hNoB, Nat.beq_refl]
  · intro parentEntry hOp hTy hB
    refine ⟨?_, ?_, ?_⟩
    · show evalReifyFnPointer locals op rawMutU32MirTy mem decls emptyLayoutTable "ArrayToPointer" = _
      unfold evalReifyFnPointer; simp only [h1, h2, h3, hL8, hOp, hTy, hArrOk, hB, Nat.beq_refl]
    · intro hDis; unfold deriveStackElemThinPtr; simp [hDis]
    · intro v0 v1 hLive hDepth hSlot
      have hAct : activeFrameSlot? locals' mem.callStack parentEntry.targetFrameDepth parentEntry.targetLocal =
          some (.init (.aggregate 0 [.scalar ⟨v0, 4⟩, .scalar ⟨v1, 4⟩])) := by
        cases hCs : mem.callStack <;> simp [activeFrameSlot?, hDepth, hCs, Nat.beq_refl, hSlot]
      have hStr : inferElemListByteStride [.scalar ⟨v0, 4⟩, .scalar ⟨v1, 4⟩] = 4 := rfl
      refine ⟨?_, ?_, ?_⟩
      · intro hProj hOff; unfold deriveStackElemThinPtr
        cases hP : parentEntry.perm with
        | disabled => exact absurd hP hLive
        | _ =>
          simp only [hProj, hOff, hAct, stripTransparentProjections, normalizeSubsliceProjections,
            readSliceBackingAggregate?, hStr, byteOffsetToElemIdx?, endsWithSubslice,
            Nat.add_zero, Nat.zero_add, Nat.ble, Nat.beq_refl]; rfl
      · intro hProj hOff; unfold deriveStackElemThinPtr
        cases hP : parentEntry.perm with
        | disabled => exact absurd hP hLive
        | _ => simp only [hProj, hOff, hAct]; rfl
      · intro hProj hNe
        have hBack : readSliceBackingAggregate? locals' (.aggregate 0 [.scalar ⟨v0, 4⟩, .scalar ⟨v1, 4⟩]) [] 2 =
            some ([], 0, [.scalar ⟨v0, 4⟩, .scalar ⟨v1, 4⟩]) := rfl
        have hLen2 : Trusted.Sequence.length ([MirSemantics.Value.scalar ⟨v0, 4⟩, .scalar ⟨v1, 4⟩]) = 2 := rfl
        unfold deriveStackElemThinPtr
        cases hP : parentEntry.perm with
        | disabled => exact absurd hP hLive
        | _ =>
          simp only [hProj, hAct, stripTransparentProjections, normalizeSubsliceProjections, hBack, hStr]
          cases hIdx : byteOffsetToElemIdx? p.offsetBytes 4 with
          | none => rfl
          | some k =>
            have hk := byteOffsetToElemIdx?_pos_of_ne_zero p.offsetBytes 4 k hNe hIdx
            have hBle : Nat.ble (Nat.add (Nat.add k 0) 2) 2 = false := by
              cases k with | zero => exact absurd hk (by decide) | succ _ => rfl
            simp only [hLen2, hBle]
  · intro hOp hTy
    show evalReifyFnPointer locals op rawMutU32MirTy mem decls emptyLayoutTable "ArrayToPointer" = _
    unfold evalReifyFnPointer; simp only [h1, h2, h3, hL8, hOp, hTy, hArrOk, Nat.beq_refl]
  · intro hOp hTy
    show evalReifyFnPointer locals op rawMutU32MirTy mem decls emptyLayoutTable "ArrayToPointer" = .ub
    unfold evalReifyFnPointer; simp only [h1, h2, h3, hL8, hOp, hTy, hArrBad, Nat.beq_refl]

/-! ### C8 Concrete End-to-End Witnesses covering ALL 5 Coercion Kinds
(`Mach` & `MachTB`) -/
def c8AllFiveMir : MirAst.CapturedMir := mkMirBody "ep2::c8_all_five"
    [mkDecl rawConstU32MirTy, mkDecl fnPtrSafeU32MirTy, mkDecl fnPtrSafeU32MirTy,
     mkDecl fnPtrUnsafeU32MirTy, mkDecl arr2U32MirTy, mkDecl rawMutArr2U32MirTy, mkDecl rawMutU32MirTy] 0
    [mkBb [mkSt (.storageLive 1), mkSt (.storageLive 2), mkSt (.storageLive 3),
       mkSt (.storageLive 4), mkSt (.storageLive 5), mkSt (.storageLive 6),
       mkSt (.assign (locPlace 1) (.cast (.pointerCoercion "ReifyFnPointer")
         (constZst (fnDefU32MirTy "ep2::target_fn")) fnPtrSafeU32MirTy)),
       mkSt (.assign (locPlace 2) (.cast (.pointerCoercion "ClosureFnPointer")
         (constZst (closureZstMirTy "ep2::zst_closure")) fnPtrSafeU32MirTy)),
       mkSt (.assign (locPlace 3) (.cast (.pointerCoercion "UnsafeFnPointer") (.copy (locPlace 1)) fnPtrUnsafeU32MirTy)),
       mkSt (.assign (locPlace 4) (.aggregate (.array u32MirTy) [constU32 10, constU32 20])),
       mkSt (.assign (locPlace 5) (.rawPtr .mut (locPlace 4))), mkSt (.assign (locPlace 6) (.cast (.pointerCoercion "ArrayToPointer")
         (.copy (locPlace 5)) rawMutU32MirTy)),
       mkSt (.assign (locPlace 0) (.cast (.pointerCoercion "MutToConstPointer") (.copy (locPlace 6)) rawConstU32MirTy))] .return_]
def c8MrFn : Gen.Function := mkMrFn [(localName 0, thinRawPtrTy), (localName 1, thinRawPtrTy), (localName 2, thinRawPtrTy),
          (localName 3, thinRawPtrTy), (localName 4, .Array u32MrTy 2),
          (localName 5, thinRawPtrTy), (localName 6, thinRawPtrTy)] [] (localName 0)
    [(bbName 0, ⟨[.Assign (.Local (localName 1)) (.Constant (.FnPointer (fnName 1)) thinRawPtrTy),
        .Assign (.Local (localName 2)) (.Constant (.FnPointer (fnName 2)) thinRawPtrTy), .Assign (.Local (localName 3))
          (.UnOp (.Cast (.Transmute thinRawPtrTy)) (.Load (.Local (localName 1)))),
        .Assign (.Local (localName 4)) (.Tuple [.Constant (.Int 10) u32MrTy, .Constant (.Int 20) u32MrTy] (.Array u32MrTy 2)),
        .Assign (.Local (localName 5)) (.AddrOf (.Local (localName 4)) (.Raw .None)), .Assign (.Local (localName 6))
          (.UnOp (.Cast (.Transmute thinRawPtrTy)) (.Load (.Local (localName 5)))),
        .Assign (.Local (localName 0)) (.UnOp (.Cast (.Transmute thinRawPtrTy)) (.Load (.Local (localName 6))))], .Return, .Regular⟩)]
def c8AllFiveMach : Mach :=
  let dummyTargetFn := mkMrFn [] [] (localName 0) [(bbName 0, ⟨[], .Return, .Regular⟩)]
  let u8b := List.replicate 8 (AbstractByte.Uninit : Byte)
  let fr := mkRootFrame c8MrFn [(localName 0, { addr := 128, provenance := some (⟨2⟩, ()) }),
     (localName 1, { addr := 256, provenance := some (⟨3⟩, ()) }), (localName 2, { addr := 384, provenance := some (⟨4⟩, ()) }),
     (localName 3, { addr := 512, provenance := some (⟨5⟩, ()) }), (localName 4, { addr := 640, provenance := some (⟨6⟩, ()) }),
     (localName 5, { addr := 768, provenance := some (⟨7⟩, ()) }), (localName 6, { addr := 896, provenance := some (⟨8⟩, ()) })]
  mkMrMach (mkMrProg [(fnName 0, c8MrFn), (fnName 1, dummyTargetFn), (fnName 2, dummyTargetFn)])
    [mkFnAlloc 4096, mkFnAlloc 8192, mkStackAlloc 128 u8b 8, mkStackAlloc 256 u8b 8,
     mkStackAlloc 384 u8b 8, mkStackAlloc 512 u8b 8, mkStackAlloc 640 u8b 4, mkStackAlloc 768 u8b 8, mkStackAlloc 896 u8b 8] [fr]
    [(fnName 1, { addr := 4096, provenance := some (⟨0⟩, ()) }), (fnName 2, { addr := 8192, provenance := some (⟨1⟩, ()) })]
theorem c8_all_five_pointer_coercions_three_way_witness : runAVal c8AllFiveMir 16 (initMachineState c8AllFiveMir []) =
      some (.ptr { allocId := 2, offsetBytes := 0 } 8) ∧ (∃ m7, Interp.steps 7 c8AllFiveMach = .ok m7 ∧
      ([3, 4, 5, 2].map (fun i => m7.mem.memory.allocations[i]?.map (·.data))) =
      [some (ptrBytes 4096 (some (⟨0⟩, ()))), some (ptrBytes 8192 (some (⟨1⟩, ()))),
       some (ptrBytes 4096 (some (⟨0⟩, ()))), some (ptrBytes 640 (some (⟨6⟩, ())))]) ∧
    (∃ m7, Interp.stepsTB 7 (liftMachToTB c8AllFiveMach) = .ok m7 ∧ MachTB.wfLive m7 ∧
      ([3, 4, 5, 2].map (fun i => m7.mem.memory.mem.allocations[i]?.map (fun a => a.data.map projByteTB))) =
      [some ((ptrBytes 4096 (some (⟨0⟩, ()))).map (projByteTB ∘ liftByteTB)),
       some ((ptrBytes 8192 (some (⟨1⟩, ()))).map (projByteTB ∘ liftByteTB)),
       some ((ptrBytes 4096 (some (⟨0⟩, ()))).map (projByteTB ∘ liftByteTB)),
       some ((ptrBytes 640 (some (⟨6⟩, ()))).map (projByteTB ∘ liftByteTB))]) :=
  ⟨rfl, ok_of_map_toOption (by decide +kernel), ok_stepsTB_wfLive (by decide +kernel)⟩
/-- Concrete C8 wide-slice (`*mut [u32] → *const [u32]`), wide-dyn (`*mut dyn
Tr → *const dyn Tr`), and negative witnesses across Trusted, `Mach`, and
`MachTB` (capturing closure `.ub`, already-`unsafe` `UnsafeFnPointer` `.ub`,
shape-mismatch `.ub`, and unrecognized coercion tag `.unsupported`). -/
theorem c8_capturing_closure_wide_and_unknown_tag_witness :
    let capDecls := [mkDecl fnPtrSafeU32MirTy, mkDecl (closureCapMirTy "ep2::cap_cl")]
    let mem0 := (initMachineState c8AllFiveMir []).memory
    let wideMir := mkMirBody "ep2::c8_wide_slice" [mkDecl rawConstSliceU32MirTy, mkDecl rawMutSliceU32MirTy] 1
      [mkBb [mkSt (.assign (locPlace 0) (.cast (.pointerCoercion "MutToConstPointer") (.copy (locPlace 1)) rawConstSliceU32MirTy))]
        .return_]
    let wideBytes := ptrBytes 256 (some (⟨1⟩, ())) ++ scalarBytes IntType.usize_ty 3
    let wideMach := c7MkTransmuteMach wideSlicePtrMrTy wideSlicePtrMrTy wideBytes 16
    -- Wide slice *mut [u32] -> *const [u32] 3-way witness
    runAVal wideMir 4 (initMachineState wideMir [annealWidePtrVal { allocId := 5, offsetBytes := 0 } 3 8]) =
      some (annealWidePtrVal { allocId := 5, offsetBytes := 0 } 3 8) ∧
    (∃ m1, Interp.step wideMach = .ok m1 ∧ m1.mem.memory.allocations[0]?.map (·.data) = some wideBytes) ∧
    (∃ m1, Interp.stepTB (liftMachToTB wideMach) = .ok m1 ∧ MachTB.wfLive m1 ∧
      m1.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) = some (wideBytes.map (projByteTB ∘ liftByteTB))) ∧
    -- Wide dyn *mut dyn Tr -> *const dyn Tr on Trusted
    evalRvalue [.uninit, .init (.aggregate 0 [.ptr { allocId := 5, offsetBytes := 0 } 8, .ptr { allocId := 9, offsetBytes := 0 } 8])]
      (.cast (.pointerCoercion "MutToConstPointer") (.copy (locPlace 1)) rawConstDynMirTy)
      mem0 [mkDecl rawConstDynMirTy, mkDecl rawMutDynMirTy] emptyLayoutTable =
      .ok (.aggregate 0 [.ptr { allocId := 5, offsetBytes := 0 } 8, .ptr { allocId := 9, offsetBytes := 0 } 8])
          [.uninit, .init (.aggregate 0 [.ptr { allocId := 5, offsetBytes := 0 } 8,
                                         .ptr { allocId := 9, offsetBytes := 0 } 8])] mem0 ∧
    -- Capturing closure rejected by ClosureFnPointer (.ub)
    evalRvalue [.uninit, .init (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨0, 8⟩])]
      (.cast (.pointerCoercion "ClosureFnPointer") (.copy (locPlace 1)) fnPtrSafeU32MirTy)
      mem0 capDecls emptyLayoutTable = .ub ∧
    -- Already-unsafe fn pointer rejected by UnsafeFnPointer (.ub)
    evalRvalue [.uninit, .init (.ptr { allocId := fnPtrAllocBase, offsetBytes := 0 } 8)]
      (.cast (.pointerCoercion "UnsafeFnPointer") (.copy (locPlace 1)) fnPtrUnsafeU32MirTy)
      mem0 [mkDecl fnPtrUnsafeU32MirTy, mkDecl fnPtrUnsafeU32MirTy] emptyLayoutTable = .ub ∧
    -- Shape-mismatch UB (thin ptr with wide slice target)
    evalRvalue [.uninit, .init (.ptr { allocId := 5, offsetBytes := 0 } 8)]
      (.cast (.pointerCoercion "MutToConstPointer") (.copy (locPlace 1)) rawConstSliceU32MirTy)
      mem0 [mkDecl rawConstSliceU32MirTy, mkDecl rawMutU32MirTy] emptyLayoutTable = .ub ∧
    -- Unrecognized coercion tag returns .unsupported
    evalRvalue [.uninit, .init (.ptr { allocId := fnPtrAllocBase, offsetBytes := 0 } 8)]
      (.cast (.pointerCoercion "UnknownCoercion") (.copy (locPlace 1)) fnPtrUnsafeU32MirTy)
      mem0 [mkDecl fnPtrUnsafeU32MirTy, mkDecl fnPtrSafeU32MirTy] emptyLayoutTable = .unsupported := ⟨rfl,
   ok_of_map_toOption (by decide +kernel), ok_stepTB_wfLive (by decide +kernel),
   rfl, rfl, rfl, rfl, rfl⟩

/-! ## §9 (`C9`): `ProjectionElem.unwrapUnsafeBinder` (`Mach` & `MachTB`) -/
/-- **C9 Fragment Boundary (`translatePlace_unwrapUnsafeBinder_none`)**:
`Translate.translatePlace` and `Translate.translateFieldPlace` both reject
`.unwrapUnsafeBinder`. -/
theorem translatePlace_unwrapUnsafeBinder_none (decls : List MirAst.LocalDecl) (loc : Nat) (innerTy : MirAst.Ty)
    (rest : List MirAst.ProjectionElem) (base : Gen.PlaceExpr) :
    translatePlace decls ⟨loc, .unwrapUnsafeBinder innerTy :: rest⟩ = none ∧
    translateFieldPlace base (.unwrapUnsafeBinder innerTy :: rest) = none := ⟨rfl, rfl⟩
/-- **C9 Trusted Universal Transparency & Deref-Chain Laws (`evalPlaceRead`,
`writePlaceValue`, `readProjectedValue`, `writeProjectedValue`,
`readProjectedValueUnionAware`, `splitLastDeref?`)**: Proves transparency of
`.unwrapUnsafeBinder` across projection reads/writes, union-aware reads,
`Rvalue.len` (`splitLastDeref?`), non-leading `.deref` `.unsupported`
boundaries, and leading-`.deref` `[.deref, .unwrapUnsafeBinder _]` reads and
writes (both untyped AND typed with non-empty `decls` for `u32` and `bool`
invalid-bit UB). -/
theorem trusted_unwrapUnsafeBinder_transparent (locals : List LocalSlot) (loc : Nat) (val newVal : MirSemantics.Value)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation) (decls : List MirAst.LocalDecl) (layouts : LayoutTable)
    (baseTy innerTy : MirAst.Ty) (rest : List MirAst.ProjectionElem) :
    readProjectedValue locals val (.unwrapUnsafeBinder innerTy :: rest) = readProjectedValue locals val rest ∧
    writeProjectedValue locals val (.unwrapUnsafeBinder innerTy :: rest) newVal = writeProjectedValue locals val rest newVal ∧
    readProjectedValueUnionAware locals decls layouts val baseTy (.unwrapUnsafeBinder innerTy :: rest) =
      readProjectedValueUnionAware locals decls layouts val (resolveTyWithLocalDecls decls layouts innerTy) rest ∧
    splitLastDeref? (.unwrapUnsafeBinder innerTy :: rest) = splitLastDeref? rest ∧
    splitLastDeref? [.deref, .unwrapUnsafeBinder innerTy] = some [] ∧
    splitLastDeref? [.unwrapUnsafeBinder innerTy, .deref] = some [] ∧
    isScalarCompatibleProj (.unwrapUnsafeBinder innerTy :: rest) = isScalarCompatibleProj rest ∧
    stripTransparentProjections (.unwrapUnsafeBinder innerTy :: rest) = stripTransparentProjections rest ∧
    (get? locals loc = some (.init val) → evalPlaceRead locals ⟨loc, [.unwrapUnsafeBinder innerTy]⟩ borrows globals = .ok val locals ∧
      writePlaceValue locals borrows ⟨loc, [.unwrapUnsafeBinder innerTy]⟩ newVal = writePlaceValue locals borrows ⟨loc, []⟩ newVal ∧
      evalPlaceRead locals ⟨loc, [.unwrapUnsafeBinder innerTy, .deref]⟩ borrows globals = .unsupported ∧
      writePlaceValue locals borrows ⟨loc, [.unwrapUnsafeBinder innerTy, .deref]⟩ newVal = .unsupported) ∧
    (∀ ptrLoc ptrVal entry callStack, get? locals ptrLoc = some (.init (.ptr ptrVal 8)) →
      lookupBorrow borrows ptrVal.tag = some entry → entry.perm = .active → entry.targetProjection = [] → ptrVal.offsetBytes = 0 →
      (activeFrameSlot? locals callStack entry.targetFrameDepth entry.targetLocal = some (.init val) →
        writePlaceValue locals borrows ⟨ptrLoc, [.deref, .unwrapUnsafeBinder innerTy]⟩ newVal [] emptyLayoutTable callStack =
          writePlaceValue locals borrows ⟨ptrLoc, [.deref]⟩ newVal [] emptyLayoutTable callStack ∧
        evalPlaceRead locals ⟨ptrLoc, [.deref, .unwrapUnsafeBinder innerTy]⟩
          borrows globals emptyLayoutTable [] [] callStack = .ok val locals) ∧
      (∀ bits newBits locals', ptrLoc = 0 → entry.targetLocal = 1 → entry.targetFrameDepth = length callStack →
        get? locals 1 = some (.init (.scalar ⟨bits, 4⟩)) → set? locals 1 (.init (.scalar ⟨newBits, 4⟩)) = some locals' →
        let declsU32 := [mkDecl rawMutU32MirTy, mkDecl u32MirTy]
        evalPlaceRead locals ⟨0, [.deref, .unwrapUnsafeBinder u32MirTy]⟩
          borrows globals emptyLayoutTable [] declsU32 callStack = .ok (.scalar ⟨bits, 4⟩) locals ∧
        writePlaceValue locals borrows ⟨0, [.deref, .unwrapUnsafeBinder u32MirTy]⟩
          (.scalar ⟨newBits, 4⟩) declsU32 emptyLayoutTable callStack = .ok locals' ∧
        writePlaceValue locals borrows ⟨0, [.deref]⟩ (.scalar ⟨newBits, 4⟩) declsU32 emptyLayoutTable callStack = .ok locals') ∧
      (ptrLoc = 0 → entry.targetLocal = 1 →
        activeFrameSlot? locals callStack entry.targetFrameDepth 1 = some (.init (.scalar ⟨2, 1⟩)) →
        evalPlaceRead locals ⟨0, [.deref, .unwrapUnsafeBinder boolMirTy]⟩ borrows globals emptyLayoutTable []
          [mkDecl { kind := .rawPtr .not boolMirTy.kind, layoutIdx := 0 }, mkDecl boolMirTy]
          callStack = .ub)) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro hSlot
    exact ⟨by unfold evalPlaceRead; dsimp only []; rw [hSlot]; rfl,
           by unfold writePlaceValue; dsimp only []; rw [hSlot]; rfl,
           by unfold evalPlaceRead; dsimp only []; rw [hSlot]; rfl,
           by unfold writePlaceValue; dsimp only []; rw [hSlot]; rfl⟩
  · intro ptrLoc ptrVal entry callStack hPtr hB hPerm hTProj hOff
    have hNil : ∀ {α : Type} (n : Nat), get? ([] : List α) n = none := fun n => by cases n <;> rfl
    have hUnion : ∀ ty, isUnionLayout emptyLayoutTable ty = false := fun ty => by
      unfold isUnionLayout LayoutTable.lookup emptyLayoutTable; cases ty.kind <;> cases ty.layoutIdx <;> rfl
    rcases ptrVal with ⟨aid, off⟩
    rcases entry with ⟨eTag, tLoc, tProj, ePerm, rOff, rLen, eProt, pTag, tDepth, aDead⟩
    dsimp only [] at hPerm hTProj hOff; subst hPerm; subst hTProj; subst hOff
    refine ⟨?_, ?_, ?_⟩
    · intro hAct; refine ⟨?_, ?_⟩
      · unfold writePlaceValue
        simp only [hPtr, hB, needsThinPtrElemResolution, hAct, writeProjectedValue]
      · unfold evalPlaceRead evalStackThinPtrTypedDerefRead
        simp only [hPtr, hB, hAct, placeTyResolved, checkDerefAlign, checkTargetPlaceAlign,
          inferCallerTargetDecls, resolveStackThinPtrTargetProjWithResidual?,
          startsWithArrayOrSliceProj, projHasSubslice, placeTouchesUnion, tyProjTouchesUnion, hUnion, resolveTyWithLocalDecls,
          readProjectedForLocal, readProjectedValue, stripTransparentProjections, hNil]; rfl
    · intro bits newBits locals' hPL hTL hDepth hSlot1 hSet1
      dsimp only [] at hTL hDepth; subst hPL; subst hTL; subst hDepth
      have hAct : activeFrameSlot? locals callStack (length callStack) 1 = some (.init (.scalar ⟨bits, 4⟩)) := by
        cases callStack <;> simp [activeFrameSlot?, Nat.beq_refl, hSlot1]
      have hTgt : activeFrameTargetLocals? locals callStack
          { tag := eTag, targetLocal := 1, targetProjection := [], perm := .active,
            rangeOffset := rOff, rangeLen := rLen, protector := eProt, parentTag := pTag,
            targetFrameDepth := length callStack, allocDead := aDead } = some locals := by
        cases callStack <;> simp [activeFrameTargetLocals?, activeFrameSlot?, Nat.beq_refl, hSlot1]
      refine ⟨?_, ?_, ?_⟩
      · unfold evalPlaceRead evalStackThinPtrTypedDerefRead
        simp only [hPtr, hB, hAct]; rfl
      · unfold writePlaceValue
        simp only [hPtr, hB, needsThinPtrElemResolution, hTgt]
        unfold writeStackThinPtrTypedDeref; simp only [hSlot1]
        change (match set? locals 1 (.init (.scalar ⟨newBits, 4⟩)) with
          | some l' => PlaceWriteResult.ok l' | none => .ub) = .ok locals'
        rw [hSet1]
      · unfold writePlaceValue
        simp only [hPtr, hB, needsThinPtrElemResolution, hTgt]
        unfold writeStackThinPtrTypedDeref; simp only [hSlot1]
        have hSpl : spliceScalarSlice? ⟨bits, 4⟩ 0 ⟨newBits, 4⟩ = some ⟨newBits, 4⟩ := rfl
        have hRd : readProjectedForLocal locals [mkDecl rawMutU32MirTy, mkDecl u32MirTy]
            emptyLayoutTable 1 (.scalar ⟨bits, 4⟩) [] = .ok (.scalar ⟨bits, 4⟩) := rfl
        simp only [hRd, hSpl, hSet1]; rfl
    · intro hPL hTL hAct
      dsimp only [] at hTL; subst hPL; subst hTL; unfold evalPlaceRead evalStackThinPtrTypedDerefRead
      simp only [hPtr, hB, hAct]; rfl
/-- **C9 MiniRust Polymorphic Field-0 Wrapper Place & `Transmute` Identity
(`Mach` & `MachTB`)**. -/
theorem checkValueM_thinRawPtr_of_inBounds {M : Type} [Gen.Memory M] [MemoryOps M]
    (addr : Int) (prov : Option (Gen.Memory.Provenance M)) (m : Option (Machine M))
    (hin : inBounds addr .Unsigned x86_64.PTR_SIZE = true) :
    checkValueM (M := M) (.Ptr (ThinPointer.widen { addr := addr, provenance := prov } none)) thinRawPtrTy m = .ok () := by
  unfold checkValueM checkPtrM
  simp only [thinRawPtrTy, ThinPointer.widen, ensureElseUb, hin, ↓reduceIte,
    PtrType.meta_kind, checkPtrMetadataM, PtrType.safe_pointee,
    Bool.not_true, Bool.false_eq_true, pure, Except.pure, bind, Except.bind]
theorem transmuteM_binderWrapper_u32_and_thinPtr {M : Type} [Gen.Memory M] [MemoryOps M]
    (bits addr : Nat) (hBits : bits < 2 ^ 32) (hAddr : addr < 2 ^ 64)
    (prov : Option (Gen.Memory.Provenance M)) (m : Option (Machine M)) :
    let vInt : Gen.Value M := .Int (intFromBits bits u32)
    let vPtr : Gen.Value M := .Ptr (ThinPointer.widen { addr := addr, provenance := prov } none)
    transmuteM (M := M) (.Tuple [vInt]) (mrBinderWrapperTy u32MrTy ⟨4⟩ ⟨4⟩) u32MrTy m = .ok vInt ∧
    transmuteM (M := M) vInt u32MrTy (mrBinderWrapperTy u32MrTy ⟨4⟩ ⟨4⟩) m = .ok (.Tuple [vInt]) ∧
    transmuteM (M := M) (.Tuple [vPtr]) (mrBinderWrapperTy thinRawPtrTy ⟨8⟩ ⟨8⟩) thinRawPtrTy m = .ok vPtr ∧
    transmuteM (M := M) vPtr thinRawPtrTy (mrBinderWrapperTy thinRawPtrTy ⟨8⟩ ⟨8⟩) m = .ok (.Tuple [vPtr]) := by
  intro vInt vPtr
  have hLenI : ((leBytes bits 4).map (fun b => (AbstractByte.Init b none : AbstractByte (Gen.Memory.Provenance M)))).length = 4 := by
    rw [List.length_map, leBytes_length]
  have hRoundI := transmuteM_binderWrapper_roundtrip (M := M) u32MrTy ⟨4⟩ ⟨4⟩ vInt _ m rfl rfl
    (encodeIntM_intFromBits u32 (by decide) bits hBits) hLenI (decodeIntM_leBytes u32 (by decide) bits hBits)
    (checkValueM_int_of_inBounds _ u32 m (inBounds_intFromBits_cf u32 (by decide) bits hBits))
  have hEncP : Type.encodeM (M := M) thinRawPtrTy vPtr = .ok (encodePtrBytesM (M := M) prov 0 (leBytes addr 8)) := by
    simp only [thinRawPtrTy, Type.encodeM, PtrType.as_wide_pair, PtrType.meta_kind, vPtr,
      ThinPointer.widen]; exact encodePtrM_eq addr hAddr prov
  have hDecP : Type.decodeM (M := M) thinRawPtrTy (encodePtrBytesM (M := M) prov 0 (leBytes addr 8)) = .ok (some vPtr) := by
    simp only [thinRawPtrTy, Type.decodeM, PtrType.as_wide_pair, PtrType.meta_kind, vPtr,
      ThinPointer.widen]; rw [decodePtrM_encodePtrBytesM addr hAddr prov, ok_bind]; rfl
  have hLenP : (encodePtrBytesM (M := M) prov 0 (leBytes addr 8)).length = 8 := by
    rw [encodePtrBytesM_length, leBytes_length]
  have hRoundP := transmuteM_binderWrapper_roundtrip (M := M) thinRawPtrTy ⟨8⟩ ⟨8⟩ vPtr _ m layout_thinRawPtr rfl hEncP hLenP hDecP
    (checkValueM_thinRawPtr_of_inBounds (addr : Int) prov m (inBounds_usize_cf addr hAddr))
  exact ⟨hRoundI.2.2.1, hRoundI.2.2.2, hRoundP.2.2.1, hRoundP.2.2.2⟩
theorem minirust_evalPlaceM_binderWrapper_field0 {M : Type} [Gen.Memory M] [MemoryOps M]
    (m m1 : Machine M) (base : Gen.PlaceExpr) (place : Gen.Place M) (inner : Gen.Type) (sz : LibSpecr.Size) (al : LibSpecr.Align)
    (hBase : evalPlaceM m base = .ok ((place, mrBinderWrapperTy inner sz al), m1))
    (hMeta : place.ptr.metadata = none) (hInnerLay : Type.layout inner = .ok (.Sized sz al))
    (hHead : TupleHeadLayout.head_size_and_align ⟨sz, al, none⟩ = (sz, al))
    (hPtr0 : ptrOffsetInboundsM m1 place.ptr.thin_pointer 0 = .ok place.ptr.thin_pointer) :
    evalPlaceM m (.Field base 0) = .ok (({ place with ptr := ThinPointer.widen place.ptr.thin_pointer none }, inner), m1) := by
  have hCond : (0 : Int) ≤ 0 ∧ (0 : Int) < ([(({ bytes := 0 } : LibSpecr.Size), inner)].length : Int) := by
    simp
  have hIdx : listIndex [(({ bytes := 0 } : LibSpecr.Size), inner)] 0 "sized_fields[field]" =
      .ok (({ bytes := 0 } : LibSpecr.Size), inner) := rfl
  have hLayWrap : Type.layout (mrBinderWrapperTy inner sz al) = .ok (.Sized sz al) := by
    simp only [mrBinderWrapperTy, Type.layout, hHead, pure, Except.pure]
  have hSzWrap : computeSizeM m1 (.Sized sz al) place.ptr.metadata = .ok sz := by
    simp only [computeSizeM, LayoutStrategy.compute_size_and_align, hMeta, pure, Except.pure, bind, Except.bind]
  unfold evalPlaceM; rw [hBase, ok_bind]; dsimp only [mrBinderWrapperTy]
  rw [ite_eq_left_iff.mpr (fun hn => absurd hCond hn), hIdx, ok_bind]; dsimp only []
  rw [show Type.layout (.Tuple [(⟨0⟩, inner)] ⟨sz, al, none⟩ none) = .ok (.Sized sz al) from hLayWrap, ok_bind, hSzWrap, ok_bind]
  have hLe : (!decide (({ bytes := 0 } : LibSpecr.Size).bytes ≤ sz.bytes)) = false := by simp
  rw [hLe]; simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show (({ bytes := 0 } : LibSpecr.Size).bytes : Int) = 0 from rfl, hPtr0, ok_bind, hInnerLay, ok_bind]; rfl
/-- **C9 Coupled Two-Sided Wrapper `Assign` Statement & `MachTB.wfLive`
Lockstep (`unwrapUnsafeBinder_assign_coupled_lockstep_and_wfLive`)**: Couples
Trusted `evalStmt` assigning through `[.unwrapUnsafeBinder innerTy]` with
MiniRust `Interp.evalStatement` (`Mach`) and `evalStatementM` (`MachTB`)
assigning through `.Field base 0` on `mrBinderWrapperTy inner sz al`,
preserving `MachTB.wfLive`! -/
theorem unwrapUnsafeBinder_assign_coupled_lockstep_and_wfLive
    (s : MachineState) (dstLoc : Nat) (innerMirTy : MirAst.Ty) (rv : MirAst.Rvalue)
    (oldVal newVal : MirSemantics.Value) (locals1 locals2 : List LocalSlot) (mem1 : MirSemantics.Memory)
    (span : String) (decls : List MirAst.LocalDecl) (layouts : LayoutTable) (mBM mBM1 mBM2 mBMf : Mach) (mTB mTB1 mTB2 mTBf : MachTB)
    (base : Gen.PlaceExpr) (src : Gen.ValueExpr) (inner : Gen.Type) (sz : LibSpecr.Size) (al : LibSpecr.Align)
    (placeBM : Gen.Place BM) (vBM : Val) (tBM : Gen.Type) (placeTB : Gen.Place TBM) (vTB : Gen.Value TBM) (tTB : Gen.Type)
    (hRv : evalRvalue s.frame.locals rv s.memory decls layouts = .ok newVal locals1 mem1)
    (hGet : get? locals1 dstLoc = some (.init oldVal))
    (hNoUnion : placeTouchesUnion decls layouts (locPlace dstLoc [.unwrapUnsafeBinder innerMirTy]) = false)
    (hSet : set? locals1 dstLoc (.init newVal) = some locals2) (hProt : mem1.activeProtectors = [])
    (hInnerLay : Type.layout inner = .ok (.Sized sz al)) (hHead : TupleHeadLayout.head_size_and_align ⟨sz, al, none⟩ = (sz, al))
    (hpBM : evalPlaceM mBM base = .ok ((placeBM, mrBinderWrapperTy inner sz al), mBM1)) (hMetaBM : placeBM.ptr.metadata = none)
    (hPtrBM0 : ptrOffsetInboundsM mBM1 placeBM.ptr.thin_pointer 0 = .ok placeBM.ptr.thin_pointer)
    (hvBM : evalValueM mBM1 src = .ok ((vBM, tBM), mBM2))
    (hstBM : placeStoreM mBM2 { placeBM with ptr := ThinPointer.widen placeBM.ptr.thin_pointer none } vBM inner = .ok mBMf)
    (hwfTB : MachTB.wfLive mTB) (hpTB : evalPlaceM mTB base = .ok ((placeTB, mrBinderWrapperTy inner sz al), mTB1))
    (hMetaTB : placeTB.ptr.metadata = none)
    (hPtrTB0 : ptrOffsetInboundsM mTB1 placeTB.ptr.thin_pointer 0 = .ok placeTB.ptr.thin_pointer)
    (hvTB : evalValueM mTB1 src = .ok ((vTB, tTB), mTB2))
    (hstTB : placeStoreM mTB2 { placeTB with ptr := ThinPointer.widen placeTB.ptr.thin_pointer none } vTB inner = .ok mTBf) :
    let resProj := resolveBorrowWriteLocalProj decls layouts locals1 dstLoc [.unwrapUnsafeBinder innerMirTy]
    evalStmt s { kind := .assign (locPlace dstLoc [.unwrapUnsafeBinder innerMirTy]) rv, span := span } decls layouts =
      MirStepNode.step (advanceStmt s locals2 { mem1 with
          borrows := invalidateConflictingBorrowsAtProj mem1.borrows dstLoc .none resProj 0 0 (length mem1.callStack) }) ∧
    Interp.evalStatement mBM (.Assign (.Field base 0) src) = .ok mBMf ∧ evalStatementM mTB (.Assign (.Field base 0) src) = .ok mTBf ∧
    MachTB.wfLive mTBf := by
  have hFBM := minirust_evalPlaceM_binderWrapper_field0 mBM mBM1 base placeBM inner sz al hpBM hMetaBM hInnerLay hHead hPtrBM0
  have hFTB := minirust_evalPlaceM_binderWrapper_field0 mTB mTB1 base placeTB inner sz al hpTB hMetaTB hInnerLay hHead hPtrTB0
  have hBM : evalStatementM mBM (.Assign (.Field base 0) src) = .ok mBMf := by
    dsimp only [evalStatementM]; rw [hFBM, ok_bind, hvBM, ok_bind]; exact hstBM
  have hTB : evalStatementM mTB (.Assign (.Field base 0) src) = .ok mTBf := by
    dsimp only [evalStatementM]; rw [hFTB, ok_bind, hvTB, ok_bind]; exact hstTB
  refine ⟨?_, by rw [← evalStatementM_bm_eq]; exact hBM, hTB, evalStatementM_tb_wfLive hwfTB hTB⟩
  simp only [evalStmt, hRv, locPlace, hGet, ensureNestedFieldShells, writeProjectedForLocal,
    hNoUnion, writeProjectedValue, hSet, hProt]
def c9BinderReadWriteMir : MirAst.CapturedMir := mkMirBody "ep2::c9_binder_rw"
    [mkDecl u32MirTy, mkDecl u32MirTy, mkDecl rawMutU32MirTy, mkDecl rawMutU32MirTy, mkDecl rawConstSliceU32MirTy] 1
    [mkBb [mkSt (.storageLive 2), mkSt (.storageLive 3),
       mkSt (.assign (locPlace 1 [.unwrapUnsafeBinder u32MirTy]) (.use (constU32 55))),
       mkSt (.assign (locPlace 0) (.use (.copy (locPlace 1 [.unwrapUnsafeBinder u32MirTy])))),
       mkSt (.assign (locPlace 2) (.rawPtr .mut (locPlace 1 [.unwrapUnsafeBinder u32MirTy]))),
       mkSt (.assign (locPlace 3) (.use (.move (locPlace 2 [.unwrapUnsafeBinder rawMutU32MirTy])))),
       mkSt (.assign (locPlace 3 [.deref, .unwrapUnsafeBinder u32MirTy]) (.use (constU32 88))),
       mkSt (.assign (locPlace 0) (.use (.move (locPlace 3 [.deref, .unwrapUnsafeBinder u32MirTy]))))]
      .return_]
def c9BinderMrFn : Gen.Function := mkMrFn [(localName 0, u32MrTy), (localName 1, mrBinderWrapperTy u32MrTy ⟨4⟩ ⟨4⟩),
          (localName 2, mrBinderWrapperTy thinRawPtrTy ⟨8⟩ ⟨8⟩)]
    [localName 1] (localName 0) [(bbName 0, ⟨[.Assign (.Field (.Local (localName 1)) 0) (.Constant (.Int 55) u32MrTy),
        .Assign (.Local (localName 0)) (.Load (.Field (.Local (localName 1)) 0)),
        .Assign (.Field (.Local (localName 2)) 0) (.AddrOf (.Field (.Local (localName 1)) 0) (.Raw .None)),
        .Assign (.Deref (.Load (.Field (.Local (localName 2)) 0)) u32MrTy) (.Constant (.Int 88) u32MrTy),
        .Assign (.Local (localName 0)) (.Load (.Deref (.Load (.Field (.Local (localName 2)) 0)) u32MrTy))],
       .Return, .Regular⟩)]
def c9BinderMach (local1Live : Bool := true) : Mach :=
  let locs : List (Gen.LocalName × Ptr) := (localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }) ::
      (if local1Live then [(localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })] else []) ++
      [(localName 2, { addr := 384, provenance := some (⟨2⟩, ()) })]
  mkMrMach (mkMrProg [(fnName 0, c9BinderMrFn)])
    [mkStackAlloc 128 (List.replicate 4 .Uninit) 4, mkStackAlloc 256 (scalarBytes u32 10) 4,
     mkStackAlloc 384 (List.replicate 8 .Uninit) 8]
    [mkRootFrame c9BinderMrFn locs]
/-- Concrete C9 positive witness (read, write, `Move`, deref, `Rvalue.len`,
wrapper `Transmute`, `MachTB.wfLive`) and dead-local UB witness across
Trusted, `Mach`, and `MachTB`. -/
theorem c9_unwrapUnsafeBinder_three_way_len_and_ub_witness :
    let sliceLenPlaceAfter : MirAst.Place := locPlace 0 [.deref, .unwrapUnsafeBinder { kind := .slice (.uint .u32), layoutIdx := 0 }]
    let sliceLenPlaceBefore : MirAst.Place := locPlace 0 [.unwrapUnsafeBinder rawConstSliceU32MirTy, .deref]
    let sliceMem := (initMachineState c9BinderReadWriteMir []).memory
    let sliceLocs : List LocalSlot := [.init (annealWidePtrVal { allocId := 9, offsetBytes := 0 } 4 8)]
    let wrapTransMach := c7MkTransmuteMach (mrBinderWrapperTy u32MrTy ⟨4⟩ ⟨4⟩) u32MrTy (scalarBytes u32 88) 4
    runAVal c9BinderReadWriteMir 12 (initMachineState c9BinderReadWriteMir [.scalar ⟨10, 4⟩]) =
      some (.scalar ⟨88, 4⟩) ∧ (∃ m5, Interp.steps 5 (c9BinderMach true) = .ok m5 ∧
      m5.mem.memory.allocations[0]?.map (·.data) = some (scalarBytes u32 88)) ∧
    (∃ m5, Interp.stepsTB 5 (liftMachToTB (c9BinderMach true)) = .ok m5 ∧ MachTB.wfLive m5 ∧
      m5.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some ((scalarBytes u32 88).map (projByteTB ∘ liftByteTB))) ∧
    (∃ m1, Interp.step wrapTransMach = .ok m1 ∧ m1.mem.memory.allocations[0]?.map (·.data) = some (scalarBytes u32 88)) ∧
    (∃ m1, Interp.stepTB (liftMachToTB wrapTransMach) = .ok m1 ∧ MachTB.wfLive m1 ∧
      m1.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some ((scalarBytes u32 88).map (projByteTB ∘ liftByteTB))) ∧
    evalRvalue sliceLocs (.len sliceLenPlaceAfter) sliceMem [mkDecl rawConstSliceU32MirTy]
      emptyLayoutTable = .ok (.scalar ⟨4, 8⟩) sliceLocs sliceMem ∧
    evalRvalue sliceLocs (.len sliceLenPlaceBefore) sliceMem [mkDecl rawConstSliceU32MirTy]
      emptyLayoutTable = .ok (.scalar ⟨4, 8⟩) sliceLocs sliceMem ∧
    stepMirFn c9BinderReadWriteMir
      { frame := { blockIdx := 0, stmtIdx := 2, locals := [.uninit, .dead, .uninit, .uninit, .uninit] },
        memory := sliceMem } = MirStepNode.fail .ub ∧
    Interp.step (c9BinderMach false) = .error (.ub "access to a dead local") ∧
    Interp.stepTB (liftMachToTB (c9BinderMach false)) = .error (.ub "access to a dead local") :=
  ⟨rfl, ok_of_map_toOption (by decide +kernel), ok_stepsTB_wfLive (by decide +kernel),
   ok_of_map_toOption (by decide +kernel), ok_stepTB_wfLive (by decide +kernel), rfl, rfl, rfl,
   eq_error_ub_of_interpUbMsg (by decide +kernel), eq_error_ub_of_interpUbMsg (by decide +kernel)⟩

/-! ## §10 (`C10`): `AggregateKind.closure` (`Mach` & `MachTB`) -/
/-- **C10 Fragment Boundary (`translateRvalue_closure_none`)**:
`Translate.translateRvalue` returns `none` for every `AggregateKind.closure`. -/
theorem translateRvalue_closure_none (layouts : LayoutTable) (decls : List MirAst.LocalDecl) (targetTy : Option MirAst.Ty)
    (dp : DefPath) (ops : List MirAst.Operand) :
    translateRvalue layouts decls targetTy (.aggregate (.closure dp) ops) = none := rfl
/-- **C10.1 Universal 0-Capture ZST Closure Step Law (`Mach` & `MachTB`)**:
Evaluating `.aggregate (.closure dp) []` produces `.aggregate 0 []` leaving
`locals` and `mem` untouched; MiniRust `ValueExpr.Tuple [] unitType` produces
`(.Tuple [], unitType)` leaving `m` untouched on EVERY `Machine M` (`Mach` &
`MachTB`). -/
theorem closure_zst_lockstep_M {M : Type} [Gen.Memory M] [MemoryOps M]
    (locals : List LocalSlot) (dp : DefPath) (mem : MirSemantics.Memory)
    (decls : List MirAst.LocalDecl) (layouts : LayoutTable) (m : Machine M) :
    evalRvalue locals (.aggregate (.closure dp) []) mem decls layouts = .ok (.aggregate 0 []) locals mem ∧
    evalValueM m (.Tuple [] unitType) = .ok ((.Tuple [], unitType), m) := ⟨rfl, rfl⟩
/-- **C10.2 Genuine Inductive `n`-Capture Closure Lockstep, Length
Preservation, & Arbitrary-Index Left-to-Right UB Propagation (`Mach` &
`MachTB`)**. -/
theorem evalOperands_length_and_ltr_ub (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable) (callerLocals : List LocalSlot) (decls : List MirAst.LocalDecl) (callStack : List SavedCallerFrame) :
    (∀ ops locals vals locals', evalOperands locals ops borrows globals layouts callerLocals decls callStack =
        .ok vals locals' → vals.length = ops.length) ∧ (∀ pre bad suf locals preVals localsMid,
      evalOperands locals pre borrows globals layouts callerLocals decls callStack = .ok preVals localsMid →
      evalOperand localsMid bad borrows globals layouts callerLocals decls callStack = .ub →
      evalOperands locals (pre ++ bad :: suf) borrows globals layouts callerLocals decls callStack = .ub) := by
  constructor
  · intro ops; induction ops with
    | nil => intro locals vals locals' h; simp [evalOperands] at h; rcases h with ⟨rfl, _⟩; rfl
    | cons op rest ih =>
      intro locals vals locals' h; simp only [evalOperands] at h
      cases h1 : evalOperand locals op borrows globals layouts callerLocals decls callStack with
      | ub | unsupported => simp [h1] at h
      | ok v l1 =>
        rw [h1] at h
        cases h2 : evalOperands l1 rest borrows globals layouts callerLocals decls callStack with
        | ub | unsupported => simp [h2] at h
        | ok vs l2 =>
          simp only [h2, OperandsEvalResult.ok.injEq] at h; rcases h with ⟨rfl, _⟩; simp [ih l1 vs l2 h2]
  · intro pre; induction pre with
    | nil =>
      intro bad suf locals preVals localsMid hPre hBad
      simp [evalOperands] at hPre; rcases hPre with ⟨_, rfl⟩; simp [evalOperands, hBad]
    | cons op rest ih =>
      intro bad suf locals preVals localsMid hPre hBad; simp only [evalOperands] at hPre
      cases h1 : evalOperand locals op borrows globals layouts callerLocals decls callStack with
      | ub | unsupported => simp [h1] at hPre
      | ok v l1 =>
        rw [h1] at hPre
        cases h2 : evalOperands l1 rest borrows globals layouts callerLocals decls callStack with
        | ub | unsupported => simp [h2] at hPre
        | ok vs l2 =>
          simp only [h2, OperandsEvalResult.ok.injEq] at hPre; rcases hPre with ⟨_, rfl⟩
          simp only [List.cons_append, evalOperands, h1, ih bad suf l1 vs l2 h2 hBad]
theorem evalValuesM_length_and_ltr_ub {M : Type} [Gen.Memory M] [MemoryOps M] :
    (∀ es (m m' : Machine M) mvals, evalValuesM m es = .ok (mvals, m') → mvals.length = es.length) ∧
    (∀ pre bad suf (m mMid : Machine M) preVals msg,
      evalValuesM m pre = .ok (preVals, mMid) → evalValueM mMid bad = .error (.ub msg) →
      evalValuesM m (pre ++ bad :: suf) = .error (.ub msg)) := by
  constructor
  · intro es; induction es with
    | nil => intro m m' mvals h; simp [evalValuesM, pure, Except.pure] at h; rcases h with ⟨rfl, _⟩; rfl
    | cons e rest ih =>
      intro m m' mvals h; simp only [evalValuesM] at h; cases h1 : evalValueM m e with
      | error _ => simp [h1, bind, Except.bind] at h
      | ok r1 =>
        rcases r1 with ⟨⟨v, _⟩, m1⟩; rw [h1, ok_bind] at h
        cases h2 : evalValuesM m1 rest with
        | error _ => simp [h2, bind, Except.bind] at h
        | ok r2 =>
          rcases r2 with ⟨vs, m2⟩
          simp only [h2, ok_bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, _⟩; simp [ih m1 m2 vs h2]
  · intro pre; induction pre with
    | nil =>
      intro bad suf m mMid preVals msg hPre hBad
      simp [evalValuesM, pure, Except.pure] at hPre; rcases hPre with ⟨_, rfl⟩
      simp [evalValuesM, hBad, bind, Except.bind]
    | cons e rest ih =>
      intro bad suf m mMid preVals msg hPre hBad; simp only [evalValuesM] at hPre
      cases h1 : evalValueM m e with
      | error _ => simp [h1, bind, Except.bind] at hPre
      | ok r1 =>
        rcases r1 with ⟨⟨v, _⟩, m1⟩; rw [h1, ok_bind] at hPre
        cases h2 : evalValuesM m1 rest with
        | error _ => simp [h2, bind, Except.bind] at hPre
        | ok r2 =>
          rcases r2 with ⟨vs, m2⟩
          simp only [h2, ok_bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hPre
          rcases hPre with ⟨_, rfl⟩
          simp only [List.cons_append, evalValuesM, h1, ok_bind, ih bad suf m1 m2 vs msg h2 hBad, bind, Except.bind]
theorem closure_n_capture_lockstep_M {M : Type} [Gen.Memory M] [MemoryOps M]
    (locals locals' : List LocalSlot) (dp : DefPath) (ops : List MirAst.Operand) (vals : List MirSemantics.Value)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (layouts : LayoutTable)
    (m m' : Machine M) (es : List Gen.ValueExpr) (mvals : List (Gen.Value M)) (mrClTy : Gen.Type) :
    (evalOperands locals ops mem.borrows mem.globals layouts mem.callerLocals decls
        mem.callStack = .ok vals locals' → evalValuesM m es = .ok (mvals, m') →
      vals.length = ops.length ∧ mvals.length = es.length ∧ evalRvalue locals (.aggregate (.closure dp) ops) mem decls layouts =
        .ok (.aggregate 0 vals) locals' mem ∧
      evalValueM m (.Tuple es mrClTy) = .ok ((.Tuple mvals, mrClTy), m')) ∧
    (∀ pre bad suf preVals localsMid mpre mbad msuf mpreVals mMid msg,
      evalOperands locals pre mem.borrows mem.globals layouts mem.callerLocals decls mem.callStack = .ok preVals localsMid →
      evalOperand localsMid bad mem.borrows mem.globals layouts mem.callerLocals decls mem.callStack = .ub →
      evalValuesM m mpre = .ok (mpreVals, mMid) → evalValueM mMid mbad = .error (.ub msg) →
      evalRvalue locals (.aggregate (.closure dp) (pre ++ bad :: suf)) mem decls layouts = .ub ∧
      evalValueM m (.Tuple (mpre ++ mbad :: msuf) mrClTy) = .error (.ub msg)) := by
  refine ⟨?_, ?_⟩
  · intro hOps hEs
    exact ⟨(evalOperands_length_and_ltr_ub ..).1 ops locals vals locals' hOps,
      (evalValuesM_length_and_ltr_ub (M := M)).1 es m m' mvals hEs,
      by simp only [evalRvalue, hOps],
      by simp only [evalValueM, hEs, bind, Except.bind, pure, Except.pure]⟩
  · intro pre bad suf preVals localsMid mpre mbad msuf mpreVals mMid msg hPre hBad hmPre hmBad
    have hT := (evalOperands_length_and_ltr_ub mem.borrows mem.globals layouts mem.callerLocals
      decls mem.callStack).2 pre bad suf locals preVals localsMid hPre hBad
    have hM := (evalValuesM_length_and_ltr_ub (M := M)).2 mpre mbad msuf m mMid mpreVals msg hmPre hmBad
    exact ⟨by simp only [evalRvalue, hT], by simp only [evalValueM, hM, bind, Except.bind]⟩
/-- **C10.3 Universal Two-Capture Closure Left-to-Right Evaluation & UB Law
(`Mach` & `MachTB`)** (corollary of `closure_n_capture_lockstep_M`). -/
theorem closure_two_capture_ltr_and_ub_M {M : Type} [Gen.Memory M] [MemoryOps M]
    (locals locals1 locals2 : List LocalSlot) (dp : DefPath) (op0 op1 : MirAst.Operand)
    (mem : MirSemantics.Memory) (decls : List MirAst.LocalDecl) (layouts : LayoutTable)
    (m m1 m2 : Machine M) (e0 e1 : Gen.ValueExpr) (mrClTy : Gen.Type) :
    (∀ v0 v1 mv0 mv1 t0 t1, evalOperand locals op0 mem.borrows mem.globals layouts mem.callerLocals decls
        mem.callStack = .ok v0 locals1 →
      evalOperand locals1 op1 mem.borrows mem.globals layouts mem.callerLocals decls
        mem.callStack = .ok v1 locals2 → evalValueM m e0 = .ok ((mv0, t0), m1) →
      evalValueM m1 e1 = .ok ((mv1, t1), m2) → evalRvalue locals (.aggregate (.closure dp) [op0, op1]) mem decls layouts =
        .ok (.aggregate 0 [v0, v1]) locals2 mem ∧
      evalValueM m (.Tuple [e0, e1] mrClTy) = .ok ((.Tuple [mv0, mv1], mrClTy), m2)) ∧
    (∀ msg, evalOperand locals op0 mem.borrows mem.globals layouts mem.callerLocals decls
        mem.callStack = .ub → evalValueM m e0 = .error (.ub msg) →
      evalRvalue locals (.aggregate (.closure dp) [op0, op1]) mem decls layouts = .ub ∧
      evalValueM m (.Tuple [e0, e1] mrClTy) = .error (.ub msg)) ∧
    (∀ v0 mv0 t0 msg, evalOperand locals op0 mem.borrows mem.globals layouts mem.callerLocals decls mem.callStack = .ok v0 locals1 →
      evalOperand locals1 op1 mem.borrows mem.globals layouts mem.callerLocals decls mem.callStack = .ub →
      evalValueM m e0 = .ok ((mv0, t0), m1) → evalValueM m1 e1 = .error (.ub msg) →
      evalRvalue locals (.aggregate (.closure dp) [op0, op1]) mem decls layouts = .ub ∧
      evalValueM m (.Tuple [e0, e1] mrClTy) = .error (.ub msg)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v0 v1 mv0 mv1 t0 t1 h0 h1 hm0 hm1
    exact ⟨by simp only [evalRvalue, evalOperands, h0, h1],
           by simp only [evalValueM, evalValuesM, hm0, hm1, bind, Except.bind, pure, Except.pure]⟩
  · intro msg h0 hm0
    exact (closure_n_capture_lockstep_M locals locals dp [] [] mem decls layouts m m [] []
      mrClTy).2 [] op0 [op1] [] locals [] e0 [e1] [] m msg rfl h0 rfl hm0
  · intro v0 mv0 t0 msg h0 h1 hm0 hm1
    exact (closure_n_capture_lockstep_M locals locals1 dp [] [] mem decls layouts m m1 [] []
      mrClTy).2 [op0] op1 [] [v0] locals1 [e0] e1 [] [mv0] m1 msg
      (by simp only [evalOperands, h0]) h1
      (by simp only [evalValuesM, hm0, bind, Except.bind, pure, Except.pure]) hm1
/-- MiniRust 16-byte closure tuple type capturing `(u32, *const u32)`: field
0 (`u32`) at offset 0, field 1 (`*const u32`) at offset 8, align 8. -/
def mrClosureCapTy : Gen.Type := .Tuple [(⟨0⟩, u32MrTy), (⟨8⟩, thinRawPtrTy)] ⟨⟨16⟩, ⟨8⟩, none⟩ none
/-- `Classical.choice`-free polymorphic 16-byte closure memory codec
(`encodeM_decodeM_mrClosureCapTy`): encodes field 0 (`u32`) at `0..4`,
preserves 4 `.Uninit` padding bytes at `4..8`, encodes field 1 (`*const u32`
with provenance `prov`) at `8..16`, and round-trips via `Type.decodeM`! -/
theorem encodeM_decodeM_mrClosureCapTy_of_codec {M : Type} [Gen.Memory M] [MemoryOps M]
    (v0 v1 : Gen.Value M) (x0 x1 x2 x3 y0 y1 y2 y3 y4 y5 y6 y7 : AbstractByte (Gen.Memory.Provenance M))
    (hEnc0 : Type.encodeM (M := M) u32MrTy v0 = .ok [x0, x1, x2, x3])
    (hDec0 : Type.decodeM (M := M) u32MrTy [x0, x1, x2, x3] = .ok (some v0))
    (hEnc1 : Type.encodeM (M := M) thinRawPtrTy v1 = .ok [y0, y1, y2, y3, y4, y5, y6, y7])
    (hDec1 : Type.decodeM (M := M) thinRawPtrTy [y0, y1, y2, y3, y4, y5, y6, y7] = .ok (some v1)) :
    let bs := [x0, x1, x2, x3] ++ List.replicate 4 .Uninit ++ [y0, y1, y2, y3, y4, y5, y6, y7]
    Type.encodeM (M := M) mrClosureCapTy (.Tuple [v0, v1]) = .ok bs ∧
    Type.decodeM (M := M) mrClosureCapTy bs = .ok (some (.Tuple [v0, v1])) := by
  intro bs
  have hSub0 : subsliceWithLength bs 0 4 = .ok [x0, x1, x2, x3] := rfl
  have hSub1 : subsliceWithLength bs 8 8 = .ok [y0, y1, y2, y3, y4, y5, y6, y7] := rfl
  refine ⟨?_, ?_⟩
  · unfold mrClosureCapTy Type.encodeM; dsimp only [TupleHeadLayout.head_size_and_align, List.length,
      ne_eq, not_true_eq_false, ↓reduceIte, Type.encodeFieldsM]
    rw [show (Size.align_to ⟨16⟩ ⟨8⟩).bytes = 16 from rfl, hEnc0, ok_bind]
    have hW0 : writeSubsliceAtIndex (List.replicate 16 (AbstractByte.Uninit : AbstractByte (Gen.Memory.Provenance M)))
        0 [x0, x1, x2, x3] = .ok ([x0, x1, x2, x3] ++ List.replicate 12 .Uninit) := rfl
    rw [show ((0 : Nat) : Int) = 0 from rfl, hW0, ok_bind, hEnc1, ok_bind]; exact rfl
  · unfold mrClosureCapTy Type.decodeM
    dsimp only [TupleHeadLayout.head_size_and_align]; rw [show (Size.align_to ⟨16⟩ ⟨8⟩).bytes = 16 from rfl]
    have hBsLen : bs.length = 16 := rfl
    rw [ite_eq_right_iff.mpr (fun hn => absurd hBsLen hn)]; dsimp only [Type.decodeFieldsM]
    have hLay0 : Type.layout u32MrTy = .ok (.Sized ⟨4⟩ ⟨4⟩) := rfl
    rw [hLay0, ok_bind, expect_size_sized, ok_bind, show ((0 : Nat) : Int) = 0 from rfl,
      show (({ bytes := 4 } : LibSpecr.Size).bytes : Int) = 4 from rfl, hSub0, ok_bind, hDec0, ok_bind]
    dsimp only []
    rw [layout_thinRawPtr, ok_bind, expect_size_sized, ok_bind,
      show ((8 : Nat) : Int) = 8 from rfl, hSub1, ok_bind, hDec1, ok_bind]; rfl
theorem encodeM_decodeM_mrClosureCapTy {M : Type} [Gen.Memory M] [MemoryOps M]
    (bits addr : Nat) (hBits : bits < 2 ^ 32) (hAddr : addr < 2 ^ 64) (prov : Option (Gen.Memory.Provenance M)) :
    let v0 : Gen.Value M := .Int (intFromBits bits u32)
    let v1 : Gen.Value M := .Ptr (ThinPointer.widen { addr := addr, provenance := prov } none)
    let bs := (leBytes bits 4).map (fun b => .Init b none) ++
      List.replicate 4 .Uninit ++ encodePtrBytesM (M := M) prov 0 (leBytes addr 8)
    Type.encodeM (M := M) mrClosureCapTy (.Tuple [v0, v1]) = .ok bs ∧
    Type.decodeM (M := M) mrClosureCapTy bs = .ok (some (.Tuple [v0, v1])) := by
  intro v0 v1 bs
  have hEnc0 : Type.encodeM (M := M) u32MrTy v0 = .ok ((leBytes bits 4).map (fun b => .Init b none)) :=
    encodeIntM_intFromBits u32 (by decide) bits hBits
  have hDec0 : Type.decodeM (M := M) u32MrTy ((leBytes bits 4).map (fun b => .Init b none)) = .ok (some v0) :=
    decodeIntM_leBytes u32 (by decide) bits hBits
  have hEnc1 : Type.encodeM (M := M) thinRawPtrTy v1 = .ok (encodePtrBytesM (M := M) prov 0 (leBytes addr 8)) := by
    simp only [thinRawPtrTy, Type.encodeM, PtrType.as_wide_pair, PtrType.meta_kind, v1,
      ThinPointer.widen]; exact encodePtrM_eq addr hAddr prov
  have hDec1 : Type.decodeM (M := M) thinRawPtrTy (encodePtrBytesM (M := M) prov 0 (leBytes addr 8)) = .ok (some v1) := by
    simp only [thinRawPtrTy, Type.decodeM, PtrType.as_wide_pair, PtrType.meta_kind, v1,
      ThinPointer.widen]; rw [decodePtrM_encodePtrBytesM addr hAddr prov, ok_bind]; rfl
  cases prov with
  | none => exact encodeM_decodeM_mrClosureCapTy_of_codec v0 v1 _ _ _ _ _ _ _ _ _ _ _ _
              hEnc0 hDec0 hEnc1 hDec1
  | some p => exact encodeM_decodeM_mrClosureCapTy_of_codec v0 v1 _ _ _ _ _ _ _ _ _ _ _ _
                hEnc0 hDec0 hEnc1 hDec1
/-- **C10.4 Coupled Closure `Assign` Statement, 16-Byte Memory Layout Store, &
`MachTB.wfLive` Lockstep (`closure_assign_coupled_lockstep_and_wfLive`)**:
Couples Trusted `evalStmt` on `dst = Rvalue.aggregate (.closure dp) ops` (for
arbitrary `decls`, `layouts`, and ANY live slot `.uninit` or `.init`) with
MiniRust `Interp.evalStatement` (`Mach`) and `evalStatementM` (`MachTB`)
storing `ValueExpr.Tuple es mrClTy` while preserving `MachTB.wfLive`, plus
`closure_cap_placeStoreM_bytes` wiring `encodeM_decodeM_mrClosureCapTy` into
`placeStoreM` so exact padded bytes `[u32_le ++ 4×.Uninit ++ ptr_bytes]` hit
`ConcurrentMemory.store`! -/
private theorem checkValueM_tuple2_of_fields {M : Type} [Gen.Memory M] [MemoryOps M]
    (o0 o1 : LibSpecr.Size) (ty0 ty1 : Gen.Type) (hl : Gen.TupleHeadLayout) (v0 v1 : Gen.Value M) (m : Option (Machine M))
    (h0 : checkValueM (M := M) v0 ty0 m = .ok ()) (h1 : checkValueM (M := M) v1 ty1 m = .ok ()) :
    checkValueM (M := M) (.Tuple [v0, v1]) (.Tuple [(o0, ty0), (o1, ty1)] hl none) m = .ok () := by
  simp only [checkValueM, ensureElseUb, List.length, beq_self_eq_true, ↓reduceIte, Bool.not_true, Bool.false_eq_true, checkFieldsM]
  rw [h0, ok_bind, h1, ok_bind]; rfl
private theorem placeStoreM_of_codec {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Machine M) (place : Gen.Place M) (val : Gen.Value M) (ty : Gen.Type)
    (bs : List (AbstractByte (Gen.Memory.Provenance M))) (cm' : Gen.ConcurrentMemory M)
    (hal : place.aligned = true) (hChk : checkValueM (M := M) val ty (some m) = .ok ()) (hEnc : Type.encodeM (M := M) ty val = .ok bs)
    (hStore : ConcurrentMemory.store m.mem place.ptr.thin_pointer bs ⟨1⟩ .None = .ok cm') :
    placeStoreM m place val ty = .ok { m with mem := cm' } := by
  unfold placeStoreM typedStoreM
  simp only [hal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hChk, hEnc, hStore, bind, Except.bind, pure, Except.pure]
theorem closure_cap_placeStoreM_bytes {M : Type} [Gen.Memory M] [MemoryOps M]
    (m : Machine M) (place : Gen.Place M) (bits addr : Nat) (hBits : bits < 2 ^ 32)
    (hAddr : addr < 2 ^ 64) (prov : Option (Gen.Memory.Provenance M)) (cm' : Gen.ConcurrentMemory M) (hal : place.aligned = true)
    (hStore : ConcurrentMemory.store m.mem place.ptr.thin_pointer
      ((leBytes bits 4).map (fun b => .Init b none) ++ List.replicate 4 .Uninit ++
        encodePtrBytesM (M := M) prov 0 (leBytes addr 8)) ⟨1⟩ .None = .ok cm') :
    let v0 : Gen.Value M := .Int (intFromBits bits u32)
    let v1 : Gen.Value M := .Ptr (ThinPointer.widen { addr := addr, provenance := prov } none)
    placeStoreM m place (.Tuple [v0, v1]) mrClosureCapTy = .ok { m with mem := cm' } := by
  intro v0 v1
  have hChk0 : checkValueM (M := M) v0 u32MrTy (some m) = .ok () := checkValueM_int_of_inBounds (intFromBits bits u32) u32 (some m)
      (inBounds_intFromBits_cf u32 (by decide) bits hBits)
  have hChk1 : checkValueM (M := M) v1 thinRawPtrTy (some m) = .ok () :=
    checkValueM_thinRawPtr_of_inBounds (M := M) (addr : Int) prov (some m) (inBounds_usize_cf addr hAddr)
  have hChk : checkValueM (M := M) (.Tuple [v0, v1]) mrClosureCapTy (some m) = .ok () := by
    rw [show mrClosureCapTy = .Tuple [(⟨0⟩, u32MrTy), (⟨8⟩, thinRawPtrTy)] ⟨⟨16⟩, ⟨8⟩, none⟩ none from rfl]
    exact checkValueM_tuple2_of_fields ⟨0⟩ ⟨8⟩ u32MrTy thinRawPtrTy ⟨⟨16⟩, ⟨8⟩, none⟩ v0 v1 (some m) hChk0 hChk1
  exact placeStoreM_of_codec m place (.Tuple [v0, v1]) mrClosureCapTy _ cm' hal hChk
    (encodeM_decodeM_mrClosureCapTy (M := M) bits addr hBits hAddr prov).1 hStore
theorem closure_assign_coupled_lockstep_and_wfLive (s : MachineState) (dstLoc : Nat) (dp : DefPath) (ops : List MirAst.Operand)
    (vals : List MirSemantics.Value) (slot : LocalSlot) (locals1 locals2 : List LocalSlot)
    (span : String) (decls : List MirAst.LocalDecl) (layouts : LayoutTable) (mBM mBM1 mBM2 mBMf : Mach) (mTB mTB1 mTB2 mTBf : MachTB)
    (dst : Gen.PlaceExpr) (es : List Gen.ValueExpr) (mrClTy : Gen.Type)
    (placeBM : Gen.Place BM) (mvalsBM : List Val) (placeTB : Gen.Place TBM) (mvalsTB : List (Gen.Value TBM))
    (hOps : evalOperands s.frame.locals ops s.memory.borrows s.memory.globals layouts
      s.memory.callerLocals decls s.memory.callStack = .ok vals locals1)
    (hProt : s.memory.activeProtectors = []) (hLive : slot ≠ .dead) (hGet : get? locals1 dstLoc = some slot)
    (hSet : set? locals1 dstLoc (.init (.aggregate 0 vals)) = some locals2)
    (hpBM : evalPlaceM mBM dst = .ok ((placeBM, mrClTy), mBM1)) (hvBM : evalValuesM mBM1 es = .ok (mvalsBM, mBM2))
    (hstBM : placeStoreM mBM2 placeBM (.Tuple mvalsBM) mrClTy = .ok mBMf) (hwfTB : MachTB.wfLive mTB)
    (hpTB : evalPlaceM mTB dst = .ok ((placeTB, mrClTy), mTB1)) (hvTB : evalValuesM mTB1 es = .ok (mvalsTB, mTB2))
    (hstTB : placeStoreM mTB2 placeTB (.Tuple mvalsTB) mrClTy = .ok mTBf) :
    evalStmt s { kind := .assign (locPlace dstLoc) (.aggregate (.closure dp) ops), span := span }
      decls layouts = MirStepNode.step (advanceStmt s locals2 { s.memory with
          borrows := invalidateConflictingBorrows s.memory.borrows dstLoc .none (length s.memory.callStack) }) ∧
    Interp.evalStatement mBM (.Assign dst (.Tuple es mrClTy)) = .ok mBMf ∧
    evalStatementM mTB (.Assign dst (.Tuple es mrClTy)) = .ok mTBf ∧ MachTB.wfLive mTBf := by
  have hBM : evalStatementM mBM (.Assign dst (.Tuple es mrClTy)) = .ok mBMf := by
    dsimp only [evalStatementM, evalValueM]; rw [hpBM, ok_bind, hvBM, ok_bind]; exact hstBM
  have hTB : evalStatementM mTB (.Assign dst (.Tuple es mrClTy)) = .ok mTBf := by
    dsimp only [evalStatementM, evalValueM]; rw [hpTB, ok_bind, hvTB, ok_bind]; exact hstTB
  refine ⟨?_, by rw [← evalStatementM_bm_eq]; exact hBM, hTB, evalStatementM_tb_wfLive hwfTB hTB⟩
  cases slot with
  | dead => exact absurd rfl hLive
  | uninit | init _ => simp only [evalStmt, evalRvalue, hOps, locPlace, hProt, hGet, hSet]
def c10ZstClosureMir : MirAst.CapturedMir := mkMirBody "ep2::c10_zst_closure" [mkDecl (closureZstMirTy "ep2::zst")] 0
    [mkBb [mkSt (.assign (locPlace 0) (.aggregate (.closure "ep2::zst") []))] .return_]
def c10CapClosureMir : MirAst.CapturedMir := mkMirBody "ep2::c10_cap_closure"
    [mkDecl (closureCapMirTy "ep2::cap"), mkDecl u32MirTy, mkDecl rawConstU32MirTy] 1
    [mkBb [mkSt (.storageLive 2), mkSt (.assign (locPlace 2) (.rawPtr .not (locPlace 1))), mkSt (.assign (locPlace 0)
             (.aggregate (.closure "ep2::cap") [.copy (locPlace 1), .copy (locPlace 2)]))] .return_]
def c10CapMrFn : Gen.Function := mkMrFn [(localName 0, mrClosureCapTy), (localName 1, u32MrTy), (localName 2, thinRawPtrTy)]
    [localName 1] (localName 0) [(bbName 0, ⟨[.Assign (.Local (localName 2)) (.AddrOf (.Local (localName 1)) (.Raw .None)),
        .Assign (.Local (localName 0)) (.Tuple [.Load (.Local (localName 1)), .Load (.Local (localName 2))] mrClosureCapTy)],
      .Return, .Regular⟩)]
def c10CapMach (local2Live : Bool := true) (local1Init : Bool := true) : Mach :=
  let a1 := mkStackAlloc 256 (if local1Init then scalarBytes u32 7 else List.replicate 4 .Uninit) 4
  let locs : List (Gen.LocalName × Ptr) := [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) }),
     (localName 1, { addr := 256, provenance := some (⟨1⟩, ()) })] ++
    (if local2Live then [(localName 2, { addr := 384, provenance := some (⟨2⟩, ()) })] else [])
  mkMrMach (mkMrProg [(fnName 0, c10CapMrFn)])
    [mkStackAlloc 128 (List.replicate 16 .Uninit) 8, a1, mkStackAlloc 384 (List.replicate 8 .Uninit) 8]
    [mkRootFrame c10CapMrFn locs (bbName 0) (if local2Live && local1Init then 0 else 1)]
def c10ZstMach : Mach :=
  let fn := mkMrFn [(localName 0, unitType)] [] (localName 0)
    [(bbName 0, ⟨[.Assign (.Local (localName 0)) (.Tuple [] unitType)], .Return, .Regular⟩)]
  mkMrMach (mkMrProg [(fnName 0, fn)]) [mkStackAlloc 128 [] 1]
    [mkRootFrame fn [(localName 0, { addr := 128, provenance := some (⟨0⟩, ()) })]]
def c10ExpectedCapBytes : List Byte := scalarBytes u32 7 ++ List.replicate 4 .Uninit ++ ptrBytes 256 (some (⟨1⟩, ()))
/-- Concrete C10 witnesses across Trusted, `Mach`, and `MachTB` (with
`MachTB.wfLive`): 0-capture ZST, 2-capture `(u32, *const u32)`, dead upvar
UB, and uninitialized upvar UB. -/
theorem c10_closure_zst_capture_and_ub_three_way_witness :
    runAVal c10ZstClosureMir 4 (initMachineState c10ZstClosureMir []) = some (.aggregate 0 []) ∧
    (∃ m1, Interp.step c10ZstMach = .ok m1 ∧ m1.mem.memory.allocations[0]?.map (·.data) = some []) ∧
    (∃ m1, Interp.stepTB (liftMachToTB c10ZstMach) = .ok m1 ∧ MachTB.wfLive m1 ∧
      m1.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) = some []) ∧
    runAVal c10CapClosureMir 6 (initMachineState c10CapClosureMir [.scalar ⟨7, 4⟩]) =
      some (.aggregate 0 [.scalar ⟨7, 4⟩, .ptr { allocId := 1, offsetBytes := 0 } 8]) ∧
    (∃ m2, Interp.steps 2 (c10CapMach true) = .ok m2 ∧ m2.mem.memory.allocations[0]?.map (·.data) = some c10ExpectedCapBytes) ∧
    (∃ m2, Interp.stepsTB 2 (liftMachToTB (c10CapMach true)) = .ok m2 ∧ MachTB.wfLive m2 ∧
      m2.mem.memory.mem.allocations[0]?.map (fun a => a.data.map projByteTB) =
        some (c10ExpectedCapBytes.map (projByteTB ∘ liftByteTB))) ∧ stepMirFn c10CapClosureMir
      { frame := { blockIdx := 0, stmtIdx := 2, locals := [.uninit, .init (.scalar ⟨7, 4⟩), .dead] },
        memory := (initMachineState c10CapClosureMir []).memory } = MirStepNode.fail .ub ∧
    Interp.step (c10CapMach false) = .error (.ub "access to a dead local") ∧
    Interp.stepTB (liftMachToTB (c10CapMach false)) = .error (.ub "access to a dead local") ∧ stepMirFn c10CapClosureMir
      { frame := { blockIdx := 0, stmtIdx := 2, locals := [.uninit, .uninit, .init (.ptr { allocId := 1, offsetBytes := 0 } 8)] },
        memory := (initMachineState c10CapClosureMir []).memory } = MirStepNode.fail .ub ∧
    Interp.step (c10CapMach true false) = .error (.ub "load at type but the data in memory violates the language invariant") ∧
    Interp.stepTB (liftMachToTB (c10CapMach true false)) =
      .error (.ub "load at type but the data in memory violates the language invariant") :=
  ⟨rfl, ok_of_map_toOption (by decide +kernel), ok_stepTB_wfLive (by decide +kernel),
   rfl, ok_of_map_toOption (by decide +kernel), ok_stepsTB_wfLive (by decide +kernel), rfl,
   eq_error_ub_of_interpUbMsg (by decide +kernel), eq_error_ub_of_interpUbMsg (by decide +kernel),
   rfl, eq_error_ub_of_interpUbMsg (by decide +kernel), eq_error_ub_of_interpUbMsg (by decide +kernel)⟩

/-! ## §11. Exhaustive Axiom, Import-Isolation, & `Classical.choice`-Free
Codec Audit -/
section AxiomAudit
open Lean Elab Command
/-- Exhaustively verify that: 1. Every declaration defined in
`MiniRustSpec.UnwindSetDiscrAndFnPtrMR` (`env.constants.map₂`) depends ONLY
on Lean's standard axioms (`propext`, `Quot.sound`, `Classical.choice`) with
zero `sorryAx` and zero `Lean.ofReduceBool` / `Lean.trustCompiler`. 2. The
module import graph satisfies `MiniRustSpec` import isolation (zero
`Anneal.*`, zero `DeinitBridge`, zero `IntrinsicBoundary` imports). 3. Core
integer/pointer/enum/closure byte-codec and `transmuteM` theorems are
strictly `Classical.choice`-free. -/
elab "#assert_unwind_setdiscr_mr_standard_axioms" : command => do
  let env ← getEnv
  for modName in env.header.moduleNames do
    if (`Anneal).isPrefixOf modName || modName == `MiniRustSpec.Correspondence.DeinitBridge ||
        modName == `MiniRustSpec.Correspondence.IntrinsicBoundary then
      throwError "import-isolation violation: {modName} must not be imported"
  let mut checked : Nat := 0
  for (c, _) in env.constants.map₂.toList do
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      if a == ``sorryAx then throwError "{c} depends on sorryAx"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} depends on non-standard axiom {a}"
    checked := checked + 1
  let choiceFreeCodecs : List Lean.Name := [``encodePtrM_eq, ``decodePtrM_encodePtrBytesM, ``transmuteM_thinRawPtr_id,
     ``evalCastOpM_transmute_thinRawPtr_id, ``evalCastOp_transmute_thinRawPtr_id,
     ``encodeIntM_intFromBits, ``decodeIntM_leBytes, ``transmuteM_int_sameSize,
     ``transmuteM_u32_to_i32, ``transmuteM_u8_to_bool, ``transmuteM_u8_to_nonZeroU8,
     ``encodeWideSliceRawPtrM_eq, ``decodeWideSliceRawPtrM_eq,
     ``transmuteM_wideSliceRawPtr_id, ``evalCastOpM_transmute_wideSliceRawPtr_id,
     ``transmuteM_binderWrapper_roundtrip, ``transmuteM_binderWrapper_u32_and_thinPtr,
     ``writeSubsliceAtIndex_byte0, ``bm_store_byte0_frame, ``tbm_store_byte0_frame,
     ``decodeM_twoVarEnumMrTy, ``encodeM_decodeM_mrClosureCapTy, ``decodeLittleEndianBytes_encode, ``abstractBytesAllProvAux_encode,
     ``encodeLittleEndianBytes_len]
  for c in choiceFreeCodecs do
    let axs ← liftCoreM <| Lean.collectAxioms c
    if axs.contains ``Classical.choice then
      throwError "byte-codec theorem {c} unexpectedly depends on Classical.choice"
  logInfo m!"MiniRustSpec.UnwindSetDiscrAndFnPtrMR: verified standard axioms for {checked} declarations (sorry_free=true, import_isolated=true, choice_free_codecs={choiceFreeCodecs.length})"
#assert_unwind_setdiscr_mr_standard_axioms
end AxiomAudit
end MiniRustSpec.UnwindSetDiscrAndFnPtrMR
