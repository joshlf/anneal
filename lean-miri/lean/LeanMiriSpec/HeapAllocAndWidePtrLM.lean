/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import Miri.Interpreter.AllocationMachine
import Miri.Interpreter.LeakCheck
import Miri.Interpreter.Cast
import Miri.Interpreter.ExecutionScalar
import Miri.Interpreter.MemoryErrors
import Miri.TreeBorrows.MachineMemoryHooks
import Miri.TreeBorrows.RetagPipeline
import LeanMiriSpec.MemoryLemmas

/-!
# Vendored Miri: heap allocation, deallocation, leak check, and `ptr::addr_eq`

This module is about the vendored, unmodified `lean-miri` only. It studies
`Miri.Memory.MemoryLifecycle.{allocatePtr, deallocatePtrWith, deallocatePtr}`
(rustc `interpret/memory.rs`), `Miri.Memory.getPtrAccess`,
`Miri.Interpreter.MemoryErrors.{access, allocation}`,
`Miri.Interpreter.AllocationMachine.{deallocate, deallocationError}`, the Tree
Borrows pipeline `Miri.TreeBorrows.RetagPipeline.retagPointerValue` and
deallocation hook `Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryDeallocation`
over `Miri.TreeBorrows.BorrowTree.{new, newChild, performBorrowAccessRange,
releaseProtector, deallocateBorrowRange}`, the leak check
`Miri.Interpreter.LeakCheck.{mayLeak, take, takeProfiled}` with
`Miri.Memory.MiriMemoryKind.mayLeak`, `Miri.ABI.Align.fromBytes`, and the
pointer operators `Miri.Interpreter.Cast.ptrToPtr`,
`Miri.Interpreter.ExecutionScalar.pointerBinary`, and
`Miri.Interpreter.ScalarOps.binary`. Nothing here mentions MiniRust or Anneal.

* **§0** Kernel evaluation of vendored code. The vendored definitions use
  source `while` loops (`Lean.Loop`, not reducible by the kernel) and a hash
  index (`KeyedArray`, whose `Std.HashMap` computes with the platform-dependent
  `USize`). `unroll_loops` derives, for a vendored definition `F`, the
  definition `T` with every `while` loop replaced by its `n`-step unrolling
  and every `KeyedArray` index query replaced by a scan of the rows, together
  with a kernel-checked proof `T.eq_src : @F = @T` (from
  `loopReal_eq_unrolled`, `KeyedArray.contains_rows`, and congruence). Every
  statement below is about the vendored `F`; `T` only tells the kernel how to
  evaluate it.
* **§1** Universal laws of the vendored definitions: the leak policy
  (`miriMemoryKind_mayLeak_iff`, `leakCheck_take_sound`), the failure
  classification of `deallocatePtrWith` and `deallocationError`
  (`deallocatePtrWith_dangling`, `deallocatePtrWith_nonzero_offset`,
  `deallocationError_ub_iff`), `Align.fromBytes` at the boundary of
  `Align::MAX` (`align_fromBytes_pow2_ok`, `align_fromBytes_too_large`), and
  `ptr::addr_eq` as fat-to-thin `ptrToPtr` followed by `pointerBinary Eq`
  (`ptrToPtr_fat_to_thin`, `addrEq_metadata_erased`, `thinEq_provenance_erased`,
  `wideEq_hetero_invalidProgram`).
* **§2** A single-threaded memory harness wired to the vendored lifecycle,
  Tree Borrows, leak check, scalar, and cast definitions.
* **§3** The 30-case observer `lmHeapWideObserve` with the exact failure of
  every case, and the threaded traces `lmHeapLifecycleTrace` and
  `lmProtectorDeallocTrace`.
* **§4** Witnesses that the conditional laws are not vacuous, the Episode 1
  capstone `ep1_lean_miri_heap_wide_capstone`, and the axiom and import audit.
-/

namespace LeanMiriSpec.HeapAllocAndWidePtrLM

open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.DataStructures Miri.Interpreter

/-! ## §0. Kernel evaluation of vendored code -/

/-- Close an equality goal with `Eq.refl`, leaving the definitional unfolding
to the kernel (no `Lean.ofReduceBool`, no compiler trust). -/
local elab "kernel_rfl" : tactic => do
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  let tgt ← Lean.MVarId.getType' mvarId
  let some (ty, lhs, _) := tgt.eq? | Lean.Meta.throwTacticEx `kernel_rfl mvarId "expected equality goal"
  let u ← Lean.Meta.getLevel ty
  mvarId.assign (Lean.mkApp2 (Lean.mkConst ``Eq.refl [u]) ty lhs)
  Lean.Elab.Tactic.replaceMainGoal []

/-- Run a source `while` body for at most `fuel` iterations, then hand the
state over to `k`. -/
def loopFuelK {β : Type} (f : Unit → β → Id (ForInStep β)) : Nat → β → (β → β) → β
  | 0, b, k => k b
  | n + 1, b, k =>
    match f () b with
    | .done v => v
    | .yield v => loopFuelK f n v k

/-- The source `while` loop of the vendored `Id.run do` blocks (`Lean.Loop`). -/
def loopReal : (β : Type) → β → (Unit → β → Id (ForInStep β)) → β :=
  fun _ init f => forIn (m := Id) Lean.Loop.mk init f

/-- Its `fuel`-step unrolling: at most `fuel` iterations are run structurally,
and only a loop that has not finished by then falls back to `loopReal`. -/
def loopUnrolled (fuel : Nat) : (β : Type) → β → (Unit → β → Id (ForInStep β)) → β :=
  fun β init f => loopFuelK f fuel init (fun b => loopReal β b f)

/-- A source `while` loop is its `fuel`-step unrolling, for every `fuel`. -/
theorem loopReal_eq_unrolled (fuel : Nat) : loopReal = loopUnrolled fuel := by
  funext β init f
  induction fuel generalizing init with
  | zero => rfl
  | succ n ih =>
    show Lean.Loop.forIn Lean.Loop.mk init f = loopFuelK f (n + 1) init (fun b => loopReal β b f)
    rw [Lean.Loop.forIn_eq_of_monadTail]
    show (match f () init with
      | .done val => val
      | .yield val => Lean.Loop.forIn Lean.Loop.mk val f) = _
    simp only [loopFuelK]
    cases f () init with
    | done v => rfl
    | yield v => exact ih v

open Lean Meta Elab Command in
/-- Resolve a constant by its user-facing name, also among private names. -/
def resolveMaybePrivate (n : Name) : CoreM Name := do
  let env ← getEnv
  if env.contains n then return n
  let found := env.constants.fold (init := (none : Option Name)) fun acc c _ =>
    if privateToUserName? c == some n then some c else acc
  match found with
  | some c => return c
  | none => throwError "unknown constant {n}"

open Lean Meta Elab Command in
/-- `unroll_loops T := F fuel n with T₁, …, Tₖ` defines `T` as the body of the
(possibly private) definition `F` in which
* every source `while` loop (`forIn Lean.Loop.mk init f` in `Id`) is replaced
  by its `n`-step unrolling `loopUnrolled n _ init f`, and
* every occurrence of the source `Sᵢ` of the twin `Tᵢ` is replaced by `Tᵢ`,
  where `Tᵢ.eq_src : Sᵢ = @Tᵢ` and `Sᵢ` is either a constant or a
  specialization `fun x₁ … xₘ => C a₁ … aₚ` of a constant `C`,
and proves `T.eq_src : @F = @T` from `loopReal_eq_unrolled n` and the
`Tᵢ.eq_src` by congruence. Nothing is assumed: `T.eq_src` is checked by the
kernel like any other theorem. -/
elab "unroll_loops " newId:ident " := " srcId:ident " fuel " n:num deps:((" with " ident,*)?) : command => do
  liftTermElabM do
    let src ← (try resolveGlobalConstNoOverload srcId catch _ => resolveMaybePrivate srcId.getId)
    let .defnInfo dinfo ← getConstInfo src | throwError "{src} is not a definition"
    let lvls := dinfo.levelParams
    let newName := (← getCurrNamespace) ++ newId.getId
    let depIds : Array Syntax := match deps.raw with
      | .node _ _ args => if args.size == 0 then #[] else (args[1]!.getSepArgs)
      | _ => #[]
    -- (twin, source term, head constant, number of binders, pattern arguments)
    let mut depInfo : Array (Name × Expr × Name × Nat × Array Expr) := #[]
    for d in depIds do
      let t ← resolveGlobalConstNoOverload d
      let thm ← getConstInfo (t ++ `eq_src)
      let some (_, lhs, _) := thm.type.eq? | throwError "{t}.eq_src is not an equation"
      let rec strip (e : Expr) (k : Nat) : Expr × Nat :=
        match e with
        | .lam _ _ b _ => strip b (k + 1)
        | e => (e, k)
      let (body, nb) := strip lhs 0
      let .const head _ := body.getAppFn | throwError "{t}.eq_src: unsupported source {lhs}"
      depInfo := depInfo.push (t, lhs, head, nb, body.getAppArgs)
    let loopTy ← inferType (mkConst ``LeanMiriSpec.HeapAllocAndWidePtrLM.loopReal)
    let depTys ← depInfo.mapM fun (_, lhs, _, _, _) => inferType lhs
    let fuel := mkNatLit n.getNat
    withLocalDeclD `L loopTy fun L => do
    let rec withDeps (i : Nat) (gs : Array Expr) (k : Array Expr → MetaM Unit) : MetaM Unit :=
      if h : i < depTys.size then
        withLocalDeclD ((`g).appendIndexAfter i) depTys[i] fun g => withDeps (i + 1) (gs.push g) k
      else k gs
    withDeps 0 #[] fun gs => do
      let body ← Core.transform dinfo.value (post := fun e => do
        if e.isAppOfArity ``ForIn.forIn 8 && (e.getArg! 1).isConstOf ``Lean.Loop &&
            (e.getArg! 0).isConstOf ``Id then
          return .done (mkApp3 L (e.getArg! 4) (e.getArg! 6) (e.getArg! 7))
        let fn := e.getAppFn
        if let .const c _ := fn then
          let args := e.getAppArgs
          for i in [:depInfo.size] do
            let (_, _, head, nb, pat) := depInfo[i]!
            if c == head && args.size ≥ pat.size then
              let mut binds : Array (Option Expr) := Array.replicate nb none
              let mut ok := true
              for j in [:pat.size] do
                match pat[j]! with
                | .bvar k =>
                  if k < nb then binds := binds.set! (nb - 1 - k) (some args[j]!) else ok := false
                | p => if p != args[j]! then ok := false
              if ok && binds.all Option.isSome then
                let g := mkAppN gs[i]! (binds.map Option.get!)
                return .done (mkAppN g (args.extract pat.size args.size))
        return .continue)
      let ctx ← mkLambdaFVars (#[L] ++ gs) body
      let twinVal := mkAppN ctx
        (#[mkApp (mkConst ``LeanMiriSpec.HeapAllocAndWidePtrLM.loopUnrolled) fuel] ++ depInfo.map fun (t, _, _, _, _) => mkConst t)
      let twinVal ← Core.betaReduce twinVal.headBeta
      addDecl <| .defnDecl {
        name := newName, levelParams := lvls, type := dinfo.type, value := twinVal,
        hints := .abbrev, safety := .safe }
      let mut proof ← mkCongrArg ctx (mkApp (mkConst ``LeanMiriSpec.HeapAllocAndWidePtrLM.loopReal_eq_unrolled) fuel)
      for (t, _, _, _, _) in depInfo do
        proof ← mkCongr proof (mkConst (t ++ `eq_src))
      let us := lvls.map mkLevelParam
      let stmt ← mkEq (mkConst src us) (mkConst newName us)
      addDecl <| .thmDecl {
        name := newName ++ `eq_src, levelParams := lvls, type := stmt, value := proof }


/-! ### `KeyedArray` index queries as row scans -/

/-- `KeyedArray.contains` at `UInt64` keys as a scan of the rows. -/
def containsU64 : (V : Type) → (keyFn : V → UInt64) → KeyedArray UInt64 V keyFn → UInt64 → Bool :=
  fun _ keyFn table key => (table.toArray.map keyFn).contains key

/-- The certified hash index contains precisely the keys of the rows
(`KeyedArray.contains_rows`). -/
theorem containsU64.eq_src :
    (fun (V : Type) (keyFn : V → UInt64) => @KeyedArray.contains UInt64 V _ _ keyFn) =
      containsU64 := by
  funext V keyFn table key
  exact KeyedArray.contains_rows table key

/-- A key that the index does not contain has no row. -/
theorem keyedArray_find?_eq_none_of_contains_false {V : Type} {keyFn : V → UInt64}
    (table : KeyedArray UInt64 V keyFn) (key : UInt64) (h : table.contains key = false) :
    table.find? key = none := by
  cases hf : table.find? key with
  | none => rfl
  | some row =>
    exfalso
    unfold KeyedArray.contains at h
    unfold KeyedArray.find? at hf
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_none_of_contains_eq_false h] at hf
    cases hf

/-- `KeyedArray.find?` at `UInt64` keys, guarded by a scan of the rows: a key
that no row has is not found, without consulting the hash index. -/
def findU64 : (V : Type) → (keyFn : V → UInt64) → KeyedArray UInt64 V keyFn → UInt64 → Option V :=
  fun _ keyFn table key =>
    if (table.toArray.map keyFn).contains key then table.find? key else none

/-- The guard changes nothing. -/
theorem findU64.eq_src :
    (fun (V : Type) (keyFn : V → UInt64) => @KeyedArray.find? UInt64 V _ _ keyFn) = findU64 := by
  funext V keyFn table key
  unfold findU64
  rw [← KeyedArray.contains_rows table key]
  cases h : table.contains key with
  | true => rfl
  | false => exact keyedArray_find?_eq_none_of_contains_false table key h

/-- A key that the index does not contain satisfies no row predicate. -/
theorem keyedArray_any?_eq_false_of_contains_false {V : Type} {keyFn : V → UInt64}
    (table : KeyedArray UInt64 V keyFn) (key : UInt64) (p : V → Bool)
    (h : table.contains key = false) :
    table.any? key p = false := by
  unfold KeyedArray.contains at h
  unfold KeyedArray.any?
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_none_of_contains_eq_false h]
  rfl

/-- `KeyedArray.any?` at `UInt64` keys, guarded by a scan of the rows. -/
def anyU64 : (V : Type) → (keyFn : V → UInt64) → KeyedArray UInt64 V keyFn → UInt64 →
    (V → Bool) → Bool :=
  fun _ keyFn table key p =>
    if (table.toArray.map keyFn).contains key then table.any? key p else false

/-- The guard changes nothing. -/
theorem anyU64.eq_src :
    (fun (V : Type) (keyFn : V → UInt64) => @KeyedArray.any? UInt64 V _ _ keyFn) = anyU64 := by
  funext V keyFn table key p
  unfold anyU64
  rw [← KeyedArray.contains_rows table key]
  cases h : table.contains key with
  | true => rfl
  | false => exact keyedArray_any?_eq_false_of_contains_false table key p h

/-! ### Evaluable twins of the vendored definitions

Each line derives a twin `T` and proves `T.eq_src : @F = @T`. The fuel is the
number of iterations a `while` loop of `F` is unrolled; a loop that needs more
leaves the kernel stuck (and the proof that uses it fails), it never yields a
wrong value. -/

unroll_loops containsIdU := Miri.Memory.MemoryState.containsId fuel 0 with containsU64
unroll_loops reserveAllocIdU := Miri.Memory.MemoryState.reserveAllocId fuel 0 with containsIdU
unroll_loops insertAllocationU := Miri.Memory.MemoryLifecycle.insertAllocation fuel 0
  with reserveAllocIdU
unroll_loops allocatePtrU := Miri.Memory.MemoryLifecycle.allocatePtr fuel 0 with insertAllocationU
unroll_loops findGlobalU := Miri.Memory.MemoryState.findGlobal? fuel 0 with findU64
unroll_loops hasFunctionPointerU := Miri.Memory.MemoryState.hasFunctionPointer fuel 0
  with containsU64, anyU64
unroll_loops getAllocInfoU := Miri.Memory.MemoryState.getAllocInfo fuel 0
  with hasFunctionPointerU, containsU64, findGlobalU
unroll_loops deallocatePtrWithU := Miri.Memory.MemoryLifecycle.deallocatePtrWith fuel 0
  with findGlobalU
unroll_loops findOffsetU := Miri.DataStructures.DedupRangeMap.findOffset fuel 70
unroll_loops iterMutWithCloneU := Miri.DataStructures.DedupRangeMap.iterMutWithClone fuel 40
  with findOffsetU
unroll_loops iterMutU := Miri.DataStructures.DedupRangeMap.iterMut fuel 0 with iterMutWithCloneU
unroll_loops modifyRangeWithCloneU := Miri.DataStructures.DedupRangeMap.modifyRangeWithClone fuel 0
  with iterMutWithCloneU
unroll_loops modifyRangeU := Miri.DataStructures.DedupRangeMap.modifyRange fuel 0
  with modifyRangeWithCloneU
unroll_loops updateSifaAfterRetagU := Miri.TreeBorrows.BorrowTree.updateSifaAfterRetag fuel 40
unroll_loops newChildU := Miri.TreeBorrows.BorrowTree.newChild fuel 0
  with updateSifaAfterRetagU, modifyRangeU
unroll_loops minExposedChildU := Miri.TreeBorrows.BorrowTree.minExposedChild fuel 40
unroll_loops performTreeAccessAtU := Miri.TreeBorrows.BorrowTree.performTreeAccessAt fuel 0
  with minExposedChildU
unroll_loops performBorrowAccessRangeU := Miri.TreeBorrows.BorrowTree.performBorrowAccessRange fuel 0
  with iterMutU, performTreeAccessAtU
unroll_loops deallocateBorrowRangeU := Miri.TreeBorrows.BorrowTree.deallocateBorrowRange fuel 0
  with performBorrowAccessRangeU, iterMutU
unroll_loops releaseProtectorU := Miri.TreeBorrows.BorrowTree.releaseProtector fuel 0
  with performTreeAccessAtU
unroll_loops commitTreeAccessU := Miri.TreeBorrows.MachineMemoryHooks.commitTreeAccess fuel 0
  with performBorrowAccessRangeU
unroll_loops beforeMemoryReadU := Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryRead fuel 0
  with commitTreeAccessU
unroll_loops beforeMemoryWriteU := Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryWrite fuel 0
  with commitTreeAccessU
unroll_loops beforeMemoryDeallocationU :=
  Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryDeallocation fuel 0 with deallocateBorrowRangeU
unroll_loops buildInsidePermissionsU := Miri.TreeBorrows.RetagPipeline.buildInsidePermissions fuel 0
  with modifyRangeU
unroll_loops accessTreeForReborrowU := Miri.TreeBorrows.RetagPipeline.accessTreeForReborrow fuel 0
  with performBorrowAccessRangeU, newChildU
unroll_loops runReborrowU := Miri.TreeBorrows.RetagPipeline.runReborrow fuel 0
  with getAllocInfoU, buildInsidePermissionsU, accessTreeForReborrowU
unroll_loops retagPointerValueU := Miri.TreeBorrows.RetagPipeline.retagPointerValue fuel 0
  with runReborrowU

/-! ## §2. A single-threaded memory harness over the vendored definitions

The harness is the part of Miri's machine that the heap shims and the pointer
operators need: a `MemoryState` whose allocations carry Tree Borrows trees,
the borrow tracker's protected tags, and the configuration bit `treeBorrows`
(Miri's `-Zmiri-tree-borrows` against no borrow tracking). Every state change
goes through a vendored definition; the harness supplies only the machine
hooks that the vendored interface leaves to the machine (addresses, root
tags, and trivial data-race and synchronization callbacks). -/

/-- The harness memory: Miri provenance, Tree Borrows trees, Miri memory kinds. -/
abbrev LmMem := MemoryState Provenance BorrowTree MiriMemoryKind

/-- A typed harness failure: the exact vendored error value that stopped an
operation. -/
inductive LmFailure where
  /-- `check_alloc_request`: alignment is zero, not a power of two, or exceeds `Align::MAX`. -/
  | allocAlign (error : AlignError)
  /-- `check_alloc_request`: the size exceeds `isize::MAX`. -/
  | allocTooLarge (size : Nat)
  /-- `Memory::allocate_ptr` failed. -/
  | allocLifecycle (error : MemoryLifecycleError)
  /-- The `dealloc` shim's alignment check failed. -/
  | deallocAlign (error : AlignError)
  /-- `Memory::deallocate_ptr` failed (classified by `AllocationMachine.deallocationError`). -/
  | dealloc (error : MemoryLifecycleError)
  /-- Tree Borrows rejected the deallocation. -/
  | treeDealloc (status : BorrowTree.BorrowTreeDeallocStatus)
  /-- Tree Borrows rejected a read or write access. -/
  | treeAccess (status : BorrowTree.BorrowTreeAccessStatus)
  /-- Vendored `RetagPipeline.retagPointerValue` failed. -/
  | retag (error : RetagPipeline.Error)
  /-- Releasing a protector failed. -/
  | protectorRelease (status : BorrowTree.ProtectorReleaseStatus)
  /-- Vendored `Miri.Memory.getPtrAccess` failed (classified by `MemoryErrors.access`). -/
  | access (error : AccessError)
  /-- `Allocation::read_scalar` or `write_scalar` failed (classified by `MemoryErrors.allocation`). -/
  | allocation (error : AllocError)
  /-- A scalar conversion failed (classified by `ScalarOps.scalarError`). -/
  | scalar (error : ScalarError)
  /-- A cast or scalar operator failed. -/
  | step (error : StepError)
  /-- `take_leaked_allocations` reported these allocations. -/
  | leak (allocIds : List AllocId)
  /-- The harness itself was used outside its domain. -/
  | harness (message : String)
  deriving DecidableEq

/-- The borrow tracker state threaded through the lifecycle hooks, directly
hosting vendored `GlobalState` and `FrameState`. -/
structure LmCtx where
  /-- Whether Tree Borrows is enabled. -/
  treeBorrows : Bool
  /-- Vendored Tree Borrows global tag supply & protected-tag table. -/
  global : GlobalState := GlobalState.new
  /-- Vendored active call frame's protected `(AllocId, BorTag)` records. -/
  frame : FrameState := {}
  /-- The typed failure of a machine hook, as `AllocationMachine.deallocate`
  keeps one in `pendingError`. -/
  pending : Option LmFailure := none

/-- The harness state. -/
structure LmState where
  /-- The memory. -/
  mem : LmMem
  /-- The borrow tracker state. -/
  ctx : LmCtx

/-- The initial state: empty memory and fresh vendored `GlobalState`. -/
def lmInit (tb : Bool) : LmState := { mem := MemoryState.empty, ctx := { treeBorrows := tb } }

/-- Little-endian, 64-bit. -/
def lmLayout : TargetDataLayout := ⟨.little, .w64⟩

/-- 64-bit pointer arithmetic context for vendored `Miri.Memory.getPtrAccess`. -/
def lmPtrArith : PointerArithmetic := ⟨Size.ofBytes 8⟩

/-- The base address of an allocation: `id * 2^32`, so every allocation is
aligned to every supported alignment and allocations of less than `2^32`
bytes do not overlap. -/
def lmBaseAddr (id : AllocId) : UInt64 := id.value * 4294967296

/-- The root tag assigned to the first allocation by `GlobalState.rootPointerTag`. -/
def lmRootTag (id : AllocId) : BorTag := ⟨id.value, id.nonzero⟩

/-- `isize::MAX` on a 64-bit target. -/
def lmIsizeMax : Nat := 9223372036854775807

/-- Checked Rust allocator alignment guard (`Layout::from_size_align` / Miri
`check_alloc_request`): rejects `align = 0` (which `rustc_abi::Align::from_bytes`
accepts as `Align::ONE` for internal ABI use) and `align ≥ 2^64` before
delegating to vendored `Align.fromBytes`. -/
def lmCheckAlign (align : Nat) : Except AlignError Align :=
  if align = 0 then .error (.notPowerOfTwo 0)
  else if align ≥ 2 ^ 64 then .error (.tooLarge (UInt64.ofNat (2 ^ 64 - 1)))
  else Align.fromBytes (UInt64.ofNat align)

/-- The machine hooks of `MachineMemoryHooks`: no data-race detector, no
synchronization objects, no diagnostics. -/
def lmMachineHooks (protectedTags : ProtectedTags) :
    MachineMemoryHooks.Hooks Unit Unit MiriMemoryKind :=
  { protectedTags := protectedTags
    emitDiagnostic := fun s _ _ => s
    dataRaceRead := fun s _ _ _ => ⟨s, .ok ()⟩
    dataRaceWrite := fun s _ _ _ => ⟨s, .ok ()⟩
    dataRaceDeallocate := fun s _ _ _ _ => ⟨s, .ok ()⟩
    syncOnAccess := fun s _ _ => ⟨s, .ok ()⟩
    deleteOnWrite := fun _ => false
    recordDeallocatedSpan := fun s _ => s
    freeAllocId := fun s _ _ _ _ => s }

/-- The `MachineMemoryHooks` context: no synchronization objects. -/
def lmHookContext : MachineMemoryHooks.Context Unit Unit :=
  { state := (), syncObjects := .empty }

/-- `init_local_allocation`: allocate the allocation's root tag from vendored
`GlobalState.rootPointerTag` and initialize a fresh `BorrowTree.new`. -/
def lmInitExtra (memory : LmMem) (ctx : LmCtx) (id : AllocId) (_kind : MemoryKind MiriMemoryKind)
    (size : Size) (_align : Align) :
    MemoryStateHookResult Provenance BorrowTree MiriMemoryKind LmCtx BorrowTree :=
  match ctx.global.rootPointerTag id with
  | .ok (global', rootTag) =>
    ⟨memory, { ctx with global := global' }, .ok (BorrowTree.new rootTag size)⟩
  | .error e => ⟨memory, ctx, .error (reprStr e)⟩

/-- `adjust_alloc_root_pointer`: the allocation's base address paired with its
stable root tag from `GlobalState.rootPointerTag`. -/
def lmAdjustRoot (memory : LmMem) (ctx : LmCtx) (id : AllocId)
    (_kind : MemoryKind MiriMemoryKind) :
    MemoryStateHookResult Provenance BorrowTree MiriMemoryKind LmCtx (Pointer Provenance) :=
  match ctx.global.rootPointerTag id with
  | .ok (global', rootTag) =>
    ⟨memory, { ctx with global := global' },
      .ok ⟨Size.ofBytes (lmBaseAddr id), .concrete id rootTag⟩⟩
  | .error e => ⟨memory, ctx, .error (reprStr e)⟩

/-- `Memory::allocate_ptr` with the harness hooks: zeroed backing storage,
uninitialized contents, `GLOBAL_KIND = MiriMemoryKind::Global`, and objects of
at most `isize::MAX` bytes. -/
def lmAllocatePtr (st : LmState) (size : Size) (align : Align) (kind : MemoryKind MiriMemoryKind)
    (globalKind : Option (MemoryKind MiriMemoryKind)) :
    MemoryLifecycleResult Provenance BorrowTree MiriMemoryKind LmCtx (Pointer Provenance) :=
  MemoryLifecycle.allocatePtr st.mem st.ctx (fun _ ctx => ctx) size align kind .Uninit
    (Size.ofBytes (UInt64.ofNat lmIsizeMax)) globalKind
    (fun size _ => some (Array.replicate size.bytes.toNat 0)) lmInitExtra lmAdjustRoot

/-- An allocation of `kind`: checks alignment (`lmCheckAlign`) and `size ≤ isize::MAX`
before calling `Memory::allocate_ptr`. A request for the global kind models the
state `get_alloc_raw_mut` leaves when it materializes a mutable static (a live
allocation of `MemoryKind::Machine(GLOBAL_KIND)`), so only then is `GLOBAL_KIND`
not passed to the dynamic-allocation check. -/
def lmAllocateKind (st : LmState) (size align : Nat) (kind : MemoryKind MiriMemoryKind) :
    Except LmFailure (Pointer (Option Provenance) × LmState) :=
  match lmCheckAlign align with
  | .error e => .error (.allocAlign e)
  | .ok al =>
    if size ≤ lmIsizeMax then
      let globalKind : Option (MemoryKind MiriMemoryKind) :=
        if kind = .machine .global then none else some (.machine .global)
      let r := lmAllocatePtr st (Size.ofBytes (UInt64.ofNat size)) al kind globalKind
      match r.outcome with
      | .ok ptr => .ok (ptr.withOptionalProvenance, { mem := r.memory, ctx := r.hooks })
      | .error e => .error (.allocLifecycle e)
    else .error (.allocTooLarge size)

/-- The Rust heap allocation shim (`__rust_alloc`): `check_alloc_request`
(`lmCheckAlign` and `size ≤ isize::MAX`, both checked before any storage is
created), then `Memory::allocate_ptr` with `MiriMemoryKind::Rust`. -/
def lmAllocate (st : LmState) (size align : Nat) :
    Except LmFailure (Pointer (Option Provenance) × LmState) :=
  lmAllocateKind st size align (.machine .rust)

/-- `ptr_get_alloc_id`: a pointer with concrete provenance resolves to its
allocation, its non-underflowing offset from the allocation's base address,
and its tag; a pointer without provenance or below its base address is dangling. -/
def lmResolve (memory : LmMem) (ctx : LmCtx) (ptr : Pointer (Option Provenance)) (_size : Int) :
    PointerResolutionResult Provenance BorrowTree MiriMemoryKind LmCtx ProvenanceExtra :=
  match ptr.provenance with
  | some (.concrete id tag) =>
    if ptr.offset.bytes < lmBaseAddr id then
      ⟨memory, ctx, .error ptr.offset.bytes⟩
    else
      ⟨memory, ctx, .ok (id, Size.ofBytes (ptr.offset.bytes - lmBaseAddr id), .concrete tag)⟩
  | some .wildcard => ⟨memory, ctx, .error ptr.offset.bytes⟩
  | none => ⟨memory, ctx, .error ptr.offset.bytes⟩

/-- Pure `PointerResolver` adapter of `lmResolve` for vendored `Miri.Memory.getPtrAccess`. -/
def lmResolvePure : PointerResolver Provenance ProvenanceExtra := fun ptr _ =>
  match ptr.provenance with
  | some (.concrete id tag) =>
    if ptr.offset.bytes < lmBaseAddr id then .error ptr.offset.bytes
    else .ok ⟨id, Size.ofBytes (ptr.offset.bytes - lmBaseAddr id), .concrete tag⟩
  | some .wildcard => .error ptr.offset.bytes
  | none => .error ptr.offset.bytes

/-- `before_memory_deallocation`: with Tree Borrows, the vendored
`MachineMemoryHooks.beforeMemoryDeallocation`; a rejection is recorded with
the exact `BorrowTreeDeallocStatus` of `deallocateBorrowRange`. Without a
borrow tracker there is nothing to check. -/
def lmBeforeDeallocation (memory : LmMem) (ctx : LmCtx)
    (allocation : Allocation Provenance BorrowTree) (pointer : Pointer (Option Provenance))
    (allocId : AllocId) (provenance : ProvenanceExtra) (size : Size) (align : Align)
    (kind : MemoryKind MiriMemoryKind) :
    MemoryStateHookResult Provenance BorrowTree MiriMemoryKind LmCtx Unit :=
  if ctx.treeBorrows then
    let r := MachineMemoryHooks.beforeMemoryDeallocation lmHookContext
      (lmMachineHooks ctx.global.protectedTags) allocation pointer allocId provenance size align kind
    match r.outcome with
    | .ok () => ⟨memory, ctx, .ok ()⟩
    | .error message =>
      ⟨memory,
        { ctx with pending := some (.treeDealloc
            (allocation.extra.deallocateBorrowRange provenance Size.ZERO size
              ctx.global.protectedTags).status) },
        .error message⟩
  else
    ⟨memory, ctx, .ok ()⟩

/-- The deallocation hooks. -/
def lmDeallocHooks :
    MemoryDeallocationHooks Provenance BorrowTree MiriMemoryKind LmCtx ProvenanceExtra :=
  { synchronizeMemory := fun _ ctx => ctx
    resolvePointer := lmResolve
    beforeDeallocation := lmBeforeDeallocation }

/-- The Rust heap deallocation shim (`__rust_dealloc`): `lmCheckAlign`,
then `Memory::deallocate_ptr` with the claimed layout and
`MiriMemoryKind::Rust`. A typed machine-hook failure takes precedence over the
lifecycle's `hookFailure`, as in `AllocationMachine.deallocate`. -/
def lmDeallocate (st : LmState) (ptr : Pointer (Option Provenance)) (size align : Nat) :
    Except LmFailure LmState :=
  match lmCheckAlign align with
  | .error e => .error (.deallocAlign e)
  | .ok al =>
    let r := MemoryLifecycle.deallocatePtrWith st.mem st.ctx ptr
      (some (Size.ofBytes (UInt64.ofNat size), al)) (.machine .rust) lmDeallocHooks
    match r.outcome with
    | .ok () => .ok { mem := r.memory, ctx := r.hooks }
    | .error e => .error (r.hooks.pending.getD (.dealloc e))

/-- The target of an access of `size` bytes via vendored `Miri.Memory.getPtrAccess`
and `MemoryState.getAllocInfo`: validates provenance, liveness (reporting
`AccessError.allocationLookup (.deadAllocation id)` on UAF), and bounds. -/
def lmAccessTarget (st : LmState) (ptr : Pointer (Option Provenance)) (size : UInt64) :
    Except LmFailure (AllocId × Size × ProvenanceExtra × Allocation Provenance BorrowTree) :=
  match getPtrAccess lmPtrArith ptr (Size.ofBytes size) .memoryAccess
      lmResolvePure st.mem.getAllocInfo with
  | .error e => .error (.access e)
  | .ok none => .error (.harness "zero-sized access in scalar load/store")
  | .ok (some (_, _, (id, offset, provenance))) =>
    match st.mem.live.find? (fun entry => entry.1 == id) with
    | none => .error (.access (.allocationLookup (.unavailable id)))
    | some (_, entry) => .ok (id, offset, provenance, entry.allocation)

/-- `before_memory_read` / `before_memory_write`: with Tree Borrows, the
vendored `MachineMemoryHooks` access hook, which updates the allocation's
tree; a rejection is reported with the exact `BorrowTreeAccessStatus`. -/
def lmTreeAccess (st : LmState) (write : Bool) (allocation : Allocation Provenance BorrowTree)
    (ptr : Pointer (Option Provenance)) (id : AllocId) (provenance : ProvenanceExtra)
    (range : AllocRange) : Except LmFailure LmState :=
  if st.ctx.treeBorrows then
    let r :=
      if write then
        MachineMemoryHooks.beforeMemoryWrite st.mem lmHookContext
          (lmMachineHooks st.ctx.global.protectedTags) allocation ptr id provenance range
      else
        MachineMemoryHooks.beforeMemoryRead st.mem lmHookContext
          (lmMachineHooks st.ctx.global.protectedTags) allocation ptr id provenance range
    match r.outcome with
    | .ok () => .ok { st with mem := r.memory }
    | .error _ =>
      .error (.treeAccess
        (allocation.extra.performBorrowAccessRange provenance range.start range.size
          (if write then .Write else .Read) st.ctx.global.protectedTags
          .VisitChildrenOfAccessed).status)
  else
    .ok st

/-- Store the unsigned integer `bits` in `size` bytes through `ptr`: vendored
`getPtrAccess`, the access hook, then `Allocation::write_scalar`. -/
def lmStore (st : LmState) (ptr : Pointer (Option Provenance)) (size : UInt64) (bits : Nat) :
    Except LmFailure LmState := do
  let (id, offset, provenance, allocation) ← lmAccessTarget st ptr size
  let range : AllocRange := ⟨offset, Size.ofBytes size⟩
  let st ← lmTreeAccess st true allocation ptr id provenance range
  match st.mem.live.find? (fun entry => entry.1 == id) with
  | none => .error (.access (.allocationLookup (.unavailable id)))
  | some (_, entry) =>
    match Miri.Memory.Scalar.fromUInt (Prov := Provenance) (BitVec.ofNat 128 bits)
        (Size.ofBytes size) with
    | .error e => .error (.scalar e)
    | .ok value =>
      match Allocation.writeScalar lmLayout range value entry.allocation with
      | .error e _ => .error (.allocation e)
      | .ok () written =>
        match st.mem.setLiveAllocation id written with
        | .error e => .error (.access (.allocationLookup e))
        | .ok mem => .ok { st with mem := mem }

/-- Load an unsigned integer of `size` bytes through `ptr`: vendored
`getPtrAccess`, the access hook, then `Allocation::read_scalar`. -/
def lmLoad (st : LmState) (ptr : Pointer (Option Provenance)) (size : UInt64) :
    Except LmFailure (Nat × LmState) := do
  let (id, offset, provenance, allocation) ← lmAccessTarget st ptr size
  let range : AllocRange := ⟨offset, Size.ofBytes size⟩
  let st ← lmTreeAccess st false allocation ptr id provenance range
  match allocation.readScalar lmLayout range false with
  | .error e => .error (.allocation e)
  | .ok value =>
    match value.toBits (Size.ofBytes size) with
    | .error e => .error (.scalar e)
    | .ok bits => .ok (bits.toNat, st)

/-- `take_leaked_allocations` without static roots: a leak is a failure. -/
def lmLeakCheck (st : LmState) : Except LmFailure Unit :=
  match LeakCheck.take st.mem #[] with
  | .error e => .error (.step e)
  | .ok (_, leaked) =>
    if leaked.isEmpty then .ok () else .error (.leak (leaked.toList.map (·.1)))

/-- Tree Borrows retag wired directly through vendored
`Miri.TreeBorrows.RetagPipeline.retagPointerValue` (and `RetagPolicy.create`
with `implicitWrites := true`, matching MiniRust's `TreeBorrowsParams ⟨true⟩`):
without a borrow tracker the pointer is unchanged; with Tree Borrows, vendored
`RetagPipeline` allocates the child tag from `GlobalState`, registers any
`WeakProtector` (`Box`) or `StrongProtector` (`&`/`&mut`) in `GlobalState` and
`FrameState`, executes the parent tree access, and inserts the child node. -/
def lmRetag (st : LmState) (ptr : Pointer (Option Provenance))
    (typeShape : RetagPipeline.RetagTypeShape) (typeFacts : RetagPolicy.TypeFacts)
    (refKind : RetagPolicy.ReferenceKind) (mode : RetagPolicy.RetagMode)
    (pointeeIsFreeze : Bool) :
    Except LmFailure (Pointer (Option Provenance) × LmState) :=
  if st.ctx.treeBorrows then
    match lmResolvePure ptr 0 with
    | .error addr => .error (.access (.danglingIntegerPointer addr 0 .memoryAccess))
    | .ok resolved =>
      match st.mem.live.find? (fun entry => entry.1 == resolved.allocId) with
      | none => .error (.access (.allocationLookup (.deadAllocation resolved.allocId)))
      | some (_, entry) =>
        let req : RetagPipeline.Request := {
          typeShape := typeShape
          typeFacts := typeFacts
          referenceKind := refKind
          mode := mode
          config := { implicitWrites := true, rustcNoWritable := false }
          layoutSize := entry.allocation.byteSize
          originalProvenance := ptr.provenance
          pointeeIsFreeze := pointeeIsFreeze
          preciseInteriorMut := false
          hooks := {
            allocationResolution := some ⟨resolved.allocId, resolved.offset, resolved.extra⟩
          }
        }
        let mstate : RetagPipeline.MachineState MiriMemoryKind :=
          ⟨st.mem, st.ctx.global, st.ctx.frame⟩
        let res := RetagPipeline.retagPointerValue mstate req
        match res.outcome with
        | .error e => .error (.retag e)
        | .ok prov =>
          .ok (⟨ptr.offset, prov⟩,
            { mem := res.state.memory
              ctx := { st.ctx with global := res.state.global, frame := res.state.frame } })
  else
    .ok (ptr, st)

/-- Release one protector `(id, tag)` in memory via vendored `BorrowTree.releaseProtector`. -/
def lmReleaseOne (protectedTags : ProtectedTags) (mem : LmMem) (entryPair : AllocId × BorTag) :
    Except LmFailure LmMem :=
  let (id, tag) := entryPair
  match mem.live.find? (fun entry => entry.1 == id) with
  | none => .ok mem
  | some (_, entry) =>
    let r := entry.allocation.extra.releaseProtector tag protectedTags
    if r.status = .Released then
      match mem.setLiveAllocation id (entry.allocation.setExtra r.tree) with
      | .error e => .error (.access (.allocationLookup e))
      | .ok mem' => .ok mem'
    else
      .error (.protectorRelease r.status)

/-- End the active call frame: for every protected `(allocId, tag)` recorded in
`FrameState`, invoke vendored `BorrowTree.releaseProtector` (when the allocation
is live), then invoke vendored `GlobalState.endCall` to remove the frame's
protectors from `GlobalState.protectedTags`. Without Tree Borrows, a no-op. -/
def lmEndCall (st : LmState) : Except LmFailure LmState :=
  if st.ctx.treeBorrows then
    match st.ctx.frame.protectedTags.toList.foldlM
        (lmReleaseOne st.ctx.global.protectedTags) st.mem with
    | .error e => .error e
    | .ok mem' =>
      .ok { mem := mem'
            ctx := { st.ctx with
              global := st.ctx.global.endCall st.ctx.frame
              frame := {} } }
  else
    .ok st

/-! ### Pointer operators: `ptrToPtr`, `pointerBinary`, `ScalarOps.binary` -/

/-- `*const ()`. -/
def tyThin : Miri.MIR.TyId := 1
/-- `*const [u8]`. -/
def tySlice : Miri.MIR.TyId := 2
/-- `*const dyn Trait`. -/
def tyDyn : Miri.MIR.TyId := 3
/-- `bool`. -/
def tyBool : Miri.MIR.TyId := 4
/-- `usize`. -/
def tyUsize : Miri.MIR.TyId := 5
/-- `()`. -/
def tyUnit : Miri.MIR.TyId := 6
/-- `[u8]`. -/
def tySliceU8 : Miri.MIR.TyId := 7
/-- `dyn Trait`. -/
def tyDynTrait : Miri.MIR.TyId := 8

/-- The ABI scalar of a pointer. -/
def abiPtr : Miri.ABI.Scalar :=
  .Initialized (value := .Pointer AddressSpace.ZERO)
    (validRange := ⟨0, BitVec.ofNat 128 0xFFFFFFFFFFFFFFFF⟩)

/-- The ABI scalar of `usize`. -/
def abiUsize : Miri.ABI.Scalar :=
  .Initialized (value := .Int .I64 false) (validRange := ⟨0, BitVec.ofNat 128 0xFFFFFFFFFFFFFFFF⟩)

/-- The ABI scalar of `bool`. -/
def abiBool : Miri.ABI.Scalar :=
  .Initialized (value := .Int .I8 false) (validRange := ⟨0, BitVec.ofNat 128 1⟩)

/-- A layout with the given ABI. -/
def mkLayout (ty : Miri.MIR.TyId) (repr : BackendRepr) (fields : FieldsShape) (sizeBytes : UInt64)
    (align : Align) : LocalLayout :=
  { ty := ty
    layout := {
      fields := fields
      variants := .Single 0
      backendRepr := repr
      largestNiche := none
      uninhabited := false
      align := ⟨align⟩
      size := Size.ofBytes sizeBytes
      maxReprAlign := none
      unadjustedAbiAlign := align
      reprC := false
      randomizationSeed := 0 } }

/-- `*const ()`: one pointer scalar. -/
def layoutThin : LocalLayout := mkLayout tyThin (.Scalar abiPtr) .Primitive 8 Align.EIGHT

/-- `*const [u8]`: a pointer and a `usize` length. -/
def layoutSlice : LocalLayout :=
  mkLayout tySlice (.ScalarPair (a := abiPtr) (b := abiUsize) (bOffset := Size.ofBytes 8))
    (.Arbitrary #[Size.ZERO, Size.ofBytes 8] #[0, 1]) 16 Align.EIGHT

/-- `*const dyn Trait`: a pointer and a vtable pointer. -/
def layoutDyn : LocalLayout :=
  mkLayout tyDyn (.ScalarPair (a := abiPtr) (b := abiPtr) (bOffset := Size.ofBytes 8))
    (.Arbitrary #[Size.ZERO, Size.ofBytes 8] #[0, 1]) 16 Align.EIGHT

/-- `bool`. -/
def layoutBool : LocalLayout := mkLayout tyBool (.Scalar abiBool) .Primitive 1 Align.ONE

/-- `usize`. -/
def layoutUsize : LocalLayout := mkLayout tyUsize (.Scalar abiUsize) .Primitive 8 Align.EIGHT

/-- `()`. -/
def layoutUnit : LocalLayout :=
  mkLayout tyUnit (.Memory (sized := true)) (.Arbitrary #[] #[]) 0 Align.ONE

/-- A hook that the pointer casts and comparisons studied here never call. -/
def lmUnused {A : Type} : RvalueM Unit A := throw (.unsupported "harness: unused hook")

/-- The compiler's description of the harness types for casts. -/
def lmTypeInfo (ty : Miri.MIR.TyId) : RvalueM Unit CastTypeInfo :=
  if ty = tyThin then pure (.rawPointer tyUnit)
  else if ty = tySlice then pure (.rawPointer tySliceU8)
  else if ty = tyDyn then pure (.rawPointer tyDynTrait)
  else if ty = tyUsize then pure (.integer .usize)
  else if ty = tyBool then pure .boolean
  else throw (.invalidProgram "harness: unknown type")

/-- The cast hooks: only `target` and `typeInfo` are consulted by `ptrToPtr`. -/
def lmCastHooks : CastHooks Provenance Unit Unit Unit where
  target := lmLayout
  typeInfo := fun _ ty => lmTypeInfo ty
  layoutOf := fun _ _ => lmUnused
  destLayout := fun _ => layoutThin
  readImmediate := fun _ _ => lmUnused
  writeImmediate := fun _ _ _ => lmUnused
  writePointer := fun _ _ _ => lmUnused
  enforceValidity := fun _ _ => lmUnused
  enforceValidityRecursively := fun _ _ => lmUnused
  validatePlace := fun _ _ _ _ => lmUnused
  derefPointer := fun _ _ => lmUnused
  checkFunctionPointer := fun _ _ => lmUnused
  exposeProvenance := fun _ _ => lmUnused
  pointerFromExposedAddress := fun _ _ => lmUnused
  usizeLayout := fun _ => pure layoutUsize
  floatOps :=
    { integerKindOf := fun _ _ => lmUnused
      formatOf := fun _ _ => lmUnused
      boolLayout := fun _ => pure layoutBool
      floatNondeterministic := false
      chooseNaN := fun _ _ => lmUnused }
  ensureMonomorphic := fun _ _ => lmUnused
  requireNoBoundVars := fun _ _ => lmUnused
  resolveFunction := fun _ _ _ => lmUnused
  resolveClosureFnOnce := fun _ _ _ => lmUnused
  functionPointer := fun _ _ => lmUnused
  builtinDeref := fun _ _ _ => lmUnused
  boxLayout := fun _ _ => lmUnused
  validateImmediateABI := fun _ _ => .error (.unsupported "harness: unused hook")
  copyAllowTransmute := fun _ _ _ => lmUnused
  copyNoValidate := fun _ _ _ _ => lmUnused
  projectRead := fun _ _ _ => lmUnused
  projectWrite := fun _ _ _ => lmUnused
  fieldLayout := fun _ _ _ => lmUnused
  lockstepTails := fun _ _ _ => lmUnused
  vtableType := fun _ _ _ => lmUnused
  vtablePointer := fun _ _ _ => lmUnused
  principal := fun _ _ => lmUnused
  vtableEntries := fun _ _ _ => lmUnused
  supertraitSlot := fun _ _ _ => lmUnused
  eraseSelfTraitRef := fun _ _ => lmUnused
  normalizePrincipal := fun _ _ => lmUnused

/-- The compiler's classification of the harness types for operators. -/
def lmClassify (ty : Miri.MIR.TyId) : RvalueM Unit ScalarTypeClass :=
  if ty = tyThin ∨ ty = tySlice ∨ ty = tyDyn then pure .pointer
  else if ty = tyUsize then pure (.integer .usize)
  else if ty = tyBool then pure .boolean
  else throw (.invalidProgram "harness: unclassified type")

/-- The result layouts of the operators. -/
def lmLeaves : ExecutionScalar.Leaves Unit Unit where
  classify := fun _ ty => lmClassify ty
  boolLayout := fun _ => pure layoutBool
  orderingLayout := fun _ => lmUnused
  overflowLayout := fun _ _ => lmUnused
  metadataLayout := fun _ _ => pure layoutUsize
  unitLayout := fun _ => pure layoutUnit

/-- Miri's pointer comparison: the vendored `ExecutionScalar.pointerBinary`. -/
def lmPointerBinary (op : Miri.MIR.BinOp) (left right : RvalueImmTy Provenance) :
    RvalueM Unit (RvalueImmTy Provenance) :=
  ExecutionScalar.pointerBinary lmLayout lmLeaves
    (fun _ ty => pure (decide (ty = tyThin ∨ ty = tySlice ∨ ty = tyDyn)))
    (fun _ => pure layoutUsize) () op left right

/-- The operator hooks: pointer operands are compared by `lmPointerBinary`. -/
def lmScalarOps : ScalarOpsHooks Provenance Unit Unit where
  classify := fun _ ty => lmClassify ty
  boolLayout := fun _ => pure layoutBool
  orderingLayout := fun _ => lmUnused
  overflowLayout := fun _ _ => lmUnused
  metadataLayout := fun _ _ => pure layoutUsize
  unitLayout := fun _ => pure layoutUnit
  floatBinary := fun _ _ _ _ => lmUnused
  pointerBinary := fun _ op left right => lmPointerBinary op left right
  floatUnary := fun _ _ _ => lmUnused
  derefValidity := fun _ _ => pure ()

/-- Run a stateless operator. -/
def lmRun {A : Type} (x : RvalueM Unit A) : Except StepError A :=
  match x () with
  | .ok a _ => .ok a
  | .error e _ => .error e

/-- The cast `p as *const ()`: the vendored `Cast.ptrToPtr`. -/
def lmToThin (value : RvalueImmTy Provenance) : Except StepError (RvalueImmTy Provenance) :=
  lmRun (Cast.ptrToPtr lmCastHooks () value layoutThin)

/-- `==`: the vendored `ScalarOps.binary` at `BinOp::Eq`. -/
def lmEq (left right : RvalueImmTy Provenance) : Except StepError (RvalueImmTy Provenance) :=
  lmRun (ScalarOps.binary lmScalarOps () .Eq left right)

/-- `ptr::addr_eq`: cast both operands to `*const ()`, then `==`. -/
def lmAddrEq (left right : RvalueImmTy Provenance) : Except StepError (RvalueImmTy Provenance) := do
  let left ← lmToThin left
  let right ← lmToThin right
  lmEq left right

/-- A slice pointer `*const [u8]`: `Immediate::new_slice`. -/
def lmSlice (ptr : Pointer (Option Provenance)) (len : UInt64) :
    Except StepError (RvalueImmTy Provenance) :=
  match Immediate.newSlice ptr len lmLayout with
  | .ok imm => .ok ⟨imm, layoutSlice⟩
  | .error e => .error (ScalarOps.immediateError e)

/-- A trait-object pointer `*const dyn Trait`: `Immediate::new_dyn_trait`. -/
def lmDyn (ptr vtable : Pointer (Option Provenance)) :
    Except StepError (RvalueImmTy Provenance) :=
  match Immediate.newDynTrait ptr vtable lmLayout with
  | .ok imm => .ok ⟨imm, layoutDyn⟩
  | .error e => .error (ScalarOps.immediateError e)

/-- The Boolean an operator returned. -/
def lmBoolOf (value : RvalueImmTy Provenance) : Except StepError Bool :=
  match value.imm.toScalar with
  | .error e => .error (ScalarOps.immediateError e)
  | .ok scalar =>
    match scalar.toBool with
    | .error e => .error (ScalarOps.scalarError e)
    | .ok b => .ok b

/-! ## §3. The 30-case observer and the threaded traces -/

/-- What a scenario shows. -/
inductive LmHeapWideObs : Type where
  | okAlloc (sizeBytes : Nat) (alignBytes : Nat)
  | okRoundTrip (readBits : Nat)
  | okDealloc
  | okBool (val : Bool)
  | memoryLeak
  | ub
  | specPanic
  | invalidOrUnsupported
  deriving DecidableEq, Repr

/-- The observation class of a `StepError`: undefined behavior, or (for every
other interpreter error) invalid or unsupported. -/
def lmObsOfStep : StepError → LmHeapWideObs
  | .undefinedBehavior _ => .ub
  | .retagWriteToReadOnly => .ub
  | .termination _ => .invalidOrUnsupported
  | .stack _ => .invalidOrUnsupported
  | .invalidBlock _ => .invalidOrUnsupported
  | .frameIndexChanged _ _ => .invalidOrUnsupported
  | .expectedMirLocation => .invalidOrUnsupported
  | .unsupported _ => .invalidOrUnsupported
  | .invalidProgram _ => .invalidOrUnsupported
  | .resourceExhaustion _ => .invalidOrUnsupported
  | .machineStop _ => .invalidOrUnsupported
  | .callback _ => .invalidOrUnsupported

/-- Whether a Tree Borrows access status is a program error (a forbidden
access), as opposed to a malformed tree. -/
def lmAccessIsUb : BorrowTree.BorrowTreeAccessStatus → Bool
  | .AccessFailure _ _ => true
  | .WildcardFailure _ _ => true
  | .Completed => false
  | .MissingTag _ => false
  | .MultipleRoots _ => false
  | .RangeMapFailure _ => false
  | .LocationMapFailure _ _ => false
  | .CacheFailure _ _ => false

/-- Whether a Tree Borrows deallocation status is a program error. -/
def lmDeallocIsUb : BorrowTree.BorrowTreeDeallocStatus → Bool
  | .ProtectedDealloc _ _ => true
  | .AccessFailure status => lmAccessIsUb status
  | .Deallocated => false
  | .MultipleRoots _ => false
  | .MissingTag _ => false
  | .RangeMapFailure _ => false

/-- The observation class of a harness failure. Every vendored error type is
classified by its own vendored classifier:
- `MemoryLifecycleError` -> `AllocationMachine.deallocationError`,
- `AccessError` -> `MemoryErrors.access`,
- `AllocError` -> `MemoryErrors.allocation`,
- `ScalarError` -> `ScalarOps.scalarError`,
- `StepError` -> `lmObsOfStep`.
An invalid allocation request (`check_alloc_request`) violates the precondition
of `Layout::from_size_align` and is undefined behavior at the Rust allocator
entry. -/
def lmObsOfFailure : LmFailure → LmHeapWideObs
  | .allocAlign _ => .ub
  | .allocTooLarge _ => .ub
  | .allocLifecycle _ => .invalidOrUnsupported
  | .deallocAlign _ => .ub
  | .dealloc e => lmObsOfStep (AllocationMachine.deallocationError e)
  | .treeDealloc status => if lmDeallocIsUb status then .ub else .invalidOrUnsupported
  | .treeAccess status => if lmAccessIsUb status then .ub else .invalidOrUnsupported
  | .retag _ => .invalidOrUnsupported
  | .protectorRelease _ => .invalidOrUnsupported
  | .access e => lmObsOfStep (MemoryErrors.access e)
  | .allocation e => lmObsOfStep (MemoryErrors.allocation e)
  | .scalar e => lmObsOfStep (ScalarOps.scalarError e)
  | .step e => lmObsOfStep e
  | .leak _ => .memoryLeak
  | .harness _ => .invalidOrUnsupported

/-- The observation of a scenario: its result, or the class of its failure. -/
def lmObserve (r : Except LmFailure LmHeapWideObs) : LmHeapWideObs :=
  match r with
  | .ok o => o
  | .error e => lmObsOfFailure e

/-- The failure of a scenario, if it failed. -/
def lmFailureOf {A : Type} (r : Except LmFailure A) : Option LmFailure :=
  match r with
  | .ok _ => none
  | .error e => some e

/-- Observe what the allocation shim created: the pointer's allocation must
be live, of kind `MiriMemoryKind::Rust`, and the pointer's address must be a
multiple of the allocation's alignment; the observation reports the
allocation's size and alignment in bytes. -/
def lmAllocObs (st : LmState) (ptr : Pointer (Option Provenance)) :
    Except LmFailure LmHeapWideObs :=
  match ptr.provenance with
  | some (.concrete id _) =>
    match st.mem.live.find? (fun entry => entry.1 == id) with
    | none => .error (.access (.allocationLookup (.deadAllocation id)))
    | some (_, entry) =>
      match entry.allocation.align.bytes with
      | .error e => .error (.allocAlign e)
      | .ok alignBytes =>
        if entry.kind = .machine .rust ∧ ptr.offset.bytes % alignBytes = 0 then
          .ok (.okAlloc entry.allocation.byteSize.bytes.toNat alignBytes.toNat)
        else
          .error (.harness "the allocation is not an aligned Rust heap allocation")
  | some .wildcard => .error (.harness "the allocation shim returned a wildcard pointer")
  | none => .error (.harness "the allocation shim returned a pointer without provenance")

/-- The allocation shim on the initial state, observed. -/
def lmObsAlloc (tb : Bool) (size align : Nat) : Except LmFailure LmHeapWideObs := do
  let (ptr, st) ← lmAllocate (lmInit tb) size align
  lmAllocObs st ptr

/-- Allocate, store, load, deallocate, leak check. -/
def lmRoundTrip (tb : Bool) (size align : Nat) (width : UInt64) (bits : Nat) :
    Except LmFailure LmHeapWideObs := do
  let (ptr, st) ← lmAllocate (lmInit tb) size align
  let st ← lmStore st ptr width bits
  let (r, st) ← lmLoad st ptr width
  let st ← lmDeallocate st ptr size align
  lmLeakCheck st
  pure (.okRoundTrip r)

/-- A distinct second `BorTag` for heterogeneous wide-pointer comparison cases. -/
def lmChildTag : BorTag := ⟨1000, by decide⟩

/-- The over-aligned `Box` of the protector scenarios: a 32-byte, 32-aligned
heap allocation holding `42u32`, retagged through vendored
`RetagPipeline.retagPointerValue`, and read once through the child when
`readChild` is set. Returns the parent pointer, the child pointer, and the state. -/
def lmBoxWithChild (tb : Bool) (typeShape : RetagPipeline.RetagTypeShape)
    (typeFacts : RetagPolicy.TypeFacts) (refKind : RetagPolicy.ReferenceKind)
    (mode : RetagPolicy.RetagMode) (pointeeIsFreeze readChild : Bool) :
    Except LmFailure (Pointer (Option Provenance) × Pointer (Option Provenance) × LmState) := do
  let (parent, st) ← lmAllocate (lmInit tb) 32 32
  let st ← lmStore st parent 4 42
  let (child, st) ← lmRetag st parent typeShape typeFacts refKind mode pointeeIsFreeze
  if readChild then
    let (_, st) ← lmLoad st child 4
    pure (parent, child, st)
  else
    pure (parent, child, st)

/-- `TypeFacts` for a `Freeze + Unpin` 32-byte pointee. -/
def lmFrozenFacts : RetagPolicy.TypeFacts := ⟨true, true, true⟩

/-- `TypeFacts` for a `!Freeze + Unpin` (`UnsafeCell`) 32-byte pointee. -/
def lmCellFacts : RetagPolicy.TypeFacts := ⟨true, true, false⟩

/-- The allocation of the first allocation shim call. -/
def lmFirstId : AllocId := ⟨1, by decide⟩

/-- An address without provenance. -/
def lmAddr (addr : UInt64) : Pointer (Option Provenance) := ⟨Size.ofBytes addr, none⟩

/-- Observe the Boolean result of a comparison. -/
def lmBoolObs (r : Except StepError (RvalueImmTy Provenance)) : Except LmFailure LmHeapWideObs :=
  match r with
  | .error e => .error (.step e)
  | .ok value =>
    match lmBoolOf value with
    | .error e => .error (.step e)
    | .ok b => .ok (.okBool b)

/-- A comparison of two operands that are built first. -/
def lmCompare (op : RvalueImmTy Provenance → RvalueImmTy Provenance →
      Except StepError (RvalueImmTy Provenance))
    (left right : Except StepError (RvalueImmTy Provenance)) : Except LmFailure LmHeapWideObs :=
  lmBoolObs (do
    let left ← left
    let right ← right
    op left right)

/-- The 30 scenarios (`0..29`). An index out of range is a harness failure. -/
def lmCase (tb : Bool) : Nat → Except LmFailure LmHeapWideObs
  | 0 => lmObsAlloc tb 0 1
  | 1 => lmObsAlloc tb 0 32
  | 2 => lmRoundTrip tb 4 4 4 3735928559
  | 3 => lmRoundTrip tb 32 32 8 81985529216486895
  | 4 => do
    let (ptr, st) ← lmAllocate (lmInit tb) 4 4
    let (r, _) ← lmLoad st ptr 4
    pure (.okRoundTrip r)
  | 5 => lmObsAlloc tb 8 3
  | 6 => lmObsAlloc tb 9223372036854775808 8
  | 7 => do
    let (ptr, st) ← lmAllocate (lmInit tb) 8 8
    let st ← lmDeallocate st ptr 8 8
    let _ ← lmDeallocate st ptr 8 8
    pure .okDealloc
  | 8 => do
    let (ptr, st) ← lmAllocate (lmInit tb) 4 4
    let st ← lmStore st ptr 4 7
    let st ← lmDeallocate st ptr 4 4
    let (r, _) ← lmLoad st ptr 4
    pure (.okRoundTrip r)
  | 9 => do
    let (ptr, st) ← lmAllocate (lmInit tb) 8 8
    let _ ← lmDeallocate st ⟨Size.ofBytes (ptr.offset.bytes + 4), ptr.provenance⟩ 8 8
    pure .okDealloc
  | 10 => do
    let (ptr, st) ← lmAllocate (lmInit tb) 8 8
    let _ ← lmDeallocate st ptr 4 8
    pure .okDealloc
  | 11 => do
    let (ptr, st) ← lmAllocate (lmInit tb) 8 8
    let _ ← lmDeallocate st ptr 8 16
    pure .okDealloc
  | 12 => do
    let _ ← lmDeallocate (lmInit tb) (lmAddr 4096) 8 8
    pure .okDealloc
  | 13 => do
    let (ptr, st) ← lmAllocateKind (lmInit tb) 4 4 (.machine .global)
    let _ ← lmDeallocate st ptr 4 4
    pure .okDealloc
  | 14 => do
    let (ptr, st) ← lmAllocateKind (lmInit tb) 4 4 .stack
    let _ ← lmDeallocate st ptr 4 4
    pure .okDealloc
  | 15 => do
    let (_, st) ← lmAllocate (lmInit tb) 8 8
    lmLeakCheck st
    pure .okDealloc
  | 16 => do
    let (ptr, st) ← lmAllocate (lmInit tb) 8 8
    let st ← lmDeallocate st ptr 8 8
    lmLeakCheck st
    pure .okDealloc
  | 17 => do
    let (_, st) ← lmAllocateKind (lmInit tb) 8 8 (.machine .global)
    lmLeakCheck st
    pure .okDealloc
  | 18 => do
    let (_, box, st) ← lmBoxWithChild tb .globalBox lmFrozenFacts .Box .FnEntry true false
    let _ ← lmDeallocate st box 32 32
    pure .okDealloc
  | 19 => do
    let (parent, _, st) ← lmBoxWithChild tb .reference lmFrozenFacts .Shared .FnEntry true true
    let _ ← lmDeallocate st parent 32 32
    pure .okDealloc
  | 20 => do
    let (parent, _, st) ← lmBoxWithChild tb .reference lmFrozenFacts .Shared .FnEntry true true
    let st ← lmEndCall st
    let _ ← lmDeallocate st parent 32 32
    pure .okDealloc
  | 21 => do
    let (_, child, st) ← lmBoxWithChild tb .reference lmFrozenFacts .Shared .Default true false
    let _ ← lmDeallocate st child 32 32
    pure .okDealloc
  | 22 => do
    let (parent, _, st) ← lmBoxWithChild tb .reference lmCellFacts .Shared .FnEntry false false
    let _ ← lmDeallocate st parent 32 32
    pure .okDealloc
  | 23 => lmCompare lmAddrEq (lmSlice (lmAddr 8192) 3) (lmSlice (lmAddr 8192) 7)
  | 24 => lmCompare lmEq (lmSlice (lmAddr 8192) 3) (lmSlice (lmAddr 8192) 7)
  | 25 => lmCompare lmAddrEq (lmDyn (lmAddr 8192) (lmAddr 36864)) (lmDyn (lmAddr 8192) (lmAddr 40960))
  | 26 => lmCompare lmEq (lmDyn (lmAddr 8192) (lmAddr 36864)) (lmDyn (lmAddr 8192) (lmAddr 40960))
  | 27 => lmCompare lmAddrEq
      (lmSlice ⟨Size.ofBytes 8192, some (.concrete lmFirstId (lmRootTag lmFirstId))⟩ 5)
      (lmDyn ⟨Size.ofBytes 8192, some (.concrete lmFirstId lmChildTag)⟩ (lmAddr 36864))
  | 28 => lmCompare lmEq
      (lmSlice ⟨Size.ofBytes 8192, some (.concrete lmFirstId (lmRootTag lmFirstId))⟩ 5)
      (lmDyn ⟨Size.ofBytes 8192, some (.concrete lmFirstId lmChildTag)⟩ (lmAddr 36864))
  | 29 => lmObsAlloc tb 0 1073741824
  | _ => .error (.harness "no such case")

/-- The 30-case observer: `tb = false` runs without a borrow tracker,
`tb = true` with Tree Borrows. For `caseIdx ≥ 30` it is
`.invalidOrUnsupported`. -/
def lmHeapWideObserve (tb : Bool) (caseIdx : Nat) : LmHeapWideObs :=
  lmObserve (lmCase tb caseIdx)

/-- The exact failure of a case, if it failed. -/
def lmCaseFailure (tb : Bool) (caseIdx : Nat) : Option LmFailure :=
  lmFailureOf (lmCase tb caseIdx)

/-- One step of a threaded trace: on success record the observation and
continue with the new state; on a failure record its class and halt. -/
def lmTraceStep {A : Type} (r : Except LmFailure (LmHeapWideObs × A))
    (k : A → List LmHeapWideObs) : List LmHeapWideObs :=
  match r with
  | .ok (o, a) => o :: k a
  | .error e => [lmObsOfFailure e]

/-- The heap lifecycle on one state: allocate a 32-byte, 32-aligned block;
store and load a `u64`; leak check before deallocation (which reports the
leak and changes nothing); `addr_eq` of two slice pointers to the block;
deallocate; and deallocate again, which halts the trace. -/
def lmHeapLifecycleTrace (tb : Bool) : List LmHeapWideObs :=
  lmTraceStep (do
      let (ptr, st) ← lmAllocate (lmInit tb) 32 32
      let o ← lmAllocObs st ptr
      pure (o, (ptr, st))) fun (ptr, st) =>
  lmTraceStep (do
      let st ← lmStore st ptr 8 14627333968688404088
      let (r, st) ← lmLoad st ptr 8
      pure (.okRoundTrip r, st)) fun st =>
  lmObserve (do lmLeakCheck st; pure .okDealloc) ::
  lmTraceStep (do
      let o ← lmCompare lmAddrEq (lmSlice ptr 2) (lmSlice ptr 4)
      pure (o, ())) fun _ =>
  lmTraceStep (do
      let st ← lmDeallocate st ptr 32 32
      pure (.okDealloc, st)) fun st =>
  lmTraceStep (do
      let st ← lmDeallocate st ptr 32 32
      pure (.okDealloc, st)) fun _ => []

/-- The protector trace on one over-aligned block with a strongly protected
`Frozen` child (`lmBoxWithChild`, before any read through the child): read
`42u32` through the child; `addr_eq` of a slice pointer through the parent
and one through the child; deallocate through the parent while the child's
protector is active; and, if that succeeded, the exit leak check. -/
def lmProtectorDeallocTrace (tb : Bool) : List LmHeapWideObs :=
  match lmBoxWithChild tb .reference lmFrozenFacts .Shared .FnEntry true false with
  | .error e => [lmObsOfFailure e]
  | .ok (parent, child, st) =>
    lmTraceStep (do
        let (r, st) ← lmLoad st child 4
        pure (.okRoundTrip r, st)) fun st =>
    lmTraceStep (do
        let o ← lmCompare lmAddrEq (lmSlice parent 1) (lmSlice child 8)
        pure (o, ())) fun _ =>
    lmTraceStep (do
        let st ← lmDeallocate st parent 32 32
        pure (.okDealloc, st)) fun st =>
    lmTraceStep (do
        lmLeakCheck st
        pure (.okDealloc, ())) fun _ => []

/-- The status of `BorrowTree.deallocateBorrowRange` on the block of a
protector scenario (with Tree Borrows, retagged via vendored `RetagPipeline`):
optionally after `lmEndCall`, deallocated through the child tag or the parent tag. -/
def lmScenarioDeallocStatus (typeShape : RetagPipeline.RetagTypeShape)
    (typeFacts : RetagPolicy.TypeFacts) (refKind : RetagPolicy.ReferenceKind)
    (mode : RetagPolicy.RetagMode) (pointeeIsFreeze readChild release throughChild : Bool) :
    Option BorrowTree.BorrowTreeDeallocStatus :=
  match lmBoxWithChild true typeShape typeFacts refKind mode pointeeIsFreeze readChild with
  | .error _ => none
  | .ok (parent, child, st) =>
    match (if release then lmEndCall st else .ok st) with
    | .error _ => none
    | .ok st =>
      let ptr := if throughChild then child else parent
      match ptr.provenance with
      | some (.concrete id tag) =>
        match st.mem.live.find? (fun entry => entry.1 == id) with
        | none => none
        | some (_, entry) =>
          some (entry.allocation.extra.deallocateBorrowRange
            (.concrete tag) Size.ZERO (Size.ofBytes 32) st.ctx.global.protectedTags).status
      | _ => none

/-- Deallocate the block of a protector scenario through its child pointer. -/
def lmDeallocThroughChild (tb : Bool) (typeShape : RetagPipeline.RetagTypeShape)
    (typeFacts : RetagPolicy.TypeFacts) (refKind : RetagPolicy.ReferenceKind)
    (mode : RetagPolicy.RetagMode) (pointeeIsFreeze : Bool) : Except LmFailure LmHeapWideObs := do
  let (_, child, st) ← lmBoxWithChild tb typeShape typeFacts refKind mode pointeeIsFreeze false
  let _ ← lmDeallocate st child 32 32
  pure .okDealloc

/-- Reading AND writing through a strongly protected `Cell` child reference
still allows deallocation through the parent `Unique` tag in Tree Borrows. -/
def lmStrongCellAccessedDealloc : Except LmFailure LmHeapWideObs := do
  let (parent, child, st) ← lmBoxWithChild true .reference lmCellFacts .Shared .FnEntry false true
  let st ← lmStore st child 4 99
  let (v, st) ← lmLoad st child 4
  let _ ← lmDeallocate st parent 32 32
  pure (.okRoundTrip v)

/-! ### Evaluable twins of the harness -/

unroll_loops lmAllocatePtrU := lmAllocatePtr fuel 0 with allocatePtrU
unroll_loops lmAllocateKindU := lmAllocateKind fuel 0 with lmAllocatePtrU
unroll_loops lmAllocateU := lmAllocate fuel 0 with lmAllocateKindU
unroll_loops lmBeforeDeallocationU := lmBeforeDeallocation fuel 0
  with beforeMemoryDeallocationU, deallocateBorrowRangeU
unroll_loops lmDeallocHooksU := lmDeallocHooks fuel 0 with lmBeforeDeallocationU
unroll_loops lmDeallocateU := lmDeallocate fuel 0 with deallocatePtrWithU, lmDeallocHooksU
unroll_loops lmAccessTargetU := lmAccessTarget fuel 0 with getAllocInfoU
unroll_loops lmTreeAccessU := lmTreeAccess fuel 0
  with beforeMemoryWriteU, beforeMemoryReadU, performBorrowAccessRangeU
unroll_loops lmStoreU := lmStore fuel 0 with lmAccessTargetU, lmTreeAccessU
unroll_loops lmLoadU := lmLoad fuel 0 with lmAccessTargetU, lmTreeAccessU
unroll_loops lmRetagU := lmRetag fuel 0 with retagPointerValueU
unroll_loops lmReleaseOneU := lmReleaseOne fuel 0 with releaseProtectorU
unroll_loops lmEndCallU := lmEndCall fuel 0 with lmReleaseOneU
unroll_loops lmObsAllocU := lmObsAlloc fuel 0 with lmAllocateU
unroll_loops lmRoundTripU := lmRoundTrip fuel 0 with lmAllocateU, lmStoreU, lmLoadU, lmDeallocateU
unroll_loops lmBoxWithChildU := lmBoxWithChild fuel 0 with lmAllocateU, lmStoreU, lmRetagU, lmLoadU
unroll_loops lmCaseU := lmCase fuel 0
  with lmObsAllocU, lmRoundTripU, lmAllocateU, lmLoadU, lmDeallocateU, lmStoreU, lmAllocateKindU,
    lmBoxWithChildU, lmEndCallU
unroll_loops lmHeapWideObserveU := lmHeapWideObserve fuel 0 with lmCaseU
unroll_loops lmCaseFailureU := lmCaseFailure fuel 0 with lmCaseU
unroll_loops lmHeapLifecycleTraceU := lmHeapLifecycleTrace fuel 0
  with lmAllocateU, lmStoreU, lmLoadU, lmDeallocateU
unroll_loops lmProtectorDeallocTraceU := lmProtectorDeallocTrace fuel 0
  with lmBoxWithChildU, lmLoadU, lmDeallocateU
unroll_loops lmScenarioDeallocStatusU := lmScenarioDeallocStatus fuel 0
  with lmBoxWithChildU, lmEndCallU, deallocateBorrowRangeU
unroll_loops lmDeallocThroughChildU := lmDeallocThroughChild fuel 0
  with lmBoxWithChildU, lmDeallocateU
unroll_loops lmStrongCellAccessedDeallocU := lmStrongCellAccessedDealloc fuel 0
  with lmBoxWithChildU, lmStoreU, lmLoadU, lmDeallocateU

/-- **The 30-case table.** Cases `0..27` succeed or are undefined behavior;
case `28` (`==` on a slice pointer and a trait-object pointer) is rejected as
an invalid program; case `29` (`align = 2^30`) is rejected by
`Align::from_bytes`. Cases `19` and `21` are mode-sensitive: `okDealloc`
without a borrow tracker, undefined behavior with Tree Borrows. -/
theorem lmHeapWideObserve_table :
    (List.range 30).map (lmHeapWideObserve false) =
      [.okAlloc 0 1, .okAlloc 0 32, .okRoundTrip 3735928559, .okRoundTrip 81985529216486895,
       .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub,
       .memoryLeak, .okDealloc, .okDealloc,
       .okDealloc, .okDealloc, .okDealloc, .okDealloc, .okDealloc,
       .okBool true, .okBool false, .okBool true, .okBool false, .okBool true,
       .invalidOrUnsupported, .ub] ∧
    (List.range 30).map (lmHeapWideObserve true) =
      [.okAlloc 0 1, .okAlloc 0 32, .okRoundTrip 3735928559, .okRoundTrip 81985529216486895,
       .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub,
       .memoryLeak, .okDealloc, .okDealloc,
       .okDealloc, .ub, .okDealloc, .ub, .okDealloc,
       .okBool true, .okBool false, .okBool true, .okBool false, .okBool true,
       .invalidOrUnsupported, .ub] := by
  rw [lmHeapWideObserveU.eq_src]
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- Out of range, the observer is `.invalidOrUnsupported` in both modes. -/
theorem lmHeapWideObserve_out_of_range (tb : Bool) (caseIdx : Nat) (h : 30 ≤ caseIdx) :
    lmHeapWideObserve tb caseIdx = .invalidOrUnsupported := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm]
  rfl

/-- The failures shared by both modes: the exact vendored error value of
every failing case outside the two Tree Borrows cases (note case 8 is now
reported directly by vendored `Miri.Memory.getPtrAccess` as
`.access (.allocationLookup (.deadAllocation lmFirstId))`!). -/
def lmSharedFailure : Nat → Option LmFailure
  | 4 => some (.allocation (.invalidUninitBytes (some
      ⟨⟨Size.ofBytes 0, Size.ofBytes 4⟩, ⟨Size.ofBytes 0, Size.ofBytes 4⟩⟩)))
  | 5 => some (.allocAlign (.notPowerOfTwo 3))
  | 6 => some (.allocTooLarge 9223372036854775808)
  | 7 => some (.dealloc (.useAfterFree lmFirstId))
  | 8 => some (.access (.allocationLookup (.deadAllocation lmFirstId)))
  | 9 => some (.dealloc (.nonzeroAllocationOffset "deallocate" lmFirstId (Size.ofBytes 4)))
  | 10 => some (.dealloc (.layoutMismatch lmFirstId (Size.ofBytes 8) (Size.ofBytes 4) ⟨3⟩ ⟨3⟩))
  | 11 => some (.dealloc (.layoutMismatch lmFirstId (Size.ofBytes 8) (Size.ofBytes 8) ⟨3⟩ ⟨4⟩))
  | 12 => some (.dealloc (.danglingPointer 4096))
  | 13 => some (.dealloc (.memoryKindMismatch lmFirstId))
  | 14 => some (.dealloc (.memoryKindMismatch lmFirstId))
  | 15 => some (.leak [lmFirstId])
  | 28 => some (.step (.invalidProgram "pointer comparison backend mismatch"))
  | 29 => some (.allocAlign (.tooLarge 1073741824))
  | _ => none

/-- The exact failure of every case without a borrow tracker (`none`: the
case succeeded). -/
theorem lmCaseFailure_table_basic :
    (List.range 30).map (lmCaseFailure false) = (List.range 30).map lmSharedFailure := by
  rw [lmCaseFailureU.eq_src]
  decide +kernel

/-- The exact failure of every case with Tree Borrows: as without a borrow
tracker, except for case `19` (the deallocation's write through the parent is
a foreign write that would disable the strongly protected, accessed `Frozen`
child) and case `21` (the deallocation's write through an unprotected `Frozen`
child is forbidden). -/
theorem lmCaseFailure_table_tb :
    (List.range 30).map (lmCaseFailure true) =
      (List.range 30).map (fun i =>
        if i = 19 then
          some (.treeDealloc (.AccessFailure (.AccessFailure ⟨0, 4⟩
            (.TransitionError 1 (.ProtectedDisabled .Frozen)))))
        else if i = 21 then
          some (.treeDealloc (.AccessFailure (.AccessFailure ⟨0, 32⟩
            (.TransitionError 1 (.ChildAccessForbidden .Frozen)))))
        else lmSharedFailure i) := by
  rw [lmCaseFailureU.eq_src]
  decide +kernel

/-- The two modes disagree on exactly the Tree Borrows cases `19` and `21`. -/
theorem lmHeapWideObserve_mode_sensitive :
    (List.range 30).filter (fun i => lmHeapWideObserve false i != lmHeapWideObserve true i) =
      [19, 21] := by
  rw [lmHeapWideObserveU.eq_src]
  decide +kernel

/-- **The heap lifecycle trace**, the same in both modes. -/
theorem lmHeapLifecycleTrace_table :
    lmHeapLifecycleTrace false =
      [.okAlloc 32 32, .okRoundTrip 14627333968688404088, .memoryLeak, .okBool true,
       .okDealloc, .ub] ∧
    lmHeapLifecycleTrace true =
      [.okAlloc 32 32, .okRoundTrip 14627333968688404088, .memoryLeak, .okBool true,
       .okDealloc, .ub] := by
  rw [lmHeapLifecycleTraceU.eq_src]
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- **The protector trace.** Without a borrow tracker the block is
deallocated and nothing leaks; with Tree Borrows deallocating through the
parent while the child's strong protector is active is undefined behavior, and
the trace halts there. -/
theorem lmProtectorDeallocTrace_table :
    lmProtectorDeallocTrace false = [.okRoundTrip 42, .okBool true, .okDealloc, .okDealloc] ∧
    lmProtectorDeallocTrace true = [.okRoundTrip 42, .okBool true, .ub] := by
  rw [lmProtectorDeallocTraceU.eq_src]
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- **`BorrowTree.deallocateBorrowRange` and protectors (`rust#165833`)**, on
the trees produced by vendored `RetagPipeline.retagPointerValue`,
`BorrowTree.performBorrowAccessRange`, and `BorrowTree.releaseProtector`:
1. through a weakly protected `Box` tag (`RetagPolicy` `.Box` + `.FnEntry`): `Deallocated`;
2. through the root while a strongly protected `Frozen` child that was read is
   live: the write would disable it, `AccessFailure … ProtectedDisabled`;
3. through a strongly protected `&mut` tag itself (`RetagPolicy` `.Mutable` + `.FnEntry`):
   the write succeeds and the strong-protector check rejects it, `ProtectedDealloc`;
4. through the root after the protecting call ended (`lmEndCall`): `Deallocated`;
5. through an unprotected `Frozen` child tag (`.Default`): the write is forbidden,
   `AccessFailure … ChildAccessForbidden`;
6. through the root while a strongly protected `Cell` child is live:
   `Deallocated` (interior mutability is exempt). -/
theorem deallocateBorrowRange_protector_laws :
    lmScenarioDeallocStatus .globalBox lmFrozenFacts .Box .FnEntry true false false true =
      some .Deallocated ∧
    lmScenarioDeallocStatus .reference lmFrozenFacts .Shared .FnEntry true true false false =
      some (.AccessFailure (.AccessFailure ⟨0, 4⟩
        (.TransitionError 1 (.ProtectedDisabled .Frozen)))) ∧
    lmScenarioDeallocStatus .reference lmFrozenFacts .Mutable .FnEntry true false false true =
      some (.ProtectedDealloc ⟨0, 32⟩ ⟨1⟩) ∧
    lmScenarioDeallocStatus .reference lmFrozenFacts .Shared .FnEntry true true true false =
      some .Deallocated ∧
    lmScenarioDeallocStatus .reference lmFrozenFacts .Shared .Default true false false true =
      some (.AccessFailure (.AccessFailure ⟨0, 32⟩
        (.TransitionError 1 (.ChildAccessForbidden .Frozen)))) ∧
    lmScenarioDeallocStatus .reference lmCellFacts .Shared .FnEntry false false false false =
      some .Deallocated := by
  rw [lmScenarioDeallocStatusU.eq_src]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The same through the whole deallocation shim (`Memory::deallocate_ptr`
with `MachineMemoryHooks.beforeMemoryDeallocation`): through a strongly
protected `&mut` tag itself the shim fails with the exact `ProtectedDealloc`
status, through a weakly protected `Box` tag it succeeds, and without a borrow
tracker both succeed. -/
theorem deallocate_through_protected_tag :
    lmFailureOf (lmDeallocThroughChild true .reference lmFrozenFacts .Mutable .FnEntry true) =
      some (.treeDealloc (.ProtectedDealloc ⟨0, 32⟩ ⟨1⟩)) ∧
    lmDeallocThroughChild true .globalBox lmFrozenFacts .Box .FnEntry true = .ok .okDealloc ∧
    lmDeallocThroughChild false .reference lmFrozenFacts .Mutable .FnEntry true = .ok .okDealloc := by
  rw [lmDeallocThroughChildU.eq_src]
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- Witness that reading AND writing through a strongly protected `Cell` child
still permits deallocation through the parent `Unique` tag in Tree Borrows. -/
theorem strongProtected_cell_accessed_dealloc_ok :
    lmStrongCellAccessedDealloc = .ok (.okRoundTrip 99) := by
  rw [lmStrongCellAccessedDeallocU.eq_src]
  decide +kernel

/-- Allocation with `align = 0` is rejected at the Rust allocator layout boundary
(even though `rustc_abi::Align::from_bytes 0 = .ok Align.ONE`). -/
theorem lmAllocate_align_zero_ub (tb : Bool) (size : Nat) :
    lmAllocate (lmInit tb) size 0 = .error (.allocAlign (.notPowerOfTwo 0)) ∧
    lmObserve (lmObsAlloc tb size 0) = .ub := ⟨rfl, rfl⟩

/-! ## §1. Universal laws of the vendored definitions -/

/-! ### Leak policy (`rust#166221`) -/

/-- `MiriMemoryKind::may_leak`, classified: Rust heap memory (and Miri, C, and
Windows heap memory and runtime memory) must not leak; machine, global,
extern-static, TLS, mmap, and socket-address memory may. -/
theorem miriMemoryKind_mayLeak_iff (kind : MiriMemoryKind) :
    kind.mayLeak = true ↔
      kind = .machine ∨ kind = .global ∨ kind = .externStatic ∨ kind = .tls ∨ kind = .mmap ∨
        kind = .socketAddress := by
  cases kind <;> simp [MiriMemoryKind.mayLeak]

/-- `LeakCheck.mayLeak` on a `MemoryKind`: stack memory must not leak,
caller-location memory may, machine memory follows `MiriMemoryKind::may_leak`. -/
theorem leakCheck_mayLeak_eq (kind : MemoryKind MiriMemoryKind) :
    LeakCheck.mayLeak kind =
      match kind with
      | .stack => false
      | .callerLocation => true
      | .machine k => k.mayLeak := by
  cases kind <;> rfl

/-- Rust heap memory must not leak; global memory may. -/
theorem leakCheck_mayLeak_rust_global :
    LeakCheck.mayLeak (.machine .rust) = false ∧ LeakCheck.mayLeak (.machine .global) = true ∧
      LeakCheck.mayLeak (.stack : MemoryKind MiriMemoryKind) = false := ⟨rfl, rfl, rfl⟩

/-- Inversion of a successful `Except` bind. -/
theorem except_bind_eq_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- **`take_leaked_allocations` only reports memory that must not leak.** For
every memory and every set of static roots, each reported allocation was live
and its kind may not leak; in particular a `MiriMemoryKind::Global`
allocation is never reported. -/
theorem leakCheck_take_sound {E : Type} (memory memory' : MemoryState Provenance E MiriMemoryKind)
    (staticRoots : Array AllocId)
    (leaked : Array (AllocId × LocalAllocation Provenance E MiriMemoryKind))
    (h : LeakCheck.take memory staticRoots = .ok (memory', leaked)) :
    ∀ entry ∈ leaked, entry ∈ memory.live ∧ LeakCheck.mayLeak entry.2.kind = false := by
  unfold LeakCheck.take LeakCheck.takeProfiled at h
  obtain ⟨reachable, _, h⟩ := except_bind_eq_ok h
  have hl : leaked = memory.live.filter
      (fun x => !LeakCheck.mayLeak x.2.kind && !reachable.contains x.1) := by
    cases h
    rfl
  subst hl
  intro entry hmem
  obtain ⟨hlive, hp⟩ := Array.mem_filter.mp hmem
  refine ⟨hlive, ?_⟩
  cases hk : LeakCheck.mayLeak entry.2.kind with
  | false => rfl
  | true => rw [hk] at hp; cases hp

/-- A global allocation is never reported as leaked. -/
theorem leakCheck_take_never_reports_global {E : Type}
    (memory memory' : MemoryState Provenance E MiriMemoryKind) (staticRoots : Array AllocId)
    (leaked : Array (AllocId × LocalAllocation Provenance E MiriMemoryKind))
    (h : LeakCheck.take memory staticRoots = .ok (memory', leaked)) :
    ∀ entry ∈ leaked, entry.2.kind ≠ .machine .global := by
  intro entry hmem hk
  have hs := (leakCheck_take_sound memory memory' staticRoots leaked h entry hmem).2
  rw [hk] at hs
  cases hs

/-- `LeakCheck.takeProfiled` agrees with `LeakCheck.take` for any profiler options. -/
theorem leakCheck_takeProfiled_eq_take {E : Type} (profile : Lean.Options)
    (memory : MemoryState Provenance E MiriMemoryKind) (staticRoots : Array AllocId) :
    LeakCheck.takeProfiled profile memory staticRoots = LeakCheck.take memory staticRoots :=
  LeakCheck.takeProfiled_eq_take profile memory staticRoots

/-- Every allocation reported as leaked by `LeakCheck.take` is removed from
`memory'.live`. -/
theorem leakCheck_take_removes_leaked {E : Type}
    (memory memory' : MemoryState Provenance E MiriMemoryKind) (staticRoots : Array AllocId)
    (leaked : Array (AllocId × LocalAllocation Provenance E MiriMemoryKind))
    (h : LeakCheck.take memory staticRoots = .ok (memory', leaked)) :
    ∀ entry ∈ memory'.live, leaked.any (·.1 == entry.1) = false := by
  unfold LeakCheck.take LeakCheck.takeProfiled at h
  obtain ⟨reachable, _, h⟩ := except_bind_eq_ok h
  cases h
  intro entry hmem
  rcases entry with ⟨id, loc⟩
  have hp := (Array.mem_filter.mp hmem).2
  dsimp only at hp
  simpa using hp

/-- If every live allocation is permitted to leak (`LeakCheck.mayLeak = true`,
for instance all `.machine .global` / `.callerLocation` allocations), then any
succeeding `LeakCheck.take` reports zero leaks. -/
theorem leakCheck_take_empty_of_all_mayLeak {E : Type}
    (memory memory' : MemoryState Provenance E MiriMemoryKind) (staticRoots : Array AllocId)
    (leaked : Array (AllocId × LocalAllocation Provenance E MiriMemoryKind))
    (hall : ∀ entry ∈ memory.live, LeakCheck.mayLeak entry.2.kind = true)
    (h : LeakCheck.take memory staticRoots = .ok (memory', leaked)) :
    leaked = #[] := by
  cases hsz : leaked.size with
  | zero => exact Array.eq_empty_of_size_eq_zero hsz
  | succ n =>
    have hlt : 0 < leaked.size := by omega
    have hmem : leaked[0] ∈ leaked := Array.getElem_mem hlt
    have ⟨hlive, hno⟩ := leakCheck_take_sound memory memory' staticRoots leaked h leaked[0] hmem
    rw [hall leaked[0] hlive] at hno
    cases hno

/-- **Universal global-root reachability seeding law (`rust#166221`)**:
a live `.machine .rust` allocation (`id₁`) reachable from a live
`.machine .global` allocation (`id₂`, `id₁ ≠ id₂`) via its provenance edges is
NOT reported as leaked by `LeakCheck.take` (even with `staticRoots = #[]`),
whereas without that edge `id₁` IS reported as leaked. -/
theorem leakCheck_take_global_pointer_exempts_heap {E : Type}
    (id1 id2 : AllocId) (hneq : id1 ≠ id2)
    (rustAlloc globAlloc : Allocation Provenance E)
    (hrust : LeakCheck.allocationIds rustAlloc = #[])
    (hglob : LeakCheck.allocationIds globAlloc = #[id1]) :
    let mem : MemoryState Provenance E MiriMemoryKind :=
      { (MemoryState.empty : MemoryState Provenance E MiriMemoryKind) with
        live := #[(id1, ⟨.machine .rust, rustAlloc⟩), (id2, ⟨.machine .global, globAlloc⟩)] }
    LeakCheck.take mem #[] = .ok (mem, #[]) := by
  intro mem
  have h12 : (id1 == id2) = false := beq_false_of_ne hneq
  have htodo : (mem.live.filterMap fun (id, entry) =>
      if entry.kind == .machine .global then some id else none) ++ #[] = #[id2] := by
    simp [mem]
  have hedges : mem.live.foldl (fun count (_, entry) =>
      count + (LeakCheck.allocationIds entry.allocation).size) 0 = 1 := by
    simp [mem, hrust, hglob]
  have hfind2 : mem.live.find? (·.1 == id2) = some (id2, ⟨.machine .global, globAlloc⟩) := by
    simp [mem, h12]
  have hfind1 : mem.live.find? (·.1 == id1) = some (id1, ⟨.machine .rust, rustAlloc⟩) := by
    simp [mem]
  have hnot0 : ((#[] : Array AllocId).contains id2) = false := by simp
  have hnotc : ((#[id2] : Array AllocId).contains id1) = false := by simp [hneq]
  have hpush2 : ((#[] : Array AllocId).push id2) = #[id2] := rfl
  have hd0 : instDecidableEqBool ((#[] : Array AllocId).contains id2) true = isFalse (by simp) := by
    cases instDecidableEqBool ((#[] : Array AllocId).contains id2) true with
    | isFalse _ => rfl
    | isTrue ht => rw [hnot0] at ht; cases ht
  have hd1 : instDecidableEqBool ((#[id2] : Array AllocId).contains id1) true =
      isFalse (by simp [hneq]) := by
    cases instDecidableEqBool ((#[id2] : Array AllocId).contains id1) true with
    | isFalse _ => rfl
    | isTrue ht => rw [hnotc] at ht; cases ht
  unfold LeakCheck.take LeakCheck.takeProfiled
  dsimp only [Lean.profileit, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  rw [htodo, hedges]
  split
  · rename_i err herr
    conv at herr => lhs; whnf
    rw [hd0] at herr
    dsimp only at herr
    simp only [hfind2, hglob, hpush2] at herr
    conv at herr => lhs; whnf
    rw [hd1] at herr
    dsimp only at herr
    simp only [hfind1, hrust] at herr
    conv at herr => lhs; whnf
    cases herr
  · rename_i v hv
    conv at hv => lhs; whnf
    rw [hd0] at hv
    dsimp only at hv
    simp only [hfind2, hglob, hpush2] at hv
    conv at hv => lhs; whnf
    rw [hd1] at hv
    dsimp only at hv
    simp only [hfind1, hrust] at hv
    conv at hv => lhs; whnf
    cases hv
    simp [LeakCheck.mayLeak, MiriMemoryKind.mayLeak, mem]

/-- Concrete `staticRoots` seeding witness: a live unfreed `.machine .rust`
allocation leaks under `staticRoots = #[]` and is exempted under
`staticRoots = #[lmFirstId]`. -/
def lmStaticRootCheck (seeded : Bool) : Except StepError (List AllocId) := do
  let alloc ← match Allocation.fromBytes (Prov := Provenance) (Array.replicate 8 0) Align.EIGHT .Mut with
    | .ok a => Except.ok a
    | .error e => Except.error (MemoryErrors.allocation e)
  let mem : MemoryState Provenance Unit MiriMemoryKind :=
    { (MemoryState.empty : MemoryState Provenance Unit MiriMemoryKind) with
      live := #[(lmFirstId, ⟨.machine .rust, alloc⟩)] }
  let roots := if seeded then #[lmFirstId] else #[]
  let (_, leaked) ← LeakCheck.take mem roots
  pure (leaked.toList.map (·.1))

/-- Without `staticRoots`, `lmFirstId` leaks; seeded in `staticRoots`, it is
exempted (`leaked = []`). -/
theorem leakCheck_static_root_seeded_witness :
    lmStaticRootCheck false = .ok [lmFirstId] ∧
    lmStaticRootCheck true = .ok [] := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-! ### `Memory::deallocate_ptr`, `AllocationMachine`, and `MemoryErrors` -/

/-- `AllocationMachine.deallocationError` classifies exactly the seven
`memory.rs::deallocate_ptr` failures as undefined behavior. -/
theorem deallocationError_ub_iff (error : MemoryLifecycleError) :
    lmObsOfStep (AllocationMachine.deallocationError error) = .ub ↔
      (∃ address, error = .danglingPointer address) ∨
      (∃ operation id offset, error = .nonzeroAllocationOffset operation id offset) ∨
      (∃ id kind, error = .globalAllocationDeallocation id kind) ∨
      (∃ id, error = .useAfterFree id) ∨
      (∃ id, error = .immutableAllocation id) ∨
      (∃ id, error = .memoryKindMismatch id) ∨
      (∃ id size requested align requestedAlign,
        error = .layoutMismatch id size requested align requestedAlign) := by
  cases error <;> simp [AllocationMachine.deallocationError, lmObsOfStep]

/-- `MemoryErrors.access` classifies dangling integer pointers, dead-allocation
use-after-free, out-of-bounds, and alignment failures as UB. -/
theorem memoryErrors_access_ub_iff (error : AccessError) :
    lmObsOfStep (MemoryErrors.access error) = .ub ↔
      (∃ a s m, error = .danglingIntegerPointer a s m) ∨
      (∃ id, error = .allocationLookup (.deadAllocation id)) ∨
      (∃ id sz off isz m, error = .pointerOutOfBounds id sz off isz m) ∨
      (∃ mis, error = .alignmentCheckFailed mis) := by
  cases error with
  | danglingIntegerPointer a s m => exact ⟨fun _ => Or.inl ⟨a, s, m, rfl⟩, fun _ => rfl⟩
  | pointerOutOfBounds id sz off isz m =>
    exact ⟨fun _ => Or.inr (Or.inr (Or.inl ⟨id, sz, off, isz, m, rfl⟩)), fun _ => rfl⟩
  | alignmentCheckFailed mis =>
    exact ⟨fun _ => Or.inr (Or.inr (Or.inr ⟨mis, rfl⟩)), fun _ => rfl⟩
  | allocationLookup r =>
    cases r with
    | deadAllocation id => exact ⟨fun _ => Or.inr (Or.inl ⟨id, rfl⟩), fun _ => rfl⟩
    | unavailable id =>
      constructor
      · intro h; cases h
      · rintro (⟨_, _, _, h⟩ | ⟨_, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, h⟩) <;> cases h
  | sizeDoesNotFitI64 _ | signedSizeOutsideI64 _ | pointerArithmetic _ | malformedAlignment _ =>
    constructor
    · intro h; cases h
    · rintro (⟨_, _, _, h⟩ | ⟨_, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, h⟩) <;> cases h

/-- `MemoryErrors.allocation` classifies uninitialized reads as UB. -/
theorem memoryErrors_allocation_uninit_ub (info : Option BadBytesAccess) :
    lmObsOfStep (MemoryErrors.allocation (.invalidUninitBytes info)) = .ub := rfl

/-- `MemoryLifecycle.deallocatePtr` is `MemoryLifecycle.deallocatePtrWith` on
the projected deallocation hooks. -/
theorem deallocatePtr_eq_deallocatePtrWith {Prov Extra MachineKind HookState ProvExtra : Type}
    [DecidableEq MachineKind] (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (pointer : Pointer (Option Prov)) (oldSizeAndAlign : Option (Size × Align))
    (kind : MemoryKind MachineKind)
    (hooks : MemoryLifecycleHooks Prov Extra MachineKind HookState ProvExtra) :
    MemoryLifecycle.deallocatePtr memory hooksState pointer oldSizeAndAlign kind hooks =
      MemoryLifecycle.deallocatePtrWith memory hooksState pointer oldSizeAndAlign kind
        hooks.deallocation := rfl

/-- A deallocation through a pointer that does not resolve to an allocation
fails with `danglingPointer`, for every memory and every hooks. -/
theorem deallocatePtrWith_dangling {Prov Extra MachineKind HookState ProvExtra : Type}
    [DecidableEq MachineKind] (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (pointer : Pointer (Option Prov)) (oldSizeAndAlign : Option (Size × Align))
    (kind : MemoryKind MachineKind)
    (hooks : MemoryDeallocationHooks Prov Extra MachineKind HookState ProvExtra) (address : UInt64)
    (h : (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer
      0).outcome = .error address) :
    (MemoryLifecycle.deallocatePtrWith memory hooksState pointer oldSizeAndAlign kind
      hooks).outcome = .error (.danglingPointer address) ∧
    (MemoryLifecycle.deallocatePtrWith memory hooksState pointer oldSizeAndAlign kind
      hooks).detached = none := by
  unfold MemoryLifecycle.deallocatePtrWith
  simp only [Id.run, h]
  exact ⟨rfl, rfl⟩

/-- A deallocation through a pointer into the middle of an allocation fails
with `nonzeroAllocationOffset`, for every memory and every hooks. -/
theorem deallocatePtrWith_nonzero_offset {Prov Extra MachineKind HookState ProvExtra : Type}
    [DecidableEq MachineKind] (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (pointer : Pointer (Option Prov)) (oldSizeAndAlign : Option (Size × Align))
    (kind : MemoryKind MachineKind)
    (hooks : MemoryDeallocationHooks Prov Extra MachineKind HookState ProvExtra)
    (id : AllocId) (offset : Size) (provExtra : ProvExtra)
    (h : (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer
      0).outcome = .ok (id, offset, provExtra))
    (hoff : (offset.bytes != 0) = true) :
    (MemoryLifecycle.deallocatePtrWith memory hooksState pointer oldSizeAndAlign kind
      hooks).outcome = .error (.nonzeroAllocationOffset "deallocate" id offset) ∧
    (MemoryLifecycle.deallocatePtrWith memory hooksState pointer oldSizeAndAlign kind
      hooks).detached = none := by
  unfold MemoryLifecycle.deallocatePtrWith
  simp only [Id.run, h]
  change (if (offset.bytes != 0) = true then _ else _ :
    MemoryDeallocationResult Prov Extra MachineKind HookState).outcome = _ ∧
    (if (offset.bytes != 0) = true then _ else _ :
      MemoryDeallocationResult Prov Extra MachineKind HookState).detached = _
  rw [ite_eq_left hoff]
  exact ⟨rfl, rfl⟩

/-- Removing `id` from `live` leaves no row with key `id`. -/
theorem live_filter_removes {Prov Extra MachineKind : Type}
    (live : Array (AllocId × LocalAllocation Prov Extra MachineKind)) (id : AllocId) :
    ∀ row ∈ live.filter (fun old => old.1 != id), row.1 ≠ id := by
  intro row hmem heq
  have hp := (Array.mem_filter.mp hmem).2
  subst heq
  simp at hp

/-- Unfolded post-resolution body of `MemoryLifecycle.deallocatePtrWith` at
offset `0`, exposing the live-map lookup and removal definitionally (without
naming private `MemoryState.removeLive`). -/
theorem deallocatePtrWith_zero_offset_step {Prov Extra MachineKind HookState ProvExtra : Type}
    [DecidableEq MachineKind] (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (pointer : Pointer (Option Prov)) (oldSizeAndAlign : Option (Size × Align))
    (kind : MemoryKind MachineKind)
    (hooks : MemoryDeallocationHooks Prov Extra MachineKind HookState ProvExtra)
    (id : AllocId) (provExtra : ProvExtra)
    (hres : (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer
      0).outcome = .ok (id, Size.ZERO, provExtra)) :
    let resolved := hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0
    let resolvedState := hooks.synchronizeMemory resolved.memory resolved.state
    let afterRemove := { resolved.memory with live := resolved.memory.live.filter fun old => old.1 != id }
    MemoryLifecycle.deallocatePtrWith memory hooksState pointer oldSizeAndAlign kind hooks =
      match (resolved.memory.live.find? fun entry => entry.1 == id).map Prod.snd with
      | some entry =>
          let detached := some (id, entry)
          let allocation := entry.allocation
          if allocation.mutability == .Not then
            ⟨afterRemove, hooks.synchronizeMemory afterRemove resolvedState, detached,
              .error (.immutableAllocation id)⟩
          else if entry.kind ≠ kind then
            ⟨afterRemove, hooks.synchronizeMemory afterRemove resolvedState, detached,
              .error (.memoryKindMismatch id)⟩
          else
            match oldSizeAndAlign with
            | some (requestedSize, requestedAlign) =>
                if requestedSize != allocation.byteSize || requestedAlign != allocation.align then
                  ⟨afterRemove, hooks.synchronizeMemory afterRemove resolvedState, detached,
                    .error (.layoutMismatch id allocation.byteSize requestedSize
                      allocation.align requestedAlign)⟩
                else
                  let before := hooks.beforeDeallocation afterRemove
                    (hooks.synchronizeMemory afterRemove resolvedState) allocation pointer id
                    provExtra allocation.byteSize allocation.align kind
                  let beforeState := hooks.synchronizeMemory before.memory before.state
                  match before.outcome with
                  | .ok () =>
                      let deadEntry : DeadAllocation := ⟨id, allocation.byteSize, allocation.align⟩
                      let alreadyDead := before.memory.dead.any fun old => old.allocId == id
                      let afterDead := { before.memory with
                        dead := (before.memory.dead.filter fun old => old.allocId != id).push deadEntry }
                      let finalState := hooks.synchronizeMemory afterDead beforeState
                      if alreadyDead then
                        ⟨afterDead, finalState, detached, .error (.duplicateDeadAllocation id)⟩
                      else
                        ⟨afterDead, finalState, detached, .ok ()⟩
                  | .error message =>
                      ⟨before.memory, beforeState, detached,
                        .error (.hookFailure "beforeMemoryDeallocation" message)⟩
            | _ =>
                let before := hooks.beforeDeallocation afterRemove
                  (hooks.synchronizeMemory afterRemove resolvedState) allocation pointer id
                  provExtra allocation.byteSize allocation.align kind
                let beforeState := hooks.synchronizeMemory before.memory before.state
                match before.outcome with
                | .ok () =>
                    let deadEntry : DeadAllocation := ⟨id, allocation.byteSize, allocation.align⟩
                    let alreadyDead := before.memory.dead.any fun old => old.allocId == id
                    let afterDead := { before.memory with
                      dead := (before.memory.dead.filter fun old => old.allocId != id).push deadEntry }
                    let finalState := hooks.synchronizeMemory afterDead beforeState
                    if alreadyDead then
                      ⟨afterDead, finalState, detached, .error (.duplicateDeadAllocation id)⟩
                    else
                      ⟨afterDead, finalState, detached, .ok ()⟩
                | .error message =>
                    ⟨before.memory, beforeState, detached,
                      .error (.hookFailure "beforeMemoryDeallocation" message)⟩
      | _ =>
          match resolved.memory.findGlobal? id with
          | some global =>
              ⟨resolved.memory, resolvedState, none,
                .error (.globalAllocationDeallocation id global.kind)⟩
          | none => ⟨resolved.memory, resolvedState, none, .error (.useAfterFree id)⟩ := by
  unfold MemoryLifecycle.deallocatePtrWith
  simp only [Id.run, hres, Size.ZERO, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    pure, Pure.pure, bind, Bind.bind]
  split
  · rename_i entry hopt
    change Option.map Prod.snd
      ((hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).memory.live.find?
        fun e => e.1 == id) = some entry at hopt
    rw [hopt]
    dsimp only
    cases hmut : (entry.allocation.mutability == Mutability.Not)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hkind : entry.kind = kind
      · simp only [hkind, ne_eq, not_true_eq_false, ↓reduceIte]
        cases oldSizeAndAlign with
        | none =>
          dsimp only
          split
          · rename_i hbef
            change (hooks.beforeDeallocation
              { (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).memory with
                live := (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).memory.live.filter
                  fun old => old.1 != id }
              (hooks.synchronizeMemory
                { (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).memory with
                  live := (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).memory.live.filter
                    fun old => old.1 != id }
                (hooks.synchronizeMemory
                  (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).memory
                  (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).state))
              entry.allocation pointer id provExtra entry.allocation.byteSize entry.allocation.align kind).outcome =
              Except.ok () at hbef
            rw [hbef]
            rfl
          · rename_i msg hbef
            change (hooks.beforeDeallocation
              { (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).memory with
                live := (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).memory.live.filter
                  fun old => old.1 != id }
              (hooks.synchronizeMemory
                { (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).memory with
                  live := (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).memory.live.filter
                    fun old => old.1 != id }
                (hooks.synchronizeMemory
                  (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).memory
                  (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).state))
              entry.allocation pointer id provExtra entry.allocation.byteSize entry.allocation.align kind).outcome =
              Except.error msg at hbef
            rw [hbef]
            rfl
        | some p =>
          rcases p with ⟨rs, ra⟩
          dsimp only
          cases hlay : (rs != entry.allocation.byteSize || ra != entry.allocation.align)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            split
            · rename_i hbef
              change (hooks.beforeDeallocation
                { (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).memory with
                  live := (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).memory.live.filter
                    fun old => old.1 != id }
                (hooks.synchronizeMemory
                  { (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).memory with
                    live := (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).memory.live.filter
                      fun old => old.1 != id }
                  (hooks.synchronizeMemory
                    (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).memory
                    (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).state))
                entry.allocation pointer id provExtra entry.allocation.byteSize entry.allocation.align kind).outcome =
                Except.ok () at hbef
              rw [hbef]
              rfl
            · rename_i msg hbef
              change (hooks.beforeDeallocation
                { (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).memory with
                  live := (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).memory.live.filter
                    fun old => old.1 != id }
                (hooks.synchronizeMemory
                  { (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).memory with
                    live := (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).memory.live.filter
                      fun old => old.1 != id }
                  (hooks.synchronizeMemory
                    (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).memory
                    (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).state))
                entry.allocation pointer id provExtra entry.allocation.byteSize entry.allocation.align kind).outcome =
                Except.error msg at hbef
              rw [hbef]
              rfl
          · simp only [↓reduceIte]; rfl
      · simp only [ne_eq, hkind, not_false_eq_true, ↓reduceIte]; rfl
    · simp only [↓reduceIte]; rfl
  · rename_i hopt
    cases hfind : Option.map Prod.snd
      ((hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).memory.live.find?
        fun e => e.1 == id) with
    | none =>
      cases (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0).memory.findGlobal? id <;>
        rfl
    | some entry =>
      exact absurd hfind (hopt entry)

/-- Deallocating an unmaterialized compiler global (absent from `live`, present
in `findGlobal?`) fails with `globalAllocationDeallocation` (`rust#166221`). -/
theorem deallocatePtrWith_global {Prov Extra MachineKind HookState ProvExtra : Type}
    [DecidableEq MachineKind] (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (pointer : Pointer (Option Prov)) (oldSizeAndAlign : Option (Size × Align))
    (kind : MemoryKind MachineKind)
    (hooks : MemoryDeallocationHooks Prov Extra MachineKind HookState ProvExtra)
    (id : AllocId) (provExtra : ProvExtra) (global : GlobalAllocation)
    (hres : (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer
      0).outcome = .ok (id, Size.ZERO, provExtra))
    (hnotlive : (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer
      0).memory.live.find? (fun entry => entry.1 == id) = none)
    (hglob : (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer
      0).memory.findGlobal? id = some global) :
    (MemoryLifecycle.deallocatePtrWith memory hooksState pointer oldSizeAndAlign kind
      hooks).outcome = .error (.globalAllocationDeallocation id global.kind) ∧
    (MemoryLifecycle.deallocatePtrWith memory hooksState pointer oldSizeAndAlign kind
      hooks).detached = none := by
  rw [deallocatePtrWith_zero_offset_step memory hooksState pointer oldSizeAndAlign kind hooks id
    provExtra hres]
  simp [hnotlive, hglob]

/-- Deallocating a pointer whose `AllocId` is neither live nor global fails
with `useAfterFree` (covering double-free). -/
theorem deallocatePtrWith_useAfterFree {Prov Extra MachineKind HookState ProvExtra : Type}
    [DecidableEq MachineKind] (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (pointer : Pointer (Option Prov)) (oldSizeAndAlign : Option (Size × Align))
    (kind : MemoryKind MachineKind)
    (hooks : MemoryDeallocationHooks Prov Extra MachineKind HookState ProvExtra)
    (id : AllocId) (provExtra : ProvExtra)
    (hres : (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer
      0).outcome = .ok (id, Size.ZERO, provExtra))
    (hnotlive : (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer
      0).memory.live.find? (fun entry => entry.1 == id) = none)
    (hnotglob : (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer
      0).memory.findGlobal? id = none) :
    (MemoryLifecycle.deallocatePtrWith memory hooksState pointer oldSizeAndAlign kind
      hooks).outcome = .error (.useAfterFree id) ∧
    (MemoryLifecycle.deallocatePtrWith memory hooksState pointer oldSizeAndAlign kind
      hooks).detached = none := by
  rw [deallocatePtrWith_zero_offset_step memory hooksState pointer oldSizeAndAlign kind hooks id
    provExtra hres]
  simp [hnotlive, hnotglob]

/-- Deallocating an immutable live allocation fails with `immutableAllocation`
AND detaches it from `live` (live-map detachment invariant). -/
theorem deallocatePtrWith_immutable {Prov Extra MachineKind HookState ProvExtra : Type}
    [DecidableEq MachineKind] (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (pointer : Pointer (Option Prov)) (oldSizeAndAlign : Option (Size × Align))
    (kind : MemoryKind MachineKind)
    (hooks : MemoryDeallocationHooks Prov Extra MachineKind HookState ProvExtra)
    (id : AllocId) (provExtra : ProvExtra) (entry : LocalAllocation Prov Extra MachineKind)
    (hres : (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer
      0).outcome = .ok (id, Size.ZERO, provExtra))
    (hlive : (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer
      0).memory.live.find? (fun e => e.1 == id) = some (id, entry))
    (himmut : entry.allocation.mutability = .Not) :
    let res := MemoryLifecycle.deallocatePtrWith memory hooksState pointer oldSizeAndAlign kind hooks
    res.outcome = .error (.immutableAllocation id) ∧
    res.detached = some (id, entry) ∧
    ∀ row ∈ res.memory.live, row.1 ≠ id := by
  intro res
  dsimp only [res]
  rw [deallocatePtrWith_zero_offset_step memory hooksState pointer oldSizeAndAlign kind hooks id
    provExtra hres]
  simp only [hlive, Option.map_some, himmut, beq_self_eq_true, ↓reduceIte]
  exact ⟨trivial, trivial, live_filter_removes _ id⟩

/-- Deallocating a mutable live allocation with the wrong `MemoryKind` (e.g.
`.stack` or materialized `.machine .global` via `.machine .rust`) fails with
`memoryKindMismatch` AND detaches it from `live` (live-map detachment invariant). -/
theorem deallocatePtrWith_kindMismatch {Prov Extra MachineKind HookState ProvExtra : Type}
    [DecidableEq MachineKind] (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (pointer : Pointer (Option Prov)) (oldSizeAndAlign : Option (Size × Align))
    (kind : MemoryKind MachineKind)
    (hooks : MemoryDeallocationHooks Prov Extra MachineKind HookState ProvExtra)
    (id : AllocId) (provExtra : ProvExtra) (entry : LocalAllocation Prov Extra MachineKind)
    (hres : (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer
      0).outcome = .ok (id, Size.ZERO, provExtra))
    (hlive : (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer
      0).memory.live.find? (fun e => e.1 == id) = some (id, entry))
    (hmut : entry.allocation.mutability = .Mut)
    (hkind : entry.kind ≠ kind) :
    let res := MemoryLifecycle.deallocatePtrWith memory hooksState pointer oldSizeAndAlign kind hooks
    res.outcome = .error (.memoryKindMismatch id) ∧
    res.detached = some (id, entry) ∧
    ∀ row ∈ res.memory.live, row.1 ≠ id := by
  intro res
  dsimp only [res]
  rw [deallocatePtrWith_zero_offset_step memory hooksState pointer oldSizeAndAlign kind hooks id
    provExtra hres]
  simp only [hlive, Option.map_some, hmut, show (Mutability.Mut == .Not) = false by rfl,
    Bool.false_eq_true, ne_eq, hkind, not_false_eq_true, ↓reduceIte]
  exact ⟨trivial, trivial, live_filter_removes _ id⟩

/-- Deallocating a mutable live allocation of matching kind with wrong size or
alignment fails with `layoutMismatch` AND detaches it from `live`. -/
theorem deallocatePtrWith_layoutMismatch {Prov Extra MachineKind HookState ProvExtra : Type}
    [DecidableEq MachineKind] (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (pointer : Pointer (Option Prov)) (reqSize : Size) (reqAlign : Align)
    (kind : MemoryKind MachineKind)
    (hooks : MemoryDeallocationHooks Prov Extra MachineKind HookState ProvExtra)
    (id : AllocId) (provExtra : ProvExtra) (entry : LocalAllocation Prov Extra MachineKind)
    (hres : (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer
      0).outcome = .ok (id, Size.ZERO, provExtra))
    (hlive : (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer
      0).memory.live.find? (fun e => e.1 == id) = some (id, entry))
    (hmut : entry.allocation.mutability = .Mut)
    (hkind : entry.kind = kind)
    (hbad : reqSize ≠ entry.allocation.byteSize ∨ reqAlign ≠ entry.allocation.align) :
    let res := MemoryLifecycle.deallocatePtrWith memory hooksState pointer
      (some (reqSize, reqAlign)) kind hooks
    res.outcome = .error (.layoutMismatch id entry.allocation.byteSize reqSize
      entry.allocation.align reqAlign) ∧
    res.detached = some (id, entry) ∧
    ∀ row ∈ res.memory.live, row.1 ≠ id := by
  intro res
  have hcond : (reqSize != entry.allocation.byteSize || reqAlign != entry.allocation.align) = true := by
    rcases hbad with hs | ha
    · simp [bne_iff_ne, hs]
    · simp [bne_iff_ne, ha]
  dsimp only [res]
  rw [deallocatePtrWith_zero_offset_step memory hooksState pointer (some (reqSize, reqAlign)) kind
    hooks id provExtra hres]
  simp only [hlive, Option.map_some, hmut, show (Mutability.Mut == .Not) = false by rfl,
    Bool.false_eq_true, hkind, ne_eq, not_true_eq_false, hcond, ↓reduceIte]
  exact ⟨trivial, trivial, live_filter_removes _ id⟩

/-- When `beforeDeallocation` fails after kind/layout checks pass, `deallocatePtrWith`
reports `.hookFailure "beforeMemoryDeallocation" msg` and retains `detached`. -/
theorem deallocatePtrWith_hookFailure {Prov Extra MachineKind HookState ProvExtra : Type}
    [DecidableEq MachineKind] (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (pointer : Pointer (Option Prov)) (kind : MemoryKind MachineKind)
    (hooks : MemoryDeallocationHooks Prov Extra MachineKind HookState ProvExtra)
    (id : AllocId) (provExtra : ProvExtra) (entry : LocalAllocation Prov Extra MachineKind)
    (msg : String)
    (hres : (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer
      0).outcome = .ok (id, Size.ZERO, provExtra))
    (hlive : (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer
      0).memory.live.find? (fun e => e.1 == id) = some (id, entry))
    (hmut : entry.allocation.mutability = .Mut)
    (hkind : entry.kind = kind)
    (hbefore :
      let r := hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0
      let afterRemove := { r.memory with live := r.memory.live.filter fun old => old.1 != id }
      let st1 := hooks.synchronizeMemory afterRemove (hooks.synchronizeMemory r.memory r.state)
      (hooks.beforeDeallocation afterRemove st1 entry.allocation pointer id provExtra
        entry.allocation.byteSize entry.allocation.align kind).outcome = .error msg) :
    let res := MemoryLifecycle.deallocatePtrWith memory hooksState pointer
      (some (entry.allocation.byteSize, entry.allocation.align)) kind hooks
    res.outcome = .error (.hookFailure "beforeMemoryDeallocation" msg) ∧
    res.detached = some (id, entry) := by
  intro res
  dsimp only [res]
  rw [deallocatePtrWith_zero_offset_step memory hooksState pointer
    (some (entry.allocation.byteSize, entry.allocation.align)) kind hooks id provExtra hres]
  simp only [hlive, Option.map_some, hmut, show (Mutability.Mut == .Not) = false by rfl,
    Bool.false_eq_true, hkind, ne_eq, not_true_eq_false, bne_self_eq_false,
    Bool.or_self, hbefore, ↓reduceIte]
  exact ⟨trivial, trivial⟩

/-- When all checks and `beforeDeallocation` succeed and `id` is not already in
`dead`, `deallocatePtrWith` returns `.ok ()`, detaches `id`, and records
`DeadAllocation ⟨id, size, align⟩` in `res.memory.dead`. -/
theorem deallocatePtrWith_ok {Prov Extra MachineKind HookState ProvExtra : Type}
    [DecidableEq MachineKind] (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (pointer : Pointer (Option Prov)) (kind : MemoryKind MachineKind)
    (hooks : MemoryDeallocationHooks Prov Extra MachineKind HookState ProvExtra)
    (id : AllocId) (provExtra : ProvExtra) (entry : LocalAllocation Prov Extra MachineKind)
    (hres : (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer
      0).outcome = .ok (id, Size.ZERO, provExtra))
    (hlive : (hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer
      0).memory.live.find? (fun e => e.1 == id) = some (id, entry))
    (hmut : entry.allocation.mutability = .Mut)
    (hkind : entry.kind = kind)
    (hbefore :
      let r := hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0
      let afterRemove := { r.memory with live := r.memory.live.filter fun old => old.1 != id }
      let st1 := hooks.synchronizeMemory afterRemove (hooks.synchronizeMemory r.memory r.state)
      (hooks.beforeDeallocation afterRemove st1 entry.allocation pointer id provExtra
        entry.allocation.byteSize entry.allocation.align kind).outcome = .ok ())
    (hnotdead :
      let r := hooks.resolvePointer memory (hooks.synchronizeMemory memory hooksState) pointer 0
      let afterRemove := { r.memory with live := r.memory.live.filter fun old => old.1 != id }
      let st1 := hooks.synchronizeMemory afterRemove (hooks.synchronizeMemory r.memory r.state)
      let bef := hooks.beforeDeallocation afterRemove st1 entry.allocation pointer id provExtra
        entry.allocation.byteSize entry.allocation.align kind
      (bef.memory.dead.any fun old => old.allocId == id) = false) :
    let res := MemoryLifecycle.deallocatePtrWith memory hooksState pointer
      (some (entry.allocation.byteSize, entry.allocation.align)) kind hooks
    res.outcome = .ok () ∧
    res.detached = some (id, entry) ∧
    (⟨id, entry.allocation.byteSize, entry.allocation.align⟩ : DeadAllocation) ∈ res.memory.dead := by
  intro res
  dsimp only [res]
  rw [deallocatePtrWith_zero_offset_step memory hooksState pointer
    (some (entry.allocation.byteSize, entry.allocation.align)) kind hooks id provExtra hres]
  simp only [hlive, Option.map_some, hmut, show (Mutability.Mut == .Not) = false by rfl,
    Bool.false_eq_true, hkind, ne_eq, not_true_eq_false, bne_self_eq_false,
    Bool.or_self, hbefore, hnotdead, ↓reduceIte]
  exact ⟨trivial, trivial, Array.mem_push_self⟩

/-- Direct universal bridge on vendored `Miri.Interpreter.AllocationMachine.deallocate`:
when pointer resolution fails with a dangling address, `AllocationMachine.deallocate`
throws `h.error (.danglingPointer address)` (since `pendingError = none`). -/
theorem allocationMachine_deallocate_dangling {K User Payload : Type} [DecidableEq K]
    (h : AllocationMachine.DeallocationHooks K User Payload)
    (pointer : Pointer (Option Provenance)) (oldLayout : Option (Size × Align))
    (kind : MemoryKind K) (st : MachineHooks.State K User) (address : UInt64)
    (hres : (h.resolvePointer st.machine.memory ⟨st.machine, none⟩ pointer 0).outcome =
      .error address)
    (hpend : (h.resolvePointer st.machine.memory ⟨st.machine, none⟩ pointer 0).state.pendingError =
      none) :
    let r := h.resolvePointer st.machine.memory ⟨st.machine, none⟩ pointer 0
    AllocationMachine.deallocate h pointer oldLayout kind st =
      .error (h.error (.danglingPointer address))
        { st with machine := { r.state.machine with memory := r.memory } } := by
  intro r
  have hsync : ({ machine := { st.machine with memory := st.machine.memory }, pendingError := none } :
      PlaceMachine.AccessState K User) = ⟨st.machine, none⟩ := rfl
  unfold AllocationMachine.deallocate MemoryLifecycle.deallocatePtrWith
  simp only [Id.run, get, getThe, MonadStateOf.get, modify, modifyGet, MonadStateOf.modifyGet,
    bind, Bind.bind, pure, Pure.pure, EStateM.bind, EStateM.get, EStateM.modifyGet,
    EStateM.throw, throw, throwThe, MonadExceptOf.throw, hsync, hres, hpend, Option.getD_none]
  rfl

/-! ### `Memory::allocate_ptr` failure classification

`MemoryLifecycle.allocatePtr` creates the backing storage (`Allocation.tryNew`)
*before* `insert_allocation` checks the size against the maximum object size,
reserves an `AllocId`, and rejects a dynamic allocation of the global kind.
The Rust allocator shim therefore has to reject a size above `isize::MAX`
before calling it (`lmAllocateKind`), or the host is asked for the storage. -/

/-- A failure to create the backing storage stops `allocate_ptr` first, with
the memory unchanged. -/
theorem allocatePtr_tryNew_error {Prov Extra MachineKind HookState : Type}
    [DecidableEq MachineKind] (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (sync : MemoryState Prov Extra MachineKind → HookState → HookState)
    (size : Size) (align : Align) (kind : MemoryKind MachineKind) (init : AllocInit)
    (maximumObjectSize : Size) (globalKind : Option (MemoryKind MachineKind))
    (zeroedStorage : Size → Align → Option (Array UInt8))
    (initExtra : MemoryState Prov Extra MachineKind → HookState → AllocId →
      MemoryKind MachineKind → Size → Align →
      MemoryStateHookResult Prov Extra MachineKind HookState Extra)
    (adjustRoot : MemoryState Prov Extra MachineKind → HookState → AllocId →
      MemoryKind MachineKind → MemoryStateHookResult Prov Extra MachineKind HookState (Pointer Prov))
    (e : AllocError) (h : Allocation.tryNew (Prov := Prov) size align init zeroedStorage = .error e) :
    (MemoryLifecycle.allocatePtr memory hooksState sync size align kind init maximumObjectSize
      globalKind zeroedStorage initExtra adjustRoot).outcome = .error (.allocation e) ∧
    (MemoryLifecycle.allocatePtr memory hooksState sync size align kind init maximumObjectSize
      globalKind zeroedStorage initExtra adjustRoot).memory = memory := by
  unfold MemoryLifecycle.allocatePtr
  simp only [Id.run, h]
  exact ⟨rfl, rfl⟩

/-- Once the storage exists, an object larger than the maximum object size
stops `insert_allocation` with `allocationTooLarge`, before any `AllocId` is
reserved: the memory is unchanged. -/
theorem allocatePtr_too_large {Prov Extra MachineKind HookState : Type}
    [DecidableEq MachineKind] (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (sync : MemoryState Prov Extra MachineKind → HookState → HookState)
    (size : Size) (align : Align) (kind : MemoryKind MachineKind) (init : AllocInit)
    (maximumObjectSize : Size) (globalKind : Option (MemoryKind MachineKind))
    (zeroedStorage : Size → Align → Option (Array UInt8))
    (initExtra : MemoryState Prov Extra MachineKind → HookState → AllocId →
      MemoryKind MachineKind → Size → Align →
      MemoryStateHookResult Prov Extra MachineKind HookState Extra)
    (adjustRoot : MemoryState Prov Extra MachineKind → HookState → AllocId →
      MemoryKind MachineKind → MemoryStateHookResult Prov Extra MachineKind HookState (Pointer Prov))
    (a : Allocation Prov Unit) (h : Allocation.tryNew (Prov := Prov) size align init zeroedStorage = .ok a)
    (hbig : a.byteSize.bytes > maximumObjectSize.bytes) :
    (MemoryLifecycle.allocatePtr memory hooksState sync size align kind init maximumObjectSize
      globalKind zeroedStorage initExtra adjustRoot).outcome =
        .error (.allocationTooLarge a.byteSize maximumObjectSize) ∧
    (MemoryLifecycle.allocatePtr memory hooksState sync size align kind init maximumObjectSize
      globalKind zeroedStorage initExtra adjustRoot).memory = memory := by
  unfold MemoryLifecycle.allocatePtr MemoryLifecycle.insertAllocation
  simp only [Id.run, h, pure_bind, hbig, ↓reduceIte]
  exact ⟨rfl, rfl⟩

/-- Once the storage exists and fits, a dynamic allocation of the global kind
is rejected with `dynamicallyAllocatingGlobal`, after the `AllocId` was
reserved (the reservation is kept, as in the source). -/
theorem allocatePtr_dynamically_global {Prov Extra MachineKind HookState : Type}
    [DecidableEq MachineKind] (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (sync : MemoryState Prov Extra MachineKind → HookState → HookState)
    (size : Size) (align : Align) (kind : MemoryKind MachineKind) (init : AllocInit)
    (maximumObjectSize : Size)
    (zeroedStorage : Size → Align → Option (Array UInt8))
    (initExtra : MemoryState Prov Extra MachineKind → HookState → AllocId →
      MemoryKind MachineKind → Size → Align →
      MemoryStateHookResult Prov Extra MachineKind HookState Extra)
    (adjustRoot : MemoryState Prov Extra MachineKind → HookState → AllocId →
      MemoryKind MachineKind → MemoryStateHookResult Prov Extra MachineKind HookState (Pointer Prov))
    (a : Allocation Prov Unit) (h : Allocation.tryNew (Prov := Prov) size align init zeroedStorage = .ok a)
    (hfit : ¬ a.byteSize.bytes > maximumObjectSize.bytes) (id : AllocId)
    (hres : memory.reserveAllocId.2 = .ok id) :
    (MemoryLifecycle.allocatePtr memory hooksState sync size align kind init maximumObjectSize
      (some kind) zeroedStorage initExtra adjustRoot).outcome = .error .dynamicallyAllocatingGlobal ∧
    (MemoryLifecycle.allocatePtr memory hooksState sync size align kind init maximumObjectSize
      (some kind) zeroedStorage initExtra adjustRoot).memory = memory.reserveAllocId.1 := by
  unfold MemoryLifecycle.allocatePtr MemoryLifecycle.insertAllocation
  cases hr : memory.reserveAllocId with
  | mk mem' r =>
    rw [hr] at hres
    simp only at hres
    subst hres
    simp only [Id.run, h, pure_bind, hfit, ↓reduceIte]
    exact ⟨rfl, rfl⟩

/-- `allocatePtr_too_large` is not vacuous and explains the shim's guard: the
vendored `Allocation.tryNew` happily creates a 16-byte backing store, and
`allocate_ptr` then rejects it against an 8-byte maximum object size. -/
theorem allocatePtr_too_large_witness :
    (MemoryLifecycle.allocatePtr (MemoryState.empty : LmMem) { treeBorrows := false }
      (fun _ ctx => ctx) (Size.ofBytes 16) Align.ONE (.machine .rust) .Uninit (Size.ofBytes 8)
      (some (.machine .global)) (fun size _ => some (Array.replicate size.bytes.toNat 0))
      lmInitExtra lmAdjustRoot).outcome =
        .error (.allocationTooLarge (Size.ofBytes 16) (Size.ofBytes 8)) := by
  rw [allocatePtrU.eq_src]
  decide +kernel

/-! ### Tree Borrows universal laws (`rust#165833`) -/

/-- On the single-threaded hooks (`lmHookContext`, `lmMachineHooks`), vendored
`MachineMemoryHooks.beforeMemoryDeallocation` succeeds **if and only if**
vendored `BorrowTree.deallocateBorrowRange` returns `.Deallocated`. -/
theorem beforeMemoryDeallocation_ok_iff (protectedTags : ProtectedTags)
    (allocation : Allocation Provenance BorrowTree) (pointer : Pointer (Option Provenance))
    (allocId : AllocId) (provenance : ProvenanceExtra) (size : Size) (align : Align)
    (kind : MemoryKind MiriMemoryKind) :
    (MachineMemoryHooks.beforeMemoryDeallocation lmHookContext (lmMachineHooks protectedTags)
      allocation pointer allocId provenance size align kind).outcome = .ok () ↔
      (allocation.extra.deallocateBorrowRange provenance Size.ZERO size protectedTags).status =
        .Deallocated := by
  unfold MachineMemoryHooks.beforeMemoryDeallocation lmHookContext lmMachineHooks
  simp only [Id.run, MachineMemoryHooks.SyncObjectStore.get,
    MachineMemoryHooks.SyncObjectStore.empty, MachineMemoryHooks.SyncObjectMap.empty,
    Array.contains_empty, Bool.false_eq_true, ↓reduceIte, Array.find?_empty, Option.map_none,
    Option.getD_none, pure, Pure.pure]
  cases h : (allocation.extra.deallocateBorrowRange provenance Size.ZERO size protectedTags).status with
  | Deallocated =>
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    exact ⟨fun _ => trivial, fun _ => rfl⟩
  | _ => simp

/-- Universal write-first law of vendored `BorrowTree.deallocateBorrowRange`:
whenever the initial write access (`performBorrowAccessRange ... .Write ...`)
does not complete, `deallocateBorrowRange` immediately returns
`.AccessFailure accessed.status`. -/
theorem deallocateBorrowRange_access_failure (tree : BorrowTree)
    (provenance : ProvenanceExtra) (offset length : Size) (protectedTags : ProtectedTags)
    (hfail : (tree.performBorrowAccessRange provenance offset length .Write protectedTags
      .VisitChildrenOfAccessed).status ≠ .Completed) :
    (tree.deallocateBorrowRange provenance offset length protectedTags).status =
      .AccessFailure (tree.performBorrowAccessRange provenance offset length .Write protectedTags
        .VisitChildrenOfAccessed).status := by
  unfold BorrowTree.deallocateBorrowRange
  have hne : ((tree.performBorrowAccessRange provenance offset length .Write protectedTags
      .VisitChildrenOfAccessed).status != .Completed) = true := bne_iff_ne.mpr hfail
  simp only [Id.run, hne, ↓reduceIte, pure, Pure.pure]

/-- Universal missing-tag law of vendored `BorrowTree.deallocateBorrowRange`. -/
theorem deallocateBorrowRange_missing_tag (tree : BorrowTree)
    (tag : BorTag) (offset length : Size) (protectedTags : ProtectedTags)
    (hok : (tree.performBorrowAccessRange (.concrete tag) offset length .Write protectedTags
      .VisitChildrenOfAccessed).status = .Completed)
    (hmiss : (tree.performBorrowAccessRange (.concrete tag) offset length .Write protectedTags
      .VisitChildrenOfAccessed).tree.indexOfTag tag = none) :
    (tree.deallocateBorrowRange (.concrete tag) offset length protectedTags).status =
      .MissingTag tag := by
  unfold BorrowTree.deallocateBorrowRange
  simp only [Id.run, hok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hmiss,
    Option.isNone_none, pure, Pure.pure]

/-- Universal `RetagPolicy.create` law (`rust#165833`): at `FnEntry`, a `Box`
(`Unpin`) ALWAYS receives a `.WeakProtector` (never `.StrongProtector`). -/
theorem retagPolicy_box_weak_protector (facts : RetagPolicy.TypeFacts)
    (config : RetagPolicy.PolicyConfig) (hunpin : facts.isUnpin = true)
    (hunsafe : facts.isUnsafeUnpin = true) :
    (RetagPolicy.create facts .Box .FnEntry config).map (·.protector) =
      some (some .WeakProtector) := by
  unfold RetagPolicy.create
  simp [Id.run, pure, Pure.pure, hunpin, hunsafe]

/-- Universal `RetagPolicy.create` law (`rust#165833`): at `FnEntry`, `&T`
(any facts) and `&mut T` (`Unpin`) ALWAYS receive a `.StrongProtector`. -/
theorem retagPolicy_ref_strong_protector (facts : RetagPolicy.TypeFacts)
    (config : RetagPolicy.PolicyConfig) :
    (RetagPolicy.create facts .Shared .FnEntry config).map (·.protector) =
      some (some .StrongProtector) ∧
    (facts.isUnpin = true → facts.isUnsafeUnpin = true →
      (RetagPolicy.create facts .Mutable .FnEntry config).map (·.protector) =
        some (some .StrongProtector)) := by
  constructor
  · unfold RetagPolicy.create; simp [Id.run, pure, Pure.pure]
  · intro hu hiu; unfold RetagPolicy.create; simp [Id.run, pure, Pure.pure, hu, hiu]

/-- Universal `RetagPolicy.create` law: non-`FnEntry` `.Default` retags install
NO protector (`protector = none`). -/
theorem retagPolicy_default_unprotected (facts : RetagPolicy.TypeFacts)
    (config : RetagPolicy.PolicyConfig) :
    (RetagPolicy.create facts .Shared .Default config).map (·.protector) = some none := by
  unfold RetagPolicy.create
  simp [Id.run, pure, Pure.pure]

/-- Universal per-location Tree Borrows deallocation-write transition laws on
vendored `Tree.LocationState.performAccess`:
1. Foreign write to `.Cell` succeeds even when `isProtected = true` and
   `accessed = true` (`Cell` exemption, Case 22).
2. Local write through `.Frozen` is always forbidden (`ChildAccessForbidden`, Case 21).
3. Foreign write to a protected, accessed `.Frozen` location triggers
   `ProtectedDisabled .Frozen` (Case 19).
4. Foreign write to an *unprotected* `.Frozen` location succeeds (Case 20). -/
theorem locationState_dealloc_write_laws (accessed isProtected : Bool)
    (sifa : IdempotentForeignAccess) :
    (Tree.LocationState.performAccess ⟨.Cell, accessed, sifa⟩ .Write .ForeignAccess isProtected =
      .Success ⟨.Cell, accessed, sifa⟩ ⟨.Cell, .Cell⟩) ∧
    (Tree.LocationState.performAccess ⟨.Frozen, accessed, sifa⟩ .Write .LocalAccess isProtected =
      .Error ⟨.Frozen, accessed, sifa⟩ (.ChildAccessForbidden .Frozen)) ∧
    (Tree.LocationState.performAccess ⟨.Frozen, true, sifa⟩ .Write .ForeignAccess true =
      .Error ⟨.Disabled, true, sifa⟩ (.ProtectedDisabled .Frozen)) ∧
    (Tree.LocationState.performAccess ⟨.Frozen, accessed, sifa⟩ .Write .ForeignAccess false =
      .Success ⟨.Disabled, accessed, sifa⟩ ⟨.Frozen, .Disabled⟩) := by
  cases accessed <;> cases isProtected <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-! ### `Align::from_bytes` at `Align::MAX` (universal over ALL `UInt64`) -/

/-- `Align::from_bytes` accepts every power of two up to `2^29`. -/
theorem align_fromBytes_pow2_ok (k : Nat) (h : k < 30) :
    Align.fromBytes (UInt64.ofNat (2 ^ k)) = .ok ⟨k⟩ := by
  have hall : (List.range 30).all
      (fun k => decide (Align.fromBytes (UInt64.ofNat (2 ^ k)) = .ok ⟨k⟩)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp hall k (List.mem_range.mpr h))

/-- `Align::from_bytes` rejects every power of two from `2^30` as too large. -/
theorem align_fromBytes_too_large (k : Nat) (h30 : 30 ≤ k) (h64 : k < 64) :
    Align.fromBytes (UInt64.ofNat (2 ^ k)) = .error (.tooLarge (UInt64.ofNat (2 ^ k))) := by
  have hall : (List.range 64).all (fun k => decide (k < 30) ||
      decide (Align.fromBytes (UInt64.ofNat (2 ^ k)) =
        .error (.tooLarge (UInt64.ofNat (2 ^ k))))) = true := by
    decide +kernel
  have hk := List.all_eq_true.mp hall k (List.mem_range.mpr h64)
  rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hk
  rcases hk with hk | hk
  · omega
  · exact hk

/-- The boundary: `2^29` is `Align::MAX`, `2^30` is too large, `3` is not a
power of two, and `0` is accepted as alignment `1` (as `rustc_abi` does). -/
theorem align_fromBytes_boundary :
    Align.fromBytes 536870912 = .ok Align.MAX ∧
    Align.fromBytes 1073741824 = .error (.tooLarge 1073741824) ∧
    Align.fromBytes 3 = .error (.notPowerOfTwo 3) ∧
    Align.fromBytes 0 = .ok Align.ONE := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Left-shifting `1 : UInt64` by `UInt64.ofNat p` always produces the power of
two `UInt64.ofNat (2 ^ (p % 64))`. -/
theorem uint64_one_shiftLeft_eq_pow2 (p : Nat) :
    UInt64.shiftLeft 1 (UInt64.ofNat p) = UInt64.ofNat (2 ^ (p % 64)) := by
  have hlt : p % 64 < 64 := Nat.mod_lt p (by decide)
  have hall : (List.range 64).all (fun k =>
      decide (UInt64.shiftLeft 1 (UInt64.ofNat k) = UInt64.ofNat (2 ^ k))) = true := by
    decide +kernel
  have hk := of_decide_eq_true (List.all_eq_true.mp hall (p % 64) (List.mem_range.mpr hlt))
  have hshift : UInt64.shiftLeft 1 (UInt64.ofNat p) = UInt64.shiftLeft 1 (UInt64.ofNat (p % 64)) := by
    apply UInt64.eq_of_toBitVec_eq
    apply BitVec.eq_of_toNat_eq
    have hdvd : 64 ∣ 2 ^ 64 := ⟨2 ^ 58, by decide⟩
    have hmod : (UInt64.ofNat p).toNat % 64 = (UInt64.ofNat (p % 64)).toNat % 64 := by
      rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat']
      rw [Nat.mod_mod_of_dvd p hdvd, Nat.mod_mod_of_dvd (p % 64) hdvd, Nat.mod_mod]
    show ((1 : BitVec 64) <<< ((UInt64.ofNat p).toBitVec % 64)).toNat =
      ((1 : BitVec 64) <<< ((UInt64.ofNat (p % 64)).toBitVec % 64)).toNat
    have hbv : ((UInt64.ofNat p).toBitVec % 64).toNat =
        ((UInt64.ofNat (p % 64)).toBitVec % 64).toNat := by
      have h64 : (64 : BitVec 64).toNat = 64 := by decide
      simpa only [BitVec.toNat_umod, h64, UInt64.toNat] using hmod
    have hbvEq : (UInt64.ofNat p).toBitVec % 64 = (UInt64.ofNat (p % 64)).toBitVec % 64 :=
      BitVec.eq_of_toNat_eq hbv
    rw [hbvEq]
  rw [hshift, hk]

/-- **Universal `notPowerOfTwo` law across ALL `2^64` values of `UInt64`**:
every nonzero `UInt64` that is not a power of two `2^k` (`k < 64`) is rejected
by `Align.fromBytes` with `.notPowerOfTwo bytes` (no `< 4096` cap!). -/
theorem align_fromBytes_not_pow2_all (bytes : UInt64) (hne : bytes ≠ 0)
    (hpow : ∀ k, k < 64 → bytes ≠ UInt64.ofNat (2 ^ k)) :
    Align.fromBytes bytes = .error (.notPowerOfTwo bytes) := by
  unfold Align.fromBytes
  have hbz : (bytes == 0) = false := beq_false_of_ne hne
  simp only [hbz, Bool.false_eq_true, ↓reduceIte]
  have hneShift : ∀ p : Nat, UInt64.shiftLeft 1 (UInt64.ofNat p) ≠ bytes := by
    intro p heq
    rw [uint64_one_shiftLeft_eq_pow2] at heq
    exact hpow (p % 64) (Nat.mod_lt p (by decide)) heq.symm
  split
  · rfl
  · rename_i hnot
    exfalso
    exact hneShift _ (by simpa [bne_iff_ne] using hnot)

/-- **Complete bidirectional `.ok` characterization of `Align.fromBytes` across
all `UInt64`**: succeeds iff `bytes = 0` (`Align.ONE`) or `bytes = 2^k` with
`k < 30`. -/
theorem align_fromBytes_ok_iff (bytes : UInt64) (al : Align) :
    Align.fromBytes bytes = .ok al ↔
      (bytes = 0 ∧ al = Align.ONE) ∨
      (∃ k, k < 30 ∧ bytes = UInt64.ofNat (2 ^ k) ∧ al = ⟨k⟩) := by
  constructor
  · intro h
    by_cases hz : bytes = 0
    · subst hz
      rw [align_fromBytes_boundary.2.2.2] at h
      exact Or.inl ⟨rfl, (Except.ok.inj h).symm⟩
    · by_cases hpow : ∃ k, k < 64 ∧ bytes = UInt64.ofNat (2 ^ k)
      · obtain ⟨k, hk64, rfl⟩ := hpow
        by_cases hk30 : k < 30
        · rw [align_fromBytes_pow2_ok k hk30] at h
          exact Or.inr ⟨k, hk30, rfl, (Except.ok.inj h).symm⟩
        · rw [align_fromBytes_too_large k (Nat.le_of_not_lt hk30) hk64] at h
          cases h
      · have hnp : ∀ k, k < 64 → bytes ≠ UInt64.ofNat (2 ^ k) :=
          fun k hk heq => hpow ⟨k, hk, heq⟩
        rw [align_fromBytes_not_pow2_all bytes hz hnp] at h
        cases h
  · rintro (⟨rfl, rfl⟩ | ⟨k, hk, rfl, rfl⟩)
    · exact align_fromBytes_boundary.2.2.2
    · exact align_fromBytes_pow2_ok k hk

/-- **Complete bidirectional `.tooLarge` characterization of `Align.fromBytes`
across all `UInt64`**: fails with `.tooLarge` iff `bytes = 2^k` with
`30 ≤ k < 64`. -/
theorem align_fromBytes_tooLarge_iff (bytes : UInt64) :
    Align.fromBytes bytes = .error (.tooLarge bytes) ↔
      ∃ k, 30 ≤ k ∧ k < 64 ∧ bytes = UInt64.ofNat (2 ^ k) := by
  constructor
  · intro h
    by_cases hz : bytes = 0
    · subst hz; rw [align_fromBytes_boundary.2.2.2] at h; cases h
    · by_cases hpow : ∃ k, k < 64 ∧ bytes = UInt64.ofNat (2 ^ k)
      · obtain ⟨k, hk64, rfl⟩ := hpow
        by_cases hk30 : k < 30
        · rw [align_fromBytes_pow2_ok k hk30] at h; cases h
        · exact ⟨k, Nat.le_of_not_lt hk30, hk64, rfl⟩
      · have hnp : ∀ k, k < 64 → bytes ≠ UInt64.ofNat (2 ^ k) :=
          fun k hk heq => hpow ⟨k, hk, heq⟩
        rw [align_fromBytes_not_pow2_all bytes hz hnp] at h
        cases h
  · rintro ⟨k, h30, h64, rfl⟩
    exact align_fromBytes_too_large k h30 h64

/-- **Complete bidirectional `.notPowerOfTwo` characterization of
`Align.fromBytes` across all `UInt64`**. -/
theorem align_fromBytes_notPowerOfTwo_iff (bytes : UInt64) :
    Align.fromBytes bytes = .error (.notPowerOfTwo bytes) ↔
      bytes ≠ 0 ∧ ∀ k, k < 64 → bytes ≠ UInt64.ofNat (2 ^ k) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro hz; subst hz; rw [align_fromBytes_boundary.2.2.2] at h; cases h
    · intro k hk64 heq; subst heq
      by_cases hk30 : k < 30
      · rw [align_fromBytes_pow2_ok k hk30] at h; cases h
      · rw [align_fromBytes_too_large k (Nat.le_of_not_lt hk30) hk64] at h; cases h
  · rintro ⟨hz, hpow⟩
    exact align_fromBytes_not_pow2_all bytes hz hpow

/-! ### `ptr::addr_eq` and wide `==` (`rust#166144`) -/

/-- Truncating any `UInt64` embedded in `U128` to 8 bytes (64 bits) is the identity. -/
theorem size_truncate_u64 (x : UInt64) :
    (Size.ofBytes 8).truncate (BitVec.ofNat 128 x.toNat) = .ok (BitVec.ofNat 128 x.toNat) := by
  have hlt : x.toNat < 2 ^ 64 := x.toFin.isLt
  have h128 : x.toNat < 2 ^ 128 := Nat.lt_trans hlt (by decide)
  have hbv : BitVec.zeroExtend 128 (BitVec.extractLsb 63 0 (BitVec.ofNat 128 x.toNat)) =
      BitVec.ofNat 128 x.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.zeroExtend, BitVec.extractLsb, BitVec.extractLsb', BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.shiftRight_zero]
    rw [Nat.mod_eq_of_lt h128, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt h128]
  change Except.ok (BitVec.zeroExtend 128 (BitVec.extractLsb 63 0 (BitVec.ofNat 128 x.toNat))) = _
  rw [hbv]

/-- `ScalarInt.tryFromUInt` at 8 bytes always succeeds on any `UInt64`, yielding
a `ScalarInt` whose `toBits (Size.ofBytes 8)` recovers `BitVec.ofNat 128 x.toNat`. -/
theorem scalarInt_tryFromUInt_u64 (x : UInt64) :
    ∃ si : ScalarInt,
      ScalarInt.tryFromUInt (BitVec.ofNat 128 x.toNat) (Size.ofBytes 8) = .ok (some si) ∧
      si.toBits (Size.ofBytes 8) = .ok (BitVec.ofNat 128 x.toNat) := by
  have hlt : x.toNat < 2 ^ 64 := x.toFin.isLt
  have h128 : x.toNat < 2 ^ 128 := Nat.lt_trans hlt (by decide)
  have hbv : BitVec.zeroExtend 128 (BitVec.extractLsb 63 0 (BitVec.ofNat 128 x.toNat)) =
      BitVec.ofNat 128 x.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.zeroExtend, BitVec.extractLsb, BitVec.extractLsb', BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.shiftRight_zero]
    rw [Nat.mod_eq_of_lt h128, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt h128]
  cases htr : ScalarInt.truncateFromUInt (BitVec.ofNat 128 x.toNat) (Size.ofBytes 8) with
  | error e =>
    have hok : (ScalarInt.truncateFromUInt (BitVec.ofNat 128 x.toNat) (Size.ofBytes 8)).isOk = true := rfl
    rw [htr] at hok; cases hok
  | ok p =>
    rcases p with ⟨si, ovf⟩
    have hovf : ovf = false := by
      have h1 : (ScalarInt.truncateFromUInt (BitVec.ofNat 128 x.toNat) (Size.ofBytes 8)).map Prod.snd =
          .ok (BitVec.zeroExtend 128 (BitVec.extractLsb 63 0 (BitVec.ofNat 128 x.toNat)) !=
            BitVec.ofNat 128 x.toNat) := rfl
      rw [htr] at h1
      simp only [Except.map, Except.ok.injEq] at h1
      rw [h1, hbv, bne_self_eq_false]
    have hbits : si.toBits (Size.ofBytes 8) = .ok (BitVec.ofNat 128 x.toNat) := by
      have h1 : (ScalarInt.truncateFromUInt (BitVec.ofNat 128 x.toNat) (Size.ofBytes 8)).bind
          (fun p => p.1.toBits (Size.ofBytes 8)) =
          .ok (BitVec.zeroExtend 128 (BitVec.extractLsb 63 0 (BitVec.ofNat 128 x.toNat))) := rfl
      rw [htr] at h1
      simpa only [Except.bind, hbv] using h1
    refine ⟨si, ?_, hbits⟩
    have htry : ScalarInt.tryFromUInt (BitVec.ofNat 128 x.toNat) (Size.ofBytes 8) =
        (ScalarInt.truncateFromUInt (BitVec.ofNat 128 x.toNat) (Size.ofBytes 8)).bind
          (fun p => if p.2 then .ok none else .ok (some p.1)) := rfl
    rw [htry, htr]
    simp [hovf, Except.bind]

/-- `Scalar.fromUInt` on any `UInt64` at 8 bytes succeeds and `toBits (Size.ofBytes 8)`
recovers `BitVec.ofNat 128 x.toNat`. -/
theorem scalar_fromUInt64_toBits (x : UInt64) :
    ∃ s : Miri.Memory.Scalar Provenance,
      Miri.Memory.Scalar.fromUInt (BitVec.ofNat 128 x.toNat) (Size.ofBytes 8) = .ok s ∧
      s.toBits (Size.ofBytes 8) = .ok (BitVec.ofNat 128 x.toNat) := by
  obtain ⟨si, htry, hbits⟩ := scalarInt_tryFromUInt_u64 x
  refine ⟨Miri.Memory.Scalar.fromScalarInt si, ?_, ?_⟩
  · unfold Miri.Memory.Scalar.fromUInt
    simp only [htry, Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  · change (si.toBits (Size.ofBytes 8)).mapError Miri.Memory.ScalarError.scalarInt = _
    rw [hbits]; rfl

/-- `Scalar.fromMaybePointer lmLayout ⟨addr, prov⟩` always succeeds and
`toBits (Size.ofBytes 8)` always returns `BitVec.ofNat 128 addr.bytes.toNat`,
completely erasing `prov` (both `some _` and `none`). -/
theorem scalar_fromMaybePointer_toBits (addr : Size) (prov : Option Provenance) :
    ∃ s : Miri.Memory.Scalar Provenance,
      Miri.Memory.Scalar.fromMaybePointer lmLayout ⟨addr, prov⟩ = .ok s ∧
      s.toBits (Size.ofBytes 8) = .ok (BitVec.ofNat 128 addr.bytes.toNat) := by
  obtain ⟨si, htry, hbits⟩ := scalarInt_tryFromUInt_u64 addr.bytes
  cases prov with
  | none =>
    refine ⟨Miri.Memory.Scalar.fromScalarInt si, ?_, ?_⟩
    · change ((do
        let scalar ← (ScalarInt.tryFromUInt (BitVec.ofNat 128 addr.bytes.toNat) (Size.ofBytes 8)).mapError
          Miri.Memory.ScalarError.scalarInt
        match scalar with
        | some s => pure (Miri.Memory.Scalar.fromScalarInt s)
        | none => throw (.pointerOffsetDoesNotFit addr (Size.ofBytes 8))) :
        Except Miri.Memory.ScalarError (Miri.Memory.Scalar Provenance)) = _
      rw [htry]; rfl
    · change (si.toBits (Size.ofBytes 8)).mapError Miri.Memory.ScalarError.scalarInt = _
      rw [hbits]; rfl
  | some p =>
    refine ⟨Miri.Memory.Scalar.fromPointer lmLayout ⟨addr, p⟩, rfl, ?_⟩
    change (Except.bind
      (Except.bind
        (Except.bind
          ((ScalarInt.tryFromUInt (BitVec.ofNat 128 addr.bytes.toNat) (Size.ofBytes 8)).mapError
            Miri.Memory.ScalarError.scalarInt)
          (fun scalar => match scalar with
            | some s => Except.ok (Miri.Memory.ScalarIntCastResult.integer s)
            | none => Except.error (.pointerOffsetDoesNotFit addr (Size.ofBytes 8))))
        (fun cast => match cast with
          | .integer v => Except.ok v
          | .erasedPointer _ _ => Except.error .readPointerAsInt))
      (fun s => (s.toBits (Size.ofBytes 8)).mapError Miri.Memory.ScalarError.scalarInt)) = _
    rw [htry]
    simp only [Except.mapError, Except.bind, hbits]

/-- The fat-to-thin cast keeps the data pointer and drops the metadata, for
every data scalar and every metadata scalar, of a slice pointer and of a
trait-object pointer. -/
theorem ptrToPtr_fat_to_thin (data metadata : Miri.Memory.Scalar Provenance) :
    lmToThin ⟨.scalarPair data metadata, layoutSlice⟩ = .ok ⟨.scalar data, layoutThin⟩ ∧
    lmToThin ⟨.scalarPair data metadata, layoutDyn⟩ = .ok ⟨.scalar data, layoutThin⟩ :=
  ⟨rfl, rfl⟩

/-- **`addr_eq` erases metadata** across all four combinations of wide pointer
types (`Slice`/`Slice`, `Dyn`/`Dyn`, `Slice`/`Dyn`, `Dyn`/`Slice`). -/
theorem addrEq_metadata_erased (dataL dataR metaL metaR : Miri.Memory.Scalar Provenance) :
    lmAddrEq ⟨.scalarPair dataL metaL, layoutSlice⟩ ⟨.scalarPair dataR metaR, layoutSlice⟩ =
      lmEq ⟨.scalar dataL, layoutThin⟩ ⟨.scalar dataR, layoutThin⟩ ∧
    lmAddrEq ⟨.scalarPair dataL metaL, layoutDyn⟩ ⟨.scalarPair dataR metaR, layoutDyn⟩ =
      lmEq ⟨.scalar dataL, layoutThin⟩ ⟨.scalar dataR, layoutThin⟩ ∧
    lmAddrEq ⟨.scalarPair dataL metaL, layoutSlice⟩ ⟨.scalarPair dataR metaR, layoutDyn⟩ =
      lmEq ⟨.scalar dataL, layoutThin⟩ ⟨.scalar dataR, layoutThin⟩ ∧
    lmAddrEq ⟨.scalarPair dataL metaL, layoutDyn⟩ ⟨.scalarPair dataR metaR, layoutSlice⟩ =
      lmEq ⟨.scalar dataL, layoutThin⟩ ⟨.scalar dataR, layoutThin⟩ :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `compare x y == .eq` on `Nat` is `x == y`. -/
theorem nat_compare_eq_iff (x y : Nat) : (compare x y == .eq) = decide (x = y) := by
  change (compareOfLessAndEq x y == .eq) = decide (x = y)
  unfold compareOfLessAndEq
  by_cases hlt : x < y
  · have hne : x ≠ y := Nat.ne_of_lt hlt
    simp [hlt, hne]
  · by_cases heq : x = y
    · subst heq; simp
    · simp [hlt, heq]

/-- Lexicographic pair comparison of `UInt64`s at `Eq` is equality of both
components. -/
theorem u64_lex_compare_eq (a b c d : UInt64) :
    ((if BitVec.ofNat 128 a.toNat == BitVec.ofNat 128 b.toNat then
        compare (BitVec.ofNat 128 c.toNat).toNat (BitVec.ofNat 128 d.toNat).toNat
      else
        compare (BitVec.ofNat 128 a.toNat).toNat (BitVec.ofNat 128 b.toNat).toNat) == .eq) =
      (a == b && c == d) := by
  have ha : (BitVec.ofNat 128 a.toNat).toNat = a.toNat :=
    Nat.mod_eq_of_lt (Nat.lt_trans a.toFin.isLt (by decide))
  have hb : (BitVec.ofNat 128 b.toNat).toNat = b.toNat :=
    Nat.mod_eq_of_lt (Nat.lt_trans b.toFin.isLt (by decide))
  have hc : (BitVec.ofNat 128 c.toNat).toNat = c.toNat :=
    Nat.mod_eq_of_lt (Nat.lt_trans c.toFin.isLt (by decide))
  have hd : (BitVec.ofNat 128 d.toNat).toNat = d.toNat :=
    Nat.mod_eq_of_lt (Nat.lt_trans d.toFin.isLt (by decide))
  rw [ha, hb, hc, hd]
  by_cases hab : a = b
  · subst hab
    simp only [beq_self_eq_true, ↓reduceIte, Bool.true_and, nat_compare_eq_iff]
    by_cases hcd : c = d
    · subst hcd; simp
    · have hne : c.toNat ≠ d.toNat :=
        fun h => hcd (UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h))
      simp [hne, beq_false_of_ne hcd]
  · have hne : a.toNat ≠ b.toNat :=
      fun h => hab (UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h))
    have hbvne : (BitVec.ofNat 128 a.toNat == BitVec.ofNat 128 b.toNat) = false := by
      cases h : (BitVec.ofNat 128 a.toNat == BitVec.ofNat 128 b.toNat) with
      | false => rfl
      | true =>
        have heq := congrArg BitVec.toNat (beq_iff_eq.mp h)
        rw [ha, hb] at heq
        exact absurd heq hne
    rw [hbvne, beq_false_of_ne hab]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and, nat_compare_eq_iff, hne, decide_false]

/-- Direct reduction of `lmEq` on two thin pointer scalars whose 8-byte bits are known. -/
theorem lmEq_thin_of_bits (sL sR : Miri.Memory.Scalar Provenance) (a b : UInt64)
    (hbL : sL.toBits (Size.ofBytes 8) = .ok (BitVec.ofNat 128 a.toNat))
    (hbR : sR.toBits (Size.ofBytes 8) = .ok (BitVec.ofNat 128 b.toNat)) :
    lmEq ⟨.scalar sL, layoutThin⟩ ⟨.scalar sR, layoutThin⟩ =
      .ok ⟨.scalar (.fromBool (a == b)), layoutBool⟩ := by
  have h1 : lmEq ⟨.scalar sL, layoutThin⟩ ⟨.scalar sR, layoutThin⟩ =
      lmRun (ExecutionScalar.pointerBinary lmLayout lmLeaves (fun _ _ => pure true)
        (fun _ => pure layoutUsize) () .Eq ⟨.scalar sL, layoutThin⟩ ⟨.scalar sR, layoutThin⟩) := rfl
  rw [h1]
  unfold lmRun ExecutionScalar.pointerBinary
  have hsz : Size.fromBits lmLayout.pointerWidth.bits = Size.ofBytes 8 := rfl
  simp only [hsz, hbL, hbR]
  have hlex := u64_lex_compare_eq a b 0 0
  have h0 : (0 : UInt64).toNat = 0 := rfl
  simp only [h0, beq_self_eq_true, Bool.and_true] at hlex
  exact congrArg
    (fun x => (Except.ok ⟨.scalar (.fromBool x), layoutBool⟩ : Except StepError (RvalueImmTy Provenance)))
    hlex

/-- Direct reduction of `lmEq` on two matching-layout wide `.scalarPair` pointers
whose data and metadata 8-byte bits are known. -/
theorem lmEq_pair_of_bits (layout : LocalLayout)
    (hlay : layout = layoutSlice ∨ layout = layoutDyn)
    (sL mL sR mR : Miri.Memory.Scalar Provenance) (a b c d : UInt64)
    (hbL : sL.toBits (Size.ofBytes 8) = .ok (BitVec.ofNat 128 a.toNat))
    (hmL : mL.toBits (Size.ofBytes 8) = .ok (BitVec.ofNat 128 c.toNat))
    (hbR : sR.toBits (Size.ofBytes 8) = .ok (BitVec.ofNat 128 b.toNat))
    (hmR : mR.toBits (Size.ofBytes 8) = .ok (BitVec.ofNat 128 d.toNat)) :
    lmEq ⟨.scalarPair sL mL, layout⟩ ⟨.scalarPair sR mR, layout⟩ =
      .ok ⟨.scalar (.fromBool (a == b && c == d)), layoutBool⟩ := by
  rcases hlay with rfl | rfl
  · have h1 : lmEq ⟨.scalarPair sL mL, layoutSlice⟩ ⟨.scalarPair sR mR, layoutSlice⟩ =
        lmRun (ExecutionScalar.pointerBinary lmLayout lmLeaves (fun _ _ => pure true)
          (fun _ => pure layoutUsize) () .Eq ⟨.scalarPair sL mL, layoutSlice⟩
          ⟨.scalarPair sR mR, layoutSlice⟩) := rfl
    rw [h1]
    unfold lmRun ExecutionScalar.pointerBinary
    have hsz : Size.fromBits lmLayout.pointerWidth.bits = Size.ofBytes 8 := rfl
    simp only [hsz, hbL, hmL, hbR, hmR]
    exact congrArg
      (fun x => (Except.ok ⟨.scalar (.fromBool x), layoutBool⟩ : Except StepError (RvalueImmTy Provenance)))
      (u64_lex_compare_eq a b c d)
  · have h1 : lmEq ⟨.scalarPair sL mL, layoutDyn⟩ ⟨.scalarPair sR mR, layoutDyn⟩ =
        lmRun (ExecutionScalar.pointerBinary lmLayout lmLeaves (fun _ _ => pure true)
          (fun _ => pure layoutUsize) () .Eq ⟨.scalarPair sL mL, layoutDyn⟩
          ⟨.scalarPair sR mR, layoutDyn⟩) := rfl
    rw [h1]
    unfold lmRun ExecutionScalar.pointerBinary
    have hsz : Size.fromBits lmLayout.pointerWidth.bits = Size.ofBytes 8 := rfl
    simp only [hsz, hbL, hmL, hbR, hmR]
    exact congrArg
      (fun x => (Except.ok ⟨.scalar (.fromBool x), layoutBool⟩ : Except StepError (RvalueImmTy Provenance)))
      (u64_lex_compare_eq a b c d)

/-- **Exact universal thin-pointer `==` law**: for EVERY pair of addresses and
EVERY pair of optional provenances, `lmEq` on thin pointers succeeds and returns
`addrL.bytes == addrR.bytes`. -/
theorem thinEq_eq (addrL addrR : Size) (provL provR : Option Provenance) :
    (do
      let sL ← (Miri.Memory.Scalar.fromMaybePointer lmLayout ⟨addrL, provL⟩).mapError
        ScalarOps.scalarError
      let sR ← (Miri.Memory.Scalar.fromMaybePointer lmLayout ⟨addrR, provR⟩).mapError
        ScalarOps.scalarError
      lmEq ⟨.scalar sL, layoutThin⟩ ⟨.scalar sR, layoutThin⟩) =
    .ok ⟨.scalar (.fromBool (addrL.bytes == addrR.bytes)), layoutBool⟩ := by
  obtain ⟨sL, hsL, hbL⟩ := scalar_fromMaybePointer_toBits addrL provL
  obtain ⟨sR, hsR, hbR⟩ := scalar_fromMaybePointer_toBits addrR provR
  simp only [hsL, hsR, Except.mapError, bind, Except.bind]
  exact lmEq_thin_of_bits sL sR addrL.bytes addrR.bytes hbL hbR

/-- **`==` on thin pointers erases provenance.** Comparing two pointers
gives the same result whatever their provenance: only the addresses are
compared. -/
theorem thinEq_provenance_erased (addrL addrR : Size) (provL provL' provR provR' : Provenance) :
    lmEq ⟨.scalar (Miri.Memory.Scalar.fromPointer lmLayout ⟨addrL, provL⟩), layoutThin⟩
        ⟨.scalar (Miri.Memory.Scalar.fromPointer lmLayout ⟨addrR, provR⟩), layoutThin⟩ =
      lmEq ⟨.scalar (Miri.Memory.Scalar.fromPointer lmLayout ⟨addrL, provL'⟩), layoutThin⟩
        ⟨.scalar (Miri.Memory.Scalar.fromPointer lmLayout ⟨addrR, provR'⟩), layoutThin⟩ := rfl

/-- Reduction of `lmSlice` given succeeding data and length scalars. -/
private theorem lmSlice_of_ok (ptr : Pointer (Option Provenance)) (len : UInt64)
    (s m : Miri.Memory.Scalar Provenance)
    (hs : Miri.Memory.Scalar.fromMaybePointer lmLayout ptr = .ok s)
    (hm : Miri.Memory.Scalar.fromUInt (BitVec.ofNat 128 len.toNat) (Size.ofBytes 8) = .ok m) :
    lmSlice ptr len = .ok ⟨.scalarPair s m, layoutSlice⟩ := by
  unfold lmSlice Immediate.newSlice
  have hsz : Size.fromBits lmLayout.pointerWidth.bits = Size.ofBytes 8 := rfl
  simp only [hsz, hs, hm, Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]

/-- Reduction of `lmDyn` given succeeding data and vtable scalars. -/
private theorem lmDyn_of_ok (ptr vt : Pointer (Option Provenance))
    (s v : Miri.Memory.Scalar Provenance)
    (hs : Miri.Memory.Scalar.fromMaybePointer lmLayout ptr = .ok s)
    (hv : Miri.Memory.Scalar.fromMaybePointer lmLayout vt = .ok v) :
    lmDyn ptr vt = .ok ⟨.scalarPair s v, layoutDyn⟩ := by
  unfold lmDyn Immediate.newDynTrait
  simp only [hs, hv, Except.mapError, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]

/-- **Universal full wide slice `==` law (`rust#166144`)**: `ScalarOps.binary .Eq`
on two slice `.scalarPair` pointers compares BOTH the address AND the length
lexicographically, erasing provenance. -/
theorem wideEq_slice_eq (addrL addrR : Size) (provL provR : Option Provenance)
    (lenL lenR : UInt64) :
    (do
      let l ← lmSlice ⟨addrL, provL⟩ lenL
      let r ← lmSlice ⟨addrR, provR⟩ lenR
      lmEq l r) =
    .ok ⟨.scalar (.fromBool (addrL.bytes == addrR.bytes && lenL == lenR)), layoutBool⟩ := by
  obtain ⟨sL, hsL, hbL⟩ := scalar_fromMaybePointer_toBits addrL provL
  obtain ⟨sR, hsR, hbR⟩ := scalar_fromMaybePointer_toBits addrR provR
  obtain ⟨mL, hmL, hmbL⟩ := scalar_fromUInt64_toBits lenL
  obtain ⟨mR, hmR, hmbR⟩ := scalar_fromUInt64_toBits lenR
  rw [lmSlice_of_ok _ _ _ _ hsL hmL, lmSlice_of_ok _ _ _ _ hsR hmR]
  exact lmEq_pair_of_bits layoutSlice (Or.inl rfl) sL mL sR mR addrL.bytes addrR.bytes lenL lenR
    hbL hmbL hbR hmbR

/-- **Universal full wide trait-object `==` law (`rust#166144`)**:
`ScalarOps.binary .Eq` on two `dyn Trait` `.scalarPair` pointers compares BOTH
the data address AND the vtable address lexicographically, erasing both
provenances. -/
theorem wideEq_dyn_eq (addrL addrR vtL vtR : Size)
    (provL provR vtProvL vtProvR : Option Provenance) :
    (do
      let l ← lmDyn ⟨addrL, provL⟩ ⟨vtL, vtProvL⟩
      let r ← lmDyn ⟨addrR, provR⟩ ⟨vtR, vtProvR⟩
      lmEq l r) =
    .ok ⟨.scalar (.fromBool (addrL.bytes == addrR.bytes && vtL.bytes == vtR.bytes)), layoutBool⟩ := by
  obtain ⟨sL, hsL, hbL⟩ := scalar_fromMaybePointer_toBits addrL provL
  obtain ⟨sR, hsR, hbR⟩ := scalar_fromMaybePointer_toBits addrR provR
  obtain ⟨vL, hvL, hvbL⟩ := scalar_fromMaybePointer_toBits vtL vtProvL
  obtain ⟨vR, hvR, hvbR⟩ := scalar_fromMaybePointer_toBits vtR vtProvR
  rw [lmDyn_of_ok _ _ _ _ hsL hvL, lmDyn_of_ok _ _ _ _ hsR hvR]
  exact lmEq_pair_of_bits layoutDyn (Or.inr rfl) sL vL sR vR addrL.bytes addrR.bytes
    vtL.bytes vtR.bytes hbL hvbL hbR hvbR

/-- **Universal closed-form `ptr::addr_eq` law on heterogeneous wide pointers
(`rust#166144`)**: casting `*const [u8]` and `*const dyn Trait` to `*const ()`
via `Cast.ptrToPtr` and comparing via `ExecutionScalar.pointerBinary .Eq`
returns `addrL.bytes == addrR.bytes`, completely independent of slice length,
vtable pointer, and both provenances. -/
theorem addrEq_hetero_eq (addrL addrR vtR : Size)
    (provL provR vtProvR : Option Provenance) (lenL : UInt64) :
    (do
      let l ← lmSlice ⟨addrL, provL⟩ lenL
      let r ← lmDyn ⟨addrR, provR⟩ ⟨vtR, vtProvR⟩
      lmAddrEq l r) =
    .ok ⟨.scalar (.fromBool (addrL.bytes == addrR.bytes)), layoutBool⟩ := by
  obtain ⟨sL, hsL, hbL⟩ := scalar_fromMaybePointer_toBits addrL provL
  obtain ⟨sR, hsR, hbR⟩ := scalar_fromMaybePointer_toBits addrR provR
  obtain ⟨mL, hmL, _⟩ := scalar_fromUInt64_toBits lenL
  obtain ⟨vR, hvR, _⟩ := scalar_fromMaybePointer_toBits vtR vtProvR
  rw [lmSlice_of_ok _ _ _ _ hsL hmL, lmDyn_of_ok _ _ _ _ hsR hvR]
  dsimp only [bind, Except.bind]
  rw [(addrEq_metadata_erased sL sR mL vR).2.2.1]
  exact lmEq_thin_of_bits sL sR addrL.bytes addrR.bytes hbL hbR

/-- **Universal separation of `addr_eq` and `==` on slices**: at equal addresses
and distinct lengths, `lmAddrEq` is `true` while `lmEq` is `false`. -/
theorem addrEq_true_wideEq_false_slice (addr : Size) (provL provR : Option Provenance)
    (lenL lenR : UInt64) (hne : lenL ≠ lenR) :
    (do let l ← lmSlice ⟨addr, provL⟩ lenL; let r ← lmSlice ⟨addr, provR⟩ lenR; lmAddrEq l r) =
      .ok ⟨.scalar (.fromBool true), layoutBool⟩ ∧
    (do let l ← lmSlice ⟨addr, provL⟩ lenL; let r ← lmSlice ⟨addr, provR⟩ lenR; lmEq l r) =
      .ok ⟨.scalar (.fromBool false), layoutBool⟩ := by
  refine ⟨?_, ?_⟩
  · obtain ⟨sL, hsL, hbL⟩ := scalar_fromMaybePointer_toBits addr provL
    obtain ⟨sR, hsR, hbR⟩ := scalar_fromMaybePointer_toBits addr provR
    obtain ⟨mL, hmL, _⟩ := scalar_fromUInt64_toBits lenL
    obtain ⟨mR, hmR, _⟩ := scalar_fromUInt64_toBits lenR
    rw [lmSlice_of_ok _ _ _ _ hsL hmL, lmSlice_of_ok _ _ _ _ hsR hmR]
    dsimp only [bind, Except.bind]
    rw [(addrEq_metadata_erased sL sR mL mR).1,
      lmEq_thin_of_bits sL sR addr.bytes addr.bytes hbL hbR, beq_self_eq_true]
  · rw [wideEq_slice_eq]
    simp [beq_false_of_ne hne]

/-- **Universal separation of `addr_eq` and `==` on trait objects**: at equal
data addresses and distinct vtable addresses, `lmAddrEq` is `true` while `lmEq`
is `false`. -/
theorem addrEq_true_wideEq_false_dyn (addr vtL vtR : Size)
    (provL provR vtProvL vtProvR : Option Provenance) (hne : vtL.bytes ≠ vtR.bytes) :
    (do
      let l ← lmDyn ⟨addr, provL⟩ ⟨vtL, vtProvL⟩
      let r ← lmDyn ⟨addr, provR⟩ ⟨vtR, vtProvR⟩
      lmAddrEq l r) = .ok ⟨.scalar (.fromBool true), layoutBool⟩ ∧
    (do
      let l ← lmDyn ⟨addr, provL⟩ ⟨vtL, vtProvL⟩
      let r ← lmDyn ⟨addr, provR⟩ ⟨vtR, vtProvR⟩
      lmEq l r) = .ok ⟨.scalar (.fromBool false), layoutBool⟩ := by
  refine ⟨?_, ?_⟩
  · obtain ⟨sL, hsL, hbL⟩ := scalar_fromMaybePointer_toBits addr provL
    obtain ⟨sR, hsR, hbR⟩ := scalar_fromMaybePointer_toBits addr provR
    obtain ⟨vL, hvL, _⟩ := scalar_fromMaybePointer_toBits vtL vtProvL
    obtain ⟨vR, hvR, _⟩ := scalar_fromMaybePointer_toBits vtR vtProvR
    rw [lmDyn_of_ok _ _ _ _ hsL hvL, lmDyn_of_ok _ _ _ _ hsR hvR]
    dsimp only [bind, Except.bind]
    rw [(addrEq_metadata_erased sL sR vL vR).2.1,
      lmEq_thin_of_bits sL sR addr.bytes addr.bytes hbL hbR, beq_self_eq_true]
  · rw [wideEq_dyn_eq]
    simp [beq_false_of_ne hne]

/-- **`==` on a slice pointer and a trait-object pointer is rejected.** For
every operand value, `ScalarOps.binary` at `Eq` on operands of the two wide
pointer types fails with `invalidProgram`: their ABIs differ. `addr_eq` on the
same operands is defined (`addrEq_metadata_erased`). -/
theorem wideEq_hetero_invalidProgram (a b c d : Miri.Memory.Scalar Provenance) :
    lmEq ⟨.scalarPair a b, layoutSlice⟩ ⟨.scalarPair c d, layoutDyn⟩ =
      .error (.invalidProgram "pointer comparison backend mismatch") ∧
    lmEq ⟨.scalarPair c d, layoutDyn⟩ ⟨.scalarPair a b, layoutSlice⟩ =
      .error (.invalidProgram "pointer comparison backend mismatch") := ⟨rfl, rfl⟩

/-- Comparing any wide pointer (`Slice` or `Dyn`) with a thin pointer in either
order is rejected with `invalidProgram`. -/
theorem wideEq_thin_wide_invalidProgram (a b c : Miri.Memory.Scalar Provenance) :
    lmEq ⟨.scalarPair a b, layoutSlice⟩ ⟨.scalar c, layoutThin⟩ =
      .error (.invalidProgram "pointer comparison backend mismatch") ∧
    lmEq ⟨.scalar c, layoutThin⟩ ⟨.scalarPair a b, layoutSlice⟩ =
      .error (.invalidProgram "pointer comparison backend mismatch") ∧
    lmEq ⟨.scalarPair a b, layoutDyn⟩ ⟨.scalar c, layoutThin⟩ =
      .error (.invalidProgram "pointer comparison backend mismatch") ∧
    lmEq ⟨.scalar c, layoutThin⟩ ⟨.scalarPair a b, layoutDyn⟩ =
      .error (.invalidProgram "pointer comparison backend mismatch") := ⟨rfl, rfl, rfl, rfl⟩

/-! ### Uninitialized heap memory -/

/-- Reading a range that the initialization mask reports uninitialized is
undefined behavior under vendored `MemoryErrors.allocation`, for every
allocation (`LeanMiriSpec.MemoryLemmas`: `Allocation.readScalar_uninit_err`). -/
theorem readScalar_uninit_ub {E : Type} (allocation : Allocation Provenance E)
    (range bad : AllocRange) (readProvenance : Bool)
    (h : allocation.initializationMask.isRangeInitialized range = .ok (.error bad)) :
    ∃ e, allocation.readScalar lmLayout range readProvenance = .error e ∧
      lmObsOfStep (MemoryErrors.allocation e) = .ub :=
  ⟨_, Allocation.readScalar_uninit_err allocation lmLayout range bad readProvenance h, rfl⟩

/-! ## §4. Vacuity, capstone, and axiom audit -/

/-- `deallocatePtrWith_nonzero_offset` is not vacuous: in the harness, the
pointer `ptr + 4` into a fresh 8-byte allocation resolves with offset `4`, so
every hypothesis of the law holds and the deallocation fails with exactly
`nonzeroAllocationOffset`. -/
theorem deallocatePtrWith_nonzero_offset_witness :
    lmCaseFailure false 9 =
      some (.dealloc (.nonzeroAllocationOffset "deallocate" lmFirstId (Size.ofBytes 4))) ∧
    (lmResolve MemoryState.empty { treeBorrows := false }
        ⟨Size.ofBytes (lmBaseAddr lmFirstId + 4), some (.concrete lmFirstId (lmRootTag lmFirstId))⟩
        0).outcome = .ok (lmFirstId, Size.ofBytes 4, .concrete (lmRootTag lmFirstId)) ∧
    ((Size.ofBytes 4).bytes != 0) = true := by
  refine ⟨?_, rfl, rfl⟩
  rw [lmCaseFailureU.eq_src]
  decide +kernel

/-- `deallocatePtrWith_dangling` is not vacuous: a pointer without provenance
does not resolve, and its deallocation fails with exactly `danglingPointer`. -/
theorem deallocatePtrWith_dangling_witness :
    (lmResolve MemoryState.empty { treeBorrows := false } (lmAddr 4096) 0).outcome =
      .error 4096 ∧
    (MemoryLifecycle.deallocatePtrWith (MemoryState.empty : LmMem) { treeBorrows := false }
        (lmAddr 4096) (some (Size.ofBytes 8, Align.EIGHT)) (.machine .rust)
        lmDeallocHooks).outcome = .error (.danglingPointer 4096) :=
  ⟨rfl, (deallocatePtrWith_dangling _ _ _ _ _ lmDeallocHooks 4096 rfl).1⟩

/-- `deallocatePtrWith_global` is not vacuous (`rust#166221`): registering a
global in `MemoryState.empty.pushGlobal` and attempting to deallocate it yields
`MemoryLifecycleError.globalAllocationDeallocation`. -/
theorem deallocatePtrWith_global_witness :
    let g : GlobalAllocation := ⟨lmFirstId, .static, Size.ofBytes 4, Align.ONE, .Not, none⟩
    let mem : LmMem := (MemoryState.empty : LmMem).pushGlobal g
    let ptr : Pointer (Option Provenance) :=
      ⟨Size.ofBytes (lmBaseAddr lmFirstId), some (.concrete lmFirstId (lmRootTag lmFirstId))⟩
    ∃ kind,
      (MemoryLifecycle.deallocatePtrWith mem { treeBorrows := false } ptr
        (some (Size.ofBytes 4, Align.ONE)) (.machine .rust) lmDeallocHooks).outcome =
        .error (.globalAllocationDeallocation lmFirstId kind) := by
  intro g mem ptr
  have hcont : mem.hasGlobalId lmFirstId = true := by
    unfold MemoryState.hasGlobalId mem MemoryState.pushGlobal MemoryState.empty
    rw [KeyedArray.contains_rows]
    simp [KeyedArray.toArray, KeyedArray.push, KeyedArray.empty, g]
  obtain ⟨g', hfind⟩ := KeyedArray.find_of_contains _ lmFirstId.value hcont
  refine ⟨g'.kind, ?_⟩
  have hres : (lmDeallocHooks.resolvePointer mem
      (lmDeallocHooks.synchronizeMemory mem { treeBorrows := false }) ptr 0).outcome =
      .ok (lmFirstId, Size.ZERO, .concrete (lmRootTag lmFirstId)) := by
    change (if lmBaseAddr lmFirstId < lmBaseAddr lmFirstId then
        Except.error (lmBaseAddr lmFirstId)
      else
        Except.ok (lmFirstId, Size.ofBytes (lmBaseAddr lmFirstId - lmBaseAddr lmFirstId),
          ProvenanceExtra.concrete (lmRootTag lmFirstId))) = _
    decide
  exact (deallocatePtrWith_global mem { treeBorrows := false } ptr
    (some (Size.ofBytes 4, Align.ONE)) (.machine .rust) lmDeallocHooks
    lmFirstId (.concrete (lmRootTag lmFirstId)) g' hres rfl hfind).1

/-- `leakCheck_take_sound` is not vacuous: on the memory left by an unfreed
Rust heap allocation, `take` reports exactly that allocation, and on the
memory left by an unfreed global allocation it reports nothing. -/
theorem leakCheck_take_witness :
    lmCaseFailure false 15 = some (.leak [lmFirstId]) ∧
    lmCaseFailure true 15 = some (.leak [lmFirstId]) ∧
    lmCaseFailure false 17 = none ∧ lmCaseFailure true 17 = none := by
  rw [lmCaseFailureU.eq_src]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- `addrEq_metadata_erased` and `wideEq_hetero_invalidProgram` are not
vacuous: the slice and trait-object operands of cases `23` to `28` are built
by `Immediate::new_slice` and `Immediate::new_dyn_trait`, so they are
`scalarPair`s of the two layouts the laws quantify over. -/
theorem wide_operands_witness :
    (∃ a b, lmSlice (lmAddr 8192) 3 = .ok ⟨.scalarPair a b, layoutSlice⟩) ∧
    (∃ a b, lmDyn (lmAddr 8192) (lmAddr 36864) = .ok ⟨.scalarPair a b, layoutDyn⟩) :=
  ⟨⟨_, _, rfl⟩, ⟨_, _, rfl⟩⟩

/-! ### Episode 1 capstone -/

/-- **Episode 1 capstone**: the headline guarantees of this module in one
statement.
1. `take_leaked_allocations` only reports live memory whose kind may not
   leak; Rust heap memory may not leak and global memory may (`rust#166221`).
2. `deallocationError` classifies exactly the seven `deallocate_ptr`
   failures as undefined behavior.
3. `Align::from_bytes` accepts the powers of two up to `2^29` and rejects
   `2^30` as too large (and every non-power-of-two across all `2^64` values).
4. `ptr::addr_eq` erases metadata (`Cast.ptrToPtr` then `pointerBinary`),
   `==` on thin pointers erases provenance, full wide `==` compares both
   address and metadata lexicographically, and `==` on a slice pointer and a
   trait-object pointer is rejected (`rust#166144`).
5. `BorrowTree.deallocateBorrowRange` on the over-aligned block via vendored
   `RetagPipeline.retagPointerValue` (`rust#165833`): weak protector
   `Deallocated`, active strong protector on an accessed `Frozen` child
   `AccessFailure`, released protector `Deallocated`, unprotected `Frozen`
   child tag `AccessFailure`, strongly protected `Cell` child `Deallocated`.
6. The kernel-evaluated 30-case table in both modes, and both threaded
   traces. -/
theorem ep1_lean_miri_heap_wide_capstone :
    ((∀ (E : Type) (memory memory' : MemoryState Provenance E MiriMemoryKind)
        (staticRoots : Array AllocId)
        (leaked : Array (AllocId × LocalAllocation Provenance E MiriMemoryKind)),
        LeakCheck.take memory staticRoots = .ok (memory', leaked) →
        ∀ entry ∈ leaked, entry ∈ memory.live ∧ LeakCheck.mayLeak entry.2.kind = false) ∧
      LeakCheck.mayLeak (.machine .rust) = false ∧ LeakCheck.mayLeak (.machine .global) = true) ∧
    (∀ error : MemoryLifecycleError,
      lmObsOfStep (AllocationMachine.deallocationError error) = .ub ↔
        (∃ address, error = .danglingPointer address) ∨
        (∃ operation id offset, error = .nonzeroAllocationOffset operation id offset) ∨
        (∃ id kind, error = .globalAllocationDeallocation id kind) ∨
        (∃ id, error = .useAfterFree id) ∨
        (∃ id, error = .immutableAllocation id) ∨
        (∃ id, error = .memoryKindMismatch id) ∨
        (∃ id size requested align requestedAlign,
          error = .layoutMismatch id size requested align requestedAlign)) ∧
    ((∀ bytes al, Align.fromBytes bytes = .ok al ↔
        (bytes = 0 ∧ al = Align.ONE) ∨
        (∃ k, k < 30 ∧ bytes = UInt64.ofNat (2 ^ k) ∧ al = ⟨k⟩)) ∧
      Align.fromBytes 1073741824 = .error (.tooLarge 1073741824)) ∧
    ((∀ dataL dataR metaL metaR : Miri.Memory.Scalar Provenance,
        lmAddrEq ⟨.scalarPair dataL metaL, layoutSlice⟩ ⟨.scalarPair dataR metaR, layoutDyn⟩ =
          lmEq ⟨.scalar dataL, layoutThin⟩ ⟨.scalar dataR, layoutThin⟩) ∧
      (∀ (addrL addrR : Size) (provL provR : Option Provenance) (lenL lenR : UInt64),
        (do let l ← lmSlice ⟨addrL, provL⟩ lenL; let r ← lmSlice ⟨addrR, provR⟩ lenR; lmEq l r) =
          .ok ⟨.scalar (.fromBool (addrL.bytes == addrR.bytes && lenL == lenR)), layoutBool⟩) ∧
      (∀ (addrL addrR : Size) (provL provL' provR provR' : Provenance),
        lmEq ⟨.scalar (Miri.Memory.Scalar.fromPointer lmLayout ⟨addrL, provL⟩), layoutThin⟩
            ⟨.scalar (Miri.Memory.Scalar.fromPointer lmLayout ⟨addrR, provR⟩), layoutThin⟩ =
          lmEq ⟨.scalar (Miri.Memory.Scalar.fromPointer lmLayout ⟨addrL, provL'⟩), layoutThin⟩
            ⟨.scalar (Miri.Memory.Scalar.fromPointer lmLayout ⟨addrR, provR'⟩), layoutThin⟩) ∧
      (∀ a b c d : Miri.Memory.Scalar Provenance,
        lmEq ⟨.scalarPair a b, layoutSlice⟩ ⟨.scalarPair c d, layoutDyn⟩ =
          .error (.invalidProgram "pointer comparison backend mismatch"))) ∧
    (lmScenarioDeallocStatus .globalBox lmFrozenFacts .Box .FnEntry true false false true =
        some .Deallocated ∧
      lmScenarioDeallocStatus .reference lmFrozenFacts .Shared .FnEntry true true false false =
        some (.AccessFailure (.AccessFailure ⟨0, 4⟩
          (.TransitionError 1 (.ProtectedDisabled .Frozen)))) ∧
      lmScenarioDeallocStatus .reference lmFrozenFacts .Shared .FnEntry true true true false =
        some .Deallocated ∧
      lmScenarioDeallocStatus .reference lmFrozenFacts .Shared .Default true false false true =
        some (.AccessFailure (.AccessFailure ⟨0, 32⟩
          (.TransitionError 1 (.ChildAccessForbidden .Frozen)))) ∧
      lmScenarioDeallocStatus .reference lmCellFacts .Shared .FnEntry false false false false =
        some .Deallocated) ∧
    ((List.range 30).map (lmHeapWideObserve false) =
        [.okAlloc 0 1, .okAlloc 0 32, .okRoundTrip 3735928559, .okRoundTrip 81985529216486895,
         .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub,
         .memoryLeak, .okDealloc, .okDealloc,
         .okDealloc, .okDealloc, .okDealloc, .okDealloc, .okDealloc,
         .okBool true, .okBool false, .okBool true, .okBool false, .okBool true,
         .invalidOrUnsupported, .ub] ∧
      (List.range 30).map (lmHeapWideObserve true) =
        [.okAlloc 0 1, .okAlloc 0 32, .okRoundTrip 3735928559, .okRoundTrip 81985529216486895,
         .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub,
         .memoryLeak, .okDealloc, .okDealloc,
         .okDealloc, .ub, .okDealloc, .ub, .okDealloc,
         .okBool true, .okBool false, .okBool true, .okBool false, .okBool true,
         .invalidOrUnsupported, .ub]) ∧
    (lmHeapLifecycleTrace false =
        [.okAlloc 32 32, .okRoundTrip 14627333968688404088, .memoryLeak, .okBool true,
         .okDealloc, .ub] ∧
      lmHeapLifecycleTrace true =
        [.okAlloc 32 32, .okRoundTrip 14627333968688404088, .memoryLeak, .okBool true,
         .okDealloc, .ub]) ∧
    (lmProtectorDeallocTrace false = [.okRoundTrip 42, .okBool true, .okDealloc, .okDealloc] ∧
      lmProtectorDeallocTrace true = [.okRoundTrip 42, .okBool true, .ub]) := by
  refine ⟨⟨?_, rfl, rfl⟩, ?_, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact fun E memory memory' staticRoots leaked h =>
      leakCheck_take_sound memory memory' staticRoots leaked h
  · exact deallocationError_ub_iff
  · exact align_fromBytes_ok_iff
  · exact align_fromBytes_boundary.2.1
  · exact fun dataL dataR metaL metaR => (addrEq_metadata_erased dataL dataR metaL metaR).2.2.1
  · exact wideEq_slice_eq
  · exact thinEq_provenance_erased
  · exact fun a b c d => (wideEq_hetero_invalidProgram a b c d).1
  · obtain ⟨h1, h2, _, h4, h5, h6⟩ := deallocateBorrowRange_protector_laws
    exact ⟨h1, h2, h4, h5, h6⟩
  · exact lmHeapWideObserve_table
  · exact lmHeapLifecycleTrace_table
  · exact lmProtectorDeallocTrace_table

/-! ### Axiom and import audit -/

section AxiomAudit

open Lean Elab Command

/-! Fail the build unless
1. this module's direct imports are exactly `Lean`, vendored `Miri.*`
   modules, and `LeanMiriSpec.MemoryLemmas` (plus the implicit `Init`);
2. no `MiniRustSpec.*`, `Anneal.*`, or `Trusted.*` module is imported, even
   transitively, and no declaration refers to any constant from those prefixes;
3. no file under `lean-miri/vendor/` is touched: every `Miri.*` constant used
   here is the vendored one (the module only *imports* `Miri.*`);
4. every declaration of this module (`env.constants.map₂`) depends only on
   Lean's standard axioms `propext`, `Quot.sound`, and `Classical.choice`: no
   `sorryAx`, no `Lean.ofReduceBool`, and no `Lean.trustCompiler`. -/

run_cmd do
  let env ← getEnv
  for imp in env.header.imports do
    let m := imp.module
    unless m == `Init || m == `Lean || (`Miri).isPrefixOf m || m == `LeanMiriSpec.MemoryLemmas do
      throwError "import-isolation violation: direct import of {m}"
  for modName in env.header.moduleNames do
    if (`MiniRustSpec).isPrefixOf modName || (`Anneal).isPrefixOf modName ||
        (`Trusted).isPrefixOf modName then
      throwError "import-isolation violation: {modName} must not be imported"
  let forbidden (modName : Lean.Name) : Bool :=
    (`MiniRustSpec).isPrefixOf modName || (`Anneal).isPrefixOf modName ||
      (`Trusted).isPrefixOf modName
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  for (c, info) in env.constants.map₂.toList do
    let used := info.type.getUsedConstants ++
      (match info.value? (allowOpaque := true) with
        | some v => v.getUsedConstants
        | none => #[])
    for u in used do
      if let some idx := env.getModuleIdxFor? u then
        let modName := env.header.moduleNames[idx.toNat]!
        if forbidden modName then
          throwError "dependency-isolation violation: {c} refers to {u} of {modName}"
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      if a == ``sorryAx then throwError "{c} depends on sorryAx"
      if a == ``Lean.ofReduceBool || a == ``Lean.trustCompiler then
        throwError "{c} depends on {a} (compiler-trusting evaluation)"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} depends on non-standard axiom {a}"
    checked := checked + 1
    if (`LeanMiriSpec.HeapAllocAndWidePtrLM).isPrefixOf c then
      if let .thmInfo _ := info then theorems := theorems + 1
  if theorems < 89 then
    throwError "axiom audit is vacuous: only {theorems} theorems of LeanMiriSpec.HeapAllocAndWidePtrLM seen"
  logInfo m!"LeanMiriSpec.HeapAllocAndWidePtrLM: {checked} declarations ({theorems} theorems) depend only on propext, Quot.sound, Classical.choice (sorry_free=true, ofReduceBool_free=true, import_isolated=true)"

end AxiomAudit

end LeanMiriSpec.HeapAllocAndWidePtrLM
