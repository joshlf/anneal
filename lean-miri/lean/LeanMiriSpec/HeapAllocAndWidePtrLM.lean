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
import Miri.TreeBorrows.MachineMemoryHooks
import LeanMiriSpec.MemoryLemmas

/-!
# Vendored Miri: heap allocation, deallocation, leak check, and `ptr::addr_eq`

This module is about the vendored, unmodified `lean-miri` only. It studies
`Miri.Memory.MemoryLifecycle.{allocatePtr, deallocatePtrWith, deallocatePtr}`
(rustc `interpret/memory.rs`), the classification
`Miri.Interpreter.AllocationMachine.deallocationError`, the Tree Borrows
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
  /-- `check_alloc_request`: `Align::from_bytes` rejected the alignment. -/
  | allocAlign (error : AlignError)
  /-- `check_alloc_request`: the size exceeds `isize::MAX`. -/
  | allocTooLarge (size : Nat)
  /-- `Memory::allocate_ptr` failed. -/
  | allocLifecycle (error : MemoryLifecycleError)
  /-- The `dealloc` shim's `Align::from_bytes(align).unwrap()` failed. -/
  | deallocAlign (error : AlignError)
  /-- `Memory::deallocate_ptr` failed (classified by `deallocationError`). -/
  | dealloc (error : MemoryLifecycleError)
  /-- Tree Borrows rejected the deallocation. -/
  | treeDealloc (status : BorrowTree.BorrowTreeDeallocStatus)
  /-- Tree Borrows rejected a read or write access. -/
  | treeAccess (status : BorrowTree.BorrowTreeAccessStatus)
  /-- `Tree::new_child` failed. -/
  | treeRetag (error : BorrowTree.ChildInsertError)
  /-- Releasing a protector failed. -/
  | protectorRelease (status : BorrowTree.ProtectorReleaseStatus)
  /-- An access through a pointer without (concrete) provenance. -/
  | danglingAccess (address : UInt64)
  /-- An access to an allocation that is not live. -/
  | useAfterFree (allocId : AllocId)
  /-- An access outside the bounds of its allocation. -/
  | outOfBounds (allocId : AllocId) (offset size : UInt64)
  /-- `Allocation::read_scalar` or `write_scalar` failed. -/
  | allocation (error : AllocError)
  /-- A scalar conversion failed. -/
  | scalar (error : ScalarError)
  /-- A cast or scalar operator failed. -/
  | step (error : StepError)
  /-- `take_leaked_allocations` reported these allocations. -/
  | leak (allocIds : List AllocId)
  /-- The harness itself was used outside its domain. -/
  | harness (message : String)
  deriving DecidableEq

/-- The borrow tracker state threaded through the lifecycle hooks. -/
structure LmCtx where
  /-- Whether Tree Borrows is enabled. -/
  treeBorrows : Bool
  /-- The borrow tracker's protected tags. -/
  protectedTags : ProtectedTags := {}
  /-- The typed failure of a machine hook, as `AllocationMachine.deallocate`
  keeps one in `pendingError`. -/
  pending : Option LmFailure := none

/-- The harness state. -/
structure LmState where
  /-- The memory. -/
  mem : LmMem
  /-- The borrow tracker state. -/
  ctx : LmCtx

/-- The initial state: empty memory. -/
def lmInit (tb : Bool) : LmState := { mem := MemoryState.empty, ctx := { treeBorrows := tb } }

/-- Little-endian, 64-bit. -/
def lmLayout : TargetDataLayout := ⟨.little, .w64⟩

/-- The base address of an allocation: `id * 2^32`, so every allocation is
aligned to every supported alignment and allocations of less than `2^32`
bytes do not overlap. -/
def lmBaseAddr (id : AllocId) : UInt64 := id.value * 4294967296

/-- The root tag of an allocation. -/
def lmRootTag (id : AllocId) : BorTag := ⟨id.value, id.nonzero⟩

/-- `isize::MAX` on a 64-bit target. -/
def lmIsizeMax : Nat := 9223372036854775807

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

/-- `init_local_allocation`: a fresh Tree Borrows tree rooted at the
allocation's root tag. -/
def lmInitExtra (memory : LmMem) (ctx : LmCtx) (id : AllocId) (_kind : MemoryKind MiriMemoryKind)
    (size : Size) (_align : Align) :
    MemoryStateHookResult Provenance BorrowTree MiriMemoryKind LmCtx BorrowTree :=
  ⟨memory, ctx, .ok (BorrowTree.new (lmRootTag id) size)⟩

/-- `adjust_alloc_root_pointer`: the allocation's base address with its root
tag. -/
def lmAdjustRoot (memory : LmMem) (ctx : LmCtx) (id : AllocId)
    (_kind : MemoryKind MiriMemoryKind) :
    MemoryStateHookResult Provenance BorrowTree MiriMemoryKind LmCtx (Pointer Provenance) :=
  ⟨memory, ctx, .ok ⟨Size.ofBytes (lmBaseAddr id), .concrete id (lmRootTag id)⟩⟩

/-- `Memory::allocate_ptr` with the harness hooks: zeroed backing storage,
uninitialized contents, `GLOBAL_KIND = MiriMemoryKind::Global`, and objects of
at most `isize::MAX` bytes. -/
def lmAllocatePtr (st : LmState) (size : Size) (align : Align) (kind : MemoryKind MiriMemoryKind)
    (globalKind : Option (MemoryKind MiriMemoryKind)) :
    MemoryLifecycleResult Provenance BorrowTree MiriMemoryKind LmCtx (Pointer Provenance) :=
  MemoryLifecycle.allocatePtr st.mem st.ctx (fun _ ctx => ctx) size align kind .Uninit
    (Size.ofBytes (UInt64.ofNat lmIsizeMax)) globalKind
    (fun size _ => some (Array.replicate size.bytes.toNat 0)) lmInitExtra lmAdjustRoot

/-- An allocation of `kind`: `Memory::allocate_ptr`. A request for the global
kind models the state `get_alloc_raw_mut` leaves when it materializes a
mutable static (a live allocation of `MemoryKind::Machine(GLOBAL_KIND)`), so
only then is `GLOBAL_KIND` not passed to the dynamic-allocation check. -/
def lmAllocateKind (st : LmState) (size align : Nat) (kind : MemoryKind MiriMemoryKind) :
    Except LmFailure (Pointer (Option Provenance) × LmState) :=
  match Align.fromBytes (UInt64.ofNat align) with
  | .error e => .error (.allocAlign e)
  | .ok al =>
    let globalKind : Option (MemoryKind MiriMemoryKind) :=
      if kind = .machine .global then none else some (.machine .global)
    let r := lmAllocatePtr st (Size.ofBytes (UInt64.ofNat size)) al kind globalKind
    match r.outcome with
    | .ok ptr => .ok (ptr.withOptionalProvenance, { mem := r.memory, ctx := r.hooks })
    | .error e => .error (.allocLifecycle e)

/-- The Rust heap allocation shim (`__rust_alloc`): `check_alloc_request`
(`Align::from_bytes` must accept the alignment and the size must not exceed
`isize::MAX`, both checked before any storage is created), then
`Memory::allocate_ptr` with `MiriMemoryKind::Rust`. -/
def lmAllocate (st : LmState) (size align : Nat) :
    Except LmFailure (Pointer (Option Provenance) × LmState) :=
  match Align.fromBytes (UInt64.ofNat align) with
  | .error e => .error (.allocAlign e)
  | .ok _ =>
    if size ≤ lmIsizeMax then lmAllocateKind st size align (.machine .rust)
    else .error (.allocTooLarge size)

/-- `ptr_get_alloc_id` for the deallocation: a pointer with concrete
provenance resolves to its allocation, its offset from the allocation's base
address, and its tag; a pointer without provenance is dangling. -/
def lmResolve (memory : LmMem) (ctx : LmCtx) (ptr : Pointer (Option Provenance)) (_size : Int) :
    PointerResolutionResult Provenance BorrowTree MiriMemoryKind LmCtx ProvenanceExtra :=
  match ptr.provenance with
  | some (.concrete id tag) =>
    ⟨memory, ctx, .ok (id, Size.ofBytes (ptr.offset.bytes - lmBaseAddr id), .concrete tag)⟩
  | some .wildcard => ⟨memory, ctx, .error ptr.offset.bytes⟩
  | none => ⟨memory, ctx, .error ptr.offset.bytes⟩

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
      (lmMachineHooks ctx.protectedTags) allocation pointer allocId provenance size align kind
    match r.outcome with
    | .ok () => ⟨memory, ctx, .ok ()⟩
    | .error message =>
      ⟨memory,
        { ctx with pending := some (.treeDealloc
            (allocation.extra.deallocateBorrowRange provenance Size.ZERO size
              ctx.protectedTags).status) },
        .error message⟩
  else
    ⟨memory, ctx, .ok ()⟩

/-- The deallocation hooks. -/
def lmDeallocHooks :
    MemoryDeallocationHooks Provenance BorrowTree MiriMemoryKind LmCtx ProvenanceExtra :=
  { synchronizeMemory := fun _ ctx => ctx
    resolvePointer := lmResolve
    beforeDeallocation := lmBeforeDeallocation }

/-- The Rust heap deallocation shim (`__rust_dealloc`): `Align::from_bytes`,
then `Memory::deallocate_ptr` with the claimed layout and
`MiriMemoryKind::Rust`. A typed machine-hook failure takes precedence over the
lifecycle's `hookFailure`, as in `AllocationMachine.deallocate`. -/
def lmDeallocate (st : LmState) (ptr : Pointer (Option Provenance)) (size align : Nat) :
    Except LmFailure LmState :=
  match Align.fromBytes (UInt64.ofNat align) with
  | .error e => .error (.deallocAlign e)
  | .ok al =>
    let r := MemoryLifecycle.deallocatePtrWith st.mem st.ctx ptr
      (some (Size.ofBytes (UInt64.ofNat size), al)) (.machine .rust) lmDeallocHooks
    match r.outcome with
    | .ok () => .ok { mem := r.memory, ctx := r.hooks }
    | .error e => .error (r.hooks.pending.getD (.dealloc e))

/-- The target of an access of `size` bytes: the live allocation of the
pointer's provenance, the offset in it, and the pointer's tag. -/
def lmAccessTarget (st : LmState) (ptr : Pointer (Option Provenance)) (size : UInt64) :
    Except LmFailure (AllocId × Size × ProvenanceExtra × Allocation Provenance BorrowTree) :=
  match ptr.provenance with
  | none => .error (.danglingAccess ptr.offset.bytes)
  | some .wildcard => .error (.danglingAccess ptr.offset.bytes)
  | some (.concrete id tag) =>
    match st.mem.live.find? (fun entry => entry.1 == id) with
    | none => .error (.useAfterFree id)
    | some (_, entry) =>
      let offset := ptr.offset.bytes - lmBaseAddr id
      if offset.toNat + size.toNat ≤ entry.allocation.byteSize.bytes.toNat then
        .ok (id, Size.ofBytes offset, .concrete tag, entry.allocation)
      else
        .error (.outOfBounds id offset size)

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
          (lmMachineHooks st.ctx.protectedTags) allocation ptr id provenance range
      else
        MachineMemoryHooks.beforeMemoryRead st.mem lmHookContext
          (lmMachineHooks st.ctx.protectedTags) allocation ptr id provenance range
    match r.outcome with
    | .ok () => .ok { st with mem := r.memory }
    | .error _ =>
      .error (.treeAccess
        (allocation.extra.performBorrowAccessRange provenance range.start range.size
          (if write then .Write else .Read) st.ctx.protectedTags .VisitChildrenOfAccessed).status)
  else
    .ok st

/-- Store the unsigned integer `bits` in `size` bytes through `ptr`: the
access hook, then `Allocation::write_scalar`. -/
def lmStore (st : LmState) (ptr : Pointer (Option Provenance)) (size : UInt64) (bits : Nat) :
    Except LmFailure LmState := do
  let (id, offset, provenance, allocation) ← lmAccessTarget st ptr size
  let range : AllocRange := ⟨offset, Size.ofBytes size⟩
  let st ← lmTreeAccess st true allocation ptr id provenance range
  match st.mem.live.find? (fun entry => entry.1 == id) with
  | none => .error (.useAfterFree id)
  | some (_, entry) =>
    match Miri.Memory.Scalar.fromUInt (Prov := Provenance) (BitVec.ofNat 128 bits)
        (Size.ofBytes size) with
    | .error e => .error (.scalar e)
    | .ok value =>
      match Allocation.writeScalar lmLayout range value entry.allocation with
      | .error e _ => .error (.allocation e)
      | .ok () written =>
        match st.mem.setLiveAllocation id written with
        | .error _ => .error (.useAfterFree id)
        | .ok mem => .ok { st with mem := mem }

/-- Load an unsigned integer of `size` bytes through `ptr`: the access hook,
then `Allocation::read_scalar`. -/
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

/-- A Tree Borrows retag of the whole allocation: without a borrow tracker
the pointer is unchanged; with Tree Borrows, a read access through the parent
tag (unless the new permission is `Cell`), then `Tree::new_child` with the new
tag holding `permission` on every byte (accessed unless `Cell`), and the
protector, if any, recorded in the borrow tracker. -/
def lmRetag (st : LmState) (ptr : Pointer (Option Provenance)) (newTag : BorTag)
    (permission : Permission) (protector : Option ProtectorKind) :
    Except LmFailure (Pointer (Option Provenance) × LmState) :=
  if st.ctx.treeBorrows then
    match ptr.provenance with
    | none => .error (.danglingAccess ptr.offset.bytes)
    | some .wildcard => .error (.danglingAccess ptr.offset.bytes)
    | some (.concrete id tag) =>
      match st.mem.live.find? (fun entry => entry.1 == id) with
      | none => .error (.useAfterFree id)
      | some (_, entry) =>
        let size := entry.allocation.byteSize
        let accessed := !permission.isCell
        let read : Except LmFailure LmState :=
          if accessed then
            lmTreeAccess st false entry.allocation ptr id (.concrete tag) ⟨Size.ZERO, size⟩
          else .ok st
        match read with
        | .error e => .error e
        | .ok st =>
          match st.mem.live.find? (fun entry => entry.1 == id) with
          | none => .error (.useAfterFree id)
          | some (_, entry) =>
            match permission.strongestIdempotentForeignAccess protector.isSome with
            | .ImpossibleProtectedReservedIM => .error (.treeRetag .ProtectedReservedIM)
            | .Access sifa =>
              let inside : DedupRangeMap Tree.LocationState :=
                DedupRangeMap.new size ⟨permission, accessed, sifa⟩
              let r := entry.allocation.extra.newChild Size.ZERO (.concrete tag) newTag inside
                permission protector.isSome
              match r.outcome with
              | .error e => .error (.treeRetag e)
              | .ok () =>
                match st.mem.setLiveAllocation id (entry.allocation.setExtra r.tree) with
                | .error _ => .error (.useAfterFree id)
                | .ok mem =>
                  let protectedTags := match protector with
                    | some kind => st.ctx.protectedTags.insert newTag kind
                    | none => st.ctx.protectedTags
                  .ok (⟨ptr.offset, some (.concrete id newTag)⟩,
                    { mem := mem, ctx := { st.ctx with protectedTags := protectedTags } })
  else
    .ok (ptr, st)

/-- The end of the call that protected `tag` in allocation `id`:
`Tree::release_protector` (the protector-end access), then the tag leaves
the borrow tracker's protected set. Without a borrow tracker, nothing. -/
def lmEndCall (st : LmState) (id : AllocId) (tag : BorTag) : Except LmFailure LmState :=
  if st.ctx.treeBorrows then
    match st.mem.live.find? (fun entry => entry.1 == id) with
    | none => .error (.useAfterFree id)
    | some (_, entry) =>
      let r := entry.allocation.extra.releaseProtector tag st.ctx.protectedTags
      if r.status = .Released then
        match st.mem.setLiveAllocation id (entry.allocation.setExtra r.tree) with
        | .error _ => .error (.useAfterFree id)
        | .ok mem =>
          .ok { mem := mem, ctx := { st.ctx with protectedTags := st.ctx.protectedTags.remove tag } }
      else
        .error (.protectorRelease r.status)
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

/-- The observation class of a harness failure. Deallocation failures are
classified by the vendored `AllocationMachine.deallocationError`. An invalid
allocation request (`check_alloc_request`) violates the precondition of
`Layout::from_size_align` and is undefined behavior at the Rust allocator
entry. -/
def lmObsOfFailure : LmFailure → LmHeapWideObs
  | .allocAlign _ => .ub
  | .allocTooLarge _ => .ub
  | .allocLifecycle _ => .invalidOrUnsupported
  | .deallocAlign _ => .ub
  | .dealloc e => lmObsOfStep (AllocationMachine.deallocationError e)
  | .treeDealloc status => if lmDeallocIsUb status then .ub else .invalidOrUnsupported
  | .treeAccess status => if lmAccessIsUb status then .ub else .invalidOrUnsupported
  | .treeRetag _ => .invalidOrUnsupported
  | .protectorRelease _ => .invalidOrUnsupported
  | .danglingAccess _ => .ub
  | .useAfterFree _ => .ub
  | .outOfBounds _ _ _ => .ub
  | .allocation (.invalidUninitBytes _) => .ub
  | .allocation .readOnlyAllocation => .ub
  | .allocation _ => .invalidOrUnsupported
  | .scalar _ => .invalidOrUnsupported
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
    | none => .error (.useAfterFree id)
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

/-- The tag of the child references. -/
def lmChildTag : BorTag := ⟨1000, by decide⟩

/-- The over-aligned `Box` of the protector scenarios: a 32-byte, 32-aligned
heap allocation holding `42u32`, with a child tag holding `permission` on
every byte and the given protector (`lmRetag`), read once through the child
when `readChild`. Returns the parent pointer, the child pointer, and the
state. -/
def lmBoxWithChild (tb : Bool) (permission : Permission) (protector : Option ProtectorKind)
    (readChild : Bool) :
    Except LmFailure (Pointer (Option Provenance) × Pointer (Option Provenance) × LmState) := do
  let (parent, st) ← lmAllocate (lmInit tb) 32 32
  let st ← lmStore st parent 4 42
  let (child, st) ← lmRetag st parent lmChildTag permission protector
  if readChild then
    let (_, st) ← lmLoad st child 4
    pure (parent, child, st)
  else
    pure (parent, child, st)

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
    let (_, box, st) ← lmBoxWithChild tb (.ReservedFrz false) (some .WeakProtector) false
    let _ ← lmDeallocate st box 32 32
    pure .okDealloc
  | 19 => do
    let (parent, _, st) ← lmBoxWithChild tb .Frozen (some .StrongProtector) true
    let _ ← lmDeallocate st parent 32 32
    pure .okDealloc
  | 20 => do
    let (parent, _, st) ← lmBoxWithChild tb .Frozen (some .StrongProtector) true
    let st ← lmEndCall st lmFirstId lmChildTag
    let _ ← lmDeallocate st parent 32 32
    pure .okDealloc
  | 21 => do
    let (_, child, st) ← lmBoxWithChild tb .Frozen none false
    let _ ← lmDeallocate st child 32 32
    pure .okDealloc
  | 22 => do
    let (parent, _, st) ← lmBoxWithChild tb .Cell (some .StrongProtector) false
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
  match lmBoxWithChild tb .Frozen (some .StrongProtector) false with
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
protector scenario (with Tree Borrows): the block of `lmBoxWithChild`,
optionally after the protecting call ended, deallocated through the child tag
or through the allocation's root tag. -/
def lmScenarioDeallocStatus (permission : Permission) (protector : Option ProtectorKind)
    (readChild release throughChild : Bool) : Option BorrowTree.BorrowTreeDeallocStatus :=
  match lmBoxWithChild true permission protector readChild with
  | .error _ => none
  | .ok (_, _, st) =>
    match (if release then lmEndCall st lmFirstId lmChildTag else .ok st) with
    | .error _ => none
    | .ok st =>
      match st.mem.live.find? (fun entry => entry.1 == lmFirstId) with
      | none => none
      | some (_, entry) =>
        some (entry.allocation.extra.deallocateBorrowRange
          (.concrete (if throughChild then lmChildTag else lmRootTag lmFirstId))
          Size.ZERO (Size.ofBytes 32) st.ctx.protectedTags).status

/-- Deallocate the block of a protector scenario through its child pointer. -/
def lmDeallocThroughChild (tb : Bool) (permission : Permission)
    (protector : Option ProtectorKind) : Except LmFailure LmHeapWideObs := do
  let (_, child, st) ← lmBoxWithChild tb permission protector false
  let _ ← lmDeallocate st child 32 32
  pure .okDealloc

/-! ### Evaluable twins of the harness -/

unroll_loops lmAllocatePtrU := lmAllocatePtr fuel 0 with allocatePtrU
unroll_loops lmAllocateKindU := lmAllocateKind fuel 0 with lmAllocatePtrU
unroll_loops lmAllocateU := lmAllocate fuel 0 with lmAllocateKindU
unroll_loops lmBeforeDeallocationU := lmBeforeDeallocation fuel 0
  with beforeMemoryDeallocationU, deallocateBorrowRangeU
unroll_loops lmDeallocHooksU := lmDeallocHooks fuel 0 with lmBeforeDeallocationU
unroll_loops lmDeallocateU := lmDeallocate fuel 0 with deallocatePtrWithU, lmDeallocHooksU
unroll_loops lmTreeAccessU := lmTreeAccess fuel 0
  with beforeMemoryWriteU, beforeMemoryReadU, performBorrowAccessRangeU
unroll_loops lmStoreU := lmStore fuel 0 with lmTreeAccessU
unroll_loops lmLoadU := lmLoad fuel 0 with lmTreeAccessU
unroll_loops lmRetagU := lmRetag fuel 0 with lmTreeAccessU, newChildU
unroll_loops lmEndCallU := lmEndCall fuel 0 with releaseProtectorU
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
every failing case outside the two Tree Borrows cases. -/
def lmSharedFailure : Nat → Option LmFailure
  | 4 => some (.allocation (.invalidUninitBytes (some
      ⟨⟨Size.ofBytes 0, Size.ofBytes 4⟩, ⟨Size.ofBytes 0, Size.ofBytes 4⟩⟩)))
  | 5 => some (.allocAlign (.notPowerOfTwo 3))
  | 6 => some (.allocTooLarge 9223372036854775808)
  | 7 => some (.dealloc (.useAfterFree lmFirstId))
  | 8 => some (.useAfterFree lmFirstId)
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
the trees that `BorrowTree.new`, `newChild`, `performBorrowAccessRange`, and
`releaseProtector` produced for the over-aligned block:
1. through a weakly protected `Box` tag: `Deallocated`;
2. through the root while a strongly protected `Frozen` child that was read is
   live: the write would disable it, `AccessFailure … ProtectedDisabled`;
3. through a strongly protected (`Reserved`) tag itself: the write succeeds
   and the strong-protector check rejects it, `ProtectedDealloc`;
4. through the root after the protecting call ended: `Deallocated`;
5. through an unprotected `Frozen` child tag: the write is forbidden,
   `AccessFailure … ChildAccessForbidden`;
6. through the root while a strongly protected `Cell` child is live:
   `Deallocated` (interior mutability is exempt). -/
theorem deallocateBorrowRange_protector_laws :
    lmScenarioDeallocStatus (.ReservedFrz false) (some .WeakProtector) false false true =
      some .Deallocated ∧
    lmScenarioDeallocStatus .Frozen (some .StrongProtector) true false false =
      some (.AccessFailure (.AccessFailure ⟨0, 4⟩
        (.TransitionError 1 (.ProtectedDisabled .Frozen)))) ∧
    lmScenarioDeallocStatus (.ReservedFrz false) (some .StrongProtector) false false true =
      some (.ProtectedDealloc ⟨0, 32⟩ ⟨1⟩) ∧
    lmScenarioDeallocStatus .Frozen (some .StrongProtector) true true false =
      some .Deallocated ∧
    lmScenarioDeallocStatus .Frozen none false false true =
      some (.AccessFailure (.AccessFailure ⟨0, 32⟩
        (.TransitionError 1 (.ChildAccessForbidden .Frozen)))) ∧
    lmScenarioDeallocStatus .Cell (some .StrongProtector) false false false =
      some .Deallocated := by
  rw [lmScenarioDeallocStatusU.eq_src]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The same through the whole deallocation shim (`Memory::deallocate_ptr`
with `MachineMemoryHooks.beforeMemoryDeallocation`): through a strongly
protected tag itself the shim fails with the exact `ProtectedDealloc` status,
through a weakly protected `Box` tag it succeeds, and without a borrow tracker
both succeed. -/
theorem deallocate_through_protected_tag :
    lmFailureOf (lmDeallocThroughChild true (.ReservedFrz false) (some .StrongProtector)) =
      some (.treeDealloc (.ProtectedDealloc ⟨0, 32⟩ ⟨1⟩)) ∧
    lmDeallocThroughChild true (.ReservedFrz false) (some .WeakProtector) = .ok .okDealloc ∧
    lmDeallocThroughChild false (.ReservedFrz false) (some .StrongProtector) = .ok .okDealloc := by
  rw [lmDeallocThroughChildU.eq_src]
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

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

/-! ### `Memory::deallocate_ptr` failure classification -/

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
      hooks).outcome = .error (.danglingPointer address) := by
  unfold MemoryLifecycle.deallocatePtrWith
  simp only [Id.run, h]
  rfl

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
      hooks).outcome = .error (.nonzeroAllocationOffset "deallocate" id offset) := by
  unfold MemoryLifecycle.deallocatePtrWith
  simp only [Id.run, h]
  change (if (offset.bytes != 0) = true then _ else _ :
    MemoryDeallocationResult Prov Extra MachineKind HookState).outcome = _
  rw [ite_eq_left hoff]
  rfl

/-! ### `Align::from_bytes` at `Align::MAX` -/

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

/-- `Align::from_bytes` rejects every non-power-of-two below `4096`. -/
theorem align_fromBytes_not_pow2 (n : Nat) (h : n < 4096) (hne : n ≠ 0)
    (hpow : ∀ k, k < 12 → n ≠ 2 ^ k) :
    Align.fromBytes (UInt64.ofNat n) = .error (.notPowerOfTwo (UInt64.ofNat n)) := by
  have hall : (List.range 4096).all (fun n => decide (n = 0) ||
      (List.range 12).any (fun k => decide (n = 2 ^ k)) ||
      decide (Align.fromBytes (UInt64.ofNat n) = .error (.notPowerOfTwo (UInt64.ofNat n)))) =
        true := by
    decide +kernel
  have hn := List.all_eq_true.mp hall n (List.mem_range.mpr h)
  rw [Bool.or_eq_true, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hn
  rcases hn with (hn | hn) | hn
  · exact absurd hn hne
  · obtain ⟨k, hk, hkn⟩ := List.any_eq_true.mp hn
    exact absurd (of_decide_eq_true hkn) (hpow k (List.mem_range.mp hk))
  · exact hn

/-! ### `ptr::addr_eq` (`rust#166144`) -/

/-- The fat-to-thin cast keeps the data pointer and drops the metadata, for
every data scalar and every metadata scalar, of a slice pointer and of a
trait-object pointer. -/
theorem ptrToPtr_fat_to_thin (data metadata : Miri.Memory.Scalar Provenance) :
    lmToThin ⟨.scalarPair data metadata, layoutSlice⟩ = .ok ⟨.scalar data, layoutThin⟩ ∧
    lmToThin ⟨.scalarPair data metadata, layoutDyn⟩ = .ok ⟨.scalar data, layoutThin⟩ :=
  ⟨rfl, rfl⟩

/-- **`addr_eq` erases metadata.** `addr_eq` of two wide pointers is `==` of
their data pointers, whatever their metadata (two lengths, two vtables, or a
length and a vtable). -/
theorem addrEq_metadata_erased (dataL dataR metaL metaR : Miri.Memory.Scalar Provenance) :
    lmAddrEq ⟨.scalarPair dataL metaL, layoutSlice⟩ ⟨.scalarPair dataR metaR, layoutSlice⟩ =
      lmEq ⟨.scalar dataL, layoutThin⟩ ⟨.scalar dataR, layoutThin⟩ ∧
    lmAddrEq ⟨.scalarPair dataL metaL, layoutDyn⟩ ⟨.scalarPair dataR metaR, layoutDyn⟩ =
      lmEq ⟨.scalar dataL, layoutThin⟩ ⟨.scalar dataR, layoutThin⟩ ∧
    lmAddrEq ⟨.scalarPair dataL metaL, layoutSlice⟩ ⟨.scalarPair dataR metaR, layoutDyn⟩ =
      lmEq ⟨.scalar dataL, layoutThin⟩ ⟨.scalar dataR, layoutThin⟩ :=
  ⟨rfl, rfl, rfl⟩

/-- **`==` on thin pointers erases provenance.** Comparing two pointers
gives the same result whatever their provenance: only the addresses are
compared. -/
theorem thinEq_provenance_erased (addrL addrR : Size) (provL provL' provR provR' : Provenance) :
    lmEq ⟨.scalar (Miri.Memory.Scalar.fromPointer lmLayout ⟨addrL, provL⟩), layoutThin⟩
        ⟨.scalar (Miri.Memory.Scalar.fromPointer lmLayout ⟨addrR, provR⟩), layoutThin⟩ =
      lmEq ⟨.scalar (Miri.Memory.Scalar.fromPointer lmLayout ⟨addrL, provL'⟩), layoutThin⟩
        ⟨.scalar (Miri.Memory.Scalar.fromPointer lmLayout ⟨addrR, provR'⟩), layoutThin⟩ := rfl

/-- **`==` on a slice pointer and a trait-object pointer is rejected.** For
every operand value, `ScalarOps.binary` at `Eq` on operands of the two wide
pointer types fails with `invalidProgram`: their ABIs differ. `addr_eq` on the
same operands is defined (`addrEq_metadata_erased`). -/
theorem wideEq_hetero_invalidProgram (a b c d : Miri.Memory.Scalar Provenance) :
    lmEq ⟨.scalarPair a b, layoutSlice⟩ ⟨.scalarPair c d, layoutDyn⟩ =
      .error (.invalidProgram "pointer comparison backend mismatch") ∧
    lmEq ⟨.scalarPair c d, layoutDyn⟩ ⟨.scalarPair a b, layoutSlice⟩ =
      .error (.invalidProgram "pointer comparison backend mismatch") := ⟨rfl, rfl⟩

/-- A comparison of a wide pointer with a thin pointer is rejected as well. -/
theorem wideEq_thin_wide_invalidProgram (a b c : Miri.Memory.Scalar Provenance) :
    lmEq ⟨.scalarPair a b, layoutSlice⟩ ⟨.scalar c, layoutThin⟩ =
      .error (.invalidProgram "pointer comparison backend mismatch") := rfl

/-! ### Uninitialized heap memory -/

/-- Reading a range that the initialization mask reports uninitialized is
undefined behavior in the harness classification, for every allocation
(`LeanMiriSpec.MemoryLemmas`: `Allocation.readScalar_uninit_err`). -/
theorem readScalar_uninit_ub {E : Type} (allocation : Allocation Provenance E)
    (range bad : AllocRange) (readProvenance : Bool)
    (h : allocation.initializationMask.isRangeInitialized range = .ok (.error bad)) :
    ∃ e, allocation.readScalar lmLayout range readProvenance = .error e ∧
      lmObsOfFailure (.allocation e) = .ub :=
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
  ⟨rfl, deallocatePtrWith_dangling _ _ _ _ _ lmDeallocHooks 4096 rfl⟩

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
   `2^30` as too large.
4. `ptr::addr_eq` erases metadata (`Cast.ptrToPtr` then `pointerBinary`),
   `==` on thin pointers erases provenance, and `==` on a slice pointer and a
   trait-object pointer is rejected (`rust#166144`).
5. `BorrowTree.deallocateBorrowRange` on the over-aligned block
   (`rust#165833`): weak protector `Deallocated`, active strong protector on
   an accessed `Frozen` child `AccessFailure`, released protector
   `Deallocated`, unprotected `Frozen` child tag `AccessFailure`, strongly
   protected `Cell` child `Deallocated`.
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
    ((∀ k, k < 30 → Align.fromBytes (UInt64.ofNat (2 ^ k)) = .ok ⟨k⟩) ∧
      Align.fromBytes 1073741824 = .error (.tooLarge 1073741824)) ∧
    ((∀ dataL dataR metaL metaR : Miri.Memory.Scalar Provenance,
        lmAddrEq ⟨.scalarPair dataL metaL, layoutSlice⟩ ⟨.scalarPair dataR metaR, layoutDyn⟩ =
          lmEq ⟨.scalar dataL, layoutThin⟩ ⟨.scalar dataR, layoutThin⟩) ∧
      (∀ (addrL addrR : Size) (provL provL' provR provR' : Provenance),
        lmEq ⟨.scalar (Miri.Memory.Scalar.fromPointer lmLayout ⟨addrL, provL⟩), layoutThin⟩
            ⟨.scalar (Miri.Memory.Scalar.fromPointer lmLayout ⟨addrR, provR⟩), layoutThin⟩ =
          lmEq ⟨.scalar (Miri.Memory.Scalar.fromPointer lmLayout ⟨addrL, provL'⟩), layoutThin⟩
            ⟨.scalar (Miri.Memory.Scalar.fromPointer lmLayout ⟨addrR, provR'⟩), layoutThin⟩) ∧
      (∀ a b c d : Miri.Memory.Scalar Provenance,
        lmEq ⟨.scalarPair a b, layoutSlice⟩ ⟨.scalarPair c d, layoutDyn⟩ =
          .error (.invalidProgram "pointer comparison backend mismatch"))) ∧
    (lmScenarioDeallocStatus (.ReservedFrz false) (some .WeakProtector) false false true =
        some .Deallocated ∧
      lmScenarioDeallocStatus .Frozen (some .StrongProtector) true false false =
        some (.AccessFailure (.AccessFailure ⟨0, 4⟩
          (.TransitionError 1 (.ProtectedDisabled .Frozen)))) ∧
      lmScenarioDeallocStatus .Frozen (some .StrongProtector) true true false =
        some .Deallocated ∧
      lmScenarioDeallocStatus .Frozen none false false true =
        some (.AccessFailure (.AccessFailure ⟨0, 32⟩
          (.TransitionError 1 (.ChildAccessForbidden .Frozen)))) ∧
      lmScenarioDeallocStatus .Cell (some .StrongProtector) false false false =
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
  refine ⟨⟨?_, rfl, rfl⟩, ?_, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact fun E memory memory' staticRoots leaked h =>
      leakCheck_take_sound memory memory' staticRoots leaked h
  · exact deallocationError_ub_iff
  · exact align_fromBytes_pow2_ok
  · exact align_fromBytes_boundary.2.1
  · exact fun dataL dataR metaL metaR => (addrEq_metadata_erased dataL dataR metaL metaR).2.2
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
   transitively;
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
    if (`LeanMiriSpec.HeapAllocAndWidePtrLM).isPrefixOf c then
      if let .thmInfo _ := info then theorems := theorems + 1
  -- This module states 37 `theorem` declarations; generated `eq_src` theorems only add to it.
  if theorems < 37 then
    throwError "axiom audit is vacuous: only {theorems} theorems of LeanMiriSpec.HeapAllocAndWidePtrLM seen"
  logInfo m!"LeanMiriSpec.HeapAllocAndWidePtrLM: {checked} declarations ({theorems} theorems) depend only on propext, Quot.sound, Classical.choice (sorry_free=true, ofReduceBool_free=true, import_isolated=true)"

end AxiomAudit

end LeanMiriSpec.HeapAllocAndWidePtrLM
