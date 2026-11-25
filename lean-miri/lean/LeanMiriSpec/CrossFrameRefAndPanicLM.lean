/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import Miri.TreeBorrows.MachineMemoryHooks
import Miri.TreeBorrows.RetagPipeline
import Miri.Interpreter.Unwind
import Miri.Interpreter.PointerOffset
import LeanMiriSpec.Correspondence.SimLM4_1
import LeanMiriSpec.Correspondence.OffsetLM4_2

/-!
# Episode 1 LeanMiri Authority: Cross-Frame References, Pointer Arithmetic, & 4-Way Panic Unwinding (`LeanMiriSpec.CrossFrameRefAndPanicLM`)

Operational correspondence between vendored unmodified `lean-miri` (`Miri.Interpreter.Step`,
`Miri.Interpreter.ControlFlow`, `Miri.Interpreter.Unwind`, `Miri.Interpreter.PointerOffset`,
`Miri.Memory.MemoryLifecycle`, `Miri.TreeBorrows.{BorrowTree, RetagPipeline, MachineMemoryHooks}`)
and Anneal's unmodified trusted MIR semantics (`Trusted.Rustc.V2026_06_01.MirSemantics`) across
the frozen 28-scenario (`0..27`) × 2-mode (`treeBorrows = false` vs `true`) matrix:

1. **Kernel-certified evaluation of vendored `Miri` code (`§0–§2`)**: derives loop-unrolled and
   row-scan twins with kernel-checked `@F = @T` equations (`loopReal_eq_unrolled`,
   `KeyedArray.contains_rows`) so every scenario runs on the REAL vendored `Miri` definitions
   with zero `native_decide` and zero `sorry`.
2. **Universal vendored `Miri` laws (`§3`)**:
   - `Pointer.wrappingSignedOffset` `+delta` / `-delta` round-trip and `ptrOffsetInbounds` OOB
     rejection;
   - `Miri.TreeBorrows.BorrowTree` `FnEntry` strong-protector foreign-write conflict vs.
     post-`releaseProtector` parent access success, `Frozen` local-write UB, and 2-frame LIFO
     protector release ordering;
   - `Miri.Interpreter.Unwind` payload push/pop LIFO invariants & empty-payload error;
   - `Miri.Interpreter.ControlFlow` `Unreachable` UB, 4-way `unwindToBlock`, and root-frame
     `returnFromCurrentFrame(..., unwinding := true)` UB.
3. **Direct two-sided `stepMirFn` ↔ `Miri.Interpreter.Step.step` simulations (`§4`)**:
   packages lockstep simulations for `TerminatorKind.assert` (pass & fail across all 4 unwind
   actions), `TerminatorKind.unreachable`, cross-frame `Call` / `Return` / multi-frame LIFO
   `UnwindResume` (including root-ceiling divergence vs. cleared-ceiling agreement), safe
   references, `BinOp.offset`, `core::intrinsics::arith_offset`, and six-state Tree Borrows.
4. **Frozen 56-cell observation table (`lmCrossFramePanicObserve_table`), out-of-range
   fail-closed guard, mode-sensitivity `↔`, capstone, and silent axiom/import-isolation audit
   (`§5–§6`)** verifying ZERO `MiniRustSpec.*` and ZERO `Anneal.*` imports.
-/

namespace LeanMiriSpec.CrossFrameRefAndPanicLM

set_option Elab.async false

open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.DataStructures Miri.Interpreter
open LeanMiriSpec.Correspondence

/-! ## §0. Frozen Observation Interface & Kernel-Certified Evaluation of Vendored `Miri` -/

/-- Frozen cross-authority observation domain for Episode 1 scenarios (constructor order
identical to `MrCrossFramePanicObs` and `CrossFramePanicObs`). -/
inductive LmCrossFramePanicObs : Type where
  | okVal (retVal : Nat) (referentVal : Nat)
  | okCleanupRecovered (retVal : Nat) (referentVal : Nat)
  | unwound (referentVal : Nat)
  | abort
  | ub
  | specPanic
  | invalidOrUnsupported
  deriving DecidableEq, Repr

/-- Number of canonical Episode 1 scenarios (`0..27`, 56 mode cells). -/
def lmCanonicalCaseCount : Nat := 28

/-- 4-byte alignment (`2^2 = 4`) for `u32` and `[u32; 2]` stack locals. -/
@[reducible] def align4 : Align := ⟨2⟩

/-- Close an equality goal via kernel definitional reduction (no `Lean.ofReduceBool`). -/
local elab "kernel_rfl" : tactic => do
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  let tgt ← Lean.MVarId.getType' mvarId
  let some (ty, lhs, _) := tgt.eq?
    | Lean.Meta.throwTacticEx `kernel_rfl mvarId "expected equality goal"
  let u ← Lean.Meta.getLevel ty
  mvarId.assign (Lean.mkApp2 (Lean.mkConst ``Eq.refl [u]) ty lhs)
  Lean.Elab.Tactic.replaceMainGoal []

/-- Bounded unrolling of a `while` loop (`Lean.Loop`) in `Id`. -/
def loopFuelK {β : Type} (f : Unit → β → Id (ForInStep β)) : Nat → β → (β → β) → β
  | 0, b, k => k b
  | n + 1, b, k =>
    match f () b with
    | .done v => v
    | .yield v => loopFuelK f n v k

def loopReal : (β : Type) → β → (Unit → β → Id (ForInStep β)) → β :=
  fun _ init f => forIn (m := Id) Lean.Loop.mk init f

def loopUnrolled (fuel : Nat) : (β : Type) → β → (Unit → β → Id (ForInStep β)) → β :=
  fun β init f => loopFuelK f fuel init (fun b => loopReal β b f)

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
private def resolveMaybePrivate (n : Name) : CoreM Name := do
  let env ← getEnv
  if env.contains n then return n
  let found := env.constants.fold (init := (none : Option Name)) fun acc c _ =>
    if privateToUserName? c == some n then some c else acc
  match found with
  | some c => return c
  | none => throwError "unknown constant {n}"

open Lean Meta Elab Command in
/-- Derive a kernel-evaluable twin `T` of a vendored definition `F` with a kernel-checked
equality theorem `T.eq_src : @F = @T` (zero axioms, zero compiler trust). -/
local elab "unroll_loops " newId:ident " := " srcId:ident " fuel " n:num
    deps:((" with " ident,*)?) : command => do
  liftTermElabM do
    let src ← (try resolveGlobalConstNoOverload srcId catch _ => resolveMaybePrivate srcId.getId)
    let .defnInfo dinfo ← getConstInfo src | throwError "{src} is not a definition"
    let lvls := dinfo.levelParams
    let newName := (← getCurrNamespace) ++ newId.getId
    let depIds : Array Syntax := match deps.raw with
      | .node _ _ args => if args.size == 0 then #[] else args[1]!.getSepArgs
      | _ => #[]
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
    let loopTy ← inferType (mkConst ``LeanMiriSpec.CrossFrameRefAndPanicLM.loopReal)
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
        (#[mkApp (mkConst ``LeanMiriSpec.CrossFrameRefAndPanicLM.loopUnrolled) fuel] ++
          depInfo.map fun (t, _, _, _, _) => mkConst t)
      let twinVal ← Core.betaReduce twinVal.headBeta
      addDecl <| .defnDecl {
        name := newName, levelParams := lvls, type := dinfo.type, value := twinVal,
        hints := .abbrev, safety := .safe }
      let mut proof ← mkCongrArg ctx
        (mkApp (mkConst ``LeanMiriSpec.CrossFrameRefAndPanicLM.loopReal_eq_unrolled) fuel)
      for (t, _, _, _, _) in depInfo do
        proof ← mkCongr proof (mkConst (t ++ `eq_src))
      let us := lvls.map mkLevelParam
      let stmt ← mkEq (mkConst src us) (mkConst newName us)
      addDecl <| .thmDecl {
        name := newName ++ `eq_src, levelParams := lvls, type := stmt, value := proof }

/-! ### `KeyedArray` row-scan twins (`KeyedArray.contains_rows`) -/

def containsU64 : (V : Type) → (keyFn : V → UInt64) → KeyedArray UInt64 V keyFn → UInt64 → Bool :=
  fun _ keyFn table key => (table.toArray.map keyFn).contains key

theorem containsU64.eq_src :
    (fun (V : Type) (keyFn : V → UInt64) => @KeyedArray.contains UInt64 V _ _ keyFn) =
      containsU64 := by
  funext V keyFn table key
  exact KeyedArray.contains_rows table key

private theorem keyedArray_find?_eq_none_of_contains_false {V : Type} {keyFn : V → UInt64}
    (table : KeyedArray UInt64 V keyFn) (key : UInt64) (h : table.contains key = false) :
    table.find? key = none := by
  cases hf : table.find? key with
  | none => rfl
  | some _ =>
    exfalso
    unfold KeyedArray.contains at h
    unfold KeyedArray.find? at hf
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_none_of_contains_eq_false h] at hf
    cases hf

def findU64 : (V : Type) → (keyFn : V → UInt64) → KeyedArray UInt64 V keyFn → UInt64 → Option V :=
  fun _ keyFn table key =>
    if (table.toArray.map keyFn).contains key then table.find? key else none

theorem findU64.eq_src :
    (fun (V : Type) (keyFn : V → UInt64) => @KeyedArray.find? UInt64 V _ _ keyFn) = findU64 := by
  funext V keyFn table key
  unfold findU64
  rw [← KeyedArray.contains_rows table key]
  cases h : table.contains key with
  | true => rfl
  | false => exact keyedArray_find?_eq_none_of_contains_false table key h

private theorem keyedArray_any?_eq_false_of_contains_false {V : Type} {keyFn : V → UInt64}
    (table : KeyedArray UInt64 V keyFn) (key : UInt64) (p : V → Bool)
    (h : table.contains key = false) :
    table.any? key p = false := by
  unfold KeyedArray.contains at h
  unfold KeyedArray.any?
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_none_of_contains_eq_false h]
  rfl

def anyU64 : (V : Type) → (keyFn : V → UInt64) → KeyedArray UInt64 V keyFn → UInt64 →
    (V → Bool) → Bool :=
  fun _ keyFn table key p =>
    if (table.toArray.map keyFn).contains key then table.any? key p else false

theorem anyU64.eq_src :
    (fun (V : Type) (keyFn : V → UInt64) => @KeyedArray.any? UInt64 V _ _ keyFn) = anyU64 := by
  funext V keyFn table key p
  unfold anyU64
  rw [← KeyedArray.contains_rows table key]
  cases h : table.contains key with
  | true => rfl
  | false => exact keyedArray_any?_eq_false_of_contains_false table key p h

/-! ### Evaluable twins of vendored `Miri` lifecycle, Tree Borrows, and retag operations -/

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
unroll_loops findOffsetU := Miri.DataStructures.DedupRangeMap.findOffset fuel 40
unroll_loops iterMutWithCloneU := Miri.DataStructures.DedupRangeMap.iterMutWithClone fuel 30
  with findOffsetU
unroll_loops iterMutU := Miri.DataStructures.DedupRangeMap.iterMut fuel 0 with iterMutWithCloneU
unroll_loops modifyRangeWithCloneU := Miri.DataStructures.DedupRangeMap.modifyRangeWithClone fuel 0
  with iterMutWithCloneU
unroll_loops modifyRangeU := Miri.DataStructures.DedupRangeMap.modifyRange fuel 0
  with modifyRangeWithCloneU
unroll_loops updateSifaAfterRetagU := Miri.TreeBorrows.BorrowTree.updateSifaAfterRetag fuel 30
unroll_loops newChildU := Miri.TreeBorrows.BorrowTree.newChild fuel 0
  with updateSifaAfterRetagU, modifyRangeU
unroll_loops minExposedChildU := Miri.TreeBorrows.BorrowTree.minExposedChild fuel 30
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

/-! ## §1. Multi-Frame Vendored `Miri` Execution Harness (Tree Borrows + Pointer Offset + Unwind) -/

/-- Harness memory: vendored `MemoryState` with `Provenance`, `BorrowTree`, and `MiriMemoryKind`. -/
abbrev LmMem := MemoryState Provenance BorrowTree MiriMemoryKind

/-- Typed failure captured directly from vendored `Miri` operations. -/
inductive LmExecFailure where
  | allocLifecycle (error : MemoryLifecycleError)
  | dealloc (error : MemoryLifecycleError)
  | treeDealloc (status : BorrowTree.BorrowTreeDeallocStatus)
  | treeAccess (status : BorrowTree.BorrowTreeAccessStatus)
  | retag (error : RetagPipeline.Error)
  | protectorRelease (status : BorrowTree.ProtectorReleaseStatus)
  | access (error : AccessError)
  | pointerOffset (error : PointerOffsetError)
  | pointer (error : PointerError)
  | allocation (error : AllocError)
  | scalar (error : ScalarError)
  | controlFlow (error : StepError)
  | abort
  | ub (msg : String)
  deriving DecidableEq

/-- One stack frame's Tree Borrows `FrameState` and stack-allocated locals (deallocated on exit). -/
structure LmCallFrame where
  tbFrame : FrameState := {}
  stackLocals : List (Pointer (Option Provenance) × Nat × Align) := []

/-- Borrow-tracker and multi-frame call-stack context threaded through vendored `Miri` hooks. -/
structure LmCtx where
  treeBorrows : Bool
  global : GlobalState := GlobalState.new
  frames : List LmCallFrame := [{}]
  unwindPayloads : List Nat := []
  nextUnwindToken : Nat := 0
  pending : Option LmExecFailure := none

/-- Complete multi-frame vendored `Miri` execution state. -/
structure LmState where
  mem : LmMem
  ctx : LmCtx

def lmInit (tb : Bool) : LmState :=
  { mem := MemoryState.empty, ctx := { treeBorrows := tb } }

def lmLayout : TargetDataLayout := ⟨.little, .w64⟩
def lmPtrArith : PointerArithmetic := ⟨Size.ofBytes 8⟩
def lmBaseAddr (id : AllocId) : UInt64 := id.value * 4294967296
def lmIsizeMax : Nat := 9223372036854775807
def lmFrozenFacts : RetagPolicy.TypeFacts := ⟨true, true, true⟩

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

def lmHookContext : MachineMemoryHooks.Context Unit Unit :=
  { state := (), syncObjects := .empty }

def lmInitExtra (memory : LmMem) (ctx : LmCtx) (id : AllocId) (_kind : MemoryKind MiriMemoryKind)
    (size : Size) (_align : Align) :
    MemoryStateHookResult Provenance BorrowTree MiriMemoryKind LmCtx BorrowTree :=
  match ctx.global.rootPointerTag id with
  | .ok (global', rootTag) =>
    ⟨memory, { ctx with global := global' }, .ok (BorrowTree.new rootTag size)⟩
  | .error e => ⟨memory, ctx, .error (reprStr e)⟩

def lmAdjustRoot (memory : LmMem) (ctx : LmCtx) (id : AllocId)
    (_kind : MemoryKind MiriMemoryKind) :
    MemoryStateHookResult Provenance BorrowTree MiriMemoryKind LmCtx (Pointer Provenance) :=
  match ctx.global.rootPointerTag id with
  | .ok (global', rootTag) =>
    ⟨memory, { ctx with global := global' },
      .ok ⟨Size.ofBytes (lmBaseAddr id), .concrete id rootTag⟩⟩
  | .error e => ⟨memory, ctx, .error (reprStr e)⟩

def lmResolve (memory : LmMem) (ctx : LmCtx) (ptr : Pointer (Option Provenance)) (_size : Int) :
    PointerResolutionResult Provenance BorrowTree MiriMemoryKind LmCtx ProvenanceExtra :=
  match ptr.provenance with
  | some (.concrete id tag) =>
    if ptr.offset.bytes < lmBaseAddr id then
      ⟨memory, ctx, .error ptr.offset.bytes⟩
    else
      ⟨memory, ctx, .ok (id, Size.ofBytes (ptr.offset.bytes - lmBaseAddr id), .concrete tag)⟩
  | _ => ⟨memory, ctx, .error ptr.offset.bytes⟩

def lmResolvePure : PointerResolver Provenance ProvenanceExtra := fun ptr _ =>
  match ptr.provenance with
  | some (.concrete id tag) =>
    if ptr.offset.bytes < lmBaseAddr id then .error ptr.offset.bytes
    else .ok ⟨id, Size.ofBytes (ptr.offset.bytes - lmBaseAddr id), .concrete tag⟩
  | _ => .error ptr.offset.bytes

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

def lmDeallocHooks :
    MemoryDeallocationHooks Provenance BorrowTree MiriMemoryKind LmCtx ProvenanceExtra :=
  { synchronizeMemory := fun _ ctx => ctx
    resolvePointer := lmResolve
    beforeDeallocation := lmBeforeDeallocation }

/-- Allocate a stack local of `(size, align)` in the active top frame via vendored
`Miri.Memory.MemoryLifecycle.allocatePtr`. -/
def lmAllocStack (st : LmState) (size : Nat) (align : Align) :
    Except LmExecFailure (Pointer (Option Provenance) × LmState) :=
  let r := MemoryLifecycle.allocatePtr st.mem st.ctx (fun _ ctx => ctx)
    (Size.ofBytes (UInt64.ofNat size)) align .stack .Uninit
    (Size.ofBytes (UInt64.ofNat lmIsizeMax)) (some (.machine .global))
    (fun sz _ => some (Array.replicate sz.bytes.toNat 0)) lmInitExtra lmAdjustRoot
  match r.outcome with
  | .error e => .error (.allocLifecycle e)
  | .ok ptr =>
    let optPtr := ptr.withOptionalProvenance
    let frames' := match r.hooks.frames with
      | top :: rest => { top with stackLocals := (optPtr, size, align) :: top.stackLocals } :: rest
      | [] => [{ stackLocals := [(optPtr, size, align)] }]
    .ok (optPtr, { mem := r.memory, ctx := { r.hooks with frames := frames' } })

/-- Deallocate one stack local via vendored `Miri.Memory.MemoryLifecycle.deallocatePtrWith`. -/
def lmDeallocStackOne (st : LmState) (entry : Pointer (Option Provenance) × Nat × Align) :
    Except LmExecFailure LmState :=
  let (ptr, size, align) := entry
  let r := MemoryLifecycle.deallocatePtrWith st.mem st.ctx ptr
    (some (Size.ofBytes (UInt64.ofNat size), align)) .stack lmDeallocHooks
  match r.outcome with
  | .ok () => .ok { mem := r.memory, ctx := r.hooks }
  | .error e => .error (r.hooks.pending.getD (.dealloc e))

/-- Access target validation via vendored `Miri.Memory.getPtrAccess` and `MemoryState.getAllocInfo`. -/
def lmAccessTarget (st : LmState) (ptr : Pointer (Option Provenance)) (size : UInt64) :
    Except LmExecFailure (AllocId × Size × ProvenanceExtra × Allocation Provenance BorrowTree) :=
  match getPtrAccess lmPtrArith ptr (Size.ofBytes size) .memoryAccess
      lmResolvePure st.mem.getAllocInfo with
  | .error e => .error (.access e)
  | .ok none => .error (.ub "zero-sized scalar access")
  | .ok (some (_, _, (id, offset, provenance))) =>
    match st.mem.live.find? (fun entry => entry.1 == id) with
    | none => .error (.access (.allocationLookup (.unavailable id)))
    | some (_, entry) => .ok (id, offset, provenance, entry.allocation)

/-- Tree Borrows read/write hook via vendored `MachineMemoryHooks.{beforeMemoryRead, beforeMemoryWrite}`. -/
def lmTreeAccess (st : LmState) (write : Bool) (allocation : Allocation Provenance BorrowTree)
    (ptr : Pointer (Option Provenance)) (id : AllocId) (provenance : ProvenanceExtra)
    (range : AllocRange) : Except LmExecFailure LmState :=
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

/-- Store a `u32` scalar through `ptr` via vendored `getPtrAccess`, Tree Borrows hook, and
`Allocation.writeScalar`. -/
def lmStoreU32 (st : LmState) (ptr : Pointer (Option Provenance)) (val : Nat) :
    Except LmExecFailure LmState := do
  let (id, offset, provenance, allocation) ← lmAccessTarget st ptr 4
  let range : AllocRange := ⟨offset, Size.ofBytes 4⟩
  let st ← lmTreeAccess st true allocation ptr id provenance range
  match st.mem.live.find? (fun entry => entry.1 == id) with
  | none => .error (.access (.allocationLookup (.unavailable id)))
  | some (_, entry) =>
    match Miri.Memory.Scalar.fromUInt (Prov := Provenance) (BitVec.ofNat 128 val)
        (Size.ofBytes 4) with
    | .error e => .error (.scalar e)
    | .ok value =>
      match Allocation.writeScalar lmLayout range value entry.allocation with
      | .error e _ => .error (.allocation e)
      | .ok () written =>
        match st.mem.setLiveAllocation id written with
        | .error e => .error (.access (.allocationLookup e))
        | .ok mem => .ok { st with mem := mem }

/-- Load a `u32` scalar through `ptr` via vendored `getPtrAccess`, Tree Borrows hook, and
`Allocation.readScalar`. -/
def lmLoadU32 (st : LmState) (ptr : Pointer (Option Provenance)) :
    Except LmExecFailure (Nat × LmState) := do
  let (id, offset, provenance, allocation) ← lmAccessTarget st ptr 4
  let range : AllocRange := ⟨offset, Size.ofBytes 4⟩
  let st ← lmTreeAccess st false allocation ptr id provenance range
  match allocation.readScalar lmLayout range false with
  | .error e => .error (.allocation e)
  | .ok value =>
    match value.toBits (Size.ofBytes 4) with
    | .error e => .error (.scalar e)
    | .ok bits => .ok (bits.toNat, st)

/-- In-bounds pointer offset via vendored `Miri.Interpreter.ptrOffsetInbounds`. -/
def lmPtrOffsetInbounds (st : LmState) (ptr : Pointer (Option Provenance)) (byteDelta : Int) :
    Except LmExecFailure (Pointer (Option Provenance)) :=
  match Miri.Interpreter.ptrOffsetInbounds lmPtrArith ptr (Int64.ofInt byteDelta)
      lmResolvePure st.mem.getAllocInfo with
  | .ok ptr' => .ok ptr'
  | .error e => .error (.pointerOffset e)

/-- Wrapping pointer offset via vendored `Miri.Memory.Pointer.wrappingSignedOffset`. -/
def lmPtrOffsetWrapping (ptr : Pointer (Option Provenance)) (byteDelta : Int) :
    Except LmExecFailure (Pointer (Option Provenance)) :=
  match ptr.wrappingSignedOffset (Int64.ofInt byteDelta) lmPtrArith with
  | .ok ptr' => .ok ptr'
  | .error e => .error (.pointer e)

/-- Push a new callee call frame onto the stack. -/
def lmEnterCall (st : LmState) : LmState :=
  { st with ctx := { st.ctx with frames := {} :: st.ctx.frames } }

/-- Retag a reference argument at `FnEntry` (or `Default`) via vendored
`Miri.TreeBorrows.RetagPipeline.retagPointerValue`, recording its strong protector in
`GlobalState` and the active top `LmCallFrame.tbFrame`. -/
def lmRetagRef (st : LmState) (ptr : Pointer (Option Provenance))
    (refKind : RetagPolicy.ReferenceKind) (mode : RetagPolicy.RetagMode) :
    Except LmExecFailure (Pointer (Option Provenance) × LmState) :=
  if st.ctx.treeBorrows then
    match lmResolvePure ptr 0 with
    | .error addr => .error (.access (.danglingIntegerPointer addr 0 .memoryAccess))
    | .ok resolved =>
      match st.mem.live.find? (fun entry => entry.1 == resolved.allocId) with
      | none => .error (.access (.allocationLookup (.deadAllocation resolved.allocId)))
      | some (_, entry) =>
        let (topFrame, restFrames) := match st.ctx.frames with
          | top :: rest => (top, rest)
          | [] => ({}, [])
        let req : RetagPipeline.Request := {
          typeShape := .reference
          typeFacts := lmFrozenFacts
          referenceKind := refKind
          mode := mode
          config := { implicitWrites := true, rustcNoWritable := false }
          layoutSize := entry.allocation.byteSize
          originalProvenance := ptr.provenance
          pointeeIsFreeze := true
          preciseInteriorMut := false
          hooks := {
            allocationResolution := some ⟨resolved.allocId, resolved.offset, resolved.extra⟩
          }
        }
        let mstate : RetagPipeline.MachineState MiriMemoryKind :=
          ⟨st.mem, st.ctx.global, topFrame.tbFrame⟩
        let res := RetagPipeline.retagPointerValue mstate req
        match res.outcome with
        | .error e => .error (.retag e)
        | .ok prov =>
          let topFrame' : LmCallFrame := { topFrame with tbFrame := res.state.frame }
          .ok (⟨ptr.offset, prov⟩,
            { mem := res.state.memory
              ctx := { st.ctx with
                global := res.state.global
                frames := topFrame' :: restFrames } })
  else
    .ok (ptr, st)

/-- Release one protector `(id, tag)` via vendored `BorrowTree.releaseProtector`. -/
def lmReleaseOne (protectedTags : ProtectedTags) (mem : LmMem) (entryPair : AllocId × BorTag) :
    Except LmExecFailure LmMem :=
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

/-- Exit the active top call frame (normal return OR panic unwind):
1. Deallocate all stack locals owned by the top frame (`lmDeallocStackOne`).
2. Release all `FnEntry` protectors owned by the top frame via vendored
   `BorrowTree.releaseProtector` and `GlobalState.endCall` (preserving outer frames'
   protectors in strict LIFO order!). -/
def lmExitCall (st : LmState) : Except LmExecFailure LmState :=
  match st.ctx.frames with
  | [] => .error (.ub "empty call stack on frame exit")
  | top :: rest => do
    let st1 ← top.stackLocals.foldlM lmDeallocStackOne st
    if st1.ctx.treeBorrows then
      match top.tbFrame.protectedTags.toList.foldlM
          (lmReleaseOne st1.ctx.global.protectedTags) st1.mem with
      | .error e => .error e
      | .ok mem' =>
        .ok { mem := mem'
              ctx := { st1.ctx with
                global := st1.ctx.global.endCall top.tbFrame
                frames := rest } }
    else
      .ok { st1 with ctx := { st1.ctx with frames := rest } }

/-- Push an unwind payload token when panic unwinding initiates. -/
def lmStartUnwind (st : LmState) : LmState :=
  { st with ctx := { st.ctx with
      unwindPayloads := st.ctx.unwindPayloads ++ [st.ctx.nextUnwindToken]
      nextUnwindToken := st.ctx.nextUnwindToken + 1 } }

/-- Pop the top unwind payload token in an outer catch harness (`catch_unwind`). -/
def lmCatchUnwind (st : LmState) : Except LmExecFailure LmState :=
  match st.ctx.unwindPayloads.getLast? with
  | none => .error (.ub "unwind payload vector is empty")
  | some _ =>
    .ok { st with ctx := { st.ctx with unwindPayloads := st.ctx.unwindPayloads.dropLast } }

/-- Root-frame unwind check directly invoking vendored
`Miri.Interpreter.ControlFlow.returnFromCurrentFrame` on a 1-frame stack:
returns `.error (.controlFlow (.undefinedBehavior "unwinding past the topmost stack frame"))`. -/
def lmRootUnwindCheck : Except LmExecFailure Unit :=
  let dummyBody : Miri.MIR.Body :=
    { phase := .Built
      argumentCount := 0
      spreadArgument := none
      locals := #[0]
      basicBlocks := #[{ statements := #[],
                         terminator := { sourceInfo := { span := ⟨0⟩, scope := 0 },
                                         kind := .UnwindResume },
                         cleanup := true }] }
  let rootFrame : Miri.Interpreter.Frame Provenance Unit Unit :=
    { body := dummyBody
      bodyIdentity := .ofCanonicalIndex 0
      functionInstance := { kind := .Item 0, args := #[] }
      extra := ()
      returnContinuation := .stop false
      returnPlace := .frameLocal 0 0 none ⟨0, zstLayoutData⟩ (.ofAllocationToken 0)
      localsIdentity := .ofAllocationToken 0
      locals := #[⟨.dead, none⟩]
      vaList := #[]
      trackCallerArg := none
      location := .mir ⟨0, 0⟩ }
  let st : Miri.Interpreter.StepState Provenance Unit Unit Unit :=
    { stack := ⟨#[rootFrame]⟩, machine := () }
  let hooks : Miri.Interpreter.ControlHooks Provenance Unit Unit Unit Unit Unit :=
    { bodySpan := fun _ => .ok ⟨0⟩
      returnOperand := fun _ s => (s, .ok ())
      popFrame := fun _ s => (s, .error (.stack .emptyStack))
      copyReturn := fun _ _ _ s => (s, .ok ())
      cleanupFrame := fun _ _ _ s => (s, .ok .normal)
      unwindTerminate := fun _ _ s => (s, .error (.termination (.abort "unwindTerminate"))) }
  match Miri.Interpreter.ControlFlow.returnFromCurrentFrame hooks () true st with
  | (_, .ok ()) => .ok ()
  | (_, .error e) => .error (.controlFlow e)

/-- `TerminatorKind.unreachable` check directly invoking vendored
`Miri.Interpreter.ControlFlow.evalTerminator`. -/
def lmUnreachableCheck : Except LmExecFailure Unit :=
  let hooks : Miri.Interpreter.TerminatorHooks Provenance Unit Unit Unit Unit Unit Unit :=
    { bodySpan := fun _ => .ok ⟨0⟩
      returnOperand := fun _ s => (s, .ok ())
      popFrame := fun _ s => (s, .error (.stack .emptyStack))
      copyReturn := fun _ _ _ s => (s, .ok ())
      cleanupFrame := fun _ _ _ s => (s, .ok .normal)
      unwindTerminate := fun _ _ s => (s, .error (.termination (.abort "unwindTerminate")))
      evalDiscriminant := fun _ _ s => (s, .ok ())
      compareSwitchCase := fun _ _ _ s => (s, .ok false)
      call := fun _ _ s => (s, .ok ())
      tailCall := fun _ _ s => (s, .ok ())
      drop := fun _ _ _ _ s => (s, .ok ())
      ignoreOptionalOverflowChecks := fun _ => false
      readAssertCondition := fun _ _ s => (s, .ok true)
      assertPanic := fun _ _ _ s => (s, .ok ()) }
  let st : Miri.Interpreter.StepState Provenance Unit Unit Unit :=
    { stack := ⟨#[]⟩, machine := () }
  match Miri.Interpreter.ControlFlow.evalTerminator hooks ()
      { sourceInfo := { span := ⟨0⟩, scope := 0 }, kind := .Unreachable } st with
  | (_, .ok ()) => .ok ()
  | (_, .error e) => .error (.controlFlow e)

/-! ### Vendored `Miri.Interpreter.ControlFlow` driver over the multi-frame harness state

Every `TerminatorKind.assert` / `UnwindAction` / `UnwindResume` / `UnwindTerminate` decision in
scenarios `14..25` is taken by the REAL vendored `Miri.Interpreter.ControlFlow.evalTerminator`
(`Assert` → `goToBlock` / `assertPanic`, `UnwindResume` → `returnFromCurrentFrame (unwinding := true)`
→ `popFrame` → `cleanupFrame` → `unwindToBlock`, `UnwindTerminate` → `unwindTerminate`), running
over `StepState` whose machine component is the harness `LmState`. The `cleanupFrame` hook executes
the callee frame teardown (`lmExitCall`: stack-local deallocation via vendored
`MemoryLifecycle.deallocatePtrWith` + `FnEntry` protector release via vendored
`BorrowTree.releaseProtector` / `GlobalState.endCall`) exactly where pinned Miri runs
`pop_stack_frame` / `after_stack_pop`, i.e. AFTER the frame pop and BEFORE the caller's unwind
continuation is followed. `assertPanic` follows the asserting frame's `UnwindAction` through the
vendored `unwindToBlock` (the net control effect of Miri's `assert_panic` → `start_panic` call
unwinding back into the asserting frame). -/

/-- Canonical harness `SourceInfo`. -/
def lmSrc : Miri.MIR.SourceInfo := { span := ⟨0⟩, scope := 0 }

/-- Harness basic block with an empty statement list. -/
def lmCfBlock (k : Miri.MIR.TerminatorKind) (cleanup : Bool) : Miri.MIR.BasicBlock :=
  { statements := #[], terminator := { sourceInfo := lmSrc, kind := k }, cleanup := cleanup }

/-- Harness block layout shared by every driver frame: `bb0` (regular entry), `bb1` (regular
return target), `bb2` (`isCleanup = true` landing pad executing `UnwindResume`). -/
def lmCfBlocks : Array Miri.MIR.BasicBlock :=
  #[lmCfBlock .Return false, lmCfBlock .Return false, lmCfBlock .UnwindResume true]

/-- A vendored `Miri.Interpreter.Frame` for the driver at `loc` with continuation `ret`. -/
def lmCfFrame (loc : Miri.Interpreter.FrameLocation) (ret : Miri.Interpreter.ReturnContinuation) :
    Miri.Interpreter.Frame Provenance Unit Unit :=
  { body := { phase := .Built, argumentCount := 0, spreadArgument := none, locals := #[0],
              basicBlocks := lmCfBlocks }
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := ret
    returnPlace := .frameLocal 0 0 none ⟨0, zstLayoutData⟩ (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[⟨.dead, none⟩]
    vaList := #[]
    trackCallerArg := none
    location := loc }

/-- Vendored `ControlHooks` over the harness machine `LmState`; `cleanupFrame` runs the
supplied frame-exit operation (instantiated with `lmExitCall`), stashing typed failures in
`LmCtx.pending` so the classifier sees the genuine root cause. -/
def lmCfControlHooks (exitCall : LmState → Except LmExecFailure LmState) :
    Miri.Interpreter.ControlHooks Provenance Unit Unit LmState Unit Unit :=
  { bodySpan := fun _ => .ok ⟨0⟩
    returnOperand := fun _ s => (s, .ok ())
    popFrame := fun _ s =>
      match s.stack.frames.back? with
      | none => (s, .error (.stack .emptyStack))
      | some fr => ({ s with stack := ⟨s.stack.frames.pop⟩ }, .ok fr)
    copyReturn := fun _ _ _ s => (s, .ok ())
    cleanupFrame := fun _ _ _ s =>
      match exitCall s.machine with
      | .ok m => ({ s with machine := m }, .ok .normal)
      | .error e =>
        ({ s with machine := { s.machine with ctx := { s.machine.ctx with pending := some e } } },
          .error (.callback "frame teardown failed"))
    unwindTerminate := fun _ _ s =>
      (s, .error (.termination (.abort "panic in a function that cannot unwind"))) }

/-- Vendored `TerminatorHooks` over `LmState`; `readAssertCondition` yields `cond` (read from
harness memory by the caller), `assertPanic` follows the asserting frame's unwind action. -/
def lmCfTermHooks (exitCall : LmState → Except LmExecFailure LmState) (cond : Bool) :
    Miri.Interpreter.TerminatorHooks Provenance Unit Unit LmState Unit Unit Unit :=
  { lmCfControlHooks exitCall with
    evalDiscriminant := fun _ _ s => (s, .error (.unsupported "harness: SwitchInt"))
    compareSwitchCase := fun _ _ _ s => (s, .error (.unsupported "harness: SwitchInt"))
    call := fun _ _ s => (s, .error (.unsupported "harness: nested call"))
    tailCall := fun _ _ s => (s, .error (.unsupported "harness: tail call"))
    drop := fun _ _ _ _ s => (s, .error (.unsupported "harness: drop"))
    ignoreOptionalOverflowChecks := fun _ => false
    readAssertCondition := fun _ _ s => (s, .ok cond)
    assertPanic := fun _ _ unwind s =>
      Miri.Interpreter.ControlFlow.unwindToBlock (lmCfControlHooks exitCall) () unwind s }

/-- Control location reached by the active frame after a vendored `ControlFlow` transition. -/
inductive LmCfOutcome where
  | atBlock (bb : Nat)
  | unwinding
  deriving DecidableEq, Repr

/-- Run ONE terminator through vendored `Miri.Interpreter.ControlFlow.evalTerminator` on the
driver stack `frames` with machine `st`, returning the resulting active-frame location. -/
def lmCfRun (exitCall : LmState → Except LmExecFailure LmState) (cond : Bool)
    (frames : Array (Miri.Interpreter.Frame Provenance Unit Unit)) (st : LmState)
    (kind : Miri.MIR.TerminatorKind) : Except LmExecFailure (LmCfOutcome × LmState) :=
  match Miri.Interpreter.ControlFlow.evalTerminator (lmCfTermHooks exitCall cond) ()
      { sourceInfo := lmSrc, kind := kind } { stack := ⟨frames⟩, machine := st } with
  | (s, .error e) => .error (s.machine.ctx.pending.getD (.controlFlow e))
  | (s, .ok ()) =>
    match s.stack.currentFrame? with
    | none => .error (.controlFlow (.stack .emptyStack))
    | some fr =>
      match fr.location with
      | .mir loc => .ok (.atBlock loc.block, s.machine)
      | .unwinding _ => .ok (.unwinding, s.machine)

/-- `TerminatorKind.assert(cond == expected, target = bb1, unwind)` in the active frame. -/
def lmCfAssert (exitCall : LmState → Except LmExecFailure LmState) (cond expected : Bool)
    (unwind : Miri.MIR.UnwindAction) (st : LmState) :
    Except LmExecFailure (LmCfOutcome × LmState) :=
  lmCfRun exitCall cond #[lmCfFrame (.mir ⟨0, 0⟩) (.stop false)] st
    (.Assert (.Copy ⟨1, #[]⟩) expected .NullPointerDereference 1 unwind)

/-- Callee `UnwindResume` from location `calleeLoc` (a cleanup block or an `.unwinding`
location) whose call edge in the caller carries `unwind`: vendored `returnFromCurrentFrame`
pops the callee, runs `cleanupFrame` (frame teardown + protector release), then follows
`unwindToBlock unwind` in the caller. -/
def lmCfUnwindResume (exitCall : LmState → Except LmExecFailure LmState)
    (calleeLoc : Miri.Interpreter.FrameLocation) (unwind : Miri.MIR.UnwindAction) (st : LmState) :
    Except LmExecFailure (LmCfOutcome × LmState) :=
  lmCfRun exitCall true
    #[lmCfFrame (.mir ⟨0, 0⟩) (.stop false), lmCfFrame calleeLoc (.goto (some 1) unwind)] st
    .UnwindResume

/-- `TerminatorKind.unwindTerminate` executed from the active frame's cleanup block. -/
def lmCfUnwindTerminate (exitCall : LmState → Except LmExecFailure LmState) (st : LmState) :
    Except LmExecFailure (LmCfOutcome × LmState) :=
  lmCfRun exitCall true #[lmCfFrame (.mir ⟨2, 0⟩) (.stop false)] st (.UnwindTerminate .InCleanup)

/-- Fail-closed expectation on the vendored control-flow location (mismatch ⇒ `invalidProgram`
⇒ `.invalidOrUnsupported`, never a silent pass). -/
def lmCfExpect (o expected : LmCfOutcome) : Except LmExecFailure Unit :=
  if o = expected then .ok ()
  else .error (.controlFlow (.invalidProgram "harness control-flow location mismatch"))

/-- Map any `LmExecFailure` into the frozen `LmCrossFramePanicObs` domain. -/
def classifyLmFailure : LmExecFailure → LmCrossFramePanicObs
  | .abort => .abort
  | .controlFlow (.termination (.abort _)) => .abort
  | .controlFlow (.invalidProgram _) => .invalidOrUnsupported
  | .controlFlow (.unsupported _) => .invalidOrUnsupported
  | _ => .ub

def observeLm (r : Except LmExecFailure LmCrossFramePanicObs) : LmCrossFramePanicObs :=
  match r with
  | .ok o => o
  | .error e => classifyLmFailure e

/-! ## §2. The 28 Canonical Vendored `Miri` Scenarios (`0..27`) -/

def lmCase (tb : Bool) : Nat → Except LmExecFailure LmCrossFramePanicObs
  -- Case 0: cross-frame `&mut u32` call, `FnEntry` protector, writeback 42, return, read 42.
  | 0 => do
    let st := lmInit tb
    let (px, st) ← lmAllocStack st 4 align4
    let st ← lmStoreU32 st px 10
    let st := lmEnterCall st
    let (pr, st) ← lmRetagRef st px .Mutable .FnEntry
    let st ← lmStoreU32 st pr 42
    let st ← lmExitCall st
    let (v, _) ← lmLoadU32 st px
    .ok (.okVal 42 v)
  -- Case 1: cross-frame `&u32` call, `FnEntry` shared protector, read 77, return.
  | 1 => do
    let st := lmInit tb
    let (px, st) ← lmAllocStack st 4 align4
    let st ← lmStoreU32 st px 77
    let st := lmEnterCall st
    let (pr, st) ← lmRetagRef st px .Shared .FnEntry
    let (r, st) ← lmLoadU32 st pr
    let st ← lmExitCall st
    let (v, _) ← lmLoadU32 st px
    .ok (.okVal r v)
  -- Case 2: post-return caller parent write succeeds after `FnEntry` protector release.
  | 2 => do
    let st := lmInit tb
    let (px, st) ← lmAllocStack st 4 align4
    let st ← lmStoreU32 st px 10
    let st := lmEnterCall st
    let (pr, st) ← lmRetagRef st px .Mutable .FnEntry
    let st ← lmStoreU32 st pr 25
    let st ← lmExitCall st
    let st ← lmStoreU32 st px 99
    let (v, _) ← lmLoadU32 st px
    .ok (.okVal v v)
  -- Case 3: `&mut [u32; 2] = [10, 20]`, callee `FnEntry`, cast + in-bounds offset(+4), write 88.
  | 3 => do
    let st := lmInit tb
    let (pa, st) ← lmAllocStack st 8 align4
    let pa1 ← lmPtrOffsetInbounds st pa 4
    let st ← lmStoreU32 st pa 10
    let st ← lmStoreU32 st pa1 20
    let st := lmEnterCall st
    let (pr, st) ← lmRetagRef st pa .Mutable .FnEntry
    let pr1 ← lmPtrOffsetInbounds st pr 4
    let st ← lmStoreU32 st pr1 88
    let st ← lmExitCall st
    let (e0, st) ← lmLoadU32 st pa
    let (e1, _) ← lmLoadU32 st pa1
    .ok (.okVal 88 (e0 * 1000 + e1))
  -- Case 4: `&mut [u32; 2] = [11, 22]`, in-bounds offset(+4) write 33, offset(-4) write 44.
  | 4 => do
    let st := lmInit tb
    let (pa, st) ← lmAllocStack st 8 align4
    let pa1 ← lmPtrOffsetInbounds st pa 4
    let st ← lmStoreU32 st pa 11
    let st ← lmStoreU32 st pa1 22
    let st := lmEnterCall st
    let (pr, st) ← lmRetagRef st pa .Mutable .FnEntry
    let pr1 ← lmPtrOffsetInbounds st pr 4
    let st ← lmStoreU32 st pr1 33
    let pr0 ← lmPtrOffsetInbounds st pr1 (-4)
    let st ← lmStoreU32 st pr0 44
    let st ← lmExitCall st
    let (e0, st) ← lmLoadU32 st pa
    let (e1, _) ← lmLoadU32 st pa1
    .ok (.okVal 44 (e0 * 1000 + e1))
  -- Case 5: `&mut [u32; 2] = [5, 6]`, wrapping offset(+4) write 55, wrapping offset(-4) write 66.
  | 5 => do
    let st := lmInit tb
    let (pa, st) ← lmAllocStack st 8 align4
    let pa1 ← lmPtrOffsetInbounds st pa 4
    let st ← lmStoreU32 st pa 5
    let st ← lmStoreU32 st pa1 6
    let st := lmEnterCall st
    let (pr, st) ← lmRetagRef st pa .Mutable .FnEntry
    let pr1 ← lmPtrOffsetWrapping pr 4
    let st ← lmStoreU32 st pr1 55
    let pr0 ← lmPtrOffsetWrapping pr1 (-4)
    let st ← lmStoreU32 st pr0 66
    let st ← lmExitCall st
    let (e0, st) ← lmLoadU32 st pa
    let (e1, _) ← lmLoadU32 st pa1
    .ok (.okVal 66 (e0 * 1000 + e1))
  -- Case 6: wrapping offset(+400) OOB without deref, then wrapping(-400), write 34 -> valid.
  | 6 => do
    let st := lmInit tb
    let (px, st) ← lmAllocStack st 4 align4
    let st ← lmStoreU32 st px 12
    let st := lmEnterCall st
    let (pr, st) ← lmRetagRef st px .Mutable .FnEntry
    let q ← lmPtrOffsetWrapping pr 400
    let p' ← lmPtrOffsetWrapping q (-400)
    let st ← lmStoreU32 st p' 34
    let st ← lmExitCall st
    let (v, _) ← lmLoadU32 st px
    .ok (.okVal 34 v)
  -- Case 7: 2-level nested reborrow call outer -> mid(p1) -> inner(p2) -> LIFO normal release.
  | 7 => do
    let st := lmInit tb
    let (px, st) ← lmAllocStack st 4 align4
    let st ← lmStoreU32 st px 1
    let st := lmEnterCall st
    let (pm, st) ← lmRetagRef st px .Mutable .FnEntry
    let st := lmEnterCall st
    let (pi, st) ← lmRetagRef st pm .Mutable .FnEntry
    let st ← lmStoreU32 st pi 7
    let st ← lmExitCall st
    let st ← lmStoreU32 st pm 10
    let (vm, st) ← lmLoadU32 st pm
    let st ← lmExitCall st
    let st ← lmStoreU32 st px (vm + 10)
    let (v, _) ← lmLoadU32 st px
    .ok (.okVal v v)
  -- Case 8 [MODE-SENSITIVE #1]: foreign write through parent `px` while callee's `FnEntry` strong
  -- protector on `&mut x` is active (`tb=false => okVal 77 77`, `tb=true => ub`).
  | 8 => do
    let st := lmInit tb
    let (px, st) ← lmAllocStack st 4 align4
    let st ← lmStoreU32 st px 10
    let st := lmEnterCall st
    let (_pr, st) ← lmRetagRef st px .Mutable .FnEntry
    let st ← lmStoreU32 st px 77
    let st ← lmExitCall st
    let (v, _) ← lmLoadU32 st px
    .ok (.okVal 77 v)
  -- Case 9 [MODE-SENSITIVE #2]: write through `Frozen` `&T` retag (`tb=false => okVal 99 99`,
  -- `tb=true => ub`).
  | 9 => do
    let st := lmInit tb
    let (px, st) ← lmAllocStack st 4 align4
    let st ← lmStoreU32 st px 10
    let st := lmEnterCall st
    let (pr, st) ← lmRetagRef st px .Shared .FnEntry
    let st ← lmStoreU32 st pr 99
    let st ← lmExitCall st
    let (v, _) ← lmLoadU32 st px
    .ok (.okVal 99 v)
  -- Case 10: callee allocates local `y = 55`, returns `&raw const y`, callee exits (deallocating
  -- `y`), caller dereferences dangling pointer -> UAR `.ub` in BOTH modes.
  | 10 => do
    let st := lmInit tb
    let st := lmEnterCall st
    let (py, st) ← lmAllocStack st 4 align4
    let st ← lmStoreU32 st py 55
    let st ← lmExitCall st
    let (v, _) ← lmLoadU32 st py
    .ok (.okVal v v)
  -- Case 11: in-bounds `ptrOffsetInbounds` past end (+12 on 8-byte array) -> `.ub` in BOTH modes.
  | 11 => do
    let st := lmInit tb
    let (pa, st) ← lmAllocStack st 8 align4
    let st := lmEnterCall st
    let (pr, st) ← lmRetagRef st pa .Mutable .FnEntry
    let _ ← lmPtrOffsetInbounds st pr 12
    let _st ← lmExitCall st
    .ok (.okVal 0 0)
  -- Case 12: in-bounds `ptrOffsetInbounds` before start (-4) -> `.ub` in BOTH modes.
  | 12 => do
    let st := lmInit tb
    let (pa, st) ← lmAllocStack st 8 align4
    let st := lmEnterCall st
    let (pr, st) ← lmRetagRef st pa .Mutable .FnEntry
    let _ ← lmPtrOffsetInbounds st pr (-4)
    let _st ← lmExitCall st
    .ok (.okVal 0 0)
  -- Case 13: wrapping offset(+400) OOB followed by deref -> `.ub` in BOTH modes.
  | 13 => do
    let st := lmInit tb
    let (px, st) ← lmAllocStack st 4 align4
    let st ← lmStoreU32 st px 12
    let st := lmEnterCall st
    let (pr, st) ← lmRetagRef st px .Mutable .FnEntry
    let q ← lmPtrOffsetWrapping pr 400
    let (v, _) ← lmLoadU32 st q
    .ok (.okVal v v)
  -- Case 14: `TerminatorKind.assert(cond == true)` passes: the condition `1` is stored to and
  -- loaded from vendored `Miri` memory, and vendored `ControlFlow.evalTerminator (.Assert ..)`
  -- must jump to `target = bb1`.
  | 14 => do
    let st := lmInit tb
    let (pc, st) ← lmAllocStack st 4 align4
    let st ← lmStoreU32 st pc 1
    let (c, st) ← lmLoadU32 st pc
    let (o, _) ← lmCfAssert lmExitCall (c == 1) true .Unreachable st
    lmCfExpect o (.atBlock 1)
    .ok (.okVal 101 101)
  -- Case 15: `TerminatorKind.assert(cond == false)` passes (condition `0` loaded from memory).
  | 15 => do
    let st := lmInit tb
    let (pc, st) ← lmAllocStack st 4 align4
    let st ← lmStoreU32 st pc 0
    let (c, st) ← lmLoadU32 st pc
    let (o, _) ← lmCfAssert lmExitCall (c == 1) false .Unreachable st
    lmCfExpect o (.atBlock 1)
    .ok (.okVal 102 102)
  -- Case 16: `TerminatorKind.unreachable` via vendored `ControlFlow.evalTerminator`.
  | 16 => do
    lmUnreachableCheck
    .ok (.okVal 0 0)
  -- Case 17: callee `FnEntry` + write 15, failing `assert(.., unwind: .Cleanup bb2)` (vendored
  -- `assertPanic` -> `unwindToBlock`), cleanup mutates `*r = 115`, callee `UnwindResume`
  -- (vendored `returnFromCurrentFrame` pops + tears down the callee frame + follows caller's
  -- `.Cleanup bb2` catch pad) -> outer harness observes `.unwound 115`.
  | 17 => do
    let st := lmInit tb
    let (px, st) ← lmAllocStack st 4 align4
    let st ← lmStoreU32 st px 10
    let st := lmEnterCall st
    let (pr, st) ← lmRetagRef st px .Mutable .FnEntry
    let st ← lmStoreU32 st pr 15
    let st := lmStartUnwind st
    let (o, st) ← lmCfAssert lmExitCall false true (.Cleanup 2) st
    lmCfExpect o (.atBlock 2)
    let st ← lmStoreU32 st pr 115
    let (o, st) ← lmCfUnwindResume lmExitCall (.mir ⟨2, 0⟩) (.Cleanup 2) st
    lmCfExpect o (.atBlock 2)
    let st ← lmCatchUnwind st
    let (v, _) ← lmLoadU32 st px
    .ok (.unwound v)
  -- Case 18: failing `assert(.., unwind: .Cleanup bb2)`, cleanup mutates `*r = 116`, vendored
  -- `UnwindTerminate` -> `.abort`.
  | 18 => do
    let st := lmInit tb
    let (px, st) ← lmAllocStack st 4 align4
    let st ← lmStoreU32 st px 10
    let st := lmEnterCall st
    let (pr, st) ← lmRetagRef st px .Mutable .FnEntry
    let st := lmStartUnwind st
    let (o, st) ← lmCfAssert lmExitCall false true (.Cleanup 2) st
    lmCfExpect o (.atBlock 2)
    let st ← lmStoreU32 st pr 116
    let _ ← lmCfUnwindTerminate lmExitCall st
    .ok .invalidOrUnsupported
  -- Case 19: failing `assert(.., unwind: .Terminate)` -> vendored `unwindToBlock` -> `unwindTerminate`.
  | 19 => do
    let _ ← lmCfAssert lmExitCall false true (.Terminate .Abi) (lmInit tb)
    .ok .invalidOrUnsupported
  -- Case 20: failing `assert(.., unwind: .Unreachable)` -> vendored `unwindToBlock` UB.
  | 20 => do
    let _ ← lmCfAssert lmExitCall false true .Unreachable (lmInit tb)
    .ok .invalidOrUnsupported
  -- Case 21: callee `FnEntry` + partial writeback 55 + failing `assert(.., unwind: .Continue)`;
  -- vendored `UnwindResume` pops the callee (releasing `pr` in `cleanupFrame`) into the caller's
  -- `.Cleanup bb2`; caller cleanup reads 55, writes 65 through `pc` (succeeds iff `pr` released),
  -- caller `UnwindResume` pops into the outer catch pad -> `.okCleanupRecovered 65 65`.
  | 21 => do
    let st := lmInit tb
    let (px, st) ← lmAllocStack st 4 align4
    let st ← lmStoreU32 st px 10
    let st := lmEnterCall st
    let (pc, st) ← lmRetagRef st px .Mutable .FnEntry
    let st := lmEnterCall st
    let (pr, st) ← lmRetagRef st pc .Mutable .FnEntry
    let st ← lmStoreU32 st pr 55
    let st := lmStartUnwind st
    let (o, st) ← lmCfAssert lmExitCall false true .Continue st
    lmCfExpect o .unwinding
    let (o, st) ← lmCfUnwindResume lmExitCall (.unwinding ⟨0⟩) (.Cleanup 2) st
    lmCfExpect o (.atBlock 2)
    let (vPartial, st) ← lmLoadU32 st pc
    let st ← lmStoreU32 st pc (vPartial + 10)
    let (o, st) ← lmCfUnwindResume lmExitCall (.mir ⟨2, 0⟩) (.Cleanup 2) st
    lmCfExpect o (.atBlock 2)
    let st ← lmCatchUnwind st
    let (vFinal, _) ← lmLoadU32 st px
    .ok (.okCleanupRecovered vFinal vFinal)
  -- Case 22: same partial writeback + callee protector release, caller cleanup writes 66, then
  -- vendored `UnwindTerminate` -> `.abort`.
  | 22 => do
    let st := lmInit tb
    let (px, st) ← lmAllocStack st 4 align4
    let st ← lmStoreU32 st px 10
    let st := lmEnterCall st
    let (pc, st) ← lmRetagRef st px .Mutable .FnEntry
    let st := lmEnterCall st
    let (pr, st) ← lmRetagRef st pc .Mutable .FnEntry
    let st ← lmStoreU32 st pr 55
    let st := lmStartUnwind st
    let (o, st) ← lmCfAssert lmExitCall false true .Continue st
    lmCfExpect o .unwinding
    let (o, st) ← lmCfUnwindResume lmExitCall (.unwinding ⟨0⟩) (.Cleanup 2) st
    lmCfExpect o (.atBlock 2)
    let st ← lmStoreU32 st pc 66
    let _ ← lmCfUnwindTerminate lmExitCall st
    .ok .invalidOrUnsupported
  -- Case 23: 3-frame LIFO unwind `outer(po) -> mid(pm) -> leaf(pl)`: leaf asserts with `.Continue`;
  -- vendored `UnwindResume` pops leaf (releasing `pl`) into mid's `.Continue` edge (mid becomes
  -- `.unwinding`), pops mid (releasing `pm`) into outer's `.Cleanup bb2`; outer cleanup reads
  -- preserved 3 and writes 300 through `po` (succeeds iff BOTH `pl` and `pm` released), outer
  -- `UnwindResume` pops into the root catch pad -> `.okCleanupRecovered 300 300`.
  | 23 => do
    let st := lmInit tb
    let (px, st) ← lmAllocStack st 4 align4
    let st ← lmStoreU32 st px 1
    let st := lmEnterCall st
    let (po, st) ← lmRetagRef st px .Mutable .FnEntry
    let st := lmEnterCall st
    let (pm, st) ← lmRetagRef st po .Mutable .FnEntry
    let st ← lmStoreU32 st pm 2
    let st := lmEnterCall st
    let (pl, st) ← lmRetagRef st pm .Mutable .FnEntry
    let st ← lmStoreU32 st pl 3
    let st := lmStartUnwind st
    let (o, st) ← lmCfAssert lmExitCall false true .Continue st
    lmCfExpect o .unwinding
    let (o, st) ← lmCfUnwindResume lmExitCall (.unwinding ⟨0⟩) .Continue st
    lmCfExpect o .unwinding
    let (o, st) ← lmCfUnwindResume lmExitCall (.unwinding ⟨0⟩) (.Cleanup 2) st
    lmCfExpect o (.atBlock 2)
    let (v3, st) ← lmLoadU32 st po
    let st ← lmStoreU32 st po (v3 * 100)
    let (o, st) ← lmCfUnwindResume lmExitCall (.mir ⟨2, 0⟩) (.Cleanup 2) st
    lmCfExpect o (.atBlock 2)
    let st ← lmCatchUnwind st
    let (vFinal, _) ← lmLoadU32 st px
    .ok (.okCleanupRecovered vFinal vFinal)
  -- Case 24: callee `FnEntry` + write 44 + `.Continue` panic; vendored `UnwindResume` pops the
  -- callee into the caller call edge `unwind: .Terminate` -> `unwindTerminate` -> `.abort`.
  | 24 => do
    let st := lmInit tb
    let (px, st) ← lmAllocStack st 4 align4
    let st ← lmStoreU32 st px 10
    let st := lmEnterCall st
    let (pr, st) ← lmRetagRef st px .Mutable .FnEntry
    let st ← lmStoreU32 st pr 44
    let st := lmStartUnwind st
    let (o, st) ← lmCfAssert lmExitCall false true .Continue st
    lmCfExpect o .unwinding
    let _ ← lmCfUnwindResume lmExitCall (.unwinding ⟨0⟩) (.Terminate .Abi) st
    .ok .invalidOrUnsupported
  -- Case 25: same, caller call edge `unwind: .Unreachable` -> vendored `unwindToBlock` UB.
  | 25 => do
    let st := lmInit tb
    let (px, st) ← lmAllocStack st 4 align4
    let st ← lmStoreU32 st px 10
    let st := lmEnterCall st
    let (pr, st) ← lmRetagRef st px .Mutable .FnEntry
    let st ← lmStoreU32 st pr 44
    let st := lmStartUnwind st
    let (o, st) ← lmCfAssert lmExitCall false true .Continue st
    lmCfExpect o .unwinding
    let _ ← lmCfUnwindResume lmExitCall (.unwinding ⟨0⟩) .Unreachable st
    .ok .invalidOrUnsupported
  -- Case 26 & 27: bare root frame unwind via vendored `ControlFlow.returnFromCurrentFrame` -> `.ub`.
  | 26 | 27 => do
    lmRootUnwindCheck
    .ok (.okVal 0 0)
  | _ => .ok .invalidOrUnsupported

/-- Frozen vendored `Miri` observer (`tb = false` vs `tb = true`), fail-closed
`.invalidOrUnsupported` for all `idx ≥ 28`. -/
def lmCrossFramePanicObserve (tb : Bool) (idx : Nat) : LmCrossFramePanicObs :=
  observeLm (lmCase tb idx)

-- Derive kernel-evaluable twins of the harness helpers and prove exact equality `@F = @F_U`!
unroll_loops lmAllocStackU := lmAllocStack fuel 0 with allocatePtrU
unroll_loops lmBeforeDeallocationU := lmBeforeDeallocation fuel 0
  with beforeMemoryDeallocationU, deallocateBorrowRangeU
unroll_loops lmDeallocHooksU := lmDeallocHooks fuel 0 with lmBeforeDeallocationU
unroll_loops lmDeallocStackOneU := lmDeallocStackOne fuel 0 with deallocatePtrWithU, lmDeallocHooksU
unroll_loops lmAccessTargetU := lmAccessTarget fuel 0 with getAllocInfoU
unroll_loops lmTreeAccessU := lmTreeAccess fuel 0
  with beforeMemoryWriteU, beforeMemoryReadU, performBorrowAccessRangeU
unroll_loops lmStoreU32U := lmStoreU32 fuel 0 with lmAccessTargetU, lmTreeAccessU
unroll_loops lmLoadU32U := lmLoadU32 fuel 0 with lmAccessTargetU, lmTreeAccessU
unroll_loops lmPtrOffsetInboundsU := lmPtrOffsetInbounds fuel 0 with getAllocInfoU
unroll_loops lmRetagRefU := lmRetagRef fuel 0 with retagPointerValueU
unroll_loops lmReleaseOneU := lmReleaseOne fuel 0 with releaseProtectorU
unroll_loops lmExitCallU := lmExitCall fuel 0 with lmDeallocStackOneU, lmReleaseOneU
unroll_loops lmCaseU := lmCase fuel 0 with lmAllocStackU, lmStoreU32U, lmLoadU32U,
  lmPtrOffsetInboundsU, lmRetagRefU, lmExitCallU
unroll_loops lmCrossFramePanicObserveU := lmCrossFramePanicObserve fuel 0 with lmCaseU

/-- Frozen expected LeanMiri table for `treeBorrows = false`. -/
def lmExpectedBasicList : List LmCrossFramePanicObs :=
  [.okVal 42 42,
   .okVal 77 77,
   .okVal 99 99,
   .okVal 88 10088,
   .okVal 44 44033,
   .okVal 66 66055,
   .okVal 34 34,
   .okVal 20 20,
   .okVal 77 77,
   .okVal 99 99,
   .ub,
   .ub,
   .ub,
   .ub,
   .okVal 101 101,
   .okVal 102 102,
   .ub,
   .unwound 115,
   .abort,
   .abort,
   .ub,
   .okCleanupRecovered 65 65,
   .abort,
   .okCleanupRecovered 300 300,
   .abort,
   .ub,
   .ub,
   .ub]

/-- Frozen expected LeanMiri table for `treeBorrows = true`. -/
def lmExpectedTbList : List LmCrossFramePanicObs :=
  [.okVal 42 42,
   .okVal 77 77,
   .okVal 99 99,
   .okVal 88 10088,
   .okVal 44 44033,
   .okVal 66 66055,
   .okVal 34 34,
   .okVal 20 20,
   .ub,
   .ub,
   .ub,
   .ub,
   .ub,
   .ub,
   .okVal 101 101,
   .okVal 102 102,
   .ub,
   .unwound 115,
   .abort,
   .abort,
   .ub,
   .okCleanupRecovered 65 65,
   .abort,
   .okCleanupRecovered 300 300,
   .abort,
   .ub,
   .ub,
   .ub]

/-- **Kernel-checked 56-cell vendored `Miri` execution table (`28 scenarios × 2 modes`)**:
rewrites through `lmCrossFramePanicObserveU.eq_src` (kernel-checked equality with the real
vendored `Miri` definitions) and closes purely by kernel reduction (zero `native_decide`). -/
theorem lmCrossFramePanicObserve_table :
    (List.range lmCanonicalCaseCount).map (lmCrossFramePanicObserve false) = lmExpectedBasicList ∧
    (List.range lmCanonicalCaseCount).map (lmCrossFramePanicObserve true) = lmExpectedTbList := by
  rw [lmCrossFramePanicObserveU.eq_src]
  constructor <;> kernel_rfl

/-- Out-of-range scenarios are fail-closed `.invalidOrUnsupported` for both modes. -/
theorem lmCrossFramePanicObserve_out_of_range (tb : Bool) (idx : Nat)
    (h : lmCanonicalCaseCount ≤ idx) :
    lmCrossFramePanicObserve tb idx = .invalidOrUnsupported := by
  unfold lmCanonicalCaseCount at h
  have hCase : lmCase tb idx = .ok .invalidOrUnsupported := by
    unfold lmCase
    split <;> first | rfl | omega
  unfold lmCrossFramePanicObserve
  rw [hCase]
  rfl

/-- Exact typed-failure diagnostics on vendored `Miri` (`tb = true`) confirming genuine root
causes on Cases `8`, `9`, `10`, `11`, `12`, `16`, `27` (memory / Tree Borrows / pointer offset /
control flow) and on the `assert` / `UnwindAction` / `unwindTerminate` Cases `18`, `19`, `20`, `22`,
`24`, `25`, whose abort / UB verdicts are produced by vendored
`Miri.Interpreter.ControlFlow.{evalTerminator, unwindToBlock, returnFromCurrentFrame}` (not
harness-hardcoded constants). -/
theorem lm_tb_exact_failure_diagnostics :
    lmCase true 8 = .error (.treeAccess (.AccessFailure ⟨0, 4⟩
      (.TransitionError 1 (.ProtectedDisabled .Unique)))) ∧
    lmCase true 9 = .error (.treeAccess (.AccessFailure ⟨0, 4⟩
      (.TransitionError 1 (.ChildAccessForbidden .Frozen)))) ∧
    lmCase true 10 = .error (.access (.allocationLookup (.deadAllocation ⟨1, by decide⟩))) ∧
    lmCase true 11 = .error (.pointerOffset (.access
      (.pointerOutOfBounds ⟨1, by decide⟩ ⟨8⟩ 0 12 .inboundsPointerArithmetic))) ∧
    lmCase true 12 = .error (.pointerOffset (.access
      (.pointerOutOfBounds ⟨1, by decide⟩ ⟨8⟩ 0 (-4) .inboundsPointerArithmetic))) ∧
    lmCase true 16 = .error (.controlFlow (.undefinedBehavior "Unreachable")) ∧
    lmCase true 27 = .error (.controlFlow
      (.undefinedBehavior "unwinding past the topmost stack frame")) ∧
    -- Control-flow root causes come from vendored `ControlFlow.{unwindToBlock, evalTerminator}`:
    lmCase true 18 = .error (.controlFlow
      (.termination (.abort "panic in a function that cannot unwind"))) ∧
    lmCase true 19 = .error (.controlFlow
      (.termination (.abort "panic in a function that cannot unwind"))) ∧
    lmCase true 20 = .error (.controlFlow
      (.undefinedBehavior "unwinding past a frame that does not allow unwinding")) ∧
    lmCase true 22 = .error (.controlFlow
      (.termination (.abort "panic in a function that cannot unwind"))) ∧
    lmCase true 24 = .error (.controlFlow
      (.termination (.abort "panic in a function that cannot unwind"))) ∧
    lmCase true 25 = .error (.controlFlow
      (.undefinedBehavior "unwinding past a frame that does not allow unwinding")) := by
  rw [lmCaseU.eq_src]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> kernel_rfl

/-- Exact LeanMiri Tree Borrows mode-sensitivity `↔` theorem: Cases `8` and `9` flip between
`treeBorrows = false` and `treeBorrows = true`, and every other canonical case agrees. -/
def lmCaseModeSensitive : Nat → Bool
  | 8 | 9 => true
  | _ => false

theorem lmCrossFramePanicObserve_mode_sensitivity :
    lmCrossFramePanicObserve false 8 = .okVal 77 77 ∧
    lmCrossFramePanicObserve true 8 = .ub ∧
    lmCrossFramePanicObserve false 9 = .okVal 99 99 ∧
    lmCrossFramePanicObserve true 9 = .ub ∧
    (∀ idx, idx < lmCanonicalCaseCount →
      (lmCrossFramePanicObserve false idx ≠ lmCrossFramePanicObserve true idx ↔
        lmCaseModeSensitive idx = true)) := by
  have hB := lmCrossFramePanicObserve_table.1
  have hT := lmCrossFramePanicObserve_table.2
  have hAll : ((List.range lmCanonicalCaseCount).all fun idx =>
      decide ((lmExpectedBasicList[idx]? ≠ lmExpectedTbList[idx]?) ↔
        lmCaseModeSensitive idx = true)) = true := by decide
  have cellB : ∀ idx, idx < lmCanonicalCaseCount →
      some (lmCrossFramePanicObserve false idx) = lmExpectedBasicList[idx]? := by
    intro idx hi
    have h' := congrArg (fun l => l[idx]?) hB
    simpa [List.getElem?_map, List.getElem?_range hi] using h'
  have cellT : ∀ idx, idx < lmCanonicalCaseCount →
      some (lmCrossFramePanicObserve true idx) = lmExpectedTbList[idx]? := by
    intro idx hi
    have h' := congrArg (fun l => l[idx]?) hT
    simpa [List.getElem?_map, List.getElem?_range hi] using h'
  refine ⟨Option.some.inj (cellB 8 (by decide)), Option.some.inj (cellT 8 (by decide)),
    Option.some.inj (cellB 9 (by decide)), Option.some.inj (cellT 9 (by decide)), ?_⟩
  intro idx hi
  have hIff := of_decide_eq_true (List.all_eq_true.mp hAll idx (List.mem_range.mpr hi))
  rw [← cellB idx hi, ← cellT idx hi] at hIff
  simpa [Option.some.injEq] using hIff

/-! ## §3. Universal Vendored `Miri` Laws (Pointer Offset, Tree Borrows Protectors, & Unwind) -/

section MiriUniversalLaws

private theorem truncateToTargetUsize_lmPtrArith (x : UInt64) :
    lmPtrArith.truncateToTargetUsize x = .ok x := by
  have hMod : x.toNat < 2 ^ 64 := x.toBitVec.isLt
  have hBit : (BitVec.zeroExtend 128 (BitVec.extractLsb 63 0 (BitVec.ofNat 128 x.toNat))).toNat = x.toNat := by
    have h128 : x.toNat < 2 ^ 128 := Nat.lt_trans hMod (by decide)
    simp only [BitVec.zeroExtend, BitVec.extractLsb, BitVec.extractLsb', BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.shiftRight_zero, Nat.mod_eq_of_lt h128, Nat.mod_eq_of_lt hMod]
  have hOf : UInt64.ofNat x.toNat = x := by
    cases x; simp [UInt64.ofNat, UInt64.toNat]
  change (if (BitVec.zeroExtend 128 (BitVec.extractLsb 63 0 (BitVec.ofNat 128 x.toNat))).toNat < 2 ^ 64 then
      Except.ok (UInt64.ofNat (BitVec.zeroExtend 128 (BitVec.extractLsb 63 0 (BitVec.ofNat 128 x.toNat))).toNat)
    else Except.error PointerError.unsignedConversionOverflow) = Except.ok x
  rw [hBit]
  simp only [hMod, ↓reduceIte, hOf]

/-- **Universal wrapping pointer offset round-trip** on vendored
`Miri.Memory.Pointer.wrappingSignedOffset`: for EVERY provenance `Prov`, EVERY pointer `ptr`,
and EVERY signed 64-bit byte offset `delta : Int64`, offsetting by `delta` and then `-delta`
recovers the EXACT original pointer (both address and provenance). -/
theorem lm_ptr_wrappingSignedOffset_roundtrip {Prov : Type} (ptr : Pointer Prov) (delta : Int64) :
    (ptr.wrappingSignedOffset delta lmPtrArith >>=
      fun p1 => p1.wrappingSignedOffset (-delta) lmPtrArith) = .ok ptr := by
  cases ptr with
  | mk off prov =>
    cases off with
    | mk bytes =>
      unfold Miri.Memory.Pointer.wrappingSignedOffset Miri.Memory.Pointer.wrappingOffset
        Miri.ABI.Size.ofBytes
      dsimp only [bind, Except.bind, pure, Except.pure]
      rw [truncateToTargetUsize_lmPtrArith]
      dsimp only
      rw [truncateToTargetUsize_lmPtrArith]
      dsimp only
      congr 2
      have hNeg : (-delta).toUInt64 = -delta.toUInt64 := by
        cases delta; rfl
      rw [hNeg, UInt64.add_assoc, UInt64.add_right_neg, UInt64.add_zero]

/-- **Universal `Miri.Interpreter.ControlFlow.evalTerminator` `.Unreachable` UB law**:
holds for EVERY `TerminatorHooks`, `choice`, `SourceInfo`, and `StepState`. -/
theorem lm_controlFlow_unreachable_ub {P L E M C Op Imm : Type}
    (hooks : Miri.Interpreter.TerminatorHooks P L E M C Op Imm) (choice : C)
    (si : Miri.MIR.SourceInfo) (st : Miri.Interpreter.StepState P L E M) :
    Miri.Interpreter.ControlFlow.evalTerminator hooks choice { sourceInfo := si, kind := .Unreachable } st =
      (st, .error (.undefinedBehavior "Unreachable")) := rfl

/-- **Universal `Miri.Interpreter.ControlFlow.unwindToBlock` `.Cleanup` & `.Unreachable` laws**:
for EVERY `ControlHooks`, `choice`, and `StepState`:
- `.Cleanup blk` jumps directly to `(blk, 0)` on a non-empty stack;
- `.Unreachable` immediately faults with `"unwinding past a frame that does not allow unwinding"`. -/
theorem lm_controlFlow_unwindToBlock_laws {P L E M C Op : Type}
    (hooks : Miri.Interpreter.ControlHooks P L E M C Op) (choice : C)
    (st : Miri.Interpreter.StepState P L E M) (blk : Miri.MIR.BasicBlockId) :
    Miri.Interpreter.ControlFlow.unwindToBlock hooks choice (.Cleanup blk) st =
      Miri.Interpreter.ControlFlow.goToBlock blk st ∧
    Miri.Interpreter.ControlFlow.unwindToBlock hooks choice .Unreachable st =
      (st, .error (.undefinedBehavior "unwinding past a frame that does not allow unwinding")) :=
  ⟨rfl, rfl⟩

/-- **Universal root-frame unwind UB law** on vendored
`Miri.Interpreter.ControlFlow.returnFromCurrentFrame`: whenever the stack has a single frame
(`frames = #[fr]`) at a cleanup block (`bb.cleanup = true`), unwinding out of the root frame
immediately faults with `"unwinding past the topmost stack frame"`. -/
theorem lm_controlFlow_root_unwind_ub {P L E M C Op : Type}
    (hooks : Miri.Interpreter.ControlHooks P L E M C Op) (choice : C)
    (fr : Miri.Interpreter.Frame P L E) (mach : M)
    (blkIdx stmtIdx : Nat) (bb : Miri.MIR.BasicBlock)
    (hLoc : fr.location = .mir ⟨blkIdx, stmtIdx⟩)
    (hBb : fr.body.basicBlocks[blkIdx]? = some bb) (hClean : bb.cleanup = true) :
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame hooks choice true
        { stack := ⟨#[fr]⟩, machine := mach } =
      ({ stack := ⟨#[fr]⟩, machine := mach },
        .error (.undefinedBehavior "unwinding past the topmost stack frame")) := by
  unfold Miri.Interpreter.ControlFlow.returnFromCurrentFrame
  have h0 : (#[fr] : Array (Miri.Interpreter.Frame P L E))[0]? = some fr := rfl
  simp only [Miri.Interpreter.Stack.currentFrame?, Array.back?, Array.size_singleton,
    Nat.sub_self, h0, hLoc, hBb, hClean, Id.run, ↓reduceIte, beq_self_eq_true, Bool.and_self]
  rfl

/-- **Universal 4-way `TerminatorKind.assert` law on vendored `ControlFlow.evalTerminator`** (driver
`lmCfAssert`), for EVERY frame-exit operation, EVERY harness state `st` without a pending failure,
and EVERY condition bit `b`:
- `assert(b == b)` jumps to `target = bb1` for every unwind action, leaving `st` untouched;
- `assert(b == !b, .Cleanup bb)` lands on the cleanup pad `bb`;
- `assert(b == !b, .Continue)` leaves the frame `.unwinding` (propagating to the caller);
- `assert(b == !b, .Terminate r)` aborts via `unwindTerminate`;
- `assert(b == !b, .Unreachable)` faults with vendored `unwindToBlock`'s UB. -/
theorem lm_cf_assert_four_way (exitCall : LmState → Except LmExecFailure LmState) (st : LmState)
    (hP : st.ctx.pending = none) (b : Bool) (u : Miri.MIR.UnwindAction) (bb : Nat)
    (r : Miri.MIR.UnwindTerminateReason) :
    lmCfAssert exitCall b b u st = .ok (.atBlock 1, st) ∧
    lmCfAssert exitCall b (!b) (.Cleanup bb) st = .ok (.atBlock bb, st) ∧
    lmCfAssert exitCall b (!b) .Continue st = .ok (.unwinding, st) ∧
    lmCfAssert exitCall b (!b) (.Terminate r) st =
      .error (.controlFlow (.termination (.abort "panic in a function that cannot unwind"))) ∧
    lmCfAssert exitCall b (!b) .Unreachable st =
      .error (.controlFlow
        (.undefinedBehavior "unwinding past a frame that does not allow unwinding")) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · cases b <;> rfl
  · cases b <;> rfl
  · cases b <;> rfl
  · cases b
    · show Except.error (st.ctx.pending.getD (.controlFlow
          (.termination (.abort "panic in a function that cannot unwind")))) = _
      rw [hP]; rfl
    · show Except.error (st.ctx.pending.getD (.controlFlow
          (.termination (.abort "panic in a function that cannot unwind")))) = _
      rw [hP]; rfl
  · cases b
    · show Except.error (st.ctx.pending.getD (.controlFlow
          (.undefinedBehavior "unwinding past a frame that does not allow unwinding"))) = _
      rw [hP]; rfl
    · show Except.error (st.ctx.pending.getD (.controlFlow
          (.undefinedBehavior "unwinding past a frame that does not allow unwinding"))) = _
      rw [hP]; rfl

/-- **Universal `GlobalState.endCall` LIFO protector removal law**:
1. Calling `endCall` on a frame `f` with `protectedTags = #[(id, tag)]` removes `tag` from
   `global.protectedTags`;
2. Any OTHER tag `outerTag ≠ tag` owned by an outer caller frame remains protected in
   `global.protectedTags` until that outer frame itself exits (`LIFO` stack discipline!). -/
theorem lm_globalState_endCall_lifo_preservation (gs : GlobalState)
    (idOuter idInner : AllocId) (tagOuter tagInner : BorTag) (hNe : tagInner ≠ tagOuter) :
    let gs1 := { gs with protectedTags :=
      (gs.protectedTags.insert tagOuter .StrongProtector).insert tagInner .StrongProtector }
    let innerFrame : FrameState := { protectedTags := #[(idInner, tagInner)] }
    let outerFrame : FrameState := { protectedTags := #[(idOuter, tagOuter)] }
    let afterInner := gs1.endCall innerFrame
    let afterOuter := afterInner.endCall outerFrame
    afterInner.protectedTags.contains tagInner = false ∧
    afterInner.protectedTags.contains tagOuter = true ∧
    afterOuter.protectedTags.contains tagOuter = false := by
  dsimp only [GlobalState.endCall, ProtectedTags.contains, ProtectedTags.get,
    ProtectedTags.insert, ProtectedTags.remove]
  have hNe' : tagOuter ≠ tagInner := Ne.symm hNe
  simp only [Array.foldl]
  refine ⟨?_, ?_, ?_⟩
  · simp [hNe']
    intro a b h
    rcases h with ⟨_, hne, _⟩ | ⟨rfl, _⟩
    · exact hne
    · exact hNe'
  · simp [hNe']
  · simp
    intro _ _ _ h2 _
    exact h2

/-- Computable kernel-checkable witness verifying both single-frame protector release and
nested 2-frame LIFO protector ordering directly on vendored `Miri.TreeBorrows.BorrowTree`. -/
def lmMultiframeLifoCheck : Bool :=
  let singleOk :=
    let st0 := lmInit true
    match lmAllocStack st0 4 align4 with
    | .ok (px, st1) =>
      match lmStoreU32 st1 px 10 with
      | .ok st2 =>
        let st3 := lmEnterCall st2
        match lmRetagRef st3 px .Mutable .FnEntry with
        | .ok (_pr, st4) =>
          !(lmStoreU32 st4 px 77).isOk &&
          (match lmExitCall st4 with
           | .ok st5 => (lmStoreU32 st5 px 99).isOk
           | .error _ => false)
        | .error _ => false
      | .error _ => false
    | .error _ => false
  let nestedOk :=
    let st0 := lmInit true
    match lmAllocStack st0 4 align4 with
    | .ok (px, st1) =>
      match lmStoreU32 st1 px 1 with
      | .ok st2 =>
        let st3 := lmEnterCall st2
        match lmRetagRef st3 px .Mutable .FnEntry with
        | .ok (pm, st4) =>
          let st5 := lmEnterCall st4
          match lmRetagRef st5 pm .Mutable .FnEntry with
          | .ok (pl, st6) =>
            match lmStoreU32 st6 pl 3 with
            | .ok st7 =>
              match lmExitCall st7 with
              | .ok stAfterLeaf =>
                !(lmStoreU32 stAfterLeaf px 88).isOk &&
                (lmStoreU32 stAfterLeaf pm 20).isOk &&
                (match lmExitCall stAfterLeaf with
                 | .ok stAfterMid => (lmStoreU32 stAfterMid px 300).isOk
                 | .error _ => false)
              | .error _ => false
            | .error _ => false
          | .error _ => false
        | .error _ => false
      | .error _ => false
    | .error _ => false
  singleOk && nestedOk

/-- **Universal `BorrowTree` `FnEntry` protector activation, foreign-write conflict,
`releaseProtector`, and post-release parent write success**:
1. Single frame: foreign write while protected fails, succeeds after `lmExitCall`.
2. Nested 2-frame LIFO (`outer -> mid -> leaf`): popping `leaf` releases `leaf`'s protector while
   keeping `mid`'s protector active (blocking grandparent write via `px` while allowing `mid` write
   via `pm`), and popping `mid` then releases `mid`'s protector allowing grandparent write `300`. -/
theorem lm_multiframe_lifo_protector_release_witness : lmMultiframeLifoCheck = true := by
  unfold lmMultiframeLifoCheck
  rw [lmAllocStackU.eq_src, lmStoreU32U.eq_src, lmRetagRefU.eq_src, lmExitCallU.eq_src]
  kernel_rfl

end MiriUniversalLaws

/-! ## §4. Direct Two-Sided `stepMirFn` ↔ `Miri.Interpreter.Step.step` Simulation Bridge -/

section StepSimulationBridge

/-- **Unified Two-Sided `stepMirFn` ↔ `Miri.Interpreter.Step.step` Lockstep Simulation Bundle**:
packages the exact, unmodified step-level correspondence theorems between
`Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn` and vendored `Miri.Interpreter.Step.step` for:
1. `TerminatorKind.unreachable` (arbitrary stack depth UB);
2. `TerminatorKind.assert` (pass, dead/uninit UB, and failing 4-way direct unwind across
   `.cleanup`, `.unreachable`, `.terminate`, `.continue_`);
3. Cross-frame `Call`, `Return`, and multi-frame LIFO `UnwindResume` (including the exact
   `rootUnwindCeiling = true` divergence vs. `rootUnwindCeiling = false` UB agreement);
4. Safe reference creation, reborrow, deref read & write;
5. In-bounds `BinOp.offset` (`step_binOp_offset_simulation`) and wrapping
   `core::intrinsics::arith_offset` (`call_intrinsic_arithOffset_stage1_simulation`);
6. Six-state Tree Borrows per-node transitions (`performAccess_permission_simulation`) and
   `BorrowTree.releaseProtector` (`borrowTree_releaseProtector_full_simulation`). -/
theorem lm_stepMirFn_miri_lockstep_simulations :
    (type_of% @step_terminator_unreachable_ub_simulation) ∧
    (type_of% @step_terminator_assert_local_simulation) ∧
    (type_of% @step_terminator_assert_failed_directUnwind_simulation) ∧
    (type_of% @step_terminator_call_simulation) ∧
    (type_of% @step_terminator_return_callee_simulation) ∧
    (type_of% @step_terminator_call_linked_panic_unwind_simulation) ∧
    (type_of% @step_terminator_unwindResume_multiFrame_simulation) ∧
    (type_of% @step_terminator_unwindResume_root_panic_vs_ub_divergence) ∧
    (type_of% @step_terminator_unwindResume_root_cleared_ceiling_ub_agreement) ∧
    (type_of% @evalRvalue_ref_simulation) ∧
    (type_of% @evalRvalue_reborrow_safeRef_simulation) ∧
    (type_of% @step_safeRef_deref_read_simulation) ∧
    (type_of% @step_safeRef_deref_write_simulation) ∧
    (type_of% @step_binOp_offset_simulation) ∧
    (type_of% @call_intrinsic_arithOffset_stage1_simulation) ∧
    (type_of% @performAccess_permission_simulation) ∧
    (type_of% @borrowTree_releaseProtector_full_simulation) :=
  ⟨@step_terminator_unreachable_ub_simulation,
   @step_terminator_assert_local_simulation,
   @step_terminator_assert_failed_directUnwind_simulation,
   @step_terminator_call_simulation,
   @step_terminator_return_callee_simulation,
   @step_terminator_call_linked_panic_unwind_simulation,
   @step_terminator_unwindResume_multiFrame_simulation,
   @step_terminator_unwindResume_root_panic_vs_ub_divergence,
   @step_terminator_unwindResume_root_cleared_ceiling_ub_agreement,
   @evalRvalue_ref_simulation,
   @evalRvalue_reborrow_safeRef_simulation,
   @step_safeRef_deref_read_simulation,
   @step_safeRef_deref_write_simulation,
   @step_binOp_offset_simulation,
   @call_intrinsic_arithOffset_stage1_simulation,
   @performAccess_permission_simulation,
   @borrowTree_releaseProtector_full_simulation⟩

end StepSimulationBridge

/-! ## §5. Episode 1 LeanMiri Capstone & Silent Axiom / Import-Isolation Audit -/

/-- **Episode 1 LeanMiri Cross-Frame Reference & Panic-Unwind Capstone.** -/
theorem ep1_lean_miri_cross_frame_panic_capstone :
    (type_of% @lmCrossFramePanicObserve_table) ∧
    (type_of% @lmCrossFramePanicObserve_out_of_range) ∧
    (type_of% @lmCrossFramePanicObserve_mode_sensitivity) ∧
    (type_of% @lm_tb_exact_failure_diagnostics) ∧
    (type_of% @lm_ptr_wrappingSignedOffset_roundtrip) ∧
    (type_of% @lm_controlFlow_unreachable_ub) ∧
    (type_of% @lm_controlFlow_unwindToBlock_laws) ∧
    (type_of% @lm_controlFlow_root_unwind_ub) ∧
    (type_of% @lm_cf_assert_four_way) ∧
    (type_of% @lm_globalState_endCall_lifo_preservation) ∧
    (type_of% @lm_multiframe_lifo_protector_release_witness) ∧
    (type_of% @lm_stepMirFn_miri_lockstep_simulations) :=
  ⟨@lmCrossFramePanicObserve_table, @lmCrossFramePanicObserve_out_of_range,
   @lmCrossFramePanicObserve_mode_sensitivity, @lm_tb_exact_failure_diagnostics,
   @lm_ptr_wrappingSignedOffset_roundtrip, @lm_controlFlow_unreachable_ub,
   @lm_controlFlow_unwindToBlock_laws, @lm_controlFlow_root_unwind_ub, @lm_cf_assert_four_way,
   @lm_globalState_endCall_lifo_preservation, @lm_multiframe_lifo_protector_release_witness,
   @lm_stepMirFn_miri_lockstep_simulations⟩

section AxiomAudit
open Lean Elab Command

run_cmd do
  let env ← getEnv
  -- Strict root isolation: ZERO `MiniRustSpec.*` and ZERO `Anneal.*` imports, even transitively!
  for modName in env.header.moduleNames do
    if (`MiniRustSpec).isPrefixOf modName || (`Anneal).isPrefixOf modName then
      throwError "import-isolation violation: {modName} must not be imported by LeanMiriSpec.CrossFrameRefAndPanicLM"
  let ns := `LeanMiriSpec.CrossFrameRefAndPanicLM
  let mut theorems : Nat := 0
  for (c, info) in env.constants.map₂.toList do
    for a in ← liftCoreM <| Lean.collectAxioms c do
      if a == ``sorryAx then throwError "{c} depends on sorryAx"
      if a == ``Lean.ofReduceBool || a == ``Lean.trustCompiler then
        throwError "{c} depends on forbidden axiom {a}"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} depends on non-standard axiom {a}"
    if ns.isPrefixOf c && !c.isInternal then
      if let .thmInfo _ := info then theorems := theorems + 1
  if theorems < 12 then
    throwError "axiom audit vacuous: only {theorems} theorems seen"

end AxiomAudit

end LeanMiriSpec.CrossFrameRefAndPanicLM
