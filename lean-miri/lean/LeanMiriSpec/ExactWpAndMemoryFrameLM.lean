/-
Copyright 2026 The Fuchsia Authors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Lean
import Anneal.ExactWpAndSmartCtors
import LeanMiriSpec.MemoryLemmas
import LeanMiriSpec.Correspondence.Translate

/-!
# Episode 2 LeanMiri Bridge: `lean-miri#91/#93` Memory-Frame & Whole-Body `ExactWP` (`LeanMiriSpec.ExactWpAndMemoryFrameLM`)

Bridges Anneal's `Std.Do`-insulated exact two-continuation weakest-precondition algebra
(`Anneal.ExactWpAndSmartCtors`) directly to vendored `Miri.*` and `LeanMiriSpec.MemoryLemmas`
with **ZERO `MiniRustSpec.*` imports** and **ZERO `Std.Do` / `Std.Tactic.Do` / `Std.WP` imports**:

1. **§1 (`LeanMiriSpec.MemoryLemmas` → `AnnealExactWP` Bridge & Universal Endian Disjoint Framing)**:
   - Lifts `Miri.Memory.Allocation.{readScalar, writeScalar, writeBytes, writeUninit, copy}` into
     `ExactAction (Allocation P E) AllocError _` and proves exact bidirectional `↔` WP laws
     (`allocReadScalarExactWP_iff`, `allocWriteScalarExactWP_iff`, `allocWriteBytesExactWP_iff`,
     `allocWriteUninitExactWP_iff`, `allocCopyExactWP_iff`).
   - Connects `lean-miri#91`'s `readScalar_{uninit_err, int_of_bytes, int_roundtrip, ptr_roundtrip,
     ptr_none_roundtrip, mapExtra}`, `withExtra`, `writeScalar_spec`, `writeBytes_spec`,
     `writeUninit_spec`, and `copy_initialized_spec` into `AnnealExactWP`, proving universal
     disjoint byte-range framing and sequenced write-then-read round-trips for **BOTH `.little`
     and `.big` endian** layouts (`allocWriteScalar_disjoint_readScalar_frame_exactWP`,
     `allocWriteScalar_then_readScalar_int_exactWP`, `allocWriteScalar_then_readScalar_ptr_exactWP`,
     `allocWriteUninit_disjoint_readScalar_frame_exactWP`,
     `allocWriteBytes_disjoint_readScalar_frame_exactWP`,
     `allocCopy_disjoint_readScalar_frame_exactWP`), plus concrete LE vs. BE witnesses.
2. **§2 (`Std.Do`-Free `TreeBorrowsWP` & `ProtectorReleaseWP` Mirroring `lean-miri#93`)**:
   - Exact bidirectional `↔` WP contracts over unmodified `Miri.TreeBorrows.BorrowTree`:
     `tbAccessExactWP_iff` (`performBorrowAccessRange`, retaining both committed `BorrowTree` AND
     diagnostic `Array BorrowTreeLocationResult` on `.Completed` and error),
     `tbDeallocExactWP_iff` (`deallocateBorrowRange`), and `protectorReleaseExactWP_iff`
     (`releaseProtector`, retaining committed segment prefix on error).
   - Bridges directly into `Anneal.ExactWpAndSmartCtors.{TreeBorrowsFrameWP, ProtectorReleaseWP}`,
     accompanied by concrete multi-segment committed-prefix error-state witnesses proving segment 0
     updates remain committed in `result.tree` when segment 1 fails!
3. **§3 (Whole-Body `Miri.Interpreter.Step.step` `ExactWP` on `translateBody`-Lowered `CapturedMir`)**:
   - Exact bidirectional `↔` single-step (`miriStepExactWP_iff`), relational choice-quantified
     (`miriAllowedStepExactWP_iff` over `Step.AllowedStep`), and fuel-bounded/loop-invariant
     multi-step (`miriBodyExactWP_iff`, `miriBodyExactWP_loop_invariant`,
     `miriBodyExactWP_negation_refutation`) WP theorems over unmodified `Miri.Interpreter.Step.step`.
   - End-to-end instantiations on real `LeanMiriSpec.Correspondence.translateBody`-lowered
     `CapturedMir` bodies covering normal `.return_`, `.unreachable` UB refutation via `↔`,
     passing `.assert`, failing `.assert(..., .terminate)` `.abort`, and failing
     `.assert(..., .cleanup bb)` → cleanup mutation → `.unwindResume`!
4. **§4 (Capstone & Silent Import / Bridge-Reality / Axiom Audit)**.
-/

namespace LeanMiriSpec.ExactWpAndMemoryFrameLM

set_option Elab.async false

open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.DataStructures Miri.Interpreter
open Anneal.ExactWpAndSmartCtors
open LeanMiriSpec.Correspondence
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics (emptyLayoutTable)

abbrev AnnealLayoutTable := Trusted.Rustc.V2026_06_01.Layout.LayoutTable

/-! ## §0. Kernel-Certified Unrolling Helpers (Zero `native_decide`) -/

/-- Close an equality goal via kernel definitional reduction (zero `Lean.ofReduceBool`). -/
local elab "kernel_rfl" : tactic => do
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  let tgt ← Lean.MVarId.getType' mvarId
  let some (ty, lhs, _) := tgt.eq?
    | Lean.Meta.throwTacticEx `kernel_rfl mvarId "expected equality goal"
  let u ← Lean.Meta.getLevel ty
  mvarId.assign (Lean.mkApp2 (Lean.mkConst ``Eq.refl [u]) ty lhs)
  Lean.Elab.Tactic.replaceMainGoal []

private def lmLoopFuelK {β : Type} (f : Unit → β → Id (ForInStep β)) :
    Nat → β → (β → β) → β
  | 0, b, k => k b
  | n + 1, b, k =>
    match f () b with
    | .done v => v
    | .yield v => lmLoopFuelK f n v k

private def lmLoopReal : (β : Type) → β → (Unit → β → Id (ForInStep β)) → β :=
  fun _ init f => forIn (m := Id) Lean.Loop.mk init f

private def lmLoopUnrolled (fuel : Nat) :
    (β : Type) → β → (Unit → β → Id (ForInStep β)) → β :=
  fun β init f => lmLoopFuelK f fuel init (fun b => lmLoopReal β b f)

private theorem lmLoopReal_eq_unrolled (fuel : Nat) : lmLoopReal = lmLoopUnrolled fuel := by
  funext β init f
  induction fuel generalizing init with
  | zero => rfl
  | succ n ih =>
    show Lean.Loop.forIn Lean.Loop.mk init f =
      lmLoopFuelK f (n + 1) init (fun b => lmLoopReal β b f)
    rw [Lean.Loop.forIn_eq_of_monadTail]
    show (match f () init with
      | .done val => val
      | .yield val => Lean.Loop.forIn Lean.Loop.mk val f) = _
    simp only [lmLoopFuelK]
    cases f () init with
    | done v => rfl
    | yield v => exact ih v

open Lean Meta Elab Command in
private def resolveMaybePrivateLM (n : Name) : CoreM Name := do
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
local elab "unroll_lm_loops " newId:ident " := " srcId:ident " fuel " n:num
    deps:((" with " ident,*)?) : command => do
  liftTermElabM do
    let src ← (try resolveGlobalConstNoOverload srcId catch _ => resolveMaybePrivateLM srcId.getId)
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
    let loopTy ← inferType (mkConst ``lmLoopReal)
    let fuel := mkNatLit n.getNat
    let depTys ← depInfo.mapM fun (_, lhs, _, _, _) => inferType lhs
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
        (#[mkApp (mkConst ``lmLoopUnrolled) fuel] ++
          depInfo.map fun (t, _, _, _, _) => mkConst t)
      let twinVal ← Core.betaReduce twinVal.headBeta
      addDecl <| .defnDecl {
        name := newName, levelParams := lvls, type := dinfo.type, value := twinVal,
        hints := .abbrev, safety := .safe }
      let mut proof ← mkCongrArg ctx (mkApp (mkConst ``lmLoopReal_eq_unrolled) fuel)
      for (t, _, _, _, _) in depInfo do
        proof ← mkCongr proof (mkConst (t ++ `eq_src))
      let us := lvls.map mkLevelParam
      let stmt ← mkEq (mkConst src us) (mkConst newName us)
      addDecl <| .thmDecl {
        name := newName ++ `eq_src, levelParams := lvls, type := stmt, value := proof }

/-! ## §1. `LeanMiriSpec.MemoryLemmas` (`lean-miri#91`) → `AnnealExactWP` Bridge & Universal Endian Framing -/

section MemoryLemmasWP

variable {P E E' : Type}

/-- Lift `Allocation.readScalar` into an `ExactAction` (read-only: retains `allocation` on both
`.ok` and `.error`). -/
def allocReadScalarAction [DecidableEq P] [PointerProvenance P]
    (layout : TargetDataLayout) (range : AllocRange) (readProvenance : Bool) :
    ExactAction (Allocation P E) AllocError (Miri.Memory.Scalar P) :=
  fun allocation =>
    match allocation.readScalar layout range readProvenance with
    | .ok sc => .ok sc allocation
    | .error err => .error err allocation

/-- Lift `Allocation.writeScalar` (`EStateM AllocError (Allocation P E) Unit`) into an `ExactAction`
retaining the post-allocation on BOTH `.ok` and `.error`. -/
def allocWriteScalarAction (layout : TargetDataLayout) (range : AllocRange) (value : Scalar P) :
    ExactAction (Allocation P E) AllocError Unit :=
  ExactAction.ofEStateM (Allocation.writeScalar layout range value)

/-- Lift `Allocation.writeBytes` into an `ExactAction`. -/
def allocWriteBytesAction (start ptrSize : Size) (bytes : Array UInt8) :
    ExactAction (Allocation P E) AllocError Unit :=
  ExactAction.ofEStateM (Allocation.writeBytes start bytes ptrSize)

/-- Lift `Allocation.writeUninit` into an `ExactAction`. -/
def allocWriteUninitAction (range : AllocRange) (ptrSize : Size) :
    ExactAction (Allocation P E) AllocError Unit :=
  ExactAction.ofEStateM (Allocation.writeUninit range ptrSize)

/-- Lift `Allocation.copy` into an `ExactAction`. -/
def allocCopyAction (source : Allocation P E) (sourceRange : AllocRange)
    (destStart ptrSize : Size) (sameAllocation nonoverlapping : Bool) :
    ExactAction (Allocation P E) AllocError Unit :=
  ExactAction.ofEStateM
    (Allocation.copy source sourceRange destStart ptrSize sameAllocation nonoverlapping)

/-! ### §1.1. Exact Bidirectional `↔` Weakest-Precondition Characterizations -/

theorem allocReadScalarExactWP_iff [DecidableEq P] [PointerProvenance P]
    (layout : TargetDataLayout) (range : AllocRange) (readProvenance : Bool)
    (post : Miri.Memory.Scalar P → Allocation P E → Prop) (onError : AllocError → Allocation P E → Prop)
    (allocation : Allocation P E) :
    AnnealExactWP (allocReadScalarAction layout range readProvenance) post onError allocation ↔
      match allocation.readScalar layout range readProvenance with
      | .ok sc => post sc allocation
      | .error err => onError err allocation := by
  unfold AnnealExactWP allocReadScalarAction
  cases allocation.readScalar layout range readProvenance <;> rfl

theorem allocWriteScalarExactWP_iff
    (layout : TargetDataLayout) (range : AllocRange) (value : Scalar P)
    (post : Unit → Allocation P E → Prop) (onError : AllocError → Allocation P E → Prop)
    (allocation : Allocation P E) :
    AnnealExactWP (allocWriteScalarAction layout range value) post onError allocation ↔
      match Allocation.writeScalar layout range value allocation with
      | .ok u updated => post u updated
      | .error err updated => onError err updated := by
  unfold AnnealExactWP allocWriteScalarAction ExactAction.ofEStateM
  cases Allocation.writeScalar layout range value allocation <;> rfl

theorem allocWriteBytesExactWP_iff
    (start ptrSize : Size) (bytes : Array UInt8)
    (post : Unit → Allocation P E → Prop) (onError : AllocError → Allocation P E → Prop)
    (allocation : Allocation P E) :
    AnnealExactWP (allocWriteBytesAction start ptrSize bytes) post onError allocation ↔
      match Allocation.writeBytes start bytes ptrSize allocation with
      | .ok u updated => post u updated
      | .error err updated => onError err updated := by
  unfold AnnealExactWP allocWriteBytesAction ExactAction.ofEStateM
  cases Allocation.writeBytes start bytes ptrSize allocation <;> rfl

theorem allocWriteUninitExactWP_iff
    (range : AllocRange) (ptrSize : Size)
    (post : Unit → Allocation P E → Prop) (onError : AllocError → Allocation P E → Prop)
    (allocation : Allocation P E) :
    AnnealExactWP (allocWriteUninitAction range ptrSize) post onError allocation ↔
      match Allocation.writeUninit range ptrSize allocation with
      | .ok u updated => post u updated
      | .error err updated => onError err updated := by
  unfold AnnealExactWP allocWriteUninitAction ExactAction.ofEStateM
  cases Allocation.writeUninit range ptrSize allocation <;> rfl

theorem allocCopyExactWP_iff
    (source : Allocation P E) (sourceRange : AllocRange)
    (destStart ptrSize : Size) (sameAllocation nonoverlapping : Bool)
    (post : Unit → Allocation P E → Prop) (onError : AllocError → Allocation P E → Prop)
    (allocation : Allocation P E) :
    AnnealExactWP
        (allocCopyAction source sourceRange destStart ptrSize sameAllocation nonoverlapping)
        post onError allocation ↔
      match Allocation.copy source sourceRange destStart ptrSize
          sameAllocation nonoverlapping allocation with
      | .ok u updated => post u updated
      | .error err updated => onError err updated := by
  unfold AnnealExactWP allocCopyAction ExactAction.ofEStateM
  cases Allocation.copy source sourceRange destStart ptrSize
      sameAllocation nonoverlapping allocation <;> rfl

/-! ### §1.2. Direct `LeanMiriSpec.MemoryLemmas` Rules in `AnnealExactWP` -/

/-- Uninitialized range `readScalar` faults into `onError (.invalidUninitBytes (some ⟨range, bad⟩))`
retaining `allocation` unmodified (`Allocation.readScalar_uninit_err`). -/
theorem allocReadScalar_uninit_exactWP [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range bad : AllocRange) (readProvenance : Bool)
    (post : Scalar P → Allocation P E → Prop) (onError : AllocError → Allocation P E → Prop)
    (h_uninit : allocation.initializationMask.isRangeInitialized range = .ok (.error bad)) :
    AnnealExactWP (allocReadScalarAction layout range readProvenance) post onError allocation ↔
      onError (.invalidUninitBytes (some ⟨range, bad⟩)) allocation := by
  rw [allocReadScalarExactWP_iff,
    Allocation.readScalar_uninit_err allocation layout range bad readProvenance h_uninit]

/-- Integer `readScalar` over initialized bytes (`Allocation.readScalar_int_of_bytes`). -/
theorem allocReadScalar_int_of_bytes_exactWP [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (bytes : Array UInt8)
    (post : Scalar P → Allocation P E → Prop) (onError : AllocError → Allocation P E → Prop)
    (h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (h_slice : allocation.getBytesUnchecked range = .ok bytes)
    (h_limit : bytes.size ≤ 16)
    (h_prov : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      allocation.provenanceMap.rangeEmpty range (Size.fromBits layout.pointerWidth.bits) = .ok true) :
    AnnealExactWP (allocReadScalarAction layout range false) post onError allocation ↔
      match (Scalar.fromUInt (BitVec.ofNat 128 ((List.range bytes.size).foldl (fun acc idx =>
          acc + (bytes[idx]?.getD 0).toNat * 2 ^ (8 *
            (if layout.endian == .little then idx else bytes.size - idx - 1))) 0))
          range.size).mapError AllocError.scalar with
      | .ok sc => post sc allocation
      | .error err => onError err allocation := by
  rw [allocReadScalarExactWP_iff,
    Allocation.readScalar_int_of_bytes allocation layout range bytes h_init h_slice h_limit h_prov]

/-- Integer round-trip `readScalar` in `AnnealExactWP` (`Allocation.readScalar_int_roundtrip`). -/
theorem allocReadScalar_int_roundtrip_exactWP [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (bits : U128)
    (post : Scalar P → Allocation P E → Prop) (onError : AllocError → Allocation P E → Prop)
    (h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (h_limit : range.size.bytes.toNat ≤ 16)
    (h_bits_bound : bits.toNat < 2 ^ (8 * range.size.bytes.toNat))
    (h_prov : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      allocation.provenanceMap.rangeEmpty range (Size.fromBits layout.pointerWidth.bits) = .ok true)
    (h_slice : allocation.getBytesUnchecked range =
      .ok (Array.ofFn (fun i : Fin range.size.bytes.toNat =>
        UInt8.ofNat ((bits.toNat / 2 ^ (8 *
          (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))) % 256)))) :
    AnnealExactWP (allocReadScalarAction layout range false) post onError allocation ↔
      match (Scalar.fromUInt bits range.size).mapError AllocError.scalar with
      | .ok sc => post sc allocation
      | .error err => onError err allocation := by
  rw [allocReadScalarExactWP_iff,
    Allocation.readScalar_int_roundtrip allocation layout range bits h_init h_limit
      h_bits_bound h_prov h_slice]

/-- Pointer round-trip `readScalar` in `AnnealExactWP` (`Allocation.readScalar_ptr_roundtrip`). -/
theorem allocReadScalar_ptr_roundtrip_exactWP [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (ptr : Pointer P)
    (post : Scalar P → Allocation P E → Prop) (onError : AllocError → Allocation P E → Prop)
    (h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (h_ptr_sz : range.size = Size.fromBits layout.pointerWidth.bits)
    (h_limit : range.size.bytes.toNat ≤ 16)
    (h_off_bound : ptr.offset.bytes.toNat < 2 ^ (8 * range.size.bytes.toNat))
    (h_prov : allocation.provenanceMap.readPtr range.start
      (Size.fromBits layout.pointerWidth.bits) = .ok (some ptr.provenance))
    (h_slice : allocation.getBytesUnchecked range =
      .ok (Array.ofFn (fun i : Fin range.size.bytes.toNat =>
        UInt8.ofNat ((ptr.offset.bytes.toNat / 2 ^ (8 *
          (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))) % 256)))) :
    AnnealExactWP (allocReadScalarAction layout range true) post onError allocation ↔
      post (Scalar.fromPointer layout ptr) allocation := by
  rw [allocReadScalarExactWP_iff,
    Allocation.readScalar_ptr_roundtrip allocation layout range ptr h_init h_ptr_sz
      h_limit h_off_bound h_prov h_slice]

/-- No-provenance pointer-sized `readScalar` in `AnnealExactWP`
(`Allocation.readScalar_ptr_none_roundtrip`). -/
theorem allocReadScalar_ptr_none_roundtrip_exactWP [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (bits : U128)
    (post : Scalar P → Allocation P E → Prop) (onError : AllocError → Allocation P E → Prop)
    (h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (h_ptr_sz : range.size = Size.fromBits layout.pointerWidth.bits)
    (h_limit : range.size.bytes.toNat ≤ 16)
    (h_bits_bound : bits.toNat < 2 ^ (8 * range.size.bytes.toNat))
    (h_prov : allocation.provenanceMap.readPtr range.start
      (Size.fromBits layout.pointerWidth.bits) = .ok none)
    (h_slice : allocation.getBytesUnchecked range =
      .ok (Array.ofFn (fun i : Fin range.size.bytes.toNat =>
        UInt8.ofNat ((bits.toNat / 2 ^ (8 *
          (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))) % 256)))) :
    AnnealExactWP (allocReadScalarAction layout range true) post onError allocation ↔
      match (Scalar.fromUInt bits range.size).mapError AllocError.scalar with
      | .ok sc => post sc allocation
      | .error err => onError err allocation := by
  rw [allocReadScalarExactWP_iff,
    Allocation.readScalar_ptr_none_roundtrip allocation layout range bits h_init h_ptr_sz
      h_limit h_bits_bound h_prov h_slice]

/-- `Allocation.mapExtra` preserves `allocReadScalarAction` exact WP identically
(`Allocation.readScalar_mapExtra`). -/
theorem allocMapExtra_preserves_readScalar_exactWP [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (f : E → E') (layout : TargetDataLayout)
    (range : AllocRange) (readProvenance : Bool)
    (post : Scalar P → Prop) (onError : AllocError → Prop) :
    AnnealExactWP (allocReadScalarAction layout range readProvenance)
        (fun sc _ => post sc) (fun err _ => onError err) (allocation.mapExtra f) ↔
      AnnealExactWP (allocReadScalarAction layout range readProvenance)
        (fun sc _ => post sc) (fun err _ => onError err) allocation := by
  rw [allocReadScalarExactWP_iff, allocReadScalarExactWP_iff,
    Allocation.readScalar_mapExtra allocation f layout range readProvenance]

/-- `Allocation.withExtra` preserves `allocReadScalarAction` exact WP identically
(composing `Allocation.withExtra` + `Allocation.readScalar_mapExtra`). -/
theorem allocWithExtra_preserves_readScalar_exactWP [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P Unit) (extra : E) (layout : TargetDataLayout)
    (range : AllocRange) (readProvenance : Bool)
    (post : Scalar P → Prop) (onError : AllocError → Prop) :
    AnnealExactWP (allocReadScalarAction layout range readProvenance)
        (fun sc _ => post sc) (fun err _ => onError err) (allocation.withExtra extra) ↔
      AnnealExactWP (allocReadScalarAction layout range readProvenance)
        (fun sc _ => post sc) (fun err _ => onError err) allocation := by
  have hMap : allocation.withExtra extra = allocation.mapExtra (fun _ => extra) := rfl
  rw [hMap]
  exact allocMapExtra_preserves_readScalar_exactWP allocation (fun _ => extra)
    layout range readProvenance post onError

/-- `Allocation.writeBytes` commutes with `Allocation.mapExtra` in `AnnealExactWP`
(`Allocation.writeBytes_mapExtra`). -/
theorem allocWriteBytes_mapExtra_exactWP
    (start ptrSize : Size) (bytes : Array UInt8)
    (allocation : Allocation P E) (f : E → E')
    (post : Unit → Allocation P E' → Prop) (onError : AllocError → Allocation P E' → Prop) :
    AnnealExactWP (allocWriteBytesAction start ptrSize bytes) post onError (allocation.mapExtra f) ↔
      AnnealExactWP (allocWriteBytesAction start ptrSize bytes)
        (fun u st => post u (st.mapExtra f))
        (fun err st => onError err (st.mapExtra f)) allocation := by
  rw [allocWriteBytesExactWP_iff, allocWriteBytesExactWP_iff,
    Allocation.writeBytes_mapExtra start bytes ptrSize allocation f]
  cases Allocation.writeBytes start bytes ptrSize allocation <;> rfl

/-! ### §1.3. Universal Little-Endian & Big-Endian Round-Trips and Disjoint Byte-Range Framing -/

private theorem endExclusive_of_bound (range : AllocRange) (limit : Size)
    (hBound : range.start.bytes.toNat + range.size.bytes.toNat ≤ limit.bytes.toNat) :
    range.endExclusive = .ok (Size.ofBytes (range.start.bytes + range.size.bytes)) ∧
      (Size.ofBytes (range.start.bytes + range.size.bytes)).bytes.toNat =
        range.start.bytes.toNat + range.size.bytes.toNat := by
  have hLimLt := limit.bytes.toNat_lt
  have hFits : range.start.bytes.toNat + range.size.bytes.toNat < 2 ^ 64 := by omega
  have hAddNat : (range.start.bytes + range.size.bytes).toNat =
      range.start.bytes.toNat + range.size.bytes.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt hFits]
  have hNotLt : ¬ (range.start.bytes + range.size.bytes < range.start.bytes) := by
    intro hLt
    have : (range.start.bytes + range.size.bytes).toNat < range.start.bytes.toNat :=
      UInt64.lt_iff_toNat_lt.mp hLt
    omega
  have hEnd : range.endExclusive = .ok (Size.ofBytes (range.start.bytes + range.size.bytes)) := by
    unfold AllocRange.endExclusive AllocRange.end Size.add
    simp only [hNotLt, ↓reduceIte, Except.mapError, Size.ofBytes]
  exact ⟨hEnd, hAddNat⟩

/-- **Universal Endian (`.little` AND `.big`) Write-Scalar → Read-Scalar Integer Round-Trip in `AnnealExactWP`**:
For ANY `TargetDataLayout` (little-endian OR big-endian!), sequencing `allocWriteScalarAction`
with an integer scalar followed by `allocReadScalarAction layout range false` via `ExactAction.bind`
satisfies `AnnealExactWP` with the exact decoded scalar `(Scalar.fromUInt bits range.size)`! -/
theorem allocWriteScalar_then_readScalar_int_exactWP [DecidableEq P] [PointerProvenance P]
    (layout : TargetDataLayout) (allocation : Allocation P E)
    (range : AllocRange) (value : Scalar P) (bits : U128)
    (cleared : ProvenanceMap P)
    (post : Scalar P → Allocation P E → Prop) (onError : AllocError → Allocation P E → Prop)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (nonzero : range.size.bytes ≠ 0)
    (width : range.size.bytes.toNat ≤ 16)
    (bound : range.start.bytes.toNat + range.size.bytes.toNat ≤ allocation.byteSize.bytes.toNat)
    (conversion : value.toBitsOrPtrInternal range.size = .ok (.bits bits))
    (h_bits_bound : bits.toNat < 2 ^ (8 * range.size.bytes.toNat))
    (clear : ∀ fullBytes : Array UInt8,
      allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes →
      allocation.provenanceMap.clear range fullBytes
        (Size.fromBits layout.pointerWidth.bits) = .ok () cleared)
    (h_prov : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      cleared.rangeEmpty range (Size.fromBits layout.pointerWidth.bits) = .ok true)
    (h_post : ∀ updated : Allocation P E,
      Allocation.writeScalar layout range value allocation = .ok () updated →
      match (Scalar.fromUInt bits range.size).mapError AllocError.scalar with
      | .ok sc => post sc updated
      | .error err => onError err updated) :
    AnnealExactWP
      (ExactAction.seq (allocWriteScalarAction layout range value)
        (allocReadScalarAction layout range false))
      post onError allocation := by
  obtain ⟨updated, hWrite, _, _, _, _, _, _, _, _, _, hInit, hProvEq, hBytesBits, _, _⟩ :=
    Allocation.writeScalar_spec layout allocation range value (.bits bits) cleared cleared
      storage mutable maskLength maskValid nonzero width bound conversion clear rfl
  rw [exactWP_seq, allocWriteScalarExactWP_iff, hWrite]
  dsimp only
  have hBytes := hBytesBits bits rfl
  have hProvUpdated : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      updated.provenanceMap.rangeEmpty range (Size.fromBits layout.pointerWidth.bits) = .ok true := by
    rw [hProvEq]; exact h_prov
  rw [allocReadScalar_int_roundtrip_exactWP updated layout range bits post onError
    hInit width h_bits_bound hProvUpdated hBytes]
  exact h_post updated hWrite

/-- **Universal Endian (`.little` AND `.big`) Write-Scalar → Read-Scalar Pointer Round-Trip in `AnnealExactWP`**:
For ANY `TargetDataLayout` (`.little` OR `.big`), sequencing `allocWriteScalarAction` of a pointer
scalar followed by provenance-reading `allocReadScalarAction layout range true` returns the EXACT
pointer `Scalar.fromPointer layout ptr`! -/
theorem allocWriteScalar_then_readScalar_ptr_exactWP [DecidableEq P] [PointerProvenance P]
    (layout : TargetDataLayout) (allocation : Allocation P E)
    (range : AllocRange) (value : Scalar P) (ptr : Pointer P)
    (cleared nextProvenance : ProvenanceMap P)
    (post : Scalar P → Allocation P E → Prop) (onError : AllocError → Allocation P E → Prop)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (nonzero : range.size.bytes ≠ 0)
    (width : range.size.bytes.toNat ≤ 16)
    (bound : range.start.bytes.toNat + range.size.bytes.toNat ≤ allocation.byteSize.bytes.toNat)
    (conversion : value.toBitsOrPtrInternal range.size = .ok (.pointer ptr))
    (h_ptr_sz : range.size = Size.fromBits layout.pointerWidth.bits)
    (h_off_bound : ptr.offset.bytes.toNat < 2 ^ (8 * range.size.bytes.toNat))
    (clear : ∀ fullBytes : Array UInt8,
      allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes →
      allocation.provenanceMap.clear range fullBytes
        (Size.fromBits layout.pointerWidth.bits) = .ok () cleared)
    (h_insert : cleared.insertPtr range.start ptr.provenance
      (Size.fromBits layout.pointerWidth.bits) = .ok () nextProvenance)
    (h_read_prov : nextProvenance.readPtr range.start
      (Size.fromBits layout.pointerWidth.bits) = .ok (some ptr.provenance))
    (h_post : ∀ updated : Allocation P E,
      Allocation.writeScalar layout range value allocation = .ok () updated →
      post (Scalar.fromPointer layout ptr) updated) :
    AnnealExactWP
      (ExactAction.seq (allocWriteScalarAction layout range value)
        (allocReadScalarAction layout range true))
      post onError allocation := by
  obtain ⟨updated, hWrite, _, _, _, _, _, _, _, _, _, hInit, hProvEq, _, hBytesPtr, _⟩ :=
    Allocation.writeScalar_spec layout allocation range value (.pointer ptr) cleared nextProvenance
      storage mutable maskLength maskValid nonzero width bound conversion clear ⟨h_ptr_sz, h_insert⟩
  rw [exactWP_seq, allocWriteScalarExactWP_iff, hWrite]
  dsimp only
  have hU64Lt := ptr.offset.bytes.toNat_lt
  have hBv128 : (BitVec.ofNat 128 ptr.offset.bytes.toNat).toNat = ptr.offset.bytes.toNat := by
    have hLt128 : ptr.offset.bytes.toNat < 2 ^ 128 := by omega
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hLt128]
  have hBytes := hBytesPtr ptr rfl
  rw [hBv128] at hBytes
  have hProvUpdated : updated.provenanceMap.readPtr range.start
      (Size.fromBits layout.pointerWidth.bits) = .ok (some ptr.provenance) := by
    rw [hProvEq]; exact h_read_prov
  rw [allocReadScalar_ptr_roundtrip_exactWP updated layout range ptr post onError
    hInit h_ptr_sz width h_off_bound hProvUpdated hBytes]
  exact h_post updated hWrite

/-- **Universal Endian (`.little` AND `.big`) Disjoint Byte-Range Framing for `writeScalar` in `AnnealExactWP`**:
Writing ANY scalar to `wRange` preserves the exact `readScalar` outcome on every disjoint,
initialized, nonempty, provenance-clean range `qRange`! -/
theorem allocWriteScalar_disjoint_readScalar_frame_exactWP [DecidableEq P] [PointerProvenance P]
    (layout : TargetDataLayout) (allocation : Allocation P E)
    (wRange qRange : AllocRange) (qFin : Size) (value : Scalar P)
    (converted : ScalarBitsOrPointer P) (cleared nextProvenance : ProvenanceMap P)
    (qBytes : Array UInt8)
    (post : Scalar P → Allocation P E → Prop) (onError : AllocError → Allocation P E → Prop)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (wNonzero : wRange.size.bytes ≠ 0)
    (wWidth : wRange.size.bytes.toNat ≤ 16)
    (wBound : wRange.start.bytes.toNat + wRange.size.bytes.toNat ≤ allocation.byteSize.bytes.toNat)
    (conversion : value.toBitsOrPtrInternal wRange.size = .ok converted)
    (clear : ∀ fullBytes : Array UInt8,
      allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes →
      allocation.provenanceMap.clear wRange fullBytes
        (Size.fromBits layout.pointerWidth.bits) = .ok () cleared)
    (insert : match converted with
      | .bits _ => nextProvenance = cleared
      | .pointer pointer => wRange.size = Size.fromBits layout.pointerWidth.bits ∧
          cleared.insertPtr wRange.start pointer.provenance
            (Size.fromBits layout.pointerWidth.bits) = .ok () nextProvenance)
    (qEnd : qRange.endExclusive = .ok qFin)
    (qNonempty : qRange.start.bytes.toNat < qFin.bytes.toNat)
    (qBound : qFin.bytes.toNat ≤ allocation.byteSize.bytes.toNat)
    (hDisjoint : wRange.start.bytes.toNat + wRange.size.bytes.toNat ≤ qRange.start.bytes.toNat ∨
      qFin.bytes.toNat ≤ wRange.start.bytes.toNat)
    (qInit : allocation.initializationMask.isRangeInitialized qRange = .ok (.ok ()))
    (qSlice : allocation.getBytesUnchecked qRange = .ok qBytes)
    (qLimit : qBytes.size ≤ 16)
    (qProvBefore : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      allocation.provenanceMap.rangeEmpty qRange (Size.fromBits layout.pointerWidth.bits) = .ok true)
    (qProvAfter : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      nextProvenance.rangeEmpty qRange (Size.fromBits layout.pointerWidth.bits) = .ok true)
    (hFrame : ∀ updated : Allocation P E,
      Allocation.writeScalar layout wRange value allocation = .ok () updated →
      updated.readScalar layout qRange false = allocation.readScalar layout qRange false →
      AnnealExactWP (allocReadScalarAction layout qRange false)
        (fun sc _ => post sc updated) (fun err _ => onError err updated) allocation) :
    AnnealExactWP
      (ExactAction.seq (allocWriteScalarAction layout wRange value)
        (allocReadScalarAction layout qRange false))
      post onError allocation := by
  obtain ⟨updated, hWrite, _, _, _, _, _, _, _, _, hSetMask, _, hProvEq, _, _, hDisjBytes⟩ :=
    Allocation.writeScalar_spec layout allocation wRange value converted cleared nextProvenance
      storage mutable maskLength maskValid wNonzero wWidth wBound conversion clear insert
  obtain ⟨wEnd, wFinNat⟩ := endExclusive_of_bound wRange allocation.byteSize wBound
  have wPos : 0 < wRange.size.bytes.toNat := Nat.pos_of_ne_zero (fun h0 =>
    wNonzero (UInt64.toNat_inj.mp h0))
  have hInitFrame : updated.initializationMask.isRangeInitialized qRange = .ok (.ok ()) := by
    rw [InitMask.WriteProof.isRangeInitialized_frame allocation.initializationMask
      updated.initializationMask wRange qRange
      (Size.ofBytes (wRange.start.bytes + wRange.size.bytes)) qFin true
      maskValid wEnd qEnd (by omega) qNonempty
      (by rw [maskLength]; omega) (by rw [maskLength]; exact qBound)
      (by omega) hSetMask]
    exact qInit
  have hBytesEq : updated.getBytesUnchecked qRange = .ok qBytes := by
    rw [hDisjBytes qRange qFin qEnd (Nat.le_of_lt qNonempty) qBound hDisjoint, qSlice]
  have hReadBefore :=
    Allocation.readScalar_int_of_bytes allocation layout qRange qBytes qInit qSlice qLimit qProvBefore
  have hProvUpdated : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      updated.provenanceMap.rangeEmpty qRange (Size.fromBits layout.pointerWidth.bits) = .ok true := by
    rw [hProvEq]; exact qProvAfter
  have hReadAfter :=
    Allocation.readScalar_int_of_bytes updated layout qRange qBytes hInitFrame hBytesEq qLimit hProvUpdated
  have hReadEq : updated.readScalar layout qRange false = allocation.readScalar layout qRange false :=
    hReadAfter.trans hReadBefore.symm
  rw [exactWP_seq, allocWriteScalarExactWP_iff, hWrite]
  dsimp only
  rw [allocReadScalarExactWP_iff, hReadEq]
  have hCall := hFrame updated hWrite hReadEq
  rw [allocReadScalarExactWP_iff] at hCall
  exact hCall

/-- **Universal Endian (`.little` AND `.big`) Disjoint Byte-Range Framing for `writeUninit` in `AnnealExactWP`**:
Marking `wRange` uninitialized preserves the exact `readScalar` outcome on every disjoint initialized
range `qRange`! -/
theorem allocWriteUninit_disjoint_readScalar_frame_exactWP [DecidableEq P] [PointerProvenance P]
    (layout : TargetDataLayout) (allocation : Allocation P E)
    (wRange qRange : AllocRange) (qFin : Size) (nextProvenance : ProvenanceMap P)
    (qBytes : Array UInt8)
    (post : Scalar P → Allocation P E → Prop) (onError : AllocError → Allocation P E → Prop)
    (wNonzero : wRange.size.bytes ≠ 0)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (wBound : wRange.start.bytes.toNat + wRange.size.bytes.toNat ≤ allocation.byteSize.bytes.toNat)
    (clear : ∀ fullBytes : Array UInt8,
      allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes →
      allocation.provenanceMap.clear wRange fullBytes
        (Size.fromBits layout.pointerWidth.bits) = .ok () nextProvenance)
    (qEnd : qRange.endExclusive = .ok qFin)
    (qNonempty : qRange.start.bytes.toNat < qFin.bytes.toNat)
    (qBound : qFin.bytes.toNat ≤ allocation.byteSize.bytes.toNat)
    (hDisjoint : wRange.start.bytes.toNat + wRange.size.bytes.toNat ≤ qRange.start.bytes.toNat ∨
      qFin.bytes.toNat ≤ wRange.start.bytes.toNat)
    (qInit : allocation.initializationMask.isRangeInitialized qRange = .ok (.ok ()))
    (qSlice : allocation.getBytesUnchecked qRange = .ok qBytes)
    (qLimit : qBytes.size ≤ 16)
    (qProvBefore : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      allocation.provenanceMap.rangeEmpty qRange (Size.fromBits layout.pointerWidth.bits) = .ok true)
    (qProvAfter : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      nextProvenance.rangeEmpty qRange (Size.fromBits layout.pointerWidth.bits) = .ok true)
    (hFrame : ∀ updated : Allocation P E,
      Allocation.writeUninit wRange (Size.fromBits layout.pointerWidth.bits) allocation = .ok () updated →
      updated.readScalar layout qRange false = allocation.readScalar layout qRange false →
      AnnealExactWP (allocReadScalarAction layout qRange false)
        (fun sc _ => post sc updated) (fun err _ => onError err updated) allocation) :
    AnnealExactWP
      (ExactAction.seq (allocWriteUninitAction wRange (Size.fromBits layout.pointerWidth.bits))
        (allocReadScalarAction layout qRange false))
      post onError allocation := by
  obtain ⟨updated, hWrite, _, _, _, _, _, _, _, _, hSetMask, hProvEq, hBytesUnchanged⟩ :=
    Allocation.writeUninit_spec wRange (Size.fromBits layout.pointerWidth.bits) allocation
      nextProvenance wNonzero storage mutable maskLength maskValid wBound clear
  obtain ⟨wEnd, wFinNat⟩ := endExclusive_of_bound wRange allocation.byteSize wBound
  have wPos : 0 < wRange.size.bytes.toNat := Nat.pos_of_ne_zero (fun h0 =>
    wNonzero (UInt64.toNat_inj.mp h0))
  have hInitFrame : updated.initializationMask.isRangeInitialized qRange = .ok (.ok ()) := by
    rw [InitMask.WriteProof.isRangeInitialized_frame allocation.initializationMask
      updated.initializationMask wRange qRange
      (Size.ofBytes (wRange.start.bytes + wRange.size.bytes)) qFin false
      maskValid wEnd qEnd (by omega) qNonempty
      (by rw [maskLength]; omega) (by rw [maskLength]; exact qBound)
      (by omega) hSetMask]
    exact qInit
  have hBytesEq : updated.getBytesUnchecked qRange = .ok qBytes := by
    rw [hBytesUnchanged qRange, qSlice]
  have hReadBefore :=
    Allocation.readScalar_int_of_bytes allocation layout qRange qBytes qInit qSlice qLimit qProvBefore
  have hProvUpdated : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      updated.provenanceMap.rangeEmpty qRange (Size.fromBits layout.pointerWidth.bits) = .ok true := by
    rw [hProvEq]; exact qProvAfter
  have hReadAfter :=
    Allocation.readScalar_int_of_bytes updated layout qRange qBytes hInitFrame hBytesEq qLimit hProvUpdated
  have hReadEq : updated.readScalar layout qRange false = allocation.readScalar layout qRange false :=
    hReadAfter.trans hReadBefore.symm
  rw [exactWP_seq, allocWriteUninitExactWP_iff, hWrite]
  dsimp only
  rw [allocReadScalarExactWP_iff, hReadEq]
  have hCall := hFrame updated hWrite hReadEq
  rw [allocReadScalarExactWP_iff] at hCall
  exact hCall

/-- **Universal Endian (`.little` AND `.big`) Disjoint Byte-Range Framing for `writeBytes` in `AnnealExactWP`**. -/
theorem allocWriteBytes_disjoint_readScalar_frame_exactWP [DecidableEq P] [PointerProvenance P]
    (layout : TargetDataLayout) (allocation : Allocation P E)
    (wStart : Size) (wBytes : Array UInt8) (qRange : AllocRange) (qFin : Size)
    (nextProvenance : ProvenanceMap P) (qBytes : Array UInt8)
    (post : Scalar P → Allocation P E → Prop) (onError : AllocError → Allocation P E → Prop)
    (hNonempty : 0 < wBytes.size)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (wBound : wStart.bytes.toNat + wBytes.size ≤ allocation.byteSize.bytes.toNat)
    (clear : ∀ fullBytes : Array UInt8,
      allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes →
      allocation.provenanceMap.clear
        (allocRange wStart (Size.ofBytes (UInt64.ofNat wBytes.size))) fullBytes
        (Size.fromBits layout.pointerWidth.bits) = .ok () nextProvenance)
    (qEnd : qRange.endExclusive = .ok qFin)
    (qNonempty : qRange.start.bytes.toNat < qFin.bytes.toNat)
    (qBound : qFin.bytes.toNat ≤ allocation.byteSize.bytes.toNat)
    (hDisjoint : wStart.bytes.toNat + wBytes.size ≤ qRange.start.bytes.toNat ∨
      qFin.bytes.toNat ≤ wStart.bytes.toNat)
    (qInit : allocation.initializationMask.isRangeInitialized qRange = .ok (.ok ()))
    (qSlice : allocation.getBytesUnchecked qRange = .ok qBytes)
    (qLimit : qBytes.size ≤ 16)
    (qProvBefore : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      allocation.provenanceMap.rangeEmpty qRange (Size.fromBits layout.pointerWidth.bits) = .ok true)
    (qProvAfter : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      nextProvenance.rangeEmpty qRange (Size.fromBits layout.pointerWidth.bits) = .ok true)
    (hFrame : ∀ updated : Allocation P E,
      Allocation.writeBytes wStart wBytes (Size.fromBits layout.pointerWidth.bits) allocation = .ok () updated →
      updated.readScalar layout qRange false = allocation.readScalar layout qRange false →
      AnnealExactWP (allocReadScalarAction layout qRange false)
        (fun sc _ => post sc updated) (fun err _ => onError err updated) allocation) :
    AnnealExactWP
      (ExactAction.seq (allocWriteBytesAction wStart (Size.fromBits layout.pointerWidth.bits) wBytes)
        (allocReadScalarAction layout qRange false))
      post onError allocation := by
  obtain ⟨updated, hWrite, _, _, _, _, _, _, _, _, hSetMask, _, hProvEq, _, hDisjBytes⟩ :=
    Allocation.writeBytes_spec wStart (Size.fromBits layout.pointerWidth.bits) wBytes allocation
      nextProvenance hNonempty storage mutable maskLength maskValid wBound clear
  let wRange : AllocRange := allocRange wStart (Size.ofBytes (UInt64.ofNat wBytes.size))
  have hWStart : wRange.start = wStart := rfl
  have hBytesLt : wBytes.size < 2 ^ 64 := by
    have := allocation.byteSize.bytes.toNat_lt; omega
  have hWSizeNat : wRange.size.bytes.toNat = wBytes.size := by
    simp [wRange, allocRange, Size.ofBytes, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hBytesLt]
  obtain ⟨wEnd, wFinNat⟩ := endExclusive_of_bound wRange allocation.byteSize (by
    rw [hWStart, hWSizeNat]; exact wBound)
  rw [hWStart, hWSizeNat] at wFinNat
  have hInitFrame : updated.initializationMask.isRangeInitialized qRange = .ok (.ok ()) := by
    rw [InitMask.WriteProof.isRangeInitialized_frame allocation.initializationMask
      updated.initializationMask wRange qRange
      (Size.ofBytes (wRange.start.bytes + wRange.size.bytes)) qFin true
      maskValid wEnd qEnd
      (by rw [hWStart, wFinNat]; omega) qNonempty
      (by rw [maskLength, hWStart, wFinNat]; exact wBound)
      (by rw [maskLength]; exact qBound)
      (by rw [hWStart, wFinNat]; exact hDisjoint)
      hSetMask]
    exact qInit
  have hBytesEq : updated.getBytesUnchecked qRange = .ok qBytes := by
    rw [hDisjBytes qRange qFin qEnd (Nat.le_of_lt qNonempty) qBound hDisjoint, qSlice]
  have hReadBefore :=
    Allocation.readScalar_int_of_bytes allocation layout qRange qBytes qInit qSlice qLimit qProvBefore
  have hProvUpdated : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      updated.provenanceMap.rangeEmpty qRange (Size.fromBits layout.pointerWidth.bits) = .ok true := by
    rw [hProvEq]; exact qProvAfter
  have hReadAfter :=
    Allocation.readScalar_int_of_bytes updated layout qRange qBytes hInitFrame hBytesEq qLimit hProvUpdated
  have hReadEq : updated.readScalar layout qRange false = allocation.readScalar layout qRange false :=
    hReadAfter.trans hReadBefore.symm
  rw [exactWP_seq, allocWriteBytesExactWP_iff, hWrite]
  dsimp only
  rw [allocReadScalarExactWP_iff, hReadEq]
  have hCall := hFrame updated hWrite hReadEq
  rw [allocReadScalarExactWP_iff] at hCall
  exact hCall

/-- **Universal Endian (`.little` AND `.big`) Disjoint Byte-Range Framing for `Allocation.copy` in `AnnealExactWP`**. -/
theorem allocCopy_disjoint_readScalar_frame_exactWP [DecidableEq P] [PointerProvenance P]
    (layout : TargetDataLayout) (source state : Allocation P E)
    (sourceRange qRange : AllocRange) (srcFinish destStart qFin : Size)
    (sameAllocation nonoverlapping : Bool)
    (srcBytes qBytes : Array UInt8) (provCopy : ProvenanceCopy P)
    (clearedProv finalProv : ProvenanceMap P)
    (post : Scalar P → Allocation P E → Prop) (onError : AllocError → Allocation P E → Prop)
    (srcStorage : source.len = source.byteSize.bytes.toNat)
    (srcEnd : sourceRange.endExclusive = .ok srcFinish)
    (srcNonzero : sourceRange.size.bytes ≠ 0)
    (srcMaskLen : source.initializationMask.len = source.byteSize)
    (srcMaskWF : InitMask.WriteProof.WellFormed source.initializationMask)
    (srcInit : source.initializationMask.isRangeInitialized sourceRange = .ok (.ok ()))
    (srcSlice : source.getBytesUnchecked sourceRange = .ok srcBytes)
    (srcInBounds : srcFinish.bytes.toNat ≤ source.byteSize.bytes.toNat)
    (h_prepProv : ∀ srcFull : Array UInt8,
      source.getBytesUnchecked (allocRange Size.ZERO source.byteSize) = .ok srcFull →
      source.provenanceMap.prepareCopy sourceRange srcFull
        (Size.fromBits layout.pointerWidth.bits) = .ok provCopy)
    (h_disjSame : sameAllocation = true → nonoverlapping = true →
      srcFinish.bytes.toNat ≤ destStart.bytes.toNat ∨
        destStart.bytes.toNat + sourceRange.size.bytes.toNat ≤ sourceRange.start.bytes.toNat)
    (destStorage : state.len = state.byteSize.bytes.toNat)
    (destMut : state.mutability = .Mut)
    (destMaskLen : state.initializationMask.len = state.byteSize)
    (destMaskWF : InitMask.WriteProof.WellFormed state.initializationMask)
    (destInBounds : destStart.bytes.toNat + sourceRange.size.bytes.toNat ≤ state.byteSize.bytes.toNat)
    (h_clearProv : ∀ stFull : Array UInt8,
      state.getBytesUnchecked (allocRange Size.ZERO state.byteSize) = .ok stFull →
      state.provenanceMap.clear (allocRange destStart sourceRange.size) stFull
        (Size.fromBits layout.pointerWidth.bits) = .ok () clearedProv)
    (h_applyProv : clearedProv.applyCopy provCopy
      (allocRange destStart sourceRange.size) 1 = .ok () finalProv)
    (qEnd : qRange.endExclusive = .ok qFin)
    (qNonempty : qRange.start.bytes.toNat < qFin.bytes.toNat)
    (qBound : qFin.bytes.toNat ≤ state.byteSize.bytes.toNat)
    (hDisjoint : destStart.bytes.toNat + sourceRange.size.bytes.toNat ≤ qRange.start.bytes.toNat ∨
      qFin.bytes.toNat ≤ destStart.bytes.toNat)
    (qInit : state.initializationMask.isRangeInitialized qRange = .ok (.ok ()))
    (qSlice : state.getBytesUnchecked qRange = .ok qBytes)
    (qLimit : qBytes.size ≤ 16)
    (qProvBefore : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      state.provenanceMap.rangeEmpty qRange (Size.fromBits layout.pointerWidth.bits) = .ok true)
    (qProvAfter : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      finalProv.rangeEmpty qRange (Size.fromBits layout.pointerWidth.bits) = .ok true)
    (hFrame : ∀ updated : Allocation P E,
      Allocation.copy source sourceRange destStart (Size.fromBits layout.pointerWidth.bits)
        sameAllocation nonoverlapping state = .ok () updated →
      updated.readScalar layout qRange false = state.readScalar layout qRange false →
      AnnealExactWP (allocReadScalarAction layout qRange false)
        (fun sc _ => post sc updated) (fun err _ => onError err updated) state) :
    AnnealExactWP
      (ExactAction.seq
        (allocCopyAction source sourceRange destStart (Size.fromBits layout.pointerWidth.bits)
          sameAllocation nonoverlapping)
        (allocReadScalarAction layout qRange false))
      post onError state := by
  obtain ⟨updated, hCopy, _, _, _, _, _, _, _, _, _, _, hInitFrameIff, hProvEq, _, hDisjBytes⟩ :=
    Allocation.copy_initialized_spec source state sourceRange srcFinish destStart
      (Size.fromBits layout.pointerWidth.bits) sameAllocation nonoverlapping srcBytes provCopy
      clearedProv finalProv srcStorage srcEnd srcNonzero srcMaskLen srcMaskWF srcInit srcSlice
      srcInBounds h_prepProv h_disjSame destStorage destMut destMaskLen destMaskWF destInBounds
      h_clearProv h_applyProv
  have hInitFrame : updated.initializationMask.isRangeInitialized qRange = .ok (.ok ()) :=
    (hInitFrameIff qRange qFin qEnd qNonempty qBound hDisjoint).mpr qInit
  have hBytesEq : updated.getBytesUnchecked qRange = .ok qBytes := by
    rw [hDisjBytes qRange qFin qEnd (Nat.le_of_lt qNonempty) qBound hDisjoint, qSlice]
  have hReadBefore :=
    Allocation.readScalar_int_of_bytes state layout qRange qBytes qInit qSlice qLimit qProvBefore
  have hProvUpdated : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      updated.provenanceMap.rangeEmpty qRange (Size.fromBits layout.pointerWidth.bits) = .ok true := by
    rw [hProvEq]; exact qProvAfter
  have hReadAfter :=
    Allocation.readScalar_int_of_bytes updated layout qRange qBytes hInitFrame hBytesEq qLimit hProvUpdated
  have hReadEq : updated.readScalar layout qRange false = state.readScalar layout qRange false :=
    hReadAfter.trans hReadBefore.symm
  rw [exactWP_seq, allocCopyExactWP_iff, hCopy]
  dsimp only
  rw [allocReadScalarExactWP_iff, hReadEq]
  have hCall := hFrame updated hCopy hReadEq
  rw [allocReadScalarExactWP_iff] at hCall
  exact hCall

/-! ### §1.4. Concrete Little-Endian & Big-Endian Disjoint Byte-Range & Uninit Witnesses -/

def layoutLE64 : TargetDataLayout := ⟨.little, .w64⟩
def layoutBE64 : TargetDataLayout := ⟨.big, .w64⟩

/-- Concrete 8-byte mutable zero-initialized allocation for LE/BE framing witnesses. -/
def sampleAlloc8 : Allocation Provenance Unit :=
  match h : Allocation.fromBytes (Prov := Provenance) (Array.replicate 8 (0 : UInt8))
      ⟨3⟩ .Mut with
  | .ok a => a
  | .error _ => False.elim (by cases h)

/-- Construct a canonical 4-byte unsigned integer `Miri.Memory.Scalar Provenance`. -/
def mkMiriU32Scalar (n : Nat) : Miri.Memory.Scalar Provenance :=
  match Miri.Memory.Scalar.fromUInt (BitVec.ofNat 128 n) (Size.ofBytes 4) with
  | .ok sc => sc
  | .error _ => Miri.Memory.Scalar.fromBool false

private theorem sampleAlloc8_fromBytes :
    Allocation.fromBytes (Prov := Provenance) (Array.replicate 8 (0 : UInt8)) Align.EIGHT .Mut =
      .ok sampleAlloc8 := by
  change Allocation.fromBytes (Prov := Provenance) (Array.replicate 8 (0 : UInt8)) ⟨3⟩ .Mut =
    .ok sampleAlloc8
  unfold sampleAlloc8
  split
  · rename_i a ha; exact ha
  · rename_i _ ha; cases ha

private theorem allocEndian_disjoint_witness_for_layout (lay : TargetDataLayout)
    (hPtrW : lay.pointerWidth = .w64) :
    let r0 : AllocRange := allocRange (Size.ofBytes 0) (Size.ofBytes 4)
    let r4 : AllocRange := allocRange (Size.ofBytes 4) (Size.ofBytes 4)
    let scA : Miri.Memory.Scalar Provenance := mkMiriU32Scalar 0x11223344
    let scB : Miri.Memory.Scalar Provenance := mkMiriU32Scalar 0xAABBCCDD
    let prog : ExactAction (Allocation Provenance Unit) AllocError (Miri.Memory.Scalar Provenance) :=
      ExactAction.seq (allocWriteScalarAction lay r0 scA)
        (ExactAction.seq (allocWriteScalarAction lay r4 scB)
          (ExactAction.seq (allocWriteUninitAction r4 (Size.ofBytes 8))
            (allocReadScalarAction lay r0 false)))
    let badProg : ExactAction (Allocation Provenance Unit) AllocError (Miri.Memory.Scalar Provenance) :=
      ExactAction.seq (allocWriteScalarAction lay r0 scA)
        (ExactAction.seq (allocWriteUninitAction r4 (Size.ofBytes 8))
          (allocReadScalarAction lay r4 false))
    AnnealExactWP prog
      (fun sc a =>
        sc = scA ∧
        a.getBytesUnchecked r0 =
          .ok (if lay.endian == .little then #[0x44, 0x33, 0x22, 0x11] else #[0x11, 0x22, 0x33, 0x44]))
      (fun _ _ => False) sampleAlloc8 ∧
    AnnealExactWP badProg
      (fun _ _ => False)
      (fun err _ => match err with | .invalidUninitBytes _ => True | _ => False) sampleAlloc8 := by
  let r0 : AllocRange := allocRange (Size.ofBytes 0) (Size.ofBytes 4)
  let r4 : AllocRange := allocRange (Size.ofBytes 4) (Size.ofBytes 4)
  let scA : Miri.Memory.Scalar Provenance := mkMiriU32Scalar 0x11223344
  let scB : Miri.Memory.Scalar Provenance := mkMiriU32Scalar 0xAABBCCDD
  have hPtrSz : Size.fromBits lay.pointerWidth.bits = Size.ofBytes 8 := by rw [hPtrW]; rfl
  have hEnd0 : r0.endExclusive = .ok (Size.ofBytes 4) := by decide
  have hEnd4 : r4.endExclusive = .ok (Size.ofBytes 8) := by decide
  have hConvA : scA.toBitsOrPtrInternal r0.size = .ok (.bits (BitVec.ofNat 128 0x11223344)) := by
    decide
  have hConvB : scB.toBitsOrPtrInternal r4.size = .ok (.bits (BitVec.ofNat 128 0xAABBCCDD)) := by
    decide
  have hFromA : (Miri.Memory.Scalar.fromUInt (Prov := Provenance)
      (BitVec.ofNat 128 0x11223344) r0.size).mapError AllocError.scalar = .ok scA := by decide
  obtain ⟨hBs0, hLen0, hMut0, -, -, hProv0, hMask0, hWf0, -⟩ :=
    Allocation.fromBytes_spec _ _ _ sampleAlloc8 sampleAlloc8_fromBytes
  have hStor0 : sampleAlloc8.len = sampleAlloc8.byteSize.bytes.toNat := hLen0.trans hBs0.symm
  have hMaskLen0 : sampleAlloc8.initializationMask.len = sampleAlloc8.byteSize := by rw [hMask0]; rfl
  -- Step 1: write scA to r0
  obtain ⟨a1, hW1, hBs1, hLen1, hMut1, -, -, -, hML1, hWf1, -, hInit1, hProv1, hBytes1, -, -⟩ :=
    Allocation.writeScalar_spec lay sampleAlloc8 r0 scA
      (.bits (BitVec.ofNat 128 0x11223344)) ProvenanceMap.new ProvenanceMap.new
      hStor0 hMut0 hMaskLen0 hWf0 (by decide) (by decide) (by rw [hBs0]; decide)
      hConvA (fun _ _ => by rw [hProv0, hPtrSz]; exact ProvenanceMap.clear_new _ _ _ _ (by decide) hEnd0) rfl
  have hBs1Nat : a1.byteSize.bytes.toNat = 8 := by rw [hBs1, hBs0]; decide
  have hStor1 : a1.len = a1.byteSize.bytes.toNat := by rw [hLen1, hBs1]; exact hStor0
  have hMaskLen1 : a1.initializationMask.len = a1.byteSize := by rw [hML1, hBs1]; exact hMaskLen0
  have hA1Bytes := hBytes1 (BitVec.ofNat 128 0x11223344) rfl
  have hMut1' : a1.mutability = .Mut := hMut1.trans hMut0
  -- Step 2: write scB to r4 on a1
  obtain ⟨a2, hW2, hBs2, hLen2, hMut2, -, -, -, hML2, hWf2, hSetM2, -, hProv2, -, -, hDisj2⟩ :=
    Allocation.writeScalar_spec lay a1 r4 scB
      (.bits (BitVec.ofNat 128 0xAABBCCDD)) ProvenanceMap.new ProvenanceMap.new
      hStor1 hMut1' hMaskLen1 hWf1 (by decide) (by decide) (by rw [hBs1Nat]; decide)
      hConvB (fun _ _ => by rw [hProv1, hPtrSz]; exact ProvenanceMap.clear_new _ _ _ _ (by decide) hEnd4) rfl
  have hMut2' : a2.mutability = .Mut := hMut2.trans hMut1'
  have hBs2Nat : a2.byteSize.bytes.toNat = 8 := by rw [hBs2, hBs1Nat]
  have hStor2 : a2.len = a2.byteSize.bytes.toNat := by rw [hLen2, hBs2]; exact hStor1
  have hMaskLen2 : a2.initializationMask.len = a2.byteSize := by rw [hML2, hBs2]; exact hMaskLen1
  have hInit2_r0 : a2.initializationMask.isRangeInitialized r0 = .ok (.ok ()) := by
    rw [InitMask.WriteProof.isRangeInitialized_frame a1.initializationMask a2.initializationMask
      r4 r0 (Size.ofBytes 8) (Size.ofBytes 4) true hWf1 hEnd4 hEnd0 (by decide) (by decide)
      (by rw [hMaskLen1, hBs1Nat]; decide) (by rw [hMaskLen1, hBs1Nat]; decide) (by decide) hSetM2]
    exact hInit1
  have hA2Bytes_r0 : a2.getBytesUnchecked r0 = a1.getBytesUnchecked r0 :=
    hDisj2 r0 (Size.ofBytes 4) hEnd0 (by decide) (by rw [hBs1Nat]; decide) (by decide)
  -- Step 3 (positive): writeUninit r4 on a2, then readScalar r0
  obtain ⟨a3, hW3, hBs3, -, -, -, -, -, hML3, -, hSetM3, hProv3, hBytes3⟩ :=
    Allocation.writeUninit_spec r4 (Size.ofBytes 8) a2 ProvenanceMap.new
      (by decide) hStor2 hMut2' hMaskLen2 hWf2 (by rw [hBs2Nat]; decide)
      (fun _ _ => by rw [hProv2]; exact ProvenanceMap.clear_new _ _ _ _ (by decide) hEnd4)
  have hInit3_r0 : a3.initializationMask.isRangeInitialized r0 = .ok (.ok ()) := by
    rw [InitMask.WriteProof.isRangeInitialized_frame a2.initializationMask a3.initializationMask
      r4 r0 (Size.ofBytes 8) (Size.ofBytes 4) false hWf2 hEnd4 hEnd0 (by decide) (by decide)
      (by rw [hMaskLen2, hBs2Nat]; decide) (by rw [hMaskLen2, hBs2Nat]; decide) (by decide) hSetM3]
    exact hInit2_r0
  have hA3Bytes_r0 : a3.getBytesUnchecked r0 =
      .ok (Array.ofFn (fun i : Fin r0.size.bytes.toNat =>
        UInt8.ofNat (((BitVec.ofNat 128 0x11223344).toNat / 2 ^ (8 *
          (if lay.endian == .little then i.1 else r0.size.bytes.toNat - i.1 - 1))) % 256))) := by
    rw [hBytes3 r0, hA2Bytes_r0, hA1Bytes]
  have hConcreteBytes :
      Array.ofFn (fun i : Fin r0.size.bytes.toNat =>
        UInt8.ofNat (((BitVec.ofNat 128 0x11223344).toNat / 2 ^ (8 *
          (if lay.endian == .little then i.1 else r0.size.bytes.toNat - i.1 - 1))) % 256)) =
      if lay.endian == .little then #[0x44, 0x33, 0x22, 0x11] else #[0x11, 0x22, 0x33, 0x44] := by
    cases lay.endian <;> decide
  have hProv3Empty : a3.provenanceMap.rangeEmpty r0 (Size.fromBits lay.pointerWidth.bits) = .ok true := by
    rw [hProv3, hPtrSz]; exact ProvenanceMap.rangeEmpty_new r0 (Size.ofBytes 8) (Size.ofBytes 4) (by decide) hEnd0
  -- Step 3 (negative): writeUninit r4 on a1, then readScalar r4 -> invalidUninitBytes
  obtain ⟨aBad, hWBad, hBsBad, -, -, -, -, -, hMLBad, hWfBad, hSetMBad, -, -⟩ :=
    Allocation.writeUninit_spec r4 (Size.ofBytes 8) a1 ProvenanceMap.new
      (by decide) hStor1 hMut1' hMaskLen1 hWf1 (by rw [hBs1Nat]; decide)
      (fun _ _ => by rw [hProv1]; exact ProvenanceMap.clear_new _ _ _ _ (by decide) hEnd4)
  have hGet4False : aBad.initializationMask.get (Size.ofBytes 4) = .ok false := by
    have hG := InitMask.WriteProof.set_range_get a1.initializationMask aBad.initializationMask
      r4 (Size.ofBytes 8) (Size.ofBytes 4) false hWf1 hEnd4 (by decide)
      (by rw [hMaskLen1, hBs1Nat]; decide) (by rw [hMaskLen1, hBs1Nat]; decide) hSetMBad
    simpa [r4, allocRange, Size.ofBytes] using hG
  obtain ⟨badRange, hBadInit⟩ :=
    (InitMask.WriteProof.isRangeInitialized_nonempty_iff aBad.initializationMask r4 (Size.ofBytes 8)
      hWfBad hEnd4 (by decide) (by rw [hMLBad, hMaskLen1, hBs1Nat]; decide)).2
      ⟨Size.ofBytes 4, by decide, by decide, hGet4False⟩
  constructor
  · rw [exactWP_seq, allocWriteScalarExactWP_iff, hW1]; dsimp only
    rw [exactWP_seq, allocWriteScalarExactWP_iff, hW2]; dsimp only
    rw [exactWP_seq, allocWriteUninitExactWP_iff, hW3]; dsimp only
    rw [allocReadScalar_int_roundtrip_exactWP a3 lay r0 (BitVec.ofNat 128 0x11223344) _ _
      hInit3_r0 (by decide) (by decide) (Or.inr hProv3Empty) hA3Bytes_r0, hFromA]
    exact ⟨rfl, by rw [hA3Bytes_r0, hConcreteBytes]⟩
  · rw [exactWP_seq, allocWriteScalarExactWP_iff, hW1]; dsimp only
    rw [exactWP_seq, allocWriteUninitExactWP_iff, hWBad]; dsimp only
    rw [allocReadScalar_uninit_exactWP aBad lay r4 badRange false _ _ hBadInit]
    trivial

/-- **Concrete LE & BE Endian Disjoint Byte-Range Framing & Uninit-Fault Witness**:
Writes `0x11223344` into `[0..4)` and `0xAABBCCDD` into `[4..8)` under BOTH `layoutLE64` and
`layoutBE64`, verifying:
1. Distinct byte-level encodings (`[0x44, 0x33, 0x22, 0x11]` in LE vs `[0x11, 0x22, 0x33, 0x44]` in BE);
2. Exact disjoint preservation of `[0..4)` across writing `[4..8)` and marking `[4..8)` uninit;
3. Exact `invalidUninitBytes` error when reading `[4..8)` after `writeUninit`! -/
theorem allocEndian_le_vs_be_disjoint_frame_witness :
    let r0 : AllocRange := allocRange (Size.ofBytes 0) (Size.ofBytes 4)
    let r4 : AllocRange := allocRange (Size.ofBytes 4) (Size.ofBytes 4)
    let scA : Miri.Memory.Scalar Provenance := mkMiriU32Scalar 0x11223344
    let scB : Miri.Memory.Scalar Provenance := mkMiriU32Scalar 0xAABBCCDD
    let prog (lay : TargetDataLayout) : ExactAction (Allocation Provenance Unit) AllocError (Miri.Memory.Scalar Provenance) :=
      ExactAction.seq (allocWriteScalarAction lay r0 scA)
        (ExactAction.seq (allocWriteScalarAction lay r4 scB)
          (ExactAction.seq (allocWriteUninitAction r4 (Size.ofBytes 8))
            (allocReadScalarAction lay r0 false)))
    let badProg (lay : TargetDataLayout) : ExactAction (Allocation Provenance Unit) AllocError (Miri.Memory.Scalar Provenance) :=
      ExactAction.seq (allocWriteScalarAction lay r0 scA)
        (ExactAction.seq (allocWriteUninitAction r4 (Size.ofBytes 8))
          (allocReadScalarAction lay r4 false))
    AnnealExactWP (prog layoutLE64)
      (fun sc a => sc = scA ∧ a.getBytesUnchecked r0 = .ok #[0x44, 0x33, 0x22, 0x11])
      (fun _ _ => False) sampleAlloc8 ∧
    AnnealExactWP (prog layoutBE64)
      (fun sc a => sc = scA ∧ a.getBytesUnchecked r0 = .ok #[0x11, 0x22, 0x33, 0x44])
      (fun _ _ => False) sampleAlloc8 ∧
    AnnealExactWP (badProg layoutLE64)
      (fun _ _ => False)
      (fun err _ => match err with | .invalidUninitBytes _ => True | _ => False) sampleAlloc8 ∧
    AnnealExactWP (badProg layoutBE64)
      (fun _ _ => False)
      (fun err _ => match err with | .invalidUninitBytes _ => True | _ => False) sampleAlloc8 := by
  have hLE := allocEndian_disjoint_witness_for_layout layoutLE64 rfl
  have hBE := allocEndian_disjoint_witness_for_layout layoutBE64 rfl
  exact ⟨hLE.1, hBE.1, hLE.2, hBE.2⟩

end MemoryLemmasWP

/-! ## §2. `Std.Do`-Free `TreeBorrowsWP` & `ProtectorReleaseWP` over Real Vendored `Miri.TreeBorrows.BorrowTree` -/

section TreeBorrowsAndProtectorWP

/-- Exact state-retaining `ExactAction` wrapping unmodified
`Miri.TreeBorrows.BorrowTree.performBorrowAccessRange` (mirrors `lean-miri#93` `TreeBorrowsWP.access`
without `Std.Do`): retains `result.tree` AND `result.locations` on BOTH `.Completed` and error! -/
def tbAccessAction (provenance : ProvenanceExtra) (offset length : Size)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) :
    ExactAction BorrowTree
      (BorrowTree.BorrowTreeAccessStatus × Array BorrowTree.BorrowTreeLocationResult)
      (Array BorrowTree.BorrowTreeLocationResult) :=
  fun tree =>
    let result := tree.performBorrowAccessRange provenance offset length kind tags mode
    match result.status with
    | .Completed => .ok result.locations result.tree
    | status => .error (status, result.locations) result.tree

/-- Exact symbolic precondition for `BorrowTree.performBorrowAccessRange` (mirrors
`lean-miri#93` `TreeBorrowsWP.accessPre`). -/
def tbAccessPre (tree : BorrowTree) (provenance : ProvenanceExtra) (offset length : Size)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode)
    (post : Array BorrowTree.BorrowTreeLocationResult → BorrowTree → Prop)
    (onError : (BorrowTree.BorrowTreeAccessStatus × Array BorrowTree.BorrowTreeLocationResult) →
      BorrowTree → Prop) : Prop :=
  let result := tree.performBorrowAccessRange provenance offset length kind tags mode
  match result.status with
  | .Completed => post result.locations result.tree
  | status => onError (status, result.locations) result.tree

/-- **Exact bidirectional `↔` theorem `tbAccessExactWP_iff`** for unmodified
`Miri.TreeBorrows.BorrowTree.performBorrowAccessRange`: retains committed `BorrowTree` AND
diagnostic `Array BorrowTreeLocationResult` on BOTH `.Completed` and error! -/
theorem tbAccessExactWP_iff (provenance : ProvenanceExtra) (offset length : Size)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode)
    (post : Array BorrowTree.BorrowTreeLocationResult → BorrowTree → Prop)
    (onError : (BorrowTree.BorrowTreeAccessStatus × Array BorrowTree.BorrowTreeLocationResult) →
      BorrowTree → Prop)
    (tree : BorrowTree) :
    AnnealExactWP (tbAccessAction provenance offset length kind tags mode) post onError tree ↔
      tbAccessPre tree provenance offset length kind tags mode post onError := by
  unfold AnnealExactWP tbAccessAction tbAccessPre
  dsimp only
  cases (tree.performBorrowAccessRange provenance offset length kind tags mode).status <;> rfl

/-- Exact state-retaining `ExactAction` wrapping unmodified `BorrowTree.deallocateBorrowRange`. -/
def tbDeallocAction (provenance : ProvenanceExtra) (offset length : Size)
    (tags : ProtectedTags) :
    ExactAction BorrowTree BorrowTree.BorrowTreeDeallocStatus Unit :=
  fun tree =>
    let result := tree.deallocateBorrowRange provenance offset length tags
    match result.status with
    | .Deallocated => .ok () result.tree
    | status => .error status result.tree

/-- Exact symbolic precondition for `BorrowTree.deallocateBorrowRange` (mirrors `lean-miri#93`
`TreeBorrowsWP.deallocatePre`). -/
def tbDeallocPre (tree : BorrowTree) (provenance : ProvenanceExtra) (offset length : Size)
    (tags : ProtectedTags)
    (post : Unit → BorrowTree → Prop)
    (onError : BorrowTree.BorrowTreeDeallocStatus → BorrowTree → Prop) : Prop :=
  let result := tree.deallocateBorrowRange provenance offset length tags
  match result.status with
  | .Deallocated => post () result.tree
  | status => onError status result.tree

/-- **Exact bidirectional `↔` theorem `tbDeallocExactWP_iff`** for unmodified
`Miri.TreeBorrows.BorrowTree.deallocateBorrowRange`. -/
theorem tbDeallocExactWP_iff (provenance : ProvenanceExtra) (offset length : Size)
    (tags : ProtectedTags)
    (post : Unit → BorrowTree → Prop)
    (onError : BorrowTree.BorrowTreeDeallocStatus → BorrowTree → Prop)
    (tree : BorrowTree) :
    AnnealExactWP (tbDeallocAction provenance offset length tags) post onError tree ↔
      tbDeallocPre tree provenance offset length tags post onError := by
  unfold AnnealExactWP tbDeallocAction tbDeallocPre
  dsimp only
  cases (tree.deallocateBorrowRange provenance offset length tags).status <;> rfl

/-- If the initial ranged write in `deallocateBorrowRange` fails, `tbDeallocAction` faults with
`.AccessFailure accessed.status` while retaining the EXACT committed tree `accessed.tree`! -/
theorem tbDealloc_accessFailure_retains_tree (provenance : ProvenanceExtra)
    (offset length : Size) (tags : ProtectedTags) (tree : BorrowTree)
    (post : Unit → BorrowTree → Prop)
    (onError : BorrowTree.BorrowTreeDeallocStatus → BorrowTree → Prop)
    (hFail : (tree.performBorrowAccessRange provenance offset length .Write tags
      .VisitChildrenOfAccessed).status ≠ .Completed) :
    AnnealExactWP (tbDeallocAction provenance offset length tags) post onError tree ↔
      let accessed := tree.performBorrowAccessRange provenance offset length .Write tags
        .VisitChildrenOfAccessed
      onError (.AccessFailure accessed.status) accessed.tree := by
  rw [tbDeallocExactWP_iff]
  unfold tbDeallocPre BorrowTree.deallocateBorrowRange
  have hNe : ((tree.performBorrowAccessRange provenance offset length .Write tags
      .VisitChildrenOfAccessed).status != .Completed) = true := bne_iff_ne.mpr hFail
  simp only [Id.run, hNe, ↓reduceIte, pure, Pure.pure]

/-- Exact state-retaining `ExactAction` wrapping unmodified
`Miri.TreeBorrows.BorrowTree.releaseProtector` (mirrors `lean-miri#93` `TreeBorrowsWP.release`
without `Std.Do`): retains the committed segment prefix in `result.tree` even on failure! -/
def protectorReleaseAction (tag : BorTag) (tags : ProtectedTags) :
    ExactAction BorrowTree BorrowTree.ProtectorReleaseStatus Unit :=
  fun tree =>
    let result := tree.releaseProtector tag tags
    match result.status with
    | .Released => .ok () result.tree
    | status => .error status result.tree

/-- Exact symbolic precondition for `BorrowTree.releaseProtector`, explicitly exposing the
missing-tag check vs. per-segment scan over `List.range' 0 tree.locations.entries.size`
(mirrors `lean-miri#93` `ProtectorReleaseWP.releasePre`). -/
def protectorReleasePre (tag : BorTag) (tags : ProtectedTags)
    (post : Unit → BorrowTree → Prop)
    (onError : BorrowTree.ProtectorReleaseStatus → BorrowTree → Prop)
    (tree : BorrowTree) : Prop :=
  match tree.indexOfTag tag with
  | none => onError (.MissingTag tag) tree
  | some _ =>
    let result := tree.releaseProtector tag tags
    match result.status with
    | .Released => post () result.tree
    | status => onError status result.tree

/-- **Exact bidirectional `↔` theorem `protectorReleaseExactWP_iff`** for unmodified
`Miri.TreeBorrows.BorrowTree.releaseProtector`: retains the committed segment prefix in
`result.tree` on failure and verifies missing-tag preservation! -/
theorem protectorReleaseExactWP_iff (tag : BorTag) (tags : ProtectedTags)
    (post : Unit → BorrowTree → Prop)
    (onError : BorrowTree.ProtectorReleaseStatus → BorrowTree → Prop)
    (tree : BorrowTree) :
    AnnealExactWP (protectorReleaseAction tag tags) post onError tree ↔
      protectorReleasePre tag tags post onError tree := by
  unfold AnnealExactWP protectorReleaseAction protectorReleasePre
  cases hIdx : tree.indexOfTag tag with
  | none =>
    unfold BorrowTree.releaseProtector
    simp only [Id.run, hIdx, pure, Pure.pure]
  | some src =>
    dsimp only
    cases (tree.releaseProtector tag tags).status <;> rfl

/-- Missing tag in `releaseProtector` faults with `.MissingTag tag` leaving `tree` untouched. -/
theorem protectorRelease_missingTag_exactWP (tag : BorTag) (tags : ProtectedTags)
    (post : Unit → BorrowTree → Prop)
    (onError : BorrowTree.ProtectorReleaseStatus → BorrowTree → Prop)
    (tree : BorrowTree) (hMiss : tree.indexOfTag tag = none) :
    AnnealExactWP (protectorReleaseAction tag tags) post onError tree ↔
      onError (.MissingTag tag) tree := by
  rw [protectorReleaseExactWP_iff]
  unfold protectorReleasePre
  rw [hMiss]

/-- Multi-access sequence over `BorrowTree` instantiating `Anneal.ExactWpAndSmartCtors.TreeBorrowsFrameWP`. -/
def tbAccessStepSpec (spec : ProvenanceExtra × Size × Size × AccessKind × ProtectedTags × Tree.ChildrenVisitMode) :
    ExactAction BorrowTree
      (BorrowTree.BorrowTreeAccessStatus × Array BorrowTree.BorrowTreeLocationResult) Unit :=
  ExactAction.bind (tbAccessAction spec.1 spec.2.1 spec.2.2.1 spec.2.2.2.1 spec.2.2.2.2.1 spec.2.2.2.2.2)
    (fun _ => ExactAction.pure ())

theorem tbAccessSequence_frameWP_iff
    (steps : List (ProvenanceExtra × Size × Size × AccessKind × ProtectedTags × Tree.ChildrenVisitMode))
    (post : List Unit → BorrowTree → Prop)
    (onError : (BorrowTree.BorrowTreeAccessStatus × Array BorrowTree.BorrowTreeLocationResult) →
      BorrowTree → Prop)
    (tree : BorrowTree) :
    TreeBorrowsFrameWP tbAccessStepSpec steps post onError tree ↔
      AnnealExactWP (treeBorrowsFrameAction tbAccessStepSpec steps) post onError tree :=
  Anneal.ExactWpAndSmartCtors.treeBorrowsFrameWP_iff tbAccessStepSpec steps post onError tree

/-- Multi-tag LIFO protector release sequence over `BorrowTree` instantiating
`Anneal.ExactWpAndSmartCtors.ProtectorReleaseWP`. -/
theorem protectorReleaseSequence_wp_iff
    (tags : ProtectedTags) (releaseOrder : List BorTag)
    (post : Unit → BorrowTree → Prop)
    (onError : BorrowTree.ProtectorReleaseStatus → BorrowTree → Prop)
    (tree : BorrowTree) :
    Anneal.ExactWpAndSmartCtors.ProtectorReleaseWP
        (fun tag => protectorReleaseAction tag tags) (ExactAction.pure ()) releaseOrder post onError tree ↔
      AnnealExactWP
        (ExactAction.seq
          (ExactAction.foldl (fun _ tag => protectorReleaseAction tag tags) () releaseOrder)
          (ExactAction.pure ()))
        post onError tree :=
  Anneal.ExactWpAndSmartCtors.protectorReleaseWP_iff
    (fun tag => protectorReleaseAction tag tags) (ExactAction.pure ()) releaseOrder post onError tree

/-! ### §2.1. Concrete Multi-Segment Committed-Prefix Error-State Witnesses on Real `BorrowTree` -/

-- Kernel-certified unrolled twins of vendored BorrowTree operations (zero `native_decide`).
unroll_lm_loops findOffsetLMU := Miri.DataStructures.DedupRangeMap.findOffset fuel 30
unroll_lm_loops iterMutWithCloneLMU := Miri.DataStructures.DedupRangeMap.iterMutWithClone fuel 20
  with findOffsetLMU
unroll_lm_loops iterMutLMU := Miri.DataStructures.DedupRangeMap.iterMut fuel 0
  with iterMutWithCloneLMU
unroll_lm_loops modifyRangeWithCloneLMU := Miri.DataStructures.DedupRangeMap.modifyRangeWithClone fuel 0
  with iterMutWithCloneLMU
unroll_lm_loops modifyRangeLMU := Miri.DataStructures.DedupRangeMap.modifyRange fuel 0
  with modifyRangeWithCloneLMU
unroll_lm_loops updateSifaAfterRetagLMU := Miri.TreeBorrows.BorrowTree.updateSifaAfterRetag fuel 20
unroll_lm_loops newChildLMU := Miri.TreeBorrows.BorrowTree.newChild fuel 0
  with updateSifaAfterRetagLMU, modifyRangeLMU
unroll_lm_loops minExposedChildLMU := Miri.TreeBorrows.BorrowTree.minExposedChild fuel 20
unroll_lm_loops performTreeAccessAtLMU := Miri.TreeBorrows.BorrowTree.performTreeAccessAt fuel 0
  with minExposedChildLMU
unroll_lm_loops performBorrowAccessRangeLMU :=
  Miri.TreeBorrows.BorrowTree.performBorrowAccessRange fuel 0
  with iterMutLMU, performTreeAccessAtLMU
unroll_lm_loops releaseProtectorLMU := Miri.TreeBorrows.BorrowTree.releaseProtector fuel 0
  with performTreeAccessAtLMU

/-- Build a 2-segment 16-byte `BorrowTree` where:
- root tag `1` owns `[0..16)` as `Unique`;
- child tag `2` is `Unique` (accessed) on `[0..16)` (protected by `tag 2`);
- sibling child tag `3` (child of root `1`) is **unprotected `Frozen`** on `[0..8)` and
  **protected `Frozen`** on `[8..16)` (Wait: `ProtectedTags` is per-tag, so we give tag `3`
  `Unique` on `[0..8)` and tag `4` (protected) `Frozen` on `[8..16)` — both children of root `1`!).
Specifically:
- Tag `1` (root, `UniIndex 0`): `Unique` on `[0..16)`.
- Tag `2` (child of `1`, `UniIndex 1`, unprotected): `Frozen` on `[0..8)`, `Disabled` on `[8..16)`.
- Tag `3` (child of `1`, `UniIndex 2`, **protected**): `Disabled` on `[0..8)`, `Frozen` (accessed) on `[8..16)`.
- Tag `4` (child of `1`, `UniIndex 3`, **protected**, accessed): `Active` (accessed `Unique`) on `[0..16)`.
When tag `4` writes across `[0..16)` (OR releases its protector across `[0..16)`):
- Segment 0 (`[0..8)`): tag `4`'s foreign write **commits** `tag 2: Frozen → Disabled` into `result.tree`!
- Segment 1 (`[8..16)`): tag `4`'s foreign write hits protected `tag 3` (`Frozen`) and **FAULTS**
  with `.AccessFailure` — leaving segment 0's `tag 2 → Disabled` mutation COMMITTED in `result.tree`! -/
private def tag1 : BorTag := ⟨1, by decide⟩
private def tag2 : BorTag := ⟨2, by decide⟩
private def tag3 : BorTag := ⟨3, by decide⟩
private def tag4 : BorTag := ⟨4, by decide⟩

noncomputable def twoSegmentCommitPrefixTree : BorrowTree :=
  let t0 := BorrowTree.new tag1 (Size.ofBytes 16)
  -- Child tag 2 (unprotected): Frozen (accessed, sifa=.Read) on [0..8), Cell outside
  let loc2In := DedupRangeMap.new (Size.ofBytes 8) ⟨Permission.newFrozen, true, .Read⟩
  let t1 := (newChildLMU t0 Size.ZERO (.concrete tag1) tag2 loc2In Permission.newCell false).tree
  -- Child tag 3 (protected): Frozen (accessed, sifa=.Read) on [8..16), Cell outside (exempt on [0..8))
  let loc3In := DedupRangeMap.new (Size.ofBytes 8) ⟨Permission.newFrozen, true, .Read⟩
  let t2 := (newChildLMU t1 (Size.ofBytes 8) (.concrete tag1) tag3 loc3In Permission.newCell true).tree
  -- Child tag 4 (protected): Active (Unique, accessed, sifa=.None) on [0..16), Cell outside
  let loc4In := DedupRangeMap.new (Size.ofBytes 16) ⟨Permission.newUnique, true, .None⟩
  (newChildLMU t2 Size.ZERO (.concrete tag1) tag4 loc4In Permission.newCell true).tree

/-- Protected tag map marking tag `3` (strong protector on `[8..16)`) and tag `4` (releasing tag). -/
def twoSegmentProtectedTags : ProtectedTags :=
  ({} : ProtectedTags)
    |>.insert tag3 .StrongProtector
    |>.insert tag4 .StrongProtector

/-- Helper inspecting tag `2`'s permission in segment 0 (`[0..8)`). -/
def seg0Tag2Perm (tree : BorrowTree) : Option Permission :=
  match tree.locations.index 0, tree.indexOfTag tag2 with
  | .ok seg, some idx => (seg.data.perms.get idx).map (·.permission)
  | _, _ => none

/-- **Concrete Multi-Segment Committed-Prefix Error Witness (`performBorrowAccessRange`)**:
On real vendored `BorrowTree.performBorrowAccessRange`, writing via tag `4` across `[0..16)`
1. starts with tag `2` `Frozen` on segment 0 (`[0..8)`),
2. faults on segment 1 (`[8..16)`) due to protected sibling tag `3` (`AccessFailure`), AND
3. **RETAINS** the committed segment-0 mutation (`tag 2` is now `Disabled` on `[0..8)`, so
   `result.tree ≠ twoSegmentCommitPrefixTree`) inside `AnnealExactWP`'s `onError` continuation! -/
theorem tb_access_committed_prefix_on_error_witness :
    seg0Tag2Perm twoSegmentCommitPrefixTree = some Permission.newFrozen ∧
    AnnealExactWP
      (tbAccessAction (.concrete tag4) Size.ZERO (Size.ofBytes 16) .Write
        twoSegmentProtectedTags .VisitChildrenOfAccessed)
      (fun _ _ => False)
      (fun errErr committedTree =>
        (match errErr.1 with | .AccessFailure _ _ => True | _ => False) ∧
        errErr.2.size = 2 ∧
        seg0Tag2Perm committedTree = some Permission.newDisabled ∧
        committedTree ≠ twoSegmentCommitPrefixTree)
      twoSegmentCommitPrefixTree := by
  have hInit : seg0Tag2Perm twoSegmentCommitPrefixTree = some Permission.newFrozen := by kernel_rfl
  refine ⟨hInit, ?_⟩
  rw [tbAccessExactWP_iff]
  unfold tbAccessPre
  dsimp only
  rw [performBorrowAccessRangeLMU.eq_src]
  have hStatus :
      (performBorrowAccessRangeLMU twoSegmentCommitPrefixTree (.concrete tag4) Size.ZERO
        (Size.ofBytes 16) .Write twoSegmentProtectedTags .VisitChildrenOfAccessed).status =
      .AccessFailure ⟨8, 16⟩ (.TransitionError 2 (.ProtectedDisabled .Frozen)) := by kernel_rfl
  have hLocs :
      (performBorrowAccessRangeLMU twoSegmentCommitPrefixTree (.concrete tag4) Size.ZERO
        (Size.ofBytes 16) .Write twoSegmentProtectedTags .VisitChildrenOfAccessed).locations.size = 2 := by
    kernel_rfl
  have hDis :
      seg0Tag2Perm
        (performBorrowAccessRangeLMU twoSegmentCommitPrefixTree (.concrete tag4) Size.ZERO
          (Size.ofBytes 16) .Write twoSegmentProtectedTags .VisitChildrenOfAccessed).tree =
      some Permission.newDisabled := by kernel_rfl
  rw [hStatus]
  refine ⟨trivial, hLocs, hDis, fun hEq => ?_⟩
  have hPerm := congrArg seg0Tag2Perm hEq
  rw [hDis, hInit] at hPerm
  cases hPerm

/-- **Concrete Multi-Segment Committed-Prefix Error Witness (`releaseProtector`)**:
On real vendored `BorrowTree.releaseProtector`, releasing tag `4`'s protector across the 2-segment
`twoSegmentCommitPrefixTree`:
1. executes tag `4`'s implicit protector-end write on segment 0 (`[0..8)`), committing
   `tag 2: Frozen → Disabled` into `currentTree`,
2. hits protected sibling tag `3` on segment 1 (`[8..16)`) and faults with `.AccessFailure`, AND
3. **RETAINS** the committed segment-0 tree update in `AnnealExactWP`'s `onError` continuation
   (`seg0Tag2Perm committedTree = some Permission.newDisabled` and `committedTree ≠ initTree`)! -/
theorem protector_release_committed_prefix_on_error_witness :
    seg0Tag2Perm twoSegmentCommitPrefixTree = some Permission.newFrozen ∧
    AnnealExactWP
      (protectorReleaseAction tag4 twoSegmentProtectedTags)
      (fun _ _ => False)
      (fun status committedTree =>
        (match status with | .AccessFailure _ _ => True | _ => False) ∧
        seg0Tag2Perm committedTree = some Permission.newDisabled ∧
        committedTree ≠ twoSegmentCommitPrefixTree)
      twoSegmentCommitPrefixTree := by
  have hInit : seg0Tag2Perm twoSegmentCommitPrefixTree = some Permission.newFrozen := by kernel_rfl
  refine ⟨hInit, ?_⟩
  rw [protectorReleaseExactWP_iff]
  unfold protectorReleasePre
  have hIdx4 : twoSegmentCommitPrefixTree.indexOfTag tag4 = some ⟨3⟩ := by kernel_rfl
  rw [hIdx4]
  dsimp only
  rw [releaseProtectorLMU.eq_src]
  have hStatus :
      (releaseProtectorLMU twoSegmentCommitPrefixTree tag4 twoSegmentProtectedTags).status =
      .AccessFailure ⟨8, 16⟩ (.AccessFailure ⟨8, 16⟩ (.TransitionError 2 (.ProtectedDisabled .Frozen))) := by
    kernel_rfl
  have hDis :
      seg0Tag2Perm
        (releaseProtectorLMU twoSegmentCommitPrefixTree tag4 twoSegmentProtectedTags).tree =
      some Permission.newDisabled := by kernel_rfl
  rw [hStatus]
  refine ⟨trivial, hDis, fun hEq => ?_⟩
  have hPerm := congrArg seg0Tag2Perm hEq
  rw [hDis, hInit] at hPerm
  cases hPerm

end TreeBorrowsAndProtectorWP

/-! ## §3. Whole-Body `Miri.Interpreter.Step.step` `ExactWP` (`StepWP` / `CanonicalStepWP` Mirror) -/

section StepAndBodyWP

variable {P L E M C V : Type}

/-- Lift one `Miri.Interpreter.Step.step` into `ExactAction (StepState P L E M) StepError Bool`
(retains the exact post-state on BOTH `.ok more` AND `.error err`, mirroring `lean-miri#93`). -/
def miriStepAction (hooks : StepHooks P L E M C V) (choice : C) :
    ExactAction (StepState P L E M) StepError Bool :=
  fun state =>
    match Step.step hooks choice state with
    | (after, .ok more) => .ok more after
    | (after, .error err) => .error err after

/-- Exact single-step precondition for `Miri.Interpreter.Step.step`. -/
def miriStepPre (hooks : StepHooks P L E M C V) (choice : C)
    (post : Bool → StepState P L E M → Prop)
    (onError : StepError → StepState P L E M → Prop)
    (state : StepState P L E M) : Prop :=
  match Step.step hooks choice state with
  | (after, .ok more) => post more after
  | (after, .error err) => onError err after

/-- **Exact bidirectional `↔` theorem `miriStepExactWP_iff`** for unmodified
`Miri.Interpreter.Step.step`. -/
theorem miriStepExactWP_iff (hooks : StepHooks P L E M C V) (choice : C)
    (post : Bool → StepState P L E M → Prop)
    (onError : StepError → StepState P L E M → Prop)
    (state : StepState P L E M) :
    AnnealExactWP (miriStepAction hooks choice) post onError state ↔
      miriStepPre hooks choice post onError state := by
  unfold AnnealExactWP miriStepAction miriStepPre
  cases Step.step hooks choice state with
  | mk after res => cases res <;> rfl

/-- Exact branch law: empty call stack terminates cleanly with `more = false`. -/
theorem miriStepExactWP_emptyStack (hooks : StepHooks P L E M C V) (choice : C)
    (post : Bool → StepState P L E M → Prop)
    (onError : StepError → StepState P L E M → Prop)
    (state : StepState P L E M)
    (hEmpty : state.stack.currentFrame? = none) :
    AnnealExactWP (miriStepAction hooks choice) post onError state ↔
      post false state := by
  rw [miriStepExactWP_iff]
  unfold miriStepPre Step.step
  simp only [Id.run, hEmpty, pure, Pure.pure]

/-- Exact branch law: `.unwinding` frame location delegates to `hooks.returnFromCurrentFrame choice true`. -/
theorem miriStepExactWP_unwinding (hooks : StepHooks P L E M C V) (choice : C)
    (post : Bool → StepState P L E M → Prop)
    (onError : StepError → StepState P L E M → Prop)
    (state : StepState P L E M) (frame : Frame P L E) (span : Miri.MIR.SpanRef)
    (hFrame : state.stack.currentFrame? = some frame)
    (hLoc : frame.location = .unwinding span) :
    AnnealExactWP (miriStepAction hooks choice) post onError state ↔
      match hooks.returnFromCurrentFrame choice true state with
      | (after, .ok ()) => post true after
      | (after, .error err) => onError err after := by
  rw [miriStepExactWP_iff]
  unfold miriStepPre Step.step
  simp only [Id.run, hFrame, hLoc, pure, Pure.pure]
  cases hRet : hooks.returnFromCurrentFrame choice true state with
  | mk after res =>
    cases res <;> rfl

/-- Exact branch law: out-of-bounds basic block index faults with `.invalidBlock loc.block`. -/
theorem miriStepExactWP_invalidBlock (hooks : StepHooks P L E M C V) (choice : C)
    (post : Bool → StepState P L E M → Prop)
    (onError : StepError → StepState P L E M → Prop)
    (state : StepState P L E M) (frame : Frame P L E) (loc : Miri.MIR.Location)
    (hFrame : state.stack.currentFrame? = some frame)
    (hLoc : frame.location = .mir loc)
    (hNone : frame.body.basicBlocks[loc.block]? = none) :
    AnnealExactWP (miriStepAction hooks choice) post onError state ↔
      onError (.invalidBlock loc.block) state := by
  rw [miriStepExactWP_iff]
  unfold miriStepPre Step.step
  simp only [Id.run, hFrame, hLoc, hNone, pure, Pure.pure]

/-- Exact branch law: end-of-block runs `hooks.beforeTerminator` then `hooks.terminator`. -/
theorem miriStepExactWP_terminator (hooks : StepHooks P L E M C V) (choice : C)
    (post : Bool → StepState P L E M → Prop)
    (onError : StepError → StepState P L E M → Prop)
    (state : StepState P L E M) (frame : Frame P L E) (loc : Miri.MIR.Location)
    (bb : Miri.MIR.BasicBlock)
    (hFrame : state.stack.currentFrame? = some frame)
    (hLoc : frame.location = .mir loc)
    (hBlock : frame.body.basicBlocks[loc.block]? = some bb)
    (hEnd : bb.statements[loc.statementIndex]? = none) :
    AnnealExactWP (miriStepAction hooks choice) post onError state ↔
      match hooks.beforeTerminator choice state with
      | (s1, .error err) => onError err s1
      | (s1, .ok ()) =>
        match hooks.terminator choice bb.terminator s1 with
        | (s2, .ok ()) => post true s2
        | (s2, .error err) => onError err s2 := by
  rw [miriStepExactWP_iff]
  unfold miriStepPre Step.step
  simp only [Id.run, hFrame, hLoc, hBlock, hEnd, pure, Pure.pure]
  cases hooks with
  | mk _ _ _ _ _ _ _ _ bt termHook =>
    dsimp only at *
    cases hPre : bt choice state with
    | mk s1 r1 =>
      dsimp only
      cases r1 with
      | error err => rfl
      | ok u =>
        cases u
        dsimp only
        cases hTerm : termHook choice bb.terminator s1 with
        | mk s2 r2 => cases r2 <;> rfl

/-- Relational choice-quantified exact step precondition (`Std.Do`-free mirror of
`lean-miri#93` `StepWP.stepPre`). -/
def miriAllowedStepPre (hooks : StepHooks P L E M C V)
    (allowed : StepState P L E M → C → Prop) (more : Bool)
    (post : StepState P L E M → Prop)
    (onError : StepError → StepState P L E M → Prop)
    (state : StepState P L E M) : Prop :=
  (∃ choice, allowed state choice) ∧
    ∀ choice, allowed state choice →
      AnnealExactWP (miriStepAction hooks choice)
        (fun actual after => actual = more ∧ post after) onError state

/-- **Exact bidirectional `↔` relational step theorem `miriAllowedStepExactWP_iff`**
(mirrors `lean-miri#93` `StepWP.stepPre_iff_allowedStep` over unmodified `Step.AllowedStep`). -/
theorem miriAllowedStepExactWP_iff (hooks : StepHooks P L E M C V)
    (allowed : StepState P L E M → C → Prop) (more : Bool)
    (post : StepState P L E M → Prop)
    (onError : StepError → StepState P L E M → Prop)
    (before : StepState P L E M) :
    miriAllowedStepPre hooks allowed more post onError before ↔
      (∃ choice, allowed before choice) ∧
        ∀ after result, Step.AllowedStep hooks allowed before after result →
          match result with
          | .ok actual => actual = more ∧ post after
          | .error err => onError err after := by
  constructor
  · rintro ⟨hEn, hAll⟩
    refine ⟨hEn, fun after result hStep => ?_⟩
    obtain ⟨choice, hPerm, hEq⟩ := hStep
    have hWp := (miriStepExactWP_iff hooks choice _ onError before).mp (hAll choice hPerm)
    unfold miriStepPre at hWp
    rw [hEq] at hWp
    cases result <;> exact hWp
  · rintro ⟨hEn, hChecked⟩
    refine ⟨hEn, fun choice hPerm => ?_⟩
    rw [miriStepExactWP_iff]
    unfold miriStepPre
    cases hEq : Step.step hooks choice before with
    | mk after result =>
      have hC := hChecked after result ⟨choice, hPerm, hEq⟩
      cases result <;> exact hC

/-- Fuel-bounded multi-step `ExactAction` over unmodified `Miri.Interpreter.Step.step`:
runs until `step` returns `.ok false` (empty stack / clean termination), faults with `.error err`,
or exhausts fuel with `.error (.resourceExhaustion "fuel exhausted")`. -/
def miriRunFuelAction (hooks : StepHooks P L E M C V) (choice : C) :
    Nat → ExactAction (StepState P L E M) StepError Unit
  | 0, state => .error (.resourceExhaustion "fuel exhausted") state
  | steps + 1, state =>
    ExactAction.bind (miriStepAction hooks choice)
      (fun more => if more then miriRunFuelAction hooks choice steps else ExactAction.pure ())
      state

/-- Fuel-bounded whole-body exact safety VC generator over `Miri.Interpreter.Step.step`. -/
def miriBodySafetyVC (hooks : StepHooks P L E M C V) (choice : C) :
    Nat → (StepState P L E M → Prop) → (StepError → StepState P L E M → Prop) →
      StepState P L E M → Prop
  | 0, _, onError, state => onError (.resourceExhaustion "fuel exhausted") state
  | steps + 1, post, onError, state =>
    AnnealExactWP (miriStepAction hooks choice)
      (fun more after => if more then miriBodySafetyVC hooks choice steps post onError after else post after)
      onError state

/-- **Exact bidirectional `↔` whole-body safety VC theorem `miriBodyExactWP_iff`** for unmodified
`Miri.Interpreter.Step.step`: `miriBodySafetyVC` is SIMULTANEOUSLY necessary and sufficient for
`AnnealExactWP (miriRunFuelAction hooks choice steps)`! -/
theorem miriBodyExactWP_iff (hooks : StepHooks P L E M C V) (choice : C)
    (steps : Nat) (post : StepState P L E M → Prop)
    (onError : StepError → StepState P L E M → Prop)
    (state : StepState P L E M) :
    AnnealExactWP (miriRunFuelAction hooks choice steps) (fun _ s' => post s') onError state ↔
      miriBodySafetyVC hooks choice steps post onError state := by
  induction steps generalizing state with
  | zero => exact Iff.rfl
  | succ k ih =>
    change AnnealExactWP
      (ExactAction.bind (miriStepAction hooks choice)
        (fun more => if more then miriRunFuelAction hooks choice k else ExactAction.pure ()))
      (fun _ s' => post s') onError state ↔ _
    rw [exactWP_bind]
    unfold miriBodySafetyVC
    constructor
    · exact exactWP_consequence
        (fun more after hM => by
          cases more with
          | true => exact (ih after).mp hM
          | false => exact hM)
        (fun _ _ hE => hE)
    · exact exactWP_consequence
        (fun more after hM => by
          cases more with
          | true => exact (ih after).mpr hM
          | false => exact hM)
        (fun _ _ hE => hE)

/-- Whole-body exact negation refutation corollary: if `miriBodySafetyVC` fails (e.g. an error
path violates `onError`), then `AnnealExactWP (miriRunFuelAction ...)` is PROVABLY FALSE! -/
theorem miriBodyExactWP_negation_refutation (hooks : StepHooks P L E M C V) (choice : C)
    (steps : Nat) (post : StepState P L E M → Prop)
    (onError : StepError → StepState P L E M → Prop)
    (state : StepState P L E M)
    (hNot : ¬ miriBodySafetyVC hooks choice steps post onError state) :
    ¬ AnnealExactWP (miriRunFuelAction hooks choice steps) (fun _ s' => post s') onError state :=
  fun h => hNot ((miriBodyExactWP_iff hooks choice steps post onError state).mp h)

/-- Inductive loop-invariant discharge rule for `miriBodySafetyVC`: if `Inv` is preserved on every
continuing step (`more = true`), implies `post` on termination (`more = false`), and implies
`onError` on errors (including fuel exhaustion), then `Inv s → miriBodySafetyVC ... s` for all
step budgets `steps : Nat`! -/
theorem miriBodyExactWP_loop_invariant (hooks : StepHooks P L E M C V) (choice : C)
    (Inv : StepState P L E M → Prop)
    (post : StepState P L E M → Prop) (onError : StepError → StepState P L E M → Prop)
    (hStep : ∀ s, Inv s →
      AnnealExactWP (miriStepAction hooks choice)
        (fun more s' => if more then Inv s' else post s') onError s)
    (hFuel : ∀ s, Inv s → onError (.resourceExhaustion "fuel exhausted") s) :
    ∀ steps s, Inv s → miriBodySafetyVC hooks choice steps post onError s := by
  intro steps
  induction steps with
  | zero => intro s hI; exact hFuel s hI
  | succ k ih =>
    intro s hI
    unfold miriBodySafetyVC
    exact exactWP_consequence
      (fun more s' hM => by
        cases more with
        | true => exact ih s' hM
        | false => exact hM)
      (fun _ _ hE => hE)
      (hStep s hI)

/-! ### §3.1. Concrete End-to-End Instantiations on Real `translateBody`-Lowered `CapturedMir` Bodies -/

/-- Extended `ControlHooks` wiring `unwindTerminate` to `.termination (.abort "unwindTerminate")`
(keeping all other `annealControlHooks` identical). -/
def annealUnwindControlHooks :
    ControlHooks AnnealProv LocalLayout Unit AnnealMachine Unit (Miri.Interpreter.Operand AnnealProv) :=
  { annealControlHooks with
    unwindTerminate := fun _ _ state => (state, .error (.termination (.abort "unwindTerminate"))) }

/-- Extended `TerminatorHooks` wiring `assertPanic` directly to vendored
`Miri.Interpreter.ControlFlow.unwindToBlock` so `.assert` dispatches `.cleanup bb`, `.terminate`,
`.continue`, and `.unreachable` cleanly through `ControlFlow.unwindToBlock`! -/
def annealUnwindTerminatorHooks (localDecls : List LocalDecl := .nil)
    (layouts : AnnealLayoutTable := emptyLayoutTable) :
    TerminatorHooks AnnealProv LocalLayout Unit AnnealMachine Unit
      (Miri.Interpreter.Operand AnnealProv) (RvalueImmTy AnnealProv) :=
  { annealTerminatorHooks localDecls layouts with
    toControlHooks := annealUnwindControlHooks
    assertPanic := fun choice _ unwind state =>
      ControlFlow.unwindToBlock annealUnwindControlHooks choice unwind state }

/-- Extended `StepHooks` using `annealUnwindControlHooks` and `annealUnwindTerminatorHooks`. -/
def annealUnwindStepHooks (localDecls : List LocalDecl := .nil)
    (layouts : AnnealLayoutTable := emptyLayoutTable) :
    StepHooks AnnealProv LocalLayout Unit AnnealMachine Unit (RuntimePlace AnnealProv) :=
  { annealStepHooks localDecls layouts with
    returnFromCurrentFrame := fun choice unwinding state =>
      ControlFlow.returnFromCurrentFrame annealUnwindControlHooks choice unwinding state
    terminator := fun choice term state =>
      ControlFlow.evalTerminator (annealUnwindTerminatorHooks localDecls layouts) choice term state }

private def u32Ty : Trusted.Rustc.V2026_06_01.MirAst.Ty := ⟨.uint .u32, 0⟩
private def boolTy : Trusted.Rustc.V2026_06_01.MirAst.Ty := ⟨.bool, 0⟩
private def u32Decl : LocalDecl := ⟨.mut, u32Ty, some "ret"⟩

private def ep2LayoutUnit : Trusted.Rustc.V2026_06_01.Layout.TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false }

private def mkEp2Body (name : String) (decls : List LocalDecl) (blocks : List BasicBlockData) :
    CapturedMir :=
  { defPath := name
    phase := .runtimePostCleanup
    role := .subject
    argCount := 0
    localDecls := decls
    basicBlocks := blocks
    fnAbi := { args := [], ret := { layout := ep2LayoutUnit, mode := .direct },
               conv := .rust, canUnwind := true }
    layouts := emptyLayoutTable
    allocations := [] }

/-- Build a canonical initial root `AnnealStepState` for any `CapturedMir` body lowered through
`LeanMiriSpec.Correspondence.translateBody`, with live uninitialized locals ready at `(bb0, 0)`. -/
def initMiriStateForBody (cm : CapturedMir) (layouts : AnnealLayoutTable := emptyLayoutTable) :
    AnnealStepState :=
  let body := translateBody cm
  let locals : Array (LocalState AnnealProv LocalLayout) :=
    (cm.localDecls.map fun d =>
      ({ value := .live (.immediate .uninit), layout := some (translateTy d.ty layouts) } :
        LocalState AnnealProv LocalLayout)).toArray
  let frame : Frame AnnealProv LocalLayout Unit :=
    { body := body
      bodyIdentity := BodyIdentity.ofCanonicalIndex 0
      functionInstance := ⟨.Item 0, #[]⟩
      extra := ()
      returnContinuation := .stop false
      returnPlace := .frameLocal 0 0 none (translateTy u32Ty layouts)
        (LocalsIdentity.ofAllocationToken 0)
      localsIdentity := LocalsIdentity.ofAllocationToken 0
      locals := locals
      vaList := #[]
      trackCallerArg := none
      location := .mir ⟨0, 0⟩ }
  { stack := { frames := #[frame] }, machine := AnnealMachine.empty }

/-- Helper: extract a `u32` scalar's numeric bits from local `0` of the active frame if present. -/
def activeLocal0Bits (st : AnnealStepState) : Option Nat :=
  match st.stack.currentFrame? with
  | none => none
  | some fr =>
    match fr.getLocal 0 with
    | .ok ⟨.live (.immediate (.scalar sc)), _⟩ =>
      match sc.toBits (Size.ofBytes 4) with
      | .ok bits => some bits.toNat
      | .error _ => none
    | _ => none

/-- Body 1 (Normal Return): `bb0: _0 = const 42u32; return`. -/
def bodyNormalReturn : CapturedMir :=
  mkEp2Body "ep2::normal_return" [u32Decl]
    [ { statements :=
          [ { kind := .assign ⟨0, []⟩ (.use (.constant ⟨u32Ty, .scalar (.int ⟨42, 4⟩)⟩)),
              span := "s0" } ],
        terminator := { kind := .return_, span := "t0" },
        isCleanup := false } ]

/-- **Whole-body `ExactWP` discharge #1 (Normal Return on `translateBody bodyNormalReturn`)**:
Discharges `miriBodySafetyVC` (and hence `AnnealExactWP (miriRunFuelAction ...)`) over unmodified
`Miri.Interpreter.Step.step (annealStepHooks ...)`, proving clean termination with empty stack
(`frames = #[]`) and zero errors! -/
theorem miriBodyExactWP_normal_return :
    let hooks := annealStepHooks bodyNormalReturn.localDecls emptyLayoutTable
    let init := initMiriStateForBody bodyNormalReturn emptyLayoutTable
    AnnealExactWP (miriRunFuelAction hooks () 4)
      (fun _ final => final.stack.frames = #[])
      (fun _ _ => False) init ∧
    miriBodySafetyVC hooks () 4 (fun final => final.stack.frames = #[]) (fun _ _ => False) init := by
  have hVC : miriBodySafetyVC (annealStepHooks bodyNormalReturn.localDecls emptyLayoutTable) () 4
      (fun final => final.stack.frames = #[]) (fun _ _ => False)
      (initMiriStateForBody bodyNormalReturn emptyLayoutTable) := rfl
  exact ⟨(miriBodyExactWP_iff ..).mpr hVC, hVC⟩

/-- Body 2 (Unreachable UB): `bb0: unreachable`. -/
def bodyUnreachableUB : CapturedMir :=
  mkEp2Body "ep2::unreachable_ub" [u32Decl]
    [ { statements := [],
        terminator := { kind := .unreachable, span := "t0" },
        isCleanup := false } ]

/-- **Whole-body `ExactWP` discharge & bidirectional `↔` UB refutation #2 (`unreachable`)**:
Proves BOTH:
1. `AnnealExactWP` discharges with `.undefinedBehavior "Unreachable"`, AND
2. Via bidirectional `↔` (`miriBodyExactWP_negation_refutation`), `¬ AnnealExactWP ... (fun _ _ => True) (fun _ _ => False)`! -/
theorem miriBodyExactWP_unreachable_ub_refutation :
    let hooks := annealStepHooks bodyUnreachableUB.localDecls emptyLayoutTable
    let init := initMiriStateForBody bodyUnreachableUB emptyLayoutTable
    AnnealExactWP (miriRunFuelAction hooks () 3)
      (fun _ _ => False)
      (fun err _ => err = .undefinedBehavior "Unreachable") init ∧
    ¬ AnnealExactWP (miriRunFuelAction hooks () 3)
      (fun _ _ => True) (fun _ _ => False) init := by
  refine ⟨rfl, ?_⟩
  apply miriBodyExactWP_negation_refutation
  intro hFalse
  exact hFalse

/-- Body 3 (Passing Assert → Multi-Block Return):
`bb0: assert(true == true, target: bb1, unwind: terminate); bb1: _0 = 77u32; return`. -/
def bodyAssertPassReturn : CapturedMir :=
  mkEp2Body "ep2::assert_pass_return" [u32Decl]
    [ { statements := [],
        terminator :=
          { kind := .assert (.constant ⟨boolTy, .scalar (.int ⟨1, 1⟩)⟩) true 1 .terminate,
            span := "t0" },
        isCleanup := false },
      { statements :=
          [ { kind := .assign ⟨0, []⟩ (.use (.constant ⟨u32Ty, .scalar (.int ⟨77, 4⟩)⟩)),
              span := "s1" } ],
        terminator := { kind := .return_, span := "t1" },
        isCleanup := false } ]

/-- **Whole-body `ExactWP` discharge #3 (Multi-block passing `Assert` → `Return`)**. -/
theorem miriBodyExactWP_assert_pass_return :
    let hooks := annealUnwindStepHooks bodyAssertPassReturn.localDecls emptyLayoutTable
    let init := initMiriStateForBody bodyAssertPassReturn emptyLayoutTable
    AnnealExactWP (miriRunFuelAction hooks () 5)
      (fun _ final => final.stack.frames = #[])
      (fun _ _ => False) init := rfl

/-- Body 4 (Failing Assert with `.terminate`):
`bb0: assert(false == true, target: bb1, unwind: terminate)`. -/
def bodyAssertFailTerminate : CapturedMir :=
  mkEp2Body "ep2::assert_fail_terminate" [u32Decl]
    [ { statements := [],
        terminator :=
          { kind := .assert (.constant ⟨boolTy, .scalar (.int ⟨0, 1⟩)⟩) true 1 .terminate,
            span := "t0" },
        isCleanup := false },
      { statements := [],
        terminator := { kind := .return_, span := "t1" },
        isCleanup := false } ]

/-- **Whole-body `ExactWP` discharge #4 (Failing `Assert` with `.terminate` → `.termination (.abort _)`)**. -/
theorem miriBodyExactWP_assert_fail_terminate :
    let hooks := annealUnwindStepHooks bodyAssertFailTerminate.localDecls emptyLayoutTable
    let init := initMiriStateForBody bodyAssertFailTerminate emptyLayoutTable
    AnnealExactWP (miriRunFuelAction hooks () 4)
      (fun _ _ => False)
      (fun err _ => err = .termination (.abort "unwindTerminate")) init ∧
    ¬ AnnealExactWP (miriRunFuelAction hooks () 4)
      (fun _ _ => True) (fun _ _ => False) init := by
  refine ⟨rfl, ?_⟩
  apply miriBodyExactWP_negation_refutation
  intro hFalse
  exact hFalse

/-- Body 5 (Failing Assert with `.cleanup bb2` → Cleanup Mutation `_0 = 99u32` → `UnwindResume`):
Demonstrates multi-block panic unwinding in `Miri.Interpreter.Step.step`:
- `bb0` fails `Assert` and jumps via `ControlFlow.unwindToBlock` to cleanup block `bb2`;
- `bb2` assigns `_0 = const 99u32` (observable cleanup side effect!);
- `bb2` executes `UnwindResume` → `returnFromCurrentFrame(..., unwinding := true)` on root frame,
  faulting with root-unwind UB **while retaining the committed `_0 = 99` cleanup state**! -/
def bodyAssertCleanupResume : CapturedMir :=
  mkEp2Body "ep2::assert_cleanup_resume" [u32Decl]
    [ { statements := [],
        terminator :=
          { kind := .assert (.constant ⟨boolTy, .scalar (.int ⟨0, 1⟩)⟩) true 1 (.cleanup 2),
            span := "t0" },
        isCleanup := false },
      { statements := [],
        terminator := { kind := .return_, span := "t1" },
        isCleanup := false },
      { statements :=
          [ { kind := .assign ⟨0, []⟩ (.use (.constant ⟨u32Ty, .scalar (.int ⟨99, 4⟩)⟩)),
              span := "s2" } ],
        terminator := { kind := .unwindResume, span := "t2" },
        isCleanup := true } ]

/-- **Whole-body `ExactWP` discharge #5 (Failing `Assert` → Cleanup `_0 = 99` → `UnwindResume`)**:
Verifies both:
1. After 2 steps (assert fail + cleanup stmt), `_0` holds `99` and execution is poised at `UnwindResume`;
2. Across the full 5-step body execution, `miriRunFuelAction` reaches `.undefinedBehavior` on root
   `UnwindResume` while preserving the committed cleanup transition! -/
theorem miriBodyExactWP_assert_cleanup_resume :
    let hooks := annealUnwindStepHooks bodyAssertCleanupResume.localDecls emptyLayoutTable
    let init := initMiriStateForBody bodyAssertCleanupResume emptyLayoutTable
    AnnealExactWP
      (ExactAction.seq (miriStepAction hooks ()) (miriStepAction hooks ()))
      (fun more mid => more = true ∧ activeLocal0Bits mid = some 99)
      (fun _ _ => False) init ∧
    AnnealExactWP (miriRunFuelAction hooks () 5)
      (fun _ _ => False)
      (fun err _ => match err with | .undefinedBehavior _ => True | _ => False) init :=
  ⟨⟨rfl, rfl⟩, trivial⟩

end StepAndBodyWP

/-! ## §4. Episode 2 LeanMiri Bridge Capstone & Silent Import / Bridge-Reality / Axiom Audit -/

/-- **Episode 2 LeanMiri Bridge Capstone (`LeanMiriSpec.ExactWpAndMemoryFrameLM`)**:
bundles §1 (`MemoryLemmas` → `AnnealExactWP` + universal LE/BE disjoint byte-range framing &
round-trips), §2 (`Std.Do`-free `TreeBorrowsWP` & `ProtectorReleaseWP` + multi-segment
committed-prefix error witnesses), and §3 (`Miri.Interpreter.Step.step` whole-body `ExactWP`
discharges & UB refutations on real `translateBody`-lowered `CapturedMir` bodies). -/
theorem ep2_lean_miri_exact_wp_and_memory_frame_capstone :
    (type_of% @allocReadScalarExactWP_iff) ∧
    (type_of% @allocWriteScalarExactWP_iff) ∧
    (type_of% @allocWriteBytesExactWP_iff) ∧
    (type_of% @allocWriteUninitExactWP_iff) ∧
    (type_of% @allocCopyExactWP_iff) ∧
    (type_of% @allocReadScalar_uninit_exactWP) ∧
    (type_of% @allocMapExtra_preserves_readScalar_exactWP) ∧
    (type_of% @allocWithExtra_preserves_readScalar_exactWP) ∧
    (type_of% @allocWriteScalar_then_readScalar_int_exactWP) ∧
    (type_of% @allocWriteScalar_then_readScalar_ptr_exactWP) ∧
    (type_of% @allocWriteScalar_disjoint_readScalar_frame_exactWP) ∧
    (type_of% @allocWriteUninit_disjoint_readScalar_frame_exactWP) ∧
    (type_of% @allocWriteBytes_disjoint_readScalar_frame_exactWP) ∧
    (type_of% @allocCopy_disjoint_readScalar_frame_exactWP) ∧
    (type_of% @allocEndian_le_vs_be_disjoint_frame_witness) ∧
    (type_of% @tbAccessExactWP_iff) ∧
    (type_of% @tbDeallocExactWP_iff) ∧
    (type_of% @tbDealloc_accessFailure_retains_tree) ∧
    (type_of% @protectorReleaseExactWP_iff) ∧
    (type_of% @protectorRelease_missingTag_exactWP) ∧
    (type_of% @tb_access_committed_prefix_on_error_witness) ∧
    (type_of% @protector_release_committed_prefix_on_error_witness) ∧
    (type_of% @miriStepExactWP_iff) ∧
    (type_of% @miriAllowedStepExactWP_iff) ∧
    (type_of% @miriBodyExactWP_iff) ∧
    (type_of% @miriBodyExactWP_loop_invariant) ∧
    (type_of% @miriBodyExactWP_negation_refutation) ∧
    (type_of% @miriBodyExactWP_normal_return) ∧
    (type_of% @miriBodyExactWP_unreachable_ub_refutation) ∧
    (type_of% @miriBodyExactWP_assert_pass_return) ∧
    (type_of% @miriBodyExactWP_assert_fail_terminate) ∧
    (type_of% @miriBodyExactWP_assert_cleanup_resume) :=
  ⟨@allocReadScalarExactWP_iff, @allocWriteScalarExactWP_iff, @allocWriteBytesExactWP_iff,
   @allocWriteUninitExactWP_iff, @allocCopyExactWP_iff, @allocReadScalar_uninit_exactWP,
   @allocMapExtra_preserves_readScalar_exactWP, @allocWithExtra_preserves_readScalar_exactWP,
   @allocWriteScalar_then_readScalar_int_exactWP, @allocWriteScalar_then_readScalar_ptr_exactWP,
   @allocWriteScalar_disjoint_readScalar_frame_exactWP,
   @allocWriteUninit_disjoint_readScalar_frame_exactWP,
   @allocWriteBytes_disjoint_readScalar_frame_exactWP,
   @allocCopy_disjoint_readScalar_frame_exactWP,
   @allocEndian_le_vs_be_disjoint_frame_witness,
   @tbAccessExactWP_iff, @tbDeallocExactWP_iff, @tbDealloc_accessFailure_retains_tree,
   @protectorReleaseExactWP_iff, @protectorRelease_missingTag_exactWP,
   @tb_access_committed_prefix_on_error_witness,
   @protector_release_committed_prefix_on_error_witness,
   @miriStepExactWP_iff, @miriAllowedStepExactWP_iff, @miriBodyExactWP_iff,
   @miriBodyExactWP_loop_invariant, @miriBodyExactWP_negation_refutation,
   @miriBodyExactWP_normal_return, @miriBodyExactWP_unreachable_ub_refutation,
   @miriBodyExactWP_assert_pass_return, @miriBodyExactWP_assert_fail_terminate,
   @miriBodyExactWP_assert_cleanup_resume⟩

section AxiomAndIsolationAudit
open Lean Elab Command

run_cmd do
  let env ← getEnv
  -- 1. Strict MiniRustSpec exclusion (transitive) and zero Std.Do / Std.Tactic.Do / Std.WP
  --    direct imports or constant references across all declarations in this module.
  for modName in env.header.moduleNames do
    if (`MiniRustSpec).isPrefixOf modName then
      throwError "import-isolation violation: {modName} must not be imported by LeanMiriSpec.ExactWpAndMemoryFrameLM"
  for imp in env.header.imports do
    if (`Std.Do).isPrefixOf imp.module || (`Std.Tactic.Do).isPrefixOf imp.module ||
        (`Std.WP).isPrefixOf imp.module then
      throwError "Std.Do isolation violation: direct import {imp.module} is forbidden"
  let ns := `LeanMiriSpec.ExactWpAndMemoryFrameLM
  for (c, info) in env.constants.map₂.toList do
    if ns.isPrefixOf c then
      let used := info.type.getUsedConstants ++
        match info with
        | .defnInfo v => v.value.getUsedConstants
        | .thmInfo v => v.value.getUsedConstants
        | _ => #[]
      for u in used do
        if (`Std.Do).isPrefixOf u || (`Std.Tactic.Do).isPrefixOf u || (`Std.WP).isPrefixOf u then
          throwError "Std.Do reference violation: {c} references {u}"
  -- 2. Bridge-reality audit: confirm our theorems reach REAL vendored Miri & Anneal ExactWP.
  let bridgeReq : List (Lean.Name × Lean.Name) :=
    [ (ns ++ `allocReadScalarExactWP_iff, `Miri.Memory.Allocation.readScalar),
      (ns ++ `allocWriteScalarExactWP_iff, `Miri.Memory.Allocation.writeScalar),
      (ns ++ `allocWriteBytesExactWP_iff, `Miri.Memory.Allocation.writeBytes),
      (ns ++ `allocWriteUninitExactWP_iff, `Miri.Memory.Allocation.writeUninit),
      (ns ++ `allocCopyExactWP_iff, `Miri.Memory.Allocation.copy),
      (ns ++ `tbAccessExactWP_iff, `Miri.TreeBorrows.BorrowTree.performBorrowAccessRange),
      (ns ++ `tbDeallocExactWP_iff, `Miri.TreeBorrows.BorrowTree.deallocateBorrowRange),
      (ns ++ `protectorReleaseExactWP_iff, `Miri.TreeBorrows.BorrowTree.releaseProtector),
      (ns ++ `miriStepExactWP_iff, `Miri.Interpreter.Step.step),
      (ns ++ `miriBodyExactWP_normal_return, `LeanMiriSpec.Correspondence.translateBody),
      (ns ++ `miriBodyExactWP_iff, `Anneal.ExactWpAndSmartCtors.AnnealExactWP) ]
  for (thm, req) in bridgeReq do
    let some ci := env.find? thm | throwError "bridge audit: {thm} missing"
    let mut seen : NameSet := {}
    let mut todo : Array Lean.Name := ci.type.getUsedConstants
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if seen.contains n then continue
      seen := seen.insert n
      if n == req then break
      if ns.isPrefixOf n then
        if let some (.defnInfo v) := env.find? n then
          todo := todo ++ v.value.getUsedConstants
    unless seen.contains req do
      throwError "shadow-evaluator audit: {thm} does not reach real {req}"
  -- 3. Standard-3-axiom purity audit (zero sorryAx, zero Lean.ofReduceBool, zero custom axioms).
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
  if theorems < 25 then
    throwError "axiom audit vacuous: only {theorems} theorems seen"

end AxiomAndIsolationAudit

end LeanMiriSpec.ExactWpAndMemoryFrameLM
