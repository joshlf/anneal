-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Trusted
import Anneal.Firewall
import Anneal.Framework.StepWp
import Anneal.CnfOrd.Worklist
import Anneal.ConjunctiveWp.WlpV2026
import Anneal.StepBound.StepBoundV2026

/-!
# Step-Chunked Multi-Frame Symbolic Execution over `V2026_06_01`
(`Anneal.MirSymExec.ChunkedCallV2026`)

Converges `google/zerocopy`'s step-chunked symbolic executor (`#4439`,
`Anneal.MirSymExec`) and multi-frame call executor (`#4450`,
`Anneal.MirSymExecCall`) onto the UNMODIFIED trusted
`Trusted.Rustc.V2026_06_01.MirSemantics` (`stepMirFn`, `evalStmt`,
`evalTerminator`, `pushCalleeFrame`, `writeReturnDestination`,
`evalDirectRustIntrinsic?`, `evalNonSelectIntrinsicCall`).

Design (zero shadow semantics):

1. **Symbolic values denote trusted values.** `SymScalar.eval env` is defined
   directly in terms of the trusted scalar kernels (`evalUncheckedAdd`,
   `evalWrappingMul`, `evalBswap`, `evalCtlz`, ...), so the symbolic result of
   an intrinsic agrees with the trusted result *by construction*; `SymCond`
   side conditions (`noOverflowAdd`, `divSafe`, `shiftInBounds`, `nonzero`,
   `assertHolds`, `switchBranchEq`, ...) carry explicit arithmetic denotations
   that are proved to imply trusted definedness.
2. **Every env-independent decision is the trusted decision.** The symbolic
   stepper (`symProgStep`) consults exactly the same trusted functions on the
   same env-independent data as `stepMirFn` (`get?` on `basicBlocks`,
   `lookupCallee`, `classifyRustIntrinsic?`, `resolveIntrinsicIsSigned`,
   `extractCalleeDefPath?`, `evalConstValue`, `operandTy`, `placeTyResolved`),
   and only scalar *bits* remain symbolic. Anything outside the supported
   fragment fails closed (`SymStepRes.stuck`).
3. **Multi-frame state mirrors `MachineState`.** `SymProg` carries the active
   `SymFrame`, the `SymSaved` caller stack (concretized to trusted
   `SavedCallerFrame`s), and `Memory.activeCallee`; `SymProg.toMachineState`
   rebuilds the exact trusted `MachineState` (`Memory.callees`,
   `Memory.callStack`, empty borrow / protector tables).
4. **Chunked runner.** `symProgRunSteps` is defined by `@Nat.rec`, so explicit
   checkpoints reduce by `rfl`; `symRunChunks` threads a list of chunk sizes.
   Soundness (`symProgStep_sound`, `symProgRunSteps_sound`,
   `symProgRunSteps_ret_sound`, `symRunChunks_sound`) is proved once,
   generically, against `stepMirFn` / `v2026Step` and lifted to
   `StepsToV2026`, `StepStageCut`, `ReachesDoneWithinV2026`,
   `ExecWithinStepsV2026`, `MirWpConverges`, `MirNoUBTree`,
   `VerificationResult`, and `StatefulVerificationResult`.
-/

namespace Anneal.MirSymExec.ChunkedCallV2026

open Trusted.Effect
open Trusted.Sequence
open Trusted.VerificationResult
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.MirFuelFree
open Anneal.Framework.StepWp
open Anneal.ConjunctiveWp
open Anneal.StepBound
open Anneal.Rustc.V2026_06_01.SymbolicEval (mirNormalPost)

/-! ## Part I: Symbolic Scalars, Values, Slots, and Side Conditions -/

/-- Symbolic environment: symbolic input `id` denotes raw bits `env id`. -/
abbrev SymEnv := Nat → Nat

/-- Bit-manipulation intrinsics (`core::intrinsics::{bswap, bitreverse, ctlz,
cttz, ctpop, ctlz_nonzero, cttz_nonzero}`). -/
inductive SymBitKind : Type where
  | bswap | bitreverse | ctlz | cttz | ctpop | ctlzNonzero | cttzNonzero

/-- Modular arithmetic intrinsics (`core::intrinsics::wrapping_{add,sub,mul}`). -/
inductive SymWrapKind : Type where
  | add | sub | mul

/-- Saturating arithmetic intrinsics (`core::intrinsics::saturating_{add,sub}`). -/
inductive SymSatKind : Type where
  | add | sub

/-- UB-guarded arithmetic intrinsics (`core::intrinsics::unchecked_*`). -/
inductive SymUncheckedKind : Type where
  | add | sub | mul | div | rem | shl | shr

/-- Raw width-parametric symbolic scalar expression trees. Widths live in the
`ScalarInt.sizeBytes` of every denotation; signedness is recorded on each
operator node exactly as resolved by the trusted intrinsic dispatcher. -/
inductive SymNode : Type where
  /-- Symbolic input `id` of byte width `width`: denotes `⟨env id, width⟩`. -/
  | var (id : Nat) (width : Nat)
  /-- Concrete scalar constant. -/
  | const (sc : ScalarInt)
  /-- `wrapping_{add,sub,mul}`. -/
  | wrappingOp (k : SymWrapKind) (a b : SymNode)
  /-- `saturating_{add,sub}` with resolved signedness. -/
  | saturatingOp (k : SymSatKind) (signed : Bool) (a b : SymNode)
  /-- `unchecked_*` with resolved lhs / rhs signedness. -/
  | uncheckedOp (k : SymUncheckedKind) (lhsSigned rhsSigned : Bool) (a b : SymNode)
  /-- `bswap` / `bitreverse` / `ctlz` / `cttz` / `ctpop` / `*_nonzero`. -/
  | bitIntrinsic (k : SymBitKind) (a : SymNode)

/-- Default scalar used only when a trusted kernel is undefined; every
symbolic step that produces such a node records a `SymCond` guaranteeing
definedness, so the default is never observed under `condsHold`. -/
def symDefaultScalar : ScalarInt := ⟨0, 0⟩

/-- Trusted bit-intrinsic kernels (exactly as called by
`evalNonSelectIntrinsicCall`, default `retBytes`). -/
def symBitEval : SymBitKind → ScalarInt → Option ScalarInt
  | .bswap, x => evalBswap x
  | .bitreverse, x => evalBitreverse x
  | .ctlz, x => evalCtlz x
  | .cttz, x => evalCttz x
  | .ctpop, x => evalCtpop x
  | .ctlzNonzero, x => evalCtlzNonzero x
  | .cttzNonzero, x => evalCttzNonzero x

/-- Trusted wrapping kernels. -/
def symWrapEval : SymWrapKind → ScalarInt → ScalarInt → Option ScalarInt
  | .add, x, y => evalWrappingAdd x y
  | .sub, x, y => evalWrappingSub x y
  | .mul, x, y => evalWrappingMul x y

/-- Trusted saturating kernels. -/
def symSatEval : SymSatKind → Bool → ScalarInt → ScalarInt → Option ScalarInt
  | .add, s, x, y => evalSaturatingAdd x y s
  | .sub, s, x, y => evalSaturatingSub x y s

/-- Trusted unchecked kernels (`shl` uses only the rhs signedness, `shr` both). -/
def symUncheckedEval :
    SymUncheckedKind → Bool → Bool → ScalarInt → ScalarInt → Option ScalarInt
  | .add, s, _, x, y => evalUncheckedAdd x y s
  | .sub, s, _, x, y => evalUncheckedSub x y s
  | .mul, s, _, x, y => evalUncheckedMul x y s
  | .div, s, _, x, y => evalUncheckedDiv x y s
  | .rem, s, _, x, y => evalUncheckedRem x y s
  | .shl, _, rs, x, y => evalUncheckedShl x y rs
  | .shr, ls, rs, x, y => evalUncheckedShr x y ls rs

/-- Fuel-bounded denotation of a raw tree by the trusted kernels. Defined by
`@Nat.rec`: no equation-compiler recursion, so the compiler emits no unsafe
recursive auxiliary. -/
def symNodeEvalFuel (env : SymEnv) (fuel : Nat) : SymNode → ScalarInt :=
  @Nat.rec (fun _ => SymNode → ScalarInt)
    (fun _ => symDefaultScalar)
    (fun _ ih e =>
      match e with
      | .var id w => ⟨env id, w⟩
      | .const sc => sc
      | .wrappingOp k a b => (symWrapEval k (ih a) (ih b)).getD symDefaultScalar
      | .saturatingOp k s a b => (symSatEval k s (ih a) (ih b)).getD symDefaultScalar
      | .uncheckedOp k ls rs a b =>
        (symUncheckedEval k ls rs (ih a) (ih b)).getD symDefaultScalar
      | .bitIntrinsic k a => (symBitEval k (ih a)).getD symDefaultScalar)
    fuel

/-- `t` has depth at most `n` (fuel `n` suffices to evaluate it). -/
inductive SymNode.DepthLE : SymNode → Nat → Prop where
  | var {id w n : Nat} : SymNode.DepthLE (.var id w) (n + 1)
  | const {sc : ScalarInt} {n : Nat} : SymNode.DepthLE (.const sc) (n + 1)
  | wrappingOp {k : SymWrapKind} {a b : SymNode} {n : Nat} :
      SymNode.DepthLE a n → SymNode.DepthLE b n → SymNode.DepthLE (.wrappingOp k a b) (n + 1)
  | saturatingOp {k : SymSatKind} {s : Bool} {a b : SymNode} {n : Nat} :
      SymNode.DepthLE a n → SymNode.DepthLE b n →
        SymNode.DepthLE (.saturatingOp k s a b) (n + 1)
  | uncheckedOp {k : SymUncheckedKind} {ls rs : Bool} {a b : SymNode} {n : Nat} :
      SymNode.DepthLE a n → SymNode.DepthLE b n →
        SymNode.DepthLE (.uncheckedOp k ls rs a b) (n + 1)
  | bitIntrinsic {k : SymBitKind} {a : SymNode} {n : Nat} :
      SymNode.DepthLE a n → SymNode.DepthLE (.bitIntrinsic k a) (n + 1)

theorem SymNode.DepthLE.mono {t : SymNode} {n : Nat} (h : t.DepthLE n) :
    ∀ {m : Nat}, n ≤ m → t.DepthLE m := by
  induction h with
  | var =>
    intro m hm
    cases m with
    | zero => exact absurd hm (Nat.not_succ_le_zero _)
    | succ m => exact .var
  | const =>
    intro m hm
    cases m with
    | zero => exact absurd hm (Nat.not_succ_le_zero _)
    | succ m => exact .const
  | wrappingOp _ _ iha ihb =>
    intro m hm
    cases m with
    | zero => exact absurd hm (Nat.not_succ_le_zero _)
    | succ m => exact .wrappingOp (iha (Nat.le_of_succ_le_succ hm)) (ihb (Nat.le_of_succ_le_succ hm))
  | saturatingOp _ _ iha ihb =>
    intro m hm
    cases m with
    | zero => exact absurd hm (Nat.not_succ_le_zero _)
    | succ m =>
      exact .saturatingOp (iha (Nat.le_of_succ_le_succ hm)) (ihb (Nat.le_of_succ_le_succ hm))
  | uncheckedOp _ _ iha ihb =>
    intro m hm
    cases m with
    | zero => exact absurd hm (Nat.not_succ_le_zero _)
    | succ m =>
      exact .uncheckedOp (iha (Nat.le_of_succ_le_succ hm)) (ihb (Nat.le_of_succ_le_succ hm))
  | bitIntrinsic _ iha =>
    intro m hm
    cases m with
    | zero => exact absurd hm (Nat.not_succ_le_zero _)
    | succ m => exact .bitIntrinsic (iha (Nat.le_of_succ_le_succ hm))

/-- Fuel stability: any fuel above a depth bound yields the same denotation. -/
theorem symNodeEvalFuel_stable (env : SymEnv) {t : SymNode} {n : Nat} (h : t.DepthLE n) :
    ∀ {m : Nat}, n ≤ m → symNodeEvalFuel env m t = symNodeEvalFuel env n t := by
  induction h with
  | var =>
    intro m hm
    cases m with
    | zero => exact absurd hm (Nat.not_succ_le_zero _)
    | succ m => rfl
  | const =>
    intro m hm
    cases m with
    | zero => exact absurd hm (Nat.not_succ_le_zero _)
    | succ m => rfl
  | wrappingOp _ _ iha ihb =>
    intro m hm
    cases m with
    | zero => exact absurd hm (Nat.not_succ_le_zero _)
    | succ m =>
      show (symWrapEval _ (symNodeEvalFuel env m _) (symNodeEvalFuel env m _)).getD _ =
        (symWrapEval _ (symNodeEvalFuel env _ _) (symNodeEvalFuel env _ _)).getD _
      rw [iha (Nat.le_of_succ_le_succ hm), ihb (Nat.le_of_succ_le_succ hm)]
  | saturatingOp _ _ iha ihb =>
    intro m hm
    cases m with
    | zero => exact absurd hm (Nat.not_succ_le_zero _)
    | succ m =>
      show (symSatEval _ _ (symNodeEvalFuel env m _) (symNodeEvalFuel env m _)).getD _ =
        (symSatEval _ _ (symNodeEvalFuel env _ _) (symNodeEvalFuel env _ _)).getD _
      rw [iha (Nat.le_of_succ_le_succ hm), ihb (Nat.le_of_succ_le_succ hm)]
  | uncheckedOp _ _ iha ihb =>
    intro m hm
    cases m with
    | zero => exact absurd hm (Nat.not_succ_le_zero _)
    | succ m =>
      show (symUncheckedEval _ _ _ (symNodeEvalFuel env m _) (symNodeEvalFuel env m _)).getD _ =
        (symUncheckedEval _ _ _ (symNodeEvalFuel env _ _) (symNodeEvalFuel env _ _)).getD _
      rw [iha (Nat.le_of_succ_le_succ hm), ihb (Nat.le_of_succ_le_succ hm)]
  | bitIntrinsic _ iha =>
    intro m hm
    cases m with
    | zero => exact absurd hm (Nat.not_succ_le_zero _)
    | succ m =>
      show (symBitEval _ (symNodeEvalFuel env m _)).getD _ =
        (symBitEval _ (symNodeEvalFuel env _ _)).getD _
      rw [iha (Nat.le_of_succ_le_succ hm)]

/-- Well-formed symbolic scalar: a raw tree bundled with a sufficient fuel. -/
structure SymScalar : Type where
  node : SymNode
  fuel : Nat
  wf : node.DepthLE fuel

/-- Denotation of a symbolic scalar under `env`, by the trusted kernels. -/
def SymScalar.eval (env : SymEnv) (s : SymScalar) : ScalarInt :=
  symNodeEvalFuel env s.fuel s.node

/-- Symbolic input `id` of byte width `w`. -/
def SymScalar.var (id w : Nat) : SymScalar := ⟨.var id w, 1, .var⟩

/-- Concrete scalar constant. -/
def SymScalar.const (sc : ScalarInt) : SymScalar := ⟨.const sc, 1, .const⟩

/-- `wrapping_{add,sub,mul}` node. -/
def SymScalar.wrappingOp (k : SymWrapKind) (a b : SymScalar) : SymScalar :=
  ⟨.wrappingOp k a.node b.node, Nat.max a.fuel b.fuel + 1,
    .wrappingOp (a.wf.mono (Nat.le_max_left _ _)) (b.wf.mono (Nat.le_max_right _ _))⟩

/-- `saturating_{add,sub}` node. -/
def SymScalar.saturatingOp (k : SymSatKind) (s : Bool) (a b : SymScalar) : SymScalar :=
  ⟨.saturatingOp k s a.node b.node, Nat.max a.fuel b.fuel + 1,
    .saturatingOp (a.wf.mono (Nat.le_max_left _ _)) (b.wf.mono (Nat.le_max_right _ _))⟩

/-- `unchecked_*` node. -/
def SymScalar.uncheckedOp (k : SymUncheckedKind) (ls rs : Bool) (a b : SymScalar) :
    SymScalar :=
  ⟨.uncheckedOp k ls rs a.node b.node, Nat.max a.fuel b.fuel + 1,
    .uncheckedOp (a.wf.mono (Nat.le_max_left _ _)) (b.wf.mono (Nat.le_max_right _ _))⟩

/-- Bit-intrinsic node. -/
def SymScalar.bitIntrinsic (k : SymBitKind) (a : SymScalar) : SymScalar :=
  ⟨.bitIntrinsic k a.node, a.fuel + 1, .bitIntrinsic a.wf⟩

theorem SymScalar.eval_var (env : SymEnv) (id w : Nat) :
    (SymScalar.var id w).eval env = ⟨env id, w⟩ := rfl

theorem SymScalar.eval_const (env : SymEnv) (sc : ScalarInt) :
    (SymScalar.const sc).eval env = sc := rfl

theorem SymScalar.eval_wrappingOp (env : SymEnv) (k : SymWrapKind) (a b : SymScalar) :
    (SymScalar.wrappingOp k a b).eval env =
      (symWrapEval k (a.eval env) (b.eval env)).getD symDefaultScalar := by
  show (symWrapEval k (symNodeEvalFuel env (Nat.max a.fuel b.fuel) a.node)
      (symNodeEvalFuel env (Nat.max a.fuel b.fuel) b.node)).getD symDefaultScalar = _
  rw [symNodeEvalFuel_stable env a.wf (Nat.le_max_left _ _),
    symNodeEvalFuel_stable env b.wf (Nat.le_max_right _ _)]
  rfl

theorem SymScalar.eval_saturatingOp (env : SymEnv) (k : SymSatKind) (s : Bool)
    (a b : SymScalar) :
    (SymScalar.saturatingOp k s a b).eval env =
      (symSatEval k s (a.eval env) (b.eval env)).getD symDefaultScalar := by
  show (symSatEval k s (symNodeEvalFuel env (Nat.max a.fuel b.fuel) a.node)
      (symNodeEvalFuel env (Nat.max a.fuel b.fuel) b.node)).getD symDefaultScalar = _
  rw [symNodeEvalFuel_stable env a.wf (Nat.le_max_left _ _),
    symNodeEvalFuel_stable env b.wf (Nat.le_max_right _ _)]
  rfl

theorem SymScalar.eval_uncheckedOp (env : SymEnv) (k : SymUncheckedKind) (ls rs : Bool)
    (a b : SymScalar) :
    (SymScalar.uncheckedOp k ls rs a b).eval env =
      (symUncheckedEval k ls rs (a.eval env) (b.eval env)).getD symDefaultScalar := by
  show (symUncheckedEval k ls rs (symNodeEvalFuel env (Nat.max a.fuel b.fuel) a.node)
      (symNodeEvalFuel env (Nat.max a.fuel b.fuel) b.node)).getD symDefaultScalar = _
  rw [symNodeEvalFuel_stable env a.wf (Nat.le_max_left _ _),
    symNodeEvalFuel_stable env b.wf (Nat.le_max_right _ _)]
  rfl

theorem SymScalar.eval_bitIntrinsic (env : SymEnv) (k : SymBitKind) (a : SymScalar) :
    (SymScalar.bitIntrinsic k a).eval env = (symBitEval k (a.eval env)).getD symDefaultScalar :=
  rfl

/-- Syntactic constant view of a symbolic scalar. -/
def SymScalar.asConst? (s : SymScalar) : Option ScalarInt :=
  match s.node with
  | .const sc => some sc
  | _ => none

/-- Symbolic runtime values. -/
inductive SymVal : Type where
  | unit : SymVal
  | scalar (s : SymScalar) : SymVal
  | aggregate (variantIdx : VariantIdx) (fields : List SymScalar) : SymVal
  | uninit : SymVal
  /-- An env-independent trusted value (e.g. evaluated constants). -/
  | concrete (v : Value) : SymVal

/-- Field-wise denotation of scalar aggregate fields. -/
def symFieldsEval (env : SymEnv) (fs : List SymScalar) : List Value :=
  fs.map (fun a => .scalar (a.eval env))

/-- Denotation of a symbolic value. -/
def SymVal.eval (env : SymEnv) : SymVal → Value
  | .unit => .unit
  | .scalar s => .scalar (s.eval env)
  | .aggregate idx fs => .aggregate idx (symFieldsEval env fs)
  | .uninit => .uninit
  | .concrete v => v

/-- Env-independent `valueContainsUninit`. -/
def SymVal.containsUninit : SymVal → Bool
  | .unit => false
  | .scalar _ => false
  | .aggregate _ _ => false
  | .uninit => true
  | .concrete v => valueContainsUninit v

/-- Scalar view of a symbolic value (constants become `SymScalar.const`). -/
def SymVal.asScalar? : SymVal → Option SymScalar
  | .scalar s => some s
  | .concrete (.scalar sc) => some (.const sc)
  | _ => none

/-- Symbolic local slots. -/
inductive SymSlot : Type where
  | dead : SymSlot
  | uninit : SymSlot
  | init (v : SymVal) : SymSlot

/-- Denotation of a symbolic slot. -/
def SymSlot.eval (env : SymEnv) : SymSlot → LocalSlot
  | .dead => .dead
  | .uninit => .uninit
  | .init v => .init (v.eval env)

/-- Denotation of a list of symbolic slots. -/
def symSlotsEval (env : SymEnv) (l : List SymSlot) : List LocalSlot :=
  l.map (SymSlot.eval env)

/-- Denotation of a list of symbolic values. -/
def symValsEval (env : SymEnv) (l : List SymVal) : List Value :=
  l.map (SymVal.eval env)

/-- Explicit symbolic side conditions recorded by the symbolic executor. -/
inductive SymCond : Type where
  /-- `unchecked_add`: no unsigned / signed overflow at the common width. -/
  | noOverflowAdd (signed : Bool) (a b : SymScalar)
  /-- `unchecked_sub`: no unsigned underflow / signed overflow. -/
  | noOverflowSub (signed : Bool) (a b : SymScalar)
  /-- `unchecked_mul`: no unsigned / signed overflow. -/
  | noOverflowMul (signed : Bool) (a b : SymScalar)
  /-- `unchecked_div`: nonzero divisor (and no signed `MIN / -1`). -/
  | divSafe (signed : Bool) (a b : SymScalar)
  /-- `unchecked_rem`: nonzero divisor (and no signed `MIN % -1`). -/
  | remSafe (signed : Bool) (a b : SymScalar)
  /-- `unchecked_shl` / `unchecked_shr`: shift amount in `[0, 8 * width)`. -/
  | shiftInBounds (rhsSigned : Bool) (a b : SymScalar)
  /-- Equal nonzero operand widths (wrapping / saturating intrinsics). -/
  | widthsMatch (a b : SymScalar)
  /-- Nonzero operand width (bit intrinsics). -/
  | widthNonzero (a : SymScalar)
  /-- `ctlz_nonzero` / `cttz_nonzero`: nonzero width and nonzero operand. -/
  | nonzero (a : SymScalar)
  /-- `Assert { cond, expected }` succeeds. -/
  | assertHolds (c : SymScalar) (expected : Bool)
  /-- `SwitchInt` discriminant equals branch value `v` and none of the earlier
  branch values `prior` (first-match semantics). -/
  | switchBranchEq (d : SymScalar) (v : Nat) (prior : List Nat)
  /-- `SwitchInt` discriminant matches none of `vs` (otherwise edge). -/
  | switchBranchOtherwise (d : SymScalar) (vs : List Nat)

/-- Canonical (wrapped) bits of a scalar at its own width. -/
def scBits (x : ScalarInt) : Nat :=
  wrapScalarBits x.bits (scalarModulus x.sizeBytes)

/-- Canonical bits of `y` reduced at the width of `x`. -/
def scBitsAt (x y : ScalarInt) : Nat :=
  wrapScalarBits y.bits (scalarModulus x.sizeBytes)

/-- Common-width precondition shared by all binary intrinsics. -/
def ScWidthsOk (x y : ScalarInt) : Prop :=
  x.sizeBytes ≠ 0 ∧ x.sizeBytes = y.sizeBytes

/-- Signed-minimum `/ -1` exclusion at width `x.sizeBytes`. -/
def ScNotMinNegOne (x y : ScalarInt) : Prop :=
  ¬ (scBits x = scalarPow2 (Nat.sub (Nat.mul x.sizeBytes 8) 1) ∧
      scBitsAt x y = Nat.sub (scalarModulus x.sizeBytes) 1)

/-- Denotation of a side condition. -/
def SymCond.holds (env : SymEnv) : SymCond → Prop
  | .noOverflowAdd s a b =>
    let x := a.eval env
    let y := b.eval env
    ScWidthsOk x y ∧
      (match s with
       | false => scBits x + scBitsAt x y < scalarModulus x.sizeBytes
       | true => signedOverflowAdd (scBits x) (scBitsAt x y) x.sizeBytes = false)
  | .noOverflowSub s a b =>
    let x := a.eval env
    let y := b.eval env
    ScWidthsOk x y ∧
      (match s with
       | false => scBitsAt x y ≤ scBits x
       | true => signedOverflowSub (scBits x) (scBitsAt x y) x.sizeBytes = false)
  | .noOverflowMul s a b =>
    let x := a.eval env
    let y := b.eval env
    ScWidthsOk x y ∧
      (match s with
       | false => scBits x * scBitsAt x y < scalarModulus x.sizeBytes
       | true => signedOverflowMul (scBits x) (scBitsAt x y) x.sizeBytes = false)
  | .divSafe s a b =>
    let x := a.eval env
    let y := b.eval env
    ScWidthsOk x y ∧ scBitsAt x y ≠ 0 ∧
      (match s with
       | false => True
       | true => ScNotMinNegOne x y)
  | .remSafe s a b =>
    let x := a.eval env
    let y := b.eval env
    ScWidthsOk x y ∧ scBitsAt x y ≠ 0 ∧
      (match s with
       | false => True
       | true => ScNotMinNegOne x y)
  | .shiftInBounds rs a b =>
    let x := a.eval env
    let y := b.eval env
    x.sizeBytes ≠ 0 ∧ y.sizeBytes ≠ 0 ∧
      (rs && isSignedNegative (scBits y) y.sizeBytes) = false ∧
      scBits y < Nat.mul x.sizeBytes 8
  | .widthsMatch a b => ScWidthsOk (a.eval env) (b.eval env)
  | .widthNonzero a => (a.eval env).sizeBytes ≠ 0
  | .nonzero a => (a.eval env).sizeBytes ≠ 0 ∧ scBits (a.eval env) ≠ 0
  | .assertHolds c expected =>
    (c.eval env).bits = (match expected with | true => 1 | false => 0)
  | .switchBranchEq d v prior =>
    (d.eval env).bits = v ∧ ∀ u, u ∈ prior → (d.eval env).bits ≠ u
  | .switchBranchOtherwise d vs => ∀ u, u ∈ vs → (d.eval env).bits ≠ u

/-- All side conditions hold. -/
def condsHold (env : SymEnv) (cs : List SymCond) : Prop :=
  cs.foldr (fun c acc => c.holds env ∧ acc) True

/-! ## Part II: Multi-Frame Symbolic Programs -/

/-- Symbolic active frame (mirrors `StackFrame`). -/
structure SymFrame : Type where
  blockIdx : BasicBlockIdx
  stmtIdx : Nat
  locals : List SymSlot

/-- Denotation of a symbolic frame. -/
def SymFrame.eval (env : SymEnv) (f : SymFrame) : StackFrame :=
  { blockIdx := f.blockIdx, stmtIdx := f.stmtIdx, locals := symSlotsEval env f.locals }

/-- Symbolic saved caller frame (mirrors the `SavedCallerFrame` pushed by
`pushCalleeFrame` under empty protector tables). -/
structure SymSaved : Type where
  callerBody : CapturedMir
  frame : SymFrame
  destination : Place
  returnTarget : BasicBlockIdx
  returnUnwind : UnwindAction

/-- Denotation of a saved caller frame. -/
def SymSaved.eval (env : SymEnv) (c : SymSaved) : SavedCallerFrame :=
  { callerBody := c.callerBody
    frame := c.frame.eval env
    destination := c.destination
    returnTarget := c.returnTarget
    calleeProtectors := []
    returnUnwind := c.returnUnwind
    isDiverging := false }

/-- Denotation of a symbolic call stack. -/
def symStackEval (env : SymEnv) (l : List SymSaved) : List SavedCallerFrame :=
  l.map (SymSaved.eval env)

/-- Static configuration: root body and linked inline callees. -/
structure SymConfig : Type where
  body : CapturedMir
  callees : List CapturedMir

/-- Multi-frame symbolic program state (mirrors `MachineState`). -/
structure SymProg : Type where
  frame : SymFrame
  stack : List SymSaved
  active : Option CapturedMir

/-- Trusted memory denoted by a symbolic program. -/
def SymProg.toMemory (cfg : SymConfig) (env : SymEnv) (p : SymProg) : Memory :=
  { nextAllocId := length cfg.body.allocations
    globals := cfg.body.allocations
    borrows := []
    nextTag := 1
    callees := cfg.callees
    callStack := symStackEval env p.stack
    activeCallee := p.active
    traitImpls := cfg.body.traitImpls }

/-- Trusted machine state denoted by a symbolic program. -/
def SymProg.toMachineState (cfg : SymConfig) (env : SymEnv) (p : SymProg) :
    MachineState :=
  { frame := p.frame.eval env, memory := p.toMemory cfg env }

/-- Symbolic counterpart of `initLocalsAux` (by `List.foldr`). -/
def symInitLocalsAux (n : Nat) (decls : List LocalDecl) (args : List SymVal) : List SymSlot :=
  decls.foldr
    (fun _ ih n args =>
      match n, args with
      | .zero, args => .uninit :: ih 1 args
      | .succ idx, arg :: restArgs => .init arg :: ih (Nat.add idx 1) restArgs
      | .succ idx, [] => .dead :: ih (Nat.add idx 1) [])
    (fun _ _ => []) n args

/-- Symbolic entry state of `cfg.body` on symbolic arguments `args`. -/
def symProgEntry (cfg : SymConfig) (args : List SymVal) : SymProg :=
  { frame := { blockIdx := 0, stmtIdx := 0
               locals := symInitLocalsAux 0 cfg.body.localDecls args }
    stack := []
    active := none }

/-! ## Part III: Single-Step Symbolic Engine -/

/-- Result of one symbolic step. -/
inductive SymStepRes : Type where
  /-- Advance to `next` under side conditions `conds`. -/
  | step (next : SymProg) (conds : List SymCond)
  /-- Root-frame normal return of `val` from `fin` under `conds`. -/
  | ret (val : SymVal) (fin : SymProg) (conds : List SymCond)
  /-- Symbolic `SwitchInt` fork: each alternative is guarded by its edge
  condition, with `conds` accumulated before the fork. -/
  | branch (alts : List (SymCond × SymProg)) (conds : List SymCond)
  /-- Outside the supported fragment (fail closed). -/
  | stuck

/-- Symbolic `evalOperand` for bare locals (`copy` / `move`) and evaluated
non-indirect constants. -/
def symOperand (globals : List CapturedAllocation) (layouts : LayoutTable)
    (locals : List SymSlot) : Operand → Option (SymVal × List SymSlot)
  | .copy p =>
    match p.projection with
    | [] =>
      match get? locals p.local_ with
      | some (.init v) =>
        match v.containsUninit with
        | false => some (v, locals)
        | true => none
      | _ => none
    | _ :: _ => none
  | .move p =>
    match p.projection with
    | [] =>
      match get? locals p.local_ with
      | some (.init v) =>
        match v.containsUninit with
        | false =>
          match set? locals p.local_ .uninit with
          | some locals' => some (v, locals')
          | none => none
        | true => none
      | _ => none
    | _ :: _ => none
  | .constant c =>
    match c.val with
    | .scalar cs =>
      match evalConstValue (.scalar cs) c.ty globals layouts with
      | some v => some (.concrete v, locals)
      | none => none
    | .zeroSized =>
      match evalConstValue .zeroSized c.ty globals layouts with
      | some v => some (.concrete v, locals)
      | none => none
    | _ => none

/-- Symbolic `evalOperandsWithBodyCast` over `symOperand` (by `List.foldr`). -/
def symOperands (globals : List CapturedAllocation) (layouts : LayoutTable)
    (locals : List SymSlot) (ops : List Operand) : Option (List SymVal × List SymSlot) :=
  ops.foldr
    (fun op ih locals =>
      match symOperand globals layouts locals op with
      | some (v, locals₁) =>
        match ih locals₁ with
        | some (vs, locals₂) => some (v :: vs, locals₂)
        | none => none
      | none => none)
    (fun locals => some ([], locals)) locals

/-- Env-independent sufficient condition for `validateLoadedValue` (types
other than `bool` / `char` impose no bit-validity check). -/
def loadedValueStaticOk (layouts : LayoutTable) (decls : List LocalDecl)
    (op : Operand) : Bool :=
  match op with
  | .constant _ => true
  | .copy _ | .move _ =>
    match operandTy decls layouts op with
    | some ty =>
      match ty.kind with
      | .bool => false
      | .char => false
      | _ => true
    | none => true

/-- Symbolic `evalRvalue` (A0 fragment: `Rvalue.use`). -/
def symRvalue (globals : List CapturedAllocation) (layouts : LayoutTable)
    (decls : List LocalDecl) (locals : List SymSlot) :
    Rvalue → Option (SymVal × List SymSlot × List SymCond)
  | .use op =>
    match symOperand globals layouts locals op with
    | some (v, locals') =>
      match loadedValueStaticOk layouts decls op with
      | true => some (v, locals', [])
      | false => none
    | none => none
  | _ => none

/-- Advance the statement index of a symbolic frame with new locals. -/
def SymFrame.advance (f : SymFrame) (locals' : List SymSlot) : SymFrame :=
  { f with stmtIdx := Nat.add f.stmtIdx 1, locals := locals' }

/-- Symbolic `evalStmt` under empty borrow / protector tables. -/
def symStmt (globals : List CapturedAllocation) (body : CapturedMir)
    (f : SymFrame) (stmt : Statement) : Option (SymFrame × List SymCond) :=
  match stmt.kind with
  | .nop => some (f.advance f.locals, [])
  | .storageLive loc =>
    match get? f.locals loc with
    | some _ =>
      match set? f.locals loc .uninit with
      | some locals' => some (f.advance locals', [])
      | none => none
    | none => none
  | .storageDead loc =>
    match get? f.locals loc with
    | some _ =>
      match set? f.locals loc .dead with
      | some locals' => some (f.advance locals', [])
      | none => none
    | none => none
  | .assign dst rv =>
    match dst.projection with
    | [] =>
      match symRvalue globals body.layouts body.localDecls f.locals rv with
      | some (v, locals₁, cs) =>
        match get? locals₁ dst.local_ with
        | some .dead => none
        | some _ =>
          match set? locals₁ dst.local_ (.init v) with
          | some locals₂ => some (f.advance locals₂, cs)
          | none => none
        | none => none
      | none => none
    | _ :: _ => none
  | _ => none

/-- Unary intrinsic shape: exactly one scalar argument. -/
def symUn (args : List SymVal) (k : SymBitKind) (mk : SymScalar → List SymCond) :
    Option (SymScalar × List SymCond) :=
  match args with
  | [a] =>
    match a.asScalar? with
    | some x => some (.bitIntrinsic k x, mk x)
    | none => none
  | _ => none

/-- Binary intrinsic shape: exactly two scalar arguments. -/
def symBin (args : List SymVal) (f : SymScalar → SymScalar → SymScalar)
    (mk : SymScalar → SymScalar → List SymCond) : Option (SymScalar × List SymCond) :=
  match args with
  | [a, b] =>
    match a.asScalar?, b.asScalar? with
    | some x, some y => some (f x y, mk x y)
    | _, _ => none
  | _ => none

/-- Symbolic intrinsic semantics for value-returning `RustIntrinsicKind`s:
result expression plus the exact side conditions guaranteeing trusted
definedness. -/
def symIntrinsic (kind : RustIntrinsicKind) (target : ResolvedCallTarget)
    (decls : List LocalDecl) (layouts : LayoutTable) (argOps : List Operand)
    (args : List SymVal) : Option (SymScalar × List SymCond) :=
    match kind with
    | .ubChecks =>
      match args with
      | [] => some (.const ⟨1, 1⟩, [])
      | _ => none
    | .ctlz => symUn args .ctlz (fun x => [.widthNonzero x])
    | .cttz => symUn args .cttz (fun x => [.widthNonzero x])
    | .ctpop => symUn args .ctpop (fun x => [.widthNonzero x])
    | .bswap => symUn args .bswap (fun x => [.widthNonzero x])
    | .bitreverse => symUn args .bitreverse (fun x => [.widthNonzero x])
    | .ctlzNonzero => symUn args .ctlzNonzero (fun x => [.nonzero x])
    | .cttzNonzero => symUn args .cttzNonzero (fun x => [.nonzero x])
    | .wrappingAdd => symBin args (.wrappingOp .add) (fun x y => [.widthsMatch x y])
    | .wrappingSub => symBin args (.wrappingOp .sub) (fun x y => [.widthsMatch x y])
    | .wrappingMul => symBin args (.wrappingOp .mul) (fun x y => [.widthsMatch x y])
    | .saturatingAdd =>
      match resolveIntrinsicIsSigned target decls layouts argOps with
      | some s => symBin args (.saturatingOp .add s) (fun x y => [.widthsMatch x y])
      | none => none
    | .saturatingSub =>
      match resolveIntrinsicIsSigned target decls layouts argOps with
      | some s => symBin args (.saturatingOp .sub s) (fun x y => [.widthsMatch x y])
      | none => none
    | .uncheckedAdd =>
      match resolveIntrinsicIsSigned target decls layouts argOps with
      | some s => symBin args (.uncheckedOp .add s false) (fun x y => [.noOverflowAdd s x y])
      | none => none
    | .uncheckedSub =>
      match resolveIntrinsicIsSigned target decls layouts argOps with
      | some s => symBin args (.uncheckedOp .sub s false) (fun x y => [.noOverflowSub s x y])
      | none => none
    | .uncheckedMul =>
      match resolveIntrinsicIsSigned target decls layouts argOps with
      | some s => symBin args (.uncheckedOp .mul s false) (fun x y => [.noOverflowMul s x y])
      | none => none
    | .uncheckedDiv =>
      match resolveIntrinsicIsSigned target decls layouts argOps with
      | some s => symBin args (.uncheckedOp .div s false) (fun x y => [.divSafe s x y])
      | none => none
    | .uncheckedRem =>
      match resolveIntrinsicIsSigned target decls layouts argOps with
      | some s => symBin args (.uncheckedOp .rem s false) (fun x y => [.remSafe s x y])
      | none => none
    | .uncheckedShl =>
      match resolveIntrinsicShiftSigned target decls layouts argOps with
      | some rs => symBin args (.uncheckedOp .shl false rs) (fun x y => [.shiftInBounds rs x y])
      | none => none
    | .uncheckedShr =>
      match
        resolveIntrinsicIsSigned target decls layouts argOps (sameRhsTy := false),
        resolveIntrinsicShiftSigned target decls layouts argOps
      with
      | some ls, some rs =>
        symBin args (.uncheckedOp .shr ls rs) (fun x y => [.shiftInBounds rs x y])
      | _, _ => none
    | _ => none

/-- Jump the active frame to block `target` with locals `locals'`. -/
def SymProg.jump (p : SymProg) (target : BasicBlockIdx) (locals' : List SymSlot) :
    SymProg :=
  { p with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } }

/-- Symbolic `SwitchInt` fork alternatives (explicit branches in order, then
otherwise). Each explicit edge excludes all earlier branch values (`prior`),
matching the first-match semantics of `lookupSwitchTarget`. -/
def symSwitchAltsAux (p : SymProg) (d : SymScalar) (locals' : List SymSlot)
    (otherwise : BasicBlockIdx) (bs : List (Nat × BasicBlockIdx)) (prior : List Nat) :
    List (SymCond × SymProg) :=
  bs.foldr
    (fun vt ih prior =>
      (.switchBranchEq d vt.1 prior, p.jump vt.2 locals') :: ih (prior ++ [vt.1]))
    (fun prior => [(.switchBranchOtherwise d prior, p.jump otherwise locals')]) prior

/-- `symSwitchAltsAux` with the excluded-value accumulator first. -/
def symSwitchAlts (p : SymProg) (d : SymScalar) (locals' : List SymSlot)
    (otherwise : BasicBlockIdx) (prior : List Nat) (bs : List (Nat × BasicBlockIdx)) :
    List (SymCond × SymProg) :=
  symSwitchAltsAux p d locals' otherwise bs prior

/-- Symbolic `evalTerminator`. -/
def symTerm (cfg : SymConfig) (p : SymProg) (body : CapturedMir) (term : Terminator) :
    SymStepRes :=
  match term.kind with
  | .goto target =>
    .step { p with frame := { p.frame with blockIdx := target, stmtIdx := 0 } } []
  | .switchInt discr targets =>
    match symOperand cfg.body.allocations body.layouts p.frame.locals discr with
    | some (v, locals') =>
      match v.asScalar? with
      | some d =>
        match d.asConst? with
        | some sc =>
          .step (p.jump (lookupSwitchTarget sc.bits targets.branches targets.otherwise)
            locals') []
        | none =>
          .branch (symSwitchAlts p d locals' targets.otherwise [] targets.branches) []
      | none => .stuck
    | none => .stuck
  | .assert cond expected target _ =>
    match symOperand cfg.body.allocations body.layouts p.frame.locals cond with
    | some (v, locals') =>
      match v.asScalar? with
      | some c => .step (p.jump target locals') [.assertHolds c expected]
      | none => .stuck
    | none => .stuck
  | .return_ =>
    match get? p.frame.locals 0 with
    | some (.init v) =>
      match v.containsUninit with
      | true => .stuck
      | false =>
        match p.stack with
        | [] => .ret v p []
        | caller :: rest =>
          match caller.destination.projection with
          | [] =>
            match get? caller.frame.locals caller.destination.local_ with
            | some .dead => .stuck
            | some _ =>
              match set? caller.frame.locals caller.destination.local_ (.init v) with
              | some locals' =>
                .step
                  { frame := { caller.frame with
                               blockIdx := caller.returnTarget
                               stmtIdx := 0
                               locals := locals' }
                    stack := rest
                    active := some caller.callerBody } []
              | none => .stuck
            | none => .stuck
          | _ :: _ => .stuck
    | _ => .stuck
  | .call func argOps destination (some targetBb) unwind =>
    match extractCalleeDefPath? func with
    | none => .stuck
    | some defPath =>
      let target : ResolvedCallTarget :=
        { defPath := defPath
          typeArgs := extractCalleeTypeArgs func
          fnSig := none
          isIndirect := false }
      match symOperands cfg.body.allocations body.layouts p.frame.locals argOps with
      | none => .stuck
      | some (args, locals') =>
        match
          lookupCallee cfg.callees body.layouts defPath target.typeArgs cfg.body.traitImpls
        with
        | some calleeBody =>
          .step
            { frame := { blockIdx := 0, stmtIdx := 0
                         locals := symInitLocalsAux 0 calleeBody.localDecls args }
              stack :=
                { callerBody := body
                  frame := { p.frame with locals := locals' }
                  destination := destination
                  returnTarget := targetBb
                  returnUnwind := unwind } :: p.stack
              active := some calleeBody } []
        | none =>
          match isDirectExactDivTarget target with
          | true => .stuck
          | false =>
            match classifyRustIntrinsic? defPath with
            | none => .stuck
            | some kind =>
              match symIntrinsic kind target body.localDecls body.layouts argOps args with
              | none => .stuck
              | some (r, cs) =>
                match destination.projection with
                | [] =>
                  match get? locals' destination.local_ with
                  | some .dead => .stuck
                  | some _ =>
                    match set? locals' destination.local_ (.init (.scalar r)) with
                    | some locals₂ => .step (p.jump targetBb locals₂) cs
                    | none => .stuck
                  | none => .stuck
                | _ :: _ => .stuck
  | _ => .stuck

/-- One symbolic step of the multi-frame program `p`. -/
def symProgStep (cfg : SymConfig) (p : SymProg) : SymStepRes :=
  let body := p.active.getD cfg.body
  match body.phase with
  | .other _ => .stuck
  | _ =>
    match get? body.basicBlocks p.frame.blockIdx with
    | none => .stuck
    | some bb =>
      match get? bb.statements p.frame.stmtIdx with
      | some stmt =>
        match symStmt cfg.body.allocations body p.frame stmt with
        | some (f', cs) => .step { p with frame := f' } cs
        | none => .stuck
      | none =>
        if p.frame.stmtIdx == length bb.statements then
          symTerm cfg p body bb.terminator
        else
          .stuck

/-! ## Part IV: Step-Chunked Runner (`@Nat.rec`) -/

/-- Prefix accumulated side conditions onto a step result. -/
def SymStepRes.addConds (cs : List SymCond) : SymStepRes → SymStepRes
  | .step p cs' => .step p (cs ++ cs')
  | .ret v fin cs' => .ret v fin (cs ++ cs')
  | .branch alts cs' => .branch alts (cs ++ cs')
  | .stuck => .stuck

/-- Continue a run from a step result with `k` remaining steps. -/
def SymStepRes.bindRun (run : SymProg → SymStepRes) : SymStepRes → SymStepRes
  | .step p cs => (run p).addConds cs
  | r => r

/-- Run up to `n` symbolic steps (stopping at return, fork, or stuck), by
`@Nat.rec` so explicit checkpoints reduce by `rfl`. -/
def symProgRunSteps (cfg : SymConfig) (n : Nat) : SymProg → SymStepRes :=
  @Nat.rec (fun _ => SymProg → SymStepRes)
    (fun p => .step p [])
    (fun _ ih p => (symProgStep cfg p).bindRun ih)
    n

/-- A chunk is a step count. -/
abbrev SymChunk := Nat

/-- Run a list of chunks in sequence (structural recursion on the chunk list;
each chunk is a `@Nat.rec` run, so pipelines reduce by `rfl`). -/
def symRunChunks (cfg : SymConfig) (ks : List SymChunk) (p : SymProg) : SymStepRes :=
  ks.foldr (fun k ih p => (symProgRunSteps cfg k p).bindRun ih) (fun p => .step p []) p

/-- Total number of steps of a chunk list. -/
def chunksTotal (ks : List SymChunk) : Nat :=
  ks.foldr (fun k acc => k + acc) 0

/-- Env-independent entry memory of a configuration. -/
def symEntryMemory (cfg : SymConfig) : Memory :=
  { nextAllocId := length cfg.body.allocations
    globals := cfg.body.allocations
    borrows := []
    nextTag := 1
    callees := cfg.callees
    callStack := []
    activeCallee := none
    traitImpls := cfg.body.traitImpls }

/-! ## Part V: Denotation Lemmas -/

/-! ### Definitional equations for the `List.foldr` / `List.map` encodings -/

theorem symSlotsEval_nil (env : SymEnv) : symSlotsEval env [] = [] := rfl
theorem symSlotsEval_cons (env : SymEnv) (s : SymSlot) (l : List SymSlot) :
    symSlotsEval env (s :: l) = s.eval env :: symSlotsEval env l := rfl
theorem symValsEval_nil (env : SymEnv) : symValsEval env [] = [] := rfl
theorem symValsEval_cons (env : SymEnv) (v : SymVal) (l : List SymVal) :
    symValsEval env (v :: l) = v.eval env :: symValsEval env l := rfl
theorem symStackEval_nil (env : SymEnv) : symStackEval env [] = [] := rfl
theorem symStackEval_cons (env : SymEnv) (c : SymSaved) (l : List SymSaved) :
    symStackEval env (c :: l) = c.eval env :: symStackEval env l := rfl
theorem symFieldsEval_nil (env : SymEnv) : symFieldsEval env [] = [] := rfl
theorem symFieldsEval_cons (env : SymEnv) (a : SymScalar) (l : List SymScalar) :
    symFieldsEval env (a :: l) = .scalar (a.eval env) :: symFieldsEval env l := rfl
theorem condsHold_nil (env : SymEnv) : condsHold env [] = True := rfl
theorem condsHold_cons (env : SymEnv) (c : SymCond) (cs : List SymCond) :
    condsHold env (c :: cs) = (c.holds env ∧ condsHold env cs) := rfl
theorem symOperands_nil (globals : List CapturedAllocation) (layouts : LayoutTable)
    (locals : List SymSlot) : symOperands globals layouts locals [] = some ([], locals) := rfl
theorem symOperands_cons (globals : List CapturedAllocation) (layouts : LayoutTable)
    (locals : List SymSlot) (op : Operand) (rest : List Operand) :
    symOperands globals layouts locals (op :: rest) =
      match symOperand globals layouts locals op with
      | some (v, locals₁) =>
        match symOperands globals layouts locals₁ rest with
        | some (vs, locals₂) => some (v :: vs, locals₂)
        | none => none
      | none => none := rfl
theorem symInitLocalsAux_nil (n : Nat) (args : List SymVal) :
    symInitLocalsAux n [] args = [] := rfl
theorem symInitLocalsAux_zero_cons (d : LocalDecl) (decls : List LocalDecl)
    (args : List SymVal) :
    symInitLocalsAux 0 (d :: decls) args = .uninit :: symInitLocalsAux 1 decls args := rfl
theorem symInitLocalsAux_succ_cons_cons (idx : Nat) (d : LocalDecl) (decls : List LocalDecl)
    (a : SymVal) (rest : List SymVal) :
    symInitLocalsAux (idx + 1) (d :: decls) (a :: rest) =
      .init a :: symInitLocalsAux (Nat.add idx 1) decls rest := rfl
theorem symInitLocalsAux_succ_cons_nil (idx : Nat) (d : LocalDecl) (decls : List LocalDecl) :
    symInitLocalsAux (idx + 1) (d :: decls) [] =
      .dead :: symInitLocalsAux (Nat.add idx 1) decls [] := rfl

theorem length_symSlotsEval (env : SymEnv) :
    ∀ l : List SymSlot, (symSlotsEval env l).length = l.length
  | [] => rfl
  | _ :: rest => congrArg Nat.succ (length_symSlotsEval env rest)

theorem get?_symSlotsEval (env : SymEnv) :
    ∀ (l : List SymSlot) (i : Nat),
      get? (symSlotsEval env l) i = (get? l i).map (SymSlot.eval env)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: rest, i + 1 => get?_symSlotsEval env rest i

theorem symSlotsEval_set (env : SymEnv) :
    ∀ (l : List SymSlot) (i : Nat) (s : SymSlot),
      symSlotsEval env (l.set i s) = (symSlotsEval env l).set i (s.eval env)
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | a :: rest, i + 1, s =>
    congrArg (List.cons (a.eval env)) (symSlotsEval_set env rest i s)

theorem set?_symSlotsEval (env : SymEnv) (l : List SymSlot) (i : Nat) (s : SymSlot) :
    set? (symSlotsEval env l) i (s.eval env) = (set? l i s).map (symSlotsEval env) := by
  unfold set?
  rw [length_symSlotsEval]
  split
  · exact congrArg some (symSlotsEval_set env l i s).symm
  · rfl

theorem set?_symSlotsEval_uninit (env : SymEnv) (l : List SymSlot) (i : Nat) :
    set? (symSlotsEval env l) i .uninit = (set? l i .uninit).map (symSlotsEval env) :=
  set?_symSlotsEval env l i .uninit

theorem set?_symSlotsEval_dead (env : SymEnv) (l : List SymSlot) (i : Nat) :
    set? (symSlotsEval env l) i .dead = (set? l i .dead).map (symSlotsEval env) :=
  set?_symSlotsEval env l i .dead

theorem set?_symSlotsEval_init (env : SymEnv) (l : List SymSlot) (i : Nat) (v : SymVal) :
    set? (symSlotsEval env l) i (.init (v.eval env)) =
      (set? l i (.init v)).map (symSlotsEval env) :=
  set?_symSlotsEval env l i (.init v)

theorem valueListContainsUninit_symFieldsEval (env : SymEnv) :
    ∀ fs : List SymScalar, valueListContainsUninit (symFieldsEval env fs) = false
  | [] => rfl
  | _ :: rest => valueListContainsUninit_symFieldsEval env rest

theorem valueContainsUninit_symVal (env : SymEnv) :
    ∀ v : SymVal, valueContainsUninit (v.eval env) = v.containsUninit
  | .unit => rfl
  | .scalar _ => rfl
  | .aggregate _ fs => valueListContainsUninit_symFieldsEval env fs
  | .uninit => rfl
  | .concrete _ => rfl

theorem symVal_eval_of_asScalar {v : SymVal} {a : SymScalar}
    (h : v.asScalar? = some a) (env : SymEnv) : v.eval env = .scalar (a.eval env) := by
  cases v with
  | scalar s =>
    injection h with h
    subst h
    rfl
  | concrete cv =>
    cases cv with
    | scalar sc =>
      injection h with h
      subst h
      rfl
    | unit => nomatch h
    | ptr _ _ => nomatch h
    | aggregate _ _ => nomatch h
    | uninit => nomatch h
  | unit => nomatch h
  | aggregate _ _ => nomatch h
  | uninit => nomatch h

theorem symScalar_eval_of_asConst {a : SymScalar} {sc : ScalarInt}
    (h : a.asConst? = some sc) (env : SymEnv) : a.eval env = sc := by
  obtain ⟨node, fuel, wf⟩ := a
  cases node with
  | const c =>
    cases wf with
    | const => exact Option.some.inj h
  | var _ _ => nomatch h
  | wrappingOp _ _ _ => nomatch h
  | saturatingOp _ _ _ _ => nomatch h
  | uncheckedOp _ _ _ _ _ => nomatch h
  | bitIntrinsic _ _ => nomatch h

theorem symSlotsEval_symInitLocalsAux (env : SymEnv) :
    ∀ (n : Nat) (decls : List LocalDecl) (args : List SymVal),
      symSlotsEval env (symInitLocalsAux n decls args) =
        initLocalsAux n decls (symValsEval env args)
  | n, [], args => by
    rw [symInitLocalsAux_nil]
    cases n <;> rfl
  | .zero, d :: decls, args => by
    rw [symInitLocalsAux_zero_cons, symSlotsEval_cons, symSlotsEval_symInitLocalsAux env 1 decls args]
    rfl
  | .succ idx, d :: decls, a :: rest => by
    rw [symInitLocalsAux_succ_cons_cons, symSlotsEval_cons,
      symSlotsEval_symInitLocalsAux env (Nat.add idx 1) decls rest]
    rfl
  | .succ idx, d :: decls, [] => by
    rw [symInitLocalsAux_succ_cons_nil, symSlotsEval_cons,
      symSlotsEval_symInitLocalsAux env (Nat.add idx 1) decls []]
    rfl

/-! ## Part VI: Operand / Rvalue / Statement Soundness -/

theorem symOperand_sound {globals : List CapturedAllocation} {layouts : LayoutTable}
    {locals : List SymSlot} {op : Operand} {v : SymVal} {locals' : List SymSlot}
    (h : symOperand globals layouts locals op = some (v, locals')) (env : SymEnv)
    (borrows : List BorrowEntry) (callerLocals : List LocalSlot) (decls : List LocalDecl)
    (callStack : List SavedCallerFrame) :
    evalOperand (symSlotsEval env locals) op borrows globals layouts callerLocals decls
      callStack = .ok (v.eval env) (symSlotsEval env locals') := by
  cases op with
  | copy p =>
    obtain ⟨loc, proj⟩ := p
    cases proj with
    | cons _ _ => nomatch h
    | nil =>
      simp only [symOperand] at h
      dsimp only [evalOperand]
      rw [get?_symSlotsEval]
      cases hg : get? locals loc with
      | none => rw [hg] at h; nomatch h
      | some sl =>
        rw [hg] at h
        cases sl with
        | dead => nomatch h
        | uninit => nomatch h
        | init w =>
          dsimp only at h
          cases hc : w.containsUninit with
          | true => rw [hc] at h; nomatch h
          | false =>
            rw [hc] at h
            injection h with h
            injection h with h1 h2
            subst h1
            subst h2
            dsimp only [Option.map, SymSlot.eval, readProjectedValue]
            rw [valueContainsUninit_symVal, hc]
  | move p =>
    obtain ⟨loc, proj⟩ := p
    cases proj with
    | cons _ _ => nomatch h
    | nil =>
      simp only [symOperand] at h
      dsimp only [evalOperand]
      rw [get?_symSlotsEval]
      cases hg : get? locals loc with
      | none => rw [hg] at h; nomatch h
      | some sl =>
        rw [hg] at h
        cases sl with
        | dead => nomatch h
        | uninit => nomatch h
        | init w =>
          dsimp only at h
          cases hc : w.containsUninit with
          | true => rw [hc] at h; nomatch h
          | false =>
            rw [hc] at h
            dsimp only at h
            cases hs : set? locals loc .uninit with
            | none => rw [hs] at h; nomatch h
            | some l' =>
              rw [hs] at h
              injection h with h
              injection h with h1 h2
              subst h1
              subst h2
              dsimp only [Option.map, SymSlot.eval, readProjectedValue]
              rw [valueContainsUninit_symVal, hc]
              dsimp only
              rw [set?_symSlotsEval_uninit, hs]
              rfl
  | constant c =>
    obtain ⟨ty, cv⟩ := c
    cases cv with
    | scalar cs =>
      simp only [symOperand] at h
      dsimp only [evalOperand]
      cases he : evalConstValue (.scalar cs) ty globals layouts with
      | none => rw [he] at h; nomatch h
      | some w =>
        rw [he] at h
        injection h with h
        injection h with h1 h2
        subst h1
        subst h2
        rfl
    | zeroSized =>
      simp only [symOperand] at h
      dsimp only [evalOperand]
      cases he : evalConstValue .zeroSized ty globals layouts with
      | none => rw [he] at h; nomatch h
      | some w =>
        rw [he] at h
        injection h with h
        injection h with h1 h2
        subst h1
        subst h2
        rfl
    | slice _ _ => nomatch h
    | indirect _ _ => nomatch h
    | unevaluated _ => nomatch h

theorem symOperand_shape {globals : List CapturedAllocation} {layouts : LayoutTable}
    {locals : List SymSlot} {op : Operand} {v : SymVal} {locals' : List SymSlot}
    (h : symOperand globals layouts locals op = some (v, locals')) :
    operandIsLeadingOpaqueCastMove op = false := by
  cases op with
  | copy _ => rfl
  | constant _ => rfl
  | move p =>
    obtain ⟨loc, proj⟩ := p
    cases proj with
    | nil => rfl
    | cons _ _ => nomatch h

theorem symOperands_sound {globals : List CapturedAllocation} {layouts : LayoutTable}
    (env : SymEnv) (borrows : List BorrowEntry) (callerLocals : List LocalSlot)
    (decls : List LocalDecl) (callStack : List SavedCallerFrame) :
    ∀ {locals : List SymSlot} {ops : List Operand} {vs : List SymVal}
      {locals' : List SymSlot},
      symOperands globals layouts locals ops = some (vs, locals') →
      evalOperandsWithBodyCast (symSlotsEval env locals) ops borrows globals layouts
        callerLocals decls callStack = .ok (symValsEval env vs) (symSlotsEval env locals')
  | locals, [], vs, locals', h => by
    rw [symOperands_nil] at h
    injection h with h
    injection h with h1 h2
    subst h1
    subst h2
    rfl
  | locals, op :: rest, vs, locals', h => by
    rw [symOperands_cons] at h
    cases h1 : symOperand globals layouts locals op with
    | none => rw [h1] at h; nomatch h
    | some r =>
      obtain ⟨v, locals₁⟩ := r
      rw [h1] at h
      dsimp only at h
      cases h2 : symOperands globals layouts locals₁ rest with
      | none => rw [h2] at h; nomatch h
      | some r2 =>
        obtain ⟨vs', locals₂⟩ := r2
        rw [h2] at h
        injection h with h
        injection h with hv hl
        subst hv
        subst hl
        have hOp : evalOperandWithBodyCast (symSlotsEval env locals) op borrows globals
            layouts callerLocals decls callStack = .ok (v.eval env) (symSlotsEval env locals₁) := by
          unfold evalOperandWithBodyCast
          rw [symOperand_shape h1]
          exact symOperand_sound h1 env borrows callerLocals [] callStack
        simp only [evalOperandsWithBodyCast]
        rw [hOp]
        dsimp only
        rw [symOperands_sound env borrows callerLocals decls callStack h2]
        rfl

theorem validateLoadedValue_of_static {layouts : LayoutTable} {decls : List LocalDecl}
    {op : Operand} (h : loadedValueStaticOk layouts decls op = true) (v : Value) :
    validateLoadedValue layouts decls op v = true := by
  cases op with
  | constant _ => rfl
  | copy p =>
    simp only [loadedValueStaticOk] at h
    simp only [validateLoadedValue]
    revert h
    cases operandTy decls layouts (.copy p) with
    | none => intro _; rfl
    | some ty =>
      dsimp only
      cases ty.kind <;> first | (intro _; rfl) | (intro h; exact absurd h Bool.false_ne_true)
  | move p =>
    simp only [loadedValueStaticOk] at h
    simp only [validateLoadedValue]
    revert h
    cases operandTy decls layouts (.move p) with
    | none => intro _; rfl
    | some ty =>
      dsimp only
      cases ty.kind <;> first | (intro _; rfl) | (intro h; exact absurd h Bool.false_ne_true)

theorem symRvalue_sound {globals : List CapturedAllocation} {layouts : LayoutTable}
    {decls : List LocalDecl} {locals : List SymSlot} {rv : Rvalue} {v : SymVal}
    {locals' : List SymSlot} {cs : List SymCond}
    (h : symRvalue globals layouts decls locals rv = some (v, locals', cs)) (env : SymEnv)
    (mem : Memory) (hg : mem.globals = globals) (hb : mem.borrows = []) :
    evalRvalue (symSlotsEval env locals) rv mem decls layouts =
      .ok (v.eval env) (symSlotsEval env locals') mem := by
  cases rv with
  | use op =>
    simp only [symRvalue] at h
    cases h1 : symOperand globals layouts locals op with
    | none => rw [h1] at h; nomatch h
    | some r =>
      obtain ⟨w, l₁⟩ := r
      rw [h1] at h
      dsimp only at h
      cases h2 : loadedValueStaticOk layouts decls op with
      | false => rw [h2] at h; nomatch h
      | true =>
        rw [h2] at h
        injection h with h
        injection h with hv h
        injection h with hl _
        subst hv
        subst hl
        simp only [evalRvalue]
        rw [hg, symOperand_sound h1 env mem.borrows mem.callerLocals decls mem.callStack]
        dsimp only
        rw [validateLoadedValue_of_static h2]
        dsimp only
        rw [hb]
        cases op with
        | constant _ => rfl
        | copy p =>
          obtain ⟨loc, proj⟩ := p
          cases proj with
          | nil => rfl
          | cons _ _ => nomatch h1
        | move p =>
          obtain ⟨loc, proj⟩ := p
          cases proj with
          | nil => rfl
          | cons _ _ => nomatch h1
  | _ => nomatch h

theorem symStmt_sound {cfg : SymConfig} {p : SymProg} {body : CapturedMir} {stmt : Statement}
    {f' : SymFrame} {cs : List SymCond}
    (h : symStmt cfg.body.allocations body p.frame stmt = some (f', cs)) (env : SymEnv) :
    evalStmt (p.toMachineState cfg env) stmt body.localDecls body.layouts =
      MirStepNode.step ({ p with frame := f' }.toMachineState cfg env) := by
  obtain ⟨kind, span⟩ := stmt
  cases kind with
  | nop =>
    simp only [symStmt] at h
    injection h with h
    injection h with h1 _
    subst h1
    rfl
  | storageLive loc =>
    simp only [symStmt] at h
    dsimp only [evalStmt, SymProg.toMachineState, SymFrame.eval]
    rw [get?_symSlotsEval]
    cases hg : get? p.frame.locals loc with
    | none => rw [hg] at h; nomatch h
    | some sl =>
      rw [hg] at h
      dsimp only at h
      dsimp only [Option.map]
      rw [set?_symSlotsEval_uninit]
      cases hs : set? p.frame.locals loc .uninit with
      | none => rw [hs] at h; nomatch h
      | some l' =>
        rw [hs] at h
        injection h with h
        injection h with h1 _
        subst h1
        rfl
  | storageDead loc =>
    simp only [symStmt] at h
    dsimp only [evalStmt, SymProg.toMachineState, SymFrame.eval]
    rw [get?_symSlotsEval]
    cases hg : get? p.frame.locals loc with
    | none => rw [hg] at h; nomatch h
    | some sl =>
      rw [hg] at h
      dsimp only at h
      dsimp only [Option.map]
      rw [set?_symSlotsEval_dead]
      cases hs : set? p.frame.locals loc .dead with
      | none => rw [hs] at h; nomatch h
      | some l' =>
        rw [hs] at h
        injection h with h
        injection h with h1 _
        subst h1
        rfl
  | assign dst rv =>
    obtain ⟨dloc, dproj⟩ := dst
    cases dproj with
    | cons _ _ => nomatch h
    | nil =>
      simp only [symStmt] at h
      cases hr : symRvalue cfg.body.allocations body.layouts body.localDecls p.frame.locals rv with
      | none => rw [hr] at h; nomatch h
      | some r =>
        obtain ⟨v, locals₁, cs'⟩ := r
        rw [hr] at h
        dsimp only at h
        have hEval := symRvalue_sound hr env (p.toMemory cfg env) rfl rfl
        dsimp only [evalStmt]
        rw [show (p.toMachineState cfg env).frame.locals = symSlotsEval env p.frame.locals from rfl,
          show (p.toMachineState cfg env).memory = p.toMemory cfg env from rfl, hEval]
        dsimp only
        rw [get?_symSlotsEval]
        cases hg : get? locals₁ dloc with
        | none => rw [hg] at h; nomatch h
        | some sl =>
          rw [hg] at h
          cases sl with
          | dead => nomatch h
          | uninit =>
            dsimp only at h
            dsimp only [Option.map, SymSlot.eval]
            rw [set?_symSlotsEval_init]
            cases hs : set? locals₁ dloc (.init v) with
            | none => rw [hs] at h; nomatch h
            | some l₂ =>
              rw [hs] at h
              injection h with h
              injection h with h1 _
              subst h1
              rfl
          | init w =>
            dsimp only at h
            dsimp only [Option.map, SymSlot.eval]
            rw [set?_symSlotsEval_init]
            cases hs : set? locals₁ dloc (.init v) with
            | none => rw [hs] at h; nomatch h
            | some l₂ =>
              rw [hs] at h
              injection h with h
              injection h with h1 _
              subst h1
              rfl
  | _ => nomatch h

/-! ## Part VII: Side Conditions Imply Trusted Intrinsic Definedness -/

theorem nat_beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem nat_beq_true_of_eq {a b : Nat} (h : a = b) : Nat.beq a b = true := by
  subst h
  exact Nat.beq_refl a

theorem nat_ble_false_of_lt {a b : Nat} (h : b < a) : Nat.ble a b = false := by
  cases hb : Nat.ble a b with
  | false => rfl
  | true => exact absurd (Nat.le_of_ble_eq_true hb) (Nat.not_le_of_gt h)

theorem scalarModulus_pos : ∀ n : Nat, 0 < scalarModulus n
  | .zero => Nat.zero_lt_one
  | .succ n => Nat.mul_pos (Nat.zero_lt_succ 255) (scalarModulus_pos n)

theorem wrapScalarBits_lt (v : Nat) {m : Nat} (hm : 0 < m) : wrapScalarBits v m < m := by
  unfold wrapScalarBits
  cases hb : Nat.ble m v with
  | true => exact Nat.mod_lt v hm
  | false =>
    exact Nat.lt_of_not_le (fun h => by
      rw [Nat.ble_eq_true_of_le h] at hb
      nomatch hb)

theorem option_eq_some_getD {α : Type} {o : Option α} (h : o.isSome = true) (d : α) :
    o = some (o.getD d) := by
  cases o with
  | none => nomatch h
  | some _ => rfl

theorem widthGuard_false {x y : ScalarInt} (h : ScWidthsOk x y) :
    Bool.or (Nat.beq x.sizeBytes 0) (Bool.not (Nat.beq x.sizeBytes y.sizeBytes)) = false := by
  rw [nat_beq_false_of_ne h.1, nat_beq_true_of_eq h.2]
  rfl

theorem unGuard_false {x : ScalarInt} (h : x.sizeBytes ≠ 0) :
    Bool.or (Nat.beq x.sizeBytes 0) (Nat.beq 4 0) = false := by
  rw [nat_beq_false_of_ne h]
  rfl

theorem evalBswap_isSome {x : ScalarInt} (h : x.sizeBytes ≠ 0) : (evalBswap x).isSome = true := by
  unfold evalBswap
  rw [nat_beq_false_of_ne h]
  rfl

theorem evalBitreverse_isSome {x : ScalarInt} (h : x.sizeBytes ≠ 0) :
    (evalBitreverse x).isSome = true := by
  unfold evalBitreverse
  rw [nat_beq_false_of_ne h]
  rfl

theorem evalCtlz_isSome {x : ScalarInt} (h : x.sizeBytes ≠ 0) : (evalCtlz x).isSome = true := by
  unfold evalCtlz
  rw [unGuard_false h]
  rfl

theorem evalCttz_isSome {x : ScalarInt} (h : x.sizeBytes ≠ 0) : (evalCttz x).isSome = true := by
  unfold evalCttz
  rw [unGuard_false h]
  rfl

theorem evalCtpop_isSome {x : ScalarInt} (h : x.sizeBytes ≠ 0) : (evalCtpop x).isSome = true := by
  unfold evalCtpop
  rw [unGuard_false h]
  rfl

theorem evalCtlzNonzero_isSome {x : ScalarInt} (h : x.sizeBytes ≠ 0) (hz : scBits x ≠ 0) :
    (evalCtlzNonzero x).isSome = true := by
  have hz' : wrapScalarBits x.bits (scalarModulus x.sizeBytes) ≠ 0 := hz
  unfold evalCtlzNonzero
  rw [unGuard_false h]
  dsimp only
  rw [nat_beq_false_of_ne hz']
  rfl

theorem evalCttzNonzero_isSome {x : ScalarInt} (h : x.sizeBytes ≠ 0) (hz : scBits x ≠ 0) :
    (evalCttzNonzero x).isSome = true := by
  have hz' : wrapScalarBits x.bits (scalarModulus x.sizeBytes) ≠ 0 := hz
  unfold evalCttzNonzero
  rw [unGuard_false h]
  dsimp only
  rw [nat_beq_false_of_ne hz']
  rfl

theorem symWrapEval_isSome (k : SymWrapKind) {x y : ScalarInt} (h : ScWidthsOk x y) :
    (symWrapEval k x y).isSome = true := by
  cases k with
  | add =>
    show (evalWrappingAdd x y).isSome = true
    unfold evalWrappingAdd; rw [widthGuard_false h]; rfl
  | sub =>
    show (evalWrappingSub x y).isSome = true
    unfold evalWrappingSub; rw [widthGuard_false h]; rfl
  | mul =>
    show (evalWrappingMul x y).isSome = true
    unfold evalWrappingMul; rw [widthGuard_false h]; rfl

theorem symSatEval_isSome (k : SymSatKind) (sg : Bool) {x y : ScalarInt} (h : ScWidthsOk x y) :
    (symSatEval k sg x y).isSome = true := by
  cases k with
  | add =>
    show (evalSaturatingAdd x y sg).isSome = true
    unfold evalSaturatingAdd
    rw [widthGuard_false h]
    dsimp only
    cases sg with
    | false => dsimp only; split <;> rfl
    | true => dsimp only; split <;> (try split) <;> rfl
  | sub =>
    show (evalSaturatingSub x y sg).isSome = true
    unfold evalSaturatingSub
    rw [widthGuard_false h]
    dsimp only
    cases sg with
    | false => dsimp only; split <;> rfl
    | true => dsimp only; split <;> (try split) <;> rfl

theorem evalUncheckedAdd_isSome {x y : ScalarInt} {sg : Bool} (hw : ScWidthsOk x y)
    (hc : match sg with
      | false => scBits x + scBitsAt x y < scalarModulus x.sizeBytes
      | true => signedOverflowAdd (scBits x) (scBitsAt x y) x.sizeBytes = false) :
    (evalUncheckedAdd x y sg).isSome = true := by
  unfold evalUncheckedAdd
  rw [widthGuard_false hw]
  cases sg with
  | false =>
    have hb : Nat.ble (scalarModulus x.sizeBytes)
        (Nat.add (wrapScalarBits x.bits (scalarModulus x.sizeBytes))
          (wrapScalarBits y.bits (scalarModulus x.sizeBytes))) = false :=
      nat_ble_false_of_lt hc
    dsimp only
    rw [hb]
    rfl
  | true =>
    have hb : signedOverflowAdd (wrapScalarBits x.bits (scalarModulus x.sizeBytes))
        (wrapScalarBits y.bits (scalarModulus x.sizeBytes)) x.sizeBytes = false := hc
    dsimp only
    rw [hb]
    rfl

theorem evalUncheckedSub_isSome {x y : ScalarInt} {sg : Bool} (hw : ScWidthsOk x y)
    (hc : match sg with
      | false => scBitsAt x y ≤ scBits x
      | true => signedOverflowSub (scBits x) (scBitsAt x y) x.sizeBytes = false) :
    (evalUncheckedSub x y sg).isSome = true := by
  unfold evalUncheckedSub
  rw [widthGuard_false hw]
  cases sg with
  | false =>
    have hb : Nat.ble (wrapScalarBits y.bits (scalarModulus x.sizeBytes))
        (wrapScalarBits x.bits (scalarModulus x.sizeBytes)) = true :=
      Nat.ble_eq_true_of_le hc
    have hd : Nat.ble (scalarModulus x.sizeBytes)
        (Nat.sub (wrapScalarBits x.bits (scalarModulus x.sizeBytes))
          (wrapScalarBits y.bits (scalarModulus x.sizeBytes))) = false :=
      nat_ble_false_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _)
        (wrapScalarBits_lt _ (scalarModulus_pos _)))
    dsimp only
    rw [hb]
    dsimp only
    rw [hd]
    rfl
  | true =>
    have hb : signedOverflowSub (wrapScalarBits x.bits (scalarModulus x.sizeBytes))
        (wrapScalarBits y.bits (scalarModulus x.sizeBytes)) x.sizeBytes = false := hc
    dsimp only
    rw [hb]
    rfl

theorem evalUncheckedMul_isSome {x y : ScalarInt} {sg : Bool} (hw : ScWidthsOk x y)
    (hc : match sg with
      | false => scBits x * scBitsAt x y < scalarModulus x.sizeBytes
      | true => signedOverflowMul (scBits x) (scBitsAt x y) x.sizeBytes = false) :
    (evalUncheckedMul x y sg).isSome = true := by
  unfold evalUncheckedMul
  rw [widthGuard_false hw]
  cases sg with
  | false =>
    have hb : Nat.ble (scalarModulus x.sizeBytes)
        (Nat.mul (wrapScalarBits x.bits (scalarModulus x.sizeBytes))
          (wrapScalarBits y.bits (scalarModulus x.sizeBytes))) = false :=
      nat_ble_false_of_lt hc
    dsimp only
    rw [hb]
    rfl
  | true =>
    have hb : signedOverflowMul (wrapScalarBits x.bits (scalarModulus x.sizeBytes))
        (wrapScalarBits y.bits (scalarModulus x.sizeBytes)) x.sizeBytes = false := hc
    dsimp only
    rw [hb]
    rfl

theorem minNegOne_guard_false {x y : ScalarInt} (h : ScNotMinNegOne x y) :
    Bool.and
      (Nat.beq (wrapScalarBits x.bits (scalarModulus x.sizeBytes))
        (scalarPow2 (Nat.sub (Nat.mul x.sizeBytes 8) 1)))
      (Nat.beq (wrapScalarBits y.bits (scalarModulus x.sizeBytes))
        (Nat.sub (scalarModulus x.sizeBytes) 1)) = false := by
  cases h1 : Nat.beq (wrapScalarBits x.bits (scalarModulus x.sizeBytes))
      (scalarPow2 (Nat.sub (Nat.mul x.sizeBytes 8) 1)) with
  | false => rfl
  | true =>
    cases h2 : Nat.beq (wrapScalarBits y.bits (scalarModulus x.sizeBytes))
        (Nat.sub (scalarModulus x.sizeBytes) 1) with
    | false => rfl
    | true => exact absurd ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩ h

theorem evalUncheckedDiv_isSome {x y : ScalarInt} {sg : Bool} (hw : ScWidthsOk x y)
    (hz : scBitsAt x y ≠ 0)
    (hc : match sg with
      | false => True
      | true => ScNotMinNegOne x y) :
    (evalUncheckedDiv x y sg).isSome = true := by
  have hz' : wrapScalarBits y.bits (scalarModulus x.sizeBytes) ≠ 0 := hz
  unfold evalUncheckedDiv
  rw [widthGuard_false hw]
  dsimp only
  rw [nat_beq_false_of_ne hz']
  cases sg with
  | false => rfl
  | true =>
    dsimp only
    rw [minNegOne_guard_false hc]
    rfl

theorem evalUncheckedRem_isSome {x y : ScalarInt} {sg : Bool} (hw : ScWidthsOk x y)
    (hz : scBitsAt x y ≠ 0)
    (hc : match sg with
      | false => True
      | true => ScNotMinNegOne x y) :
    (evalUncheckedRem x y sg).isSome = true := by
  have hz' : wrapScalarBits y.bits (scalarModulus x.sizeBytes) ≠ 0 := hz
  unfold evalUncheckedRem
  rw [widthGuard_false hw]
  dsimp only
  rw [nat_beq_false_of_ne hz']
  cases sg with
  | false => rfl
  | true =>
    dsimp only
    rw [minNegOne_guard_false hc]
    rfl

theorem shiftGuards_false {x y : ScalarInt} {rs : Bool} (hx : x.sizeBytes ≠ 0)
    (hy : y.sizeBytes ≠ 0) (hn : (rs && isSignedNegative (scBits y) y.sizeBytes) = false)
    (hb : scBits y < Nat.mul x.sizeBytes 8) :
    Bool.or (Nat.beq x.sizeBytes 0) (Nat.beq y.sizeBytes 0) = false ∧
      Bool.or (Bool.and rs (isSignedNegative (wrapScalarBits y.bits (scalarModulus y.sizeBytes))
          y.sizeBytes))
        (Nat.ble (Nat.mul x.sizeBytes 8) (wrapScalarBits y.bits (scalarModulus y.sizeBytes))) =
        false := by
  refine ⟨?_, ?_⟩
  · rw [nat_beq_false_of_ne hx, nat_beq_false_of_ne hy]
    rfl
  · have hn' : Bool.and rs (isSignedNegative (wrapScalarBits y.bits (scalarModulus y.sizeBytes))
        y.sizeBytes) = false := hn
    have hb' : Nat.ble (Nat.mul x.sizeBytes 8)
        (wrapScalarBits y.bits (scalarModulus y.sizeBytes)) = false := nat_ble_false_of_lt hb
    rw [hn', hb']
    rfl

theorem evalUncheckedShl_isSome {x y : ScalarInt} {rs : Bool} (hx : x.sizeBytes ≠ 0)
    (hy : y.sizeBytes ≠ 0) (hn : (rs && isSignedNegative (scBits y) y.sizeBytes) = false)
    (hb : scBits y < Nat.mul x.sizeBytes 8) :
    (evalUncheckedShl x y rs).isSome = true := by
  have ⟨g1, g2⟩ := shiftGuards_false hx hy hn hb
  unfold evalUncheckedShl
  rw [g1]
  dsimp only
  rw [g2]
  rfl

theorem evalUncheckedShr_isSome {x y : ScalarInt} {ls rs : Bool} (hx : x.sizeBytes ≠ 0)
    (hy : y.sizeBytes ≠ 0) (hn : (rs && isSignedNegative (scBits y) y.sizeBytes) = false)
    (hb : scBits y < Nat.mul x.sizeBytes 8) :
    (evalUncheckedShr x y ls rs).isSome = true := by
  have ⟨g1, g2⟩ := shiftGuards_false hx hy hn hb
  unfold evalUncheckedShr
  rw [g1]
  dsimp only
  rw [g2]
  rfl

/-! ### Closed forms for unsigned unchecked arithmetic -/

theorem wrapScalarBits_of_lt {v m : Nat} (h : v < m) : wrapScalarBits v m = v := by
  unfold wrapScalarBits
  rw [nat_ble_false_of_lt h]

/-- Unsigned `unchecked_add` in range is exact addition. -/
theorem evalUncheckedAdd_unsigned_eq {a b w : Nat} (hw : w ≠ 0)
    (ha : a < scalarModulus w) (hb : b < scalarModulus w) (hab : a + b < scalarModulus w) :
    evalUncheckedAdd ⟨a, w⟩ ⟨b, w⟩ false = some ⟨a + b, w⟩ := by
  unfold evalUncheckedAdd
  rw [widthGuard_false (x := ⟨a, w⟩) (y := ⟨b, w⟩) ⟨hw, rfl⟩]
  dsimp only
  rw [wrapScalarBits_of_lt ha, wrapScalarBits_of_lt hb]
  have hn : Nat.ble (scalarModulus w) (Nat.add a b) = false := nat_ble_false_of_lt hab
  rw [hn]
  rfl

/-- Unsigned `unchecked_mul` in range is exact multiplication. -/
theorem evalUncheckedMul_unsigned_eq {a b w : Nat} (hw : w ≠ 0)
    (ha : a < scalarModulus w) (hb : b < scalarModulus w) (hab : a * b < scalarModulus w) :
    evalUncheckedMul ⟨a, w⟩ ⟨b, w⟩ false = some ⟨a * b, w⟩ := by
  unfold evalUncheckedMul
  rw [widthGuard_false (x := ⟨a, w⟩) (y := ⟨b, w⟩) ⟨hw, rfl⟩]
  dsimp only
  rw [wrapScalarBits_of_lt ha, wrapScalarBits_of_lt hb]
  have hn : Nat.ble (scalarModulus w) (Nat.mul a b) = false := nat_ble_false_of_lt hab
  rw [hn]
  rfl

/-! ## Part VIII: Intrinsic Soundness against `evalNonSelectIntrinsicCall` -/

theorem symUn_shape {args : List SymVal} {k : SymBitKind} {mk : SymScalar → List SymCond}
    {r : SymScalar} {cs : List SymCond} (h : symUn args k mk = some (r, cs)) :
    ∃ a x, args = [a] ∧ a.asScalar? = some x ∧ r = .bitIntrinsic k x ∧ cs = mk x := by
  cases args with
  | nil => nomatch h
  | cons a rest =>
    cases rest with
    | cons _ _ => nomatch h
    | nil =>
      simp only [symUn] at h
      cases hx : a.asScalar? with
      | none => rw [hx] at h; nomatch h
      | some x =>
        rw [hx] at h
        injection h with h
        injection h with h1 h2
        exact ⟨a, x, rfl, hx, h1.symm, h2.symm⟩

theorem symBin_shape {args : List SymVal} {f : SymScalar → SymScalar → SymScalar}
    {mk : SymScalar → SymScalar → List SymCond} {r : SymScalar} {cs : List SymCond}
    (h : symBin args f mk = some (r, cs)) :
    ∃ a b x y, args = [a, b] ∧ a.asScalar? = some x ∧ b.asScalar? = some y ∧
      r = f x y ∧ cs = mk x y := by
  cases args with
  | nil => nomatch h
  | cons a rest =>
    cases rest with
    | nil => nomatch h
    | cons b rest =>
      cases rest with
      | cons _ _ => nomatch h
      | nil =>
        simp only [symBin] at h
        cases hx : a.asScalar? with
        | none => rw [hx] at h; nomatch h
        | some x =>
          cases hy : b.asScalar? with
          | none => rw [hx, hy] at h; nomatch h
          | some y =>
            rw [hx, hy] at h
            injection h with h
            injection h with h1 h2
            exact ⟨a, b, x, y, rfl, hx, hy, h1.symm, h2.symm⟩

theorem symValsEval_one {a : SymVal} {x : SymScalar} (hx : a.asScalar? = some x)
    (env : SymEnv) : symValsEval env [a] = [.scalar (x.eval env)] := by
  rw [symValsEval_cons, symValsEval_nil, symVal_eval_of_asScalar hx env]

theorem symValsEval_two {a b : SymVal} {x y : SymScalar} (hx : a.asScalar? = some x)
    (hy : b.asScalar? = some y) (env : SymEnv) :
    symValsEval env [a, b] = [.scalar (x.eval env), .scalar (y.eval env)] := by
  rw [symValsEval_cons, symValsEval_cons, symValsEval_nil, symVal_eval_of_asScalar hx env,
    symVal_eval_of_asScalar hy env]

theorem writeIntrinsicScalarResult_some (s : MachineState) (locals' : List LocalSlot)
    (dst : Place) (bb : BasicBlockIdx) {o : Option ScalarInt} (h : o.isSome = true) :
    writeIntrinsicScalarResult s locals' dst bb o =
      writeIntrinsicReturn s locals' dst bb (.scalar (o.getD symDefaultScalar)) := by
  rw [option_eq_some_getD h symDefaultScalar]
  rfl

/-- Generic intrinsic soundness: under the recorded side conditions, the
trusted value-returning intrinsic step writes exactly the symbolic result. -/
theorem symIntrinsic_sound {kind : RustIntrinsicKind} {target : ResolvedCallTarget}
    {decls : List LocalDecl} {layouts : LayoutTable} {argOps : List Operand}
    {args : List SymVal} {r : SymScalar} {cs : List SymCond}
    (h : symIntrinsic kind target decls layouts argOps args = some (r, cs)) (env : SymEnv)
    (hc : condsHold env cs) (s : MachineState) (locals' : List LocalSlot) (dst : Place)
    (bb : BasicBlockIdx) :
    evalNonSelectIntrinsicCall kind s target decls layouts argOps (symValsEval env args)
      locals' dst bb = writeIntrinsicReturn s locals' dst bb (.scalar (r.eval env)) := by
  cases kind with
  | ubChecks =>
    simp only [symIntrinsic] at h
    cases args with
    | cons _ _ => nomatch h
    | nil =>
      injection h with h
      injection h with h1 _
      subst h1
      rfl
  | ctlz =>
    obtain ⟨a, x, rfl, hx, rfl, rfl⟩ := symUn_shape h
    rw [symValsEval_one hx env]
    exact writeIntrinsicScalarResult_some s locals' dst bb (evalCtlz_isSome hc.1)
  | cttz =>
    obtain ⟨a, x, rfl, hx, rfl, rfl⟩ := symUn_shape h
    rw [symValsEval_one hx env]
    exact writeIntrinsicScalarResult_some s locals' dst bb (evalCttz_isSome hc.1)
  | ctpop =>
    obtain ⟨a, x, rfl, hx, rfl, rfl⟩ := symUn_shape h
    rw [symValsEval_one hx env]
    exact writeIntrinsicScalarResult_some s locals' dst bb (evalCtpop_isSome hc.1)
  | bswap =>
    obtain ⟨a, x, rfl, hx, rfl, rfl⟩ := symUn_shape h
    rw [symValsEval_one hx env]
    exact writeIntrinsicScalarResult_some s locals' dst bb (evalBswap_isSome hc.1)
  | bitreverse =>
    obtain ⟨a, x, rfl, hx, rfl, rfl⟩ := symUn_shape h
    rw [symValsEval_one hx env]
    exact writeIntrinsicScalarResult_some s locals' dst bb (evalBitreverse_isSome hc.1)
  | ctlzNonzero =>
    obtain ⟨a, x, rfl, hx, rfl, rfl⟩ := symUn_shape h
    rw [symValsEval_one hx env]
    exact writeIntrinsicScalarResult_some s locals' dst bb
      (evalCtlzNonzero_isSome hc.1.1 hc.1.2)
  | cttzNonzero =>
    obtain ⟨a, x, rfl, hx, rfl, rfl⟩ := symUn_shape h
    rw [symValsEval_one hx env]
    exact writeIntrinsicScalarResult_some s locals' dst bb
      (evalCttzNonzero_isSome hc.1.1 hc.1.2)
  | wrappingAdd =>
    obtain ⟨a, b, x, y, rfl, hx, hy, rfl, rfl⟩ := symBin_shape h
    rw [symValsEval_two hx hy env]
    rw [SymScalar.eval_wrappingOp]
    exact writeIntrinsicScalarResult_some s locals' dst bb (symWrapEval_isSome .add hc.1)
  | wrappingSub =>
    obtain ⟨a, b, x, y, rfl, hx, hy, rfl, rfl⟩ := symBin_shape h
    rw [symValsEval_two hx hy env]
    rw [SymScalar.eval_wrappingOp]
    exact writeIntrinsicScalarResult_some s locals' dst bb (symWrapEval_isSome .sub hc.1)
  | wrappingMul =>
    obtain ⟨a, b, x, y, rfl, hx, hy, rfl, rfl⟩ := symBin_shape h
    rw [symValsEval_two hx hy env]
    rw [SymScalar.eval_wrappingOp]
    exact writeIntrinsicScalarResult_some s locals' dst bb (symWrapEval_isSome .mul hc.1)
  | saturatingAdd =>
    simp only [symIntrinsic] at h
    cases hs : resolveIntrinsicIsSigned target decls layouts argOps with
    | none => rw [hs] at h; nomatch h
    | some sg =>
      rw [hs] at h
      obtain ⟨a, b, x, y, rfl, hx, hy, rfl, rfl⟩ := symBin_shape h
      rw [symValsEval_two hx hy env]
      dsimp only [evalNonSelectIntrinsicCall]
      rw [hs]
      rw [SymScalar.eval_saturatingOp]
      exact writeIntrinsicScalarResult_some s locals' dst bb (symSatEval_isSome .add sg hc.1)
  | saturatingSub =>
    simp only [symIntrinsic] at h
    cases hs : resolveIntrinsicIsSigned target decls layouts argOps with
    | none => rw [hs] at h; nomatch h
    | some sg =>
      rw [hs] at h
      obtain ⟨a, b, x, y, rfl, hx, hy, rfl, rfl⟩ := symBin_shape h
      rw [symValsEval_two hx hy env]
      dsimp only [evalNonSelectIntrinsicCall]
      rw [hs]
      rw [SymScalar.eval_saturatingOp]
      exact writeIntrinsicScalarResult_some s locals' dst bb (symSatEval_isSome .sub sg hc.1)
  | uncheckedAdd =>
    simp only [symIntrinsic] at h
    cases hs : resolveIntrinsicIsSigned target decls layouts argOps with
    | none => rw [hs] at h; nomatch h
    | some sg =>
      rw [hs] at h
      obtain ⟨a, b, x, y, rfl, hx, hy, rfl, rfl⟩ := symBin_shape h
      rw [symValsEval_two hx hy env]
      dsimp only [evalNonSelectIntrinsicCall]
      rw [hs]
      rw [SymScalar.eval_uncheckedOp]
      exact writeIntrinsicScalarResult_some s locals' dst bb
        (evalUncheckedAdd_isSome hc.1.1 hc.1.2)
  | uncheckedSub =>
    simp only [symIntrinsic] at h
    cases hs : resolveIntrinsicIsSigned target decls layouts argOps with
    | none => rw [hs] at h; nomatch h
    | some sg =>
      rw [hs] at h
      obtain ⟨a, b, x, y, rfl, hx, hy, rfl, rfl⟩ := symBin_shape h
      rw [symValsEval_two hx hy env]
      dsimp only [evalNonSelectIntrinsicCall]
      rw [hs]
      rw [SymScalar.eval_uncheckedOp]
      exact writeIntrinsicScalarResult_some s locals' dst bb
        (evalUncheckedSub_isSome hc.1.1 hc.1.2)
  | uncheckedMul =>
    simp only [symIntrinsic] at h
    cases hs : resolveIntrinsicIsSigned target decls layouts argOps with
    | none => rw [hs] at h; nomatch h
    | some sg =>
      rw [hs] at h
      obtain ⟨a, b, x, y, rfl, hx, hy, rfl, rfl⟩ := symBin_shape h
      rw [symValsEval_two hx hy env]
      dsimp only [evalNonSelectIntrinsicCall]
      rw [hs]
      rw [SymScalar.eval_uncheckedOp]
      exact writeIntrinsicScalarResult_some s locals' dst bb
        (evalUncheckedMul_isSome hc.1.1 hc.1.2)
  | uncheckedDiv =>
    simp only [symIntrinsic] at h
    cases hs : resolveIntrinsicIsSigned target decls layouts argOps with
    | none => rw [hs] at h; nomatch h
    | some sg =>
      rw [hs] at h
      obtain ⟨a, b, x, y, rfl, hx, hy, rfl, rfl⟩ := symBin_shape h
      rw [symValsEval_two hx hy env]
      dsimp only [evalNonSelectIntrinsicCall]
      rw [hs]
      rw [SymScalar.eval_uncheckedOp]
      exact writeIntrinsicScalarResult_some s locals' dst bb
        (evalUncheckedDiv_isSome hc.1.1 hc.1.2.1 hc.1.2.2)
  | uncheckedRem =>
    simp only [symIntrinsic] at h
    cases hs : resolveIntrinsicIsSigned target decls layouts argOps with
    | none => rw [hs] at h; nomatch h
    | some sg =>
      rw [hs] at h
      obtain ⟨a, b, x, y, rfl, hx, hy, rfl, rfl⟩ := symBin_shape h
      rw [symValsEval_two hx hy env]
      dsimp only [evalNonSelectIntrinsicCall]
      rw [hs]
      rw [SymScalar.eval_uncheckedOp]
      exact writeIntrinsicScalarResult_some s locals' dst bb
        (evalUncheckedRem_isSome hc.1.1 hc.1.2.1 hc.1.2.2)
  | uncheckedShl =>
    simp only [symIntrinsic] at h
    cases hs : resolveIntrinsicShiftSigned target decls layouts argOps with
    | none => rw [hs] at h; nomatch h
    | some rs =>
      rw [hs] at h
      obtain ⟨a, b, x, y, rfl, hx, hy, rfl, rfl⟩ := symBin_shape h
      rw [symValsEval_two hx hy env]
      dsimp only [evalNonSelectIntrinsicCall]
      rw [hs]
      rw [SymScalar.eval_uncheckedOp]
      exact writeIntrinsicScalarResult_some s locals' dst bb
        (evalUncheckedShl_isSome hc.1.1 hc.1.2.1 hc.1.2.2.1 hc.1.2.2.2)
  | uncheckedShr =>
    simp only [symIntrinsic] at h
    cases hs : resolveIntrinsicIsSigned target decls layouts argOps (sameRhsTy := false) with
    | none => rw [hs] at h; nomatch h
    | some ls =>
      cases hr : resolveIntrinsicShiftSigned target decls layouts argOps with
      | none => rw [hs, hr] at h; nomatch h
      | some rs =>
        rw [hs, hr] at h
        obtain ⟨a, b, x, y, rfl, hx, hy, rfl, rfl⟩ := symBin_shape h
        rw [symValsEval_two hx hy env]
        dsimp only [evalNonSelectIntrinsicCall]
        rw [hs, hr]
        rw [SymScalar.eval_uncheckedOp]
        exact writeIntrinsicScalarResult_some s locals' dst bb
          (evalUncheckedShr_isSome hc.1.1 hc.1.2.1 hc.1.2.2.1 hc.1.2.2.2)
  | constEvalSelect => nomatch h
  | arithOffset => nomatch h
  | threeWayCompare => nomatch h
  | sizeOfVal => nomatch h
  | alignOfVal => nomatch h
  | copyNonOverlapping => nomatch h
  | writeBytes => nomatch h

/-! ## Part IX: Terminator Soundness against `evalTerminator` -/

theorem symOperand_bodyCast_sound {globals : List CapturedAllocation} {layouts : LayoutTable}
    {locals : List SymSlot} {op : Operand} {v : SymVal} {locals' : List SymSlot}
    (h : symOperand globals layouts locals op = some (v, locals')) (env : SymEnv)
    (borrows : List BorrowEntry) (callerLocals : List LocalSlot) (decls : List LocalDecl)
    (callStack : List SavedCallerFrame) :
    evalOperandWithBodyCast (symSlotsEval env locals) op borrows globals layouts callerLocals
      decls callStack = .ok (v.eval env) (symSlotsEval env locals') := by
  unfold evalOperandWithBodyCast
  rw [symOperand_shape h]
  exact symOperand_sound h env borrows callerLocals [] callStack

theorem evalDirectRustIntrinsic?_of_sym {kind : RustIntrinsicKind}
    {target : ResolvedCallTarget} {decls : List LocalDecl} {layouts : LayoutTable}
    {argOps : List Operand} {args : List SymVal} {rr : SymScalar × List SymCond}
    (hk : classifyRustIntrinsic? target.defPath = some kind)
    (hi : symIntrinsic kind target decls layouts argOps args = some rr)
    (s : MachineState) (cb : Option CapturedMir) (argVals : List Value)
    (locals' : List LocalSlot) (dst : Place) (bb : BasicBlockIdx) (unwind : UnwindAction) :
    evalDirectRustIntrinsic? s cb target decls layouts argOps argVals locals' dst bb unwind =
      some (evalNonSelectIntrinsicCall kind s target decls layouts argOps argVals locals' dst
        bb) := by
  unfold evalDirectRustIntrinsic?
  rw [hk]
  cases kind <;> first | rfl | nomatch hi

theorem symTerm_step_sound {cfg : SymConfig} {p : SymProg} {body : CapturedMir}
    {term : Terminator} {p' : SymProg} {cs : List SymCond}
    (h : symTerm cfg p body term = .step p' cs) (env : SymEnv) (hc : condsHold env cs) :
    ∃ obs, evalTerminator (p.toMachineState cfg env) term (some body) =
      MirStepNode.emitStep obs (p'.toMachineState cfg env) := by
  obtain ⟨kind, span⟩ := term
  cases kind with
  | goto t =>
    simp only [symTerm] at h
    injection h with h1 _
    subst h1
    exact ⟨.silent, rfl⟩
  | switchInt discr targets =>
    simp only [symTerm] at h
    cases ho : symOperand cfg.body.allocations body.layouts p.frame.locals discr with
    | none => rw [ho] at h; nomatch h
    | some r =>
      obtain ⟨v, locals'⟩ := r
      rw [ho] at h
      dsimp only at h
      cases ha : v.asScalar? with
      | none => rw [ha] at h; nomatch h
      | some a =>
        rw [ha] at h
        dsimp only at h
        cases hk : a.asConst? with
        | none => rw [hk] at h; nomatch h
        | some sc =>
          rw [hk] at h
          injection h with h1 _
          subst h1
          dsimp only [evalTerminator, SymProg.toMachineState, SymProg.toMemory, SymFrame.eval]
          rw [symOperand_bodyCast_sound ho env, symVal_eval_of_asScalar ha env,
            symScalar_eval_of_asConst hk env]
          exact ⟨_, rfl⟩
  | assert cond expected target unwind =>
    simp only [symTerm] at h
    cases ho : symOperand cfg.body.allocations body.layouts p.frame.locals cond with
    | none => rw [ho] at h; nomatch h
    | some r =>
      obtain ⟨v, locals'⟩ := r
      rw [ho] at h
      dsimp only at h
      cases ha : v.asScalar? with
      | none => rw [ha] at h; nomatch h
      | some c =>
        rw [ha] at h
        injection h with h1 h2
        subst h1
        subst h2
        dsimp only [evalTerminator, SymProg.toMachineState, SymProg.toMemory, SymFrame.eval]
        rw [symOperand_bodyCast_sound ho env, symVal_eval_of_asScalar ha env]
        refine ⟨.silent, ?_⟩
        cases expected with
        | true =>
          have h1 : (c.eval env).bits = 1 := hc.1
          dsimp only
          rw [nat_beq_true_of_eq h1]
          rfl
        | false =>
          have h1 : (c.eval env).bits = 0 := hc.1
          dsimp only
          rw [nat_beq_true_of_eq h1]
          rfl
  | return_ =>
    simp only [symTerm] at h
    cases hg : get? p.frame.locals 0 with
    | none => rw [hg] at h; nomatch h
    | some sl =>
      rw [hg] at h
      cases sl with
      | dead => nomatch h
      | uninit => nomatch h
      | init v =>
        dsimp only at h
        cases hu : v.containsUninit with
        | true => rw [hu] at h; nomatch h
        | false =>
          rw [hu] at h
          dsimp only at h
          cases hs : p.stack with
          | nil => rw [hs] at h; nomatch h
          | cons caller rest =>
            rw [hs] at h
            obtain ⟨cb, cf, ⟨dloc, dproj⟩, rt, ru⟩ := caller
            cases dproj with
            | cons _ _ => nomatch h
            | nil =>
              dsimp only at h
              cases hg2 : get? cf.locals dloc with
              | none => rw [hg2] at h; nomatch h
              | some sl2 =>
                rw [hg2] at h
                cases sl2 with
                | dead => nomatch h
                | uninit | init _ =>
                  dsimp only at h
                  cases hw : set? cf.locals dloc (.init v) with
                  | none => rw [hw] at h; nomatch h
                  | some l' =>
                    rw [hw] at h
                    injection h with h1 _
                    subst h1
                    refine ⟨.silent, ?_⟩
                    simp only [evalTerminator, SymProg.toMachineState, SymProg.toMemory,
                      SymFrame.eval, get?_symSlotsEval, hg, Option.map, SymSlot.eval,
                      hasFrameDeallocProtectorConflict, disableFrameBorrows, hs, symStackEval_cons,
                      SymSaved.eval, valueContainsUninit_symVal, hu, restoreCallerProtectors,
                      writeReturnDestination, hg2, hasProtectedWriteConflict,
                      set?_symSlotsEval_init, hw, invalidateConflictingBorrows]
                    rfl
  | call func argOps destination target unwind =>
    cases target with
    | none => nomatch h
    | some targetBb =>
      simp only [symTerm] at h
      cases hf : extractCalleeDefPath? func with
      | none => rw [hf] at h; nomatch h
      | some defPath =>
        rw [hf] at h
        dsimp only at h
        cases ho : symOperands cfg.body.allocations body.layouts p.frame.locals argOps with
        | none => rw [ho] at h; nomatch h
        | some r =>
          obtain ⟨args, locals'⟩ := r
          rw [ho] at h
          dsimp only at h
          cases hl : lookupCallee cfg.callees body.layouts defPath (extractCalleeTypeArgs func)
              cfg.body.traitImpls with
          | some calleeBody =>
            rw [hl] at h
            injection h with h1 _
            subst h1
            refine ⟨.silent, ?_⟩
            simp only [evalTerminator, SymProg.toMachineState, SymProg.toMemory, SymFrame.eval,
              resolveCallTarget, hf, bodyLocalDeclsOf]
            rw [symOperands_sound env _ _ _ _ ho]
            simp only [hl, checkCalleeTargetCompatible_direct, pushCalleeFrame, initLocals,
              ← symSlotsEval_symInitLocalsAux]
            rfl
          | none =>
            rw [hl] at h
            dsimp only at h
            cases hx : isDirectExactDivTarget
                { defPath := defPath, typeArgs := extractCalleeTypeArgs func, fnSig := none,
                  isIndirect := false } with
            | true => rw [hx] at h; nomatch h
            | false =>
              rw [hx] at h
              dsimp only at h
              cases hk : classifyRustIntrinsic? defPath with
              | none => rw [hk] at h; nomatch h
              | some kind =>
                rw [hk] at h
                dsimp only at h
                cases hi : symIntrinsic kind
                    { defPath := defPath, typeArgs := extractCalleeTypeArgs func, fnSig := none,
                      isIndirect := false } body.localDecls body.layouts argOps args with
                | none => rw [hi] at h; nomatch h
                | some rr =>
                  obtain ⟨res, cs'⟩ := rr
                  rw [hi] at h
                  dsimp only at h
                  obtain ⟨dloc, dproj⟩ := destination
                  cases dproj with
                  | cons _ _ => nomatch h
                  | nil =>
                    dsimp only at h
                    cases hg : get? locals' dloc with
                    | none => rw [hg] at h; nomatch h
                    | some sl =>
                      rw [hg] at h
                      cases sl with
                      | dead => nomatch h
                      | uninit | init _ =>
                        dsimp only at h
                        cases hw : set? locals' dloc (.init (.scalar res)) with
                        | none => rw [hw] at h; nomatch h
                        | some l₂ =>
                          rw [hw] at h
                          injection h with h1 h2
                          subst h1
                          subst h2
                          refine ⟨.silent, ?_⟩
                          simp only [evalTerminator, SymProg.toMachineState, SymProg.toMemory,
                            SymFrame.eval, resolveCallTarget, hf, bodyLocalDeclsOf]
                          rw [symOperands_sound env _ _ _ _ ho]
                          simp only [hl, hx]
                          rw [evalDirectRustIntrinsic?_of_sym hk hi]
                          dsimp only
                          rw [symIntrinsic_sound hi env hc]
                          simp only [writeIntrinsicReturn, writePlaceValue, get?_symSlotsEval, hg,
                            Option.map, SymSlot.eval, invalidateDirectDestWriteBorrows]
                          rw [show (LocalSlot.init (Value.scalar (res.eval env))) =
                            SymSlot.eval env (.init (.scalar res)) from rfl,
                            set?_symSlotsEval, hw]
                          rfl
  | _ => nomatch h

theorem symTerm_ret_sound {cfg : SymConfig} {p : SymProg} {body : CapturedMir}
    {term : Terminator} {v : SymVal} {fin : SymProg} {cs : List SymCond}
    (h : symTerm cfg p body term = .ret v fin cs) (env : SymEnv) :
    fin = p ∧ cs = [] ∧
      evalTerminator (p.toMachineState cfg env) term (some body) =
        MirStepNode.retNormal (v.eval env) (p.toMachineState cfg env).memory := by
  obtain ⟨kind, span⟩ := term
  cases kind with
  | return_ =>
    simp only [symTerm] at h
    cases hg : get? p.frame.locals 0 with
    | none => rw [hg] at h; nomatch h
    | some sl =>
      rw [hg] at h
      cases sl with
      | dead => nomatch h
      | uninit => nomatch h
      | init w =>
        dsimp only at h
        cases hu : w.containsUninit with
        | true => rw [hu] at h; nomatch h
        | false =>
          rw [hu] at h
          dsimp only at h
          cases hs : p.stack with
          | cons caller rest =>
            rw [hs] at h
            dsimp only at h
            repeat' (first | contradiction | split at h)
          | nil =>
            rw [hs] at h
            injection h with h1 h2 h3
            subst h1
            subst h2
            subst h3
            refine ⟨rfl, rfl, ?_⟩
            simp only [evalTerminator, SymProg.toMachineState, SymProg.toMemory,
              SymFrame.eval, get?_symSlotsEval, hg, Option.map, SymSlot.eval,
              hasFrameDeallocProtectorConflict, disableFrameBorrows, hs, symStackEval_nil,
              valueContainsUninit_symVal, hu]
  | goto _ => nomatch h
  | switchInt _ _ =>
    simp only [symTerm] at h
    repeat' (first | contradiction | split at h)
  | assert _ _ _ _ =>
    simp only [symTerm] at h
    repeat' (first | contradiction | split at h)
  | call _ _ _ target _ =>
    cases target with
    | none => nomatch h
    | some _ =>
      simp only [symTerm] at h
      repeat' (first | contradiction | split at h)
  | _ => nomatch h

theorem symSwitchAlts_sound (p : SymProg) (d : SymScalar) (l : List SymSlot)
    (o : BasicBlockIdx) (env : SymEnv) :
    ∀ (prior : List Nat) (bs : List (Nat × BasicBlockIdx)) (c : SymCond) (q : SymProg),
      (c, q) ∈ symSwitchAlts p d l o prior bs → c.holds env →
      (∀ u, u ∈ prior → (d.eval env).bits ≠ u) ∧
        q = p.jump (lookupSwitchTarget (d.eval env).bits bs o) l
  | prior, [], c, q, hm, hh => by
    cases hm with
    | head => exact ⟨hh, rfl⟩
    | tail _ hm' => nomatch hm'
  | prior, (v, t) :: rest, c, q, hm, hh => by
    cases hm with
    | head =>
      obtain ⟨hv, hp⟩ := hh
      refine ⟨hp, ?_⟩
      show p.jump t l = p.jump (match Nat.beq (d.eval env).bits v with
        | true => t | false => lookupSwitchTarget (d.eval env).bits rest o) l
      rw [nat_beq_true_of_eq hv]
    | tail _ hm' =>
      obtain ⟨hp, hq⟩ := symSwitchAlts_sound p d l o env (prior ++ [v]) rest c q hm' hh
      have hne : (d.eval env).bits ≠ v :=
        hp v (List.mem_append_right prior (List.Mem.head []))
      refine ⟨fun u hu => hp u (List.mem_append_left [v] hu), ?_⟩
      rw [hq]
      show p.jump (lookupSwitchTarget (d.eval env).bits rest o) l =
        p.jump (match Nat.beq (d.eval env).bits v with
          | true => t | false => lookupSwitchTarget (d.eval env).bits rest o) l
      rw [nat_beq_false_of_ne hne]

theorem symTerm_branch_sound {cfg : SymConfig} {p : SymProg} {body : CapturedMir}
    {term : Terminator} {alts : List (SymCond × SymProg)} {cs : List SymCond}
    (h : symTerm cfg p body term = .branch alts cs) (env : SymEnv) :
    cs = [] ∧ ∀ c q, (c, q) ∈ alts → c.holds env →
      ∃ obs, evalTerminator (p.toMachineState cfg env) term (some body) =
        MirStepNode.emitStep obs (q.toMachineState cfg env) := by
  obtain ⟨kind, span⟩ := term
  cases kind with
  | switchInt discr targets =>
    simp only [symTerm] at h
    cases ho : symOperand cfg.body.allocations body.layouts p.frame.locals discr with
    | none => rw [ho] at h; nomatch h
    | some r =>
      obtain ⟨v, locals'⟩ := r
      rw [ho] at h
      dsimp only at h
      cases ha : v.asScalar? with
      | none => rw [ha] at h; nomatch h
      | some a =>
        rw [ha] at h
        dsimp only at h
        cases hk : a.asConst? with
        | some sc => rw [hk] at h; nomatch h
        | none =>
          rw [hk] at h
          injection h with h1 h2
          subst h1
          subst h2
          refine ⟨rfl, fun c q hm hh => ?_⟩
          obtain ⟨_, hq⟩ := symSwitchAlts_sound p a locals' targets.otherwise env [] _ c q hm hh
          subst hq
          dsimp only [evalTerminator, SymProg.toMachineState, SymProg.toMemory, SymFrame.eval]
          rw [symOperand_bodyCast_sound ho env, symVal_eval_of_asScalar ha env]
          exact ⟨_, rfl⟩
  | goto _ => nomatch h
  | return_ =>
    simp only [symTerm] at h
    repeat' (first | contradiction | split at h)
  | assert _ _ _ _ =>
    simp only [symTerm] at h
    repeat' (first | contradiction | split at h)
  | call _ _ _ target _ =>
    cases target with
    | none => nomatch h
    | some _ =>
      simp only [symTerm] at h
      repeat' (first | contradiction | split at h)
  | _ => nomatch h

/-! ## Part X: Whole-Step Soundness against `stepMirFn` / `v2026Step` -/

/-- `stepMirFn` on a denoted symbolic program, with every env-independent
projection already reduced (definitional). -/
theorem stepMirFn_toMachineState (cfg : SymConfig) (p : SymProg) (env : SymEnv) :
    stepMirFn cfg.body (p.toMachineState cfg env) =
      match (p.active.getD cfg.body).phase with
      | .other _ => MirStepNode.unsupported
      | _ =>
        match get? (p.active.getD cfg.body).basicBlocks p.frame.blockIdx with
        | none => MirStepNode.fail .ub
        | some bb =>
          match get? bb.statements p.frame.stmtIdx with
          | some stmt =>
            evalStmt (p.toMachineState cfg env) stmt (p.active.getD cfg.body).localDecls
              (p.active.getD cfg.body).layouts
          | none =>
            if p.frame.stmtIdx == length bb.statements then
              evalTerminator (p.toMachineState cfg env) bb.terminator
                (some (p.active.getD cfg.body))
            else
              MirStepNode.fail .ub :=
  rfl

/-- Dispatch lemma: the trusted step at a supported program point is the
statement / terminator step the symbolic engine analyzed. -/
theorem symProgStep_dispatch {cfg : SymConfig} {p : SymProg} {r : SymStepRes}
    (h : symProgStep cfg p = r) (hr : r ≠ .stuck) (env : SymEnv) :
    ∃ bb, get? (p.active.getD cfg.body).basicBlocks p.frame.blockIdx = some bb ∧
      ((∃ stmt f' cs, get? bb.statements p.frame.stmtIdx = some stmt ∧
          symStmt cfg.body.allocations (p.active.getD cfg.body) p.frame stmt = some (f', cs) ∧
          r = .step { p with frame := f' } cs ∧
          stepMirFn cfg.body (p.toMachineState cfg env) =
            evalStmt (p.toMachineState cfg env) stmt (p.active.getD cfg.body).localDecls
              (p.active.getD cfg.body).layouts) ∨
        (symTerm cfg p (p.active.getD cfg.body) bb.terminator = r ∧
          stepMirFn cfg.body (p.toMachineState cfg env) =
            evalTerminator (p.toMachineState cfg env) bb.terminator
              (some (p.active.getD cfg.body)))) := by
  unfold symProgStep at h
  dsimp only at h
  rw [stepMirFn_toMachineState]
  cases hph : (p.active.getD cfg.body).phase with
  | other _ =>
    rw [hph] at h
    exact absurd h.symm hr
  | runtimePostCleanup | runtimeOptimized =>
    rw [hph] at h
    dsimp only at h ⊢
    cases hb : get? (p.active.getD cfg.body).basicBlocks p.frame.blockIdx with
    | none =>
      rw [hb] at h
      exact absurd h.symm hr
    | some bb =>
      rw [hb] at h
      dsimp only at h ⊢
      refine ⟨bb, rfl, ?_⟩
      cases hs : get? bb.statements p.frame.stmtIdx with
      | some stmt =>
        rw [hs] at h
        dsimp only at h ⊢
        cases hst : symStmt cfg.body.allocations (p.active.getD cfg.body) p.frame stmt with
        | none =>
          rw [hst] at h
          exact absurd h.symm hr
        | some fc =>
          obtain ⟨f', cs⟩ := fc
          rw [hst] at h
          exact Or.inl ⟨stmt, f', cs, rfl, hst, h.symm, rfl⟩
      | none =>
        rw [hs] at h
        dsimp only at h ⊢
        cases hl : (p.frame.stmtIdx == length bb.statements) with
        | false =>
          rw [hl] at h
          exact absurd h.symm hr
        | true =>
          rw [hl] at h
          exact Or.inr ⟨h, rfl⟩

/-- **Single-step soundness** against unmodified `stepMirFn`. -/
theorem symProgStep_sound {cfg : SymConfig} {p p' : SymProg} {cs : List SymCond}
    (h : symProgStep cfg p = .step p' cs) (env : SymEnv) (hc : condsHold env cs) :
    ∃ obs, stepMirFn cfg.body (p.toMachineState cfg env) =
      MirStepNode.emitStep obs (p'.toMachineState cfg env) := by
  obtain ⟨bb, _, hcase⟩ := symProgStep_dispatch h (fun h' => SymStepRes.noConfusion h') env
  rcases hcase with ⟨stmt, f', cs', _, hst, hr, hstep⟩ | ⟨ht, hstep⟩
  · injection hr with h1 _
    subst h1
    rw [hstep, symStmt_sound hst env]
    exact ⟨.silent, rfl⟩
  · rw [hstep]
    exact symTerm_step_sound ht env hc

/-- Single-step soundness lifted to Episode 1's `v2026Step`. -/
theorem symProgStep_v2026_sound {cfg : SymConfig} {p p' : SymProg} {cs : List SymCond}
    (h : symProgStep cfg p = .step p' cs) (env : SymEnv) (hc : condsHold env cs) :
    v2026Step cfg.body (p.toMachineState cfg env) = .step (p'.toMachineState cfg env) := by
  obtain ⟨obs, hs⟩ := symProgStep_sound h env hc
  unfold v2026Step
  rw [hs]
  exact ofV2026MirStepNode_emitStep obs _

/-- Root-return soundness against unmodified `stepMirFn`. -/
theorem symProgStep_ret_sound {cfg : SymConfig} {p : SymProg} {v : SymVal} {fin : SymProg}
    {cs : List SymCond} (h : symProgStep cfg p = .ret v fin cs) (env : SymEnv) :
    fin = p ∧ cs = [] ∧
      stepMirFn cfg.body (p.toMachineState cfg env) =
        MirStepNode.retNormal (v.eval env) (p.toMachineState cfg env).memory := by
  obtain ⟨bb, _, hcase⟩ := symProgStep_dispatch h (fun h' => SymStepRes.noConfusion h') env
  rcases hcase with ⟨_, _, _, _, _, hr, _⟩ | ⟨ht, hstep⟩
  · nomatch hr
  · rw [hstep]
    exact symTerm_ret_sound ht env

/-- Root-return soundness lifted to `v2026Step`. -/
theorem symProgStep_ret_v2026_sound {cfg : SymConfig} {p : SymProg} {v : SymVal}
    {fin : SymProg} {cs : List SymCond} (h : symProgStep cfg p = .ret v fin cs) (env : SymEnv) :
    v2026Step cfg.body (p.toMachineState cfg env) =
      .done (.normal (v.eval env, (p.toMachineState cfg env).memory)) := by
  obtain ⟨_, _, hs⟩ := symProgStep_ret_sound h env
  unfold v2026Step
  rw [hs]
  rfl

/-- Fork soundness: every enabled alternative is the trusted successor. -/
theorem symProgStep_branch_sound {cfg : SymConfig} {p : SymProg}
    {alts : List (SymCond × SymProg)} {cs : List SymCond}
    (h : symProgStep cfg p = .branch alts cs) (env : SymEnv) :
    cs = [] ∧ ∀ c q, (c, q) ∈ alts → c.holds env →
      v2026Step cfg.body (p.toMachineState cfg env) = .step (q.toMachineState cfg env) := by
  obtain ⟨bb, _, hcase⟩ := symProgStep_dispatch h (fun h' => SymStepRes.noConfusion h') env
  rcases hcase with ⟨_, _, _, _, _, hr, _⟩ | ⟨ht, hstep⟩
  · nomatch hr
  · obtain ⟨hcs, halts⟩ := symTerm_branch_sound ht env
    refine ⟨hcs, fun c q hm hh => ?_⟩
    obtain ⟨obs, ho⟩ := halts c q hm hh
    unfold v2026Step
    rw [hstep, ho]
    exact ofV2026MirStepNode_emitStep obs _

/-! ## Part XI: Chunked Runner Laws and Multi-Step Soundness -/

theorem condsHold_append (env : SymEnv) :
    ∀ (a b : List SymCond), condsHold env (a ++ b) ↔ condsHold env a ∧ condsHold env b
  | [], _ => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | _ :: rest, b =>
    ⟨fun h => ⟨⟨h.1, ((condsHold_append env rest b).mp h.2).1⟩,
        ((condsHold_append env rest b).mp h.2).2⟩,
     fun h => ⟨h.1.1, (condsHold_append env rest b).mpr ⟨h.1.2, h.2⟩⟩⟩

theorem SymStepRes.addConds_nil : ∀ r : SymStepRes, r.addConds [] = r
  | .step _ _ => rfl
  | .ret _ _ _ => rfl
  | .branch _ _ => rfl
  | .stuck => rfl

theorem SymStepRes.addConds_addConds (cs cs' : List SymCond) :
    ∀ r : SymStepRes, (r.addConds cs').addConds cs = r.addConds (cs ++ cs')
  | .step p c => by simp only [SymStepRes.addConds, List.append_assoc]
  | .ret v f c => by simp only [SymStepRes.addConds, List.append_assoc]
  | .branch a c => by simp only [SymStepRes.addConds, List.append_assoc]
  | .stuck => rfl

theorem SymStepRes.bindRun_addConds (g : SymProg → SymStepRes) (cs : List SymCond) :
    ∀ r : SymStepRes, (r.addConds cs).bindRun g = (r.bindRun g).addConds cs
  | .step p c => by
    show (g p).addConds (cs ++ c) = ((g p).addConds c).addConds cs
    rw [SymStepRes.addConds_addConds]
  | .ret _ _ _ => rfl
  | .branch _ _ => rfl
  | .stuck => rfl

theorem SymStepRes.bindRun_assoc (f g : SymProg → SymStepRes) :
    ∀ r : SymStepRes, (r.bindRun f).bindRun g = r.bindRun (fun q => (f q).bindRun g)
  | .step p c => SymStepRes.bindRun_addConds g c (f p)
  | .ret _ _ _ => rfl
  | .branch _ _ => rfl
  | .stuck => rfl

theorem symProgRunSteps_zero (cfg : SymConfig) (p : SymProg) :
    symProgRunSteps cfg 0 p = .step p [] := rfl

theorem symProgRunSteps_succ (cfg : SymConfig) (k : Nat) (p : SymProg) :
    symProgRunSteps cfg (k + 1) p = (symProgStep cfg p).bindRun (symProgRunSteps cfg k) :=
  rfl

theorem symProgRunSteps_add (cfg : SymConfig) :
    ∀ (k₁ k₂ : Nat) (p : SymProg),
      symProgRunSteps cfg (k₁ + k₂) p =
        (symProgRunSteps cfg k₁ p).bindRun (symProgRunSteps cfg k₂)
  | 0, k₂, p => by
    rw [Nat.zero_add, symProgRunSteps_zero]
    show symProgRunSteps cfg k₂ p = (symProgRunSteps cfg k₂ p).addConds []
    rw [SymStepRes.addConds_nil]
  | k₁ + 1, k₂, p => by
    rw [Nat.succ_add, symProgRunSteps_succ, symProgRunSteps_succ, SymStepRes.bindRun_assoc]
    have ih : symProgRunSteps cfg (k₁ + k₂) =
        fun q => (symProgRunSteps cfg k₁ q).bindRun (symProgRunSteps cfg k₂) :=
      funext (symProgRunSteps_add cfg k₁ k₂)
    rw [ih]

theorem symProgRunSteps_trans {cfg : SymConfig} {k₁ k₂ : Nat} {p q : SymProg}
    {cs₁ : List SymCond} {r : SymStepRes}
    (h₁ : symProgRunSteps cfg k₁ p = .step q cs₁) (h₂ : symProgRunSteps cfg k₂ q = r) :
    symProgRunSteps cfg (k₁ + k₂) p = r.addConds cs₁ := by
  rw [symProgRunSteps_add, h₁]
  show (symProgRunSteps cfg k₂ q).addConds cs₁ = r.addConds cs₁
  rw [h₂]

theorem addConds_eq_step {r : SymStepRes} {cs₁ cs : List SymCond} {q : SymProg}
    (h : r.addConds cs₁ = .step q cs) : ∃ cs₂, r = .step q cs₂ ∧ cs = cs₁ ++ cs₂ := by
  cases r with
  | step q' c =>
    injection h with h1 h2
    exact ⟨c, h1 ▸ rfl, h2.symm⟩
  | ret _ _ _ => nomatch h
  | branch _ _ => nomatch h
  | stuck => nomatch h

theorem addConds_eq_ret {r : SymStepRes} {cs₁ cs : List SymCond} {v : SymVal} {fin : SymProg}
    (h : r.addConds cs₁ = .ret v fin cs) : ∃ cs₂, r = .ret v fin cs₂ ∧ cs = cs₁ ++ cs₂ := by
  cases r with
  | ret v' f' c =>
    injection h with h1 h2 h3
    exact ⟨c, h1 ▸ h2 ▸ rfl, h3.symm⟩
  | step _ _ => nomatch h
  | branch _ _ => nomatch h
  | stuck => nomatch h

theorem addConds_eq_branch {r : SymStepRes} {cs₁ cs : List SymCond}
    {alts : List (SymCond × SymProg)}
    (h : r.addConds cs₁ = .branch alts cs) : ∃ cs₂, r = .branch alts cs₂ ∧ cs = cs₁ ++ cs₂ := by
  cases r with
  | branch a c =>
    injection h with h1 h2
    exact ⟨c, h1 ▸ rfl, h2.symm⟩
  | step _ _ => nomatch h
  | ret _ _ _ => nomatch h
  | stuck => nomatch h

/-- **`k`-step soundness**: a symbolic `k`-step run refines an exact
`StepsToV2026` trace of unmodified `v2026Step` / `stepMirFn`. -/
theorem symProgRunSteps_sound (cfg : SymConfig) (env : SymEnv) :
    ∀ (k : Nat) {p q : SymProg} {cs : List SymCond},
      symProgRunSteps cfg k p = .step q cs → condsHold env cs →
      StepsToV2026 cfg.body k (p.toMachineState cfg env) (q.toMachineState cfg env)
  | 0, p, q, cs, h, _ => by
    rw [symProgRunSteps_zero] at h
    injection h with h1 _
    subst h1
    exact StepsToV2026.refl _
  | k + 1, p, q, cs, h, hc => by
    rw [symProgRunSteps_succ] at h
    cases hs : symProgStep cfg p with
    | step p₁ cs₁ =>
      rw [hs] at h
      obtain ⟨cs₂, h₂, hcs⟩ := addConds_eq_step h
      subst hcs
      have hc' := (condsHold_append env cs₁ cs₂).mp hc
      exact StepsToV2026.step (symProgStep_v2026_sound hs env hc'.1)
        (symProgRunSteps_sound cfg env k h₂ hc'.2)
    | ret _ _ _ => rw [hs] at h; nomatch h
    | branch _ _ => rw [hs] at h; nomatch h
    | stuck => rw [hs] at h; nomatch h

/-- `k`-step soundness sealed as Episode 1's `Framework.StepWp.StepStageCut`. -/
theorem symProgRunSteps_step_sound {cfg : SymConfig} {k : Nat} {p q : SymProg}
    {cs : List SymCond} (h : symProgRunSteps cfg k p = .step q cs) (env : SymEnv)
    (hc : condsHold env cs) :
    StepStageCut (v2026Step cfg.body) k (p.toMachineState cfg env) (q.toMachineState cfg env) :=
  (symProgRunSteps_sound cfg env k h hc).to_stepStageCut

/-- **Exact return soundness**: a symbolic run ending in `.ret` is an exact
`StepsToV2026` prefix followed by a trusted normal return. -/
theorem symProgRunSteps_ret_exact (cfg : SymConfig) (env : SymEnv) :
    ∀ (k : Nat) {p : SymProg} {v : SymVal} {fin : SymProg} {cs : List SymCond},
      symProgRunSteps cfg k p = .ret v fin cs → condsHold env cs →
      ∃ j, j + 1 ≤ k ∧
        StepsToV2026 cfg.body j (p.toMachineState cfg env) (fin.toMachineState cfg env) ∧
        v2026Step cfg.body (fin.toMachineState cfg env) =
          .done (.normal (v.eval env, (fin.toMachineState cfg env).memory))
  | 0, p, v, fin, cs, h, _ => by
    rw [symProgRunSteps_zero] at h
    nomatch h
  | k + 1, p, v, fin, cs, h, hc => by
    rw [symProgRunSteps_succ] at h
    cases hs : symProgStep cfg p with
    | step p₁ cs₁ =>
      rw [hs] at h
      obtain ⟨cs₂, h₂, hcs⟩ := addConds_eq_ret h
      subst hcs
      have hc' := (condsHold_append env cs₁ cs₂).mp hc
      obtain ⟨j, hj, hsteps, hdone⟩ := symProgRunSteps_ret_exact cfg env k h₂ hc'.2
      exact ⟨j + 1, Nat.succ_le_succ hj,
        StepsToV2026.step (symProgStep_v2026_sound hs env hc'.1) hsteps, hdone⟩
    | ret v' fin' cs' =>
      rw [hs] at h
      injection h with h1 h2 h3
      subst h1
      subst h2
      subst h3
      obtain ⟨hfin, _, _⟩ := symProgStep_ret_sound hs env
      subst hfin
      exact ⟨0, Nat.succ_le_succ (Nat.zero_le k), StepsToV2026.refl _,
        symProgStep_ret_v2026_sound hs env⟩
    | branch _ _ => rw [hs] at h; nomatch h
    | stuck => rw [hs] at h; nomatch h

/-- Return soundness onto `ReachesDoneWithinV2026` (any postcondition
satisfied by the symbolic return value). -/
theorem symProgRunSteps_ret_sound {cfg : SymConfig} {k : Nat} {p : SymProg} {v : SymVal}
    {fin : SymProg} {cs : List SymCond} (h : symProgRunSteps cfg k p = .ret v fin cs)
    (env : SymEnv) (hc : condsHold env cs) {post : MirOutcome → Prop}
    (hpost : post (.normal (v.eval env, (fin.toMachineState cfg env).memory))) :
    ReachesDoneWithinV2026 cfg.body post k (p.toMachineState cfg env) := by
  obtain ⟨j, hj, hsteps, hdone⟩ := symProgRunSteps_ret_exact cfg env k h hc
  exact ReachesDoneWithinV2026.mono hj
    (reachesDoneWithinV2026_of_stepsTo hsteps (reachesDoneWithinV2026_of_done hdone hpost))

/-- Fork soundness for a run: the prefix is an exact trace and every enabled
alternative is a trusted successor. -/
theorem symProgRunSteps_branch_sound (cfg : SymConfig) (env : SymEnv) :
    ∀ (k : Nat) {p : SymProg} {alts : List (SymCond × SymProg)} {cs : List SymCond},
      symProgRunSteps cfg k p = .branch alts cs → condsHold env cs →
      ∃ (j : Nat) (fork : SymProg), j + 1 ≤ k ∧
        StepsToV2026 cfg.body j (p.toMachineState cfg env) (fork.toMachineState cfg env) ∧
        ∀ c q, (c, q) ∈ alts → c.holds env →
          v2026Step cfg.body (fork.toMachineState cfg env) = .step (q.toMachineState cfg env)
  | 0, p, alts, cs, h, _ => by
    rw [symProgRunSteps_zero] at h
    nomatch h
  | k + 1, p, alts, cs, h, hc => by
    rw [symProgRunSteps_succ] at h
    cases hs : symProgStep cfg p with
    | step p₁ cs₁ =>
      rw [hs] at h
      obtain ⟨cs₂, h₂, hcs⟩ := addConds_eq_branch h
      subst hcs
      have hc' := (condsHold_append env cs₁ cs₂).mp hc
      obtain ⟨j, fork, hj, hsteps, halts⟩ := symProgRunSteps_branch_sound cfg env k h₂ hc'.2
      exact ⟨j + 1, fork, Nat.succ_le_succ hj,
        StepsToV2026.step (symProgStep_v2026_sound hs env hc'.1) hsteps, halts⟩
    | branch alts' cs' =>
      rw [hs] at h
      injection h with h1 h2
      subst h1
      subst h2
      exact ⟨0, p, Nat.succ_le_succ (Nat.zero_le k), StepsToV2026.refl _,
        (symProgStep_branch_sound hs env).2⟩
    | ret _ _ _ => rw [hs] at h; nomatch h
    | stuck => rw [hs] at h; nomatch h

theorem symRunChunks_nil (cfg : SymConfig) (p : SymProg) :
    symRunChunks cfg [] p = .step p [] := rfl

theorem symRunChunks_cons (cfg : SymConfig) (k : SymChunk) (ks : List SymChunk)
    (p : SymProg) :
    symRunChunks cfg (k :: ks) p = (symProgRunSteps cfg k p).bindRun (symRunChunks cfg ks) :=
  rfl

/-- A chunk pipeline is exactly the run of its total step count. -/
theorem symRunChunks_eq (cfg : SymConfig) :
    ∀ (ks : List SymChunk) (p : SymProg),
      symRunChunks cfg ks p = symProgRunSteps cfg (chunksTotal ks) p
  | [], p => by
    rw [symRunChunks_nil]
    rfl
  | k :: ks, p => by
    rw [symRunChunks_cons]
    have ih : symRunChunks cfg ks = symProgRunSteps cfg (chunksTotal ks) :=
      funext (symRunChunks_eq cfg ks)
    rw [ih, show chunksTotal (k :: ks) = k + chunksTotal ks from rfl,
      symProgRunSteps_add]

theorem symProgEntry_toMachineState (cfg : SymConfig) (args : List SymVal) (env : SymEnv) :
    (symProgEntry cfg args).toMachineState cfg env =
      initMachineStateWithCallees cfg.body (symValsEval env args) cfg.callees := by
  obtain ⟨body, callees⟩ := cfg
  cases callees with
  | nil =>
    simp only [SymProg.toMachineState, symProgEntry, SymFrame.eval, SymProg.toMemory,
      symStackEval, symSlotsEval_symInitLocalsAux]
    rfl
  | cons _ _ =>
    simp only [SymProg.toMachineState, symProgEntry, SymFrame.eval, SymProg.toMemory,
      symStackEval, symSlotsEval_symInitLocalsAux]
    rfl

theorem symProgEntry_toMachineState_stateful (cfg : SymConfig) (args : List SymVal)
    (env : SymEnv) :
    (symProgEntry cfg args).toMachineState cfg env =
      Trusted.VerificationResult.initMachineStateWithMemoryAndCallees cfg.body
        (symValsEval env args) (symEntryMemory cfg) cfg.callees := by
  obtain ⟨body, callees⟩ := cfg
  cases callees with
  | nil =>
    simp only [SymProg.toMachineState, symProgEntry, SymFrame.eval, SymProg.toMemory,
      symStackEval, symSlotsEval_symInitLocalsAux]
    rfl
  | cons _ _ =>
    simp only [SymProg.toMachineState, symProgEntry, SymFrame.eval, SymProg.toMemory,
      symStackEval, symSlotsEval_symInitLocalsAux]
    rfl

/-- **End-to-end multi-chunk soundness**: a symbolic chunk pipeline that
returns from the entry state yields `ReachesDoneWithinV2026`,
`ExecWithinStepsV2026`, `ExecStatefulWithinStepsV2026`, unmodified
`MirWpConverges`, and `MirNoUBTree` for the concrete arguments it denotes. -/
theorem symRunChunks_sound {cfg : SymConfig} {ks : List SymChunk} {args : List SymVal}
    {v : SymVal} {fin : SymProg} {cs : List SymCond}
    (h : symRunChunks cfg ks (symProgEntry cfg args) = .ret v fin cs) (env : SymEnv)
    (hc : condsHold env cs) {post : MirOutcome → Prop}
    (hpost : post (.normal (v.eval env, (fin.toMachineState cfg env).memory))) :
    ReachesDoneWithinV2026 cfg.body post (chunksTotal ks)
        ((symProgEntry cfg args).toMachineState cfg env) ∧
      ExecWithinStepsV2026 cfg.body (symValsEval env args) cfg.callees post (chunksTotal ks) ∧
      ExecStatefulWithinStepsV2026 cfg.body (symValsEval env args) (symEntryMemory cfg)
        cfg.callees post (chunksTotal ks) ∧
      MirWpConverges cfg.body
        (initMachineStateWithCallees cfg.body (symValsEval env args) cfg.callees) post ∧
      MirNoUBTree (mirTree cfg.body
        (initMachineStateWithCallees cfg.body (symValsEval env args) cfg.callees)) := by
  rw [symRunChunks_eq] at h
  have hR := symProgRunSteps_ret_sound h env hc hpost
  have hE : ExecWithinStepsV2026 cfg.body (symValsEval env args) cfg.callees post
      (chunksTotal ks) := by
    unfold ExecWithinStepsV2026
    rw [← symProgEntry_toMachineState]
    exact hR
  have hS : ExecStatefulWithinStepsV2026 cfg.body (symValsEval env args) (symEntryMemory cfg)
      cfg.callees post (chunksTotal ks) := by
    unfold ExecStatefulWithinStepsV2026
    rw [← symProgEntry_toMachineState_stateful]
    exact hR
  exact ⟨hR, hE, hS, mirWpConverges_of_reachesDoneWithinV2026 hE,
    mirNoUBTree_of_reachesDoneWithinV2026 hE⟩

/-- Stateless `VerificationResult` (panic-forbidding) from a symbolic chunk
pipeline, for every concrete argument list denoted by the symbolic entry. -/
theorem verificationResult_of_symRunChunks (c : Claim) (cfg : SymConfig)
    (hb : cfg.body = c.body) (hcal : cfg.callees = c.callees)
    (ks : List SymChunk) (symArgs : List SymVal) (v : SymVal) (fin : SymProg)
    (cs : List SymCond)
    (h : symRunChunks cfg ks (symProgEntry cfg symArgs) = .ret v fin cs)
    (henv : ∀ args, c.pre args → ∃ env : SymEnv, symValsEval env symArgs = args ∧
      condsHold env cs ∧ c.post args (v.eval env)) :
    VerificationResult c := by
  refine verifyMirNoPanic_of_execWithinStepsV2026 c (fun args hPre => ?_)
  obtain ⟨env, hargs, hc, hpost⟩ := henv args hPre
  obtain ⟨_, hE, _⟩ := symRunChunks_sound h env hc
    (post := mirNormalPost (fun retVal _ => c.post args retVal)) hpost
  rw [hb, hcal, hargs] at hE
  exact ⟨_, hE⟩

/-- Stateful `StatefulVerificationResult` (panic-forbidding) from a symbolic
chunk pipeline whose precondition pins the entry memory. -/
theorem statefulVerificationResult_of_symRunChunks (c : StatefulClaim) (cfg : SymConfig)
    (hb : cfg.body = c.body) (hcal : cfg.callees = c.callees)
    (ks : List SymChunk) (symArgs : List SymVal) (v : SymVal) (fin : SymProg)
    (cs : List SymCond)
    (h : symRunChunks cfg ks (symProgEntry cfg symArgs) = .ret v fin cs)
    (henv : ∀ args mem, c.pre args mem → mem = symEntryMemory cfg ∧
      ∃ env : SymEnv, symValsEval env symArgs = args ∧ condsHold env cs ∧
        c.post args mem (v.eval env) (fin.toMachineState cfg env).memory) :
    StatefulVerificationResult c := by
  refine verifyStatefulMirNoPanic_of_execWithinStepsV2026 c (fun args mem hPre => ?_)
  obtain ⟨hmem, env, hargs, hc, hpost⟩ := henv args mem hPre
  obtain ⟨_, _, hS, _⟩ := symRunChunks_sound h env hc
    (post := mirNormalPost (c.post args mem)) hpost
  rw [hb, hcal, hargs, ← hmem] at hS
  exact ⟨_, hS⟩


/-! ## Part XII: Fail-Closed Refutation Bridges -/

/-- Fault refutation: a symbolic prefix reaching a state where the trusted step
faults refutes `MirNoUBTree`, `MirWpConverges`, and every
`ReachesDoneWithinV2026` from the denoted start state. -/
theorem symProgRunSteps_fault_refutes {cfg : SymConfig} {k : Nat} {p q : SymProg}
    {cs : List SymCond} (h : symProgRunSteps cfg k p = .step q cs) (env : SymEnv)
    (hc : condsHold env cs) {fk : FailureKind}
    (hf : v2026Step cfg.body (q.toMachineState cfg env) = .fault (.fail fk)) :
    ¬ MirNoUBTree (mirTree cfg.body (p.toMachineState cfg env)) ∧
      (∀ post, ¬ MirWpConverges cfg.body (p.toMachineState cfg env) post) ∧
      (∀ post bound, ¬ ReachesDoneWithinV2026 cfg.body post bound (p.toMachineState cfg env)) := by
  have hSteps := symProgRunSteps_sound cfg env k h hc
  have hUB := not_mirNoUBTree_of_stepsTo_fault_fail hSteps hf
  exact ⟨hUB, fun _ hW => hUB (Anneal.PureMirExec.treeSafe_and_ret_of_mirWpConverges hW).1,
    fun _ _ => not_reachesDoneWithinV2026_of_stepsTo_fault hSteps hf⟩

/-- Non-normal-outcome refutation: a symbolic prefix reaching a state whose
trusted step terminates with an outcome violating `post` refutes every
`ReachesDoneWithinV2026` for `post`. -/
theorem symProgRunSteps_done_refutes {cfg : SymConfig} {k : Nat} {p q : SymProg}
    {cs : List SymCond} (h : symProgRunSteps cfg k p = .step q cs) (env : SymEnv)
    (hc : condsHold env cs) {out : MirOutcome} {post : MirOutcome → Prop}
    (hd : v2026Step cfg.body (q.toMachineState cfg env) = .done out) (hn : ¬ post out) :
    ∀ bound, ¬ ReachesDoneWithinV2026 cfg.body post bound (p.toMachineState cfg env) :=
  fun _ => not_reachesDoneWithinV2026_of_stepsTo_done_fail
    (symProgRunSteps_sound cfg env k h hc) hd hn

end Anneal.MirSymExec.ChunkedCallV2026
