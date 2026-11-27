-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Trusted
import Anneal.Firewall
import Anneal.ParametricCore.BlockTree
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

/-- Unary scalar operators (`!x` on `bool`, bitwise `!x` on integers, wrapping `-x`). -/
inductive SymUnOp : Type where
  | neg | notInt | notBool

/-- Overflow-checking binary operators (`AddWithOverflow`, `SubWithOverflow`,
`MulWithOverflow`). -/
inductive SymOverflowKind : Type where
  | add | sub | mul

/-- Raw width-parametric symbolic scalar expression trees. Widths live in the
`ScalarInt.sizeBytes` of every denotation; signedness is recorded on each
operator node exactly as resolved by the trusted MIR / intrinsic dispatcher. -/
inductive SymNode : Type where
  /-- Symbolic input `id` of byte width `width`: denotes `⟨env id, width⟩`. -/
  | var (id : Nat) (width : Nat)
  /-- Concrete scalar constant. -/
  | const (sc : ScalarInt)
  /-- Unary MIR scalar operator (`-x`, `!x`). -/
  | unaryOp (op : SymUnOp) (a : SymNode)
  /-- Scalar MIR `Rvalue.binaryOp` (`evalScalarBinOp`). -/
  | binOp (op : BinOp) (signed : Bool) (a b : SymNode)
  /-- Value component `.0` of `Rvalue.binaryOp` `*WithOverflow`. -/
  | checkedVal (k : SymOverflowKind) (signed : Bool) (a b : SymNode)
  /-- Overflow-flag component `.1` of `Rvalue.binaryOp` `*WithOverflow`. -/
  | checkedFlag (k : SymOverflowKind) (signed : Bool) (a b : SymNode)
  /-- Integer-to-integer MIR cast (`CastKind.intToInt`). -/
  | castInt (signed : Bool) (targetBytes : Nat) (a : SymNode)
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

/-- Trusted unary scalar evaluation (exact match with `evalRvalue` / `evalUnaryNot`). -/
def symUnOpEval : SymUnOp → ScalarInt → ScalarInt
  | .neg, sc =>
    let modulus := scalarModulus sc.sizeBytes
    let canonical := wrapScalarBits sc.bits modulus
    ⟨wrapScalarBits (Nat.sub modulus canonical) modulus, sc.sizeBytes⟩
  | .notInt, sc =>
    let modulus := scalarModulus sc.sizeBytes
    let canonical := wrapScalarBits sc.bits modulus
    ⟨Nat.sub (Nat.sub modulus 1) canonical, sc.sizeBytes⟩
  | .notBool, sc =>
    ⟨match Nat.beq sc.bits 0 with | true => 1 | false => 0, 1⟩

/-- Trusted scalar `Rvalue.binaryOp` kernel (calling `evalScalarBinOp` directly). -/
def symBinOpEval (op : BinOp) (signed : Bool) (x y : ScalarInt) : Option ScalarInt :=
  match evalScalarBinOp op x y [] emptyMemory signed with
  | .ok (.scalar sc) _ _ => some sc
  | _ => none

/-- Map `SymOverflowKind` to its trusted `BinOp`. -/
def symOverflowToBinOp : SymOverflowKind → BinOp
  | .add => .addWithOverflow
  | .sub => .subWithOverflow
  | .mul => .mulWithOverflow

/-- Value component `.0` of trusted `evalScalarBinOp` `*WithOverflow`. -/
def symCheckedValEval (k : SymOverflowKind) (signed : Bool) (x y : ScalarInt) :
    Option ScalarInt :=
  match evalScalarBinOp (symOverflowToBinOp k) x y [] emptyMemory signed with
  | .ok (.aggregate 0 [.scalar v, .scalar _]) _ _ => some v
  | _ => none

/-- Overflow flag `.1` of trusted `evalScalarBinOp` `*WithOverflow`. -/
def symCheckedFlagEval (k : SymOverflowKind) (signed : Bool) (x y : ScalarInt) :
    Option ScalarInt :=
  match evalScalarBinOp (symOverflowToBinOp k) x y [] emptyMemory signed with
  | .ok (.aggregate 0 [.scalar _, .scalar f]) _ _ => some f
  | _ => none

/-- Trusted `CastKind.intToInt` kernel (exact match with `evalRvalue`). -/
def symCastIntEval (signed : Bool) (targetBytes : Nat) (sc : ScalarInt) : ScalarInt :=
  let modulus := scalarModulus targetBytes
  let castedBits :=
    match signed with
    | false => wrapScalarBits sc.bits modulus
    | true =>
      match Nat.ble targetBytes sc.sizeBytes with
      | true => wrapScalarBits sc.bits modulus
      | false => signExtendBits sc.bits sc.sizeBytes targetBytes
  ⟨castedBits, targetBytes⟩

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
      | .unaryOp op a => symUnOpEval op (ih a)
      | .binOp op s a b => (symBinOpEval op s (ih a) (ih b)).getD symDefaultScalar
      | .checkedVal k s a b => (symCheckedValEval k s (ih a) (ih b)).getD symDefaultScalar
      | .checkedFlag k s a b => (symCheckedFlagEval k s (ih a) (ih b)).getD symDefaultScalar
      | .castInt s tb a => symCastIntEval s tb (ih a)
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
  | unaryOp {op : SymUnOp} {a : SymNode} {n : Nat} :
      SymNode.DepthLE a n → SymNode.DepthLE (.unaryOp op a) (n + 1)
  | binOp {op : BinOp} {s : Bool} {a b : SymNode} {n : Nat} :
      SymNode.DepthLE a n → SymNode.DepthLE b n → SymNode.DepthLE (.binOp op s a b) (n + 1)
  | checkedVal {k : SymOverflowKind} {s : Bool} {a b : SymNode} {n : Nat} :
      SymNode.DepthLE a n → SymNode.DepthLE b n → SymNode.DepthLE (.checkedVal k s a b) (n + 1)
  | checkedFlag {k : SymOverflowKind} {s : Bool} {a b : SymNode} {n : Nat} :
      SymNode.DepthLE a n → SymNode.DepthLE b n → SymNode.DepthLE (.checkedFlag k s a b) (n + 1)
  | castInt {s : Bool} {tb : Nat} {a : SymNode} {n : Nat} :
      SymNode.DepthLE a n → SymNode.DepthLE (.castInt s tb a) (n + 1)
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
  | unaryOp _ iha =>
    intro m hm
    cases m with
    | zero => exact absurd hm (Nat.not_succ_le_zero _)
    | succ m => exact .unaryOp (iha (Nat.le_of_succ_le_succ hm))
  | binOp _ _ iha ihb =>
    intro m hm
    cases m with
    | zero => exact absurd hm (Nat.not_succ_le_zero _)
    | succ m => exact .binOp (iha (Nat.le_of_succ_le_succ hm)) (ihb (Nat.le_of_succ_le_succ hm))
  | checkedVal _ _ iha ihb =>
    intro m hm
    cases m with
    | zero => exact absurd hm (Nat.not_succ_le_zero _)
    | succ m =>
      exact .checkedVal (iha (Nat.le_of_succ_le_succ hm)) (ihb (Nat.le_of_succ_le_succ hm))
  | checkedFlag _ _ iha ihb =>
    intro m hm
    cases m with
    | zero => exact absurd hm (Nat.not_succ_le_zero _)
    | succ m =>
      exact .checkedFlag (iha (Nat.le_of_succ_le_succ hm)) (ihb (Nat.le_of_succ_le_succ hm))
  | castInt _ iha =>
    intro m hm
    cases m with
    | zero => exact absurd hm (Nat.not_succ_le_zero _)
    | succ m => exact .castInt (iha (Nat.le_of_succ_le_succ hm))
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
  | unaryOp _ iha =>
    intro m hm
    cases m with
    | zero => exact absurd hm (Nat.not_succ_le_zero _)
    | succ m =>
      show symUnOpEval _ (symNodeEvalFuel env m _) = symUnOpEval _ (symNodeEvalFuel env _ _)
      rw [iha (Nat.le_of_succ_le_succ hm)]
  | binOp _ _ iha ihb =>
    intro m hm
    cases m with
    | zero => exact absurd hm (Nat.not_succ_le_zero _)
    | succ m =>
      show (symBinOpEval _ _ (symNodeEvalFuel env m _) (symNodeEvalFuel env m _)).getD _ =
        (symBinOpEval _ _ (symNodeEvalFuel env _ _) (symNodeEvalFuel env _ _)).getD _
      rw [iha (Nat.le_of_succ_le_succ hm), ihb (Nat.le_of_succ_le_succ hm)]
  | checkedVal _ _ iha ihb =>
    intro m hm
    cases m with
    | zero => exact absurd hm (Nat.not_succ_le_zero _)
    | succ m =>
      show (symCheckedValEval _ _ (symNodeEvalFuel env m _) (symNodeEvalFuel env m _)).getD _ =
        (symCheckedValEval _ _ (symNodeEvalFuel env _ _) (symNodeEvalFuel env _ _)).getD _
      rw [iha (Nat.le_of_succ_le_succ hm), ihb (Nat.le_of_succ_le_succ hm)]
  | checkedFlag _ _ iha ihb =>
    intro m hm
    cases m with
    | zero => exact absurd hm (Nat.not_succ_le_zero _)
    | succ m =>
      show (symCheckedFlagEval _ _ (symNodeEvalFuel env m _) (symNodeEvalFuel env m _)).getD _ =
        (symCheckedFlagEval _ _ (symNodeEvalFuel env _ _) (symNodeEvalFuel env _ _)).getD _
      rw [iha (Nat.le_of_succ_le_succ hm), ihb (Nat.le_of_succ_le_succ hm)]
  | castInt _ iha =>
    intro m hm
    cases m with
    | zero => exact absurd hm (Nat.not_succ_le_zero _)
    | succ m =>
      show symCastIntEval _ _ (symNodeEvalFuel env m _) =
        symCastIntEval _ _ (symNodeEvalFuel env _ _)
      rw [iha (Nat.le_of_succ_le_succ hm)]
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

/-- Unary scalar operator node. -/
def SymScalar.unaryOp (op : SymUnOp) (a : SymScalar) : SymScalar :=
  ⟨.unaryOp op a.node, a.fuel + 1, .unaryOp a.wf⟩

/-- Scalar `Rvalue.binaryOp` node. -/
def SymScalar.binOp (op : BinOp) (s : Bool) (a b : SymScalar) : SymScalar :=
  ⟨.binOp op s a.node b.node, Nat.max a.fuel b.fuel + 1,
    .binOp (a.wf.mono (Nat.le_max_left _ _)) (b.wf.mono (Nat.le_max_right _ _))⟩

/-- Value component `.0` of `*WithOverflow` binary op. -/
def SymScalar.checkedVal (k : SymOverflowKind) (s : Bool) (a b : SymScalar) : SymScalar :=
  ⟨.checkedVal k s a.node b.node, Nat.max a.fuel b.fuel + 1,
    .checkedVal (a.wf.mono (Nat.le_max_left _ _)) (b.wf.mono (Nat.le_max_right _ _))⟩

/-- Overflow-flag component `.1` of `*WithOverflow` binary op. -/
def SymScalar.checkedFlag (k : SymOverflowKind) (s : Bool) (a b : SymScalar) : SymScalar :=
  ⟨.checkedFlag k s a.node b.node, Nat.max a.fuel b.fuel + 1,
    .checkedFlag (a.wf.mono (Nat.le_max_left _ _)) (b.wf.mono (Nat.le_max_right _ _))⟩

/-- `CastKind.intToInt` node. -/
def SymScalar.castInt (s : Bool) (tb : Nat) (a : SymScalar) : SymScalar :=
  ⟨.castInt s tb a.node, a.fuel + 1, .castInt a.wf⟩

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

theorem SymScalar.eval_unaryOp (env : SymEnv) (op : SymUnOp) (a : SymScalar) :
    (SymScalar.unaryOp op a).eval env = symUnOpEval op (a.eval env) := rfl

theorem SymScalar.eval_binOp (env : SymEnv) (op : BinOp) (s : Bool) (a b : SymScalar) :
    (SymScalar.binOp op s a b).eval env =
      (symBinOpEval op s (a.eval env) (b.eval env)).getD symDefaultScalar := by
  show (symBinOpEval op s (symNodeEvalFuel env (Nat.max a.fuel b.fuel) a.node)
      (symNodeEvalFuel env (Nat.max a.fuel b.fuel) b.node)).getD symDefaultScalar = _
  rw [symNodeEvalFuel_stable env a.wf (Nat.le_max_left _ _),
    symNodeEvalFuel_stable env b.wf (Nat.le_max_right _ _)]
  rfl

theorem SymScalar.eval_checkedVal (env : SymEnv) (k : SymOverflowKind) (s : Bool)
    (a b : SymScalar) :
    (SymScalar.checkedVal k s a b).eval env =
      (symCheckedValEval k s (a.eval env) (b.eval env)).getD symDefaultScalar := by
  show (symCheckedValEval k s (symNodeEvalFuel env (Nat.max a.fuel b.fuel) a.node)
      (symNodeEvalFuel env (Nat.max a.fuel b.fuel) b.node)).getD symDefaultScalar = _
  rw [symNodeEvalFuel_stable env a.wf (Nat.le_max_left _ _),
    symNodeEvalFuel_stable env b.wf (Nat.le_max_right _ _)]
  rfl

theorem SymScalar.eval_checkedFlag (env : SymEnv) (k : SymOverflowKind) (s : Bool)
    (a b : SymScalar) :
    (SymScalar.checkedFlag k s a b).eval env =
      (symCheckedFlagEval k s (a.eval env) (b.eval env)).getD symDefaultScalar := by
  show (symCheckedFlagEval k s (symNodeEvalFuel env (Nat.max a.fuel b.fuel) a.node)
      (symNodeEvalFuel env (Nat.max a.fuel b.fuel) b.node)).getD symDefaultScalar = _
  rw [symNodeEvalFuel_stable env a.wf (Nat.le_max_left _ _),
    symNodeEvalFuel_stable env b.wf (Nat.le_max_right _ _)]
  rfl

theorem SymScalar.eval_castInt (env : SymEnv) (s : Bool) (tb : Nat) (a : SymScalar) :
    (SymScalar.castInt s tb a).eval env = symCastIntEval s tb (a.eval env) := rfl

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
  /-- Valid 1-byte boolean scalar (`sizeBytes = 1 ∧ (bits = 0 ∨ bits = 1)`). -/
  | validBool (a : SymScalar)
  /-- MIR `Rvalue.binaryOp .addUnchecked`: raw-bit no-overflow guard. -/
  | binNoOverflowAdd (signed : Bool) (a b : SymScalar)
  /-- MIR `Rvalue.binaryOp .subUnchecked`: raw-bit no-overflow guard. -/
  | binNoOverflowSub (signed : Bool) (a b : SymScalar)
  /-- MIR `Rvalue.binaryOp .mulUnchecked`: raw-bit no-overflow guard. -/
  | binNoOverflowMul (signed : Bool) (a b : SymScalar)
  /-- MIR `Rvalue.binaryOp .div`: nonzero raw divisor (and no signed `MIN / -1`). -/
  | binDivSafe (signed : Bool) (a b : SymScalar)
  /-- MIR `Rvalue.binaryOp .rem`: nonzero raw divisor (and no signed `MIN % -1`). -/
  | binRemSafe (signed : Bool) (a b : SymScalar)
  /-- MIR `Rvalue.binaryOp .{shlUnchecked,shrUnchecked}`: raw shift `< 8 * width`. -/
  | binShiftInBounds (a b : SymScalar)

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
  | .validBool a =>
    let x := a.eval env
    x.sizeBytes = 1 ∧ (x.bits = 0 ∨ x.bits = 1)
  | .binNoOverflowAdd s a b =>
    let x := a.eval env
    let y := b.eval env
    ScWidthsOk x y ∧
      (match s with
       | false => x.bits + y.bits < scalarModulus x.sizeBytes
       | true => signedOverflowAdd x.bits y.bits x.sizeBytes = false)
  | .binNoOverflowSub s a b =>
    let x := a.eval env
    let y := b.eval env
    ScWidthsOk x y ∧
      (match s with
       | false => y.bits ≤ x.bits ∧ Nat.sub x.bits y.bits < scalarModulus x.sizeBytes
       | true => signedOverflowSub x.bits y.bits x.sizeBytes = false)
  | .binNoOverflowMul s a b =>
    let x := a.eval env
    let y := b.eval env
    ScWidthsOk x y ∧
      (match s with
       | false => x.bits * y.bits < scalarModulus x.sizeBytes
       | true => signedOverflowMul x.bits y.bits x.sizeBytes = false)
  | .binDivSafe s a b =>
    let x := a.eval env
    let y := b.eval env
    ScWidthsOk x y ∧ y.bits ≠ 0 ∧
      (match s with
       | false => True
       | true => ScNotMinNegOne x y)
  | .binRemSafe s a b =>
    let x := a.eval env
    let y := b.eval env
    ScWidthsOk x y ∧ y.bits ≠ 0 ∧
      (match s with
       | false => True
       | true => ScNotMinNegOne x y)
  | .binShiftInBounds a b =>
    let x := a.eval env
    let y := b.eval env
    x.sizeBytes ≠ 0 ∧ y.sizeBytes ≠ 0 ∧ y.bits < Nat.mul x.sizeBytes 8

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

/-- Symbolic `evalOperand` for bare locals (`copy` / `move`), single-level
non-union scalar aggregate field projections (`[.field idx _]`), and evaluated
non-indirect constants. -/
def symOperand (globals : List CapturedAllocation) (layouts : LayoutTable)
    (decls : List LocalDecl) (locals : List SymSlot) :
    Operand → Option (SymVal × List SymSlot)
  | .copy p =>
    match p.projection with
    | [] =>
      match get? locals p.local_ with
      | some (.init v) =>
        match v.containsUninit with
        | false => some (v, locals)
        | true => none
      | _ => none
    | [.field idx _] =>
      match placeTouchesUnion decls layouts p with
      | true => none
      | false =>
        match get? locals p.local_ with
        | some (.init (.aggregate _ fs)) =>
          match get? fs idx with
          | some s => some (.scalar s, locals)
          | none => none
        | _ => none
    | _ => none
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
    | [.field idx _] =>
      match placeTouchesUnion decls layouts p with
      | true => none
      | false =>
        match get? locals p.local_ with
        | some (.init (.aggregate _ fs)) =>
          match get? fs idx with
          | some s => some (.scalar s, locals)
          | none => none
        | _ => none
    | _ => none
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

/-- Symbolic `evalOperands` / `evalOperandsWithBodyCast` over `symOperand` (by `List.foldr`). -/
def symOperands (globals : List CapturedAllocation) (layouts : LayoutTable)
    (decls : List LocalDecl) (locals : List SymSlot) (ops : List Operand) :
    Option (List SymVal × List SymSlot) :=
  ops.foldr
    (fun op ih locals =>
      match symOperand globals layouts decls locals op with
      | some (v, locals₁) =>
        match ih locals₁ with
        | some (vs, locals₂) => some (v :: vs, locals₂)
        | none => none
      | none => none)
    (fun locals => some ([], locals)) locals

/-- Extract a list of symbolic scalars from symbolic values (for scalar aggregates). -/
def symValsAsScalars? (vs : List SymVal) : Option (List SymScalar) :=
  vs.foldr
    (fun v ih =>
      match v.asScalar?, ih with
      | some s, some ss => some (s :: ss)
      | _, _ => none)
    (some [])

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

/-- Symbolic scalar `Rvalue.binaryOp` dispatch (including `*WithOverflow` checked
binary operators returning `.aggregate 0 [val, flag]`). -/
def symScalarBinOp (op : BinOp) (signed : Bool) (a b : SymScalar) :
    Option (SymVal × List SymCond) :=
  match op with
  | .add | .sub | .mul | .bitAnd | .bitOr | .bitXor
  | .eq | .ne | .lt | .le | .gt | .ge | .cmp =>
    some (.scalar (.binOp op signed a b), [.widthsMatch a b])
  | .shl | .shr =>
    some (.scalar (.binOp op signed a b), [.widthNonzero a, .widthNonzero b])
  | .addWithOverflow =>
    some (.aggregate 0 [.checkedVal .add signed a b, .checkedFlag .add signed a b],
      [.widthsMatch a b])
  | .subWithOverflow =>
    some (.aggregate 0 [.checkedVal .sub signed a b, .checkedFlag .sub signed a b],
      [.widthsMatch a b])
  | .mulWithOverflow =>
    some (.aggregate 0 [.checkedVal .mul signed a b, .checkedFlag .mul signed a b],
      [.widthsMatch a b])
  | .addUnchecked =>
    some (.scalar (.binOp .addUnchecked signed a b), [.binNoOverflowAdd signed a b])
  | .subUnchecked =>
    some (.scalar (.binOp .subUnchecked signed a b), [.binNoOverflowSub signed a b])
  | .mulUnchecked =>
    some (.scalar (.binOp .mulUnchecked signed a b), [.binNoOverflowMul signed a b])
  | .div =>
    some (.scalar (.binOp .div signed a b), [.binDivSafe signed a b])
  | .rem =>
    some (.scalar (.binOp .rem signed a b), [.binRemSafe signed a b])
  | .shlUnchecked =>
    some (.scalar (.binOp .shlUnchecked signed a b), [.binShiftInBounds a b])
  | .shrUnchecked =>
    some (.scalar (.binOp .shrUnchecked signed a b), [.binShiftInBounds a b])
  | .offset => none

/-- Env-independent discriminant computation for an initialized scalar aggregate
(exact mirror of `evalPlaceDiscriminant` when `valueListContainsUninit = false`). -/
def symAggDiscriminant? (variantIdx fieldCount : Nat) (place : Place)
    (decls : List LocalDecl) (layouts : LayoutTable) : Option ScalarInt :=
  match placeTyResolved decls layouts place with
  | some pTy =>
    match pTy.kind with
    | .never => none
    | .adt defPath _ =>
      let evalOrderingOrVariant : Option ScalarInt :=
        match Bool.and (stringEq defPath "core::cmp::Ordering") (Nat.beq fieldCount 0) with
        | true =>
          match variantIdx with
          | 0 => some ⟨255, 1⟩
          | 1 => some ⟨0, 1⟩
          | 2 => some ⟨1, 1⟩
          | _ => none
        | false => some ⟨variantIdx, 8⟩
      match LayoutTable.lookup layouts pTy.layoutIdx with
      | some { isUninhabited := true, .. } => none
      | some { variants := .empty, .. } => none
      | some { variants := .single expectedIdx, .. } =>
        match Nat.beq variantIdx expectedIdx with
        | true => some ⟨0, 8⟩
        | false => none
      | some { variants := .multiple _ _ variants, .. } =>
        let varBoundsOk :=
          match variants with
          | .nil => true
          | _ :: _ => Nat.ble (.succ variantIdx) (length variants)
        match varBoundsOk with
        | true => evalOrderingOrVariant
        | false => none
      | none => evalOrderingOrVariant
    | .tuple _ | .array _ _ | .slice _ | .str =>
      match Nat.beq variantIdx 0 with
      | true => some ⟨0, 8⟩
      | false => none
    | _ => some ⟨variantIdx, 8⟩
  | none => some ⟨variantIdx, 8⟩

/-- Symbolic `evalRvalue`: `use` (including `bool` locals with `validBool`),
`unaryOp` (`neg`, `not` on `bool`/int), `binaryOp` (all scalar arithmetic,
bitwise, shift, comparison, unchecked, and `*WithOverflow` checked ops),
`cast .intToInt`, scalar `aggregate` (`tuple`, `array`, `closure`), and
bare-local `discriminant`. -/
def symRvalue (globals : List CapturedAllocation) (layouts : LayoutTable)
    (decls : List LocalDecl) (locals : List SymSlot) :
    Rvalue → Option (SymVal × List SymSlot × List SymCond)
  | .use op =>
    match symOperand globals layouts decls locals op with
    | some (v, locals') =>
      match loadedValueStaticOk layouts decls op with
      | true => some (v, locals', [])
      | false =>
        match operandTy decls layouts op with
        | some ty =>
          match ty.kind, v.asScalar? with
          | .bool, some sc => some (v, locals', [.validBool sc])
          | _, _ => none
        | none => none
    | none => none
  | .unaryOp .neg op =>
    match symOperand globals layouts decls locals op with
    | some (v, locals') =>
      match v.asScalar? with
      | some x => some (.scalar (.unaryOp .neg x), locals', [.widthNonzero x])
      | none => none
    | none => none
  | .unaryOp .not op =>
    match symOperand globals layouts decls locals op with
    | some (v, locals') =>
      match v.asScalar? with
      | some x =>
        match operandTy decls layouts op with
        | some ty =>
          match ty.kind with
          | .bool => some (.scalar (.unaryOp .notBool x), locals', [.validBool x])
          | .uint _ | .int _ => some (.scalar (.unaryOp .notInt x), locals', [.widthNonzero x])
          | _ => none
        | none => none
      | none => none
    | none => none
  | .binaryOp op lhsOp rhsOp =>
    match symOperand globals layouts decls locals lhsOp with
    | some (lv, locals₁) =>
      match symOperand globals layouts decls locals₁ rhsOp with
      | some (rv, locals₂) =>
        match lv.asScalar?, rv.asScalar? with
        | some a, some b =>
          let signed := operandIsSigned decls lhsOp layouts
          match symScalarBinOp op signed a b with
          | some (res, cs) => some (res, locals₂, cs)
          | none => none
        | _, _ => none
      | none => none
    | none => none
  | .cast .intToInt op targetTy =>
    match symOperand globals layouts decls locals op with
    | some (v, locals') =>
      match v.asScalar?, intCastTargetBytes targetTy.kind with
      | some x, some targetBytes =>
        let signed := operandIsSigned decls op layouts
        some (.scalar (.castInt signed targetBytes x), locals', [.widthNonzero x])
      | _, _ => none
    | none => none
  | .aggregate .tuple ops | .aggregate (.array _) ops | .aggregate (.closure _) ops =>
    match symOperands globals layouts decls locals ops with
    | some (vs, locals') =>
      match symValsAsScalars? vs with
      | some fs => some (.aggregate 0 fs, locals', [])
      | none => none
    | none => none
  | .discriminant place =>
    match place.projection with
    | [] =>
      match get? locals place.local_ with
      | some (.init (.aggregate variantIdx fs)) =>
        match symAggDiscriminant? variantIdx (length fs) place decls layouts with
        | some sc => some (.concrete (.scalar sc), locals, [])
        | none => none
      | _ => none
    | _ :: _ => none
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
  | .deinit p =>
    match p.projection with
    | [] =>
      match get? f.locals p.local_ with
      | some .dead => none
      | some _ =>
        match set? f.locals p.local_ .uninit with
        | some locals' => some (f.advance locals', [])
        | none => none
      | none => none
    | _ :: _ => none
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
    match symOperand cfg.body.allocations body.layouts body.localDecls p.frame.locals discr with
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
    match symOperand cfg.body.allocations body.layouts body.localDecls p.frame.locals cond with
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
      match symOperands cfg.body.allocations body.layouts body.localDecls p.frame.locals argOps with
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

/-- Symbolic observation of a step: silent, or a `SwitchInt` `.vis` event
carrying the (symbolic) discriminant bits. -/
inductive SymObs : Type where
  | silent : SymObs
  | event (d : SymScalar) : SymObs

/-- Denotation of a symbolic observation as a trusted `MirObs`. -/
def SymObs.eval (env : SymEnv) : SymObs → MirObs
  | .silent => .silent
  | .event d => .event (d.eval env).bits

/-- Exact observation emitted by the trusted `evalTerminator` step analysed by
`symTerm` (only `SwitchInt` is observable, emitting its discriminant bits). -/
def symTermObs (cfg : SymConfig) (p : SymProg) (body : CapturedMir) (term : Terminator) :
    SymObs :=
  match term.kind with
  | .switchInt discr _ =>
    match symOperand cfg.body.allocations body.layouts body.localDecls p.frame.locals discr with
    | some (v, _) =>
      match v.asScalar? with
      | some d => .event d
      | none => .silent
    | none => .silent
  | _ => .silent

/-- One symbolic step of the multi-frame program `p`, fetching root basic blocks
through an arbitrary block-lookup table `rootLook` (e.g. a dense
`Chunk8BlockTree.lookup?` for `O(log N)` / `O(1)` lookup without unfolding
`cfg.body.basicBlocks`). -/
def symProgStepWith (cfg : SymConfig) (rootLook : Nat → Option BasicBlockData)
    (p : SymProg) : SymStepRes :=
  let body := p.active.getD cfg.body
  match body.phase with
  | .other _ => .stuck
  | _ =>
    let bb? :=
      match p.active with
      | none => rootLook p.frame.blockIdx
      | some activeBody => get? activeBody.basicBlocks p.frame.blockIdx
    match bb? with
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

/-- One symbolic step of the multi-frame program `p`. -/
def symProgStep (cfg : SymConfig) (p : SymProg) : SymStepRes :=
  symProgStepWith cfg (fun idx => get? cfg.body.basicBlocks idx) p

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

/-- Run up to `n` symbolic steps using an explicit root block-lookup table
`rootLook` (`@Nat.rec` so explicit checkpoints reduce by `rfl`). -/
def symProgRunStepsWith (cfg : SymConfig) (rootLook : Nat → Option BasicBlockData)
    (n : Nat) : SymProg → SymStepRes :=
  @Nat.rec (fun _ => SymProg → SymStepRes)
    (fun p => .step p [])
    (fun _ ih p => (symProgStepWith cfg rootLook p).bindRun ih)
    n

/-- Run up to `n` symbolic steps (stopping at return, fork, or stuck), by
`@Nat.rec` so explicit checkpoints reduce by `rfl`. -/
def symProgRunSteps (cfg : SymConfig) (n : Nat) : SymProg → SymStepRes :=
  @Nat.rec (fun _ => SymProg → SymStepRes)
    (fun p => .step p [])
    (fun _ ih p => (symProgStep cfg p).bindRun ih)
    n

/-- A chunk is a step count. -/
abbrev SymChunk := Nat

/-- Run a list of chunks in sequence using an explicit root block-lookup table
`rootLook` (e.g. `Chunk8BlockTree.lookup?`). -/
def symRunChunksWith (cfg : SymConfig) (rootLook : Nat → Option BasicBlockData)
    (ks : List SymChunk) (p : SymProg) : SymStepRes :=
  ks.foldr (fun k ih p => (symProgRunStepsWith cfg rootLook k p).bindRun ih)
    (fun p => .step p []) p

/-- Run a list of chunks in sequence (structural recursion on the chunk list;
each chunk is a `@Nat.rec` run, so pipelines reduce by `rfl`). -/
def symRunChunks (cfg : SymConfig) (ks : List SymChunk) (p : SymProg) : SymStepRes :=
  ks.foldr (fun k ih p => (symProgRunSteps cfg k p).bindRun ih) (fun p => .step p []) p

/-- Total number of steps of a chunk list. -/
def chunksTotal (ks : List SymChunk) : Nat :=
  ks.foldr (fun k acc => k + acc) 0

/-- Dense `Chunk8BlockTree` block-lookup context for `body.basicBlocks`
(`O(log N)` spine depth + `O(1)` 8-wide leaf dispatch, zero linear traversal). -/
structure SymBlockCtx (body : CapturedMir) : Type where
  tree : Anneal.ParametricCore.Chunk8BlockTree BasicBlockData
  valid : Anneal.ParametricCore.ValidChunk8BlockTree body.basicBlocks tree

/-- Build the canonical `Chunk8BlockTree` block context for `body`. -/
def SymBlockCtx.ofBody (body : CapturedMir) : SymBlockCtx body :=
  { tree := Anneal.ParametricCore.Chunk8BlockTree.ofList body.basicBlocks
    valid := Anneal.ParametricCore.valid_chunk8BlockTree_ofList body.basicBlocks }

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
    (decls : List LocalDecl) (locals : List SymSlot) :
    symOperands globals layouts decls locals [] = some ([], locals) := rfl
theorem symOperands_cons (globals : List CapturedAllocation) (layouts : LayoutTable)
    (decls : List LocalDecl) (locals : List SymSlot) (op : Operand) (rest : List Operand) :
    symOperands globals layouts decls locals (op :: rest) =
      match symOperand globals layouts decls locals op with
      | some (v, locals₁) =>
        match symOperands globals layouts decls locals₁ rest with
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
  cases Nat.decLt i l.length with
  | isTrue h =>
    rw [Anneal.ParametricCore.ite_prop_pos h, Anneal.ParametricCore.ite_prop_pos h]
    exact congrArg some (symSlotsEval_set env l i s).symm
  | isFalse h =>
    rw [Anneal.ParametricCore.ite_prop_neg h, Anneal.ParametricCore.ite_prop_neg h]
    rfl

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

theorem get?_symFieldsEval (env : SymEnv) :
    ∀ (fs : List SymScalar) (i : Nat),
      get? (symFieldsEval env fs) i = (get? fs i).map (fun s => Value.scalar (s.eval env))
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: rest, i + 1 => get?_symFieldsEval env rest i

theorem length_symFieldsEval (env : SymEnv) :
    ∀ fs : List SymScalar, length (symFieldsEval env fs) = length fs
  | [] => rfl
  | _ :: rest => congrArg Nat.succ (length_symFieldsEval env rest)

theorem symValsAsScalars?_sound (env : SymEnv) :
    ∀ {vs : List SymVal} {fs : List SymScalar},
      symValsAsScalars? vs = some fs → symValsEval env vs = symFieldsEval env fs
  | [], fs, h => by
    injection h with h
    subst h
    rfl
  | v :: rest, fs, h => by
    change (match v.asScalar?, symValsAsScalars? rest with
      | some s, some ss => some (s :: ss)
      | _, _ => none) = some fs at h
    cases hv : v.asScalar? with
    | none => rw [hv] at h; nomatch h
    | some s =>
      cases hr : symValsAsScalars? rest with
      | none => rw [hv, hr] at h; nomatch h
      | some ss =>
        rw [hv, hr] at h
        injection h with h
        subst h
        rw [symValsEval_cons, symFieldsEval_cons, symVal_eval_of_asScalar hv env,
          symValsAsScalars?_sound env hr]

theorem symScalar_eval_of_asConst {a : SymScalar} {sc : ScalarInt}
    (h : a.asConst? = some sc) (env : SymEnv) : a.eval env = sc := by
  obtain ⟨node, fuel, wf⟩ := a
  cases node with
  | const c =>
    cases wf with
    | const => exact Option.some.inj h
  | var _ _ => nomatch h
  | unaryOp _ _ => nomatch h
  | binOp _ _ _ _ => nomatch h
  | checkedVal _ _ _ _ => nomatch h
  | checkedFlag _ _ _ _ => nomatch h
  | castInt _ _ _ => nomatch h
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

theorem symOperand_sound {globals : List CapturedAllocation} {layouts : LayoutTable}
    {decls : List LocalDecl} {locals : List SymSlot} {op : Operand} {v : SymVal}
    {locals' : List SymSlot}
    (h : symOperand globals layouts decls locals op = some (v, locals')) (env : SymEnv)
    (borrows : List BorrowEntry) (callerLocals : List LocalSlot)
    (callStack : List SavedCallerFrame) :
    evalOperand (symSlotsEval env locals) op borrows globals layouts callerLocals decls
      callStack = .ok (v.eval env) (symSlotsEval env locals') ∧
    evalOperand (symSlotsEval env locals) op borrows globals layouts callerLocals []
      callStack = .ok (v.eval env) (symSlotsEval env locals') := by
  cases op with
  | copy p =>
    obtain ⟨loc, proj⟩ := p
    cases proj with
    | nil =>
      simp only [symOperand] at h
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
            refine ⟨?_, ?_⟩ <;> (
              dsimp only [evalOperand]
              rw [get?_symSlotsEval, hg]
              dsimp only [Option.map, SymSlot.eval, readProjectedValue]
              rw [valueContainsUninit_symVal, hc])
    | cons pe rest =>
      cases pe with
      | field idx fty =>
        cases rest with
        | cons _ _ => nomatch h
        | nil =>
          simp only [symOperand] at h
          cases hu : placeTouchesUnion decls layouts { local_ := loc, projection := [.field idx fty] } with
          | true => rw [hu] at h; nomatch h
          | false =>
            rw [hu] at h
            dsimp only at h
            cases hg : get? locals loc with
            | none => rw [hg] at h; nomatch h
            | some sl =>
              rw [hg] at h
              cases sl with
              | dead => nomatch h
              | uninit => nomatch h
              | init w =>
                cases w with
                | aggregate vidx fs =>
                  dsimp only at h
                  cases hf : get? fs idx with
                  | none => rw [hf] at h; nomatch h
                  | some s =>
                    rw [hf] at h
                    injection h with h
                    injection h with h1 h2
                    subst h1
                    subst h2
                    refine ⟨?_, ?_⟩
                    · dsimp only [evalOperand]
                      rw [get?_symSlotsEval, hg, hu]
                      dsimp only [Option.map, SymSlot.eval, SymVal.eval, readProjectedValue]
                      rw [get?_symFieldsEval, hf]
                      rfl
                    · dsimp only [evalOperand]
                      rw [get?_symSlotsEval, hg]
                      dsimp only [Option.map, SymSlot.eval, SymVal.eval, placeTouchesUnion,
                        readProjectedValue]
                      rw [get?_symFieldsEval, hf]
                      rfl
                | unit => nomatch h
                | scalar _ => nomatch h
                | uninit => nomatch h
                | concrete _ => nomatch h
      | deref => nomatch h
      | index _ => nomatch h
      | constantIndex _ _ _ => nomatch h
      | subslice _ _ _ => nomatch h
      | downcast _ _ => nomatch h
      | opaqueCast _ => nomatch h
      | unwrapUnsafeBinder _ => nomatch h
  | move p =>
    obtain ⟨loc, proj⟩ := p
    cases proj with
    | nil =>
      simp only [symOperand] at h
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
              refine ⟨?_, ?_⟩ <;> (
                dsimp only [evalOperand]
                rw [get?_symSlotsEval, hg]
                dsimp only [Option.map, SymSlot.eval, readProjectedValue]
                rw [valueContainsUninit_symVal, hc]
                dsimp only
                rw [set?_symSlotsEval_uninit, hs]
                rfl)
    | cons pe rest =>
      cases pe with
      | field idx fty =>
        cases rest with
        | cons _ _ => nomatch h
        | nil =>
          simp only [symOperand] at h
          cases hu : placeTouchesUnion decls layouts { local_ := loc, projection := [.field idx fty] } with
          | true => rw [hu] at h; nomatch h
          | false =>
            rw [hu] at h
            dsimp only at h
            cases hg : get? locals loc with
            | none => rw [hg] at h; nomatch h
            | some sl =>
              rw [hg] at h
              cases sl with
              | dead => nomatch h
              | uninit => nomatch h
              | init w =>
                cases w with
                | aggregate vidx fs =>
                  dsimp only at h
                  cases hf : get? fs idx with
                  | none => rw [hf] at h; nomatch h
                  | some s =>
                    rw [hf] at h
                    injection h with h
                    injection h with h1 h2
                    subst h1
                    subst h2
                    refine ⟨?_, ?_⟩
                    · dsimp only [evalOperand]
                      rw [get?_symSlotsEval, hg, hu]
                      dsimp only [Option.map, SymSlot.eval, SymVal.eval, readProjectedValue]
                      rw [get?_symFieldsEval, hf]
                      rfl
                    · dsimp only [evalOperand]
                      rw [get?_symSlotsEval, hg]
                      dsimp only [Option.map, SymSlot.eval, SymVal.eval, placeTouchesUnion,
                        readProjectedValue]
                      rw [get?_symFieldsEval, hf]
                      rfl
                | unit => nomatch h
                | scalar _ => nomatch h
                | uninit => nomatch h
                | concrete _ => nomatch h
      | deref => nomatch h
      | index _ => nomatch h
      | constantIndex _ _ _ => nomatch h
      | subslice _ _ _ => nomatch h
      | downcast _ _ => nomatch h
      | opaqueCast _ => nomatch h
      | unwrapUnsafeBinder _ => nomatch h
  | constant c =>
    obtain ⟨ty, cv⟩ := c
    cases cv with
    | scalar cs =>
      simp only [symOperand] at h
      cases he : evalConstValue (.scalar cs) ty globals layouts with
      | none => rw [he] at h; nomatch h
      | some w =>
        rw [he] at h
        injection h with h
        injection h with h1 h2
        subst h1
        subst h2
        exact ⟨by dsimp only [evalOperand]; rw [he]; rfl,
          by dsimp only [evalOperand]; rw [he]; rfl⟩
    | zeroSized =>
      simp only [symOperand] at h
      cases he : evalConstValue .zeroSized ty globals layouts with
      | none => rw [he] at h; nomatch h
      | some w =>
        rw [he] at h
        injection h with h
        injection h with h1 h2
        subst h1
        subst h2
        exact ⟨by dsimp only [evalOperand]; rw [he]; rfl,
          by dsimp only [evalOperand]; rw [he]; rfl⟩
    | slice _ _ => nomatch h
    | indirect _ _ => nomatch h
    | unevaluated _ => nomatch h

theorem symOperand_shape {globals : List CapturedAllocation} {layouts : LayoutTable}
    {decls : List LocalDecl} {locals : List SymSlot} {op : Operand} {v : SymVal}
    {locals' : List SymSlot}
    (h : symOperand globals layouts decls locals op = some (v, locals')) :
    operandIsLeadingOpaqueCastMove op = false := by
  cases op with
  | copy _ => rfl
  | constant _ => rfl
  | move p =>
    obtain ⟨loc, proj⟩ := p
    cases proj with
    | nil => rfl
    | cons pe rest =>
      cases pe with
      | field _ _ => rfl
      | deref => nomatch h
      | index _ => nomatch h
      | constantIndex _ _ _ => nomatch h
      | subslice _ _ _ => nomatch h
      | downcast _ _ => nomatch h
      | opaqueCast _ => nomatch h
      | unwrapUnsafeBinder _ => nomatch h

theorem symOperands_evalOperands_sound {globals : List CapturedAllocation} {layouts : LayoutTable}
    {decls : List LocalDecl} (env : SymEnv) (borrows : List BorrowEntry)
    (callerLocals : List LocalSlot) (callStack : List SavedCallerFrame) :
    ∀ {locals : List SymSlot} {ops : List Operand} {vs : List SymVal}
      {locals' : List SymSlot},
      symOperands globals layouts decls locals ops = some (vs, locals') →
      evalOperands (symSlotsEval env locals) ops borrows globals layouts
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
    cases h1 : symOperand globals layouts decls locals op with
    | none => rw [h1] at h; nomatch h
    | some r =>
      obtain ⟨v, locals₁⟩ := r
      rw [h1] at h
      dsimp only at h
      cases h2 : symOperands globals layouts decls locals₁ rest with
      | none => rw [h2] at h; nomatch h
      | some r2 =>
        obtain ⟨vs', locals₂⟩ := r2
        rw [h2] at h
        injection h with h
        injection h with hv hl
        subst hv
        subst hl
        simp only [evalOperands]
        rw [(symOperand_sound h1 env borrows callerLocals callStack).1]
        dsimp only
        rw [symOperands_evalOperands_sound env borrows callerLocals callStack h2]
        rfl

theorem symOperands_sound {globals : List CapturedAllocation} {layouts : LayoutTable}
    {decls : List LocalDecl} (env : SymEnv) (borrows : List BorrowEntry)
    (callerLocals : List LocalSlot) (callStack : List SavedCallerFrame) :
    ∀ {locals : List SymSlot} {ops : List Operand} {vs : List SymVal}
      {locals' : List SymSlot},
      symOperands globals layouts decls locals ops = some (vs, locals') →
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
    cases h1 : symOperand globals layouts decls locals op with
    | none => rw [h1] at h; nomatch h
    | some r =>
      obtain ⟨v, locals₁⟩ := r
      rw [h1] at h
      dsimp only at h
      cases h2 : symOperands globals layouts decls locals₁ rest with
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
          exact (symOperand_sound h1 env borrows callerLocals callStack).2
        simp only [evalOperandsWithBodyCast]
        rw [hOp]
        dsimp only
        rw [symOperands_sound env borrows callerLocals callStack h2]
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

theorem validateLoadedValue_of_validBool {layouts : LayoutTable} {decls : List LocalDecl}
    {op : Operand} {ty : Ty} (hty : operandTy decls layouts op = some ty)
    (hk : ty.kind = .bool) {sc : ScalarInt} (hb : sc.bits = 0 ∨ sc.bits = 1) :
    validateLoadedValue layouts decls op (.scalar sc) = true := by
  have hdisj : Bool.or (Nat.beq sc.bits 0) (Nat.beq sc.bits 1) = true := by
    cases hb with
    | inl h0 => rw [h0]; rfl
    | inr h1 => rw [h1]; rfl
  cases op with
  | constant _ => rfl
  | copy p =>
    simp only [validateLoadedValue, hty, hk, hdisj]
  | move p =>
    simp only [validateLoadedValue, hty, hk, hdisj]

theorem evalSignedDiv_transport (a b sz : Nat) (l₁ l₂ : List LocalSlot) (m₁ m₂ : Memory)
    {v : Value} (h : evalSignedDiv a b sz l₁ m₁ = .ok v l₁ m₁) :
    evalSignedDiv a b sz l₂ m₂ = .ok v l₂ m₂ := by
  unfold evalSignedDiv at h ⊢
  dsimp only at h ⊢
  cases hc : Bool.and (Nat.beq (wrapScalarBits a (scalarModulus sz))
      (scalarPow2 (Nat.sub (Nat.mul sz 8) 1)))
      (Nat.beq (wrapScalarBits b (scalarModulus sz)) (Nat.sub (scalarModulus sz) 1)) with
  | true => rw [hc] at h; nomatch h
  | false => rw [hc] at h; injection h with h1; rw [h1]

theorem evalSignedRem_transport (a b sz : Nat) (l₁ l₂ : List LocalSlot) (m₁ m₂ : Memory)
    {v : Value} (h : evalSignedRem a b sz l₁ m₁ = .ok v l₁ m₁) :
    evalSignedRem a b sz l₂ m₂ = .ok v l₂ m₂ := by
  unfold evalSignedRem at h ⊢
  dsimp only at h ⊢
  cases hc : Bool.and (Nat.beq (wrapScalarBits a (scalarModulus sz))
      (scalarPow2 (Nat.sub (Nat.mul sz 8) 1)))
      (Nat.beq (wrapScalarBits b (scalarModulus sz)) (Nat.sub (scalarModulus sz) 1)) with
  | true => rw [hc] at h; nomatch h
  | false => rw [hc] at h; injection h with h1; rw [h1]

theorem evalScalarBinOp_transport (op : BinOp) (lhs rhs : ScalarInt) (signed : Bool)
    (l₁ l₂ : List LocalSlot) (m₁ m₂ : Memory) {v : Value}
    (h : evalScalarBinOp op lhs rhs l₁ m₁ signed = .ok v l₁ m₁) :
    evalScalarBinOp op lhs rhs l₂ m₂ signed = .ok v l₂ m₂ := by
  unfold evalScalarBinOp at h ⊢
  cases hz : Nat.beq lhs.sizeBytes 0 with
  | true => rw [hz] at h; nomatch h
  | false =>
    rw [hz] at h
    dsimp only at h ⊢
    cases op with
    | shl =>
      cases hr : Nat.beq rhs.sizeBytes 0 with
      | true => rw [hr] at h; nomatch h
      | false => rw [hr] at h; injection h with h1; rw [h1]
    | shlUnchecked =>
      cases hr : Nat.beq rhs.sizeBytes 0 with
      | true => rw [hr] at h; nomatch h
      | false =>
        rw [hr] at h; dsimp only at h ⊢
        cases hb : Nat.ble (Nat.mul lhs.sizeBytes 8) rhs.bits with
        | true => rw [hb] at h; nomatch h
        | false => rw [hb] at h; injection h with h1; rw [h1]
    | shr =>
      cases hr : Nat.beq rhs.sizeBytes 0 with
      | true => rw [hr] at h; nomatch h
      | false => rw [hr] at h; injection h with h1; rw [h1]
    | shrUnchecked =>
      cases hr : Nat.beq rhs.sizeBytes 0 with
      | true => rw [hr] at h; nomatch h
      | false =>
        rw [hr] at h; dsimp only at h ⊢
        cases hb : Nat.ble (Nat.mul lhs.sizeBytes 8) rhs.bits with
        | true => rw [hb] at h; nomatch h
        | false => rw [hb] at h; injection h with h1; rw [h1]
    | add | addWithOverflow | mul | mulWithOverflow | bitAnd | bitOr | bitXor
    | eq | ne | lt | le | gt | ge =>
      cases hw : Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rw [hw] at h; nomatch h
      | true => rw [hw] at h; injection h with h1; rw [h1]
    | sub =>
      cases hw : Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rw [hw] at h; nomatch h
      | true =>
        rw [hw] at h; dsimp only at h ⊢
        cases hb : Nat.ble rhs.bits lhs.bits <;> (rw [hb] at h; injection h with h1; rw [h1])
    | subWithOverflow =>
      cases hw : Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rw [hw] at h; nomatch h
      | true =>
        rw [hw] at h; dsimp only at h ⊢
        cases signed with
        | true => injection h with h1; rw [h1]
        | false =>
          dsimp only at h ⊢
          cases hb : Nat.ble rhs.bits lhs.bits <;> (rw [hb] at h; injection h with h1; rw [h1])
    | addUnchecked =>
      cases hw : Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rw [hw] at h; nomatch h
      | true =>
        rw [hw] at h; dsimp only at h ⊢
        cases signed with
        | false =>
          dsimp only at h ⊢
          cases hb : Nat.ble (scalarModulus lhs.sizeBytes) (Nat.add lhs.bits rhs.bits) with
          | true => rw [hb] at h; nomatch h
          | false => rw [hb] at h; injection h with h1; rw [h1]
        | true =>
          dsimp only at h ⊢
          cases hb : signedOverflowAdd lhs.bits rhs.bits lhs.sizeBytes with
          | true => rw [hb] at h; nomatch h
          | false => rw [hb] at h; injection h with h1; rw [h1]
    | subUnchecked =>
      cases hw : Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rw [hw] at h; nomatch h
      | true =>
        rw [hw] at h; dsimp only at h ⊢
        cases signed with
        | false =>
          dsimp only at h ⊢
          cases hb : Nat.ble rhs.bits lhs.bits with
          | false => rw [hb] at h; nomatch h
          | true =>
            rw [hb] at h; dsimp only at h ⊢
            cases hd : Nat.ble (scalarModulus lhs.sizeBytes) (Nat.sub lhs.bits rhs.bits) with
            | true => rw [hd] at h; nomatch h
            | false => rw [hd] at h; injection h with h1; rw [h1]
        | true =>
          dsimp only at h ⊢
          cases hb : signedOverflowSub lhs.bits rhs.bits lhs.sizeBytes with
          | true => rw [hb] at h; nomatch h
          | false => rw [hb] at h; injection h with h1; rw [h1]
    | mulUnchecked =>
      cases hw : Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rw [hw] at h; nomatch h
      | true =>
        rw [hw] at h; dsimp only at h ⊢
        cases signed with
        | false =>
          dsimp only at h ⊢
          cases hb : Nat.ble (scalarModulus lhs.sizeBytes) (Nat.mul lhs.bits rhs.bits) with
          | true => rw [hb] at h; nomatch h
          | false => rw [hb] at h; injection h with h1; rw [h1]
        | true =>
          dsimp only at h ⊢
          cases hb : signedOverflowMul lhs.bits rhs.bits lhs.sizeBytes with
          | true => rw [hb] at h; nomatch h
          | false => rw [hb] at h; injection h with h1; rw [h1]
    | div =>
      cases hw : Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rw [hw] at h; nomatch h
      | true =>
        rw [hw] at h; dsimp only at h ⊢
        cases hb : Nat.beq rhs.bits 0 with
        | true => rw [hb] at h; nomatch h
        | false =>
          rw [hb] at h; dsimp only at h ⊢
          cases signed with
          | false => injection h with h1; rw [h1]
          | true => exact evalSignedDiv_transport lhs.bits rhs.bits lhs.sizeBytes l₁ l₂ m₁ m₂ h
    | rem =>
      cases hw : Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rw [hw] at h; nomatch h
      | true =>
        rw [hw] at h; dsimp only at h ⊢
        cases hb : Nat.beq rhs.bits 0 with
        | true => rw [hb] at h; nomatch h
        | false =>
          rw [hb] at h; dsimp only at h ⊢
          cases signed with
          | false => injection h with h1; rw [h1]
          | true => exact evalSignedRem_transport lhs.bits rhs.bits lhs.sizeBytes l₁ l₂ m₁ m₂ h
    | cmp =>
      cases hw : Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rw [hw] at h; nomatch h
      | true =>
        rw [hw] at h; dsimp only at h ⊢
        cases signed with
        | false =>
          dsimp only at h ⊢
          cases heq : Nat.beq lhs.bits rhs.bits with
          | true => rw [heq] at h; injection h with h1; rw [h1]
          | false =>
            rw [heq] at h; dsimp only at h ⊢
            cases hle : Nat.ble lhs.bits rhs.bits <;> (rw [hle] at h; injection h with h1; rw [h1])
        | true =>
          dsimp only at h ⊢
          cases heq : Nat.beq (wrapScalarBits lhs.bits (scalarModulus lhs.sizeBytes))
              (wrapScalarBits rhs.bits (scalarModulus lhs.sizeBytes)) with
          | true => rw [heq] at h; injection h with h1; rw [h1]
          | false =>
            rw [heq] at h; dsimp only at h ⊢
            cases hlt : signedLt (wrapScalarBits lhs.bits (scalarModulus lhs.sizeBytes))
                (wrapScalarBits rhs.bits (scalarModulus lhs.sizeBytes)) lhs.sizeBytes <;>
              (rw [hlt] at h; injection h with h1; rw [h1])
    | offset =>
      cases hw : Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rw [hw] at h; nomatch h
      | true => rw [hw] at h; nomatch h

theorem evalScalarBinOp_ok_scalar {op : BinOp} {signed : Bool} {x y sc : ScalarInt}
    (h : evalScalarBinOp op x y [] emptyMemory signed = .ok (.scalar sc) [] emptyMemory)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp op x y locals mem signed =
      .ok (.scalar ((symBinOpEval op signed x y).getD symDefaultScalar)) locals mem := by
  have hsym : symBinOpEval op signed x y = some sc := by
    unfold symBinOpEval
    rw [h]
  rw [hsym]
  exact evalScalarBinOp_transport op x y signed [] locals emptyMemory mem h

theorem evalScalarBinOp_ok_checked {k : SymOverflowKind} {signed : Bool} {x y sv sf : ScalarInt}
    (h : evalScalarBinOp (symOverflowToBinOp k) x y [] emptyMemory signed =
      .ok (.aggregate 0 [.scalar sv, .scalar sf]) [] emptyMemory)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp (symOverflowToBinOp k) x y locals mem signed =
      .ok (.aggregate 0
        [.scalar ((symCheckedValEval k signed x y).getD symDefaultScalar),
         .scalar ((symCheckedFlagEval k signed x y).getD symDefaultScalar)]) locals mem := by
  have hv : symCheckedValEval k signed x y = some sv := by
    unfold symCheckedValEval; rw [h]
    rfl
  have hf : symCheckedFlagEval k signed x y = some sf := by
    unfold symCheckedFlagEval; rw [h]
    rfl
  rw [hv, hf]
  exact evalScalarBinOp_transport (symOverflowToBinOp k) x y signed [] locals emptyMemory mem h

theorem symScalarBinOp_sound {op : BinOp} {signed : Bool} {a b : SymScalar} {res : SymVal}
    {cs : List SymCond} (h : symScalarBinOp op signed a b = some (res, cs)) (env : SymEnv)
    (hc : condsHold env cs) (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp op (a.eval env) (b.eval env) locals mem signed =
      .ok (res.eval env) locals mem := by
  cases op with
  | offset => nomatch h
  | add | mul | bitAnd | bitOr | bitXor | eq | ne | lt | le | gt | ge =>
    injection h with h; injection h with h1 h2; subst h1; subst h2
    have hw : ScWidthsOk (a.eval env) (b.eval env) := hc.1
    change evalScalarBinOp _ (a.eval env) (b.eval env) locals mem signed =
      .ok (.scalar ((SymScalar.binOp _ signed a b).eval env)) locals mem
    rw [SymScalar.eval_binOp]
    exact evalScalarBinOp_ok_scalar (by
      unfold evalScalarBinOp
      rw [nat_beq_false_of_ne hw.1, nat_beq_true_of_eq hw.2]) locals mem
  | sub =>
    injection h with h; injection h with h1 h2; subst h1; subst h2
    have hw : ScWidthsOk (a.eval env) (b.eval env) := hc.1
    change evalScalarBinOp .sub (a.eval env) (b.eval env) locals mem signed =
      .ok (.scalar ((SymScalar.binOp .sub signed a b).eval env)) locals mem
    rw [SymScalar.eval_binOp]
    cases hb : Nat.ble (b.eval env).bits (a.eval env).bits with
    | true =>
      exact evalScalarBinOp_ok_scalar (by
        unfold evalScalarBinOp
        rw [nat_beq_false_of_ne hw.1, nat_beq_true_of_eq hw.2]
        dsimp only; rw [hb]) locals mem
    | false =>
      exact evalScalarBinOp_ok_scalar (by
        unfold evalScalarBinOp
        rw [nat_beq_false_of_ne hw.1, nat_beq_true_of_eq hw.2]
        dsimp only; rw [hb]) locals mem
  | cmp =>
    injection h with h; injection h with h1 h2; subst h1; subst h2
    have hw : ScWidthsOk (a.eval env) (b.eval env) := hc.1
    change evalScalarBinOp .cmp (a.eval env) (b.eval env) locals mem signed =
      .ok (.scalar ((SymScalar.binOp .cmp signed a b).eval env)) locals mem
    rw [SymScalar.eval_binOp]
    cases signed with
    | false =>
      cases heq : Nat.beq (a.eval env).bits (b.eval env).bits with
      | true =>
        exact evalScalarBinOp_ok_scalar (by
          unfold evalScalarBinOp
          rw [nat_beq_false_of_ne hw.1, nat_beq_true_of_eq hw.2]
          dsimp only; rw [heq]) locals mem
      | false =>
        cases hle : Nat.ble (a.eval env).bits (b.eval env).bits <;>
          exact evalScalarBinOp_ok_scalar (by
            unfold evalScalarBinOp
            rw [nat_beq_false_of_ne hw.1, nat_beq_true_of_eq hw.2]
            dsimp only; rw [heq]; dsimp only; rw [hle]) locals mem
    | true =>
      cases heq : Nat.beq (wrapScalarBits (a.eval env).bits (scalarModulus (a.eval env).sizeBytes))
          (wrapScalarBits (b.eval env).bits (scalarModulus (a.eval env).sizeBytes)) with
      | true =>
        exact evalScalarBinOp_ok_scalar (by
          unfold evalScalarBinOp
          rw [nat_beq_false_of_ne hw.1, nat_beq_true_of_eq hw.2]
          dsimp only; rw [heq]) locals mem
      | false =>
        cases hlt : signedLt (wrapScalarBits (a.eval env).bits (scalarModulus (a.eval env).sizeBytes))
            (wrapScalarBits (b.eval env).bits (scalarModulus (a.eval env).sizeBytes))
            (a.eval env).sizeBytes <;>
          exact evalScalarBinOp_ok_scalar (by
            unfold evalScalarBinOp
            rw [nat_beq_false_of_ne hw.1, nat_beq_true_of_eq hw.2]
            dsimp only; rw [heq]; dsimp only; rw [hlt]) locals mem
  | shl | shr =>
    injection h with h; injection h with h1 h2; subst h1; subst h2
    have hwa : (a.eval env).sizeBytes ≠ 0 := hc.1
    have hwb : (b.eval env).sizeBytes ≠ 0 := hc.2.1
    change evalScalarBinOp _ (a.eval env) (b.eval env) locals mem signed =
      .ok (.scalar ((SymScalar.binOp _ signed a b).eval env)) locals mem
    rw [SymScalar.eval_binOp]
    exact evalScalarBinOp_ok_scalar (by
      unfold evalScalarBinOp
      rw [nat_beq_false_of_ne hwa, nat_beq_false_of_ne hwb]) locals mem
  | shlUnchecked | shrUnchecked =>
    injection h with h; injection h with h1 h2; subst h1; subst h2
    have hwa : (a.eval env).sizeBytes ≠ 0 := hc.1.1
    have hwb : (b.eval env).sizeBytes ≠ 0 := hc.1.2.1
    have hlt : (b.eval env).bits < Nat.mul (a.eval env).sizeBytes 8 := hc.1.2.2
    change evalScalarBinOp _ (a.eval env) (b.eval env) locals mem signed =
      .ok (.scalar ((SymScalar.binOp _ signed a b).eval env)) locals mem
    rw [SymScalar.eval_binOp]
    exact evalScalarBinOp_ok_scalar (by
      unfold evalScalarBinOp
      rw [nat_beq_false_of_ne hwa, nat_beq_false_of_ne hwb]
      dsimp only
      rw [nat_ble_false_of_lt hlt]) locals mem
  | addWithOverflow =>
    injection h with h; injection h with h1 h2; subst h1; subst h2
    have hw : ScWidthsOk (a.eval env) (b.eval env) := hc.1
    change evalScalarBinOp .addWithOverflow (a.eval env) (b.eval env) locals mem signed =
      .ok (.aggregate 0 [.scalar ((SymScalar.checkedVal .add signed a b).eval env),
        .scalar ((SymScalar.checkedFlag .add signed a b).eval env)]) locals mem
    rw [SymScalar.eval_checkedVal, SymScalar.eval_checkedFlag]
    exact evalScalarBinOp_ok_checked (k := .add) (by
      unfold evalScalarBinOp symOverflowToBinOp
      rw [nat_beq_false_of_ne hw.1, nat_beq_true_of_eq hw.2]) locals mem
  | mulWithOverflow =>
    injection h with h; injection h with h1 h2; subst h1; subst h2
    have hw : ScWidthsOk (a.eval env) (b.eval env) := hc.1
    change evalScalarBinOp .mulWithOverflow (a.eval env) (b.eval env) locals mem signed =
      .ok (.aggregate 0 [.scalar ((SymScalar.checkedVal .mul signed a b).eval env),
        .scalar ((SymScalar.checkedFlag .mul signed a b).eval env)]) locals mem
    rw [SymScalar.eval_checkedVal, SymScalar.eval_checkedFlag]
    exact evalScalarBinOp_ok_checked (k := .mul) (by
      unfold evalScalarBinOp symOverflowToBinOp
      rw [nat_beq_false_of_ne hw.1, nat_beq_true_of_eq hw.2]) locals mem
  | subWithOverflow =>
    injection h with h; injection h with h1 h2; subst h1; subst h2
    have hw : ScWidthsOk (a.eval env) (b.eval env) := hc.1
    change evalScalarBinOp .subWithOverflow (a.eval env) (b.eval env) locals mem signed =
      .ok (.aggregate 0 [.scalar ((SymScalar.checkedVal .sub signed a b).eval env),
        .scalar ((SymScalar.checkedFlag .sub signed a b).eval env)]) locals mem
    rw [SymScalar.eval_checkedVal, SymScalar.eval_checkedFlag]
    cases signed with
    | true =>
      exact evalScalarBinOp_ok_checked (k := .sub) (by
        unfold evalScalarBinOp symOverflowToBinOp
        rw [nat_beq_false_of_ne hw.1, nat_beq_true_of_eq hw.2]) locals mem
    | false =>
      cases hb : Nat.ble (b.eval env).bits (a.eval env).bits <;>
        exact evalScalarBinOp_ok_checked (k := .sub) (by
          unfold evalScalarBinOp symOverflowToBinOp
          rw [nat_beq_false_of_ne hw.1, nat_beq_true_of_eq hw.2]
          dsimp only; rw [hb]) locals mem
  | addUnchecked =>
    injection h with h; injection h with h1 h2; subst h1; subst h2
    have hw : ScWidthsOk (a.eval env) (b.eval env) := hc.1.1
    change evalScalarBinOp .addUnchecked (a.eval env) (b.eval env) locals mem signed =
      .ok (.scalar ((SymScalar.binOp .addUnchecked signed a b).eval env)) locals mem
    rw [SymScalar.eval_binOp]
    cases signed with
    | false =>
      have hlt : Nat.add (a.eval env).bits (b.eval env).bits < scalarModulus (a.eval env).sizeBytes :=
        hc.1.2
      exact evalScalarBinOp_ok_scalar (by
        unfold evalScalarBinOp
        rw [nat_beq_false_of_ne hw.1, nat_beq_true_of_eq hw.2]
        dsimp only; rw [nat_ble_false_of_lt hlt]) locals mem
    | true =>
      have ho : signedOverflowAdd (a.eval env).bits (b.eval env).bits (a.eval env).sizeBytes =
          false := hc.1.2
      exact evalScalarBinOp_ok_scalar (by
        unfold evalScalarBinOp
        rw [nat_beq_false_of_ne hw.1, nat_beq_true_of_eq hw.2]
        dsimp only; rw [ho]) locals mem
  | subUnchecked =>
    injection h with h; injection h with h1 h2; subst h1; subst h2
    have hw : ScWidthsOk (a.eval env) (b.eval env) := hc.1.1
    change evalScalarBinOp .subUnchecked (a.eval env) (b.eval env) locals mem signed =
      .ok (.scalar ((SymScalar.binOp .subUnchecked signed a b).eval env)) locals mem
    rw [SymScalar.eval_binOp]
    cases signed with
    | false =>
      have hle : (b.eval env).bits ≤ (a.eval env).bits := hc.1.2.1
      have hlt : Nat.sub (a.eval env).bits (b.eval env).bits <
          scalarModulus (a.eval env).sizeBytes := hc.1.2.2
      exact evalScalarBinOp_ok_scalar (by
        unfold evalScalarBinOp
        rw [nat_beq_false_of_ne hw.1, nat_beq_true_of_eq hw.2]
        dsimp only
        rw [Nat.ble_eq_true_of_le hle]
        dsimp only
        rw [nat_ble_false_of_lt hlt]) locals mem
    | true =>
      have ho : signedOverflowSub (a.eval env).bits (b.eval env).bits (a.eval env).sizeBytes =
          false := hc.1.2
      exact evalScalarBinOp_ok_scalar (by
        unfold evalScalarBinOp
        rw [nat_beq_false_of_ne hw.1, nat_beq_true_of_eq hw.2]
        dsimp only; rw [ho]) locals mem
  | mulUnchecked =>
    injection h with h; injection h with h1 h2; subst h1; subst h2
    have hw : ScWidthsOk (a.eval env) (b.eval env) := hc.1.1
    change evalScalarBinOp .mulUnchecked (a.eval env) (b.eval env) locals mem signed =
      .ok (.scalar ((SymScalar.binOp .mulUnchecked signed a b).eval env)) locals mem
    rw [SymScalar.eval_binOp]
    cases signed with
    | false =>
      have hlt : Nat.mul (a.eval env).bits (b.eval env).bits < scalarModulus (a.eval env).sizeBytes :=
        hc.1.2
      exact evalScalarBinOp_ok_scalar (by
        unfold evalScalarBinOp
        rw [nat_beq_false_of_ne hw.1, nat_beq_true_of_eq hw.2]
        dsimp only; rw [nat_ble_false_of_lt hlt]) locals mem
    | true =>
      have ho : signedOverflowMul (a.eval env).bits (b.eval env).bits (a.eval env).sizeBytes =
          false := hc.1.2
      exact evalScalarBinOp_ok_scalar (by
        unfold evalScalarBinOp
        rw [nat_beq_false_of_ne hw.1, nat_beq_true_of_eq hw.2]
        dsimp only; rw [ho]) locals mem
  | div =>
    injection h with h; injection h with h1 h2; subst h1; subst h2
    have hw : ScWidthsOk (a.eval env) (b.eval env) := hc.1.1
    have hnz : (b.eval env).bits ≠ 0 := hc.1.2.1
    change evalScalarBinOp .div (a.eval env) (b.eval env) locals mem signed =
      .ok (.scalar ((SymScalar.binOp .div signed a b).eval env)) locals mem
    rw [SymScalar.eval_binOp]
    cases signed with
    | false =>
      exact evalScalarBinOp_ok_scalar (by
        unfold evalScalarBinOp
        rw [nat_beq_false_of_ne hw.1, nat_beq_true_of_eq hw.2]
        dsimp only; rw [nat_beq_false_of_ne hnz]) locals mem
    | true =>
      have hm : ScNotMinNegOne (a.eval env) (b.eval env) := hc.1.2.2
      exact evalScalarBinOp_ok_scalar (by
        unfold evalScalarBinOp
        rw [nat_beq_false_of_ne hw.1, nat_beq_true_of_eq hw.2]
        dsimp only; rw [nat_beq_false_of_ne hnz]
        dsimp only [evalSignedDiv]
        rw [minNegOne_guard_false hm]) locals mem
  | rem =>
    injection h with h; injection h with h1 h2; subst h1; subst h2
    have hw : ScWidthsOk (a.eval env) (b.eval env) := hc.1.1
    have hnz : (b.eval env).bits ≠ 0 := hc.1.2.1
    change evalScalarBinOp .rem (a.eval env) (b.eval env) locals mem signed =
      .ok (.scalar ((SymScalar.binOp .rem signed a b).eval env)) locals mem
    rw [SymScalar.eval_binOp]
    cases signed with
    | false =>
      exact evalScalarBinOp_ok_scalar (by
        unfold evalScalarBinOp
        rw [nat_beq_false_of_ne hw.1, nat_beq_true_of_eq hw.2]
        dsimp only; rw [nat_beq_false_of_ne hnz]) locals mem
    | true =>
      have hm : ScNotMinNegOne (a.eval env) (b.eval env) := hc.1.2.2
      exact evalScalarBinOp_ok_scalar (by
        unfold evalScalarBinOp
        rw [nat_beq_false_of_ne hw.1, nat_beq_true_of_eq hw.2]
        dsimp only; rw [nat_beq_false_of_ne hnz]
        dsimp only [evalSignedRem]
        rw [minNegOne_guard_false hm]) locals mem

theorem evalPlaceDiscriminant_aggregate_eq {variantIdx : VariantIdx} {fs : List SymScalar}
    {place : Place} {decls : List LocalDecl} {layouts : LayoutTable} {sc : ScalarInt}
    (h : symAggDiscriminant? variantIdx (length fs) place decls layouts = some sc)
    (env : SymEnv) (locals : List LocalSlot) (mem : Memory) :
    evalPlaceDiscriminant (.aggregate variantIdx (symFieldsEval env fs)) locals mem place
      decls layouts = .ok (.scalar sc) locals mem := by
  unfold evalPlaceDiscriminant
  dsimp only
  rw [valueListContainsUninit_symFieldsEval]
  dsimp only
  unfold symAggDiscriminant? at h
  cases hty : placeTyResolved decls layouts place with
  | none =>
    rw [hty] at h
    injection h with h1
    rw [← h1]
  | some pTy =>
    rw [hty] at h
    dsimp only at h ⊢
    cases hk : pTy.kind with
    | never => rw [hk] at h; nomatch h
    | tuple _ | array _ _ | slice _ | str =>
      rw [hk] at h
      dsimp only at h ⊢
      cases hv : Nat.beq variantIdx 0 with
      | false => rw [hv] at h; nomatch h
      | true => rw [hv] at h; injection h with h1; rw [← h1]
    | adt defPath _ =>
      rw [hk] at h
      dsimp only at h ⊢
      rw [length_symFieldsEval]
      cases hl : LayoutTable.lookup layouts pTy.layoutIdx with
      | none =>
        rw [hl] at h; dsimp only at h ⊢
        cases hord : Bool.and (stringEq defPath "core::cmp::Ordering") (Nat.beq (length fs) 0) with
        | false => rw [hord] at h; injection h with h1; rw [← h1]
        | true =>
          rw [hord] at h; dsimp only at h ⊢
          match variantIdx, h with
          | 0, h => injection h with h1; rw [← h1]; rfl
          | 1, h => injection h with h1; rw [← h1]; rfl
          | 2, h => injection h with h1; rw [← h1]; rfl
          | _ + 3, h => nomatch h
      | some lay =>
        rw [hl] at h
        cases lay with
        | mk _ _ _ _ variants isUninhabited _ _ =>
          cases isUninhabited with
          | true => nomatch h
          | false =>
            cases variants with
            | empty => nomatch h
            | single expectedIdx =>
              dsimp only at h ⊢
              cases heq : Nat.beq variantIdx expectedIdx with
              | false => rw [heq] at h; nomatch h
              | true => rw [heq] at h; injection h with h1; rw [← h1]
            | multiple _ _ variants =>
              dsimp only at h ⊢
              cases variants with
              | nil =>
                dsimp only at h ⊢
                cases hord : Bool.and (stringEq defPath "core::cmp::Ordering") (Nat.beq (length fs) 0) with
                | false => rw [hord] at h; injection h with h1; rw [← h1]
                | true =>
                  rw [hord] at h; dsimp only at h ⊢
                  match variantIdx, h with
                  | 0, h => injection h with h1; rw [← h1]; rfl
                  | 1, h => injection h with h1; rw [← h1]; rfl
                  | 2, h => injection h with h1; rw [← h1]; rfl
                  | _ + 3, h => nomatch h
              | cons vh vt =>
                dsimp only at h ⊢
                cases hvb : Nat.ble (.succ variantIdx) (length (vh :: vt)) with
                | false => rw [hvb] at h; nomatch h
                | true =>
                  rw [hvb] at h; dsimp only at h ⊢
                  cases hord : Bool.and (stringEq defPath "core::cmp::Ordering") (Nat.beq (length fs) 0) with
                  | false => rw [hord] at h; injection h with h1; rw [← h1]
                  | true =>
                    rw [hord] at h; dsimp only at h ⊢
                    match variantIdx, h with
                    | 0, h => injection h with h1; rw [← h1]; rfl
                    | 1, h => injection h with h1; rw [← h1]; rfl
                    | 2, h => injection h with h1; rw [← h1]; rfl
                    | _ + 3, h => nomatch h
    | bool | char | int _ | uint _ | float _ | ref _ _ | rawPtr _ _
    | fnDef _ _ | fnPtr _ _ _ _ | closure _ | alias | dynamic
    | param _ | foreign _ | other _ =>
      rw [hk] at h
      injection h with h1
      rw [← h1]

theorem symRvalue_sound {globals : List CapturedAllocation} {layouts : LayoutTable}
    {decls : List LocalDecl} {locals : List SymSlot} {rv : Rvalue} {v : SymVal}
    {locals' : List SymSlot} {cs : List SymCond}
    (h : symRvalue globals layouts decls locals rv = some (v, locals', cs)) (env : SymEnv)
    (hc : condsHold env cs) (mem : Memory) (hg : mem.globals = globals) (hb : mem.borrows = []) :
    evalRvalue (symSlotsEval env locals) rv mem decls layouts =
      .ok (v.eval env) (symSlotsEval env locals') mem := by
  cases rv with
  | use op =>
    simp only [symRvalue] at h
    cases h1 : symOperand globals layouts decls locals op with
    | none => rw [h1] at h; nomatch h
    | some r =>
      obtain ⟨w, l₁⟩ := r
      rw [h1] at h
      dsimp only at h
      have hOp := (symOperand_sound h1 env mem.borrows mem.callerLocals mem.callStack).1
      have hTail : ∀ (v' : SymVal) (l' : List SymSlot),
          validateLoadedValue layouts decls op (v'.eval env) = true →
          symOperand globals layouts decls locals op = some (v', l') →
          evalRvalue (symSlotsEval env locals) (.use op) mem decls layouts =
            .ok (v'.eval env) (symSlotsEval env l') mem := by
        intro v' l' hval hop
        simp only [evalRvalue]
        rw [hg, (symOperand_sound hop env mem.borrows mem.callerLocals mem.callStack).1]
        dsimp only
        rw [hval]
        dsimp only
        rw [hb]
        cases op with
        | constant _ => rfl
        | copy p =>
          obtain ⟨loc, proj⟩ := p
          cases proj with
          | nil => rfl
          | cons pe _ => cases pe <;> first | rfl | nomatch hop
        | move p =>
          obtain ⟨loc, proj⟩ := p
          cases proj with
          | nil => rfl
          | cons pe _ => cases pe <;> first | rfl | nomatch hop
      cases h2 : loadedValueStaticOk layouts decls op with
      | true =>
        rw [h2] at h
        injection h with h
        injection h with hv h
        injection h with hl _
        subst hv
        subst hl
        exact hTail w l₁ (validateLoadedValue_of_static h2 _) h1
      | false =>
        rw [h2] at h
        dsimp only at h
        cases hty : operandTy decls layouts op with
        | none => rw [hty] at h; nomatch h
        | some ty =>
          rw [hty] at h
          dsimp only at h
          cases hk : ty.kind with
          | bool =>
            rw [hk] at h
            cases has : w.asScalar? with
            | none => rw [has] at h; nomatch h
            | some sc =>
              rw [has] at h
              injection h with h
              injection h with hv h
              injection h with hl hcs
              subst hv
              subst hl
              subst hcs
              have hval : validateLoadedValue layouts decls op (w.eval env) = true := by
                rw [symVal_eval_of_asScalar has env]
                exact validateLoadedValue_of_validBool hty hk hc.1.2
              exact hTail w l₁ hval h1
          | char | int _ | uint _ | float _ | ref _ _ | rawPtr _ _ | array _ _ | slice _
          | str | tuple _ | adt _ _ | fnDef _ _ | fnPtr _ _ _ _ | closure _ | alias
          | never | dynamic | param _ | foreign _ | other _ =>
            rw [hk] at h; nomatch h
  | unaryOp uop op =>
    cases uop with
    | ptrMetadata => nomatch h
    | neg =>
      simp only [symRvalue] at h
      cases h1 : symOperand globals layouts decls locals op with
      | none => rw [h1] at h; nomatch h
      | some r =>
        obtain ⟨w, l₁⟩ := r
        rw [h1] at h; dsimp only at h
        cases ha : w.asScalar? with
        | none => rw [ha] at h; nomatch h
        | some x =>
          rw [ha] at h
          injection h with h; injection h with hv h; injection h with hl hcs
          subst hv; subst hl; subst hcs
          simp only [evalRvalue]
          rw [hg, (symOperand_sound h1 env mem.borrows mem.callerLocals mem.callStack).1,
            symVal_eval_of_asScalar ha env]
          dsimp only
          rw [nat_beq_false_of_ne hc.1]
          rfl
    | not =>
      simp only [symRvalue] at h
      cases h1 : symOperand globals layouts decls locals op with
      | none => rw [h1] at h; nomatch h
      | some r =>
        obtain ⟨w, l₁⟩ := r
        rw [h1] at h; dsimp only at h
        cases ha : w.asScalar? with
        | none => rw [ha] at h; nomatch h
        | some x =>
          rw [ha] at h; dsimp only at h
          cases hty : operandTy decls layouts op with
          | none => rw [hty] at h; nomatch h
          | some ty =>
            rw [hty] at h; dsimp only at h
            cases hk : ty.kind with
            | bool =>
              rw [hk] at h
              injection h with h; injection h with hv h; injection h with hl hcs
              subst hv; subst hl; subst hcs
              simp only [evalRvalue]
              rw [hg, (symOperand_sound h1 env mem.borrows mem.callerLocals mem.callStack).1,
                symVal_eval_of_asScalar ha env]
              dsimp only [evalUnaryNot]
              rw [hty]
              dsimp only
              rw [hk]
              dsimp only
              rw [nat_beq_true_of_eq hc.1.1]
              dsimp only
              cases hc.1.2 with
              | inl h0 =>
                rw [nat_beq_true_of_eq h0]
                show RvalueEvalResult.ok (.scalar ⟨1, 1⟩) _ _ =
                  .ok (.scalar ⟨match Nat.beq (x.eval env).bits 0 with | true => 1 | false => 0, 1⟩) _ _
                rw [nat_beq_true_of_eq h0]
              | inr h1b =>
                show (match Nat.beq (x.eval env).bits 0 with
                  | true => RvalueEvalResult.ok (.scalar ⟨1, 1⟩) _ _
                  | false => match Nat.beq (x.eval env).bits 1 with
                    | true => .ok (.scalar ⟨0, 1⟩) _ _
                    | false => .ub) =
                  .ok (.scalar ⟨match Nat.beq (x.eval env).bits 0 with | true => 1 | false => 0, 1⟩) _ _
                rw [h1b]
            | uint _ | int _ =>
              rw [hk] at h
              injection h with h; injection h with hv h; injection h with hl hcs
              subst hv; subst hl; subst hcs
              simp only [evalRvalue]
              rw [hg, (symOperand_sound h1 env mem.borrows mem.callerLocals mem.callStack).1,
                symVal_eval_of_asScalar ha env]
              dsimp only [evalUnaryNot]
              rw [hty]
              dsimp only
              rw [hk]
              dsimp only
              rw [nat_beq_false_of_ne hc.1]
              rfl
            | char | float _ | ref _ _ | rawPtr _ _ | array _ _ | slice _ | str | tuple _
            | adt _ _ | fnDef _ _ | fnPtr _ _ _ _ | closure _ | alias | never | dynamic
            | param _ | foreign _ | other _ =>
              rw [hk] at h; nomatch h
  | binaryOp op lhsOp rhsOp =>
    simp only [symRvalue] at h
    cases h1 : symOperand globals layouts decls locals lhsOp with
    | none => rw [h1] at h; nomatch h
    | some r1 =>
      obtain ⟨lv, l₁⟩ := r1
      rw [h1] at h; dsimp only at h
      cases h2 : symOperand globals layouts decls l₁ rhsOp with
      | none => rw [h2] at h; nomatch h
      | some r2 =>
        obtain ⟨rv', l₂⟩ := r2
        rw [h2] at h; dsimp only at h
        cases ha : lv.asScalar? with
        | none => rw [ha] at h; nomatch h
        | some a =>
          cases hb' : rv'.asScalar? with
          | none => rw [ha, hb'] at h; nomatch h
          | some b =>
            rw [ha, hb'] at h; dsimp only at h
            cases hs : symScalarBinOp op (operandIsSigned decls lhsOp layouts) a b with
            | none => rw [hs] at h; nomatch h
            | some r3 =>
              obtain ⟨res, cs'⟩ := r3
              rw [hs] at h
              injection h with h; injection h with hv h; injection h with hl hcs
              subst hv; subst hl; subst hcs
              simp only [evalRvalue]
              rw [hg, (symOperand_sound h1 env mem.borrows mem.callerLocals mem.callStack).1]
              dsimp only
              rw [(symOperand_sound h2 env mem.borrows mem.callerLocals mem.callStack).1,
                symVal_eval_of_asScalar ha env, symVal_eval_of_asScalar hb' env]
              cases op with
              | offset => nomatch hs
              | add | addUnchecked | addWithOverflow | sub | subUnchecked | subWithOverflow
              | mul | mulUnchecked | mulWithOverflow | div | rem | bitXor | bitAnd | bitOr
              | shl | shlUnchecked | shr | shrUnchecked | eq | lt | le | ne | ge | gt | cmp =>
                exact symScalarBinOp_sound hs env hc (symSlotsEval env l₂) mem
  | cast ck op targetTy =>
    cases ck with
    | intToInt =>
      simp only [symRvalue] at h
      cases h1 : symOperand globals layouts decls locals op with
      | none => rw [h1] at h; nomatch h
      | some r =>
        obtain ⟨w, l₁⟩ := r
        rw [h1] at h; dsimp only at h
        cases ha : w.asScalar? with
        | none => rw [ha] at h; nomatch h
        | some x =>
          cases ht : intCastTargetBytes targetTy.kind with
          | none => rw [ha, ht] at h; nomatch h
          | some tb =>
            rw [ha, ht] at h
            injection h with h; injection h with hv h; injection h with hl hcs
            subst hv; subst hl; subst hcs
            simp only [evalRvalue]
            rw [hg, (symOperand_sound h1 env mem.borrows mem.callerLocals mem.callStack).1,
              symVal_eval_of_asScalar ha env]
            dsimp only
            rw [nat_beq_false_of_ne hc.1, ht]
            rfl
    | _ => nomatch h
  | aggregate ak ops =>
    cases ak with
    | tuple =>
      simp only [symRvalue] at h
      cases h1 : symOperands globals layouts decls locals ops with
      | none => rw [h1] at h; nomatch h
      | some r =>
        obtain ⟨vs, l₁⟩ := r
        rw [h1] at h; dsimp only at h
        cases h2 : symValsAsScalars? vs with
        | none => rw [h2] at h; nomatch h
        | some fs =>
          rw [h2] at h
          injection h with h; injection h with hv h; injection h with hl _
          subst hv; subst hl
          simp only [evalRvalue]
          rw [hg, symOperands_evalOperands_sound env mem.borrows mem.callerLocals mem.callStack h1,
            symValsAsScalars?_sound env h2]
          rfl
    | array _ =>
      simp only [symRvalue] at h
      cases h1 : symOperands globals layouts decls locals ops with
      | none => rw [h1] at h; nomatch h
      | some r =>
        obtain ⟨vs, l₁⟩ := r
        rw [h1] at h; dsimp only at h
        cases h2 : symValsAsScalars? vs with
        | none => rw [h2] at h; nomatch h
        | some fs =>
          rw [h2] at h
          injection h with h; injection h with hv h; injection h with hl _
          subst hv; subst hl
          simp only [evalRvalue]
          rw [hg, symOperands_evalOperands_sound env mem.borrows mem.callerLocals mem.callStack h1,
            symValsAsScalars?_sound env h2]
          rfl
    | closure _ =>
      simp only [symRvalue] at h
      cases h1 : symOperands globals layouts decls locals ops with
      | none => rw [h1] at h; nomatch h
      | some r =>
        obtain ⟨vs, l₁⟩ := r
        rw [h1] at h; dsimp only at h
        cases h2 : symValsAsScalars? vs with
        | none => rw [h2] at h; nomatch h
        | some fs =>
          rw [h2] at h
          injection h with h; injection h with hv h; injection h with hl _
          subst hv; subst hl
          simp only [evalRvalue]
          rw [hg, symOperands_evalOperands_sound env mem.borrows mem.callerLocals mem.callStack h1,
            symValsAsScalars?_sound env h2]
          rfl
    | adt _ _ _ => nomatch h
    | rawPtr _ _ => nomatch h
    | coroutine _ => nomatch h
  | discriminant place =>
    obtain ⟨ploc, pproj⟩ := place
    cases pproj with
    | cons _ _ => nomatch h
    | nil =>
      simp only [symRvalue] at h
      cases hg' : get? locals ploc with
      | none => rw [hg'] at h; nomatch h
      | some sl =>
        rw [hg'] at h
        cases sl with
        | dead => nomatch h
        | uninit => nomatch h
        | init w =>
          cases w with
          | aggregate vidx fs =>
            dsimp only at h
            cases hd : symAggDiscriminant? vidx (length fs) { local_ := ploc, projection := [] }
                decls layouts with
            | none => rw [hd] at h; nomatch h
            | some sc =>
              rw [hd] at h
              injection h with h; injection h with hv h; injection h with hl _
              subst hv; subst hl
              simp only [evalRvalue]
              rw [get?_symSlotsEval, hg']
              exact evalPlaceDiscriminant_aggregate_eq hd env (symSlotsEval env locals) mem
          | unit => nomatch h
          | scalar _ => nomatch h
          | uninit => nomatch h
          | concrete _ => nomatch h
  | _ => nomatch h

theorem symStmt_sound {cfg : SymConfig} {p : SymProg} {body : CapturedMir} {stmt : Statement}
    {f' : SymFrame} {cs : List SymCond}
    (h : symStmt cfg.body.allocations body p.frame stmt = some (f', cs)) (env : SymEnv)
    (hc : condsHold env cs) :
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
  | deinit dst =>
    obtain ⟨dloc, dproj⟩ := dst
    cases dproj with
    | cons _ _ => nomatch h
    | nil =>
      simp only [symStmt] at h
      dsimp only [evalStmt, SymProg.toMachineState, SymFrame.eval]
      rw [get?_symSlotsEval]
      cases hg : get? p.frame.locals dloc with
      | none => rw [hg] at h; nomatch h
      | some sl =>
        rw [hg] at h
        cases sl with
        | dead => nomatch h
        | uninit =>
          dsimp only at h
          dsimp only [Option.map, SymSlot.eval]
          rw [set?_symSlotsEval_uninit]
          cases hs : set? p.frame.locals dloc .uninit with
          | none => rw [hs] at h; nomatch h
          | some l' =>
            rw [hs] at h
            injection h with h; injection h with h1 _
            subst h1
            rfl
        | init _ =>
          dsimp only at h
          dsimp only [Option.map, SymSlot.eval]
          rw [set?_symSlotsEval_uninit]
          cases hs : set? p.frame.locals dloc .uninit with
          | none => rw [hs] at h; nomatch h
          | some l' =>
            rw [hs] at h
            injection h with h; injection h with h1 _
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
        cases hg : get? locals₁ dloc with
        | none => rw [hg] at h; nomatch h
        | some sl =>
          rw [hg] at h
          cases sl with
          | dead => nomatch h
          | uninit =>
            dsimp only at h
            cases hs : set? locals₁ dloc (.init v) with
            | none => rw [hs] at h; nomatch h
            | some l₂ =>
              rw [hs] at h
              injection h with h
              injection h with h1 hcs
              subst h1
              subst hcs
              have hEval := symRvalue_sound hr env hc (p.toMemory cfg env) rfl rfl
              dsimp only [evalStmt]
              rw [show (p.toMachineState cfg env).frame.locals = symSlotsEval env p.frame.locals from rfl,
                show (p.toMachineState cfg env).memory = p.toMemory cfg env from rfl, hEval]
              dsimp only
              rw [get?_symSlotsEval, hg]
              dsimp only [Option.map, SymSlot.eval]
              rw [set?_symSlotsEval_init, hs]
              rfl
          | init w =>
            dsimp only at h
            cases hs : set? locals₁ dloc (.init v) with
            | none => rw [hs] at h; nomatch h
            | some l₂ =>
              rw [hs] at h
              injection h with h
              injection h with h1 hcs
              subst h1
              subst hcs
              have hEval := symRvalue_sound hr env hc (p.toMemory cfg env) rfl rfl
              dsimp only [evalStmt]
              rw [show (p.toMachineState cfg env).frame.locals = symSlotsEval env p.frame.locals from rfl,
                show (p.toMachineState cfg env).memory = p.toMemory cfg env from rfl, hEval]
              dsimp only
              rw [get?_symSlotsEval, hg]
              dsimp only [Option.map, SymSlot.eval]
              rw [set?_symSlotsEval_init, hs]
              rfl
  | _ => nomatch h

/-! ## Part VII: Side Conditions Imply Trusted Intrinsic Definedness -/

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
    {decls : List LocalDecl} {locals : List SymSlot} {op : Operand} {v : SymVal}
    {locals' : List SymSlot}
    (h : symOperand globals layouts decls locals op = some (v, locals')) (env : SymEnv)
    (borrows : List BorrowEntry) (callerLocals : List LocalSlot)
    (callStack : List SavedCallerFrame) :
    evalOperandWithBodyCast (symSlotsEval env locals) op borrows globals layouts callerLocals
      decls callStack = .ok (v.eval env) (symSlotsEval env locals') := by
  unfold evalOperandWithBodyCast
  rw [symOperand_shape h]
  exact (symOperand_sound h env borrows callerLocals callStack).2

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

theorem symTerm_step_sound_obs {cfg : SymConfig} {p : SymProg} {body : CapturedMir}
    {term : Terminator} {p' : SymProg} {cs : List SymCond}
    (h : symTerm cfg p body term = .step p' cs) (env : SymEnv) (hc : condsHold env cs) :
    evalTerminator (p.toMachineState cfg env) term (some body) =
      MirStepNode.emitStep ((symTermObs cfg p body term).eval env)
        (p'.toMachineState cfg env) := by
  obtain ⟨kind, span⟩ := term
  cases kind with
  | goto t =>
    simp only [symTerm] at h
    injection h with h1 _
    subst h1
    rfl
  | switchInt discr targets =>
    simp only [symTerm] at h
    cases ho : symOperand cfg.body.allocations body.layouts body.localDecls p.frame.locals discr with
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
          have hobs : symTermObs cfg p body { kind := .switchInt discr targets, span := span } =
              .event a := by
            simp only [symTermObs, ho, ha]
          rw [hobs]
          dsimp only [evalTerminator, SymProg.toMachineState, SymProg.toMemory, SymFrame.eval,
            bodyLocalDeclsOf, SymObs.eval]
          rw [symOperand_bodyCast_sound ho env, symVal_eval_of_asScalar ha env,
            symScalar_eval_of_asConst hk env]
          rfl
  | assert cond expected target unwind =>
    simp only [symTerm] at h
    cases ho : symOperand cfg.body.allocations body.layouts body.localDecls p.frame.locals cond with
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
        dsimp only [evalTerminator, SymProg.toMachineState, SymProg.toMemory, SymFrame.eval,
          bodyLocalDeclsOf]
        rw [symOperand_bodyCast_sound ho env, symVal_eval_of_asScalar ha env]
        show _ = MirStepNode.emitStep MirObs.silent _
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
                    show _ = MirStepNode.emitStep MirObs.silent _
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
        cases ho : symOperands cfg.body.allocations body.layouts body.localDecls p.frame.locals argOps with
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
            show _ = MirStepNode.emitStep MirObs.silent _
            simp only [evalTerminator, SymProg.toMachineState, SymProg.toMemory, SymFrame.eval,
              resolveCallTarget, hf, bodyLocalDeclsOf]
            rw [symOperands_sound env _ _ _ ho]
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
                          show _ = MirStepNode.emitStep MirObs.silent _
                          simp only [evalTerminator, SymProg.toMachineState, SymProg.toMemory,
                            SymFrame.eval, resolveCallTarget, hf, bodyLocalDeclsOf]
                          rw [symOperands_sound env _ _ _ ho]
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

/-- Single-step terminator soundness (existential observation form). -/
theorem symTerm_step_sound {cfg : SymConfig} {p : SymProg} {body : CapturedMir}
    {term : Terminator} {p' : SymProg} {cs : List SymCond}
    (h : symTerm cfg p body term = .step p' cs) (env : SymEnv) (hc : condsHold env cs) :
    ∃ obs, evalTerminator (p.toMachineState cfg env) term (some body) =
      MirStepNode.emitStep obs (p'.toMachineState cfg env) :=
  ⟨_, symTerm_step_sound_obs h env hc⟩

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

theorem symTerm_branch_sound_obs {cfg : SymConfig} {p : SymProg} {body : CapturedMir}
    {term : Terminator} {alts : List (SymCond × SymProg)} {cs : List SymCond}
    (h : symTerm cfg p body term = .branch alts cs) (env : SymEnv) :
    cs = [] ∧ ∀ c q, (c, q) ∈ alts → c.holds env →
      evalTerminator (p.toMachineState cfg env) term (some body) =
        MirStepNode.emitStep ((symTermObs cfg p body term).eval env)
          (q.toMachineState cfg env) := by
  obtain ⟨kind, span⟩ := term
  cases kind with
  | switchInt discr targets =>
    simp only [symTerm] at h
    cases ho : symOperand cfg.body.allocations body.layouts body.localDecls p.frame.locals discr with
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
          have hobs : symTermObs cfg p body { kind := .switchInt discr targets, span := span } =
              .event a := by
            simp only [symTermObs, ho, ha]
          rw [hobs]
          dsimp only [evalTerminator, SymProg.toMachineState, SymProg.toMemory, SymFrame.eval,
            bodyLocalDeclsOf, SymObs.eval]
          rw [symOperand_bodyCast_sound ho env, symVal_eval_of_asScalar ha env]
          rfl
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


/-- Fork soundness (existential observation form). -/
theorem symTerm_branch_sound {cfg : SymConfig} {p : SymProg} {body : CapturedMir}
    {term : Terminator} {alts : List (SymCond × SymProg)} {cs : List SymCond}
    (h : symTerm cfg p body term = .branch alts cs) (env : SymEnv) :
    cs = [] ∧ ∀ c q, (c, q) ∈ alts → c.holds env →
      ∃ obs, evalTerminator (p.toMachineState cfg env) term (some body) =
        MirStepNode.emitStep obs (q.toMachineState cfg env) :=
  ⟨(symTerm_branch_sound_obs h env).1,
    fun c q hm hh => ⟨_, (symTerm_branch_sound_obs h env).2 c q hm hh⟩⟩

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
        (get? bb.statements p.frame.stmtIdx = none ∧
          symTerm cfg p (p.active.getD cfg.body) bb.terminator = r ∧
          stepMirFn cfg.body (p.toMachineState cfg env) =
            evalTerminator (p.toMachineState cfg env) bb.terminator
              (some (p.active.getD cfg.body)))) := by
  unfold symProgStep symProgStepWith at h
  dsimp only at h
  have hbbEq : (match p.active with
      | none => get? cfg.body.basicBlocks p.frame.blockIdx
      | some activeBody => get? activeBody.basicBlocks p.frame.blockIdx) =
      get? (p.active.getD cfg.body).basicBlocks p.frame.blockIdx := by
    cases p.active <;> rfl
  rw [hbbEq] at h
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
        revert h
        refine Anneal.Firewall.ite_eq_elim_imp (fun hLen hTerm => ?_) (fun _ hStuck => absurd hStuck.symm hr)
        rw [Anneal.ParametricCore.ite_prop_pos hLen]
        exact Or.inr ⟨rfl, hTerm, rfl⟩

/-- **Single-step soundness** against unmodified `stepMirFn`. -/
theorem symProgStep_sound {cfg : SymConfig} {p p' : SymProg} {cs : List SymCond}
    (h : symProgStep cfg p = .step p' cs) (env : SymEnv) (hc : condsHold env cs) :
    ∃ obs, stepMirFn cfg.body (p.toMachineState cfg env) =
      MirStepNode.emitStep obs (p'.toMachineState cfg env) := by
  obtain ⟨bb, _, hcase⟩ := symProgStep_dispatch h (fun h' => SymStepRes.noConfusion h') env
  rcases hcase with ⟨stmt, f', cs', _, hst, hr, hstep⟩ | ⟨_, ht, hstep⟩
  · injection hr with h1 h2
    subst h1
    subst h2
    rw [hstep, symStmt_sound hst env hc]
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
  rcases hcase with ⟨_, _, _, _, _, hr, _⟩ | ⟨_, ht, hstep⟩
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
  rcases hcase with ⟨_, _, _, _, _, hr, _⟩ | ⟨_, ht, hstep⟩
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

/-! ## Part XIII: `Chunk8BlockTree` Lookup & `Anneal.Firewall` / `BoolCertCut` Bridges -/

/-- `Trusted.Sequence.get?` agrees unconditionally with `Anneal.ParametricCore.listGet?`. -/
theorem sequenceGet?_eq_listGet? {α : Type} (xs : List α) (idx : Nat) :
    get? xs idx = Anneal.ParametricCore.listGet? xs idx :=
  Anneal.ParametricCore.listGet?_eq_of_rec get? (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl) xs idx

/-- Pointwise lookup agreement makes `symProgStepWith` identical to `symProgStep`. -/
theorem symProgStepWith_eq_symProgStep {cfg : SymConfig}
    {rootLook : Nat → Option BasicBlockData}
    (hLook : ∀ idx, rootLook idx = get? cfg.body.basicBlocks idx) (p : SymProg) :
    symProgStepWith cfg rootLook p = symProgStep cfg p := by
  unfold symProgStep symProgStepWith
  cases p.active with
  | some _ => rfl
  | none =>
    dsimp only
    rw [hLook p.frame.blockIdx]

/-- Dense `Chunk8BlockTree` block-context step agreement (`O(log N)` spine + `O(1)` leaf). -/
theorem symProgStepWith_blockCtx_eq (cfg : SymConfig) (ctx : SymBlockCtx cfg.body)
    (p : SymProg) :
    symProgStepWith cfg ctx.tree.lookup? p = symProgStep cfg p :=
  symProgStepWith_eq_symProgStep
    (fun idx => (ctx.valid.2 idx).trans (sequenceGet?_eq_listGet? cfg.body.basicBlocks idx).symm) p

/-- `symProgRunStepsWith` agrees with `symProgRunSteps` under any valid `SymBlockCtx`. -/
theorem symProgRunStepsWith_blockCtx_eq (cfg : SymConfig) (ctx : SymBlockCtx cfg.body) :
    ∀ (n : Nat) (p : SymProg),
      symProgRunStepsWith cfg ctx.tree.lookup? n p = symProgRunSteps cfg n p
  | 0, _ => rfl
  | n + 1, p => by
    change (symProgStepWith cfg ctx.tree.lookup? p).bindRun
        (symProgRunStepsWith cfg ctx.tree.lookup? n) =
      (symProgStep cfg p).bindRun (symProgRunSteps cfg n)
    rw [symProgStepWith_blockCtx_eq cfg ctx p]
    have ih : symProgRunStepsWith cfg ctx.tree.lookup? n = symProgRunSteps cfg n :=
      funext (symProgRunStepsWith_blockCtx_eq cfg ctx n)
    rw [ih]

/-- `symRunChunksWith` agrees with `symRunChunks` under any valid `SymBlockCtx`. -/
theorem symRunChunksWith_blockCtx_eq (cfg : SymConfig) (ctx : SymBlockCtx cfg.body) :
    ∀ (ks : List SymChunk) (p : SymProg),
      symRunChunksWith cfg ctx.tree.lookup? ks p = symRunChunks cfg ks p
  | [], _ => rfl
  | k :: ks, p => by
    change (symProgRunStepsWith cfg ctx.tree.lookup? k p).bindRun
        (symRunChunksWith cfg ctx.tree.lookup? ks) =
      (symProgRunSteps cfg k p).bindRun (symRunChunks cfg ks)
    rw [symProgRunStepsWith_blockCtx_eq cfg ctx k p]
    have ih : symRunChunksWith cfg ctx.tree.lookup? ks = symRunChunks cfg ks :=
      funext (symRunChunksWith_blockCtx_eq cfg ctx ks)
    rw [ih]

/-- End-to-end multi-chunk soundness directly through a dense `Chunk8BlockTree`
(`SymBlockCtx`) without linear `basicBlocks` traversal. -/
theorem symRunChunksWith_sound {cfg : SymConfig} (ctx : SymBlockCtx cfg.body)
    {ks : List SymChunk} {args : List SymVal} {v : SymVal} {fin : SymProg} {cs : List SymCond}
    (h : symRunChunksWith cfg ctx.tree.lookup? ks (symProgEntry cfg args) = .ret v fin cs)
    (env : SymEnv) (hc : condsHold env cs) {post : MirOutcome → Prop}
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
  rw [symRunChunksWith_blockCtx_eq] at h
  exact symRunChunks_sound h env hc hpost

/-- Tagged `Anneal.Firewall.Firewall` wrapper over symbolic side conditions. -/
abbrev SymCondFirewall (tag : Nat) (env : SymEnv) (cs : List SymCond) : Prop :=
  Anneal.Firewall.Firewall tag (condsHold env cs)

/-- `Anneal.Firewall.IndexedCut` barrier sealing `ReachesDoneWithinV2026` at
explicit symbolic chunk budgets so intermediate goals never expose expanded
`MirSemantics` propositions to outer tactics. -/
abbrev SymChunkCut (cfg : SymConfig) (post : MirOutcome → Prop)
    (budget : Nat) (st : MachineState) : Prop :=
  Anneal.Firewall.IndexedCut (fun n s => ReachesDoneWithinV2026 cfg.body post n s) budget st

/-- Seal a terminal symbolic chunk behind `SymChunkCut` (`IndexedCut`), consuming
a `SymCondFirewall`-wrapped side-condition proof. -/
theorem symChunkCut_ret {cfg : SymConfig} {k tag : Nat} {p : SymProg} {v : SymVal}
    {fin : SymProg} {cs : List SymCond} {env : SymEnv} {post : MirOutcome → Prop}
    (h : symProgRunSteps cfg k p = .ret v fin cs)
    (hc : SymCondFirewall tag env cs)
    (hpost : post (.normal (v.eval env, (fin.toMachineState cfg env).memory))) :
    SymChunkCut cfg post k (p.toMachineState cfg env) :=
  Anneal.Firewall.seal_cut
    (symProgRunSteps_ret_sound h env (Anneal.Firewall.unwrap hc) hpost)

/-- Prepend a symbolic checkpoint chunk (`k₁` steps) onto a sealed `SymChunkCut`
(`k₂` steps) via `Anneal.Firewall.step_cut` and `StepStageCut` composition. -/
theorem symChunkCut_step {cfg : SymConfig} {k₁ k₂ tag : Nat} {p q : SymProg}
    {cs : List SymCond} {env : SymEnv} {post : MirOutcome → Prop}
    (h : symProgRunSteps cfg k₁ p = .step q cs)
    (hc : SymCondFirewall tag env cs)
    (hNext : SymChunkCut cfg post k₂ (q.toMachineState cfg env)) :
    SymChunkCut cfg post (k₁ + k₂) (p.toMachineState cfg env) :=
  Anneal.Firewall.step_cut
    (fun hReach =>
      reachesDoneWithinV2026_of_stepsTo
        (symProgRunSteps_sound cfg env k₁ h (Anneal.Firewall.unwrap hc)) hReach)
    hNext

/-- Unseal a `SymChunkCut` at the symbolic entry state into all top-level
`V2026_06_01` convergence and safety theorems via `Anneal.Firewall.finish_cut`. -/
theorem symChunkCut_entry_sound {cfg : SymConfig} {args : List SymVal} {budget : Nat}
    {env : SymEnv} {post : MirOutcome → Prop}
    (hCut : SymChunkCut cfg post budget ((symProgEntry cfg args).toMachineState cfg env)) :
    ExecWithinStepsV2026 cfg.body (symValsEval env args) cfg.callees post budget ∧
      MirWpConverges cfg.body
        (initMachineStateWithCallees cfg.body (symValsEval env args) cfg.callees) post ∧
      MirNoUBTree (mirTree cfg.body
        (initMachineStateWithCallees cfg.body (symValsEval env args) cfg.callees)) := by
  have hR : ReachesDoneWithinV2026 cfg.body post budget
      ((symProgEntry cfg args).toMachineState cfg env) :=
    Anneal.Firewall.finish_cut (fun h => h) hCut
  have hE : ExecWithinStepsV2026 cfg.body (symValsEval env args) cfg.callees post budget := by
    unfold ExecWithinStepsV2026
    rw [← symProgEntry_toMachineState]
    exact hR
  exact ⟨hE, mirWpConverges_of_reachesDoneWithinV2026 hE,
    mirNoUBTree_of_reachesDoneWithinV2026 hE⟩

/-- Discharge a multi-chunk symbolic run through a sealed `@[irreducible]`
`Framework.StepWp.BoolCertCut` reflective certificate. -/
theorem symRunChunks_of_boolCert {Code : Type} {check : Code → Bool} {cert : Code}
    {cfg : SymConfig} {ks : List SymChunk} {args : List SymVal} {v : SymVal}
    {fin : SymProg} {cs : List SymCond} {env : SymEnv} {post : MirOutcome → Prop}
    (hCert : BoolCertCut check cert)
    (hSound : check cert = true → symRunChunks cfg ks (symProgEntry cfg args) = .ret v fin cs)
    (hc : condsHold env cs)
    (hpost : post (.normal (v.eval env, (fin.toMachineState cfg env).memory))) :
    ExecWithinStepsV2026 cfg.body (symValsEval env args) cfg.callees post (chunksTotal ks) ∧
      MirWpConverges cfg.body
        (initMachineStateWithCallees cfg.body (symValsEval env args) cfg.callees) post ∧
      MirNoUBTree (mirTree cfg.body
        (initMachineStateWithCallees cfg.body (symValsEval env args) cfg.callees)) := by
  have hRun := BoolCertCut.elim hSound hCert
  obtain ⟨_, hE, _, hW, hU⟩ := symRunChunks_sound hRun env hc hpost
  exact ⟨hE, hW, hU⟩

/-! ## Part XIV: Exactness of Intrinsic Side Conditions & Generic Fail-Closed UB

Every `SymCond` recorded for a value-returning intrinsic is not merely
sufficient but EXACT: trusted definedness of the kernel implies the condition.
Hence a violated recorded condition is not a symbolic artefact — the
unmodified trusted `evalTerminator` / `stepMirFn` step is `MirStepNode.fail .ub`
(`symIntrinsic_ub_of_not_conds`, `symProgStep_ub_of_not_conds`). -/

theorem nat_ne_of_beq_false {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := fun he => by
  rw [he, Nat.beq_refl] at h
  nomatch h

theorem nat_lt_of_ble_false {a b : Nat} (h : Nat.ble a b = false) : b < a :=
  Nat.lt_of_not_le (fun hle => by
    rw [Nat.ble_eq_true_of_le hle] at h
    nomatch h)

theorem widthGuard_ok_of_false {x y : ScalarInt}
    (h : Bool.or (Nat.beq x.sizeBytes 0) (Bool.not (Nat.beq x.sizeBytes y.sizeBytes)) = false) :
    ScWidthsOk x y := by
  cases h1 : Nat.beq x.sizeBytes 0 with
  | true => rw [h1] at h; nomatch h
  | false =>
    cases h2 : Nat.beq x.sizeBytes y.sizeBytes with
    | false => rw [h1, h2] at h; nomatch h
    | true => exact ⟨nat_ne_of_beq_false h1, Nat.eq_of_beq_eq_true h2⟩

theorem unGuard_ok_of_false {x : ScalarInt}
    (h : Bool.or (Nat.beq x.sizeBytes 0) (Nat.beq 4 0) = false) : x.sizeBytes ≠ 0 := by
  cases h1 : Nat.beq x.sizeBytes 0 with
  | true => rw [h1] at h; nomatch h
  | false => exact nat_ne_of_beq_false h1

/-- Exactness: definedness of a width-only bit intrinsic implies `widthNonzero`. -/
theorem symBitEval_complete_width {k : SymBitKind} {x : ScalarInt}
    (hk : k ≠ .ctlzNonzero ∧ k ≠ .cttzNonzero) (h : (symBitEval k x).isSome = true) :
    x.sizeBytes ≠ 0 := by
  cases k with
  | bswap =>
    show x.sizeBytes ≠ 0
    change (evalBswap x).isSome = true at h
    unfold evalBswap at h
    cases h1 : Nat.beq x.sizeBytes 0 with
    | true => rw [h1] at h; nomatch h
    | false => exact nat_ne_of_beq_false h1
  | bitreverse =>
    change (evalBitreverse x).isSome = true at h
    unfold evalBitreverse at h
    cases h1 : Nat.beq x.sizeBytes 0 with
    | true => rw [h1] at h; nomatch h
    | false => exact nat_ne_of_beq_false h1
  | ctlz =>
    change (evalCtlz x).isSome = true at h
    unfold evalCtlz at h
    cases hg : Bool.or (Nat.beq x.sizeBytes 0) (Nat.beq 4 0) with
    | true => rw [hg] at h; nomatch h
    | false => exact unGuard_ok_of_false hg
  | cttz =>
    change (evalCttz x).isSome = true at h
    unfold evalCttz at h
    cases hg : Bool.or (Nat.beq x.sizeBytes 0) (Nat.beq 4 0) with
    | true => rw [hg] at h; nomatch h
    | false => exact unGuard_ok_of_false hg
  | ctpop =>
    change (evalCtpop x).isSome = true at h
    unfold evalCtpop at h
    cases hg : Bool.or (Nat.beq x.sizeBytes 0) (Nat.beq 4 0) with
    | true => rw [hg] at h; nomatch h
    | false => exact unGuard_ok_of_false hg
  | ctlzNonzero => exact absurd rfl hk.1
  | cttzNonzero => exact absurd rfl hk.2

/-- Exactness for `ctlz_nonzero` / `cttz_nonzero`. -/
theorem symBitEval_complete_nonzero {k : SymBitKind} {x : ScalarInt}
    (hk : k = .ctlzNonzero ∨ k = .cttzNonzero) (h : (symBitEval k x).isSome = true) :
    x.sizeBytes ≠ 0 ∧ scBits x ≠ 0 := by
  rcases hk with hk | hk <;> subst hk
  · change (evalCtlzNonzero x).isSome = true at h
    unfold evalCtlzNonzero at h
    cases hg : Bool.or (Nat.beq x.sizeBytes 0) (Nat.beq 4 0) with
    | true => rw [hg] at h; nomatch h
    | false =>
      rw [hg] at h
      dsimp only at h
      cases hz : Nat.beq (wrapScalarBits x.bits (scalarModulus x.sizeBytes)) 0 with
      | true => rw [hz] at h; nomatch h
      | false => exact ⟨unGuard_ok_of_false hg, nat_ne_of_beq_false hz⟩
  · change (evalCttzNonzero x).isSome = true at h
    unfold evalCttzNonzero at h
    cases hg : Bool.or (Nat.beq x.sizeBytes 0) (Nat.beq 4 0) with
    | true => rw [hg] at h; nomatch h
    | false =>
      rw [hg] at h
      dsimp only at h
      cases hz : Nat.beq (wrapScalarBits x.bits (scalarModulus x.sizeBytes)) 0 with
      | true => rw [hz] at h; nomatch h
      | false => exact ⟨unGuard_ok_of_false hg, nat_ne_of_beq_false hz⟩

theorem symWrapEval_complete (k : SymWrapKind) {x y : ScalarInt}
    (h : (symWrapEval k x y).isSome = true) : ScWidthsOk x y := by
  cases k with
  | add =>
    change (evalWrappingAdd x y).isSome = true at h
    unfold evalWrappingAdd at h
    cases hg : Bool.or (Nat.beq x.sizeBytes 0) (Bool.not (Nat.beq x.sizeBytes y.sizeBytes)) with
    | true => rw [hg] at h; nomatch h
    | false => exact widthGuard_ok_of_false hg
  | sub =>
    change (evalWrappingSub x y).isSome = true at h
    unfold evalWrappingSub at h
    cases hg : Bool.or (Nat.beq x.sizeBytes 0) (Bool.not (Nat.beq x.sizeBytes y.sizeBytes)) with
    | true => rw [hg] at h; nomatch h
    | false => exact widthGuard_ok_of_false hg
  | mul =>
    change (evalWrappingMul x y).isSome = true at h
    unfold evalWrappingMul at h
    cases hg : Bool.or (Nat.beq x.sizeBytes 0) (Bool.not (Nat.beq x.sizeBytes y.sizeBytes)) with
    | true => rw [hg] at h; nomatch h
    | false => exact widthGuard_ok_of_false hg

theorem symSatEval_complete (k : SymSatKind) (sg : Bool) {x y : ScalarInt}
    (h : (symSatEval k sg x y).isSome = true) : ScWidthsOk x y := by
  cases k with
  | add =>
    change (evalSaturatingAdd x y sg).isSome = true at h
    unfold evalSaturatingAdd at h
    cases hg : Bool.or (Nat.beq x.sizeBytes 0) (Bool.not (Nat.beq x.sizeBytes y.sizeBytes)) with
    | true => rw [hg] at h; nomatch h
    | false => exact widthGuard_ok_of_false hg
  | sub =>
    change (evalSaturatingSub x y sg).isSome = true at h
    unfold evalSaturatingSub at h
    cases hg : Bool.or (Nat.beq x.sizeBytes 0) (Bool.not (Nat.beq x.sizeBytes y.sizeBytes)) with
    | true => rw [hg] at h; nomatch h
    | false => exact widthGuard_ok_of_false hg

theorem evalUncheckedAdd_complete {x y : ScalarInt} {sg : Bool} :
    (evalUncheckedAdd x y sg).isSome = true →
    ScWidthsOk x y ∧
      (match sg with
       | false => scBits x + scBitsAt x y < scalarModulus x.sizeBytes
       | true => signedOverflowAdd (scBits x) (scBitsAt x y) x.sizeBytes = false) := by
  intro h
  unfold evalUncheckedAdd at h
  cases hg : Bool.or (Nat.beq x.sizeBytes 0) (Bool.not (Nat.beq x.sizeBytes y.sizeBytes)) with
  | true => rw [hg] at h; nomatch h
  | false =>
    rw [hg] at h
    refine ⟨widthGuard_ok_of_false hg, ?_⟩
    cases sg with
    | false =>
      dsimp only at h
      cases hb : Nat.ble (scalarModulus x.sizeBytes)
          (Nat.add (wrapScalarBits x.bits (scalarModulus x.sizeBytes))
            (wrapScalarBits y.bits (scalarModulus x.sizeBytes))) with
      | true => rw [hb] at h; nomatch h
      | false => exact nat_lt_of_ble_false hb
    | true =>
      dsimp only at h
      cases hb : signedOverflowAdd (wrapScalarBits x.bits (scalarModulus x.sizeBytes))
          (wrapScalarBits y.bits (scalarModulus x.sizeBytes)) x.sizeBytes with
      | true => rw [hb] at h; nomatch h
      | false => exact hb

theorem evalUncheckedSub_complete {x y : ScalarInt} {sg : Bool} :
    (evalUncheckedSub x y sg).isSome = true →
    ScWidthsOk x y ∧
      (match sg with
       | false => scBitsAt x y ≤ scBits x
       | true => signedOverflowSub (scBits x) (scBitsAt x y) x.sizeBytes = false) := by
  intro h
  unfold evalUncheckedSub at h
  cases hg : Bool.or (Nat.beq x.sizeBytes 0) (Bool.not (Nat.beq x.sizeBytes y.sizeBytes)) with
  | true => rw [hg] at h; nomatch h
  | false =>
    rw [hg] at h
    refine ⟨widthGuard_ok_of_false hg, ?_⟩
    cases sg with
    | false =>
      dsimp only at h
      cases hb : Nat.ble (wrapScalarBits y.bits (scalarModulus x.sizeBytes))
          (wrapScalarBits x.bits (scalarModulus x.sizeBytes)) with
      | false => rw [hb] at h; nomatch h
      | true => exact Nat.le_of_ble_eq_true hb
    | true =>
      dsimp only at h
      cases hb : signedOverflowSub (wrapScalarBits x.bits (scalarModulus x.sizeBytes))
          (wrapScalarBits y.bits (scalarModulus x.sizeBytes)) x.sizeBytes with
      | true => rw [hb] at h; nomatch h
      | false => exact hb

theorem evalUncheckedMul_complete {x y : ScalarInt} {sg : Bool} :
    (evalUncheckedMul x y sg).isSome = true →
    ScWidthsOk x y ∧
      (match sg with
       | false => scBits x * scBitsAt x y < scalarModulus x.sizeBytes
       | true => signedOverflowMul (scBits x) (scBitsAt x y) x.sizeBytes = false) := by
  intro h
  unfold evalUncheckedMul at h
  cases hg : Bool.or (Nat.beq x.sizeBytes 0) (Bool.not (Nat.beq x.sizeBytes y.sizeBytes)) with
  | true => rw [hg] at h; nomatch h
  | false =>
    rw [hg] at h
    refine ⟨widthGuard_ok_of_false hg, ?_⟩
    cases sg with
    | false =>
      dsimp only at h
      cases hb : Nat.ble (scalarModulus x.sizeBytes)
          (Nat.mul (wrapScalarBits x.bits (scalarModulus x.sizeBytes))
            (wrapScalarBits y.bits (scalarModulus x.sizeBytes))) with
      | true => rw [hb] at h; nomatch h
      | false => exact nat_lt_of_ble_false hb
    | true =>
      dsimp only at h
      cases hb : signedOverflowMul (wrapScalarBits x.bits (scalarModulus x.sizeBytes))
          (wrapScalarBits y.bits (scalarModulus x.sizeBytes)) x.sizeBytes with
      | true => rw [hb] at h; nomatch h
      | false => exact hb

theorem minNegOne_ok_of_guard_false {x y : ScalarInt}
    (h : Bool.and
      (Nat.beq (wrapScalarBits x.bits (scalarModulus x.sizeBytes))
        (scalarPow2 (Nat.sub (Nat.mul x.sizeBytes 8) 1)))
      (Nat.beq (wrapScalarBits y.bits (scalarModulus x.sizeBytes))
        (Nat.sub (scalarModulus x.sizeBytes) 1)) = false) :
    ScNotMinNegOne x y := by
  intro ⟨ha, hb⟩
  have ha' : wrapScalarBits x.bits (scalarModulus x.sizeBytes) =
      scalarPow2 (Nat.sub (Nat.mul x.sizeBytes 8) 1) := ha
  have hb' : wrapScalarBits y.bits (scalarModulus x.sizeBytes) =
      Nat.sub (scalarModulus x.sizeBytes) 1 := hb
  rw [nat_beq_true_of_eq ha', nat_beq_true_of_eq hb'] at h
  nomatch h

theorem evalUncheckedDiv_complete {x y : ScalarInt} {sg : Bool} :
    (evalUncheckedDiv x y sg).isSome = true →
    ScWidthsOk x y ∧ scBitsAt x y ≠ 0 ∧
      (match sg with
       | false => True
       | true => ScNotMinNegOne x y) := by
  intro h
  unfold evalUncheckedDiv at h
  cases hg : Bool.or (Nat.beq x.sizeBytes 0) (Bool.not (Nat.beq x.sizeBytes y.sizeBytes)) with
  | true => rw [hg] at h; nomatch h
  | false =>
    rw [hg] at h
    dsimp only at h
    cases hz : Nat.beq (wrapScalarBits y.bits (scalarModulus x.sizeBytes)) 0 with
    | true => rw [hz] at h; nomatch h
    | false =>
      rw [hz] at h
      refine ⟨widthGuard_ok_of_false hg, nat_ne_of_beq_false hz, ?_⟩
      cases sg with
      | false => trivial
      | true =>
        dsimp only at h
        cases hm : Bool.and
            (Nat.beq (wrapScalarBits x.bits (scalarModulus x.sizeBytes))
              (scalarPow2 (Nat.sub (Nat.mul x.sizeBytes 8) 1)))
            (Nat.beq (wrapScalarBits y.bits (scalarModulus x.sizeBytes))
              (Nat.sub (scalarModulus x.sizeBytes) 1)) with
        | true => rw [hm] at h; nomatch h
        | false => exact minNegOne_ok_of_guard_false hm

theorem evalUncheckedRem_complete {x y : ScalarInt} {sg : Bool} :
    (evalUncheckedRem x y sg).isSome = true →
    ScWidthsOk x y ∧ scBitsAt x y ≠ 0 ∧
      (match sg with
       | false => True
       | true => ScNotMinNegOne x y) := by
  intro h
  unfold evalUncheckedRem at h
  cases hg : Bool.or (Nat.beq x.sizeBytes 0) (Bool.not (Nat.beq x.sizeBytes y.sizeBytes)) with
  | true => rw [hg] at h; nomatch h
  | false =>
    rw [hg] at h
    dsimp only at h
    cases hz : Nat.beq (wrapScalarBits y.bits (scalarModulus x.sizeBytes)) 0 with
    | true => rw [hz] at h; nomatch h
    | false =>
      rw [hz] at h
      refine ⟨widthGuard_ok_of_false hg, nat_ne_of_beq_false hz, ?_⟩
      cases sg with
      | false => trivial
      | true =>
        dsimp only at h
        cases hm : Bool.and
            (Nat.beq (wrapScalarBits x.bits (scalarModulus x.sizeBytes))
              (scalarPow2 (Nat.sub (Nat.mul x.sizeBytes 8) 1)))
            (Nat.beq (wrapScalarBits y.bits (scalarModulus x.sizeBytes))
              (Nat.sub (scalarModulus x.sizeBytes) 1)) with
        | true => rw [hm] at h; nomatch h
        | false => exact minNegOne_ok_of_guard_false hm

theorem shiftGuards_ok {x y : ScalarInt} {rs : Bool}
    (g1 : Bool.or (Nat.beq x.sizeBytes 0) (Nat.beq y.sizeBytes 0) = false)
    (g2 : Bool.or (Bool.and rs (isSignedNegative (wrapScalarBits y.bits (scalarModulus y.sizeBytes))
          y.sizeBytes))
        (Nat.ble (Nat.mul x.sizeBytes 8) (wrapScalarBits y.bits (scalarModulus y.sizeBytes))) =
        false) :
    x.sizeBytes ≠ 0 ∧ y.sizeBytes ≠ 0 ∧
      (rs && isSignedNegative (scBits y) y.sizeBytes) = false ∧
      scBits y < Nat.mul x.sizeBytes 8 := by
  cases h1 : Nat.beq x.sizeBytes 0 with
  | true => rw [h1] at g1; nomatch g1
  | false =>
    cases h2 : Nat.beq y.sizeBytes 0 with
    | true => rw [h1, h2] at g1; nomatch g1
    | false =>
      cases hn : Bool.and rs (isSignedNegative (wrapScalarBits y.bits (scalarModulus y.sizeBytes))
          y.sizeBytes) with
      | true => rw [hn] at g2; nomatch g2
      | false =>
        cases hb : Nat.ble (Nat.mul x.sizeBytes 8)
            (wrapScalarBits y.bits (scalarModulus y.sizeBytes)) with
        | true => rw [hn, hb] at g2; nomatch g2
        | false =>
          exact ⟨nat_ne_of_beq_false h1, nat_ne_of_beq_false h2, hn, nat_lt_of_ble_false hb⟩

theorem evalUncheckedShl_complete {x y : ScalarInt} {rs : Bool}
    (h : (evalUncheckedShl x y rs).isSome = true) :
    x.sizeBytes ≠ 0 ∧ y.sizeBytes ≠ 0 ∧
      (rs && isSignedNegative (scBits y) y.sizeBytes) = false ∧
      scBits y < Nat.mul x.sizeBytes 8 := by
  unfold evalUncheckedShl at h
  cases g1 : Bool.or (Nat.beq x.sizeBytes 0) (Nat.beq y.sizeBytes 0) with
  | true => rw [g1] at h; nomatch h
  | false =>
    rw [g1] at h
    dsimp only at h
    cases g2 : Bool.or (Bool.and rs (isSignedNegative
        (wrapScalarBits y.bits (scalarModulus y.sizeBytes)) y.sizeBytes))
        (Nat.ble (Nat.mul x.sizeBytes 8) (wrapScalarBits y.bits (scalarModulus y.sizeBytes))) with
    | true => rw [g2] at h; nomatch h
    | false => exact shiftGuards_ok g1 g2

theorem evalUncheckedShr_complete {x y : ScalarInt} {ls rs : Bool}
    (h : (evalUncheckedShr x y ls rs).isSome = true) :
    x.sizeBytes ≠ 0 ∧ y.sizeBytes ≠ 0 ∧
      (rs && isSignedNegative (scBits y) y.sizeBytes) = false ∧
      scBits y < Nat.mul x.sizeBytes 8 := by
  unfold evalUncheckedShr at h
  cases g1 : Bool.or (Nat.beq x.sizeBytes 0) (Nat.beq y.sizeBytes 0) with
  | true => rw [g1] at h; nomatch h
  | false =>
    rw [g1] at h
    dsimp only at h
    cases g2 : Bool.or (Bool.and rs (isSignedNegative
        (wrapScalarBits y.bits (scalarModulus y.sizeBytes)) y.sizeBytes))
        (Nat.ble (Nat.mul x.sizeBytes 8) (wrapScalarBits y.bits (scalarModulus y.sizeBytes))) with
    | true => rw [g2] at h; nomatch h
    | false => exact shiftGuards_ok g1 g2

theorem writeIntrinsicScalarResult_none_of_not {s : MachineState} {locals' : List LocalSlot}
    {dst : Place} {bb : BasicBlockIdx} {o : Option ScalarInt} {P : Prop}
    (hc : o.isSome = true → P) (hn : ¬ P) :
    writeIntrinsicScalarResult s locals' dst bb o = MirStepNode.fail .ub := by
  cases ho : o with
  | none => rfl
  | some v => exact absurd (hc (by rw [ho]; rfl)) hn

/-- **Generic fail-closed UB:** if the side conditions recorded for a
value-returning intrinsic are violated, the unmodified trusted
`evalNonSelectIntrinsicCall` step is `MirStepNode.fail .ub`. -/
theorem symIntrinsic_ub_of_not_conds {kind : RustIntrinsicKind} {target : ResolvedCallTarget}
    {decls : List LocalDecl} {layouts : LayoutTable} {argOps : List Operand}
    {args : List SymVal} {r : SymScalar} {cs : List SymCond}
    (h : symIntrinsic kind target decls layouts argOps args = some (r, cs)) (env : SymEnv)
    (hn : ¬ condsHold env cs) (s : MachineState) (locals' : List LocalSlot) (dst : Place)
    (bb : BasicBlockIdx) :
    evalNonSelectIntrinsicCall kind s target decls layouts argOps (symValsEval env args)
      locals' dst bb = MirStepNode.fail .ub := by
  have hn1 : ∀ c : SymCond, cs = [c] → ¬ c.holds env := fun c hcs hc => by
    subst hcs
    exact hn ⟨hc, trivial⟩
  cases kind with
  | ubChecks =>
    simp only [symIntrinsic] at h
    cases args with
    | cons _ _ => nomatch h
    | nil =>
      injection h with h
      injection h with _ h2
      subst h2
      exact absurd trivial hn
  | ctlz =>
    obtain ⟨a, x, rfl, hx, rfl, rfl⟩ := symUn_shape h
    rw [symValsEval_one hx env]
    exact writeIntrinsicScalarResult_none_of_not
      (symBitEval_complete_width (k := .ctlz) ⟨nofun, nofun⟩) (hn1 _ rfl)
  | cttz =>
    obtain ⟨a, x, rfl, hx, rfl, rfl⟩ := symUn_shape h
    rw [symValsEval_one hx env]
    exact writeIntrinsicScalarResult_none_of_not
      (symBitEval_complete_width (k := .cttz) ⟨nofun, nofun⟩) (hn1 _ rfl)
  | ctpop =>
    obtain ⟨a, x, rfl, hx, rfl, rfl⟩ := symUn_shape h
    rw [symValsEval_one hx env]
    exact writeIntrinsicScalarResult_none_of_not
      (symBitEval_complete_width (k := .ctpop) ⟨nofun, nofun⟩) (hn1 _ rfl)
  | bswap =>
    obtain ⟨a, x, rfl, hx, rfl, rfl⟩ := symUn_shape h
    rw [symValsEval_one hx env]
    exact writeIntrinsicScalarResult_none_of_not
      (symBitEval_complete_width (k := .bswap) ⟨nofun, nofun⟩) (hn1 _ rfl)
  | bitreverse =>
    obtain ⟨a, x, rfl, hx, rfl, rfl⟩ := symUn_shape h
    rw [symValsEval_one hx env]
    exact writeIntrinsicScalarResult_none_of_not
      (symBitEval_complete_width (k := .bitreverse) ⟨nofun, nofun⟩) (hn1 _ rfl)
  | ctlzNonzero =>
    obtain ⟨a, x, rfl, hx, rfl, rfl⟩ := symUn_shape h
    rw [symValsEval_one hx env]
    exact writeIntrinsicScalarResult_none_of_not
      (symBitEval_complete_nonzero (k := .ctlzNonzero) (Or.inl rfl)) (hn1 _ rfl)
  | cttzNonzero =>
    obtain ⟨a, x, rfl, hx, rfl, rfl⟩ := symUn_shape h
    rw [symValsEval_one hx env]
    exact writeIntrinsicScalarResult_none_of_not
      (symBitEval_complete_nonzero (k := .cttzNonzero) (Or.inr rfl)) (hn1 _ rfl)
  | wrappingAdd =>
    obtain ⟨a, b, x, y, rfl, hx, hy, rfl, rfl⟩ := symBin_shape h
    rw [symValsEval_two hx hy env]
    exact writeIntrinsicScalarResult_none_of_not (symWrapEval_complete .add) (hn1 _ rfl)
  | wrappingSub =>
    obtain ⟨a, b, x, y, rfl, hx, hy, rfl, rfl⟩ := symBin_shape h
    rw [symValsEval_two hx hy env]
    exact writeIntrinsicScalarResult_none_of_not (symWrapEval_complete .sub) (hn1 _ rfl)
  | wrappingMul =>
    obtain ⟨a, b, x, y, rfl, hx, hy, rfl, rfl⟩ := symBin_shape h
    rw [symValsEval_two hx hy env]
    exact writeIntrinsicScalarResult_none_of_not (symWrapEval_complete .mul) (hn1 _ rfl)
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
      exact writeIntrinsicScalarResult_none_of_not (symSatEval_complete .add sg) (hn1 _ rfl)
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
      exact writeIntrinsicScalarResult_none_of_not (symSatEval_complete .sub sg) (hn1 _ rfl)
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
      exact writeIntrinsicScalarResult_none_of_not evalUncheckedAdd_complete (hn1 _ rfl)
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
      exact writeIntrinsicScalarResult_none_of_not evalUncheckedSub_complete (hn1 _ rfl)
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
      exact writeIntrinsicScalarResult_none_of_not evalUncheckedMul_complete (hn1 _ rfl)
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
      exact writeIntrinsicScalarResult_none_of_not evalUncheckedDiv_complete (hn1 _ rfl)
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
      exact writeIntrinsicScalarResult_none_of_not evalUncheckedRem_complete (hn1 _ rfl)
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
      exact writeIntrinsicScalarResult_none_of_not evalUncheckedShl_complete (hn1 _ rfl)
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
        exact writeIntrinsicScalarResult_none_of_not evalUncheckedShr_complete (hn1 _ rfl)
  | constEvalSelect => nomatch h
  | arithOffset => nomatch h
  | threeWayCompare => nomatch h
  | sizeOfVal => nomatch h
  | alignOfVal => nomatch h
  | copyNonOverlapping => nomatch h
  | writeBytes => nomatch h

/-- Terminator-level generic fail-closed UB: a symbolic `call` step whose
recorded side conditions fail is a trusted `MirStepNode.fail .ub`. -/
theorem symTerm_call_ub_of_not_conds {cfg : SymConfig} {p : SymProg} {body : CapturedMir}
    {func : Operand} {argOps : List Operand} {destination : Place} {targetBb : BasicBlockIdx}
    {unwind : UnwindAction} {span : String} {p' : SymProg} {cs : List SymCond}
    (h : symTerm cfg p body
      { kind := .call func argOps destination (some targetBb) unwind, span := span } =
        .step p' cs)
    (env : SymEnv) (hn : ¬ condsHold env cs) :
    evalTerminator (p.toMachineState cfg env)
      { kind := .call func argOps destination (some targetBb) unwind, span := span }
      (some body) = MirStepNode.fail .ub := by
  simp only [symTerm] at h
  cases hf : extractCalleeDefPath? func with
  | none => rw [hf] at h; nomatch h
  | some defPath =>
    rw [hf] at h
    dsimp only at h
    cases ho : symOperands cfg.body.allocations body.layouts body.localDecls p.frame.locals
        argOps with
    | none => rw [ho] at h; nomatch h
    | some r =>
      obtain ⟨args, locals'⟩ := r
      rw [ho] at h
      dsimp only at h
      cases hl : lookupCallee cfg.callees body.layouts defPath (extractCalleeTypeArgs func)
          cfg.body.traitImpls with
      | some calleeBody =>
        rw [hl] at h
        injection h with _ h2
        subst h2
        exact absurd trivial hn
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
              have hcs : cs' = cs := by
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
                        injection h with _ h2
              subst hcs
              simp only [evalTerminator, SymProg.toMachineState, SymProg.toMemory,
                SymFrame.eval, resolveCallTarget, hf, bodyLocalDeclsOf]
              rw [symOperands_sound env _ _ _ ho]
              simp only [hl, hx]
              rw [evalDirectRustIntrinsic?_of_sym hk hi]
              dsimp only
              rw [symIntrinsic_ub_of_not_conds hi env hn]

/-- The active program point of `p` is a returning `call` terminator. -/
def SymProg.atCall (cfg : SymConfig) (p : SymProg) : Bool :=
  match get? (p.active.getD cfg.body).basicBlocks p.frame.blockIdx with
  | some bb =>
    match get? bb.statements p.frame.stmtIdx with
    | some _ => false
    | none =>
      match bb.terminator.kind with
      | .call _ _ _ (some _) _ => true
      | _ => false
  | none => false

/-- **Program-level generic fail-closed UB:** at a `call` program point, a
symbolic step whose recorded side conditions are violated is exactly a trusted
UB fault of unmodified `stepMirFn`. -/
theorem symProgStep_ub_of_not_conds {cfg : SymConfig} {p p' : SymProg} {cs : List SymCond}
    (h : symProgStep cfg p = .step p' cs) (env : SymEnv) (hn : ¬ condsHold env cs)
    (hat : p.atCall cfg = true) :
    stepMirFn cfg.body (p.toMachineState cfg env) = MirStepNode.fail .ub := by
  obtain ⟨bb, hb, hcase⟩ := symProgStep_dispatch h (fun h' => SymStepRes.noConfusion h') env
  unfold SymProg.atCall at hat
  rw [hb] at hat
  dsimp only at hat
  cases hs : get? bb.statements p.frame.stmtIdx with
  | some _ =>
    rw [hs] at hat
    nomatch hat
  | none =>
    rw [hs] at hat
    dsimp only at hat
    rcases hcase with ⟨_, _, _, hs', _, _, _⟩ | ⟨_, ht, hstep⟩
    · rw [hs] at hs'
      nomatch hs'
    · rw [hstep]
      cases hterm : bb.terminator with
      | mk kind span =>
        rw [hterm] at ht hat
        dsimp only at hat
        cases kind with
        | call func argOps destination target unwind =>
          cases target with
          | none => nomatch hat
          | some targetBb => exact symTerm_call_ub_of_not_conds ht env hn
        | _ => nomatch hat

/-- Run-level fail-closed refutation: a symbolic prefix to a `call` point whose
next symbolic step records violated conditions refutes `MirNoUBTree`,
`MirWpConverges`, and every `ReachesDoneWithinV2026` of the unmodified trusted
semantics from the start state. -/
theorem symProgRunSteps_ub_refutes {cfg : SymConfig} {k : Nat} {p q q' : SymProg}
    {cs cs' : List SymCond} (hpre : symProgRunSteps cfg k p = .step q cs)
    (hstep : symProgStep cfg q = .step q' cs') (hat : q.atCall cfg = true) (env : SymEnv)
    (hc : condsHold env cs) (hn : ¬ condsHold env cs') :
    ¬ MirNoUBTree (mirTree cfg.body (p.toMachineState cfg env)) ∧
      (∀ post, ¬ MirWpConverges cfg.body (p.toMachineState cfg env) post) ∧
      (∀ post bound, ¬ ReachesDoneWithinV2026 cfg.body post bound (p.toMachineState cfg env)) :=
  symProgRunSteps_fault_refutes hpre env hc (fk := .ub) (by
    unfold v2026Step
    rw [symProgStep_ub_of_not_conds hstep env hn hat]
    rfl)

/-! ## Part XV: Exact Observable-Event Correspondence -/

/-- Exact observation emitted by the next trusted step of `p`. -/
def symProgObs (cfg : SymConfig) (p : SymProg) : SymObs :=
  match get? (p.active.getD cfg.body).basicBlocks p.frame.blockIdx with
  | some bb =>
    match get? bb.statements p.frame.stmtIdx with
    | some _ => .silent
    | none => symTermObs cfg p (p.active.getD cfg.body) bb.terminator
  | none => .silent

/-- **Exact single-step soundness**: the unmodified trusted step emits exactly
the symbolic observation (`.silent`, or `SwitchInt`'s `.vis` event with the
symbolic discriminant bits) and lands in the denoted successor. -/
theorem symProgStep_sound_obs {cfg : SymConfig} {p p' : SymProg} {cs : List SymCond}
    (h : symProgStep cfg p = .step p' cs) (env : SymEnv) (hc : condsHold env cs) :
    stepMirFn cfg.body (p.toMachineState cfg env) =
      MirStepNode.emitStep ((symProgObs cfg p).eval env) (p'.toMachineState cfg env) := by
  obtain ⟨bb, hb, hcase⟩ := symProgStep_dispatch h (fun h' => SymStepRes.noConfusion h') env
  rcases hcase with ⟨stmt, f', cs', hs, hst, hr, hstep⟩ | ⟨hs, ht, hstep⟩
  · injection hr with h1 h2
    subst h1
    subst h2
    have hobs : symProgObs cfg p = .silent := by
      unfold symProgObs
      rw [hb]
      dsimp only
      rw [hs]
    rw [hstep, symStmt_sound hst env hc, hobs]
    rfl
  · have hobs : symProgObs cfg p = symTermObs cfg p (p.active.getD cfg.body) bb.terminator := by
      unfold symProgObs
      rw [hb]
      dsimp only
      rw [hs]
    rw [hstep, hobs]
    exact symTerm_step_sound_obs ht env hc

/-- Exact fork soundness: every enabled alternative is the trusted successor
reached by emitting the `SwitchInt` event with the symbolic discriminant bits. -/
theorem symProgStep_branch_sound_obs {cfg : SymConfig} {p : SymProg}
    {alts : List (SymCond × SymProg)} {cs : List SymCond}
    (h : symProgStep cfg p = .branch alts cs) (env : SymEnv) :
    ∀ c q, (c, q) ∈ alts → c.holds env →
      stepMirFn cfg.body (p.toMachineState cfg env) =
        MirStepNode.emitStep ((symProgObs cfg p).eval env) (q.toMachineState cfg env) := by
  obtain ⟨bb, hb, hcase⟩ := symProgStep_dispatch h (fun h' => SymStepRes.noConfusion h') env
  rcases hcase with ⟨_, _, _, _, _, hr, _⟩ | ⟨hs, ht, hstep⟩
  · nomatch hr
  · intro c q hm hh
    have hobs : symProgObs cfg p = symTermObs cfg p (p.active.getD cfg.body) bb.terminator := by
      unfold symProgObs
      rw [hb]
      dsimp only
      rw [hs]
    rw [hstep, hobs]
    exact (symTerm_branch_sound_obs ht env).2 c q hm hh

/-! ## Part XVI: Recursive Compound Static Width / Bool Analysis & `BoolCertCut`

Computable `@Nat.rec` static width and boolean-validity checkers over compound
`SymScalar` expressions (`var`, `const`, `unaryOp`, `castInt`, `wrappingOp`,
`saturatingOp`, `bitIntrinsic`, total `binOp`, `checkedVal`, `checkedFlag`)
plus constant `assertHolds`, sealed behind `Framework.StepWp.BoolCertCut`. -/

/-- Check equal nonzero static widths. -/
def staticWidthsMatch (wa? wb? : Option Nat) : Option Nat :=
  match wa?, wb? with
  | some wa, some wb =>
    match Bool.and (Bool.not (Nat.beq wa 0)) (Nat.beq wa wb) with
    | true => some wa
    | false => none
  | _, _ => none

/-- Recursive `@Nat.rec` static byte-width analysis over compound `SymNode`s. -/
def symNodeStaticWidth? (fuel : Nat) : SymNode → Option Nat :=
  @Nat.rec (fun _ => SymNode → Option Nat)
    (fun _ => none)
    (fun _ ih e =>
      match e with
      | .var _ w => some w
      | .const sc => some sc.sizeBytes
      | .castInt _ tb _ => some tb
      | .unaryOp .notBool _ => some 1
      | .unaryOp .neg a => ih a
      | .unaryOp .notInt a => ih a
      | .wrappingOp _ a b => staticWidthsMatch (ih a) (ih b)
      | .saturatingOp _ _ a b => staticWidthsMatch (ih a) (ih b)
      | .checkedVal _ _ a b => staticWidthsMatch (ih a) (ih b)
      | .checkedFlag _ _ a b =>
        match staticWidthsMatch (ih a) (ih b) with
        | some _ => some 1
        | none => none
      | .bitIntrinsic k a =>
        match ih a with
        | some wa =>
          match Nat.beq wa 0 with
          | true => none
          | false =>
            match k with
            | .bswap | .bitreverse => some wa
            | .ctlz | .cttz | .ctpop => some 4
            | .ctlzNonzero | .cttzNonzero => none
        | none => none
      | .binOp op _ a b =>
        match op with
        | .add | .sub | .mul | .bitAnd | .bitOr | .bitXor =>
          staticWidthsMatch (ih a) (ih b)
        | .eq | .ne | .lt | .le | .gt | .ge | .cmp =>
          match staticWidthsMatch (ih a) (ih b) with
          | some _ => some 1
          | none => none
        | .shl | .shr =>
          match ih a, ih b with
          | some wa, some wb =>
            match Bool.and (Bool.not (Nat.beq wa 0)) (Bool.not (Nat.beq wb 0)) with
            | true => some wa
            | false => none
          | _, _ => none
        | _ => none
      | .uncheckedOp _ _ _ _ _ => none)
    fuel

/-- Statically known byte width of a compound symbolic scalar. -/
def SymScalar.staticWidth? (s : SymScalar) : Option Nat :=
  symNodeStaticWidth? s.fuel s.node

/-- Statically guaranteed 1-byte boolean scalar (`sizeBytes = 1 ∧ (bits = 0 ∨ bits = 1)`). -/
def SymScalar.isValidBoolStatic (s : SymScalar) : Bool :=
  match s.fuel with
  | 0 => false
  | n + 1 =>
    match s.node with
    | .const sc =>
      Bool.and (Nat.beq sc.sizeBytes 1) (Bool.or (Nat.beq sc.bits 0) (Nat.beq sc.bits 1))
    | .unaryOp .notBool _ => true
    | .checkedFlag _ _ a b =>
      match staticWidthsMatch (symNodeStaticWidth? n a) (symNodeStaticWidth? n b) with
      | some _ => true
      | none => false
    | .binOp op _ a b =>
      match op with
      | .eq | .ne | .lt | .le | .gt | .ge =>
        match staticWidthsMatch (symNodeStaticWidth? n a) (symNodeStaticWidth? n b) with
        | some _ => true
        | none => false
      | _ => false
    | _ => false

theorem staticWidthsMatch_sound {wa? wb? : Option Nat} {w : Nat}
    (h : staticWidthsMatch wa? wb? = some w) :
    wa? = some w ∧ wb? = some w ∧ w ≠ 0 := by
  unfold staticWidthsMatch at h
  cases wa? with
  | none => nomatch h
  | some wa =>
    cases wb? with
    | none => nomatch h
    | some wb =>
      dsimp only at h
      cases h0 : Nat.beq wa 0 with
      | true => rw [h0] at h; nomatch h
      | false =>
        cases he : Nat.beq wa wb with
        | false => rw [h0, he] at h; nomatch h
        | true =>
          rw [h0, he] at h
          injection h with hw
          subst hw
          exact ⟨rfl, congrArg some (Nat.eq_of_beq_eq_true he).symm, nat_ne_of_beq_false h0⟩

theorem symWrapEval_sizeBytes (k : SymWrapKind) {x y : ScalarInt} (hw : ScWidthsOk x y) :
    ((symWrapEval k x y).getD symDefaultScalar).sizeBytes = x.sizeBytes := by
  cases k with
  | add =>
    show ((evalWrappingAdd x y).getD symDefaultScalar).sizeBytes = x.sizeBytes
    unfold evalWrappingAdd; rw [widthGuard_false hw]; rfl
  | sub =>
    show ((evalWrappingSub x y).getD symDefaultScalar).sizeBytes = x.sizeBytes
    unfold evalWrappingSub; rw [widthGuard_false hw]; rfl
  | mul =>
    show ((evalWrappingMul x y).getD symDefaultScalar).sizeBytes = x.sizeBytes
    unfold evalWrappingMul; rw [widthGuard_false hw]; rfl

theorem symSatEval_sizeBytes (k : SymSatKind) (sg : Bool) {x y : ScalarInt} (hw : ScWidthsOk x y) :
    ((symSatEval k sg x y).getD symDefaultScalar).sizeBytes = x.sizeBytes := by
  cases k with
  | add =>
    show ((evalSaturatingAdd x y sg).getD symDefaultScalar).sizeBytes = x.sizeBytes
    unfold evalSaturatingAdd; rw [widthGuard_false hw]; dsimp only
    cases sg with
    | false => dsimp only; split <;> rfl
    | true => dsimp only; split <;> (try split) <;> rfl
  | sub =>
    show ((evalSaturatingSub x y sg).getD symDefaultScalar).sizeBytes = x.sizeBytes
    unfold evalSaturatingSub; rw [widthGuard_false hw]; dsimp only
    cases sg with
    | false => dsimp only; split <;> rfl
    | true => dsimp only; split <;> (try split) <;> rfl

theorem symCheckedValEval_sizeBytes (k : SymOverflowKind) (sg : Bool) {x y : ScalarInt}
    (hw : ScWidthsOk x y) :
    ((symCheckedValEval k sg x y).getD symDefaultScalar).sizeBytes = x.sizeBytes := by
  cases k with
  | add =>
    unfold symCheckedValEval symOverflowToBinOp evalScalarBinOp
    rw [nat_beq_false_of_ne hw.1, nat_beq_true_of_eq hw.2]; rfl
  | mul =>
    unfold symCheckedValEval symOverflowToBinOp evalScalarBinOp
    rw [nat_beq_false_of_ne hw.1, nat_beq_true_of_eq hw.2]; rfl
  | sub =>
    unfold symCheckedValEval symOverflowToBinOp evalScalarBinOp
    rw [nat_beq_false_of_ne hw.1, nat_beq_true_of_eq hw.2]
    cases sg with
    | true => rfl
    | false =>
      dsimp only
      cases hb : Nat.ble y.bits x.bits <;> rfl

theorem symCheckedFlagEval_validBool (k : SymOverflowKind) (sg : Bool) {x y : ScalarInt}
    (hw : ScWidthsOk x y) :
    let sc := (symCheckedFlagEval k sg x y).getD symDefaultScalar
    sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1) := by
  cases k with
  | add =>
    unfold symCheckedFlagEval symOverflowToBinOp evalScalarBinOp
    rw [nat_beq_false_of_ne hw.1, nat_beq_true_of_eq hw.2]
    dsimp only
    cases sg with
    | false =>
      dsimp only
      cases hb : Nat.ble (scalarModulus x.sizeBytes) (Nat.add x.bits y.bits) with
      | true => exact ⟨rfl, Or.inr rfl⟩
      | false => exact ⟨rfl, Or.inl rfl⟩
    | true =>
      dsimp only
      cases hb : signedOverflowAdd x.bits y.bits x.sizeBytes with
      | true => exact ⟨rfl, Or.inr rfl⟩
      | false => exact ⟨rfl, Or.inl rfl⟩
  | mul =>
    unfold symCheckedFlagEval symOverflowToBinOp evalScalarBinOp
    rw [nat_beq_false_of_ne hw.1, nat_beq_true_of_eq hw.2]
    dsimp only
    cases sg with
    | false =>
      dsimp only
      cases hb : Nat.ble (scalarModulus x.sizeBytes) (Nat.mul x.bits y.bits) with
      | true => exact ⟨rfl, Or.inr rfl⟩
      | false => exact ⟨rfl, Or.inl rfl⟩
    | true =>
      dsimp only
      cases hb : signedOverflowMul x.bits y.bits x.sizeBytes with
      | true => exact ⟨rfl, Or.inr rfl⟩
      | false => exact ⟨rfl, Or.inl rfl⟩
  | sub =>
    unfold symCheckedFlagEval symOverflowToBinOp evalScalarBinOp
    rw [nat_beq_false_of_ne hw.1, nat_beq_true_of_eq hw.2]
    dsimp only
    cases sg with
    | false =>
      dsimp only
      cases hb : Nat.ble y.bits x.bits with
      | true => exact ⟨rfl, Or.inl rfl⟩
      | false => exact ⟨rfl, Or.inr rfl⟩
    | true =>
      dsimp only
      cases hb : signedOverflowSub x.bits y.bits x.sizeBytes with
      | true => exact ⟨rfl, Or.inr rfl⟩
      | false => exact ⟨rfl, Or.inl rfl⟩

theorem boolToScalar_validBool (b : Bool) :
    (boolToScalar b).sizeBytes = 1 ∧ ((boolToScalar b).bits = 0 ∨ (boolToScalar b).bits = 1) := by
  cases b with
  | false => exact ⟨rfl, Or.inl rfl⟩
  | true => exact ⟨rfl, Or.inr rfl⟩

theorem symNodeStaticWidth?_bitIntrinsic (fuel : Nat) (k : SymBitKind) (a : SymNode) :
    symNodeStaticWidth? (fuel + 1) (.bitIntrinsic k a) =
      match symNodeStaticWidth? fuel a with
      | some wa =>
        match Nat.beq wa 0 with
        | true => none
        | false =>
          match k with
          | .bswap | .bitreverse => some wa
          | .ctlz | .cttz | .ctpop => some 4
          | .ctlzNonzero | .cttzNonzero => none
      | none => none := rfl

theorem symNodeStaticWidth?_sound (env : SymEnv) :
    ∀ (fuel : Nat) (t : SymNode) (w : Nat),
      symNodeStaticWidth? fuel t = some w → (symNodeEvalFuel env fuel t).sizeBytes = w
  | 0, _, _, h => nomatch h
  | fuel + 1, t, w, h => by
    cases t with
    | var id w' => exact Option.some.inj h
    | const sc => exact Option.some.inj h
    | castInt s tb a => exact Option.some.inj h
    | unaryOp uop a =>
      cases uop with
      | notBool => exact Option.some.inj h
      | neg => exact symNodeStaticWidth?_sound env fuel a w h
      | notInt => exact symNodeStaticWidth?_sound env fuel a w h
    | wrappingOp k a b =>
      obtain ⟨ha, hb, hnz⟩ := staticWidthsMatch_sound h
      have hwa := symNodeStaticWidth?_sound env fuel a w ha
      have hwb := symNodeStaticWidth?_sound env fuel b w hb
      have hok : ScWidthsOk (symNodeEvalFuel env fuel a) (symNodeEvalFuel env fuel b) :=
        ⟨hwa.symm ▸ hnz, hwa.trans hwb.symm⟩
      exact (symWrapEval_sizeBytes k hok).trans hwa
    | saturatingOp k sg a b =>
      obtain ⟨ha, hb, hnz⟩ := staticWidthsMatch_sound h
      have hwa := symNodeStaticWidth?_sound env fuel a w ha
      have hwb := symNodeStaticWidth?_sound env fuel b w hb
      have hok : ScWidthsOk (symNodeEvalFuel env fuel a) (symNodeEvalFuel env fuel b) :=
        ⟨hwa.symm ▸ hnz, hwa.trans hwb.symm⟩
      exact (symSatEval_sizeBytes k sg hok).trans hwa
    | checkedVal k sg a b =>
      obtain ⟨ha, hb, hnz⟩ := staticWidthsMatch_sound h
      have hwa := symNodeStaticWidth?_sound env fuel a w ha
      have hwb := symNodeStaticWidth?_sound env fuel b w hb
      have hok : ScWidthsOk (symNodeEvalFuel env fuel a) (symNodeEvalFuel env fuel b) :=
        ⟨hwa.symm ▸ hnz, hwa.trans hwb.symm⟩
      exact (symCheckedValEval_sizeBytes k sg hok).trans hwa
    | checkedFlag k sg a b =>
      change (match staticWidthsMatch (symNodeStaticWidth? fuel a) (symNodeStaticWidth? fuel b) with
        | some _ => some 1 | none => none) = some w at h
      cases hm : staticWidthsMatch (symNodeStaticWidth? fuel a) (symNodeStaticWidth? fuel b) with
      | none => rw [hm] at h; nomatch h
      | some wm =>
        rw [hm] at h
        injection h with hw
        subst hw
        obtain ⟨ha, hb, hnz⟩ := staticWidthsMatch_sound hm
        have hwa := symNodeStaticWidth?_sound env fuel a wm ha
        have hwb := symNodeStaticWidth?_sound env fuel b wm hb
        have hok : ScWidthsOk (symNodeEvalFuel env fuel a) (symNodeEvalFuel env fuel b) :=
          ⟨hwa.symm ▸ hnz, hwa.trans hwb.symm⟩
        exact (symCheckedFlagEval_validBool k sg hok).1
    | bitIntrinsic k a =>
      rw [symNodeStaticWidth?_bitIntrinsic] at h
      cases ha : symNodeStaticWidth? fuel a with
      | none => rw [ha] at h; nomatch h
      | some wa =>
        rw [ha] at h; dsimp only at h
        cases h0 : Nat.beq wa 0 with
        | true => rw [h0] at h; nomatch h
        | false =>
          rw [h0] at h; dsimp only at h
          have hwa := symNodeStaticWidth?_sound env fuel a wa ha
          have hnz : (symNodeEvalFuel env fuel a).sizeBytes ≠ 0 := hwa.symm ▸ nat_ne_of_beq_false h0
          cases k with
          | bswap =>
            injection h with hw; subst hw
            show ((evalBswap (symNodeEvalFuel env fuel a)).getD symDefaultScalar).sizeBytes = wa
            unfold evalBswap; rw [nat_beq_false_of_ne hnz]; exact hwa
          | bitreverse =>
            injection h with hw; subst hw
            show ((evalBitreverse (symNodeEvalFuel env fuel a)).getD symDefaultScalar).sizeBytes = wa
            unfold evalBitreverse; rw [nat_beq_false_of_ne hnz]; exact hwa
          | ctlz =>
            injection h with hw; subst hw
            show ((evalCtlz (symNodeEvalFuel env fuel a)).getD symDefaultScalar).sizeBytes = 4
            unfold evalCtlz; rw [unGuard_false hnz]; rfl
          | cttz =>
            injection h with hw; subst hw
            show ((evalCttz (symNodeEvalFuel env fuel a)).getD symDefaultScalar).sizeBytes = 4
            unfold evalCttz; rw [unGuard_false hnz]; rfl
          | ctpop =>
            injection h with hw; subst hw
            show ((evalCtpop (symNodeEvalFuel env fuel a)).getD symDefaultScalar).sizeBytes = 4
            unfold evalCtpop; rw [unGuard_false hnz]; rfl
          | ctlzNonzero | cttzNonzero => nomatch h
    | binOp op sg a b =>
      cases op with
      | add | mul | bitAnd | bitOr | bitXor =>
        obtain ⟨ha, hb, hnz⟩ := staticWidthsMatch_sound h
        have hwa := symNodeStaticWidth?_sound env fuel a w ha
        have hwb := symNodeStaticWidth?_sound env fuel b w hb
        show ((symBinOpEval _ sg (symNodeEvalFuel env fuel a) (symNodeEvalFuel env fuel b)).getD
          symDefaultScalar).sizeBytes = w
        unfold symBinOpEval evalScalarBinOp
        rw [nat_beq_false_of_ne (hwa.symm ▸ hnz), nat_beq_true_of_eq (hwa.trans hwb.symm)]
        exact hwa
      | sub =>
        obtain ⟨ha, hb, hnz⟩ := staticWidthsMatch_sound h
        have hwa := symNodeStaticWidth?_sound env fuel a w ha
        have hwb := symNodeStaticWidth?_sound env fuel b w hb
        show ((symBinOpEval .sub sg (symNodeEvalFuel env fuel a) (symNodeEvalFuel env fuel b)).getD
          symDefaultScalar).sizeBytes = w
        unfold symBinOpEval evalScalarBinOp
        rw [nat_beq_false_of_ne (hwa.symm ▸ hnz), nat_beq_true_of_eq (hwa.trans hwb.symm)]
        dsimp only
        cases Nat.ble (symNodeEvalFuel env fuel b).bits (symNodeEvalFuel env fuel a).bits <;> exact hwa
      | eq | ne | lt | le | gt | ge =>
        change (match staticWidthsMatch (symNodeStaticWidth? fuel a) (symNodeStaticWidth? fuel b) with
          | some _ => some 1 | none => none) = some w at h
        cases hm : staticWidthsMatch (symNodeStaticWidth? fuel a) (symNodeStaticWidth? fuel b) with
        | none => rw [hm] at h; nomatch h
        | some wm =>
          rw [hm] at h; injection h with hw; subst hw
          obtain ⟨ha, hb, hnz⟩ := staticWidthsMatch_sound hm
          have hwa := symNodeStaticWidth?_sound env fuel a wm ha
          have hwb := symNodeStaticWidth?_sound env fuel b wm hb
          show ((symBinOpEval _ sg (symNodeEvalFuel env fuel a) (symNodeEvalFuel env fuel b)).getD
            symDefaultScalar).sizeBytes = 1
          unfold symBinOpEval evalScalarBinOp
          rw [nat_beq_false_of_ne (hwa.symm ▸ hnz), nat_beq_true_of_eq (hwa.trans hwb.symm)]
          exact (boolToScalar_validBool _).1
      | cmp =>
        change (match staticWidthsMatch (symNodeStaticWidth? fuel a) (symNodeStaticWidth? fuel b) with
          | some _ => some 1 | none => none) = some w at h
        cases hm : staticWidthsMatch (symNodeStaticWidth? fuel a) (symNodeStaticWidth? fuel b) with
        | none => rw [hm] at h; nomatch h
        | some wm =>
          rw [hm] at h; injection h with hw; subst hw
          obtain ⟨ha, hb, hnz⟩ := staticWidthsMatch_sound hm
          have hwa := symNodeStaticWidth?_sound env fuel a wm ha
          have hwb := symNodeStaticWidth?_sound env fuel b wm hb
          show ((symBinOpEval .cmp sg (symNodeEvalFuel env fuel a) (symNodeEvalFuel env fuel b)).getD
            symDefaultScalar).sizeBytes = 1
          unfold symBinOpEval evalScalarBinOp
          rw [nat_beq_false_of_ne (hwa.symm ▸ hnz), nat_beq_true_of_eq (hwa.trans hwb.symm)]
          dsimp only
          cases sg with
          | false =>
            dsimp only
            cases Nat.beq (symNodeEvalFuel env fuel a).bits (symNodeEvalFuel env fuel b).bits with
            | true => rfl
            | false =>
              dsimp only
              cases Nat.ble (symNodeEvalFuel env fuel a).bits (symNodeEvalFuel env fuel b).bits <;> rfl
          | true =>
            dsimp only
            cases Nat.beq (wrapScalarBits (symNodeEvalFuel env fuel a).bits
                (scalarModulus (symNodeEvalFuel env fuel a).sizeBytes))
                (wrapScalarBits (symNodeEvalFuel env fuel b).bits
                  (scalarModulus (symNodeEvalFuel env fuel a).sizeBytes)) with
            | true => rfl
            | false =>
              dsimp only
              cases signedLt (wrapScalarBits (symNodeEvalFuel env fuel a).bits
                  (scalarModulus (symNodeEvalFuel env fuel a).sizeBytes))
                  (wrapScalarBits (symNodeEvalFuel env fuel b).bits
                    (scalarModulus (symNodeEvalFuel env fuel a).sizeBytes))
                  (symNodeEvalFuel env fuel a).sizeBytes <;> rfl
      | shl | shr =>
        change (match symNodeStaticWidth? fuel a, symNodeStaticWidth? fuel b with
          | some wa, some wb =>
            match Bool.and (Bool.not (Nat.beq wa 0)) (Bool.not (Nat.beq wb 0)) with
            | true => some wa | false => none
          | _, _ => none) = some w at h
        cases ha : symNodeStaticWidth? fuel a with
        | none => rw [ha] at h; nomatch h
        | some wa =>
          cases hb : symNodeStaticWidth? fuel b with
          | none => rw [ha, hb] at h; nomatch h
          | some wb =>
            rw [ha, hb] at h; dsimp only at h
            cases h0a : Nat.beq wa 0 with
            | true => rw [h0a] at h; nomatch h
            | false =>
              cases h0b : Nat.beq wb 0 with
              | true => rw [h0a, h0b] at h; nomatch h
              | false =>
                rw [h0a, h0b] at h; injection h with hw; subst hw
                have hwa := symNodeStaticWidth?_sound env fuel a wa ha
                have hwb := symNodeStaticWidth?_sound env fuel b wb hb
                show ((symBinOpEval _ sg (symNodeEvalFuel env fuel a) (symNodeEvalFuel env fuel b)).getD
                  symDefaultScalar).sizeBytes = wa
                unfold symBinOpEval evalScalarBinOp
                rw [nat_beq_false_of_ne (hwa.symm ▸ nat_ne_of_beq_false h0a),
                  nat_beq_false_of_ne (hwb.symm ▸ nat_ne_of_beq_false h0b)]
                exact hwa
      | addUnchecked | addWithOverflow | subUnchecked | subWithOverflow
      | mulUnchecked | mulWithOverflow | div | rem | shlUnchecked | shrUnchecked | offset =>
        nomatch h
    | uncheckedOp _ _ _ _ _ => nomatch h

theorem SymScalar.sizeBytes_of_staticWidth {s : SymScalar} {w : Nat}
    (h : s.staticWidth? = some w) (env : SymEnv) : (s.eval env).sizeBytes = w :=
  symNodeStaticWidth?_sound env s.fuel s.node w h

theorem SymScalar.validBool_of_static {s : SymScalar} (h : s.isValidBoolStatic = true)
    (env : SymEnv) :
    (s.eval env).sizeBytes = 1 ∧ ((s.eval env).bits = 0 ∨ (s.eval env).bits = 1) := by
  obtain ⟨node, fuel, wf⟩ := s
  cases fuel with
  | zero => nomatch h
  | succ n =>
    unfold SymScalar.isValidBoolStatic at h
    dsimp only at h
    cases node with
    | const sc =>
      dsimp only at h
      cases h1 : Nat.beq sc.sizeBytes 1 with
      | false => rw [h1] at h; nomatch h
      | true =>
        rw [h1] at h
        cases h0 : Nat.beq sc.bits 0 with
        | true => exact ⟨Nat.eq_of_beq_eq_true h1, Or.inl (Nat.eq_of_beq_eq_true h0)⟩
        | false =>
          rw [h0] at h
          cases h1b : Nat.beq sc.bits 1 with
          | false => rw [h1b] at h; nomatch h
          | true => exact ⟨Nat.eq_of_beq_eq_true h1, Or.inr (Nat.eq_of_beq_eq_true h1b)⟩
    | unaryOp uop a =>
      cases uop with
      | notBool =>
        show (symUnOpEval .notBool (symNodeEvalFuel env n a)).sizeBytes = 1 ∧
          ((symUnOpEval .notBool (symNodeEvalFuel env n a)).bits = 0 ∨
            (symUnOpEval .notBool (symNodeEvalFuel env n a)).bits = 1)
        dsimp only [symUnOpEval]
        cases Nat.beq (symNodeEvalFuel env n a).bits 0 with
        | true => exact ⟨rfl, Or.inr rfl⟩
        | false => exact ⟨rfl, Or.inl rfl⟩
      | neg | notInt => nomatch h
    | checkedFlag k sg a b =>
      dsimp only at h
      cases hm : staticWidthsMatch (symNodeStaticWidth? n a) (symNodeStaticWidth? n b) with
      | none => rw [hm] at h; nomatch h
      | some wm =>
        obtain ⟨ha, hb, hnz⟩ := staticWidthsMatch_sound hm
        have hwa := symNodeStaticWidth?_sound env n a wm ha
        have hwb := symNodeStaticWidth?_sound env n b wm hb
        exact symCheckedFlagEval_validBool k sg ⟨hwa.symm ▸ hnz, hwa.trans hwb.symm⟩
    | binOp op sg a b =>
      cases op with
      | eq | ne | lt | le | gt | ge =>
        dsimp only at h
        cases hm : staticWidthsMatch (symNodeStaticWidth? n a) (symNodeStaticWidth? n b) with
        | none => rw [hm] at h; nomatch h
        | some wm =>
          obtain ⟨ha, hb, hnz⟩ := staticWidthsMatch_sound hm
          have hwa := symNodeStaticWidth?_sound env n a wm ha
          have hwb := symNodeStaticWidth?_sound env n b wm hb
          show ((symBinOpEval _ sg (symNodeEvalFuel env n a) (symNodeEvalFuel env n b)).getD
            symDefaultScalar).sizeBytes = 1 ∧
            (((symBinOpEval _ sg (symNodeEvalFuel env n a) (symNodeEvalFuel env n b)).getD
              symDefaultScalar).bits = 0 ∨
             ((symBinOpEval _ sg (symNodeEvalFuel env n a) (symNodeEvalFuel env n b)).getD
              symDefaultScalar).bits = 1)
          unfold symBinOpEval evalScalarBinOp
          rw [nat_beq_false_of_ne (hwa.symm ▸ hnz), nat_beq_true_of_eq (hwa.trans hwb.symm)]
          exact boolToScalar_validBool _
      | add | addUnchecked | addWithOverflow | sub | subUnchecked | subWithOverflow
      | mul | mulUnchecked | mulWithOverflow | div | rem | bitXor | bitAnd | bitOr
      | shl | shlUnchecked | shr | shrUnchecked | cmp | offset => nomatch h
    | var _ _ | castInt _ _ _ | wrappingOp _ _ _ | saturatingOp _ _ _ _
    | uncheckedOp _ _ _ _ _ | checkedVal _ _ _ _ | bitIntrinsic _ _ => nomatch h

/-- Env-independent static discharge of a single side condition (widths on
compound expressions, static `validBool`, and constant `assertHolds`). -/
def symCondStatic : SymCond → Bool
  | .widthsMatch a b =>
    match staticWidthsMatch a.staticWidth? b.staticWidth? with
    | some _ => true
    | none => false
  | .widthNonzero a =>
    match a.staticWidth? with
    | some wa => Bool.not (Nat.beq wa 0)
    | none => false
  | .validBool a => a.isValidBoolStatic
  | .assertHolds c expected =>
    match c.asConst? with
    | some sc => Nat.beq sc.bits (match expected with | true => 1 | false => 0)
    | none => false
  | _ => false

/-- Env-independent static discharge of a side-condition list. -/
def condsStatic (cs : List SymCond) : Bool :=
  cs.foldr (fun c acc => Bool.and (symCondStatic c) acc) true

theorem symCondStatic_sound {c : SymCond} (h : symCondStatic c = true) (env : SymEnv) :
    c.holds env := by
  cases c with
  | widthsMatch a b =>
    simp only [symCondStatic] at h
    cases hm : staticWidthsMatch a.staticWidth? b.staticWidth? with
    | none => rw [hm] at h; nomatch h
    | some w =>
      obtain ⟨ha, hb, hnz⟩ := staticWidthsMatch_sound hm
      exact ⟨(SymScalar.sizeBytes_of_staticWidth ha env).symm ▸ hnz,
        (SymScalar.sizeBytes_of_staticWidth ha env).trans
          (SymScalar.sizeBytes_of_staticWidth hb env).symm⟩
  | widthNonzero a =>
    simp only [symCondStatic] at h
    cases ha : a.staticWidth? with
    | none => rw [ha] at h; nomatch h
    | some wa =>
      rw [ha] at h; dsimp only at h
      cases h0 : Nat.beq wa 0 with
      | true => rw [h0] at h; nomatch h
      | false =>
        show (a.eval env).sizeBytes ≠ 0
        rw [SymScalar.sizeBytes_of_staticWidth ha env]
        exact nat_ne_of_beq_false h0
  | validBool a =>
    exact SymScalar.validBool_of_static h env
  | assertHolds c expected =>
    simp only [symCondStatic] at h
    cases hc : c.asConst? with
    | none => rw [hc] at h; nomatch h
    | some sc =>
      rw [hc] at h
      cases expected with
      | true =>
        show (c.eval env).bits = 1
        rw [symScalar_eval_of_asConst hc env]
        exact Nat.eq_of_beq_eq_true h
      | false =>
        show (c.eval env).bits = 0
        rw [symScalar_eval_of_asConst hc env]
        exact Nat.eq_of_beq_eq_true h
  | _ => nomatch h

theorem condsStatic_sound :
    ∀ {cs : List SymCond}, condsStatic cs = true → ∀ env, condsHold env cs
  | [], _, _ => trivial
  | c :: rest, h, env => by
    have h' : Bool.and (symCondStatic c) (condsStatic rest) = true := h
    cases hc : symCondStatic c with
    | false => rw [hc] at h'; nomatch h'
    | true =>
      rw [hc] at h'
      exact ⟨symCondStatic_sound hc env, condsStatic_sound h' env⟩

/-- Load-bearing reflective certificate: a sealed `BoolCertCut condsStatic cs`
discharges `condsHold env cs` for every environment. -/
theorem condsHold_of_boolCert {cs : List SymCond} (hCert : BoolCertCut condsStatic cs)
    (env : SymEnv) : condsHold env cs :=
  condsStatic_sound (BoolCertCut.unseal hCert) env

/-- End-to-end multi-chunk soundness with side conditions discharged entirely
by a sealed `BoolCertCut condsStatic cs`. -/
theorem symRunChunks_of_condsCert {cfg : SymConfig} {ks : List SymChunk} {args : List SymVal}
    {v : SymVal} {fin : SymProg} {cs : List SymCond}
    (hRun : symRunChunks cfg ks (symProgEntry cfg args) = .ret v fin cs)
    (hCert : BoolCertCut condsStatic cs) (env : SymEnv) {post : MirOutcome → Prop}
    (hpost : post (.normal (v.eval env, (fin.toMachineState cfg env).memory))) :
    ExecWithinStepsV2026 cfg.body (symValsEval env args) cfg.callees post (chunksTotal ks) ∧
      MirWpConverges cfg.body
        (initMachineStateWithCallees cfg.body (symValsEval env args) cfg.callees) post ∧
      MirNoUBTree (mirTree cfg.body
        (initMachineStateWithCallees cfg.body (symValsEval env args) cfg.callees)) := by
  obtain ⟨_, hE, _, hW, hU⟩ := symRunChunks_sound hRun env (condsHold_of_boolCert hCert env) hpost
  exact ⟨hE, hW, hU⟩

/-! ## Part XVII: Explicit `stepMirState`, `execStepOutcome`, and `mirCallTree` Bridges -/

/-- Exact single-step refinement directly onto unmodified `stepMirState`. -/
theorem symProgStep_stepMirState_sound_obs {cfg : SymConfig} {p p' : SymProg} {cs : List SymCond}
    (h : symProgStep cfg p = .step p' cs) (env : SymEnv) (hc : condsHold env cs) :
    stepMirState cfg.body (.running (p.toMachineState cfg env)) =
      MirStepNode.emitStep ((symProgObs cfg p).eval env) (p'.toMachineState cfg env) :=
  symProgStep_sound_obs h env hc

/-- Exact root-return refinement directly onto unmodified `stepMirState`. -/
theorem symProgStep_ret_stepMirState_sound {cfg : SymConfig} {p : SymProg} {v : SymVal}
    {fin : SymProg} {cs : List SymCond} (h : symProgStep cfg p = .ret v fin cs) (env : SymEnv) :
    stepMirState cfg.body (.running (p.toMachineState cfg env)) =
      MirStepNode.retNormal (v.eval env) (p.toMachineState cfg env).memory :=
  (symProgStep_ret_sound h env).2.2

/-- Return soundness lifted directly onto Episode 1's `Framework.StepWp.execStepOutcome`. -/
theorem symProgRunSteps_ret_execStepOutcome {cfg : SymConfig} {k : Nat} {p : SymProg}
    {v : SymVal} {fin : SymProg} {cs : List SymCond}
    (h : symProgRunSteps cfg k p = .ret v fin cs) (env : SymEnv) (hc : condsHold env cs)
    {post : MirOutcome → Prop}
    (hpost : post (.normal (v.eval env, (fin.toMachineState cfg env).memory))) :
    execStepOutcome (v2026Step cfg.body) post (fun _ => False) k (p.toMachineState cfg env) :=
  reachesDoneWithinV2026_iff_execStepOutcome.mp (symProgRunSteps_ret_sound h env hc hpost)

/-- Standalone (`callees = []`) multi-chunk soundness directly onto unmodified
`mirCallTree cfg.body (symValsEval env args)`. -/
theorem symRunChunks_mirCallTree_sound {cfg : SymConfig} (hcal : cfg.callees = [])
    {ks : List SymChunk} {args : List SymVal} {v : SymVal} {fin : SymProg} {cs : List SymCond}
    (h : symRunChunks cfg ks (symProgEntry cfg args) = .ret v fin cs) (env : SymEnv)
    (hc : condsHold env cs) {post : MirOutcome → Prop}
    (hpost : post (.normal (v.eval env, (fin.toMachineState cfg env).memory))) :
    MirNoUBTree (mirCallTree cfg.body (symValsEval env args)) ∧
      ∀ tr out, Trusted.ITree.ReachesRet (mirCallTree cfg.body (symValsEval env args)) tr out →
        post out := by
  obtain ⟨hR, _⟩ := symRunChunks_sound h env hc hpost
  have hExec : execStepOutcome (v2026Step cfg.body) post (fun _ => False) (chunksTotal ks)
      (initMachineState cfg.body (symValsEval env args)) := by
    have hE := reachesDoneWithinV2026_iff_execStepOutcome.mp hR
    rw [symProgEntry_toMachineState, hcal] at hE
    exact hE
  exact ⟨mirNoUBTree_mirCallTree_of_v2026Exec hExec,
    reachesRet_post_mirCallTree_of_v2026Exec hExec⟩

/-! ## Part XVIII: Statement-Level & `Assert`-Terminator Exactness & Fail-Closed UB / Panic -/

/-- Structural width validity precondition separating arithmetic UB (`.ub`) from
unsupported width mismatch (`.unsupported`) in `evalScalarBinOp` / `evalRvalue`. -/
def symCondWidthOk (env : SymEnv) : SymCond → Prop
  | .binNoOverflowAdd _ a b | .binNoOverflowSub _ a b | .binNoOverflowMul _ a b
  | .binDivSafe _ a b | .binRemSafe _ a b =>
    ScWidthsOk (a.eval env) (b.eval env)
  | .binShiftInBounds a b =>
    (a.eval env).sizeBytes ≠ 0 ∧ (b.eval env).sizeBytes ≠ 0
  | .validBool _ => True
  | _ => False

theorem symScalarBinOp_ub_of_not_conds {op : BinOp} {signed : Bool} {a b : SymScalar}
    {res : SymVal} {c : SymCond} (h : symScalarBinOp op signed a b = some (res, [c]))
    (env : SymEnv) (hw : symCondWidthOk env c) (hn : ¬ c.holds env)
    (locals : List LocalSlot) (mem : Memory) :
    evalScalarBinOp op (a.eval env) (b.eval env) locals mem signed = .ub := by
  cases op with
  | addUnchecked =>
    injection h with h; injection h with _ h2; injection h2 with h2; subst h2
    have hW : ScWidthsOk (a.eval env) (b.eval env) := hw
    unfold evalScalarBinOp
    rw [nat_beq_false_of_ne hW.1, nat_beq_true_of_eq hW.2]
    dsimp only
    cases signed with
    | false =>
      dsimp only
      cases hb : Nat.ble (scalarModulus (a.eval env).sizeBytes)
          (Nat.add (a.eval env).bits (b.eval env).bits) with
      | true => rfl
      | false => exact absurd ⟨hW, nat_lt_of_ble_false hb⟩ hn
    | true =>
      dsimp only
      cases hb : signedOverflowAdd (a.eval env).bits (b.eval env).bits (a.eval env).sizeBytes with
      | true => rfl
      | false => exact absurd ⟨hW, hb⟩ hn
  | subUnchecked =>
    injection h with h; injection h with _ h2; injection h2 with h2; subst h2
    have hW : ScWidthsOk (a.eval env) (b.eval env) := hw
    unfold evalScalarBinOp
    rw [nat_beq_false_of_ne hW.1, nat_beq_true_of_eq hW.2]
    dsimp only
    cases signed with
    | false =>
      dsimp only
      cases hb : Nat.ble (b.eval env).bits (a.eval env).bits with
      | false => rfl
      | true =>
        dsimp only
        cases hd : Nat.ble (scalarModulus (a.eval env).sizeBytes)
            (Nat.sub (a.eval env).bits (b.eval env).bits) with
        | true => rfl
        | false => exact absurd ⟨hW, Nat.le_of_ble_eq_true hb, nat_lt_of_ble_false hd⟩ hn
    | true =>
      dsimp only
      cases hb : signedOverflowSub (a.eval env).bits (b.eval env).bits (a.eval env).sizeBytes with
      | true => rfl
      | false => exact absurd ⟨hW, hb⟩ hn
  | mulUnchecked =>
    injection h with h; injection h with _ h2; injection h2 with h2; subst h2
    have hW : ScWidthsOk (a.eval env) (b.eval env) := hw
    unfold evalScalarBinOp
    rw [nat_beq_false_of_ne hW.1, nat_beq_true_of_eq hW.2]
    dsimp only
    cases signed with
    | false =>
      dsimp only
      cases hb : Nat.ble (scalarModulus (a.eval env).sizeBytes)
          (Nat.mul (a.eval env).bits (b.eval env).bits) with
      | true => rfl
      | false => exact absurd ⟨hW, nat_lt_of_ble_false hb⟩ hn
    | true =>
      dsimp only
      cases hb : signedOverflowMul (a.eval env).bits (b.eval env).bits (a.eval env).sizeBytes with
      | true => rfl
      | false => exact absurd ⟨hW, hb⟩ hn
  | div =>
    injection h with h; injection h with _ h2; injection h2 with h2; subst h2
    have hW : ScWidthsOk (a.eval env) (b.eval env) := hw
    unfold evalScalarBinOp
    rw [nat_beq_false_of_ne hW.1, nat_beq_true_of_eq hW.2]
    dsimp only
    cases hz : Nat.beq (b.eval env).bits 0 with
    | true => rfl
    | false =>
      dsimp only
      cases signed with
      | false => exact absurd ⟨hW, nat_ne_of_beq_false hz, trivial⟩ hn
      | true =>
        unfold evalSignedDiv
        dsimp only
        cases hm : Bool.and
            (Nat.beq (wrapScalarBits (a.eval env).bits (scalarModulus (a.eval env).sizeBytes))
              (scalarPow2 (Nat.sub (Nat.mul (a.eval env).sizeBytes 8) 1)))
            (Nat.beq (wrapScalarBits (b.eval env).bits (scalarModulus (a.eval env).sizeBytes))
              (Nat.sub (scalarModulus (a.eval env).sizeBytes) 1)) with
        | true => rfl
        | false =>
          exact absurd ⟨hW, nat_ne_of_beq_false hz, minNegOne_ok_of_guard_false hm⟩ hn
  | rem =>
    injection h with h; injection h with _ h2; injection h2 with h2; subst h2
    have hW : ScWidthsOk (a.eval env) (b.eval env) := hw
    unfold evalScalarBinOp
    rw [nat_beq_false_of_ne hW.1, nat_beq_true_of_eq hW.2]
    dsimp only
    cases hz : Nat.beq (b.eval env).bits 0 with
    | true => rfl
    | false =>
      dsimp only
      cases signed with
      | false => exact absurd ⟨hW, nat_ne_of_beq_false hz, trivial⟩ hn
      | true =>
        unfold evalSignedRem
        dsimp only
        cases hm : Bool.and
            (Nat.beq (wrapScalarBits (a.eval env).bits (scalarModulus (a.eval env).sizeBytes))
              (scalarPow2 (Nat.sub (Nat.mul (a.eval env).sizeBytes 8) 1)))
            (Nat.beq (wrapScalarBits (b.eval env).bits (scalarModulus (a.eval env).sizeBytes))
              (Nat.sub (scalarModulus (a.eval env).sizeBytes) 1)) with
        | true => rfl
        | false =>
          exact absurd ⟨hW, nat_ne_of_beq_false hz, minNegOne_ok_of_guard_false hm⟩ hn
  | shlUnchecked | shrUnchecked =>
    injection h with h; injection h with _ h2; injection h2 with h2; subst h2
    have hWa : (a.eval env).sizeBytes ≠ 0 := hw.1
    have hWb : (b.eval env).sizeBytes ≠ 0 := hw.2
    unfold evalScalarBinOp
    rw [nat_beq_false_of_ne hWa, nat_beq_false_of_ne hWb]
    dsimp only
    cases hb : Nat.ble (Nat.mul (a.eval env).sizeBytes 8) (b.eval env).bits with
    | true => rfl
    | false => exact absurd ⟨hWa, hWb, nat_lt_of_ble_false hb⟩ hn
  | add | addWithOverflow | sub | subWithOverflow | mul | mulWithOverflow
  | bitXor | bitAnd | bitOr | eq | lt | le | ne | ge | gt | cmp =>
    injection h with h; injection h with _ h2; injection h2 with h2; subst h2; exact False.elim hw
  | shl | shr =>
    injection h with h; injection h with _ h2; nomatch h2
  | offset => nomatch h

/-- Statement-level generic fail-closed UB for `Rvalue`: if a supported rvalue
records a UB-guarded condition `[c]` whose width precondition holds (`symCondWidthOk`)
and whose arithmetic/validity guard fails (`¬ c.holds env`), unmodified trusted
`evalRvalue` returns `.ub` (covering all 7 UB-guarded `binaryOp`s plus `bool`
validity on `unaryOp .not` and `use`). -/
theorem symRvalue_ub_of_not_conds {globals : List CapturedAllocation} {layouts : LayoutTable}
    {decls : List LocalDecl} {locals : List SymSlot} {rv : Rvalue} {v : SymVal}
    {locals' : List SymSlot} {c : SymCond}
    (h : symRvalue globals layouts decls locals rv = some (v, locals', [c])) (env : SymEnv)
    (hw : symCondWidthOk env c) (hn : ¬ c.holds env)
    (hUseBoolSize : ∀ sc, c = .validBool sc → (sc.eval env).sizeBytes = 1)
    (mem : Memory) (hg : mem.globals = globals) :
    evalRvalue (symSlotsEval env locals) rv mem decls layouts = .ub := by
  cases rv with
  | use op =>
    simp only [symRvalue] at h
    cases h1 : symOperand globals layouts decls locals op with
    | none => rw [h1] at h; nomatch h
    | some r =>
      obtain ⟨w, l₁⟩ := r
      rw [h1] at h; dsimp only at h
      cases h2 : loadedValueStaticOk layouts decls op with
      | true => rw [h2] at h; nomatch h
      | false =>
        rw [h2] at h; dsimp only at h
        cases hty : operandTy decls layouts op with
        | none => rw [hty] at h; nomatch h
        | some ty =>
          rw [hty] at h; dsimp only at h
          cases hk : ty.kind with
          | bool =>
            rw [hk] at h
            cases has : w.asScalar? with
            | none => rw [has] at h; nomatch h
            | some sc =>
              rw [has] at h
              injection h with h; injection h with _ h; injection h with _ hcs
              injection hcs with hc; subst hc
              simp only [evalRvalue]
              rw [hg, (symOperand_sound h1 env mem.borrows mem.callerLocals mem.callStack).1,
                symVal_eval_of_asScalar has env]
              dsimp only
              have hsz : (sc.eval env).sizeBytes = 1 := hUseBoolSize sc rfl
              have hne : Bool.or (Nat.beq (sc.eval env).bits 0) (Nat.beq (sc.eval env).bits 1) =
                  false := by
                cases h0 : Nat.beq (sc.eval env).bits 0 with
                | true => exact absurd ⟨hsz, Or.inl (Nat.eq_of_beq_eq_true h0)⟩ hn
                | false =>
                  cases h1b : Nat.beq (sc.eval env).bits 1 with
                  | true => exact absurd ⟨hsz, Or.inr (Nat.eq_of_beq_eq_true h1b)⟩ hn
                  | false => rfl
              cases op with
              | constant _ => nomatch h2
              | copy _ | move _ =>
                simp only [validateLoadedValue, hty, hk, hne]
          | char | int _ | uint _ | float _ | ref _ _ | rawPtr _ _ | array _ _ | slice _
          | str | tuple _ | adt _ _ | fnDef _ _ | fnPtr _ _ _ _ | closure _ | alias
          | never | dynamic | param _ | foreign _ | other _ => rw [hk] at h; nomatch h
  | unaryOp uop op =>
    cases uop with
    | ptrMetadata => nomatch h
    | neg =>
      simp only [symRvalue] at h
      cases h1 : symOperand globals layouts decls locals op with
      | none => rw [h1] at h; nomatch h
      | some r =>
        obtain ⟨w, l₁⟩ := r
        rw [h1] at h; dsimp only at h
        cases ha : w.asScalar? with
        | none => rw [ha] at h; nomatch h
        | some x =>
          rw [ha] at h
          injection h with h; injection h with _ h; injection h with _ hcs
          injection hcs with hc; subst hc; exact False.elim hw
    | not =>
      simp only [symRvalue] at h
      cases h1 : symOperand globals layouts decls locals op with
      | none => rw [h1] at h; nomatch h
      | some r =>
        obtain ⟨w, l₁⟩ := r
        rw [h1] at h; dsimp only at h
        cases ha : w.asScalar? with
        | none => rw [ha] at h; nomatch h
        | some x =>
          rw [ha] at h; dsimp only at h
          cases hty : operandTy decls layouts op with
          | none => rw [hty] at h; nomatch h
          | some ty =>
            rw [hty] at h; dsimp only at h
            cases hk : ty.kind with
            | bool =>
              rw [hk] at h
              injection h with h; injection h with _ h; injection h with _ hcs
              injection hcs with hc; subst hc
              simp only [evalRvalue]
              rw [hg, (symOperand_sound h1 env mem.borrows mem.callerLocals mem.callStack).1,
                symVal_eval_of_asScalar ha env]
              dsimp only [evalUnaryNot]
              rw [hty]; dsimp only; rw [hk]; dsimp only
              cases hsz : Nat.beq (x.eval env).sizeBytes 1 with
              | false => rfl
              | true =>
                dsimp only
                cases h0 : Nat.beq (x.eval env).bits 0 with
                | true =>
                  exact absurd ⟨Nat.eq_of_beq_eq_true hsz, Or.inl (Nat.eq_of_beq_eq_true h0)⟩ hn
                | false =>
                  dsimp only
                  cases h1b : Nat.beq (x.eval env).bits 1 with
                  | true =>
                    exact absurd ⟨Nat.eq_of_beq_eq_true hsz, Or.inr (Nat.eq_of_beq_eq_true h1b)⟩ hn
                  | false => rfl
            | uint _ | int _ =>
              rw [hk] at h
              injection h with h; injection h with _ h; injection h with _ hcs
              injection hcs with hc; subst hc; exact False.elim hw
            | char | float _ | ref _ _ | rawPtr _ _ | array _ _ | slice _ | str | tuple _
            | adt _ _ | fnDef _ _ | fnPtr _ _ _ _ | closure _ | alias | never | dynamic
            | param _ | foreign _ | other _ => rw [hk] at h; nomatch h
  | binaryOp op lhsOp rhsOp =>
    simp only [symRvalue] at h
    cases h1 : symOperand globals layouts decls locals lhsOp with
    | none => rw [h1] at h; nomatch h
    | some r1 =>
      obtain ⟨lv, l₁⟩ := r1
      rw [h1] at h; dsimp only at h
      cases h2 : symOperand globals layouts decls l₁ rhsOp with
      | none => rw [h2] at h; nomatch h
      | some r2 =>
        obtain ⟨rv', l₂⟩ := r2
        rw [h2] at h; dsimp only at h
        cases ha : lv.asScalar? with
        | none => rw [ha] at h; nomatch h
        | some a =>
          cases hb' : rv'.asScalar? with
          | none => rw [ha, hb'] at h; nomatch h
          | some b =>
            rw [ha, hb'] at h; dsimp only at h
            cases hs : symScalarBinOp op (operandIsSigned decls lhsOp layouts) a b with
            | none => rw [hs] at h; nomatch h
            | some r3 =>
              obtain ⟨res, cs'⟩ := r3
              rw [hs] at h
              injection h with h; injection h with _ h; injection h with _ hcs
              subst hcs
              simp only [evalRvalue]
              rw [hg, (symOperand_sound h1 env mem.borrows mem.callerLocals mem.callStack).1]
              dsimp only
              rw [(symOperand_sound h2 env mem.borrows mem.callerLocals mem.callStack).1,
                symVal_eval_of_asScalar ha env, symVal_eval_of_asScalar hb' env]
              cases op with
              | offset => nomatch hs
              | add | addUnchecked | addWithOverflow | sub | subUnchecked | subWithOverflow
              | mul | mulUnchecked | mulWithOverflow | div | rem | bitXor | bitAnd | bitOr
              | shl | shlUnchecked | shr | shrUnchecked | eq | lt | le | ne | ge | gt | cmp =>
                exact symScalarBinOp_ub_of_not_conds hs env hw hn (symSlotsEval env l₂) mem
  | cast ck op targetTy =>
    cases ck with
    | intToInt =>
      simp only [symRvalue] at h
      cases h1 : symOperand globals layouts decls locals op with
      | none => rw [h1] at h; nomatch h
      | some r =>
        obtain ⟨w, l₁⟩ := r
        rw [h1] at h; dsimp only at h
        cases ha : w.asScalar? with
        | none => rw [ha] at h; nomatch h
        | some x =>
          cases ht : intCastTargetBytes targetTy.kind with
          | none => rw [ha, ht] at h; nomatch h
          | some tb =>
            rw [ha, ht] at h
            injection h with h; injection h with _ h; injection h with _ hcs
            injection hcs with hc; subst hc; exact False.elim hw
    | _ => nomatch h
  | aggregate ak ops =>
    cases ak with
    | tuple | array _ | closure _ =>
      simp only [symRvalue] at h
      repeat' (first | contradiction | (injection h with h; injection h with _ h; injection h with _ h; nomatch h) | split at h)
    | adt _ _ _ | rawPtr _ _ | coroutine _ => nomatch h
  | discriminant place =>
    obtain ⟨ploc, pproj⟩ := place
    cases pproj with
    | cons _ _ => nomatch h
    | nil =>
      simp only [symRvalue] at h
      repeat' (first | contradiction | (injection h with h; injection h with _ h; injection h with _ h; nomatch h) | split at h)
  | _ => nomatch h

/-- Statement-level generic fail-closed UB on `evalStmt`. -/
theorem symStmt_ub_of_not_conds {cfg : SymConfig} {p : SymProg} {body : CapturedMir}
    {stmt : Statement} {f' : SymFrame} {c : SymCond}
    (h : symStmt cfg.body.allocations body p.frame stmt = some (f', [c])) (env : SymEnv)
    (hw : symCondWidthOk env c) (hn : ¬ c.holds env)
    (hUseBoolSize : ∀ sc, c = .validBool sc → (sc.eval env).sizeBytes = 1) :
    evalStmt (p.toMachineState cfg env) stmt body.localDecls body.layouts = MirStepNode.fail .ub := by
  obtain ⟨kind, span⟩ := stmt
  cases kind with
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
        rw [hr] at h; dsimp only at h
        have hcs : cs' = [c] := by
          cases hg : get? locals₁ dloc with
          | none => rw [hg] at h; nomatch h
          | some sl =>
            rw [hg] at h
            cases sl with
            | dead => nomatch h
            | uninit | init _ =>
              dsimp only at h
              cases hs : set? locals₁ dloc (.init v) with
              | none => rw [hs] at h; nomatch h
              | some _ => rw [hs] at h; injection h with h; injection h with _ h2
        subst hcs
        have hUb := symRvalue_ub_of_not_conds hr env hw hn hUseBoolSize (p.toMemory cfg env) rfl
        dsimp only [evalStmt]
        rw [show (p.toMachineState cfg env).frame.locals = symSlotsEval env p.frame.locals from rfl,
          show (p.toMachineState cfg env).memory = p.toMemory cfg env from rfl, hUb]
  | nop => simp only [symStmt] at h; nomatch h
  | storageLive _ =>
    simp only [symStmt] at h
    repeat' (first | contradiction | (injection h with h; injection h with _ h; nomatch h) | split at h)
  | storageDead _ =>
    simp only [symStmt] at h
    repeat' (first | contradiction | (injection h with h; injection h with _ h; nomatch h) | split at h)
  | deinit dst =>
    obtain ⟨_, dproj⟩ := dst
    cases dproj with
    | cons _ _ => nomatch h
    | nil =>
      simp only [symStmt] at h
      repeat' (first | contradiction | (injection h with h; injection h with _ h; nomatch h) | split at h)
  | _ => nomatch h

/-- The active program point of `p` is an `assign` statement. -/
def SymProg.atStmt (cfg : SymConfig) (p : SymProg) : Bool :=
  match get? (p.active.getD cfg.body).basicBlocks p.frame.blockIdx with
  | some bb =>
    match get? bb.statements p.frame.stmtIdx with
    | some _ => true
    | none => false
  | none => false

/-- Program-level generic fail-closed UB for a statement step (`Rvalue.binaryOp`
unchecked/div/rem/shift or invalid `bool`). -/
theorem symProgStep_stmt_ub_of_not_conds {cfg : SymConfig} {p p' : SymProg} {c : SymCond}
    (h : symProgStep cfg p = .step p' [c]) (env : SymEnv) (hat : p.atStmt cfg = true)
    (hw : symCondWidthOk env c) (hn : ¬ c.holds env)
    (hUseBoolSize : ∀ sc, c = .validBool sc → (sc.eval env).sizeBytes = 1) :
    stepMirFn cfg.body (p.toMachineState cfg env) = MirStepNode.fail .ub := by
  obtain ⟨bb, hb, hcase⟩ := symProgStep_dispatch h (fun h' => SymStepRes.noConfusion h') env
  unfold SymProg.atStmt at hat
  rw [hb] at hat; dsimp only at hat
  cases hs : get? bb.statements p.frame.stmtIdx with
  | none => rw [hs] at hat; nomatch hat
  | some stmt =>
    rcases hcase with ⟨stmt', f', cs', hs', hst, hr, hstep⟩ | ⟨hs', _, _⟩
    · rw [hs] at hs'; injection hs' with hse; subst hse
      injection hr with _ hcs; subst hcs
      rw [hstep]
      exact symStmt_ub_of_not_conds hst env hw hn hUseBoolSize
    · rw [hs] at hs'; nomatch hs'

/-- Run-level generic fail-closed UB for a statement step. -/
theorem symProgRunSteps_stmt_ub_refutes {cfg : SymConfig} {k : Nat} {p q q' : SymProg}
    {cs : List SymCond} {c : SymCond} (hpre : symProgRunSteps cfg k p = .step q cs)
    (hstep : symProgStep cfg q = .step q' [c]) (hat : q.atStmt cfg = true) (env : SymEnv)
    (hc : condsHold env cs) (hw : symCondWidthOk env c) (hn : ¬ c.holds env)
    (hUseBoolSize : ∀ sc, c = .validBool sc → (sc.eval env).sizeBytes = 1) :
    ¬ MirNoUBTree (mirTree cfg.body (p.toMachineState cfg env)) ∧
      (∀ post, ¬ MirWpConverges cfg.body (p.toMachineState cfg env) post) ∧
      (∀ post bound, ¬ ReachesDoneWithinV2026 cfg.body post bound (p.toMachineState cfg env)) :=
  symProgRunSteps_fault_refutes hpre env hc (fk := .ub) (by
    unfold v2026Step
    rw [symProgStep_stmt_ub_of_not_conds hstep env hat hw hn hUseBoolSize]
    rfl)

/-- Unwind action of an `Assert` terminator at `p` (if `p` is at an `Assert`). -/
def SymProg.atAssertUnwind? (cfg : SymConfig) (p : SymProg) : Option UnwindAction :=
  match get? (p.active.getD cfg.body).basicBlocks p.frame.blockIdx with
  | some bb =>
    match get? bb.statements p.frame.stmtIdx with
    | some _ => none
    | none =>
      match bb.terminator.kind with
      | .assert _ _ _ unwind => some unwind
      | _ => none
  | none => none

/-- Generic fail-closed `Assert` violation: when `assertHolds` fails at an
`Assert` terminator, unmodified `evalTerminator` runs `applyUnwindAction`
(`.unreachable` -> `fail .ub`, `.terminate` -> `retOutcome .abort`, root
`.continue_` -> `retOutcome .panic`). -/
theorem symTerm_assert_fail_of_not_conds {cfg : SymConfig} {p : SymProg} {body : CapturedMir}
    {cond : Operand} {expected : Bool} {target : BasicBlockIdx} {unwind : UnwindAction}
    {span : String} {p' : SymProg} {cs : List SymCond}
    (h : symTerm cfg p body
      { kind := .assert cond expected target unwind, span := span } = .step p' cs)
    (env : SymEnv) (hn : ¬ condsHold env cs) :
    ∃ locals', evalTerminator (p.toMachineState cfg env)
      { kind := .assert cond expected target unwind, span := span } (some body) =
      match applyUnwindAction (p.toMachineState cfg env) locals'
          (p.toMachineState cfg env).memory unwind with
      | .running nextState => MirStepNode.step nextState
      | .halted out => MirStepNode.retOutcome out
      | .faulted fk => MirStepNode.fail fk := by
  simp only [symTerm] at h
  cases ho : symOperand cfg.body.allocations body.layouts body.localDecls p.frame.locals cond with
  | none => rw [ho] at h; nomatch h
  | some r =>
    obtain ⟨v, locals'⟩ := r
    rw [ho] at h; dsimp only at h
    cases ha : v.asScalar? with
    | none => rw [ha] at h; nomatch h
    | some c =>
      rw [ha] at h
      injection h with _ h2
      subst h2
      refine ⟨symSlotsEval env locals', ?_⟩
      dsimp only [evalTerminator, SymProg.toMachineState, SymProg.toMemory, SymFrame.eval,
        bodyLocalDeclsOf]
      rw [symOperand_bodyCast_sound ho env, symVal_eval_of_asScalar ha env]
      dsimp only
      cases expected with
      | true =>
        dsimp only
        cases hq : Nat.beq (c.eval env).bits 1 with
        | false => rfl
        | true => exact absurd ⟨Nat.eq_of_beq_eq_true hq, trivial⟩ hn
      | false =>
        dsimp only
        cases hq : Nat.beq (c.eval env).bits 0 with
        | false => rfl
        | true => exact absurd ⟨Nat.eq_of_beq_eq_true hq, trivial⟩ hn

/-- Program-level `Assert` with `unwind = .unreachable`: violated `SymCond`
implies unmodified `stepMirFn = MirStepNode.fail .ub`. -/
theorem symProgStep_assert_ub_of_not_conds {cfg : SymConfig} {p p' : SymProg} {cs : List SymCond}
    (h : symProgStep cfg p = .step p' cs) (env : SymEnv) (hn : ¬ condsHold env cs)
    (hat : p.atAssertUnwind? cfg = some .unreachable) :
    stepMirFn cfg.body (p.toMachineState cfg env) = MirStepNode.fail .ub := by
  obtain ⟨bb, hb, hcase⟩ := symProgStep_dispatch h (fun h' => SymStepRes.noConfusion h') env
  unfold SymProg.atAssertUnwind? at hat
  rw [hb] at hat; dsimp only at hat
  cases hs : get? bb.statements p.frame.stmtIdx with
  | some _ => rw [hs] at hat; nomatch hat
  | none =>
    rw [hs] at hat; dsimp only at hat
    rcases hcase with ⟨_, _, _, hs', _, _, _⟩ | ⟨_, ht, hstep⟩
    · rw [hs] at hs'; nomatch hs'
    · rw [hstep]
      cases hterm : bb.terminator with
      | mk kind span =>
        rw [hterm] at ht hat; dsimp only at hat
        cases kind with
        | assert cond expected target unwind =>
          injection hat with hu; subst hu
          obtain ⟨_, heq⟩ := symTerm_assert_fail_of_not_conds ht env hn
          exact heq
        | _ => nomatch hat

/-- Run-level `Assert (.unreachable)` fail-closed UB refutation. -/
theorem symProgRunSteps_assert_ub_refutes {cfg : SymConfig} {k : Nat} {p q q' : SymProg}
    {cs cs' : List SymCond} (hpre : symProgRunSteps cfg k p = .step q cs)
    (hstep : symProgStep cfg q = .step q' cs')
    (hat : q.atAssertUnwind? cfg = some .unreachable) (env : SymEnv)
    (hc : condsHold env cs) (hn : ¬ condsHold env cs') :
    ¬ MirNoUBTree (mirTree cfg.body (p.toMachineState cfg env)) ∧
      (∀ post, ¬ MirWpConverges cfg.body (p.toMachineState cfg env) post) ∧
      (∀ post bound, ¬ ReachesDoneWithinV2026 cfg.body post bound (p.toMachineState cfg env)) :=
  symProgRunSteps_fault_refutes hpre env hc (fk := .ub) (by
    unfold v2026Step
    rw [symProgStep_assert_ub_of_not_conds hstep env hn hat]
    rfl)

/-- Program-level root `Assert` with `unwind = .continue_`: violated `SymCond`
implies unmodified `stepMirFn = MirStepNode.retOutcome .panic`. -/
theorem symProgStep_assert_panic_of_not_conds {cfg : SymConfig} {p p' : SymProg}
    {cs : List SymCond} (h : symProgStep cfg p = .step p' cs) (env : SymEnv)
    (hn : ¬ condsHold env cs) (hstack : p.stack = [])
    (hat : p.atAssertUnwind? cfg = some .continue_) :
    stepMirFn cfg.body (p.toMachineState cfg env) = MirStepNode.retOutcome .panic := by
  obtain ⟨bb, hb, hcase⟩ := symProgStep_dispatch h (fun h' => SymStepRes.noConfusion h') env
  unfold SymProg.atAssertUnwind? at hat
  rw [hb] at hat; dsimp only at hat
  cases hs : get? bb.statements p.frame.stmtIdx with
  | some _ => rw [hs] at hat; nomatch hat
  | none =>
    rw [hs] at hat; dsimp only at hat
    rcases hcase with ⟨_, _, _, hs', _, _, _⟩ | ⟨_, ht, hstep⟩
    · rw [hs] at hs'; nomatch hs'
    · rw [hstep]
      cases hterm : bb.terminator with
      | mk kind span =>
        rw [hterm] at ht hat; dsimp only at hat
        cases kind with
        | assert cond expected target unwind =>
          injection hat with hu; subst hu
          obtain ⟨_, heq⟩ := symTerm_assert_fail_of_not_conds ht env hn
          rw [heq]
          simp only [applyUnwindAction, SymProg.toMachineState, SymProg.toMemory,
            hstack, symStackEval_nil, unwindFromCallStack]
        | _ => nomatch hat

/-- Run-level root `Assert (.continue_)` panic refutation against any
normal-return postcondition (`¬ post .panic`). -/
theorem symProgRunSteps_assert_panic_refutes {cfg : SymConfig} {k : Nat} {p q q' : SymProg}
    {cs cs' : List SymCond} (hpre : symProgRunSteps cfg k p = .step q cs)
    (hstep : symProgStep cfg q = .step q' cs') (hstack : q.stack = [])
    (hat : q.atAssertUnwind? cfg = some .continue_) (env : SymEnv)
    (hc : condsHold env cs) (hn : ¬ condsHold env cs')
    {post : MirOutcome → Prop} (hnp : ¬ post .panic) :
    ∀ bound, ¬ ReachesDoneWithinV2026 cfg.body post bound (p.toMachineState cfg env) :=
  symProgRunSteps_done_refutes hpre env hc (out := .panic) (by
    unfold v2026Step
    rw [symProgStep_assert_panic_of_not_conds hstep env hn hstack hat]
    rfl) hnp

end Anneal.MirSymExec.ChunkedCallV2026
