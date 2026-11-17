-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Trusted
import Anneal.MirLiftCore

/-!
# The `@[irreducible]` opaque callee table

An opaque, sealed callee table over the real `Trusted.Rustc.V2026_06_01` MIR, layout,
and machine-state types, whose full resolution `OpaqueCalleeTable.lookup` is *exactly*
the trusted `lookupCallee` (`opaqueCalleeTable_lookup_eq_trusted`), so every theorem below
is a statement about the trusted machine.

* **Sealing.** `OpaqueCalleeTable` and its five operations (`ofList`, `toList`,
  `lookupRaw`, `traitImpls`, `lookup`) are `@[irreducible]`: `whnf` / `simp` / `decide`
  never unfold a table into its `O(|callees|)` list scan. All reasoning goes through the
  defining equations and the `O(1)` use-site certificates.
* **`O(1)` certificates.** Raw `lookupRaw` certificates (`lookupRaw_ofList_cons_hit` /
  `_skip` / `_miss`, the single-declaration `lookupRaw_ofList_append_cons_of_skips`, and
  `lookupRaw_ofList_of_mem_nodup`), the per-table `traitImpls_ofList` certificate, and
  resolution certificates for monomorphic, polymorphic, free-generic, trait-override,
  polymorphic trait-override, and default-method calls, all with `tbl.toList`-free forms
  (`lookupCallee_hit_free_poly_opaque`, `lookupCallee_trait_hit_cert`,
  `lookupCallee_trait_hit_poly_cert`, `lookupCallee_trait_default_hit_cert`), plus the
  miss certificates.
* **Exact literal `switchInt` pruning.** `stepTerminatorWith` is the trusted
  `evalTerminator` with the `.call` / `.tailCall` arms copied verbatim under an abstract
  resolver; a literal discriminant jumps straight to its taken target. Pruning is exact
  (`stepTerminatorWith_prune_exact`) and a pruned opaque step *is* the trusted
  `stepMirFn` (`stepBranchPruned_eq_trusted`).
* **Unconditional trusted frame lemma.** Every trusted step (`evalStmt`,
  `evalTerminator`, the intrinsic helpers, hence `stepMirFn`) and every resolver-parametric
  pruned step keeps `memory.callees` and `memory.traitImpls` (`stepMirFn_frames`,
  `stepBranchPruned_frames`), so `evalWithOpaqueCallees_eq_trusted_unconditional`
  identifies the opaque evaluator with iterated `stepMirFn` from *every* state linking the
  table (`initMachineStateWithCallees`, `initMachineStateWithMemoryAndCallees`).
* **Demanded-key call-cone narrowing** (`evalWithOpaqueCallees_cone_narrow`) and its
  **bridge to `Anneal.MirLiftCore`**: raw-lookup agreement on a cone
  (`OpaqueCalleeTable.AgreesOn`) is `MirLiftCore.calleesAgreeOn` on the sealed lists and
  narrows the opaque evaluator, `runCfgWithCallees`, `wpMirExecSym`, and
  `MirWpConverges` without unfolding `tbl.toList` at the use site — under semantic
  `ConeReach`, the syntactic `CallConeClosed` check, the `MirLiftCore.CalleeInitWf` forms
  reaching the empty table (`_closed_wf`), and the polymorphic `CallConeClosedPoly` forms
  whose trait-impl side condition is stated over the sealed `traitImpls` (`_closed_poly_wf`).

Concrete canaries, the `@[irreducible]` opacity witness, the heartbeat regression gate,
and the module-wide axiom / namespace audit live in
`tests/mir/CompilerQueryAndOpaqueCalleeTests.lean`.
-/

namespace Anneal.OpaqueCalleeTable

open Trusted.Effect (FailureKind Outcome)
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## `DecidableEq` without `BEq` on the real `Trusted` V2026_06_01 types

Every instance below is `DecidableEq` only. No `BEq` instance is derived or registered
for any type, so `a == b` always elaborates through `instBEqOfDecidableEq` and the core
`instLawfulBEq` applies (`beq_iff_eq`); the shadowing hazard a redundant `BEq`
derivation would introduce is demonstrated in
`tests/mir/CompilerQueryAndOpaqueCalleeTests.lean` (`ShadowingDemo`). -/

/-- Axiom-free `DecidableEq` from an injective constructor index with a left
inverse (`ofIdx (idx a) = a`). Used for the nine enumeration-shaped `Trusted`
types instead of `deriving instance DecidableEq`: Lean's enumeration deriving
handler emits the *global* auxiliaries `T.ofNat` / `T.ofNat_ctorIdx` in the
derived type's own namespace, so two modules that both derive such an instance can
never be imported together. `Anneal.Rustc.V2026_06_01.TraceCheck` (imported by the
`Anneal` root) already derives all nine (a co-import fails with `(kernel) constant
has already been declared 'Trusted.Rustc.V2026_06_01.MirAst.Mutability.ofNat'`);
the instances below create constants only inside this namespace. Non-enumeration
`deriving instance` handlers name everything hygienically in the current
namespace, so they never collide. -/
def decEqOfCtorIdx {α : Type} (idx : α → Nat) (ofIdx : Nat → α)
    (h : ∀ a, ofIdx (idx a) = a) : DecidableEq α := fun a b =>
  if hab : idx a = idx b then isTrue (by rw [← h a, hab, h b])
  else isFalse (fun e => hab (congrArg idx e))

/-- Left inverse of `AbiPassMode.ctorIdx`. -/
def abiPassModeOfIdx : Nat → AbiPassMode
  | 0 => .ignore | 1 => .direct | 2 => .pair | _ => .indirect

instance instDecidableEqAbiPassMode : DecidableEq AbiPassMode :=
  decEqOfCtorIdx AbiPassMode.ctorIdx abiPassModeOfIdx (fun a => by cases a <;> rfl)

/-- Left inverse of `UintTy.ctorIdx`. -/
def uintTyOfIdx : Nat → UintTy
  | 0 => .u8 | 1 => .u16 | 2 => .u32 | 3 => .u64 | 4 => .u128 | _ => .usize

instance instDecidableEqUintTy : DecidableEq UintTy :=
  decEqOfCtorIdx UintTy.ctorIdx uintTyOfIdx (fun a => by cases a <;> rfl)

/-- Left inverse of `IntTy.ctorIdx`. -/
def intTyOfIdx : Nat → IntTy
  | 0 => .i8 | 1 => .i16 | 2 => .i32 | 3 => .i64 | 4 => .i128 | _ => .isize

instance instDecidableEqIntTy : DecidableEq IntTy :=
  decEqOfCtorIdx IntTy.ctorIdx intTyOfIdx (fun a => by cases a <;> rfl)

/-- Left inverse of `FloatTy.ctorIdx`. -/
def floatTyOfIdx : Nat → FloatTy
  | 0 => .f16 | 1 => .f32 | 2 => .f64 | _ => .f128

instance instDecidableEqFloatTy : DecidableEq FloatTy :=
  decEqOfCtorIdx FloatTy.ctorIdx floatTyOfIdx (fun a => by cases a <;> rfl)

/-- Left inverse of `Mutability.ctorIdx`. -/
def mutabilityOfIdx : Nat → Mutability
  | 0 => .not | _ => .mut

instance instDecidableEqMutability : DecidableEq Mutability :=
  decEqOfCtorIdx Mutability.ctorIdx mutabilityOfIdx (fun a => by cases a <;> rfl)

/-- Left inverse of `Safety.ctorIdx`. -/
def safetyOfIdx : Nat → Safety
  | 0 => .safe | _ => .unsafe_

instance instDecidableEqSafety : DecidableEq Safety :=
  decEqOfCtorIdx Safety.ctorIdx safetyOfIdx (fun a => by cases a <;> rfl)

/-- Left inverse of `UnOp.ctorIdx`. -/
def unOpOfIdx : Nat → UnOp
  | 0 => .not | 1 => .neg | _ => .ptrMetadata

instance instDecidableEqUnOp : DecidableEq UnOp :=
  decEqOfCtorIdx UnOp.ctorIdx unOpOfIdx (fun a => by cases a <;> rfl)

/-- Left inverse of `BinOp.ctorIdx`. -/
def binOpOfIdx : Nat → BinOp
  | 0 => .add | 1 => .addUnchecked | 2 => .addWithOverflow | 3 => .sub | 4 => .subUnchecked
  | 5 => .subWithOverflow | 6 => .mul | 7 => .mulUnchecked | 8 => .mulWithOverflow | 9 => .div
  | 10 => .rem | 11 => .bitXor | 12 => .bitAnd | 13 => .bitOr | 14 => .shl | 15 => .shlUnchecked
  | 16 => .shr | 17 => .shrUnchecked | 18 => .eq | 19 => .lt | 20 => .le | 21 => .ne | 22 => .ge
  | 23 => .gt | 24 => .cmp | _ => .offset

instance instDecidableEqBinOp : DecidableEq BinOp :=
  decEqOfCtorIdx BinOp.ctorIdx binOpOfIdx (fun a => by cases a <;> rfl)

/-- Left inverse of `RetagKind.ctorIdx`. -/
def retagKindOfIdx : Nat → RetagKind
  | 0 => .fnEntry | 1 => .twoPhase | 2 => .raw | _ => .default

instance instDecidableEqRetagKind : DecidableEq RetagKind :=
  decEqOfCtorIdx RetagKind.ctorIdx retagKindOfIdx (fun a => by cases a <;> rfl)

deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.Layout.Size
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.Layout.Align
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.Layout.WrappingRange
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.Layout.PrimitiveKind
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.Layout.ScalarLayout
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.Layout.FieldsShape
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.Layout.VariantsShape
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.Layout.BackendRepr
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.Layout.TypeLayout
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.Layout.ArgAbi
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.Layout.CallConv
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.Layout.FnAbi
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.Layout.LayoutTable
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.ScalarInt
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.ProvenancePtr
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirSemantics.MirObs

/-- Constructor tag of a `RigidTy`: `rigidTyStructEq_iff` dispatches on a single
diagonal `match` (off-diagonal constructor pairs are refuted by the match
compiler from `rigidTyTag a = rigidTyTag b`, avoiding a quadratic case split). -/
def rigidTyTag : RigidTy → Nat
  | .param .. => 0
  | .alias .. => 1
  | .bool => 2
  | .char => 3
  | .int _ => 4
  | .uint _ => 5
  | .float _ => 6
  | .never => 7
  | .str => 8
  | .tuple _ => 9
  | .array .. => 10
  | .slice _ => 11
  | .ref .. => 12
  | .rawPtr .. => 13
  | .adt .. => 14
  | .fnDef .. => 15
  | .fnPtr .. => 16
  | .closure .. => 17
  | .dynamic _ => 18
  | .foreign _ => 19
  | .other _ => 20

mutual
/-- Structural Boolean equality on the nested inductive `RigidTy` (catch-all
`false` off the diagonal, so it evaluates under `decide`, `whnf`, and the kernel). -/
def rigidTyStructEq : RigidTy → RigidTy → Bool
  | .param i n, .param j m => decide (i = j) && decide (n = m)
  | .alias d as, .alias e bs => decide (d = e) && rigidTyListStructEq as bs
  | .bool, .bool => true
  | .char, .char => true
  | .int w, .int v => decide (w = v)
  | .uint w, .uint v => decide (w = v)
  | .float w, .float v => decide (w = v)
  | .never, .never => true
  | .str, .str => true
  | .tuple as, .tuple bs => rigidTyListStructEq as bs
  | .array x n, .array y m => rigidTyStructEq x y && decide (n = m)
  | .slice x, .slice y => rigidTyStructEq x y
  | .ref m x, .ref n y => decide (m = n) && rigidTyStructEq x y
  | .rawPtr m x, .rawPtr n y => decide (m = n) && rigidTyStructEq x y
  | .adt d as, .adt e bs => decide (d = e) && rigidTyListStructEq as bs
  | .fnDef d as, .fnDef e bs => decide (d = e) && rigidTyListStructEq as bs
  | .fnPtr ins o sf cc, .fnPtr jns p tf dd =>
    rigidTyListStructEq ins jns && rigidTyStructEq o p && decide (sf = tf) && decide (cc = dd)
  | .closure d as, .closure e bs => decide (d = e) && rigidTyListStructEq as bs
  | .dynamic d, .dynamic e => decide (d = e)
  | .foreign d, .foreign e => decide (d = e)
  | .other d, .other e => decide (d = e)
  | _, _ => false

/-- Pointwise companion of `rigidTyStructEq`. -/
def rigidTyListStructEq : List RigidTy → List RigidTy → Bool
  | [], [] => true
  | a :: as, b :: bs => rigidTyStructEq a b && rigidTyListStructEq as bs
  | _, _ => false
end

/-- Off the constructor diagonal, `rigidTyStructEq` is `false` (one cheap case per
constructor pair; no recursion needed). -/
theorem rigidTyStructEq_of_tag_ne {a b : RigidTy} (h : rigidTyTag a ≠ rigidTyTag b) :
    rigidTyStructEq a b = false := by
  cases a <;> cases b <;> first | rfl | exact absurd rfl h

mutual
/-- `rigidTyStructEq` decides `RigidTy` equality. Each diagonal case is unfolded by
`show` (definitional unfolding) rather than `simp [rigidTyStructEq]`, so no
equation lemmas are generated for the catch-all definition: Lean proves the
catch-all equation `rigidTyStructEq.eq_22` (and `eq_def`) with whatever simp set
the *ambient import closure* provides, and inside the `Anneal` root closure those
auto-generated lemmas depend on `Classical.choice` (caught by the module audit). -/
theorem rigidTyStructEq_iff (a b : RigidTy) : rigidTyStructEq a b = true ↔ a = b :=
  if hTag : rigidTyTag a = rigidTyTag b then
    match a, b, hTag with
    | .param i n, .param j m, _ => by
      show (decide (i = j) && decide (n = m)) = true ↔ _
      simp
    | .alias d as, .alias e bs, _ => by
      have ih := rigidTyListStructEq_iff as bs
      show (decide (d = e) && rigidTyListStructEq as bs) = true ↔ _
      simp [ih]
    | .bool, .bool, _ => by show true = true ↔ _; simp
    | .char, .char, _ => by show true = true ↔ _; simp
    | .int w, .int v, _ => by show decide (w = v) = true ↔ _; simp
    | .uint w, .uint v, _ => by show decide (w = v) = true ↔ _; simp
    | .float w, .float v, _ => by show decide (w = v) = true ↔ _; simp
    | .never, .never, _ => by show true = true ↔ _; simp
    | .str, .str, _ => by show true = true ↔ _; simp
    | .tuple as, .tuple bs, _ => by
      have ih := rigidTyListStructEq_iff as bs
      show rigidTyListStructEq as bs = true ↔ _
      simp [ih]
    | .array x n, .array y m, _ => by
      have ih := rigidTyStructEq_iff x y
      show (rigidTyStructEq x y && decide (n = m)) = true ↔ _
      simp [ih]
    | .slice x, .slice y, _ => by
      have ih := rigidTyStructEq_iff x y
      show rigidTyStructEq x y = true ↔ _
      simp [ih]
    | .ref m x, .ref n y, _ => by
      have ih := rigidTyStructEq_iff x y
      show (decide (m = n) && rigidTyStructEq x y) = true ↔ _
      simp [ih]
    | .rawPtr m x, .rawPtr n y, _ => by
      have ih := rigidTyStructEq_iff x y
      show (decide (m = n) && rigidTyStructEq x y) = true ↔ _
      simp [ih]
    | .adt d as, .adt e bs, _ => by
      have ih := rigidTyListStructEq_iff as bs
      show (decide (d = e) && rigidTyListStructEq as bs) = true ↔ _
      simp [ih]
    | .fnDef d as, .fnDef e bs, _ => by
      have ih := rigidTyListStructEq_iff as bs
      show (decide (d = e) && rigidTyListStructEq as bs) = true ↔ _
      simp [ih]
    | .fnPtr ins o sf cc, .fnPtr jns p tf dd, _ => by
      have ih₁ := rigidTyListStructEq_iff ins jns
      have ih₂ := rigidTyStructEq_iff o p
      show (rigidTyListStructEq ins jns && rigidTyStructEq o p && decide (sf = tf) &&
        decide (cc = dd)) = true ↔ _
      simp [ih₁, ih₂, Bool.and_assoc]
    | .closure d as, .closure e bs, _ => by
      have ih := rigidTyListStructEq_iff as bs
      show (decide (d = e) && rigidTyListStructEq as bs) = true ↔ _
      simp [ih]
    | .dynamic d, .dynamic e, _ => by show decide (d = e) = true ↔ _; simp
    | .foreign d, .foreign e, _ => by show decide (d = e) = true ↔ _; simp
    | .other d, .other e, _ => by show decide (d = e) = true ↔ _; simp
  else by
    rw [rigidTyStructEq_of_tag_ne hTag]
    exact ⟨(fun h => nomatch h), fun e => absurd (congrArg rigidTyTag e) hTag⟩

/-- Pointwise companion of `rigidTyStructEq_iff`. -/
theorem rigidTyListStructEq_iff (as bs : List RigidTy) :
    rigidTyListStructEq as bs = true ↔ as = bs :=
  match as, bs with
  | [], [] => by show true = true ↔ _; simp
  | [], _ :: _ => by show false = true ↔ _; simp
  | _ :: _, [] => by show false = true ↔ _; simp
  | a :: as, b :: bs => by
    have ih₁ := rigidTyStructEq_iff a b
    have ih₂ := rigidTyListStructEq_iff as bs
    show (rigidTyStructEq a b && rigidTyListStructEq as bs) = true ↔ _
    simp [ih₁, ih₂]
end

/-- Axiom-free manual `DecidableEq` for the nested inductive `RigidTy`
(`deriving DecidableEq` does not support nested inductives). -/
instance instDecidableEqRigidTy : DecidableEq RigidTy :=
  fun a b => decidable_of_iff _ (rigidTyStructEq_iff a b)

deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.Ty
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.TraitRef
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.TraitImplEntry
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.ConstScalar
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.ConstValue
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.ConstOperand
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.MirPhaseTag
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.ContractRole
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.GenericParamDef
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.ProjectionElem
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.Place
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.Operand
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.NullOp
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.BorrowKind
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.CastKind
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.AggregateKind
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.Rvalue
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.NonDivergingIntrinsic
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.StatementKind
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.Statement
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.SwitchTargets
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.UnwindAction
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.TerminatorKind
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.Terminator
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.BasicBlockData
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.LocalDecl
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.CapturedAllocation
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.CapturedMir

/-- Constructor tag of a `Value`. -/
def valueTag : Value → Nat
  | .unit => 0
  | .scalar _ => 1
  | .ptr .. => 2
  | .aggregate .. => 3

mutual
/-- Structural Boolean equality on the nested inductive `Value`. -/
def valueStructEq : Value → Value → Bool
  | .unit, .unit => true
  | .scalar a, .scalar b => decide (a = b)
  | .ptr p₁ s₁, .ptr p₂ s₂ => decide (p₁ = p₂) && decide (s₁ = s₂)
  | .aggregate v₁ fs₁, .aggregate v₂ fs₂ => decide (v₁ = v₂) && valueListStructEq fs₁ fs₂
  | _, _ => false

/-- Pointwise companion of `valueStructEq`. -/
def valueListStructEq : List Value → List Value → Bool
  | [], [] => true
  | a :: as, b :: bs => valueStructEq a b && valueListStructEq as bs
  | _, _ => false
end

theorem valueStructEq_of_tag_ne {a b : Value} (h : valueTag a ≠ valueTag b) :
    valueStructEq a b = false := by
  cases a <;> cases b <;> first | rfl | exact absurd rfl h

mutual
/-- `valueStructEq` decides `Value` equality. -/
theorem valueStructEq_iff (a b : Value) : valueStructEq a b = true ↔ a = b :=
  if hTag : valueTag a = valueTag b then
    match a, b, hTag with
    | .unit, .unit, _ => by show true = true ↔ _; simp
    | .scalar x, .scalar y, _ => by show decide (x = y) = true ↔ _; simp
    | .ptr p₁ s₁, .ptr p₂ s₂, _ => by
      show (decide (p₁ = p₂) && decide (s₁ = s₂)) = true ↔ _
      simp
    | .aggregate v₁ fs₁, .aggregate v₂ fs₂, _ => by
      have ih := valueListStructEq_iff fs₁ fs₂
      show (decide (v₁ = v₂) && valueListStructEq fs₁ fs₂) = true ↔ _
      simp [ih]
  else by
    rw [valueStructEq_of_tag_ne hTag]
    exact ⟨(fun h => nomatch h), fun e => absurd (congrArg valueTag e) hTag⟩

/-- Pointwise companion of `valueStructEq_iff`. -/
theorem valueListStructEq_iff (as bs : List Value) :
    valueListStructEq as bs = true ↔ as = bs :=
  match as, bs with
  | [], [] => by show true = true ↔ _; simp
  | [], _ :: _ => by show false = true ↔ _; simp
  | _ :: _, [] => by show false = true ↔ _; simp
  | a :: as, b :: bs => by
    have ih₁ := valueStructEq_iff a b
    have ih₂ := valueListStructEq_iff as bs
    show (valueStructEq a b && valueListStructEq as bs) = true ↔ _
    simp [ih₁, ih₂]
end

/-- Axiom-free manual `DecidableEq` for the nested inductive `Value`. -/
instance instDecidableEqValue : DecidableEq Value :=
  fun a b => decidable_of_iff _ (valueStructEq_iff a b)

deriving instance DecidableEq for Trusted.Effect.Outcome
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirSemantics.StackFrame
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirSemantics.TreeBorrowPerm
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirSemantics.BorrowEntry
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirSemantics.SavedCallerFrame
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirSemantics.FnPtrEntry
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirSemantics.Memory
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirSemantics.MachineState
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirSemantics.MirCallReq
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirSemantics.MirExecState

/-- `LawfulBEq CapturedMir` through `instBEqOfDecidableEq`. -/
theorem capturedMir_beq_iff_eq {a b : CapturedMir} : (a == b) = true ↔ a = b := beq_iff_eq

/-- `LawfulBEq MachineState` through `instBEqOfDecidableEq`. -/
theorem machineState_beq_iff_eq {a b : MachineState} : (a == b) = true ↔ a = b := beq_iff_eq

/-- `LawfulBEq TreeBorrowPerm` through `instBEqOfDecidableEq`: only `DecidableEq` is derived
here, so the redundant structural `BEq` of
`theory/Correspondence/V2026_06_01/L4_TreeBorrows.lean` is never needed. -/
theorem treeBorrowPerm_beq_iff_eq {a b : TreeBorrowPerm} : (a == b) = true ↔ a = b := beq_iff_eq

/-- `BEq RigidTy` is `instBEqOfDecidableEq` (no shadowing `BEq` exists). -/
theorem rigidTy_beq_eq_decide (a b : RigidTy) : (a == b) = decide (a = b) := rfl

/-- `LawfulBEq RigidTy` through `instBEqOfDecidableEq`: `beq_iff_eq` applies. -/
theorem rigidTy_beq_iff_eq {a b : RigidTy} : (a == b) = true ↔ a = b := beq_iff_eq

/-- `LawfulBEq LayoutTable` through `instBEqOfDecidableEq`. -/
theorem layoutTable_beq_iff_eq {a b : LayoutTable} : (a == b) = true ↔ a = b := beq_iff_eq

/-- `LawfulBEq TraitImplEntry` through `instBEqOfDecidableEq`. -/
theorem traitImplEntry_beq_iff_eq {a b : TraitImplEntry} : (a == b) = true ↔ a = b :=
  beq_iff_eq

/-- `LawfulBEq FnAbi` through `instBEqOfDecidableEq`. -/
theorem fnAbi_beq_iff_eq {a b : FnAbi} : (a == b) = true ↔ a = b := beq_iff_eq

/-- `DefPath` is `String`, whose core `DecidableEq` is reused (no new instance). -/
theorem defPath_beq_iff_eq {a b : DefPath} : (a == b) = true ↔ a = b := beq_iff_eq

/-- Soundness of the trusted byte-wise `listByteEq`. -/
theorem listByteEq_sound : ∀ (xs ys : List UInt8), listByteEq xs ys = true → xs = ys
  | [], [], _ => rfl
  | b₁ :: bs₁, b₂ :: bs₂, h => by
    unfold listByteEq at h
    cases hb : Nat.beq b₁.toBitVec.toNat b₂.toBitVec.toNat with
    | false => rw [hb] at h; nomatch h
    | true =>
      rw [hb] at h
      have hByte : b₁ = b₂ :=
        UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true hb))
      rw [hByte, listByteEq_sound bs₁ bs₂ h]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

/-- Reflexivity of the trusted byte-wise `listByteEq`. -/
theorem listByteEq_refl : ∀ (xs : List UInt8), listByteEq xs xs = true
  | [] => rfl
  | b :: bs => by simp [listByteEq, listByteEq_refl bs]

/-- Trusted byte-wise `stringEq` is `DefPath` (string) equality. -/
theorem stringEq_eq_true_iff {a b : String} : stringEq a b = true ↔ a = b := by
  constructor
  · intro h
    unfold stringEq at h
    exact String.toByteArray_inj.mp
      (ByteArray.ext (Array.toList_inj.mp (listByteEq_sound _ _ h)))
  · rintro rfl
    unfold stringEq
    exact listByteEq_refl _

/-- Trusted `stringEq` coincides with `decide (a = b)`. -/
theorem stringEq_eq_decide (a b : String) : stringEq a b = decide (a = b) := by
  cases h : stringEq a b
  · have hne : ¬ a = b := fun hab => by
      rw [stringEq_eq_true_iff.mpr hab] at h
      nomatch h
    simp [hne]
  · simp [stringEq_eq_true_iff.mp h]


/-! ## Part A: the `@[irreducible]` opaque callee table -/

/-- Lookup key of a callee table: the arguments of the trusted `lookupCallee`
after the callee list. -/
structure CalleeKey : Type where
  /-- Caller layout table (`callerLayouts`). -/
  callerLayouts : LayoutTable
  /-- Callee `DefPath`. -/
  defPath : DefPath
  /-- Call-site generic type arguments. -/
  typeArgs : List RigidTy
  /-- Extra `TraitImplEntry` records (`Memory.traitImpls`). -/
  extraTraitImpls : List TraitImplEntry
  deriving DecidableEq

/-- Callee resolver `(callerLayouts, defPath, typeArgs, extraTraitImpls) ↦ body`:
the role played by `lookupCallee s.memory.callees` inside the trusted
`evalTerminator`. -/
abbrev CalleeResolver : Type :=
  LayoutTable → DefPath → List RigidTy → List TraitImplEntry → Option CapturedMir

/-- Apply a resolver to a key. -/
def CalleeKey.apply (r : CalleeResolver) (k : CalleeKey) : Option CapturedMir :=
  r k.callerLayouts k.defPath k.typeArgs k.extraTraitImpls

/-- The trusted list-backed resolver (`lookupCallee callees`). -/
def listResolver (callees : List CapturedMir) : CalleeResolver :=
  fun callerLayouts defPath typeArgs extra =>
    lookupCallee callees callerLayouts defPath typeArgs extra

/-- Opaque callee-table carrier, backed by a real `List CapturedMir` and sealed
`@[irreducible]` below so `whnf`/`simp`/`decide` never unfold a table into its
`O(|callees|)` list scan; all reasoning goes through the defining equations and
the `O(1)` certificate lemmas. -/
def OpaqueCalleeTable : Type := List CapturedMir

namespace OpaqueCalleeTable

/-- Seal a callee list into an opaque table. -/
def ofList (callees : List CapturedMir) : OpaqueCalleeTable := callees

/-- The underlying callee list. -/
def toList (tbl : OpaqueCalleeTable) : List CapturedMir := tbl

/-- Raw `DefPath` lookup (`findCallee?`). -/
def lookupRaw (tbl : OpaqueCalleeTable) (defPath : DefPath) : Option CapturedMir :=
  findCallee? tbl.toList defPath

/-- Full callee resolution: exactly the trusted `lookupCallee` (monomorphic hits,
polymorphic instantiation via `CapturedMir.instantiate` and
`RigidTy.computeLayout`, `TraitImplEntry` override/default resolution over
`extraTraitImpls ++ flatMapTraitImpls callees`, and misses). -/
def lookup (tbl : OpaqueCalleeTable) : CalleeResolver :=
  fun callerLayouts defPath typeArgs extra =>
    lookupCallee tbl.toList callerLayouts defPath typeArgs extra

/-- Key-based lookup. -/
def lookupKey (tbl : OpaqueCalleeTable) (k : CalleeKey) : Option CapturedMir :=
  k.apply tbl.lookup

/-- Captured `TraitImplEntry` records across the table (`flatMapTraitImpls tbl.toList`),
sealed `@[irreducible]` below so free-generic and trait-method certificates rewrite
`tbl.traitImpls` once per table instead of unfolding `tbl.toList` at every call site. -/
def traitImpls (tbl : OpaqueCalleeTable) : List TraitImplEntry :=
  flatMapTraitImpls tbl.toList

theorem toList_ofList (callees : List CapturedMir) : (ofList callees).toList = callees := rfl

theorem ofList_toList (tbl : OpaqueCalleeTable) : ofList tbl.toList = tbl := rfl

theorem lookupRaw_eq (tbl : OpaqueCalleeTable) (defPath : DefPath) :
    tbl.lookupRaw defPath = findCallee? tbl.toList defPath := rfl

theorem lookup_eq (tbl : OpaqueCalleeTable) (callerLayouts : LayoutTable) (defPath : DefPath)
    (typeArgs : List RigidTy) (extra : List TraitImplEntry) :
    tbl.lookup callerLayouts defPath typeArgs extra =
      lookupCallee tbl.toList callerLayouts defPath typeArgs extra := rfl

theorem lookupKey_eq (tbl : OpaqueCalleeTable) (k : CalleeKey) :
    tbl.lookupKey k = tbl.lookup k.callerLayouts k.defPath k.typeArgs k.extraTraitImpls := rfl

theorem traitImpls_eq (tbl : OpaqueCalleeTable) :
    tbl.traitImpls = flatMapTraitImpls tbl.toList := rfl

end OpaqueCalleeTable

attribute [irreducible] OpaqueCalleeTable OpaqueCalleeTable.ofList OpaqueCalleeTable.toList
  OpaqueCalleeTable.lookupRaw OpaqueCalleeTable.lookup OpaqueCalleeTable.traitImpls

/-- One-time per-table `traitImpls` certificate: `(ofList callees).traitImpls` is
`flatMapTraitImpls callees`. -/
theorem traitImpls_ofList (callees : List CapturedMir) :
    (OpaqueCalleeTable.ofList callees).traitImpls = flatMapTraitImpls callees := by
  rw [OpaqueCalleeTable.traitImpls_eq, OpaqueCalleeTable.toList_ofList]

/-- **Equivalence**: opaque-table lookup is the trusted `lookupCallee`. -/
theorem opaqueCalleeTable_lookup_eq_trusted (callees : List CapturedMir)
    (callerLayouts : LayoutTable) (defPath : DefPath) (typeArgs : List RigidTy)
    (extra : List TraitImplEntry) :
    (OpaqueCalleeTable.ofList callees).lookup callerLayouts defPath typeArgs extra =
      lookupCallee callees callerLayouts defPath typeArgs extra := by
  rw [OpaqueCalleeTable.lookup_eq, OpaqueCalleeTable.toList_ofList]

/-- Resolver-level form of `opaqueCalleeTable_lookup_eq_trusted`. -/
theorem opaqueCalleeTable_lookup_eq_listResolver (callees : List CapturedMir) :
    (OpaqueCalleeTable.ofList callees).lookup = listResolver callees := by
  funext callerLayouts defPath typeArgs extra
  exact opaqueCalleeTable_lookup_eq_trusted callees callerLayouts defPath typeArgs extra

/-- Raw certificate: a head entry with the requested `DefPath` hits in `O(1)`. -/
theorem lookupRaw_ofList_cons_hit {c : CapturedMir} {rest : List CapturedMir}
    {defPath : DefPath} (h : c.defPath = defPath) :
    (OpaqueCalleeTable.ofList (c :: rest)).lookupRaw defPath = some c := by
  rw [OpaqueCalleeTable.lookupRaw_eq, OpaqueCalleeTable.toList_ofList]
  simp [findCallee?, stringEq_eq_true_iff.mpr h]

/-- Raw certificate: a head entry with a different `DefPath` is skipped. -/
theorem lookupRaw_ofList_cons_miss {c : CapturedMir} {rest : List CapturedMir}
    {defPath : DefPath} (h : c.defPath ≠ defPath) :
    (OpaqueCalleeTable.ofList (c :: rest)).lookupRaw defPath =
      (OpaqueCalleeTable.ofList rest).lookupRaw defPath := by
  rw [OpaqueCalleeTable.lookupRaw_eq, OpaqueCalleeTable.lookupRaw_eq,
    OpaqueCalleeTable.toList_ofList, OpaqueCalleeTable.toList_ofList]
  have hne : stringEq c.defPath defPath = false := by
    cases hs : stringEq c.defPath defPath
    · rfl
    · exact absurd (stringEq_eq_true_iff.mp hs) h
  simp [findCallee?, hne]

/-- Raw certificate step in the trusted `findCallee?` form: a head entry whose
`DefPath` the trusted byte-wise `stringEq` rejects is skipped (what a capture
tool emits, discharged by kernel evaluation of one `stringEq`). -/
theorem lookupRaw_ofList_cons_skip {c : CapturedMir} {rest : List CapturedMir}
    {defPath : DefPath} (h : stringEq c.defPath defPath = false) :
    (OpaqueCalleeTable.ofList (c :: rest)).lookupRaw defPath =
      (OpaqueCalleeTable.ofList rest).lookupRaw defPath := by
  rw [OpaqueCalleeTable.lookupRaw_eq, OpaqueCalleeTable.lookupRaw_eq,
    OpaqueCalleeTable.toList_ofList, OpaqueCalleeTable.toList_ofList]
  simp only [findCallee?, h]

/-- Single-declaration raw certificate: every entry before the target is rejected
by the trusted `stringEq` (one Boolean fact, discharged by a single kernel
evaluation) and the target's `DefPath` matches. -/
theorem lookupRaw_ofList_append_cons_of_skips :
    ∀ {pre post : List CapturedMir} {c : CapturedMir} {defPath : DefPath},
      pre.all (fun x => !stringEq x.defPath defPath) = true → c.defPath = defPath →
        (OpaqueCalleeTable.ofList (pre ++ c :: post)).lookupRaw defPath = some c
  | [], _, _, _, _, hhit => lookupRaw_ofList_cons_hit hhit
  | x :: xs, post, c, defPath, hskip, hhit => by
    have hx : stringEq x.defPath defPath = false := by
      cases h : stringEq x.defPath defPath
      · rfl
      · simp [List.all_cons, h] at hskip
    have hxs : xs.all (fun x => !stringEq x.defPath defPath) = true := by
      simp only [List.all_cons, hx, Bool.not_false, Bool.true_and] at hskip
      exact hskip
    rw [List.cons_append, lookupRaw_ofList_cons_skip hx]
    exact lookupRaw_ofList_append_cons_of_skips (post := post) hxs hhit

/-- Amortized raw certificate: once the table's `DefPath`s are known to be
duplicate-free (checked once per table), every member's certificate is a plain
membership proof, with no string comparisons at the use site. -/
theorem lookupRaw_ofList_of_mem_nodup :
    ∀ {callees : List CapturedMir} {c : CapturedMir},
      (callees.map (·.defPath)).Nodup → c ∈ callees →
        (OpaqueCalleeTable.ofList callees).lookupRaw c.defPath = some c
  | [], _, _, hmem => nomatch hmem
  | x :: xs, c, hnd, hmem => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hmem with rfl | hxs
    · exact lookupRaw_ofList_cons_hit rfl
    · have hne : x.defPath ≠ c.defPath := by
        intro e
        exact hnd.1 (e ▸ List.mem_map_of_mem hxs)
      rw [lookupRaw_ofList_cons_miss hne]
      exact lookupRaw_ofList_of_mem_nodup hnd.2 hxs

/-- **`O(1)` certificate (direct monomorphic hit)**: from a raw certificate, the
full trusted resolution of a monomorphic callee rewrites to `some c`. -/
theorem lookupCallee_hit_mono {tbl : OpaqueCalleeTable} {callerLayouts : LayoutTable}
    {defPath : DefPath} {extra : List TraitImplEntry} {c : CapturedMir}
    (hraw : tbl.lookupRaw defPath = some c) (hmono : c.typeParamCount = 0) :
    tbl.lookup callerLayouts defPath [] extra = some c := by
  rw [OpaqueCalleeTable.lookupRaw_eq] at hraw
  rw [OpaqueCalleeTable.lookup_eq]
  unfold lookupCallee resolveCalleeBodyAndArgs?
  simp only [hraw, hmono]
  rfl

/-- **`O(1)` key certificate (direct monomorphic hit)**: the `CalleeKey` form of
`lookupCallee_hit_mono`. Rewrite with this (or with `OpaqueCalleeTable.lookupKey_eq`) instead of a
definitional `show` / `change` between `lookupKey` and `lookup`: the kernel ignores
`@[irreducible]`, and a definitional step between differently-headed sealed operations makes it
unfold the table into its `O(|callees|)` list scan (the heartbeat regression gate of
`tests/mir/CompilerQueryAndOpaqueCalleeTests.lean` measures exactly this). -/
theorem lookupKey_hit_mono {tbl : OpaqueCalleeTable} {k : CalleeKey} {c : CapturedMir}
    (hraw : tbl.lookupRaw k.defPath = some c) (hk : k.typeArgs = [])
    (hmono : c.typeParamCount = 0) : tbl.lookupKey k = some c := by
  obtain ⟨L, dp, tys, ti⟩ := k
  simp only at hraw hk
  subst hk
  rw [OpaqueCalleeTable.lookupKey_eq]
  exact lookupCallee_hit_mono hraw hmono

/-- Layout of one generic argument under `callerLayouts`, exactly as computed by
the trusted `lookupCallee` (rejecting arguments with out-of-range parameters). -/
def argLayout? (callerLayouts : LayoutTable) (argTy : RigidTy) : Option TypeLayout :=
  match allParamsInCallerLayouts (length callerLayouts.entries) argTy with
  | false => none
  | true =>
    RigidTy.computeLayout callerLayouts.pointerBits callerLayouts.entries
      (callerParamSubst 0 callerLayouts.entries) none argTy

/-- Layouts of all generic arguments (`none` if any argument is uninstantiable). -/
def instantiationLayouts? (callerLayouts : LayoutTable) : List RigidTy → Option (List TypeLayout)
  | [] => some []
  | ty :: rest =>
    match argLayout? callerLayouts ty, instantiationLayouts? callerLayouts rest with
    | some l, some ls => some (l :: ls)
    | _, _ => none

/-- The trusted accumulator loop `lookupCallee.resolveLayouts` is
`instantiationLayouts?`. -/
theorem resolveLayouts_eq_instantiationLayouts (callerLayouts : LayoutTable) :
    ∀ (tys : List RigidTy) (acc : List TypeLayout),
      lookupCallee.resolveLayouts callerLayouts tys acc =
        (instantiationLayouts? callerLayouts tys).map (acc.reverse ++ ·)
  | [], acc => by simp [lookupCallee.resolveLayouts, instantiationLayouts?]
  | ty :: rest, acc => by
    have ih := resolveLayouts_eq_instantiationLayouts callerLayouts rest
    simp only [lookupCallee.resolveLayouts, instantiationLayouts?, argLayout?]
    cases hp : allParamsInCallerLayouts (length callerLayouts.entries) ty with
    | false => simp
    | true =>
      cases hc : RigidTy.computeLayout callerLayouts.pointerBits callerLayouts.entries
          (callerParamSubst 0 callerLayouts.entries) none ty with
      | none => simp
      | some l =>
        simp only [ih]
        cases instantiationLayouts? callerLayouts rest <;> simp

/-- **`O(1)` certificate (direct polymorphic instantiation)**: from a resolution
certificate and an instantiation-layout certificate, the trusted resolution
rewrites to the instantiated body `c.instantiate (eff.zip argLayouts)`. -/
theorem lookupCallee_hit {tbl : OpaqueCalleeTable} {callerLayouts : LayoutTable}
    {defPath : DefPath} {typeArgs : List RigidTy} {extra : List TraitImplEntry}
    {c : CapturedMir} {eff : List RigidTy} {argLayouts : List TypeLayout}
    (hres : resolveCalleeBodyAndArgs? tbl.toList defPath typeArgs extra = some (c, eff))
    (hpoly : (c.typeParamCount == 0 && eff.isEmpty) = false)
    (harity : eff.length = c.typeParamCount)
    (hlay : instantiationLayouts? callerLayouts eff = some argLayouts) :
    tbl.lookup callerLayouts defPath typeArgs extra = some (c.instantiate (eff.zip argLayouts)) := by
  rw [OpaqueCalleeTable.lookup_eq]
  unfold lookupCallee
  simp only [hres, hpoly, harity, resolveLayouts_eq_instantiationLayouts, hlay]
  simp

/-- **`O(1)` certificate (miss)**: an unresolvable target misses. -/
theorem lookupCallee_miss {tbl : OpaqueCalleeTable} {callerLayouts : LayoutTable}
    {defPath : DefPath} {typeArgs : List RigidTy} {extra : List TraitImplEntry}
    (hres : resolveCalleeBodyAndArgs? tbl.toList defPath typeArgs extra = none) :
    tbl.lookup callerLayouts defPath typeArgs extra = none := by
  rw [OpaqueCalleeTable.lookup_eq]
  unfold lookupCallee
  simp [hres]

/-- Miss certificate for a direct non-generic call to an absent `DefPath`. -/
theorem lookupCallee_miss_direct {tbl : OpaqueCalleeTable} {callerLayouts : LayoutTable}
    {defPath : DefPath} {extra : List TraitImplEntry}
    (hraw : tbl.lookupRaw defPath = none) :
    tbl.lookup callerLayouts defPath [] extra = none := by
  rw [OpaqueCalleeTable.lookupRaw_eq] at hraw
  apply lookupCallee_miss
  simp [resolveCalleeBodyAndArgs?, hraw]

/-- Miss certificate for an arity-mismatched resolved generic callee. -/
theorem lookupCallee_miss_arity {tbl : OpaqueCalleeTable} {callerLayouts : LayoutTable}
    {defPath : DefPath} {typeArgs : List RigidTy} {extra : List TraitImplEntry}
    {c : CapturedMir} {eff : List RigidTy}
    (hres : resolveCalleeBodyAndArgs? tbl.toList defPath typeArgs extra = some (c, eff))
    (hpoly : (c.typeParamCount == 0 && eff.isEmpty) = false)
    (harity : eff.length ≠ c.typeParamCount) :
    tbl.lookup callerLayouts defPath typeArgs extra = none := by
  rw [OpaqueCalleeTable.lookup_eq]
  unfold lookupCallee
  simp [hres, hpoly, harity]

/-- Miss certificate for a resolved generic callee whose arguments have no
computable layout under `callerLayouts`. -/
theorem lookupCallee_miss_uninstantiable {tbl : OpaqueCalleeTable}
    {callerLayouts : LayoutTable} {defPath : DefPath} {typeArgs : List RigidTy}
    {extra : List TraitImplEntry} {c : CapturedMir} {eff : List RigidTy}
    (hres : resolveCalleeBodyAndArgs? tbl.toList defPath typeArgs extra = some (c, eff))
    (hpoly : (c.typeParamCount == 0 && eff.isEmpty) = false)
    (harity : eff.length = c.typeParamCount)
    (hlay : instantiationLayouts? callerLayouts eff = none) :
    tbl.lookup callerLayouts defPath typeArgs extra = none := by
  rw [OpaqueCalleeTable.lookup_eq]
  unfold lookupCallee
  simp only [hres, hpoly, harity, resolveLayouts_eq_instantiationLayouts, hlay]
  simp

/-- The `TraitImplEntry` match set consulted by the trusted resolver. -/
def traitMatches (tbl : OpaqueCalleeTable) (extra : List TraitImplEntry) (defPath : DefPath)
    (typeArgs : List RigidTy) : List (TraitImplEntry × Option (List RigidTy)) :=
  collectMatchingTraitImpls tbl.toList (extra ++ flatMapTraitImpls tbl.toList) defPath typeArgs

/-- Resolution certificate for a `TraitImplEntry` override: a unique most-specific
matching entry whose `implPath` is a captured callee with matching arity. -/
theorem resolve_trait_override {tbl : OpaqueCalleeTable} {defPath : DefPath}
    {firstArg : RigidTy} {restArgs : List RigidTy} {extra : List TraitImplEntry}
    {winner : TraitImplEntry} {implArgs : List RigidTy} {c : CapturedMir}
    (hfirst : rigidTyTag firstArg ≠ 0)
    (hwin : filterMostSpecificTraitImpls (traitMatches tbl extra defPath (firstArg :: restArgs))
      (traitMatches tbl extra defPath (firstArg :: restArgs)) = [(winner, some implArgs)])
    (himpl : tbl.lookupRaw winner.implPath = some c)
    (hoverride : winner.implPath ≠ defPath)
    (harity : implArgs.length = c.typeParamCount) :
    resolveCalleeBodyAndArgs? tbl.toList defPath (firstArg :: restArgs) extra =
      some (c, implArgs) := by
  rw [OpaqueCalleeTable.lookupRaw_eq] at himpl
  unfold traitMatches at hwin
  have hov : stringEq winner.implPath defPath = false := by
    cases hs : stringEq winner.implPath defPath
    · rfl
    · exact absurd (stringEq_eq_true_iff.mp hs) hoverride
  have hlen : (implArgs.length == c.typeParamCount) = true := by
    rw [harity]
    exact decide_eq_true rfl
  cases hm : collectMatchingTraitImpls tbl.toList (extra ++ flatMapTraitImpls tbl.toList)
      defPath (firstArg :: restArgs) with
  | nil => rw [hm] at hwin; simp [filterMostSpecificTraitImpls] at hwin
  | cons m ms =>
    rw [hm] at hwin
    cases firstArg <;> first
      | exact absurd rfl hfirst
      | simp only [resolveCalleeBodyAndArgs?, hm, hwin, himpl, hov, hlen, ite_true]

/-- **`O(1)` certificate (`TraitImplEntry` override hit)**: a monomorphic
override resolves to its `impl` body. -/
theorem lookupCallee_trait_hit {tbl : OpaqueCalleeTable} {callerLayouts : LayoutTable}
    {defPath : DefPath} {firstArg : RigidTy} {restArgs : List RigidTy}
    {extra : List TraitImplEntry} {winner : TraitImplEntry} {c : CapturedMir}
    (hfirst : rigidTyTag firstArg ≠ 0)
    (hwin : filterMostSpecificTraitImpls (traitMatches tbl extra defPath (firstArg :: restArgs))
      (traitMatches tbl extra defPath (firstArg :: restArgs)) = [(winner, some [])])
    (himpl : tbl.lookupRaw winner.implPath = some c)
    (hoverride : winner.implPath ≠ defPath)
    (hmono : c.typeParamCount = 0) :
    tbl.lookup callerLayouts defPath (firstArg :: restArgs) extra = some c := by
  have hres := resolve_trait_override hfirst hwin himpl hoverride (by rw [hmono]; rfl)
  rw [OpaqueCalleeTable.lookup_eq]
  unfold lookupCallee
  simp only [hres, hmono]
  rfl

/-- **`O(1)` certificate (polymorphic `TraitImplEntry` override hit)**: a generic
trait `impl` override resolves to `c.instantiate (implArgs.zip argLayouts)`. -/
theorem lookupCallee_trait_hit_poly {tbl : OpaqueCalleeTable} {callerLayouts : LayoutTable}
    {defPath : DefPath} {firstArg : RigidTy} {restArgs : List RigidTy}
    {extra : List TraitImplEntry} {winner : TraitImplEntry} {implArgs : List RigidTy}
    {c : CapturedMir} {argLayouts : List TypeLayout}
    (hfirst : rigidTyTag firstArg ≠ 0)
    (hwin : filterMostSpecificTraitImpls (traitMatches tbl extra defPath (firstArg :: restArgs))
      (traitMatches tbl extra defPath (firstArg :: restArgs)) = [(winner, some implArgs)])
    (himpl : tbl.lookupRaw winner.implPath = some c)
    (hoverride : winner.implPath ≠ defPath)
    (hpoly : (c.typeParamCount == 0 && implArgs.isEmpty) = false)
    (harity : implArgs.length = c.typeParamCount)
    (hlay : instantiationLayouts? callerLayouts implArgs = some argLayouts) :
    tbl.lookup callerLayouts defPath (firstArg :: restArgs) extra =
      some (c.instantiate (implArgs.zip argLayouts)) :=
  lookupCallee_hit (resolve_trait_override hfirst hwin himpl hoverride harity) hpoly harity hlay

/-- Resolution certificate for explicit default trait method inheritance
(`winner.implPath = defPath`, resolving the trait's default method body `c`
with the full call-site `firstArg :: restArgs`). -/
theorem resolve_trait_default {tbl : OpaqueCalleeTable} {defPath : DefPath}
    {firstArg : RigidTy} {restArgs : List RigidTy} {extra : List TraitImplEntry}
    {winner : TraitImplEntry} {implArgs : List RigidTy} {c : CapturedMir}
    (hfirst : rigidTyTag firstArg ≠ 0)
    (hwin : filterMostSpecificTraitImpls (traitMatches tbl extra defPath (firstArg :: restArgs))
      (traitMatches tbl extra defPath (firstArg :: restArgs)) = [(winner, some implArgs)])
    (hdefault : winner.implPath = defPath)
    (hbody : tbl.lookupRaw defPath = some c)
    (harity : (firstArg :: restArgs).length = c.typeParamCount) :
    resolveCalleeBodyAndArgs? tbl.toList defPath (firstArg :: restArgs) extra =
      some (c, firstArg :: restArgs) := by
  rw [OpaqueCalleeTable.lookupRaw_eq, ← hdefault] at hbody
  unfold traitMatches at hwin
  have hdef : stringEq winner.implPath defPath = true :=
    stringEq_eq_true_iff.mpr hdefault
  have hlen : ((firstArg :: restArgs).length == c.typeParamCount) = true := by
    rw [harity]
    exact decide_eq_true rfl
  cases hm : collectMatchingTraitImpls tbl.toList (extra ++ flatMapTraitImpls tbl.toList)
      defPath (firstArg :: restArgs) with
  | nil => rw [hm] at hwin; simp [filterMostSpecificTraitImpls] at hwin
  | cons m ms =>
    rw [hm] at hwin
    cases firstArg <;> first
      | exact absurd rfl hfirst
      | simp only [resolveCalleeBodyAndArgs?, hm, hwin, hbody, hdef, hlen, ite_true]

/-- **`O(1)` certificate (default trait method inheritance hit)**: when the
winning `TraitImplEntry` inherits the default trait method (`winner.implPath = defPath`),
lookup instantiates the trait's default method body `c` with `firstArg :: restArgs`. -/
theorem lookupCallee_trait_default_hit {tbl : OpaqueCalleeTable} {callerLayouts : LayoutTable}
    {defPath : DefPath} {firstArg : RigidTy} {restArgs : List RigidTy}
    {extra : List TraitImplEntry} {winner : TraitImplEntry} {implArgs : List RigidTy}
    {c : CapturedMir} {argLayouts : List TypeLayout}
    (hfirst : rigidTyTag firstArg ≠ 0)
    (hwin : filterMostSpecificTraitImpls (traitMatches tbl extra defPath (firstArg :: restArgs))
      (traitMatches tbl extra defPath (firstArg :: restArgs)) = [(winner, some implArgs)])
    (hdefault : winner.implPath = defPath)
    (hbody : tbl.lookupRaw defPath = some c)
    (harity : (firstArg :: restArgs).length = c.typeParamCount)
    (hlay : instantiationLayouts? callerLayouts (firstArg :: restArgs) = some argLayouts) :
    tbl.lookup callerLayouts defPath (firstArg :: restArgs) extra =
      some (c.instantiate ((firstArg :: restArgs).zip argLayouts)) :=
  lookupCallee_hit (resolve_trait_default hfirst hwin hdefault hbody harity)
    (by simp) harity hlay

/-- Resolution certificate for a direct polymorphic function or fallback default
trait method (`(traitMatches ...).isEmpty = true`, concrete `firstArg`). -/
theorem resolve_free_poly_or_default {tbl : OpaqueCalleeTable} {defPath : DefPath}
    {firstArg : RigidTy} {restArgs : List RigidTy} {extra : List TraitImplEntry}
    {c : CapturedMir}
    (hfirst : rigidTyTag firstArg ≠ 0)
    (hnoTrait : (traitMatches tbl extra defPath (firstArg :: restArgs)).isEmpty = true)
    (hraw : tbl.lookupRaw defPath = some c)
    (hconcrete : allParamsInCallerLayouts 0 firstArg = true) :
    resolveCalleeBodyAndArgs? tbl.toList defPath (firstArg :: restArgs) extra =
      some (c, firstArg :: restArgs) := by
  have hnil : traitMatches tbl extra defPath (firstArg :: restArgs) = [] :=
    List.isEmpty_iff.mp hnoTrait
  rw [OpaqueCalleeTable.lookupRaw_eq] at hraw
  unfold traitMatches at hnil
  cases firstArg <;> first
    | exact absurd rfl hfirst
    | simp only [resolveCalleeBodyAndArgs?, hnil, hraw, hconcrete, Bool.not_true, Bool.and_false]

/-- **`O(1)` certificate (direct polymorphic / fallback default-method hit)**
stated directly in terms of `tbl.lookupRaw` and `(traitMatches ...).isEmpty = true`. -/
theorem lookupCallee_hit_poly {tbl : OpaqueCalleeTable} {callerLayouts : LayoutTable}
    {defPath : DefPath} {firstArg : RigidTy} {restArgs : List RigidTy}
    {extra : List TraitImplEntry} {c : CapturedMir} {argLayouts : List TypeLayout}
    (hfirst : rigidTyTag firstArg ≠ 0)
    (hnoTrait : (traitMatches tbl extra defPath (firstArg :: restArgs)).isEmpty = true)
    (hraw : tbl.lookupRaw defPath = some c)
    (hconcrete : allParamsInCallerLayouts 0 firstArg = true)
    (harity : (firstArg :: restArgs).length = c.typeParamCount)
    (hlay : instantiationLayouts? callerLayouts (firstArg :: restArgs) = some argLayouts) :
    tbl.lookup callerLayouts defPath (firstArg :: restArgs) extra =
      some (c.instantiate ((firstArg :: restArgs).zip argLayouts)) :=
  lookupCallee_hit (resolve_free_poly_or_default hfirst hnoTrait hraw hconcrete)
    (by simp) harity hlay

/-- With no registered `TraitImplEntry` for `defPath`, the trusted
`collectMatchingTraitImpls` scan returns its accumulator unchanged. -/
theorem collectMatchingTraitImpls_of_no_impl (callees : List CapturedMir) (defPath : DefPath)
    (typeArgs : List RigidTy) :
    ∀ (impls : List TraitImplEntry) (acc : List (TraitImplEntry × Option (List RigidTy))),
      hasTraitImplForDefPath impls defPath = false →
        collectMatchingTraitImpls callees impls defPath typeArgs acc = acc
  | [], _, _ => rfl
  | e :: rest, acc, h => by
    have he : stringEq e.traitRef.defPath defPath = false := by
      cases hs : stringEq e.traitRef.defPath defPath
      · rfl
      · simp [hasTraitImplForDefPath, hs] at h
    have hrest : hasTraitImplForDefPath rest defPath = false := by
      simp only [hasTraitImplForDefPath, he] at h
      exact h
    simp only [collectMatchingTraitImpls, he, Bool.false_eq_true, ite_false]
    exact collectMatchingTraitImpls_of_no_impl callees defPath typeArgs rest acc hrest

/-- Resolution certificate for a *free* generic function: no registered
`TraitImplEntry` targets `defPath`, so every non-empty `typeArgs` (concrete or
still-generic `.param` first argument) resolves to the captured body. -/
theorem resolve_free_poly {tbl : OpaqueCalleeTable} {defPath : DefPath}
    {firstArg : RigidTy} {restArgs : List RigidTy} {extra : List TraitImplEntry}
    {c : CapturedMir}
    (hnoImpl : hasTraitImplForDefPath (extra ++ flatMapTraitImpls tbl.toList) defPath = false)
    (hraw : tbl.lookupRaw defPath = some c) :
    resolveCalleeBodyAndArgs? tbl.toList defPath (firstArg :: restArgs) extra =
      some (c, firstArg :: restArgs) := by
  rw [OpaqueCalleeTable.lookupRaw_eq] at hraw
  have hnil : collectMatchingTraitImpls tbl.toList (extra ++ flatMapTraitImpls tbl.toList)
      defPath (firstArg :: restArgs) = [] :=
    collectMatchingTraitImpls_of_no_impl _ _ _ _ [] hnoImpl
  cases firstArg <;>
    simp only [resolveCalleeBodyAndArgs?, hnil, hraw, hnoImpl, Bool.false_and]

/-- **`O(1)` certificate (free generic function)**: one per-`defPath` certificate
(`hnoImpl`, independent of the call-site `typeArgs`) plus the raw `lookupRaw`
certificate rewrite *every* instantiation `defPath::<firstArg, restArgs…>` —
including still-generic callers (`.param` first argument), which
`lookupCallee_hit_poly` excludes — to the instantiated body. -/
theorem lookupCallee_hit_free_poly {tbl : OpaqueCalleeTable} {callerLayouts : LayoutTable}
    {defPath : DefPath} {firstArg : RigidTy} {restArgs : List RigidTy}
    {extra : List TraitImplEntry} {c : CapturedMir} {argLayouts : List TypeLayout}
    (hnoImpl : hasTraitImplForDefPath (extra ++ flatMapTraitImpls tbl.toList) defPath = false)
    (hraw : tbl.lookupRaw defPath = some c)
    (harity : (firstArg :: restArgs).length = c.typeParamCount)
    (hlay : instantiationLayouts? callerLayouts (firstArg :: restArgs) = some argLayouts) :
    tbl.lookup callerLayouts defPath (firstArg :: restArgs) extra =
      some (c.instantiate ((firstArg :: restArgs).zip argLayouts)) :=
  lookupCallee_hit (resolve_free_poly hnoImpl hraw) (by simp) harity hlay

/-- **`O(1)` certificate (free generic function, `tbl.toList`-free)**: uses the
sealed `tbl.traitImpls` projection (rewritten once per table by `htraits`) instead
of unfolding `flatMapTraitImpls tbl.toList` across all `M` callees. -/
theorem lookupCallee_hit_free_poly_opaque {tbl : OpaqueCalleeTable} {callerLayouts : LayoutTable}
    {defPath : DefPath} {firstArg : RigidTy} {restArgs : List RigidTy}
    {extra impls : List TraitImplEntry} {c : CapturedMir} {argLayouts : List TypeLayout}
    (htraits : tbl.traitImpls = impls)
    (hnoImpl : hasTraitImplForDefPath (extra ++ impls) defPath = false)
    (hraw : tbl.lookupRaw defPath = some c)
    (harity : (firstArg :: restArgs).length = c.typeParamCount)
    (hlay : instantiationLayouts? callerLayouts (firstArg :: restArgs) = some argLayouts) :
    tbl.lookup callerLayouts defPath (firstArg :: restArgs) extra =
      some (c.instantiate ((firstArg :: restArgs).zip argLayouts)) := by
  rw [← htraits, OpaqueCalleeTable.traitImpls_eq] at hnoImpl
  exact lookupCallee_hit_free_poly hnoImpl hraw harity hlay

/-- Resolver-parametric companion of `collectMatchingTraitImpls`: replaces the
linear `findCallee? callees entry.implPath` scan with an opaque raw lookup
`lookupRaw : DefPath → Option CapturedMir` (`tbl.lookupRaw`), which is only
invoked on entries whose `(traitRef.defPath, traitRef.args)` header actually
matches `(defPath, typeArgs)`. -/
def collectMatchingTraitImplsWith (lookupRaw : DefPath → Option CapturedMir)
    (traitImpls : List TraitImplEntry) (defPath : DefPath) (typeArgs : List RigidTy)
    (acc : List (TraitImplEntry × Option (List RigidTy)) := []) :
    List (TraitImplEntry × Option (List RigidTy)) :=
  match traitImpls with
  | [] => acc
  | entry :: rest =>
    if stringEq entry.traitRef.defPath defPath then
      match entry.traitRef.args with
      | [] => collectMatchingTraitImplsWith lookupRaw rest defPath typeArgs acc
      | _ :: _ =>
        match matchRigidTyPrefix entry.traitRef.args typeArgs [] with
        | none => collectMatchingTraitImplsWith lookupRaw rest defPath typeArgs acc
        | some (subst, methodTypeArgs) =>
          let rawImplTypeArgsOpt :=
            match extractImplTypeArgs subst subst.length with
            | some implHeaderArgs => some (implHeaderArgs ++ methodTypeArgs)
            | none => none
          let implTypeArgsOpt :=
            match rawImplTypeArgsOpt, lookupRaw entry.implPath with
            | some rawArgs, some c =>
              let effectiveTypeArgs :=
                match stringEq entry.implPath defPath with
                | true => typeArgs
                | false => rawArgs
              if effectiveTypeArgs.length == c.typeParamCount then
                some effectiveTypeArgs
              else
                none
            | _, _ => none
          collectMatchingTraitImplsWith lookupRaw rest defPath typeArgs
            (upsertMatchingTraitImpl entry implTypeArgsOpt acc)
    else
      collectMatchingTraitImplsWith lookupRaw rest defPath typeArgs acc

/-- `collectMatchingTraitImpls tbl.toList` equals `collectMatchingTraitImplsWith tbl.lookupRaw`. -/
theorem collectMatchingTraitImpls_eq_with (tbl : OpaqueCalleeTable)
    (defPath : DefPath) (typeArgs : List RigidTy) :
    ∀ (impls : List TraitImplEntry) (acc : List (TraitImplEntry × Option (List RigidTy))),
      collectMatchingTraitImpls tbl.toList impls defPath typeArgs acc =
        collectMatchingTraitImplsWith tbl.lookupRaw impls defPath typeArgs acc
  | [], _ => rfl
  | entry :: rest, acc => by
    unfold collectMatchingTraitImpls collectMatchingTraitImplsWith
    rw [OpaqueCalleeTable.lookupRaw_eq]
    by_cases hd : stringEq entry.traitRef.defPath defPath = true
    · simp only [hd, ite_true]
      cases entry.traitRef.args with
      | nil => exact collectMatchingTraitImpls_eq_with tbl defPath typeArgs rest acc
      | cons a as =>
        dsimp only
        cases matchRigidTyPrefix (a :: as) typeArgs [] with
        | none => exact collectMatchingTraitImpls_eq_with tbl defPath typeArgs rest acc
        | some p =>
          exact collectMatchingTraitImpls_eq_with tbl defPath typeArgs rest _
    · simp only [hd, Bool.false_eq_true, ite_false]
      exact collectMatchingTraitImpls_eq_with tbl defPath typeArgs rest acc

/-- Opaque-table trait match collector: uses `tbl.traitImpls` and `tbl.lookupRaw`,
never mentioning `tbl.toList`. -/
def traitMatchesOpaque (tbl : OpaqueCalleeTable) (extra : List TraitImplEntry)
    (defPath : DefPath) (typeArgs : List RigidTy) :
    List (TraitImplEntry × Option (List RigidTy)) :=
  collectMatchingTraitImplsWith tbl.lookupRaw (extra ++ tbl.traitImpls) defPath typeArgs []

theorem traitMatches_eq_opaque (tbl : OpaqueCalleeTable) (extra : List TraitImplEntry)
    (defPath : DefPath) (typeArgs : List RigidTy) :
    traitMatches tbl extra defPath typeArgs = traitMatchesOpaque tbl extra defPath typeArgs := by
  unfold traitMatches traitMatchesOpaque
  rw [← OpaqueCalleeTable.traitImpls_eq, collectMatchingTraitImpls_eq_with]

/-- A `TraitImplEntry` for a different trait method is skipped without calling `lookupRaw`. -/
theorem collectMatchingTraitImplsWith_cons_ne_path
    {lookupRaw : DefPath → Option CapturedMir} {entry : TraitImplEntry}
    {rest : List TraitImplEntry} {defPath : DefPath} {typeArgs : List RigidTy}
    {acc : List (TraitImplEntry × Option (List RigidTy))}
    (hne : stringEq entry.traitRef.defPath defPath = false) :
    collectMatchingTraitImplsWith lookupRaw (entry :: rest) defPath typeArgs acc =
      collectMatchingTraitImplsWith lookupRaw rest defPath typeArgs acc := by
  rw [collectMatchingTraitImplsWith]
  simp only [hne, Bool.false_eq_true, ite_false]

/-- A `TraitImplEntry` whose `traitRef.args` does not match `typeArgs` is skipped
without calling `lookupRaw`. -/
theorem collectMatchingTraitImplsWith_cons_ne_args
    {lookupRaw : DefPath → Option CapturedMir} {entry : TraitImplEntry}
    {rest : List TraitImplEntry} {defPath : DefPath} {typeArgs : List RigidTy}
    {acc : List (TraitImplEntry × Option (List RigidTy))}
    (hpath : stringEq entry.traitRef.defPath defPath = true)
    (hargs : (match entry.traitRef.args with
      | [] => true
      | _ :: _ => (matchRigidTyPrefix entry.traitRef.args typeArgs []).isNone) = true) :
    collectMatchingTraitImplsWith lookupRaw (entry :: rest) defPath typeArgs acc =
      collectMatchingTraitImplsWith lookupRaw rest defPath typeArgs acc := by
  rw [collectMatchingTraitImplsWith]
  simp only [hpath, ite_true]
  cases htr : entry.traitRef.args with
  | nil => rfl
  | cons a as =>
    rw [htr] at hargs
    cases hm : matchRigidTyPrefix (a :: as) typeArgs [] with
    | none => rfl
    | some _ => rw [hm] at hargs; nomatch hargs

/-- A matching monomorphic `TraitImplEntry` override rewrites its body lookup in `O(1)`
via its `lookupRaw` certificate (`himpl : lookupRaw entry.implPath = some c`). -/
theorem collectMatchingTraitImplsWith_cons_hit_mono
    {lookupRaw : DefPath → Option CapturedMir} {entry : TraitImplEntry}
    {rest : List TraitImplEntry} {defPath : DefPath} {typeArgs : List RigidTy}
    {acc : List (TraitImplEntry × Option (List RigidTy))}
    {a : RigidTy} {as : List RigidTy} {c : CapturedMir}
    (hpath : stringEq entry.traitRef.defPath defPath = true)
    (htr : entry.traitRef.args = a :: as)
    (hmatch : matchRigidTyPrefix (a :: as) typeArgs [] = some ([], []))
    (himpl : lookupRaw entry.implPath = some c)
    (hov : stringEq entry.implPath defPath = false)
    (hmono : c.typeParamCount = 0) :
    collectMatchingTraitImplsWith lookupRaw (entry :: rest) defPath typeArgs acc =
      collectMatchingTraitImplsWith lookupRaw rest defPath typeArgs
        (upsertMatchingTraitImpl entry (some []) acc) := by
  have hex : extractImplTypeArgs [] 0 = some [] := rfl
  rw [collectMatchingTraitImplsWith]
  simp only [hpath, ite_true, htr, hmatch, himpl, hov, List.length_nil, List.append_nil]
  rw [hex]
  simp only [List.length_nil, hmono]
  rfl

/-- **`O(1)` certificate (monomorphic `TraitImplEntry` override hit, `tbl.toList`-free)**:
given a per-table `tbl.traitImpls = impls` certificate and `winner`'s `lookupRaw`
certificate, resolves a trait method call without ever unfolding `tbl.toList`. -/
theorem lookupCallee_trait_hit_cert {tbl : OpaqueCalleeTable} {callerLayouts : LayoutTable}
    {defPath : DefPath} {firstArg : RigidTy} {restArgs : List RigidTy}
    {extra impls : List TraitImplEntry} {winner : TraitImplEntry}
    {matches_ : List (TraitImplEntry × Option (List RigidTy))} {c : CapturedMir}
    (hfirst : rigidTyTag firstArg ≠ 0)
    (htraits : tbl.traitImpls = impls)
    (hcollect : collectMatchingTraitImplsWith tbl.lookupRaw (extra ++ impls)
      defPath (firstArg :: restArgs) [] = matches_)
    (hwin : filterMostSpecificTraitImpls matches_ matches_ = [(winner, some [])])
    (himpl : tbl.lookupRaw winner.implPath = some c)
    (hoverride : winner.implPath ≠ defPath)
    (hmono : c.typeParamCount = 0) :
    tbl.lookup callerLayouts defPath (firstArg :: restArgs) extra = some c := by
  apply lookupCallee_trait_hit hfirst ?_ himpl hoverride hmono
  rw [traitMatches_eq_opaque]
  unfold traitMatchesOpaque
  rw [htraits, hcollect]
  exact hwin

/-- A matching polymorphic `TraitImplEntry` override rewrites its body lookup in `O(1)`
via its `lookupRaw` certificate (`himpl : lookupRaw entry.implPath = some c`). -/
theorem collectMatchingTraitImplsWith_cons_hit_poly
    {lookupRaw : DefPath → Option CapturedMir} {entry : TraitImplEntry}
    {rest : List TraitImplEntry} {defPath : DefPath} {typeArgs : List RigidTy}
    {acc : List (TraitImplEntry × Option (List RigidTy))}
    {a : RigidTy} {as : List RigidTy} {subst : List (Nat × RigidTy)}
    {methodTypeArgs implHeaderArgs : List RigidTy} {c : CapturedMir}
    (hpath : stringEq entry.traitRef.defPath defPath = true)
    (htr : entry.traitRef.args = a :: as)
    (hmatch : matchRigidTyPrefix (a :: as) typeArgs [] = some (subst, methodTypeArgs))
    (hex : extractImplTypeArgs subst subst.length = some implHeaderArgs)
    (himpl : lookupRaw entry.implPath = some c)
    (hov : stringEq entry.implPath defPath = false)
    (harity : ((implHeaderArgs ++ methodTypeArgs).length == c.typeParamCount) = true) :
    collectMatchingTraitImplsWith lookupRaw (entry :: rest) defPath typeArgs acc =
      collectMatchingTraitImplsWith lookupRaw rest defPath typeArgs
        (upsertMatchingTraitImpl entry (some (implHeaderArgs ++ methodTypeArgs)) acc) := by
  rw [collectMatchingTraitImplsWith]
  simp only [hpath, ite_true, htr, hmatch, hex, himpl, hov, harity]

/-- A matching default-method `TraitImplEntry` (`stringEq entry.implPath defPath = true`)
rewrites its body lookup in `O(1)` via the default method's `lookupRaw` certificate. -/
theorem collectMatchingTraitImplsWith_cons_hit_default
    {lookupRaw : DefPath → Option CapturedMir} {entry : TraitImplEntry}
    {rest : List TraitImplEntry} {defPath : DefPath} {typeArgs : List RigidTy}
    {acc : List (TraitImplEntry × Option (List RigidTy))}
    {a : RigidTy} {as : List RigidTy} {subst : List (Nat × RigidTy)}
    {methodTypeArgs implHeaderArgs : List RigidTy} {c : CapturedMir}
    (hpath : stringEq entry.traitRef.defPath defPath = true)
    (htr : entry.traitRef.args = a :: as)
    (hmatch : matchRigidTyPrefix (a :: as) typeArgs [] = some (subst, methodTypeArgs))
    (hex : extractImplTypeArgs subst subst.length = some implHeaderArgs)
    (himpl : lookupRaw entry.implPath = some c)
    (hdef : stringEq entry.implPath defPath = true)
    (harity : (typeArgs.length == c.typeParamCount) = true) :
    collectMatchingTraitImplsWith lookupRaw (entry :: rest) defPath typeArgs acc =
      collectMatchingTraitImplsWith lookupRaw rest defPath typeArgs
        (upsertMatchingTraitImpl entry (some typeArgs) acc) := by
  rw [collectMatchingTraitImplsWith]
  simp only [hpath, ite_true, htr, hmatch, hex, himpl, hdef, harity]

/-- **`O(1)` certificate (polymorphic `TraitImplEntry` override hit, `tbl.toList`-free)**:
given a per-table `tbl.traitImpls = impls` certificate and `winner`'s `lookupRaw`
certificate, resolves a polymorphic trait override without ever unfolding `tbl.toList`. -/
theorem lookupCallee_trait_hit_poly_cert {tbl : OpaqueCalleeTable} {callerLayouts : LayoutTable}
    {defPath : DefPath} {firstArg : RigidTy} {restArgs : List RigidTy}
    {extra impls : List TraitImplEntry} {winner : TraitImplEntry} {implArgs : List RigidTy}
    {matches_ : List (TraitImplEntry × Option (List RigidTy))} {c : CapturedMir}
    {argLayouts : List TypeLayout}
    (hfirst : rigidTyTag firstArg ≠ 0)
    (htraits : tbl.traitImpls = impls)
    (hcollect : collectMatchingTraitImplsWith tbl.lookupRaw (extra ++ impls)
      defPath (firstArg :: restArgs) [] = matches_)
    (hwin : filterMostSpecificTraitImpls matches_ matches_ = [(winner, some implArgs)])
    (himpl : tbl.lookupRaw winner.implPath = some c)
    (hoverride : winner.implPath ≠ defPath)
    (hpoly : (c.typeParamCount == 0 && implArgs.isEmpty) = false)
    (harity : implArgs.length = c.typeParamCount)
    (hlay : instantiationLayouts? callerLayouts implArgs = some argLayouts) :
    tbl.lookup callerLayouts defPath (firstArg :: restArgs) extra =
      some (c.instantiate (implArgs.zip argLayouts)) := by
  apply lookupCallee_trait_hit_poly hfirst ?_ himpl hoverride hpoly harity hlay
  rw [traitMatches_eq_opaque]
  unfold traitMatchesOpaque
  rw [htraits, hcollect]
  exact hwin

/-- **`O(1)` certificate (default trait method inheritance hit, `tbl.toList`-free)**:
given a per-table `tbl.traitImpls = impls` certificate and the default method's
`lookupRaw` certificate, resolves default trait method inheritance without ever
unfolding `tbl.toList`. -/
theorem lookupCallee_trait_default_hit_cert {tbl : OpaqueCalleeTable} {callerLayouts : LayoutTable}
    {defPath : DefPath} {firstArg : RigidTy} {restArgs : List RigidTy}
    {extra impls : List TraitImplEntry} {winner : TraitImplEntry} {implArgs : List RigidTy}
    {matches_ : List (TraitImplEntry × Option (List RigidTy))} {c : CapturedMir}
    {argLayouts : List TypeLayout}
    (hfirst : rigidTyTag firstArg ≠ 0)
    (htraits : tbl.traitImpls = impls)
    (hcollect : collectMatchingTraitImplsWith tbl.lookupRaw (extra ++ impls)
      defPath (firstArg :: restArgs) [] = matches_)
    (hwin : filterMostSpecificTraitImpls matches_ matches_ = [(winner, some implArgs)])
    (hdefault : winner.implPath = defPath)
    (hbody : tbl.lookupRaw defPath = some c)
    (harity : (firstArg :: restArgs).length = c.typeParamCount)
    (hlay : instantiationLayouts? callerLayouts (firstArg :: restArgs) = some argLayouts) :
    tbl.lookup callerLayouts defPath (firstArg :: restArgs) extra =
      some (c.instantiate ((firstArg :: restArgs).zip argLayouts)) := by
  apply lookupCallee_trait_default_hit (implArgs := implArgs) hfirst ?_ hdefault hbody harity hlay
  rw [traitMatches_eq_opaque]
  unfold traitMatchesOpaque
  rw [htraits, hcollect]
  exact hwin

/-- **`O(1)` key certificate (miss)**: the `CalleeKey` form of `lookupCallee_miss_direct`. -/
theorem lookupKey_miss_direct {tbl : OpaqueCalleeTable} {k : CalleeKey}
    (hraw : tbl.lookupRaw k.defPath = none) (hk : k.typeArgs = []) :
    tbl.lookupKey k = none := by
  obtain ⟨L, dp, tys, ti⟩ := k
  simp only at hraw hk
  subst hk
  rw [OpaqueCalleeTable.lookupKey_eq]
  exact lookupCallee_miss_direct hraw

/-- **`O(1)` key certificate (direct polymorphic / fallback default-method hit)**:
the `CalleeKey` form of `lookupCallee_hit_poly`. -/
theorem lookupKey_hit_poly {tbl : OpaqueCalleeTable} {k : CalleeKey}
    {firstArg : RigidTy} {restArgs : List RigidTy} {c : CapturedMir}
    {argLayouts : List TypeLayout}
    (hk : k.typeArgs = firstArg :: restArgs)
    (hfirst : rigidTyTag firstArg ≠ 0)
    (hnoTrait : (traitMatches tbl k.extraTraitImpls k.defPath (firstArg :: restArgs)).isEmpty = true)
    (hraw : tbl.lookupRaw k.defPath = some c)
    (hconcrete : allParamsInCallerLayouts 0 firstArg = true)
    (harity : (firstArg :: restArgs).length = c.typeParamCount)
    (hlay : instantiationLayouts? k.callerLayouts (firstArg :: restArgs) = some argLayouts) :
    tbl.lookupKey k = some (c.instantiate ((firstArg :: restArgs).zip argLayouts)) := by
  obtain ⟨L, dp, tys, ti⟩ := k
  simp only at hk hnoTrait hraw hlay
  subst hk
  rw [OpaqueCalleeTable.lookupKey_eq]
  exact lookupCallee_hit_poly hfirst hnoTrait hraw hconcrete harity hlay

/-- **`O(1)` key certificate (free generic function)**: the `CalleeKey` form of
`lookupCallee_hit_free_poly`. -/
theorem lookupKey_hit_free_poly {tbl : OpaqueCalleeTable} {k : CalleeKey}
    {firstArg : RigidTy} {restArgs : List RigidTy} {c : CapturedMir}
    {argLayouts : List TypeLayout}
    (hk : k.typeArgs = firstArg :: restArgs)
    (hnoImpl : hasTraitImplForDefPath (k.extraTraitImpls ++ flatMapTraitImpls tbl.toList)
      k.defPath = false)
    (hraw : tbl.lookupRaw k.defPath = some c)
    (harity : (firstArg :: restArgs).length = c.typeParamCount)
    (hlay : instantiationLayouts? k.callerLayouts (firstArg :: restArgs) = some argLayouts) :
    tbl.lookupKey k = some (c.instantiate ((firstArg :: restArgs).zip argLayouts)) := by
  obtain ⟨L, dp, tys, ti⟩ := k
  simp only at hk hnoImpl hraw hlay
  subst hk
  rw [OpaqueCalleeTable.lookupKey_eq]
  exact lookupCallee_hit_free_poly hnoImpl hraw harity hlay

/-- **`O(1)` key certificate (free generic function, `tbl.toList`-free)**: the `CalleeKey`
form of `lookupCallee_hit_free_poly_opaque`, rewriting `tbl.lookupKey k` without unfolding
`tbl.toList` in either the elaborator or the kernel. -/
theorem lookupKey_hit_free_poly_opaque {tbl : OpaqueCalleeTable} {k : CalleeKey}
    {firstArg : RigidTy} {restArgs : List RigidTy} {impls : List TraitImplEntry}
    {c : CapturedMir} {argLayouts : List TypeLayout}
    (hk : k.typeArgs = firstArg :: restArgs)
    (htraits : tbl.traitImpls = impls)
    (hnoImpl : hasTraitImplForDefPath (k.extraTraitImpls ++ impls) k.defPath = false)
    (hraw : tbl.lookupRaw k.defPath = some c)
    (harity : (firstArg :: restArgs).length = c.typeParamCount)
    (hlay : instantiationLayouts? k.callerLayouts (firstArg :: restArgs) = some argLayouts) :
    tbl.lookupKey k = some (c.instantiate ((firstArg :: restArgs).zip argLayouts)) := by
  obtain ⟨L, dp, tys, ti⟩ := k
  simp only at hk hnoImpl hraw hlay
  subst hk
  rw [OpaqueCalleeTable.lookupKey_eq]
  exact lookupCallee_hit_free_poly_opaque htraits hnoImpl hraw harity hlay

/-- **`O(1)` key certificate (monomorphic `TraitImplEntry` override hit, `tbl.toList`-free)**:
the `CalleeKey` form of `lookupCallee_trait_hit_cert`. -/
theorem lookupKey_trait_hit_cert {tbl : OpaqueCalleeTable} {k : CalleeKey}
    {firstArg : RigidTy} {restArgs : List RigidTy} {impls : List TraitImplEntry}
    {winner : TraitImplEntry} {matches_ : List (TraitImplEntry × Option (List RigidTy))}
    {c : CapturedMir}
    (hk : k.typeArgs = firstArg :: restArgs)
    (hfirst : rigidTyTag firstArg ≠ 0)
    (htraits : tbl.traitImpls = impls)
    (hcollect : collectMatchingTraitImplsWith tbl.lookupRaw (k.extraTraitImpls ++ impls)
      k.defPath (firstArg :: restArgs) [] = matches_)
    (hwin : filterMostSpecificTraitImpls matches_ matches_ = [(winner, some [])])
    (himpl : tbl.lookupRaw winner.implPath = some c)
    (hoverride : winner.implPath ≠ k.defPath)
    (hmono : c.typeParamCount = 0) :
    tbl.lookupKey k = some c := by
  obtain ⟨L, dp, tys, ti⟩ := k
  simp only at hk hcollect hoverride
  subst hk
  rw [OpaqueCalleeTable.lookupKey_eq]
  exact lookupCallee_trait_hit_cert hfirst htraits hcollect hwin himpl hoverride hmono

/-- **`O(1)` key certificate (polymorphic `TraitImplEntry` override hit, `tbl.toList`-free)**:
the `CalleeKey` form of `lookupCallee_trait_hit_poly_cert`. -/
theorem lookupKey_trait_hit_poly_cert {tbl : OpaqueCalleeTable} {k : CalleeKey}
    {firstArg : RigidTy} {restArgs : List RigidTy} {impls : List TraitImplEntry}
    {winner : TraitImplEntry} {implArgs : List RigidTy}
    {matches_ : List (TraitImplEntry × Option (List RigidTy))} {c : CapturedMir}
    {argLayouts : List TypeLayout}
    (hk : k.typeArgs = firstArg :: restArgs)
    (hfirst : rigidTyTag firstArg ≠ 0)
    (htraits : tbl.traitImpls = impls)
    (hcollect : collectMatchingTraitImplsWith tbl.lookupRaw (k.extraTraitImpls ++ impls)
      k.defPath (firstArg :: restArgs) [] = matches_)
    (hwin : filterMostSpecificTraitImpls matches_ matches_ = [(winner, some implArgs)])
    (himpl : tbl.lookupRaw winner.implPath = some c)
    (hoverride : winner.implPath ≠ k.defPath)
    (hpoly : (c.typeParamCount == 0 && implArgs.isEmpty) = false)
    (harity : implArgs.length = c.typeParamCount)
    (hlay : instantiationLayouts? k.callerLayouts implArgs = some argLayouts) :
    tbl.lookupKey k = some (c.instantiate (implArgs.zip argLayouts)) := by
  obtain ⟨L, dp, tys, ti⟩ := k
  simp only at hk hcollect hoverride hlay
  subst hk
  rw [OpaqueCalleeTable.lookupKey_eq]
  exact lookupCallee_trait_hit_poly_cert hfirst htraits hcollect hwin himpl hoverride
    hpoly harity hlay

/-- **`O(1)` key certificate (default trait method inheritance hit, `tbl.toList`-free)**:
the `CalleeKey` form of `lookupCallee_trait_default_hit_cert`. -/
theorem lookupKey_trait_default_hit_cert {tbl : OpaqueCalleeTable} {k : CalleeKey}
    {firstArg : RigidTy} {restArgs : List RigidTy} {impls : List TraitImplEntry}
    {winner : TraitImplEntry} {implArgs : List RigidTy}
    {matches_ : List (TraitImplEntry × Option (List RigidTy))} {c : CapturedMir}
    {argLayouts : List TypeLayout}
    (hk : k.typeArgs = firstArg :: restArgs)
    (hfirst : rigidTyTag firstArg ≠ 0)
    (htraits : tbl.traitImpls = impls)
    (hcollect : collectMatchingTraitImplsWith tbl.lookupRaw (k.extraTraitImpls ++ impls)
      k.defPath (firstArg :: restArgs) [] = matches_)
    (hwin : filterMostSpecificTraitImpls matches_ matches_ = [(winner, some implArgs)])
    (hdefault : winner.implPath = k.defPath)
    (hbody : tbl.lookupRaw k.defPath = some c)
    (harity : (firstArg :: restArgs).length = c.typeParamCount)
    (hlay : instantiationLayouts? k.callerLayouts (firstArg :: restArgs) = some argLayouts) :
    tbl.lookupKey k = some (c.instantiate ((firstArg :: restArgs).zip argLayouts)) := by
  obtain ⟨L, dp, tys, ti⟩ := k
  simp only at hk hcollect hdefault hbody hlay
  subst hk
  rw [OpaqueCalleeTable.lookupKey_eq]
  exact lookupCallee_trait_default_hit_cert hfirst htraits hcollect hwin hdefault hbody
    harity hlay

/-! ### Literal-discriminant branch pruning over the real trusted step -/

/-- Literal scalar `switchInt` discriminant (`ConstValue.scalar (.int si)`): covers
literal `bool` (`if true` / `if false`, `bits ∈ {0, 1}`) and literal integer
`match` scrutinees. -/
def literalDiscrBits? : Operand → Option Nat
  | .constant c =>
    match c.val with
    | .scalar (.int si) => some si.bits
    | _ => none
  | _ => none

/-- Literal `bool` recognizer (a special case of `literalDiscrBits?`). -/
def literalBool? : Operand → Option Bool
  | .constant { ty := { kind := .bool, .. }, val := .scalar (.int si) } =>
    if si.bits = 0 then some false else if si.bits = 1 then some true else none
  | _ => none

/-- A literal `bool` is a literal discriminant with bit `0` / `1`. -/
theorem literalDiscrBits_of_literalBool {op : Operand} {b : Bool}
    (h : literalBool? op = some b) : literalDiscrBits? op = some (if b then 1 else 0) := by
  match op, h with
  | .constant { ty := { kind := .bool, .. }, val := .scalar (.int si) }, h =>
    simp only [literalBool?] at h
    simp only [literalDiscrBits?]
    by_cases h0 : si.bits = 0
    · simp [h0] at h; subst h; simp [h0]
    · by_cases h1 : si.bits = 1
      · simp [h1] at h; subst h; simp [h1]
      · simp [h0, h1] at h

/-- Resolver-parametric copy of the trusted `evalTailCallTerminator`
(`resolve` replaces `lookupCallee s.memory.callees`). -/
def tailCallWith (resolve : CalleeResolver) (s : MachineState) (func : Operand) (argOps : List Operand)
    (currentBody : Option CapturedMir) : MirStepNode :=
  let bodyLocalDecls := bodyLocalDeclsOf currentBody
  let bodyLayouts : LayoutTable :=
    match currentBody with
    | .some b => b.layouts
    | .none => emptyLayoutTable
  match
    resolveCallTarget
      s
      func
      (length argOps)
      bodyLocalDecls
      bodyLayouts
  with
  | .ub => MirStepNode.fail .ub
  | .unsupported => MirStepNode.unsupported
  | .ok target localsAfterFunc =>
    match
      evalOperands
        localsAfterFunc
        argOps
        s.memory.borrows
        s.memory.globals
        bodyLayouts
        s.memory.callerLocals
        (callStack := s.memory.callStack)
    with
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
    | .ok argVals _ =>
      let depth := length s.memory.callStack
      let nLocals := length s.frame.locals
      match
        hasFrameDeallocProtectorConflict
          s.memory.borrows
          s.memory.activeProtectors
          depth
          nLocals
      with
      | true => MirStepNode.fail .ub
      | false =>
        let memAfterTeardown : Memory :=
          { s.memory with borrows := disableFrameBorrows s.memory.borrows depth nLocals }
        match resolve bodyLayouts target.defPath target.typeArgs s.memory.traitImpls with
        | .some calleeBody =>
          match checkCalleeTargetCompatible target calleeBody (length argVals) with
          | false => MirStepNode.fail .ub
          | true =>
            MirStepNode.step (enterTailCalleeFrame memAfterTeardown calleeBody argVals)
        | .none =>
          MirStepNode.extCall
            { defPath := target.defPath, typeArgs := target.typeArgs, args := argVals,
              memory := memAfterTeardown }
            resumeExternalTailCall

/-- Resolver-parametric copy of the trusted `evalTerminator`: the `.call` and
`.tailCall` arms are the trusted arms verbatim with `resolve` in place of
`lookupCallee s.memory.callees`; when `prune = true`, a `switchInt` on a literal
discriminant jumps straight to its taken target without evaluating the operand
(the dead arm, and every callee it mentions, drops out syntactically); all other
terminators delegate to the trusted `evalTerminator`. -/
def stepTerminatorWith (prune : Bool) (resolve : CalleeResolver) (s : MachineState)
    (term : Terminator) (currentBody : Option CapturedMir) : MirStepNode :=
  match term.kind with
  | .switchInt discr targets =>
    match prune, literalDiscrBits? discr with
    | true, some bits =>
      MirStepNode.emitStep (.event bits) {
        s with
        frame := {
          blockIdx := lookupSwitchTarget bits targets.branches targets.otherwise
          stmtIdx := 0
          locals := s.frame.locals }
      }
    | _, _ => evalTerminator s term currentBody
  | .call func argOps destination (.some targetBb) unwind =>
    let bodyLocalDecls := bodyLocalDeclsOf currentBody
    let bodyLayouts : LayoutTable :=
      match currentBody with
      | .some b => b.layouts
      | .none => emptyLayoutTable
    match
      resolveCallTarget
        s
        func
        (length argOps)
        bodyLocalDecls
        bodyLayouts
    with
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
    | .ok target localsAfterFunc =>
      match
        evalOperands
          localsAfterFunc
          argOps
          s.memory.borrows
          s.memory.globals
          bodyLayouts
          s.memory.callerLocals
          (callStack := s.memory.callStack)
      with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok argVals locals' =>
        match resolve bodyLayouts target.defPath target.typeArgs s.memory.traitImpls with
        | .some calleeBody =>
          match checkCalleeTargetCompatible target calleeBody (length argVals) with
          | false => MirStepNode.fail .ub
          | true =>
            match currentBody with
            | .none => MirStepNode.unsupported
            | .some callerBody =>
              MirStepNode.step
                (pushCalleeFrame
                  s
                  callerBody
                  locals'
                  destination
                  targetBb
                  calleeBody
                  argVals
                  unwind)
        | .none =>
          match isDirectExactDivTarget target with
          | true =>
            match argVals with
            | .scalar lhs :: .scalar rhs :: .nil =>
              match
                resolveIntrinsicIsSigned
                  target
                  bodyLocalDecls
                  bodyLayouts
                  argOps
              with
              | .none => MirStepNode.unsupported
              | .some isSigned =>
                match evalExactDiv lhs rhs isSigned with
                | .some retScalar =>
                  writeIntrinsicReturn s locals' destination targetBb (.scalar retScalar)
                | .none => MirStepNode.fail .ub
            | _ => MirStepNode.fail .ub
          | false =>
            match target.isIndirect with
            | true =>
              MirStepNode.extCall
                { defPath := target.defPath, typeArgs := target.typeArgs, args := argVals, memory := s.memory }
                (resumeExternalCall s locals' destination targetBb unwind)
            | false =>
              match
                evalDirectRustIntrinsic?
                  s
                  currentBody
                  target
                  bodyLocalDecls
                  bodyLayouts
                  argOps
                  argVals
                  locals'
                  destination
                  targetBb
                  unwind
              with
              | .some stepNode => stepNode
              | .none =>
                MirStepNode.extCall
                  { defPath := target.defPath, typeArgs := target.typeArgs, args := argVals, memory := s.memory }
                  (resumeExternalCall s locals' destination targetBb unwind)
  -- Diverging call (`target == Option.none`, return type `!`):
  | .call func argOps destination .none unwind =>
    let bodyLocalDecls := bodyLocalDeclsOf currentBody
    let bodyLayouts : LayoutTable :=
      match currentBody with
      | .some b => b.layouts
      | .none => emptyLayoutTable
    match
      resolveCallTarget
        s
        func
        (length argOps)
        bodyLocalDecls
        bodyLayouts
    with
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
    | .ok target localsAfterFunc =>
      match
        evalOperands
          localsAfterFunc
          argOps
          s.memory.borrows
          s.memory.globals
          bodyLayouts
          s.memory.callerLocals
          (callStack := s.memory.callStack)
      with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok argVals locals' =>
        match resolve bodyLayouts target.defPath target.typeArgs s.memory.traitImpls with
        | .some calleeBody =>
          match checkCalleeTargetCompatible target calleeBody (length argVals) with
          | false => MirStepNode.fail .ub
          | true =>
            match currentBody with
            | .none => MirStepNode.unsupported
            | .some callerBody =>
              MirStepNode.step
                (pushDivergingCalleeFrame
                  s
                  callerBody
                  locals'
                  destination
                  unwind
                  calleeBody
                  argVals)
        | .none =>
          -- A diverging call to `core::intrinsics::const_eval_select` (one whose
          -- `called_at_rt` returns `!`) is not unpacked here; like any other
          -- unlinked callee it becomes an external call, which constrains
          -- nothing. Captured MIR never contains one, because `rustc` replaces
          -- every `const_eval_select` call with a direct call to `called_at_rt`
          -- before `optimized_mir` (`withConstEvalSelectIntrinsicTypeArgs`).
          match target.isIndirect with
          | false =>
            match isUnreachableCallTarget target.defPath with
            | true => MirStepNode.fail .ub
            | false =>
              match isAbortingPanicDefPath target.defPath with
              | true => MirStepNode.retOutcome .abort
              | false =>
                match isUnwindingPanicDefPath target.defPath with
                | true =>
                  match applyUnwindAction s locals' s.memory unwind with
                  | .running nextState => MirStepNode.step nextState
                  | .halted out => MirStepNode.retOutcome out
                  | .faulted fk => MirStepNode.fail fk
                | false =>
                  MirStepNode.extCall
                    { defPath := target.defPath, typeArgs := target.typeArgs, args := argVals, memory := s.memory }
                    (resumeExternalDivergingCall s locals' unwind)
          | true =>
            MirStepNode.extCall
              { defPath := target.defPath, typeArgs := target.typeArgs, args := argVals, memory := s.memory }
              (resumeExternalDivergingCall s locals' unwind)
  | .tailCall func argOps =>
    tailCallWith resolve s func argOps currentBody
  | _ => evalTerminator s term currentBody

/-- The trusted `stepMirFn` with its terminator step abstracted. -/
def stepMirFnWith (termStep : MachineState → Terminator → Option CapturedMir → MirStepNode)
    (body : CapturedMir) (s : MachineState) : MirStepNode :=
  let currentBody := s.memory.activeCallee.getD body
  match currentBody.phase with
  | .other _ => MirStepNode.unsupported
  | _ =>
    match get? currentBody.basicBlocks s.frame.blockIdx with
    | none => MirStepNode.fail .ub
    | some bb =>
      match get? bb.statements s.frame.stmtIdx with
      | some stmt => evalStmt s stmt currentBody.localDecls currentBody.layouts
      | none =>
        if s.frame.stmtIdx == length bb.statements then
          termStep s bb.terminator (some currentBody)
        else
          MirStepNode.fail .ub

/-- **Branch-pruned single step** under a callee resolver. -/
def stepBranchPruned (resolve : CalleeResolver) (body : CapturedMir) (s : MachineState) :
    MirStepNode :=
  stepMirFnWith (stepTerminatorWith true resolve) body s

/-- Unpruned list-backed single step (trusted switch semantics, `lookupCallee callees`). -/
def stepListUnpruned (callees : List CapturedMir) (body : CapturedMir) (s : MachineState) :
    MirStepNode :=
  stepMirFnWith (stepTerminatorWith false (listResolver callees)) body s

/-- The trusted `stepMirFn` is `stepMirFnWith evalTerminator`. -/
theorem stepMirFn_eq_stepMirFnWith (body : CapturedMir) (s : MachineState) :
    stepMirFn body s = stepMirFnWith (fun s t cb => evalTerminator s t cb) body s := rfl

/-- `tailCallWith` under the memory's own callee list is the trusted tail call. -/
theorem tailCallWith_list_eq_trusted (s : MachineState) (func : Operand)
    (argOps : List Operand) (currentBody : Option CapturedMir) :
    tailCallWith (listResolver s.memory.callees) s func argOps currentBody =
      evalTailCallTerminator s func argOps currentBody := rfl

/-- **Pruning is exact**: the literal-discriminant shortcut equals the trusted
`evalOperand`-driven `switchInt` step on every terminator. -/
theorem stepTerminatorWith_prune_exact (resolve : CalleeResolver) (s : MachineState)
    (term : Terminator) (currentBody : Option CapturedMir) :
    stepTerminatorWith true resolve s term currentBody =
      stepTerminatorWith false resolve s term currentBody := by
  obtain ⟨kind, span⟩ := term
  cases kind with
  | switchInt discr targets =>
    cases discr with
    | constant c =>
      obtain ⟨ty, val⟩ := c
      cases val with
      | scalar sc =>
        cases sc with
        | int si => rfl
        | ptr p sz => rfl
      | _ => rfl
    | copy p => rfl
    | move p => rfl
  | call func argOps destination target unwind => cases target <;> rfl
  | _ => rfl

/-- The unpruned list-backed terminator step under the memory's own callee list
is the trusted `evalTerminator`. -/
theorem stepTerminatorWith_list_eq_trusted (s : MachineState) (term : Terminator)
    (currentBody : Option CapturedMir) :
    stepTerminatorWith false (listResolver s.memory.callees) s term currentBody =
      evalTerminator s term currentBody := by
  obtain ⟨kind, span⟩ := term
  cases kind with
  | call func argOps destination target unwind => cases target <;> rfl
  | _ => rfl

/-- `O(1)` dead-branch pruning lemma: a literal `switchInt` step is its taken
target, independent of the dead arm. -/
theorem stepTerminatorWith_litSwitch (resolve : CalleeResolver) (s : MachineState)
    (ty : Ty) (si : ScalarInt) (targets : SwitchTargets) (span : String)
    (currentBody : Option CapturedMir) :
    stepTerminatorWith true resolve s
        ⟨.switchInt (.constant ⟨ty, .scalar (.int si)⟩) targets, span⟩ currentBody =
      MirStepNode.emitStep (.event si.bits) {
        s with
        frame := {
          blockIdx := lookupSwitchTarget si.bits targets.branches targets.otherwise
          stmtIdx := 0
          locals := s.frame.locals } } := rfl

/-- Pointwise congruence of `stepMirFnWith` in its terminator step at state `s`. -/
theorem stepMirFnWith_congr_at
    {t₁ t₂ : MachineState → Terminator → Option CapturedMir → MirStepNode}
    {body : CapturedMir} {s : MachineState}
    (h : ∀ term cb, t₁ s term cb = t₂ s term cb) :
    stepMirFnWith t₁ body s = stepMirFnWith t₂ body s := by
  unfold stepMirFnWith
  simp only [h]

/-- Congruence of `stepMirFnWith` in its terminator step. -/
theorem stepMirFnWith_congr
    {t₁ t₂ : MachineState → Terminator → Option CapturedMir → MirStepNode}
    (h : ∀ s term cb, t₁ s term cb = t₂ s term cb) (body : CapturedMir) (s : MachineState) :
    stepMirFnWith t₁ body s = stepMirFnWith t₂ body s := by
  have : t₁ = t₂ := by funext s term cb; exact h s term cb
  rw [this]

/-- **Pruned opaque step = unpruned list step** (single step). -/
theorem stepBranchPruned_eq_stepListUnpruned (callees : List CapturedMir) (body : CapturedMir)
    (s : MachineState) :
    stepBranchPruned (OpaqueCalleeTable.ofList callees).lookup body s =
      stepListUnpruned callees body s := by
  unfold stepBranchPruned stepListUnpruned
  rw [opaqueCalleeTable_lookup_eq_listResolver]
  exact stepMirFnWith_congr (fun s term cb => stepTerminatorWith_prune_exact _ s term cb) body s

/-- **Trusted agreement** (list): with the memory's own callee list, the unpruned
list step is the trusted `stepMirFn`. -/
theorem stepListUnpruned_eq_trusted (body : CapturedMir) (s : MachineState) :
    stepListUnpruned s.memory.callees body s = stepMirFn body s := by
  rw [stepMirFn_eq_stepMirFnWith]
  unfold stepListUnpruned
  exact stepMirFnWith_congr_at (fun term cb => stepTerminatorWith_list_eq_trusted s term cb)

/-- **Trusted agreement** (opaque, pruned): a branch-pruned step over an opaque
table holding the memory's callee list is the trusted `stepMirFn`. -/
theorem stepBranchPruned_eq_trusted (tbl : OpaqueCalleeTable) (body : CapturedMir)
    (s : MachineState) (h : tbl.toList = s.memory.callees) :
    stepBranchPruned tbl.lookup body s = stepMirFn body s := by
  rw [← OpaqueCalleeTable.ofList_toList tbl, h, stepBranchPruned_eq_stepListUnpruned,
    stepListUnpruned_eq_trusted]

/-! ### Fuel-bounded multi-step evaluation -/

/-- Classification of one trusted `MirStepNode` transition. -/
inductive StepView : Type where
  /-- Continue at `next`, possibly after emitting observation `obs`. -/
  | cont (obs : Option MirObs) (next : MirExecState)
  /-- Root return. -/
  | ret (out : MirOutcome)
  /-- Operational fault. -/
  | fault (kind : FailureKind)
  /-- External / unlinked call awaiting the environment. -/
  | external (req : MirCallReq)
  deriving DecidableEq

/-- View a `MirStepNode` (`ITreeF MirEffect MirOutcome MirExecState`). -/
def viewStepNode : MirStepNode → StepView
  | .ret out => .ret out
  | .tau next => .cont none next
  | .vis (.inl (.fail fk)) _ => .fault fk
  | .vis (.inr (.inl (.emit ev))) k => .cont (some ev) (k PUnit.unit)
  | .vis (.inr (.inr (.call req))) _ => .external req

/-- Terminal result of a fuel-bounded run, with its observation trace. -/
inductive RunResult : Type where
  | halted (out : MirOutcome) (trace : List MirObs)
  | faulted (kind : FailureKind) (trace : List MirObs)
  | external (req : MirCallReq) (trace : List MirObs)
  | outOfFuel (state : MachineState) (trace : List MirObs)
  deriving DecidableEq

/-- Iterate a single-step function for at most `fuel` steps. -/
def runSteps (step : MachineState → MirStepNode) : Nat → MachineState → List MirObs → RunResult
  | 0, s, tr => .outOfFuel s tr
  | n + 1, s, tr =>
    match viewStepNode (step s) with
    | .cont obs (.running s') => runSteps step n s' (tr ++ obs.toList)
    | .cont obs (.halted out) => .halted out (tr ++ obs.toList)
    | .cont obs (.faulted fk) => .faulted fk (tr ++ obs.toList)
    | .ret out => .halted out tr
    | .fault fk => .faulted fk tr
    | .external req => .external req tr

/-- Fuel-bounded branch-pruned evaluation over an opaque callee table. -/
def evalWithOpaqueCallees (tbl : OpaqueCalleeTable) (body : CapturedMir) (fuel : Nat)
    (s : MachineState) : RunResult :=
  runSteps (stepBranchPruned tbl.lookup body) fuel s []

/-- Fuel-bounded unpruned evaluation over a concrete callee list. -/
def evalWithListCallees (callees : List CapturedMir) (body : CapturedMir) (fuel : Nat)
    (s : MachineState) : RunResult :=
  runSteps (stepListUnpruned callees body) fuel s []

/-- **Exact equivalence**: opaque-table branch-pruned evaluation equals concrete
list-backed unpruned evaluation for every program, callee list (hence every
caller layout and trait-impl table), state, and fuel. -/
theorem evalWithOpaqueCallees_eq_evalWithListCallees (callees : List CapturedMir)
    (body : CapturedMir) (fuel : Nat) (s : MachineState) :
    evalWithOpaqueCallees (OpaqueCalleeTable.ofList callees) body fuel s =
      evalWithListCallees callees body fuel s := by
  unfold evalWithOpaqueCallees evalWithListCallees
  have h : stepBranchPruned (OpaqueCalleeTable.ofList callees).lookup body =
      stepListUnpruned callees body :=
    funext (stepBranchPruned_eq_stepListUnpruned callees body)
  rw [h]

/-- Table-level form of `evalWithOpaqueCallees_eq_evalWithListCallees`. -/
theorem evalWithOpaqueCallees_eq_evalWithListCallees_toList (tbl : OpaqueCalleeTable)
    (body : CapturedMir) (fuel : Nat) (s : MachineState) :
    evalWithOpaqueCallees tbl body fuel s = evalWithListCallees tbl.toList body fuel s := by
  rw [← evalWithOpaqueCallees_eq_evalWithListCallees, OpaqueCalleeTable.ofList_toList]

/-- States at which a fuel-bounded run applies its step function. -/
def runVisited (step : MachineState → MirStepNode) : Nat → MachineState → List MachineState
  | 0, _ => []
  | n + 1, s =>
    s :: match viewStepNode (step s) with
      | .cont _ (.running s') => runVisited step n s'
      | _ => []

/-- Two step functions agreeing on every state one run visits yield equal runs. -/
theorem runSteps_congr_visited {step₁ step₂ : MachineState → MirStepNode} :
    ∀ (fuel : Nat) (s : MachineState) (tr : List MirObs),
      (∀ s' ∈ runVisited step₂ fuel s, step₁ s' = step₂ s') →
        runSteps step₁ fuel s tr = runSteps step₂ fuel s tr
  | 0, _, _, _ => rfl
  | n + 1, s, tr, h => by
    have hs : step₁ s = step₂ s := h s (by simp [runVisited])
    simp only [runSteps, hs]
    split
    · rename_i obs s' hv
      apply runSteps_congr_visited n s' _
      intro s'' hs''
      apply h
      simp [runVisited, hv, hs'']
    all_goals rfl

/-- **Multi-step trusted agreement**: when every state the pruned opaque run visits
keeps the table's callees in `memory.callees` (the trusted frame condition), the
run *is* the iterated trusted `stepMirFn`. -/
theorem evalWithOpaqueCallees_eq_trusted (tbl : OpaqueCalleeTable) (body : CapturedMir)
    (fuel : Nat) (s : MachineState)
    (hframe : ∀ s' ∈ runVisited (stepBranchPruned tbl.lookup body) fuel s,
      s'.memory.callees = tbl.toList) :
    evalWithOpaqueCallees tbl body fuel s = runSteps (stepMirFn body) fuel s [] := by
  unfold evalWithOpaqueCallees
  exact (runSteps_congr_visited fuel s []
    (fun s' hs' => (stepBranchPruned_eq_trusted tbl body s' (hframe s' hs').symm).symm)).symm

/-! ### Demanded-key call-cone narrowing -/

/-- The terminator executed by the next step at `s`, with its active body. -/
def activeTerminator? (body : CapturedMir) (s : MachineState) : Option (Terminator × CapturedMir) :=
  let currentBody := s.memory.activeCallee.getD body
  match currentBody.phase with
  | .other _ => none
  | _ =>
    match get? currentBody.basicBlocks s.frame.blockIdx with
    | none => none
    | some bb =>
      match get? bb.statements s.frame.stmtIdx with
      | some _ => none
      | none =>
        if s.frame.stmtIdx == length bb.statements then some (bb.terminator, currentBody)
        else none

/-- The callee-table key a call / tail-call terminator demands at `s`. -/
def terminatorKey? (s : MachineState) (term : Terminator) (currentBody : CapturedMir) :
    Option CalleeKey :=
  match term.kind with
  | .call func argOps _ _ _ =>
    match resolveCallTarget s func (length argOps) currentBody.localDecls currentBody.layouts with
    | .ok target _ =>
      some ⟨currentBody.layouts, target.defPath, target.typeArgs, s.memory.traitImpls⟩
    | _ => none
  | .tailCall func argOps =>
    match resolveCallTarget s func (length argOps) currentBody.localDecls currentBody.layouts with
    | .ok target _ =>
      some ⟨currentBody.layouts, target.defPath, target.typeArgs, s.memory.traitImpls⟩
    | _ => none
  | _ => none

/-- The callee-table key demanded by the next step at `s` (if any). Literal
`switchInt` steps demand nothing, so dead-arm call sites are never demanded. -/
def demandedKey? (body : CapturedMir) (s : MachineState) : Option CalleeKey :=
  match activeTerminator? body s with
  | some (term, cb) => terminatorKey? s term cb
  | none => none

/-- All callee-table keys demanded along a fuel-bounded branch-pruned run: the
live reachable call cone (dead literal arms and unreachable blocks excluded). -/
def demandedKeys (resolve : CalleeResolver) (body : CapturedMir) :
    Nat → MachineState → List CalleeKey
  | 0, _ => []
  | n + 1, s =>
    (demandedKey? body s).toList ++
      match viewStepNode (stepBranchPruned resolve body s) with
      | .cont _ (.running s') => demandedKeys resolve body n s'
      | _ => []

/-- A terminator step depends on its resolver only at the demanded key. -/
theorem stepTerminatorWith_congr (prune : Bool) {r₁ r₂ : CalleeResolver} (s : MachineState)
    (term : Terminator) (cb : CapturedMir)
    (h : ∀ k, terminatorKey? s term cb = some k → k.apply r₁ = k.apply r₂) :
    stepTerminatorWith prune r₁ s term (some cb) = stepTerminatorWith prune r₂ s term (some cb) := by
  obtain ⟨kind, span⟩ := term
  cases kind with
  | call func argOps destination tgt unwind =>
    cases hrt : resolveCallTarget s func (length argOps) cb.localDecls cb.layouts with
    | ok target locals =>
      have hk := h ⟨cb.layouts, target.defPath, target.typeArgs, s.memory.traitImpls⟩
        (by simp only [terminatorKey?, hrt])
      simp only [CalleeKey.apply] at hk
      cases tgt <;> simp only [stepTerminatorWith, bodyLocalDeclsOf, hrt, hk]
    | ub => cases tgt <;> simp only [stepTerminatorWith, bodyLocalDeclsOf, hrt]
    | unsupported => cases tgt <;> simp only [stepTerminatorWith, bodyLocalDeclsOf, hrt]
  | tailCall func argOps =>
    cases hrt : resolveCallTarget s func (length argOps) cb.localDecls cb.layouts with
    | ok target locals =>
      have hk := h ⟨cb.layouts, target.defPath, target.typeArgs, s.memory.traitImpls⟩
        (by simp only [terminatorKey?, hrt])
      simp only [CalleeKey.apply] at hk
      simp only [stepTerminatorWith, tailCallWith, bodyLocalDeclsOf, hrt, hk]
    | ub => simp only [stepTerminatorWith, tailCallWith, bodyLocalDeclsOf, hrt]
    | unsupported => simp only [stepTerminatorWith, tailCallWith, bodyLocalDeclsOf, hrt]
  | _ => rfl

/-- `stepMirFnWith` depends on its terminator step only at the active terminator. -/
theorem stepMirFnWith_congr_active
    {t₁ t₂ : MachineState → Terminator → Option CapturedMir → MirStepNode}
    (body : CapturedMir) (s : MachineState)
    (h : ∀ term cb, activeTerminator? body s = some (term, cb) →
      t₁ s term (some cb) = t₂ s term (some cb)) :
    stepMirFnWith t₁ body s = stepMirFnWith t₂ body s := by
  unfold stepMirFnWith
  unfold activeTerminator? at h
  dsimp only at h ⊢
  cases hph : (s.memory.activeCallee.getD body).phase with
  | other name => rfl
  | runtimePostCleanup | runtimeOptimized =>
    simp only [hph] at h ⊢
    cases hbb : get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx with
    | none => rfl
    | some bb =>
      simp only [hbb] at h ⊢
      cases hst : get? bb.statements s.frame.stmtIdx with
      | some st => rfl
      | none =>
        simp only [hst] at h ⊢
        by_cases hidx : (s.frame.stmtIdx == length bb.statements) = true
        · simp only [hidx, ite_true] at h ⊢
          exact h _ _ rfl
        · simp only [hidx] at h ⊢
          rfl

/-- **Single-step cone congruence**: a pruned step depends on the resolver only
at the key it demands. -/
theorem stepBranchPruned_congr {r₁ r₂ : CalleeResolver} (body : CapturedMir) (s : MachineState)
    (h : ∀ k, demandedKey? body s = some k → k.apply r₁ = k.apply r₂) :
    stepBranchPruned r₁ body s = stepBranchPruned r₂ body s := by
  unfold stepBranchPruned
  apply stepMirFnWith_congr_active
  intro term cb hact
  apply stepTerminatorWith_congr
  intro k hk
  apply h
  simp [demandedKey?, hact, hk]

/-- Multi-step cone congruence for arbitrary resolvers. -/
theorem runSteps_pruned_cone {r₁ r₂ : CalleeResolver} (body : CapturedMir) :
    ∀ (fuel : Nat) (s : MachineState) (tr : List MirObs),
      (∀ k ∈ demandedKeys r₂ body fuel s, k.apply r₁ = k.apply r₂) →
        runSteps (stepBranchPruned r₁ body) fuel s tr =
          runSteps (stepBranchPruned r₂ body) fuel s tr
  | 0, _, _, _ => rfl
  | n + 1, s, tr, h => by
    have hstep : stepBranchPruned r₁ body s = stepBranchPruned r₂ body s :=
      stepBranchPruned_congr body s (fun k hk => h k (by simp [demandedKeys, hk]))
    simp only [runSteps, hstep]
    split
    · rename_i obs s' hv
      apply runSteps_pruned_cone body n s' _
      intro k hk
      apply h
      simp [demandedKeys, hv, hk]
    all_goals rfl

/-- **Call-cone narrowing**: if `narrowTbl` agrees with `fullTbl` on every key
demanded along the full-table run (the live reachable call cone, which excludes
callees referenced only from dead literal arms or unreachable blocks), the
narrowed evaluation produces exactly the same result. -/
theorem evalWithOpaqueCallees_cone_narrow (narrowTbl fullTbl : OpaqueCalleeTable)
    (body : CapturedMir) (fuel : Nat) (s : MachineState)
    (hcone : ∀ k ∈ demandedKeys fullTbl.lookup body fuel s,
      narrowTbl.lookupKey k = fullTbl.lookupKey k) :
    evalWithOpaqueCallees narrowTbl body fuel s = evalWithOpaqueCallees fullTbl body fuel s :=
  runSteps_pruned_cone body fuel s [] hcone

/-- Narrowing stated against the narrowed run's own demanded keys (the form a
client uses after running only the small table). -/
theorem evalWithOpaqueCallees_cone_narrow_of_narrow (narrowTbl fullTbl : OpaqueCalleeTable)
    (body : CapturedMir) (fuel : Nat) (s : MachineState)
    (hcone : ∀ k ∈ demandedKeys narrowTbl.lookup body fuel s,
      narrowTbl.lookupKey k = fullTbl.lookupKey k) :
    evalWithOpaqueCallees narrowTbl body fuel s = evalWithOpaqueCallees fullTbl body fuel s :=
  (runSteps_pruned_cone body fuel s [] (fun k hk => (hcone k hk).symm)).symm


/-! ### Canaries over concrete captured MIR -/

/-- Decidable run tag. -/
inductive RunTag : Type where
  | halted
  | faulted
  | external
  | outOfFuel
  deriving DecidableEq

/-- Decidable observation of a run (tag, branch-event trace, returned scalar bits,
external-call target). -/
structure RunSummary : Type where
  tag : RunTag
  trace : List MirObs
  retBits : Option Nat
  externalTarget : Option DefPath
  deriving DecidableEq

/-- Summarize a run result. -/
def RunResult.summary : RunResult → RunSummary
  | .halted out tr =>
    ⟨.halted, tr, (match out with | .normal (.scalar si, _) => some si.bits | _ => none), none⟩
  | .faulted _ tr => ⟨.faulted, tr, none, none⟩
  | .external req tr => ⟨.external, tr, none, some req.defPath⟩
  | .outOfFuel _ tr => ⟨.outOfFuel, tr, none, none⟩


/-- `DefPath` of the active callee after a continuing step (`none` at the root body or on a
non-continuing step). -/
def StepView.activeCalleePath? : StepView → Option DefPath
  | .cont _ (.running s') => s'.memory.activeCallee.map (·.defPath)
  | _ => none

/-! ### Unconditional trusted frame lemma: `memory.callees` and `memory.traitImpls`

The trusted machine *reads* `Memory.callees` (callee resolution, `checkCalleeSig`) and
`Memory.traitImpls` (trait-method resolution) but never *writes* them: every `evalStmt`,
`evalTerminator`, intrinsic helper, frame push / pop, and unwind keeps both fields, and
only an external call — which ends every run below — installs an environment-supplied
memory. The lemmas in this section prove this for *every* state, statement, terminator,
and callee resolver, with no cone, monomorphism, or intrinsic side condition. They reuse
`Anneal.MirLiftCore`'s commutation lemmas for the callee-query-free fragment and handle the
remaining cases directly: function-pointer reification casts (which consult
`Memory.callees` through `checkCalleeSig`), polymorphic / trait-dispatched calls, and the
`core::intrinsics::const_eval_select` runtime callee. -/

/-- The callee frame of a machine state: its linked callee table and its registered
`TraitImplEntry` records. -/
def CalleeFrame (callees : List CapturedMir) (traitImpls : List TraitImplEntry)
    (s : MachineState) : Prop :=
  s.memory.callees = callees ∧ s.memory.traitImpls = traitImpls

/-- Every continuing (`.tau` or observation) successor of `n` keeps the callee table and the
trait impls of `s`. -/
abbrev FramesStep (s : MachineState) (n : MirStepNode) : Prop :=
  MirLiftCore.NodeSuccs (CalleeFrame s.memory.callees s.memory.traitImpls) n

/-- A step that is a fixed point of `Memory.withCalleeCtx` at `s`'s own context frames `s`. -/
theorem framesStep_of_ctx_fixed {s : MachineState} {n : MirStepNode}
    (hfix : n = MirLiftCore.MirStepNode.mapMem
      (MirLiftCore.Memory.withCalleeCtx s.memory.callees s.memory.activeCallee
        s.memory.traitImpls) n) :
    FramesStep s n :=
  MirLiftCore.nodeSuccs_of_fixed hfix fun s' hs' => by
    have hm : s'.memory = MirLiftCore.Memory.withCalleeCtx s.memory.callees
        s.memory.activeCallee s.memory.traitImpls s'.memory :=
      congrArg MachineState.memory hs'
    exact ⟨by rw [hm], by rw [hm]⟩

/-- A silent step to a state with the same callee table and trait impls frames `s`. -/
theorem framesStep_step {s st : MachineState} (hc : st.memory.callees = s.memory.callees)
    (ht : st.memory.traitImpls = s.memory.traitImpls) : FramesStep s (MirStepNode.step st) :=
  ⟨hc, ht⟩

/-- `writeIntrinsicReturn` frames its state. -/
theorem writeIntrinsicReturn_frames (s : MachineState) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (retVal : Value) :
    FramesStep s (writeIntrinsicReturn s locals' destination targetBb retVal) :=
  framesStep_of_ctx_fixed
    (MirLiftCore.writeIntrinsicReturn_calleeCtx_preserved s locals' destination targetBb retVal)

/-- `writeIntrinsicScalarResult` frames its state. -/
theorem writeIntrinsicScalarResult_frames (s : MachineState) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (resOpt : Option ScalarInt) :
    FramesStep s (writeIntrinsicScalarResult s locals' destination targetBb resOpt) := by
  have h := MirLiftCore.writeIntrinsicScalarResult_withCalleeCtx s.memory.callees
    s.memory.activeCallee s.memory.traitImpls s locals' destination targetBb resOpt
  rw [MirLiftCore.MachineState.withCalleeCtx_self] at h
  exact framesStep_of_ctx_fixed h

/-- Every inline (non-`const_eval_select`) compiler intrinsic frames its state. -/
theorem evalNonSelectIntrinsicCall_frames (kind : RustIntrinsicKind) (s : MachineState)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) :
    FramesStep s (evalNonSelectIntrinsicCall kind s target bodyLocalDecls bodyLayouts
      argOps argVals locals' destination targetBb) :=
  framesStep_of_ctx_fixed
    (MirLiftCore.evalNonSelectIntrinsicCall_calleeCtx_preserved kind s target bodyLocalDecls
      bodyLayouts argOps argVals locals' destination targetBb)

/-- Unwinding through saved caller frames keeps the callee table and trait impls of the
unwound memory. -/
theorem unwindFromCallStack_frames :
    ∀ (stk : List SavedCallerFrame) (m : Memory) (s' : MachineState),
      unwindFromCallStack stk m = .running s' →
        s'.memory.callees = m.callees ∧ s'.memory.traitImpls = m.traitImpls
  | [], _, _, h => by cases h
  | caller :: rest, m, s', h => by
    unfold unwindFromCallStack at h
    dsimp only at h
    cases hr : caller.returnUnwind with
    | unreachable => rw [hr] at h; dsimp only at h; cases h
    | terminate => rw [hr] at h; dsimp only at h; cases h
    | continue_ =>
      rw [hr] at h
      dsimp only at h
      exact unwindFromCallStack_frames rest
        { m with
          callStack := rest
          activeCallee := some caller.callerBody
          activeProtectors := restoreCallerProtectors caller } s' h
    | cleanup bb =>
      rw [hr] at h
      dsimp only at h
      cases h
      exact ⟨rfl, rfl⟩

/-- A resolved unwind action keeps the callee table and trait impls of its state. -/
theorem applyUnwindAction_frames {s : MachineState} {l : List LocalSlot} {u : UnwindAction}
    {s' : MachineState} (h : applyUnwindAction s l s.memory u = .running s') :
    CalleeFrame s.memory.callees s.memory.traitImpls s' := by
  cases u with
  | unreachable => cases h
  | terminate => cases h
  | continue_ => exact unwindFromCallStack_frames s.memory.callStack s.memory s' h
  | cleanup bb => cases h; exact ⟨rfl, rfl⟩

/-- `TerminatorKind.return_` into a saved caller keeps the callee table and trait impls. -/
theorem calleeFrame_return {s : MachineState} {caller : SavedCallerFrame}
    {rest : List SavedCallerFrame} {retVal : Value} {locals' : List LocalSlot} {mem' : Memory}
    {F : StackFrame}
    (h_w : writeReturnDestination caller.frame.locals (MirLiftCore.ccReturnCallerMem s caller rest)
      caller.destination retVal caller.callerBody.localDecls caller.callerBody.layouts =
        .ok locals' mem') :
    CalleeFrame s.memory.callees s.memory.traitImpls { frame := F, memory := mem' } := by
  obtain ⟨hc, _, ht⟩ := MirLiftCore.writeReturnDestination_ctx_preserved h_w
  exact ⟨hc, ht⟩

/-- `internFnPtr` (function-pointer reification) only extends `Memory.fnPtrs`. -/
theorem internFnPtr_keepsCtx {mem : Memory} {defPath : DefPath} {typeArgs : List RigidTy}
    {fnSig : Option RigidTy} {allocId : AllocId} {mem' : Memory}
    (h : internFnPtr mem defPath typeArgs fnSig = (allocId, mem')) :
    mem'.callees = mem.callees ∧ mem'.activeCallee = mem.activeCallee ∧
      mem'.traitImpls = mem.traitImpls := by
  unfold internFnPtr at h
  split at h <;> (injection h with _ h₂; subst h₂; exact ⟨rfl, rfl, rfl⟩)

/-- Result-memory predicate of an rvalue evaluation: the callee context (`callees`,
`activeCallee`, `traitImpls`) of `mem` is kept. -/
def RvalueKeepsCtx (mem : Memory) : RvalueEvalResult → Prop
  | .ok _ _ mem' =>
    mem'.callees = mem.callees ∧ mem'.activeCallee = mem.activeCallee ∧
      mem'.traitImpls = mem.traitImpls
  | .ub => True
  | .unsupported => True

/-- **Every** rvalue evaluation keeps the callee context of its memory, including the
function-pointer reification casts that read `Memory.callees` through `checkCalleeSig`
(`Rvalue.calleeQueryFree rv = false`). -/
theorem evalRvalue_keepsCtx (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    RvalueKeepsCtx mem (evalRvalue locals rv mem localDecls layouts) := by
  cases h_free : MirLiftCore.Rvalue.calleeQueryFree rv with
  | true =>
    have hfix := MirLiftCore.evalRvalue_withCalleeCtx mem.callees mem.activeCallee
      mem.traitImpls locals rv mem localDecls layouts h_free
    change evalRvalue locals rv mem localDecls layouts = _ at hfix
    revert hfix
    cases evalRvalue locals rv mem localDecls layouts with
    | ok v l m =>
      intro hfix
      injection hfix with _ _ hm
      exact ⟨by rw [hm], by rw [hm], by rw [hm]⟩
    | ub => intro _; exact True.intro
    | unsupported => intro _; exact True.intro
  | false =>
    cases rv with
    | cast kind op ty =>
      cases kind with
      | pointerCoercion ck =>
        have h' : (!isReifyFnPointerCoercion ck || stringEq ck "UnsafeFnPointer") = false := h_free
        cases h_r : isReifyFnPointerCoercion ck with
        | false => rw [h_r] at h'; nomatch h'
        | true =>
          cases h_s : stringEq ck "UnsafeFnPointer" with
          | true => rw [h_r, h_s] at h'; nomatch h'
          | false =>
            show RvalueKeepsCtx mem (evalReifyFnPointer locals op ty mem localDecls layouts ck)
            unfold evalReifyFnPointer
            simp only [h_r, h_s]
            repeat' (first
              | exact True.intro
              | exact ⟨rfl, rfl, rfl⟩
              | exact internFnPtr_keepsCtx ‹_›
              | split
              | (dsimp only))
      | _ => nomatch h_free
    | _ => nomatch h_free

/-- Assignment-destination write of `evalStmt`'s `.assign` arm, after the rvalue has
evaluated to `val` with frame locals `locals₁` and memory `mem₁` (non-dereferencing
projected destination). Agrees with the trusted arm by `evalStmt_assign_eq`. -/
def assignNonDerefStep
    (s : MachineState) (dstLoc : Local) (proj : List ProjectionElem)
    (val : Value) (locals₁ : List LocalSlot) (mem₁ : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) : MirStepNode :=
  match get? locals₁ dstLoc with
  | .some (.init rootVal) =>
    match
      writeProjectedForLocal
        locals₁
        localDecls
        layouts
        dstLoc
        (ensureNestedFieldShells rootVal proj)
        proj
        val
    with
    | .ok rootVal' =>
      match set? locals₁ dstLoc (.init rootVal') with
      | .some locals₂ =>
        let resolvedLocalProj :=
          resolveBorrowWriteLocalProj localDecls layouts locals₁ dstLoc proj
        match mem₁.activeProtectors with
        | .nil =>
          let borrows' :=
            invalidateConflictingBorrowsAtProj
              mem₁.borrows dstLoc .none resolvedLocalProj 0 0 (length mem₁.callStack)
          MirStepNode.step
            (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
        | protHead :: protTail =>
          match
            hasProtectedWriteConflict
              mem₁.borrows (protHead :: protTail) dstLoc .none resolvedLocalProj 0 0
              (length mem₁.callStack)
          with
          | true => MirStepNode.fail .ub
          | false =>
            let borrows' :=
              invalidateConflictingBorrowsAtProj
                mem₁.borrows dstLoc .none resolvedLocalProj 0 0 (length mem₁.callStack)
            MirStepNode.step
              (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
      | .none => MirStepNode.fail .ub
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
  | .some .uninit =>
    match (match proj with
       | hd :: tl => uninitFieldWriteShell? localDecls layouts dstLoc hd tl
       | .nil => .none) with
    | .some rootVal =>
      match writeProjectedForLocal locals₁ localDecls layouts dstLoc rootVal proj val with
      | .ok rootVal' =>
        match set? locals₁ dstLoc (.init rootVal') with
        | .some locals₂ =>
          let resolvedLocalProj :=
            resolveBorrowWriteLocalProj
              localDecls
              layouts
              locals₁
              dstLoc
              proj
          match mem₁.activeProtectors with
          | .nil =>
            let borrows' :=
              invalidateConflictingBorrowsAtProj
                mem₁.borrows dstLoc .none resolvedLocalProj 0 0 (length mem₁.callStack)
            MirStepNode.step
              (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
          | protHead :: protTail =>
            match
              hasProtectedWriteConflict
                mem₁.borrows (protHead :: protTail) dstLoc .none resolvedLocalProj 0 0
                (length mem₁.callStack)
            with
            | true => MirStepNode.fail .ub
            | false =>
              let borrows' :=
                invalidateConflictingBorrowsAtProj
                  mem₁.borrows dstLoc .none resolvedLocalProj 0 0 (length mem₁.callStack)
              MirStepNode.step
                (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
        | .none => MirStepNode.fail .ub
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
    | .none => MirStepNode.fail .ub
  | .some .dead => MirStepNode.fail .ub
  | .none => MirStepNode.fail .ub

/-- Assignment-destination write of `evalStmt`'s `.assign` arm (unprojected, dereferencing,
and projected destinations), after the rvalue has evaluated to `val` with frame locals
`locals₁` and memory `mem₁`; agrees with the trusted arm by `evalStmt_assign_eq`. -/
def assignDstStep
    (s : MachineState) (dst : Place) (val : Value)
    (locals₁ : List LocalSlot) (mem₁ : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) : MirStepNode :=
  match dst.projection with
  | .nil =>
    match get? locals₁ dst.local_ with
    | .some .dead => MirStepNode.fail .ub
    | .some _ =>
      match set? locals₁ dst.local_ (.init val) with
      | .some locals₂ =>
        match mem₁.activeProtectors with
        | .nil =>
          let borrows' :=
            invalidateConflictingBorrows mem₁.borrows dst.local_ .none (length mem₁.callStack)
          MirStepNode.step
            (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
        | protHead :: protTail =>
          match
            hasProtectedWriteConflict
              mem₁.borrows (protHead :: protTail) dst.local_ .none .nil 0 0
              (length mem₁.callStack)
          with
          | true => MirStepNode.fail .ub
          | false =>
            let borrows' :=
              invalidateConflictingBorrows mem₁.borrows dst.local_ .none (length mem₁.callStack)
            MirStepNode.step
              (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
      | .none => MirStepNode.fail .ub
    | .none => MirStepNode.fail .ub
  | .deref :: restProj =>
    match
      evalPlaceWrite locals₁ mem₁.borrows dst val mem₁.activeProtectors localDecls layouts
        mem₁.callStack
    with
    | .ok locals₂ =>
      match
        Bool.or
          (derefWriteTreeUB locals₁ mem₁.borrows dst)
          (derefWriteUnionProtectorUB
            localDecls layouts locals₁ mem₁.borrows mem₁.activeProtectors dst restProj
            mem₁.callStack)
      with
      | true => MirStepNode.fail .ub
      | false =>
        let borrows' :=
          invalidateDerefWriteBorrowsWithLayouts
            localDecls layouts locals₁ mem₁.borrows dst restProj mem₁.callStack
        MirStepNode.step (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
    | .ub =>
      match mem₁.callStack with
      | .nil =>
        match mem₁.callerLocals with
        | .nil => MirStepNode.fail .ub
        | _ :: _ =>
          match
            evalCallerPlaceWrite
              locals₁ mem₁.callerLocals mem₁.borrows dst val mem₁.activeProtectors
          with
          | .ok callerLocals' =>
            match derefWriteTreeUB locals₁ mem₁.borrows dst with
            | true => MirStepNode.fail .ub
            | false =>
              let borrows' :=
                invalidateDerefWriteBorrows
                  locals₁ mem₁.borrows dst restProj mem₁.callerLocals
              MirStepNode.step
                (advanceStmt s locals₁
                  { mem₁ with borrows := borrows', callerLocals := callerLocals' })
          | .ub => MirStepNode.fail .ub
          | .unsupported => MirStepNode.unsupported
      | _ :: _ =>
        evalForeignFrameDerefWrite s locals₁ mem₁ dst restProj val localDecls layouts
    | .unsupported => MirStepNode.unsupported
  | hd :: tl =>
    assignNonDerefStep s dst.local_ (hd :: tl) val locals₁ mem₁ localDecls layouts

/-- The trusted `.assign` arm of `evalStmt` is the rvalue evaluation followed by
`assignDstStep`. -/
theorem evalStmt_assign_eq (s : MachineState) (dst : Place) (rv : Rvalue) (span : String)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalStmt s ⟨.assign dst rv, span⟩ localDecls layouts =
      match evalRvalue s.frame.locals rv s.memory localDecls layouts with
      | .ok val locals₁ mem₁ => assignDstStep s dst val locals₁ mem₁ localDecls layouts
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported := by
  unfold evalStmt
  dsimp only
  cases evalRvalue s.frame.locals rv s.memory localDecls layouts with
  | ub => rfl
  | unsupported => rfl
  | ok val locals₁ mem₁ =>
    rcases dst with ⟨dstLoc, dstProj⟩
    cases dstProj with
    | nil => rfl
    | cons hd tl => cases hd <;> rfl

/-- The assignment write frames `s` whenever the rvalue kept `s`'s callee context. -/
theorem assignDstStep_frames {s : MachineState} {dst : Place} {val : Value}
    {locals₁ : List LocalSlot} {mem₁ : Memory} {localDecls : List LocalDecl}
    {layouts : LayoutTable}
    (h : mem₁.callees = s.memory.callees ∧ mem₁.activeCallee = s.memory.activeCallee ∧
      mem₁.traitImpls = s.memory.traitImpls) :
    FramesStep s (assignDstStep s dst val locals₁ mem₁ localDecls layouts) := by
  have hforeign : ∀ restProj, FramesStep s
      (evalForeignFrameDerefWrite s locals₁ mem₁ dst restProj val localDecls layouts) := by
    intro restProj
    have hg : MirLiftCore.Memory.withCalleeCtx s.memory.callees s.memory.activeCallee
        s.memory.traitImpls mem₁ = mem₁ := by
      rw [← h.1, ← h.2.1, ← h.2.2]
    have hfix := MirLiftCore.evalForeignFrameDerefWrite_withCalleeCtx s.memory.callees
      s.memory.activeCallee s.memory.traitImpls s locals₁ mem₁ dst restProj val localDecls
      layouts
    rw [MirLiftCore.MachineState.withCalleeCtx_self, hg] at hfix
    exact framesStep_of_ctx_fixed hfix
  unfold assignDstStep assignNonDerefStep
  repeat' (first
    | exact True.intro
    | exact framesStep_step h.1 h.2.2
    | exact hforeign _
    | split
    | (dsimp only))

/-- **Statement frame lemma**: every trusted `evalStmt` step frames its state. -/
theorem evalStmt_frames (s : MachineState) (stmt : Statement) (localDecls : List LocalDecl)
    (layouts : LayoutTable) : FramesStep s (evalStmt s stmt localDecls layouts) := by
  rcases stmt with ⟨kind, span⟩
  cases kind with
  | assign dst rv =>
    rw [evalStmt_assign_eq]
    have hrv := evalRvalue_keepsCtx s.frame.locals rv s.memory localDecls layouts
    revert hrv
    cases evalRvalue s.frame.locals rv s.memory localDecls layouts with
    | ok val locals₁ mem₁ => intro hrv; exact assignDstStep_frames hrv
    | ub => intro _; exact True.intro
    | unsupported => intro _; exact True.intro
  | _ =>
    exact framesStep_of_ctx_fixed
      (MirLiftCore.evalStmt_calleeCtx_preserved s _ localDecls layouts rfl)

/-- Every trusted direct compiler-intrinsic step — including the `const_eval_select`
runtime callee, which is resolved through the trusted `lookupCallee s.memory.callees` and
entered with `pushCalleeFrame` — frames its state. -/
theorem evalDirectRustIntrinsic?_frames {s : MachineState} {currentBody : Option CapturedMir}
    {target : ResolvedCallTarget} {bodyLocalDecls : List LocalDecl} {bodyLayouts : LayoutTable}
    {argOps : List Operand} {argVals : List Value} {locals' : List LocalSlot}
    {destination : Place} {targetBb : BasicBlockIdx} {unwind : UnwindAction} {n : MirStepNode}
    (h : evalDirectRustIntrinsic? s currentBody target bodyLocalDecls bodyLayouts argOps argVals
      locals' destination targetBb unwind = some n) :
    FramesStep s n := by
  unfold evalDirectRustIntrinsic? at h
  split at h
  · nomatch h
  · injection h with h
    subst h
    repeat' (first
      | exact True.intro
      | exact framesStep_step rfl rfl
      | exact writeIntrinsicScalarResult_frames _ _ _ _ _
      | exact evalNonSelectIntrinsicCall_frames _ _ _ _ _ _ _ _ _ _
      | exact applyUnwindAction_frames ‹_›
      | (dsimp only)
      | split)
  · injection h with h
    subst h
    exact evalNonSelectIntrinsicCall_frames _ _ _ _ _ _ _ _ _ _

/-- **Terminator frame lemma** for *every* callee resolver and pruning mode: every
`stepTerminatorWith` step frames its state. Instantiated at the memory's own list resolver
it is the trusted `evalTerminator` (`stepTerminatorWith_list_eq_trusted`). -/
theorem stepTerminatorWith_frames (prune : Bool) (resolve : CalleeResolver) (s : MachineState)
    (term : Terminator) (currentBody : Option CapturedMir) :
    FramesStep s (stepTerminatorWith prune resolve s term currentBody) := by
  have hself : CalleeFrame s.memory.callees s.memory.traitImpls s := ⟨rfl, rfl⟩
  rcases term with ⟨kind, span⟩
  cases kind with
  | goto target => exact hself
  | switchInt discr targets =>
    unfold stepTerminatorWith evalTerminator
    dsimp only
    repeat' (first | exact True.intro | exact hself | (dsimp only) | split)
  | unwindResume =>
    show FramesStep s (evalTerminator s ⟨.unwindResume, span⟩ currentBody)
    unfold evalTerminator
    dsimp only
    repeat' (first
      | exact True.intro
      | exact unwindFromCallStack_frames s.memory.callStack s.memory _ ‹_›
      | (dsimp only)
      | split)
  | unwindTerminate => exact True.intro
  | return_ =>
    show FramesStep s (evalTerminator s ⟨.return_, span⟩ currentBody)
    rw [MirLiftCore.ccEvalReturn_eq]
    unfold MirLiftCore.ccEvalReturn
    repeat' (first | exact True.intro | exact calleeFrame_return ‹_› | (dsimp only) | split)
  | unreachable => exact True.intro
  | drop place target unwind =>
    show FramesStep s (evalTerminator s ⟨.drop place target unwind, span⟩ currentBody)
    unfold evalTerminator
    dsimp only
    repeat' (first | exact True.intro | exact hself | (dsimp only) | split)
  | assert cond expected target unwind =>
    show FramesStep s (evalTerminator s ⟨.assert cond expected target unwind, span⟩ currentBody)
    unfold evalTerminator
    dsimp only
    repeat' (first | exact True.intro | exact hself | exact applyUnwindAction_frames ‹_› | (dsimp only) | split)
  | call func argOps destination target unwind =>
    cases target with
    | some targetBb =>
      unfold stepTerminatorWith
      dsimp only
      repeat' (first
        | exact True.intro
        | exact hself
        | exact writeIntrinsicReturn_frames _ _ _ _ _
        | exact evalDirectRustIntrinsic?_frames ‹_›
        | (dsimp only)
        | split)
    | none =>
      unfold stepTerminatorWith
      dsimp only
      repeat' (first
        | exact True.intro
        | exact hself
        | exact applyUnwindAction_frames ‹_›
        | (dsimp only)
        | split)
  | tailCall func argOps =>
    unfold stepTerminatorWith tailCallWith
    dsimp only
    repeat' (first | exact True.intro | exact framesStep_step rfl rfl | (dsimp only) | split)
  | _ => exact True.intro

/-- `stepMirFnWith` frames its state whenever its terminator step does. -/
theorem stepMirFnWith_frames
    {termStep : MachineState → Terminator → Option CapturedMir → MirStepNode}
    (hterm : ∀ s term cb, FramesStep s (termStep s term cb)) (body : CapturedMir)
    (s : MachineState) : FramesStep s (stepMirFnWith termStep body s) := by
  unfold stepMirFnWith
  dsimp only
  split
  · exact True.intro
  · cases h_bb : get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx with
    | none => exact True.intro
    | some blk =>
      dsimp only
      cases h_st : get? blk.statements s.frame.stmtIdx with
      | some stmt => exact evalStmt_frames s stmt _ _
      | none =>
        dsimp only
        split
        · exact hterm _ _ _
        · exact True.intro

/-- **Pruned-step frame lemma**: a branch-pruned step under *any* callee resolver (in
particular any opaque table, however it relates to `s.memory.callees`) frames its state. -/
theorem stepBranchPruned_frames (resolve : CalleeResolver) (body : CapturedMir)
    (s : MachineState) : FramesStep s (stepBranchPruned resolve body s) :=
  stepMirFnWith_frames (stepTerminatorWith_frames true resolve) body s

/-- **Unconditional trusted frame lemma**: every trusted `stepMirFn` step keeps
`memory.callees` and `memory.traitImpls` in every continuing successor. -/
theorem stepMirFn_frames (body : CapturedMir) (s : MachineState) :
    FramesStep s (stepMirFn body s) := by
  rw [← stepListUnpruned_eq_trusted]
  exact stepMirFnWith_frames (stepTerminatorWith_frames false _) body s

/-- A successor exposed by `viewStepNode` satisfies every `NodeSuccs` invariant. -/
theorem nodeSuccs_of_view {P : MachineState → Prop} {n : MirStepNode} {obs : Option MirObs}
    {s' : MachineState} (hn : MirLiftCore.NodeSuccs P n)
    (hv : viewStepNode n = .cont obs (.running s')) : P s' := by
  rcases n with out | st | ⟨e, k⟩
  · nomatch hv
  · change StepView.cont none st = .cont obs (.running s') at hv
    injection hv with _ hst
    subst hst
    exact hn
  · rcases e with fk | x | c
    · cases fk with
      | fail kind => nomatch hv
    · cases x with
      | emit ev =>
        change StepView.cont (some ev) (k PUnit.unit) = .cont obs (.running s') at hv
        injection hv with _ hk
        change (match k PUnit.unit with
          | .running s' => P s'
          | _ => True) at hn
        rw [hk] at hn
        exact hn
    · cases c with
      | call req => nomatch hv

/-- Every state a fuel-bounded run of a framing step function visits keeps the initial
callee table and trait impls. -/
theorem runVisited_frames {step : MachineState → MirStepNode}
    (hstep : ∀ s, FramesStep s (step s)) :
    ∀ (fuel : Nat) (s s' : MachineState), s' ∈ runVisited step fuel s →
      CalleeFrame s.memory.callees s.memory.traitImpls s'
  | 0, _, _, h => nomatch h
  | n + 1, s, s', h => by
    unfold runVisited at h
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨rfl, rfl⟩
    · split at h
      · rename_i obs s₁ hv
        have h₁ : CalleeFrame s.memory.callees s.memory.traitImpls s₁ :=
          nodeSuccs_of_view (hstep s) hv
        have h₂ := runVisited_frames hstep n s₁ s' h
        exact ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩
      · nomatch h

/-- The trusted frame condition of `evalWithOpaqueCallees_eq_trusted`, strengthened to
`memory.traitImpls`: every state the pruned opaque run visits keeps the table's callee list
and the `TraitImplEntry` records `extraTraitImpls`. -/
def OpaqueRunFramed (tbl : OpaqueCalleeTable) (extraTraitImpls : List TraitImplEntry)
    (body : CapturedMir) (fuel : Nat) (s : MachineState) : Prop :=
  ∀ s' ∈ runVisited (stepBranchPruned tbl.lookup body) fuel s,
    s'.memory.callees = tbl.toList ∧ s'.memory.traitImpls = extraTraitImpls

/-- **The frame condition holds unconditionally** from every state that links the table
(`s.memory.callees = tbl.toList`) with trait impls `extraTraitImpls`. -/
theorem opaqueRunFramed_of_init (tbl : OpaqueCalleeTable) (extraTraitImpls : List TraitImplEntry)
    (body : CapturedMir) (fuel : Nat) (s : MachineState)
    (hcallees : s.memory.callees = tbl.toList) (htraits : s.memory.traitImpls = extraTraitImpls) :
    OpaqueRunFramed tbl extraTraitImpls body fuel s := fun s' hs' =>
  have h := runVisited_frames (stepBranchPruned_frames tbl.lookup body) fuel s s' hs'
  ⟨h.1.trans hcallees, h.2.trans htraits⟩

/-- Every state the iterated trusted `stepMirFn` visits keeps the initial callee table and
trait impls (no frame hypothesis). -/
theorem trusted_runVisited_frames (body : CapturedMir) (fuel : Nat) (s s' : MachineState)
    (hs' : s' ∈ runVisited (stepMirFn body) fuel s) :
    s'.memory.callees = s.memory.callees ∧ s'.memory.traitImpls = s.memory.traitImpls :=
  runVisited_frames (stepMirFn_frames body) fuel s s' hs'

/-- Multi-step trusted agreement from the strengthened frame condition. -/
theorem evalWithOpaqueCallees_eq_trusted_of_framed (tbl : OpaqueCalleeTable)
    (extraTraitImpls : List TraitImplEntry) (body : CapturedMir) (fuel : Nat) (s : MachineState)
    (hframed : OpaqueRunFramed tbl extraTraitImpls body fuel s) :
    evalWithOpaqueCallees tbl body fuel s = runSteps (stepMirFn body) fuel s [] :=
  evalWithOpaqueCallees_eq_trusted tbl body fuel s fun s' hs' => (hframed s' hs').1

/-- **Unconditional multi-step trusted agreement**: from *every* state linking the table in
`memory.callees`, the branch-pruned opaque evaluation is the iterated trusted `stepMirFn`;
the `memory.callees` / `memory.traitImpls` frame condition of
`evalWithOpaqueCallees_eq_trusted` is discharged by `stepBranchPruned_frames`. -/
theorem evalWithOpaqueCallees_eq_trusted_unconditional (tbl : OpaqueCalleeTable)
    (body : CapturedMir) (fuel : Nat) (s : MachineState)
    (hcallees : s.memory.callees = tbl.toList) :
    evalWithOpaqueCallees tbl body fuel s = runSteps (stepMirFn body) fuel s [] :=
  evalWithOpaqueCallees_eq_trusted_of_framed tbl s.memory.traitImpls body fuel s
    (opaqueRunFramed_of_init tbl s.memory.traitImpls body fuel s hcallees rfl)

/-- `initMachineStateWithCallees` links its callee list, empty or not. -/
theorem initMachineStateWithCallees_callees (body : CapturedMir) (args : List Value)
    (callees : List CapturedMir) :
    (initMachineStateWithCallees body args callees).memory.callees = callees := by
  cases callees <;> rfl

/-- `initMachineStateWithCallees` registers the root body's trait impls, empty list or not. -/
theorem initMachineStateWithCallees_traitImpls (body : CapturedMir) (args : List Value)
    (callees : List CapturedMir) :
    (initMachineStateWithCallees body args callees).memory.traitImpls = body.traitImpls := by
  cases callees <;> rfl

/-- **Unconditional agreement from `initMachineStateWithCallees`** (every table, including
the empty one). -/
theorem evalWithOpaqueCallees_eq_trusted_initWithCallees (tbl : OpaqueCalleeTable)
    (body : CapturedMir) (args : List Value) (fuel : Nat) :
    evalWithOpaqueCallees tbl body fuel (initMachineStateWithCallees body args tbl.toList) =
      runSteps (stepMirFn body) fuel (initMachineStateWithCallees body args tbl.toList) [] :=
  evalWithOpaqueCallees_eq_trusted_unconditional tbl body fuel _
    (initMachineStateWithCallees_callees body args tbl.toList)

/-- The frame condition from `initMachineStateWithCallees`: the run keeps the table and the
root body's trait impls. -/
theorem opaqueRunFramed_initWithCallees (tbl : OpaqueCalleeTable) (body : CapturedMir)
    (args : List Value) (fuel : Nat) :
    OpaqueRunFramed tbl body.traitImpls body fuel
      (initMachineStateWithCallees body args tbl.toList) :=
  opaqueRunFramed_of_init tbl body.traitImpls body fuel _
    (initMachineStateWithCallees_callees body args tbl.toList)
    (initMachineStateWithCallees_traitImpls body args tbl.toList)

/-- **Unconditional agreement from `initMachineStateWithMemoryAndCallees`** under
`MirLiftCore.CalleeInitWf`: a non-empty table, or the empty table over a clean entry memory
(`mem.callees = []`). -/
theorem evalWithOpaqueCallees_eq_trusted_initWithMemoryAndCallees_of_wf (tbl : OpaqueCalleeTable)
    (body : CapturedMir) (args : List Value) (mem : Memory) (fuel : Nat)
    (hwf : MirLiftCore.CalleeInitWf body mem tbl.toList) :
    evalWithOpaqueCallees tbl body fuel
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          tbl.toList) =
      runSteps (stepMirFn body) fuel
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          tbl.toList) [] :=
  evalWithOpaqueCallees_eq_trusted_unconditional tbl body fuel _
    (MirLiftCore.initMachineStateWithMemoryAndCallees_callees_of_wf body args mem hwf)

/-- **Unconditional agreement from `initMachineStateWithMemoryAndCallees`** for every
non-empty table (an empty table leaves the given memory's callee list in place). -/
theorem evalWithOpaqueCallees_eq_trusted_initWithMemoryAndCallees (tbl : OpaqueCalleeTable)
    (body : CapturedMir) (args : List Value) (mem : Memory) (fuel : Nat)
    (hne : tbl.toList ≠ []) :
    evalWithOpaqueCallees tbl body fuel
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          tbl.toList) =
      runSteps (stepMirFn body) fuel
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          tbl.toList) [] :=
  evalWithOpaqueCallees_eq_trusted_initWithMemoryAndCallees_of_wf tbl body args mem fuel
    (Or.inl hne)

/-- A demanded key carries the trait impls of the state demanding it. -/
theorem demandedKey?_extraTraitImpls {body : CapturedMir} {s : MachineState} {k : CalleeKey}
    (h : demandedKey? body s = some k) : k.extraTraitImpls = s.memory.traitImpls := by
  unfold demandedKey? at h
  split at h
  · unfold terminatorKey? at h
    repeat' (first | (cases h <;> rfl) | split at h)
  · nomatch h

/-- Every demanded key is demanded at a visited state. -/
theorem mem_demandedKeys_visited {resolve : CalleeResolver} {body : CapturedMir} :
    ∀ (fuel : Nat) (s : MachineState) (k : CalleeKey), k ∈ demandedKeys resolve body fuel s →
      ∃ s' ∈ runVisited (stepBranchPruned resolve body) fuel s, demandedKey? body s' = some k
  | 0, _, _, h => nomatch h
  | n + 1, s, k, h => by
    unfold demandedKeys at h
    rcases List.mem_append.mp h with h | h
    · refine ⟨s, by unfold runVisited; exact List.Mem.head _, ?_⟩
      cases hk : demandedKey? body s with
      | none => rw [hk] at h; nomatch h
      | some k' =>
        rw [hk] at h
        rw [List.mem_singleton.mp h]
    · split at h
      · rename_i obs s₁ hv
        obtain ⟨s', hs', hk⟩ := mem_demandedKeys_visited n s₁ k h
        exact ⟨s', by unfold runVisited; rw [hv]; exact List.Mem.tail _ hs', hk⟩
      · nomatch h

/-- **Every key demanded along a pruned run (under any resolver) carries the initial
trait impls**: the `extraTraitImpls` component of the call cone is fixed by the start state. -/
theorem demandedKeys_extraTraitImpls (resolve : CalleeResolver) (body : CapturedMir)
    (fuel : Nat) (s : MachineState) :
    ∀ k ∈ demandedKeys resolve body fuel s, k.extraTraitImpls = s.memory.traitImpls := by
  intro k hk
  obtain ⟨s', hs', hk'⟩ := mem_demandedKeys_visited fuel s k hk
  rw [demandedKey?_extraTraitImpls hk']
  exact (runVisited_frames (stepBranchPruned_frames resolve body) fuel s s' hs').2

/-! ### Bridge to `Anneal.MirLiftCore` call-cone narrowing

`Anneal.MirLiftCore` narrows the trusted machine's *own* callee table: replacing
`Memory.callees = c₁` by any `c₂` with `calleesAgreeOn cone c₁ c₂` (first-match `findCallee?`
agreement on a cone of definition paths) preserves every cone-safe step, bounded run
(`runCfgWithCallees`), and callee-insensitive weakest precondition (`wpMirExecSym`,
`MirWpConverges`). An opaque table plugs into that surface through its sealed list
`tbl.toList : MirLiftCore.CalleeEnv`, with agreement stated over the sealed raw lookup:
`OpaqueCalleeTable.AgreesOn cone t₁ t₂` is exactly `calleesAgreeOn cone t₁.toList
t₂.toList` (`calleesAgreeOn_toList_iff`), so a client discharges it with the same `O(1)`
`lookupRaw` certificates it uses for stepping, never unfolding `tbl.toList`. Conversely,
`AgreesOn` narrows the opaque evaluator's demanded-key cone
(`evalWithOpaqueCallees_cone_narrow_of_agreesOn`), and every halting opaque run is a
halting `runCfgWithCallees` run (`runCfgWithCallees_of_evalWithOpaqueCallees_halted`), which
`MirLiftCore` then narrows to the smaller table. -/

/-- Raw-lookup agreement of two opaque tables on a call cone of definition paths (the
opaque-table form of `MirLiftCore.calleesAgreeOn`). -/
def OpaqueCalleeTable.AgreesOn (cone : List DefPath) (t₁ t₂ : OpaqueCalleeTable) : Prop :=
  ∀ dp, dp ∈ cone → t₁.lookupRaw dp = t₂.lookupRaw dp

theorem OpaqueCalleeTable.AgreesOn.refl (cone : List DefPath) (t : OpaqueCalleeTable) :
    OpaqueCalleeTable.AgreesOn cone t t := fun _ _ => rfl

theorem OpaqueCalleeTable.AgreesOn.symm {cone : List DefPath} {t₁ t₂ : OpaqueCalleeTable}
    (h : OpaqueCalleeTable.AgreesOn cone t₁ t₂) : OpaqueCalleeTable.AgreesOn cone t₂ t₁ :=
  fun dp hdp => (h dp hdp).symm

theorem OpaqueCalleeTable.AgreesOn.trans {cone : List DefPath} {t₁ t₂ t₃ : OpaqueCalleeTable}
    (h₁₂ : OpaqueCalleeTable.AgreesOn cone t₁ t₂) (h₂₃ : OpaqueCalleeTable.AgreesOn cone t₂ t₃) :
    OpaqueCalleeTable.AgreesOn cone t₁ t₃ :=
  fun dp hdp => (h₁₂ dp hdp).trans (h₂₃ dp hdp)

/-- **`AgreesOn` is `MirLiftCore.calleesAgreeOn` on the sealed lists.** -/
theorem calleesAgreeOn_toList_iff (cone : List DefPath) (t₁ t₂ : OpaqueCalleeTable) :
    MirLiftCore.calleesAgreeOn cone t₁.toList t₂.toList ↔ OpaqueCalleeTable.AgreesOn cone t₁ t₂ := by
  constructor
  · intro h dp hdp
    rw [OpaqueCalleeTable.lookupRaw_eq, OpaqueCalleeTable.lookupRaw_eq]
    exact h dp hdp
  · intro h dp hdp
    have := h dp hdp
    rw [OpaqueCalleeTable.lookupRaw_eq, OpaqueCalleeTable.lookupRaw_eq] at this
    exact this

/-- `AgreesOn` gives `MirLiftCore.calleesAgreeOn` on the sealed lists. -/
theorem calleesAgreeOn_of_agreesOn {cone : List DefPath} {t₁ t₂ : OpaqueCalleeTable}
    (h : OpaqueCalleeTable.AgreesOn cone t₁ t₂) :
    MirLiftCore.calleesAgreeOn cone t₁.toList t₂.toList :=
  (calleesAgreeOn_toList_iff cone t₁ t₂).mpr h

/-- A single raw-lookup hit certifies that a sealed table is non-empty (the side condition
of `MirLiftCore`'s entry-state narrowing lemmas), without unfolding `tbl.toList`. -/
theorem toList_ne_nil_of_lookupRaw {tbl : OpaqueCalleeTable} {dp : DefPath} {c : CapturedMir}
    (h : tbl.lookupRaw dp = some c) : tbl.toList ≠ [] := by
  intro hnil
  rw [OpaqueCalleeTable.lookupRaw_eq, hnil] at h
  nomatch h

/-- Canonical cone narrowing of an opaque table: the bodies of `tbl` whose `defPath` lies in
`cone` (`MirLiftCore.coneBodies`), sealed again. -/
def OpaqueCalleeTable.narrowToCone (cone : List DefPath) (tbl : OpaqueCalleeTable) :
    OpaqueCalleeTable :=
  OpaqueCalleeTable.ofList (MirLiftCore.coneBodies cone tbl.toList)

/-- The canonical narrowing agrees with the table on its cone. -/
theorem lookupRaw_narrowToCone {cone : List DefPath} {dp : DefPath} (tbl : OpaqueCalleeTable)
    (hdp : dp ∈ cone) : (tbl.narrowToCone cone).lookupRaw dp = tbl.lookupRaw dp := by
  unfold OpaqueCalleeTable.narrowToCone
  rw [OpaqueCalleeTable.lookupRaw_eq, OpaqueCalleeTable.lookupRaw_eq,
    OpaqueCalleeTable.toList_ofList]
  exact MirLiftCore.findCallee?_coneBodies tbl.toList hdp

/-- `narrowToCone` always agrees with the table on its cone. -/
theorem agreesOn_narrowToCone (cone : List DefPath) (tbl : OpaqueCalleeTable) :
    OpaqueCalleeTable.AgreesOn cone tbl (tbl.narrowToCone cone) :=
  fun _ hdp => (lookupRaw_narrowToCone tbl hdp).symm

/-- A monomorphic key whose path lies in the cone resolves identically in agreeing tables. -/
theorem lookupKey_eq_of_agreesOn_mono {cone : List DefPath} {t₁ t₂ : OpaqueCalleeTable}
    {k : CalleeKey} (h : OpaqueCalleeTable.AgreesOn cone t₁ t₂) (hk : k.defPath ∈ cone)
    (hmono : k.typeArgs = []) : t₁.lookupKey k = t₂.lookupKey k := by
  obtain ⟨L, dp, tys, ti⟩ := k
  simp only at hk hmono
  subst hmono
  rw [OpaqueCalleeTable.lookupKey_eq, OpaqueCalleeTable.lookupKey_eq,
    OpaqueCalleeTable.lookup_eq, OpaqueCalleeTable.lookup_eq]
  exact MirLiftCore.lookupCallee_nil_eq_of_findCallee_eq L ti
    ((calleesAgreeOn_of_agreesOn h) dp hk)

/-- A (possibly polymorphic) key whose path lies in the cone and has no registered
`TraitImplEntry` in either table (stated over the sealed `traitImpls`) resolves identically
in agreeing tables. -/
theorem lookupKey_eq_of_agreesOn_free {cone : List DefPath} {t₁ t₂ : OpaqueCalleeTable}
    {k : CalleeKey} (h : OpaqueCalleeTable.AgreesOn cone t₁ t₂) (hk : k.defPath ∈ cone)
    (h₁ : hasTraitImplForDefPath (k.extraTraitImpls ++ t₁.traitImpls) k.defPath = false)
    (h₂ : hasTraitImplForDefPath (k.extraTraitImpls ++ t₂.traitImpls) k.defPath = false) :
    t₁.lookupKey k = t₂.lookupKey k := by
  obtain ⟨L, dp, tys, ti⟩ := k
  simp only at hk h₁ h₂
  rw [OpaqueCalleeTable.traitImpls_eq] at h₁ h₂
  rw [OpaqueCalleeTable.lookupKey_eq, OpaqueCalleeTable.lookupKey_eq,
    OpaqueCalleeTable.lookup_eq, OpaqueCalleeTable.lookup_eq]
  exact MirLiftCore.lookupCallee_eq_of_findCallee_eq_of_no_traitImpl L tys ti
    ((calleesAgreeOn_of_agreesOn h) dp hk) h₁ h₂

/-- **Cone narrowing of the opaque evaluator from `calleesAgreeOn`**: if every key the
full-table run demands is a monomorphic call into `cone`, raw-lookup agreement on `cone`
(equivalently `MirLiftCore.calleesAgreeOn cone narrowTbl.toList fullTbl.toList`) gives an
identical run. -/
theorem evalWithOpaqueCallees_cone_narrow_of_agreesOn (cone : List DefPath)
    (narrowTbl fullTbl : OpaqueCalleeTable) (body : CapturedMir) (fuel : Nat) (s : MachineState)
    (h : OpaqueCalleeTable.AgreesOn cone narrowTbl fullTbl)
    (hkeys : ∀ k ∈ demandedKeys fullTbl.lookup body fuel s, k.defPath ∈ cone ∧ k.typeArgs = []) :
    evalWithOpaqueCallees narrowTbl body fuel s = evalWithOpaqueCallees fullTbl body fuel s :=
  evalWithOpaqueCallees_cone_narrow narrowTbl fullTbl body fuel s fun k hk =>
    lookupKey_eq_of_agreesOn_mono h (hkeys k hk).1 (hkeys k hk).2

/-- A halting iterated trusted run is a halting `MirFuelFree.runMirExecBounded` run (one more
unit of fuel absorbs the final `.tau (.halted _)` step). -/
theorem runMirExecBounded_of_runSteps_halted (body : CapturedMir) :
    ∀ (fuel : Nat) (s : MachineState) (tr : List MirObs) (out : MirOutcome) (tr' : List MirObs),
      runSteps (stepMirFn body) fuel s tr = .halted out tr' →
        MirFuelFree.runMirExecBounded (fuel + 1) body (.running s) = some out
  | 0, _, _, _, _, h => nomatch h
  | n + 1, s, tr, out, tr', h => by
    unfold runSteps at h
    unfold MirFuelFree.runMirExecBounded
    show (match stepMirFn body s with
      | .ret out => some out
      | .tau st' => MirFuelFree.runMirExecBounded (n + 1) body st'
      | .vis (.inr (.inl _)) k => MirFuelFree.runMirExecBounded (n + 1) body (k PUnit.unit)
      | .vis (.inl _) _ => none
      | .vis (.inr (.inr _)) _ => none) = some out
    revert h
    rcases stepMirFn body s with out' | st | ⟨e, k⟩
    · intro h
      change RunResult.halted out' tr = .halted out tr' at h
      injection h with h
      rw [h]
    · rcases st with s' | out' | fk
      · intro h
        exact runMirExecBounded_of_runSteps_halted body n s' _ out tr' h
      · intro h
        change RunResult.halted out' (tr ++ none.toList) = .halted out tr' at h
        injection h with h
        rw [h]
        rfl
      · intro h
        nomatch h
    · rcases e with fk | x | c
      · cases fk with
        | fail kind => intro h; nomatch h
      · cases x with
        | emit ev =>
          intro h
          show MirFuelFree.runMirExecBounded (n + 1) body (k PUnit.unit) = some out
          have hview : viewStepNode (.vis (.inr (.inl (.emit ev))) k) =
              StepView.cont (some ev) (k PUnit.unit) := rfl
          rw [hview] at h
          revert h
          cases k PUnit.unit with
          | running s' =>
            intro h
            exact runMirExecBounded_of_runSteps_halted body n s' _ out tr' h
          | halted out' =>
            intro h
            injection h with h
            rw [h]
            rfl
          | faulted fk =>
            intro h
            nomatch h
      · cases c with
        | call req => intro h; nomatch h

/-- **Opaque evaluation → `MirLiftCore.runCfgWithCallees`** under `MirLiftCore.CalleeInitWf`
(also covering the empty table over a clean entry memory). -/
theorem runCfgWithCallees_of_evalWithOpaqueCallees_halted_of_wf (tbl : OpaqueCalleeTable)
    (body : CapturedMir) (args : List Value) (mem : Memory) (fuel : Nat) (out : MirOutcome)
    (tr : List MirObs) (hwf : MirLiftCore.CalleeInitWf body mem tbl.toList)
    (h : evalWithOpaqueCallees tbl body fuel
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
        tbl.toList) = .halted out tr) :
    MirLiftCore.runCfgWithCallees (fuel + 1) body args mem tbl.toList = some out := by
  rw [evalWithOpaqueCallees_eq_trusted_initWithMemoryAndCallees_of_wf tbl body args mem fuel hwf]
    at h
  exact runMirExecBounded_of_runSteps_halted body fuel _ [] out tr h

/-- **Opaque evaluation → `MirLiftCore.runCfgWithCallees`**: a halting branch-pruned opaque
run from the multi-callee entry state of a non-empty table is a halting
`runCfgWithCallees` run with the sealed list, which `MirLiftCore` narrows further
(`runCfgWithCallees_cone_narrow_of_agreesOn`). -/
theorem runCfgWithCallees_of_evalWithOpaqueCallees_halted (tbl : OpaqueCalleeTable)
    (body : CapturedMir) (args : List Value) (mem : Memory) (fuel : Nat) (out : MirOutcome)
    (tr : List MirObs) (hne : tbl.toList ≠ [])
    (h : evalWithOpaqueCallees tbl body fuel
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
        tbl.toList) = .halted out tr) :
    MirLiftCore.runCfgWithCallees (fuel + 1) body args mem tbl.toList = some out :=
  runCfgWithCallees_of_evalWithOpaqueCallees_halted_of_wf tbl body args mem fuel out tr
    (Or.inl hne) h

/-- **`runCfgWithCallees` narrowing between opaque tables** (`MirLiftCore.runCfgWithCallees_cone_narrow`
with agreement over `lookupRaw`). -/
theorem runCfgWithCallees_cone_narrow_of_agreesOn (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : t₁.toList ≠ []) (h₂ : t₂.toList ≠ []) (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (h_reach : MirLiftCore.ConeReach body (MirLiftCore.StepConeSafe cone body) fuel
      (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
        t₁.toList))) :
    MirLiftCore.runCfgWithCallees fuel body args mem t₂.toList =
      (MirLiftCore.runCfgWithCallees fuel body args mem t₁.toList).map
        (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList)) :=
  MirLiftCore.runCfgWithCallees_cone_narrow cone fuel body args mem h₁ h₂
    (calleesAgreeOn_of_agreesOn h_agree) h_reach

/-- **Syntactic `runCfgWithCallees` narrowing between opaque tables** under the decidable
`MirLiftCore.CallConeClosed` check (no `ConeReach` obligation). -/
theorem runCfgWithCallees_cone_narrow_of_agreesOn_closed (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : t₁.toList ≠ []) (h₂ : t₂.toList ≠ []) (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (h_closed : MirLiftCore.CallConeClosed cone body t₁.toList = true)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = []) :
    MirLiftCore.runCfgWithCallees fuel body args mem t₂.toList =
      (MirLiftCore.runCfgWithCallees fuel body args mem t₁.toList).map
        (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList)) :=
  MirLiftCore.runCfgWithCallees_cone_narrow_of_closed cone fuel body args mem h₁ h₂
    (calleesAgreeOn_of_agreesOn h_agree) h_closed h_ac h_cs

/-- **`wpMirExecSym` narrowing between opaque tables**: every callee-insensitive
postcondition transfers between the multi-callee entry states of agreeing tables. -/
theorem wpMirExecSym_cone_narrow_of_agreesOn (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : t₁.toList ≠ []) (h₂ : t₂.toList ≠ []) (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (post : MirOutcome → Prop)
    (h_post : ∀ out,
      post (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList) out) ↔ post out)
    (h_reach : MirLiftCore.ConeReach body (MirLiftCore.StepConeSafe cone body) fuel
      (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
        t₁.toList))) :
    Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₂.toList)) post ↔
      Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₁.toList)) post :=
  MirLiftCore.wpMirExecSym_cone_narrow_init cone fuel body args mem h₁ h₂
    (calleesAgreeOn_of_agreesOn h_agree) post h_post h_reach

/-- **`MirWpConverges` narrowing between opaque tables.** -/
theorem mirWpConverges_cone_narrow_of_agreesOn (cone : List DefPath) (body : CapturedMir)
    (args : List Value) (mem : Memory) {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : t₁.toList ≠ []) (h₂ : t₂.toList ≠ []) (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (post : MirOutcome → Prop)
    (h_post : ∀ out,
      post (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList) out) ↔ post out)
    (h_reach : ∀ fuel, MirLiftCore.ConeReach body (MirLiftCore.StepConeSafe cone body) fuel
      (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
        t₁.toList))) :
    MirFuelFree.MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₂.toList) post ↔
      MirFuelFree.MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₁.toList) post :=
  MirLiftCore.mirWpConverges_cone_narrow_init cone body args mem h₁ h₂
    (calleesAgreeOn_of_agreesOn h_agree) post h_post h_reach

/-- A single raw-lookup hit discharges `MirLiftCore.CalleeInitWf` for a sealed table. -/
theorem calleeInitWf_of_lookupRaw {tbl : OpaqueCalleeTable} {dp : DefPath} {c : CapturedMir}
    (body : CapturedMir) (mem : Memory) (h : tbl.lookupRaw dp = some c) :
    MirLiftCore.CalleeInitWf body mem tbl.toList :=
  Or.inl (toList_ne_nil_of_lookupRaw h)

/-- **Syntactic `runCfgWithCallees` narrowing between opaque tables, down to the empty table**
(`MirLiftCore.runCfgWithCallees_cone_narrow_of_closed_wf` with agreement over `lookupRaw`). -/
theorem runCfgWithCallees_cone_narrow_of_agreesOn_closed_wf (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : MirLiftCore.CalleeInitWf body mem t₁.toList)
    (h₂ : MirLiftCore.CalleeInitWf body mem t₂.toList)
    (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (h_closed : MirLiftCore.CallConeClosed cone body t₁.toList = true)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = []) :
    MirLiftCore.runCfgWithCallees fuel body args mem t₂.toList =
      (MirLiftCore.runCfgWithCallees fuel body args mem t₁.toList).map
        (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList)) :=
  MirLiftCore.runCfgWithCallees_cone_narrow_of_closed_wf cone fuel body args mem h₁ h₂
    (calleesAgreeOn_of_agreesOn h_agree) h_closed h_ac h_cs

/-- **Syntactic `wpMirExecSym` narrowing between opaque tables, down to the empty table.** -/
theorem wpMirExecSym_cone_narrow_of_agreesOn_closed_wf (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : MirLiftCore.CalleeInitWf body mem t₁.toList)
    (h₂ : MirLiftCore.CalleeInitWf body mem t₂.toList)
    (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (h_closed : MirLiftCore.CallConeClosed cone body t₁.toList = true)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out,
      post (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList) out) ↔ post out) :
    Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₂.toList)) post ↔
      Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₁.toList)) post :=
  MirLiftCore.wpMirExecSym_cone_narrow_of_closed_wf cone fuel body args mem h₁ h₂
    (calleesAgreeOn_of_agreesOn h_agree) h_closed h_ac h_cs post h_post

/-- **Syntactic `MirWpConverges` narrowing between opaque tables, down to the empty table.** -/
theorem mirWpConverges_cone_narrow_of_agreesOn_closed_wf (cone : List DefPath)
    (body : CapturedMir) (args : List Value) (mem : Memory) {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : MirLiftCore.CalleeInitWf body mem t₁.toList)
    (h₂ : MirLiftCore.CalleeInitWf body mem t₂.toList)
    (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (h_closed : MirLiftCore.CallConeClosed cone body t₁.toList = true)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out,
      post (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList) out) ↔ post out) :
    MirFuelFree.MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₂.toList) post ↔
      MirFuelFree.MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₁.toList) post :=
  MirLiftCore.mirWpConverges_cone_narrow_of_closed_wf cone body args mem h₁ h₂
    (calleesAgreeOn_of_agreesOn h_agree) h_closed h_ac h_cs post h_post

/-- The `MirLiftCore` trait-impl side condition stated over the sealed `traitImpls`. -/
theorem noTraitImplInCone_toList {cone : List DefPath} {ti : List TraitImplEntry}
    {tbl : OpaqueCalleeTable}
    (h : ∀ dp, dp ∈ cone → hasTraitImplForDefPath (ti ++ tbl.traitImpls) dp = false) :
    ∀ dp, dp ∈ cone → hasTraitImplForDefPath (ti ++ flatMapTraitImpls tbl.toList) dp = false := by
  rw [← OpaqueCalleeTable.traitImpls_eq]
  exact h

/-- **Polymorphic syntactic `runCfgWithCallees` narrowing between opaque tables**
(`MirLiftCore.runCfgWithCallees_cone_narrow_of_closed_poly_wf`): generic callees and
polymorphic inline intrinsics in the cone, with the narrowed table's trait-impl side condition
stated over the sealed `traitImpls`. -/
theorem runCfgWithCallees_cone_narrow_of_agreesOn_closed_poly_wf (cone : List DefPath)
    (fuel : Nat) (body : CapturedMir) (args : List Value) (mem : Memory)
    {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : MirLiftCore.CalleeInitWf body mem t₁.toList)
    (h₂ : MirLiftCore.CalleeInitWf body mem t₂.toList)
    (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (h_closed : MirLiftCore.CallConeClosedPoly cone body t₁.toList body.traitImpls = true)
    (h_no₂ : ∀ dp, dp ∈ cone →
      hasTraitImplForDefPath (body.traitImpls ++ t₂.traitImpls) dp = false)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = []) :
    MirLiftCore.runCfgWithCallees fuel body args mem t₂.toList =
      (MirLiftCore.runCfgWithCallees fuel body args mem t₁.toList).map
        (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList)) :=
  MirLiftCore.runCfgWithCallees_cone_narrow_of_closed_poly_wf cone fuel body args mem h₁ h₂
    (calleesAgreeOn_of_agreesOn h_agree) h_closed (noTraitImplInCone_toList h_no₂) h_ac h_cs

/-- **Polymorphic syntactic `wpMirExecSym` narrowing between opaque tables.** -/
theorem wpMirExecSym_cone_narrow_of_agreesOn_closed_poly_wf (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : MirLiftCore.CalleeInitWf body mem t₁.toList)
    (h₂ : MirLiftCore.CalleeInitWf body mem t₂.toList)
    (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (h_closed : MirLiftCore.CallConeClosedPoly cone body t₁.toList body.traitImpls = true)
    (h_no₂ : ∀ dp, dp ∈ cone →
      hasTraitImplForDefPath (body.traitImpls ++ t₂.traitImpls) dp = false)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out,
      post (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList) out) ↔ post out) :
    Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₂.toList)) post ↔
      Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₁.toList)) post :=
  MirLiftCore.wpMirExecSym_cone_narrow_of_closed_poly_wf cone fuel body args mem h₁ h₂
    (calleesAgreeOn_of_agreesOn h_agree) h_closed (noTraitImplInCone_toList h_no₂) h_ac h_cs
    post h_post

/-- **Polymorphic syntactic `MirWpConverges` narrowing between opaque tables.** -/
theorem mirWpConverges_cone_narrow_of_agreesOn_closed_poly_wf (cone : List DefPath)
    (body : CapturedMir) (args : List Value) (mem : Memory) {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : MirLiftCore.CalleeInitWf body mem t₁.toList)
    (h₂ : MirLiftCore.CalleeInitWf body mem t₂.toList)
    (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (h_closed : MirLiftCore.CallConeClosedPoly cone body t₁.toList body.traitImpls = true)
    (h_no₂ : ∀ dp, dp ∈ cone →
      hasTraitImplForDefPath (body.traitImpls ++ t₂.traitImpls) dp = false)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out,
      post (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList) out) ↔ post out) :
    MirFuelFree.MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₂.toList) post ↔
      MirFuelFree.MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₁.toList) post :=
  MirLiftCore.mirWpConverges_cone_narrow_of_closed_poly_wf cone body args mem h₁ h₂
    (calleesAgreeOn_of_agreesOn h_agree) h_closed (noTraitImplInCone_toList h_no₂) h_ac h_cs
    post h_post

/-! #### `tbl.toList`-free syntactic call-cone closure (`callConeClosed` & `callConeClosedPoly`)

`MirLiftCore.CallConeClosed` and `MirLiftCore.CallConeClosedPoly` scan `coneBodies cone tbl.toList`
and `flatMapTraitImpls tbl.toList`, which (a) forces `tbl.toList` to be unfolded across all `M`
callees at the use site and (b) inspects *shadowed* duplicate `DefPath` entries in `tbl.toList`
that `findCallee?` / `lookupRaw` can never return.

`OpaqueCalleeTable.callConeClosed` and `OpaqueCalleeTable.callConeClosedPoly` instead query only
`tbl.lookupRaw dp` for `dp ∈ cone` and the sealed `tbl.traitImpls`, so a client discharges cone
closure in `O(|cone|)` rewrites using the same `lookupRaw` and `traitImpls` certificates it uses
for stepping — never unfolding `tbl.toList`, invariant under `OpaqueCalleeTable.AgreesOn cone`,
and strictly more general when `tbl` contains shadowed duplicate entries. -/

/-- **`tbl.toList`-free syntactic call-cone closure**: checks `root` and the first-match body
`tbl.lookupRaw dp` for each `dp ∈ cone`. -/
def OpaqueCalleeTable.callConeClosed (cone : List DefPath) (root : CapturedMir)
    (tbl : OpaqueCalleeTable) : Bool :=
  MirLiftCore.bodyCallsInCone cone root &&
    cone.all (fun dp =>
      match tbl.lookupRaw dp with
      | some b => MirLiftCore.bodyCallsInCone cone b
      | none => true)

/-- **`tbl.toList`-free polymorphic syntactic call-cone closure**: checks `root`, the first-match
body `tbl.lookupRaw dp` for each `dp ∈ cone`, and absence of trait-impl dispatch over the sealed
`tbl.traitImpls`. -/
def OpaqueCalleeTable.callConeClosedPoly (cone : List DefPath) (root : CapturedMir)
    (tbl : OpaqueCalleeTable) (ti : List TraitImplEntry := []) : Bool :=
  MirLiftCore.bodyCallsInConePoly cone root &&
    cone.all (fun dp =>
      (match tbl.lookupRaw dp with
       | some b => MirLiftCore.bodyCallsInConePoly cone b
       | none => true) &&
      !hasTraitImplForDefPath (ti ++ tbl.traitImpls) dp)

theorem listAll_congr {α : Type} {f g : α → Bool} :
    ∀ {xs : List α}, (∀ x ∈ xs, f x = g x) → xs.all f = xs.all g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.all_cons, h x (List.Mem.head _),
      listAll_congr (fun y hy => h y (List.Mem.tail _ hy))]

/-- `callConeClosed` is invariant under `OpaqueCalleeTable.AgreesOn cone` (unlike
`MirLiftCore.CallConeClosed`, which also scans shadowed duplicate entries in `coneBodies`). -/
theorem callConeClosed_congr_of_agreesOn {cone : List DefPath} {t₁ t₂ : OpaqueCalleeTable}
    (root : CapturedMir) (h : OpaqueCalleeTable.AgreesOn cone t₁ t₂) :
    t₁.callConeClosed cone root = t₂.callConeClosed cone root := by
  unfold OpaqueCalleeTable.callConeClosed
  congr 1
  exact listAll_congr fun dp hdp => by rw [h dp hdp]

/-- `callConeClosedPoly` is invariant under `OpaqueCalleeTable.AgreesOn cone` and agreement of
`hasTraitImplForDefPath` on `cone`. -/
theorem callConeClosedPoly_congr_of_agreesOn {cone : List DefPath} {t₁ t₂ : OpaqueCalleeTable}
    (root : CapturedMir) (ti : List TraitImplEntry) (h : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (ht : ∀ dp, dp ∈ cone →
      hasTraitImplForDefPath (ti ++ t₁.traitImpls) dp =
        hasTraitImplForDefPath (ti ++ t₂.traitImpls) dp) :
    t₁.callConeClosedPoly cone root ti = t₂.callConeClosedPoly cone root ti := by
  unfold OpaqueCalleeTable.callConeClosedPoly
  congr 1
  exact listAll_congr fun dp hdp => by rw [h dp hdp, ht dp hdp]

/-- `MirLiftCore.CallConeClosed` implies `OpaqueCalleeTable.callConeClosed` (the converse can fail
when `tbl.toList` contains a shadowed duplicate entry with `defPath ∈ cone`). -/
theorem callConeClosed_of_mirLiftCore {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} (h : MirLiftCore.CallConeClosed cone root tbl.toList = true) :
    tbl.callConeClosed cone root = true := by
  unfold MirLiftCore.CallConeClosed at h
  rw [Bool.and_eq_true] at h
  unfold OpaqueCalleeTable.callConeClosed
  rw [Bool.and_eq_true]
  refine ⟨h.1, List.all_eq_true.mpr fun dp hdp => ?_⟩
  cases hraw : tbl.lookupRaw dp with
  | none => rfl
  | some b =>
    rw [OpaqueCalleeTable.lookupRaw_eq] at hraw
    obtain ⟨hm, hd⟩ := MirLiftCore.findCallee?_spec hraw
    apply List.all_eq_true.mp h.2 b
    unfold MirLiftCore.coneBodies
    rw [List.mem_filter]
    exact ⟨hm, MirLiftCore.inCone_iff.mpr (hd ▸ hdp)⟩

/-- `MirLiftCore.CallConeClosedPoly` implies `OpaqueCalleeTable.callConeClosedPoly`. -/
theorem callConeClosedPoly_of_mirLiftCore {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {ti : List TraitImplEntry}
    (h : MirLiftCore.CallConeClosedPoly cone root tbl.toList ti = true) :
    tbl.callConeClosedPoly cone root ti = true := by
  unfold MirLiftCore.CallConeClosedPoly at h
  simp only [Bool.and_eq_true] at h
  unfold OpaqueCalleeTable.callConeClosedPoly
  rw [Bool.and_eq_true]
  refine ⟨h.1.1, List.all_eq_true.mpr fun dp hdp => ?_⟩
  rw [Bool.and_eq_true, OpaqueCalleeTable.traitImpls_eq]
  refine ⟨?_, List.all_eq_true.mp h.2 dp hdp⟩
  cases hraw : tbl.lookupRaw dp with
  | none => rfl
  | some b =>
    rw [OpaqueCalleeTable.lookupRaw_eq] at hraw
    obtain ⟨hm, hd⟩ := MirLiftCore.findCallee?_spec hraw
    apply List.all_eq_true.mp h.1.2 b
    unfold MirLiftCore.coneBodies
    rw [List.mem_filter]
    exact ⟨hm, MirLiftCore.inCone_iff.mpr (hd ▸ hdp)⟩

/-- `b` is the root body or the first-match body `tbl.lookupRaw dp = some b` for some `dp ∈ cone`. -/
def InConeLookup (cone : List DefPath) (root : CapturedMir) (tbl : OpaqueCalleeTable)
    (b : CapturedMir) : Prop :=
  b = root ∨ ∃ dp, dp ∈ cone ∧ tbl.lookupRaw dp = some b

/-- Reachable-state invariant of a `callConeClosed` execution over `tbl`. -/
def ClosedInvLookup (cone : List DefPath) (root : CapturedMir) (tbl : OpaqueCalleeTable)
    (s : MachineState) : Prop :=
  s.memory.callees = tbl.toList ∧
    InConeLookup cone root tbl (s.memory.activeCallee.getD root) ∧
    ∀ f, f ∈ s.memory.callStack → InConeLookup cone root tbl f.callerBody

theorem bodyCallsInCone_of_inConeLookup {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {b : CapturedMir}
    (h_closed : tbl.callConeClosed cone root = true)
    (hb : InConeLookup cone root tbl b) : MirLiftCore.bodyCallsInCone cone b = true := by
  unfold OpaqueCalleeTable.callConeClosed at h_closed
  rw [Bool.and_eq_true] at h_closed
  rcases hb with rfl | ⟨dp, hdp, hraw⟩
  · exact h_closed.1
  · have h := List.all_eq_true.mp h_closed.2 dp hdp
    rw [hraw] at h
    exact h

theorem stepConeSafe_of_closedInvLookup {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {s : MachineState}
    (h_closed : tbl.callConeClosed cone root = true)
    (h_inv : ClosedInvLookup cone root tbl s) : MirLiftCore.StepConeSafe cone root s := by
  intro blk h_bb
  have h_body := bodyCallsInCone_of_inConeLookup h_closed h_inv.2.1
  unfold MirLiftCore.bodyCallsInCone at h_body
  have h_blk := List.all_eq_true.mp h_body blk (List.mem_of_getElem? h_bb)
  rw [Bool.and_eq_true] at h_blk
  exact ⟨fun stmt h_st => List.all_eq_true.mp h_blk.1 stmt (List.mem_of_getElem? h_st),
    MirLiftCore.termConeSafe_of_termCallsInCone h_blk.2⟩

theorem closedInvLookup_of_callerBodies {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {s s' : MachineState}
    (h_inv : ClosedInvLookup cone root tbl s)
    (hc : s'.memory.callees = s.memory.callees)
    (hac : s'.memory.activeCallee = s.memory.activeCallee)
    (hb : MirLiftCore.CallerBodiesEq s.memory.callStack s'.memory.callStack) :
    ClosedInvLookup cone root tbl s' := by
  refine ⟨hc.trans h_inv.1, hac ▸ h_inv.2.1, ?_⟩
  intro f hf
  obtain ⟨f₀, hf₀, he⟩ := hb.mem hf
  exact he ▸ h_inv.2.2 f₀ hf₀

theorem nodeSuccs_closedInvLookup_of_ctx {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {s : MachineState} {n : MirStepNode}
    (h_inv : ClosedInvLookup cone root tbl s)
    (hfix : n = MirLiftCore.MirStepNode.mapMem
      (MirLiftCore.Memory.withCalleeCtx s.memory.callees s.memory.activeCallee
        s.memory.traitImpls) n)
    (hb : MirLiftCore.NodeSuccs
      (fun s' => MirLiftCore.CallerBodiesEq s.memory.callStack s'.memory.callStack) n) :
    MirLiftCore.NodeSuccs (ClosedInvLookup cone root tbl) n := by
  refine MirLiftCore.NodeSuccs.mono ?_
    (MirLiftCore.NodeSuccs.and
      (MirLiftCore.nodeSuccs_of_fixed (P := fun s' => s' = MirLiftCore.MachineState.mapMem
        (MirLiftCore.Memory.withCalleeCtx s.memory.callees s.memory.activeCallee
          s.memory.traitImpls) s')
        hfix (fun _ h => h))
      hb)
  rintro s' ⟨hs', hb'⟩
  have hm : s'.memory =
      MirLiftCore.Memory.withCalleeCtx s.memory.callees s.memory.activeCallee
        s.memory.traitImpls s'.memory :=
    congrArg MachineState.memory hs'
  exact closedInvLookup_of_callerBodies h_inv (by rw [hm]) (by rw [hm]) hb'

theorem closedInvLookup_return {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {s : MachineState} {caller : SavedCallerFrame}
    {rest : List SavedCallerFrame} {retVal : Value} {locals' : List LocalSlot} {mem' : Memory}
    {F : StackFrame}
    (h_inv : ClosedInvLookup cone root tbl s) (h_cs : s.memory.callStack = caller :: rest)
    (h_w : writeReturnDestination caller.frame.locals (MirLiftCore.ccReturnCallerMem s caller rest)
      caller.destination retVal caller.callerBody.localDecls caller.callerBody.layouts =
        .ok locals' mem') :
    ClosedInvLookup cone root tbl { frame := F, memory := mem' } := by
  obtain ⟨hc, hac, _⟩ := MirLiftCore.writeReturnDestination_ctx_preserved h_w
  have hb := MirLiftCore.writeReturnDestination_callerBodies h_w
  refine ⟨hc.trans h_inv.1, ?_, ?_⟩
  · show InConeLookup cone root tbl (mem'.activeCallee.getD root)
    rw [hac]
    exact h_inv.2.2 caller (by rw [h_cs]; exact List.Mem.head _)
  · intro f hf
    obtain ⟨f₀, hf₀, he⟩ := hb.mem hf
    exact he ▸ h_inv.2.2 f₀ (by rw [h_cs]; exact List.Mem.tail _ hf₀)

theorem closedInvLookup_unwindFromCallStack {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} :
    ∀ (stk : List SavedCallerFrame) (m : Memory), m.callees = tbl.toList →
      (∀ f, f ∈ stk → InConeLookup cone root tbl f.callerBody) →
      ∀ s', unwindFromCallStack stk m = .running s' → ClosedInvLookup cone root tbl s'
  | [], _, _, _, _, h => by cases h
  | caller :: rest, m, hc, hf, s', h => by
    unfold unwindFromCallStack at h
    dsimp only at h
    cases hr : caller.returnUnwind with
    | unreachable => rw [hr] at h; dsimp only at h; cases h
    | terminate => rw [hr] at h; dsimp only at h; cases h
    | continue_ =>
      rw [hr] at h
      dsimp only at h
      exact closedInvLookup_unwindFromCallStack rest
        { m with
          callStack := rest
          activeCallee := some caller.callerBody
          activeProtectors := restoreCallerProtectors caller }
        hc (fun f hm => hf f (List.Mem.tail _ hm)) s' h
    | cleanup bb =>
      rw [hr] at h
      dsimp only at h
      cases h
      exact ⟨hc, hf caller (List.Mem.head _), fun f hm => hf f (List.Mem.tail _ hm)⟩

private theorem nodeSuccs_unwindMatchLookup {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} (st : MirExecState)
    (h : ∀ s', st = .running s' → ClosedInvLookup cone root tbl s') :
    MirLiftCore.NodeSuccs (ClosedInvLookup cone root tbl)
      (match (generalizing := false) st with
        | .running nextState => MirStepNode.step nextState
        | .halted out => MirStepNode.retOutcome out
        | .faulted fk => MirStepNode.fail fk) := by
  cases st with
  | running s' => exact h s' rfl
  | halted _ => trivial
  | faulted _ => trivial

private theorem nodeSuccs_applyUnwindLookup {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {s : MachineState} (h_inv : ClosedInvLookup cone root tbl s)
    (l : List LocalSlot) (u : UnwindAction) :
    MirLiftCore.NodeSuccs (ClosedInvLookup cone root tbl)
      (match applyUnwindAction s l s.memory u with
        | .running nextState => MirStepNode.step nextState
        | .halted out => MirStepNode.retOutcome out
        | .faulted fk => MirStepNode.fail fk) := by
  refine nodeSuccs_unwindMatchLookup _ ?_
  intro s' hs'
  cases u with
  | unreachable => cases hs'
  | terminate => cases hs'
  | continue_ =>
    exact closedInvLookup_unwindFromCallStack s.memory.callStack s.memory h_inv.1 h_inv.2.2 s' hs'
  | cleanup bb =>
    cases hs'
    exact h_inv

private theorem inConeLookup_of_lookup {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {L : LayoutTable} {dp : DefPath} {ti : List TraitImplEntry}
    {b : CapturedMir} (h_dp : dp ∈ cone) (h_lk : lookupCallee tbl.toList L dp [] ti = some b) :
    InConeLookup cone root tbl b :=
  Or.inr ⟨dp, h_dp,
    (OpaqueCalleeTable.lookupRaw_eq tbl dp).trans (MirLiftCore.lookupCallee_nil_eq_some h_lk)⟩

private theorem closedInvLookup_push {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {s : MachineState} {saved : SavedCallerFrame} {b : CapturedMir}
    {F : StackFrame} (h_inv : ClosedInvLookup cone root tbl s)
    (h_saved : InConeLookup cone root tbl saved.callerBody)
    (h_b : InConeLookup cone root tbl b) :
    ClosedInvLookup cone root tbl
      { frame := F,
        memory := { s.memory with
          callStack := saved :: s.memory.callStack
          activeCallee := some b } } := by
  refine ⟨h_inv.1, h_b, ?_⟩
  intro f hf
  cases hf with
  | head => exact h_saved
  | tail _ hf => exact h_inv.2.2 f hf

theorem nodeSuccs_evalDirectRustIntrinsic?_lookup {cone : List DefPath}
    {root : CapturedMir} {tbl : OpaqueCalleeTable} {s : MachineState}
    (h_inv : ClosedInvLookup cone root tbl s) (currentBody : Option CapturedMir)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (unwind : UnwindAction)
    (h_cl : MirLiftCore.isNonSelectIntrinsicOpt (classifyRustIntrinsic? target.defPath) = true)
    (fallback : MirStepNode) (h_fb : MirLiftCore.NodeSuccs (ClosedInvLookup cone root tbl) fallback) :
    MirLiftCore.NodeSuccs (ClosedInvLookup cone root tbl)
      (match evalDirectRustIntrinsic? s currentBody target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb unwind with
       | some stepNode => stepNode
       | none => fallback) := by
  unfold evalDirectRustIntrinsic?
  cases h_k : classifyRustIntrinsic? target.defPath with
  | none => exact h_fb
  | some kind =>
    rw [h_k] at h_cl
    have h_step : ∀ (k : RustIntrinsicKind),
        MirLiftCore.NodeSuccs (ClosedInvLookup cone root tbl)
          (evalNonSelectIntrinsicCall k s target bodyLocalDecls bodyLayouts
            argOps argVals locals' destination targetBb) := by
      intro k
      exact nodeSuccs_closedInvLookup_of_ctx h_inv
        (MirLiftCore.evalNonSelectIntrinsicCall_calleeCtx_preserved k s target bodyLocalDecls
          bodyLayouts argOps argVals locals' destination targetBb)
        (MirLiftCore.evalNonSelectIntrinsicCall_callerBodies k s target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb)
    cases kind with
    | constEvalSelect => cases h_cl
    | _ => exact h_step _

theorem nodeSuccs_evalTerminatorLookup {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {s : MachineState} {term : Terminator}
    (h_inv : ClosedInvLookup cone root tbl s)
    (h_term : MirLiftCore.TermConeSafe cone s (s.memory.activeCallee.getD root) term) :
    MirLiftCore.NodeSuccs (ClosedInvLookup cone root tbl)
      (evalTerminator s term (some (s.memory.activeCallee.getD root))) := by
  have h_cur : InConeLookup cone root tbl (s.memory.activeCallee.getD root) := h_inv.2.1
  rcases term with ⟨kind, span⟩
  cases kind with
  | goto target => exact h_inv
  | switchInt discr targets =>
    unfold evalTerminator; dsimp only
    repeat' (first | trivial | exact h_inv | split)
  | unwindResume =>
    unfold evalTerminator; dsimp only
    exact nodeSuccs_unwindMatchLookup _
      (closedInvLookup_unwindFromCallStack s.memory.callStack s.memory h_inv.1 h_inv.2.2)
  | unwindTerminate => trivial
  | return_ =>
    rw [MirLiftCore.ccEvalReturn_eq]
    unfold MirLiftCore.ccEvalReturn
    repeat' (first | trivial | exact closedInvLookup_return h_inv ‹_› ‹_› | split)
  | unreachable => trivial
  | drop place target unwind =>
    unfold evalTerminator; dsimp only
    repeat' (first | trivial | exact h_inv | split)
  | assert cond expected target unwind =>
    unfold evalTerminator; dsimp only
    repeat' (first | trivial | exact h_inv | exact nodeSuccs_applyUnwindLookup h_inv _ _ | split)
  | call func argOps destination target unwind =>
    have hq : MirLiftCore.CallTargetInCone cone s (s.memory.activeCallee.getD root) func
        (length argOps) := h_term
    cases target with
    | some targetBb =>
      unfold evalTerminator; dsimp only
      cases h_res : resolveCallTarget s func (length argOps)
          (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root)))
          (s.memory.activeCallee.getD root).layouts with
      | ub => trivial
      | unsupported => trivial
      | ok tgt localsAfterFunc =>
        obtain ⟨h_dp, h_ta, h_cl⟩ := hq tgt localsAfterFunc h_res
        dsimp only
        cases evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
            (s.memory.activeCallee.getD root).layouts s.memory.callerLocals
            (callStack := s.memory.callStack) with
        | ub => trivial
        | unsupported => trivial
        | ok argVals locals' =>
          dsimp only
          rw [h_ta]
          cases h_lk : lookupCallee s.memory.callees (s.memory.activeCallee.getD root).layouts
              tgt.defPath [] s.memory.traitImpls with
          | some calleeBody =>
            dsimp only
            cases checkCalleeTargetCompatible tgt calleeBody (length argVals) with
            | false => trivial
            | true =>
              rw [h_inv.1] at h_lk
              exact closedInvLookup_push h_inv h_cur (inConeLookup_of_lookup h_dp h_lk)
          | none =>
            dsimp only
            repeat' (first
              | trivial | exact h_inv
              | exact nodeSuccs_closedInvLookup_of_ctx h_inv
                  (MirLiftCore.writeIntrinsicReturn_calleeCtx_preserved _ _ _ _ _)
                  (MirLiftCore.writeIntrinsicReturn_callerBodies _ _ _ _ _)
              | exact nodeSuccs_evalDirectRustIntrinsic?_lookup h_inv _ _ _ _ _ _ _ _ _ _ h_cl _
                  (by
                    repeat' (first
                      | trivial | exact h_inv
                      | exact nodeSuccs_closedInvLookup_of_ctx h_inv
                          (MirLiftCore.writeIntrinsicReturn_calleeCtx_preserved _ _ _ _ _)
                          (MirLiftCore.writeIntrinsicReturn_callerBodies _ _ _ _ _)
                      | split))
              | split)
    | none =>
      unfold evalTerminator; dsimp only
      cases h_res : resolveCallTarget s func (length argOps)
          (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root)))
          (s.memory.activeCallee.getD root).layouts with
      | ub => trivial
      | unsupported => trivial
      | ok tgt localsAfterFunc =>
        obtain ⟨h_dp, h_ta, h_cl⟩ := hq tgt localsAfterFunc h_res
        dsimp only
        cases evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
            (s.memory.activeCallee.getD root).layouts s.memory.callerLocals
            (callStack := s.memory.callStack) with
        | ub => trivial
        | unsupported => trivial
        | ok argVals locals' =>
          dsimp only
          rw [h_ta]
          cases h_lk : lookupCallee s.memory.callees (s.memory.activeCallee.getD root).layouts
              tgt.defPath [] s.memory.traitImpls with
          | some calleeBody =>
            dsimp only
            cases checkCalleeTargetCompatible tgt calleeBody (length argVals) with
            | false => trivial
            | true =>
              rw [h_inv.1] at h_lk
              exact closedInvLookup_push h_inv h_cur (inConeLookup_of_lookup h_dp h_lk)
          | none =>
            dsimp only
            repeat' (first | trivial | exact nodeSuccs_applyUnwindLookup h_inv _ _ | split)
  | tailCall func argOps =>
    have hq : MirLiftCore.CallTargetInCone cone s (s.memory.activeCallee.getD root) func
        (length argOps) := h_term
    unfold evalTerminator; dsimp only
    unfold evalTailCallTerminator; dsimp only
    cases h_res : resolveCallTarget s func (length argOps)
        (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root)))
        (s.memory.activeCallee.getD root).layouts with
    | ub => trivial
    | unsupported => trivial
    | ok tgt localsAfterFunc =>
      obtain ⟨h_dp, h_ta, _⟩ := hq tgt localsAfterFunc h_res
      dsimp only
      cases evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
          (s.memory.activeCallee.getD root).layouts s.memory.callerLocals
          (callStack := s.memory.callStack) with
      | ub => trivial
      | unsupported => trivial
      | ok argVals locals' =>
        dsimp only
        rw [h_ta]
        cases h_lk : lookupCallee s.memory.callees (s.memory.activeCallee.getD root).layouts
            tgt.defPath [] s.memory.traitImpls with
        | some calleeBody =>
          dsimp only
          rw [h_inv.1] at h_lk
          repeat' (first
            | trivial
            | exact ⟨h_inv.1, inConeLookup_of_lookup h_dp h_lk, h_inv.2.2⟩
            | split)
        | none =>
          dsimp only
          repeat' (first | trivial | split)
  | _ => trivial

theorem nodeSuccs_stepMirFnLookup {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {s : MachineState}
    (h_closed : tbl.callConeClosed cone root = true)
    (h_inv : ClosedInvLookup cone root tbl s) :
    MirLiftCore.NodeSuccs (ClosedInvLookup cone root tbl) (stepMirFn root s) := by
  have h_safe := stepConeSafe_of_closedInvLookup h_closed h_inv
  unfold stepMirFn; dsimp only
  split
  · trivial
  · cases h_bb : get? (s.memory.activeCallee.getD root).basicBlocks s.frame.blockIdx with
    | none => trivial
    | some blk =>
      obtain ⟨h_stmt, h_term⟩ := h_safe blk h_bb
      dsimp only
      cases h_st : get? blk.statements s.frame.stmtIdx with
      | some stmt =>
        dsimp only
        exact nodeSuccs_closedInvLookup_of_ctx h_inv
          (MirLiftCore.evalStmt_calleeCtx_preserved s stmt _ _ (h_stmt stmt h_st))
          (MirLiftCore.evalStmt_callerBodies s stmt _ _)
      | none =>
        dsimp only
        by_cases h_end : (s.frame.stmtIdx == length blk.statements) = true
        · simp only [h_end, ite_true]
          exact nodeSuccs_evalTerminatorLookup h_inv h_term
        · simp only [h_end, Bool.false_eq_true, ite_false]
          trivial

/-- **`tbl.toList`-free syntactic closure implies `MirLiftCore.ConeReach`** for every fuel bound. -/
theorem coneReach_of_closedInvLookup {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} (h_closed : tbl.callConeClosed cone root = true) :
    ∀ (fuel : Nat) (s : MachineState), ClosedInvLookup cone root tbl s →
      MirLiftCore.ConeReach root (MirLiftCore.StepConeSafe cone root) fuel (.running s)
  | 0, _, _ => trivial
  | fuel + 1, s, h_inv => by
    refine ⟨stepConeSafe_of_closedInvLookup h_closed h_inv, ?_⟩
    have h_succ := nodeSuccs_stepMirFnLookup h_closed h_inv
    revert h_succ
    cases stepMirFn root s with
    | ret _ => intro _; trivial
    | tau st' =>
      cases st' with
      | running s' => intro h; exact coneReach_of_closedInvLookup h_closed fuel s' h
      | halted _ => intro _; cases fuel <;> trivial
      | faulted _ => intro _; cases fuel <;> trivial
    | vis e k =>
      rcases e with fk | obs | ⟨req⟩
      · intro _; trivial
      · intro h
        show MirLiftCore.ConeReach root _ fuel (k PUnit.unit)
        revert h
        show (match k PUnit.unit with
          | .running s' => ClosedInvLookup cone root tbl s'
          | _ => True) → _
        cases k PUnit.unit with
        | running s' => intro h; exact coneReach_of_closedInvLookup h_closed fuel s' h
        | halted _ => intro _; cases fuel <;> trivial
        | faulted _ => intro _; cases fuel <;> trivial
      · intro _; trivial

theorem initMachineStateWithMemoryAndCallees_activeCallee (body : CapturedMir) (args : List Value)
    (mem : Memory) (c : List CapturedMir) :
    (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c).memory.activeCallee =
      mem.activeCallee := by
  cases c <;> rfl

theorem initMachineStateWithMemoryAndCallees_callStack (body : CapturedMir) (args : List Value)
    (mem : Memory) (c : List CapturedMir) :
    (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem c).memory.callStack =
      mem.callStack := by
  cases c <;> rfl

theorem closedInvLookup_init_of_wf (cone : List DefPath) (body : CapturedMir) (args : List Value)
    (mem : Memory) {tbl : OpaqueCalleeTable} (h₁ : MirLiftCore.CalleeInitWf body mem tbl.toList)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = []) :
    ClosedInvLookup cone body tbl
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem tbl.toList) := by
  refine ⟨MirLiftCore.initMachineStateWithMemoryAndCallees_callees_of_wf body args mem h₁, ?_, ?_⟩
  · show InConeLookup cone body tbl
      ((Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
        tbl.toList).memory.activeCallee.getD body)
    rw [initMachineStateWithMemoryAndCallees_activeCallee, h_ac]
    exact Or.inl rfl
  · intro f hf
    rw [initMachineStateWithMemoryAndCallees_callStack, h_cs] at hf
    cases hf

/-- **`tbl.toList`-free syntactic `runCfgWithCallees` narrowing between opaque tables**
(discharged via `t₁.callConeClosed`, which queries only `t₁.lookupRaw` on `cone`). -/
theorem runCfgWithCallees_cone_narrow_of_callConeClosed_wf (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : MirLiftCore.CalleeInitWf body mem t₁.toList)
    (h₂ : MirLiftCore.CalleeInitWf body mem t₂.toList)
    (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (h_closed : t₁.callConeClosed cone body = true)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = []) :
    MirLiftCore.runCfgWithCallees fuel body args mem t₂.toList =
      (MirLiftCore.runCfgWithCallees fuel body args mem t₁.toList).map
        (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList)) := by
  unfold MirLiftCore.runCfgWithCallees
  rw [MirLiftCore.initMachineStateWithMemoryAndCallees_withCallees_of_wf body args mem h₁ h₂]
  refine MirLiftCore.runMirExecBounded_cone_narrow cone body t₂.toList fuel _
    (coneReach_of_closedInvLookup h_closed fuel _
      (closedInvLookup_init_of_wf cone body args mem h₁ h_ac h_cs)) ?_
  intro s hs
  cases hs
  rw [MirLiftCore.initMachineStateWithMemoryAndCallees_callees_of_wf body args mem h₁]
  exact calleesAgreeOn_of_agreesOn h_agree

/-- **`tbl.toList`-free syntactic `wpMirExecSym` narrowing between opaque tables.** -/
theorem wpMirExecSym_cone_narrow_of_callConeClosed_wf (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : MirLiftCore.CalleeInitWf body mem t₁.toList)
    (h₂ : MirLiftCore.CalleeInitWf body mem t₂.toList)
    (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (h_closed : t₁.callConeClosed cone body = true)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out,
      post (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList) out) ↔ post out) :
    Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₂.toList)) post ↔
      Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₁.toList)) post := by
  rw [MirLiftCore.initMachineStateWithMemoryAndCallees_withCallees_of_wf body args mem h₁ h₂]
  refine MirLiftCore.wpMirExecSym_cone_narrow cone body t₂.toList post h_post fuel _
    (coneReach_of_closedInvLookup h_closed fuel _
      (closedInvLookup_init_of_wf cone body args mem h₁ h_ac h_cs)) ?_
  intro s hs
  cases hs
  rw [MirLiftCore.initMachineStateWithMemoryAndCallees_callees_of_wf body args mem h₁]
  exact calleesAgreeOn_of_agreesOn h_agree

/-- **`tbl.toList`-free syntactic `MirWpConverges` narrowing between opaque tables.** -/
theorem mirWpConverges_cone_narrow_of_callConeClosed_wf (cone : List DefPath)
    (body : CapturedMir) (args : List Value) (mem : Memory) {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : MirLiftCore.CalleeInitWf body mem t₁.toList)
    (h₂ : MirLiftCore.CalleeInitWf body mem t₂.toList)
    (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (h_closed : t₁.callConeClosed cone body = true)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out,
      post (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList) out) ↔ post out) :
    MirFuelFree.MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₂.toList) post ↔
      MirFuelFree.MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₁.toList) post := by
  rw [MirLiftCore.initMachineStateWithMemoryAndCallees_withCallees_of_wf body args mem h₁ h₂]
  refine MirLiftCore.mirWpConverges_cone_narrow cone body t₂.toList post h_post _
    (fun fuel =>
      coneReach_of_closedInvLookup h_closed fuel _
        (closedInvLookup_init_of_wf cone body args mem h₁ h_ac h_cs)) ?_
  rw [MirLiftCore.initMachineStateWithMemoryAndCallees_callees_of_wf body args mem h₁]
  exact calleesAgreeOn_of_agreesOn h_agree

/-- `b` is the root body or an instantiation `b₀.instantiate subst` of a first-match body
`tbl.lookupRaw dp = some b₀` for some `dp ∈ cone`. -/
def InConeLookupPoly (cone : List DefPath) (root : CapturedMir) (tbl : OpaqueCalleeTable)
    (b : CapturedMir) : Prop :=
  b = root ∨ ∃ dp, dp ∈ cone ∧ ∃ b₀ subst, tbl.lookupRaw dp = some b₀ ∧ b = b₀.instantiate subst

/-- Reachable-state invariant of a `callConeClosedPoly` execution over `tbl`. -/
def ClosedInvLookupPoly (cone : List DefPath) (root : CapturedMir) (tbl : OpaqueCalleeTable)
    (ti : List TraitImplEntry) (s : MachineState) : Prop :=
  s.memory.callees = tbl.toList ∧ s.memory.traitImpls = ti ∧
    InConeLookupPoly cone root tbl (s.memory.activeCallee.getD root) ∧
    ∀ f, f ∈ s.memory.callStack → InConeLookupPoly cone root tbl f.callerBody

theorem bodyCallsInConePoly_of_inConeLookupPoly {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {ti : List TraitImplEntry} {b : CapturedMir}
    (h_closed : tbl.callConeClosedPoly cone root ti = true)
    (hb : InConeLookupPoly cone root tbl b) : MirLiftCore.bodyCallsInConePoly cone b = true := by
  unfold OpaqueCalleeTable.callConeClosedPoly at h_closed
  rw [Bool.and_eq_true] at h_closed
  rcases hb with rfl | ⟨dp, hdp, b₀, subst, hraw, rfl⟩
  · exact h_closed.1
  · have h := List.all_eq_true.mp h_closed.2 dp hdp
    rw [Bool.and_eq_true, hraw] at h
    exact MirLiftCore.bodyCallsInConePoly_instantiate subst h.1

theorem noTraitImpl_of_callConeClosedPoly_lookup {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {ti : List TraitImplEntry} {dp : DefPath}
    (h_closed : tbl.callConeClosedPoly cone root ti = true) (h_dp : dp ∈ cone) :
    hasTraitImplForDefPath (ti ++ flatMapTraitImpls tbl.toList) dp = false := by
  unfold OpaqueCalleeTable.callConeClosedPoly at h_closed
  rw [Bool.and_eq_true] at h_closed
  have h := List.all_eq_true.mp h_closed.2 dp h_dp
  rw [Bool.and_eq_true, OpaqueCalleeTable.traitImpls_eq] at h
  cases htr : hasTraitImplForDefPath (ti ++ flatMapTraitImpls tbl.toList) dp with
  | false => rfl
  | true => rw [htr] at h; cases h.2

theorem stepConeSafePoly_of_closedInvLookupPoly {cone : List DefPath} {root : CapturedMir}
    {tbl t₂ : OpaqueCalleeTable} {ti : List TraitImplEntry} {s : MachineState}
    (h_closed : tbl.callConeClosedPoly cone root ti = true)
    (h_no₂ : ∀ dp, dp ∈ cone → hasTraitImplForDefPath (ti ++ t₂.traitImpls) dp = false)
    (h_inv : ClosedInvLookupPoly cone root tbl ti s) :
    MirLiftCore.StepConeSafePoly cone t₂.toList root s := by
  intro blk h_bb
  have h_body := bodyCallsInConePoly_of_inConeLookupPoly h_closed h_inv.2.2.1
  unfold MirLiftCore.bodyCallsInConePoly at h_body
  have h_blk := List.all_eq_true.mp h_body blk (List.mem_of_getElem? h_bb)
  rw [Bool.and_eq_true] at h_blk
  refine ⟨fun stmt h_st => List.all_eq_true.mp h_blk.1 stmt (List.mem_of_getElem? h_st), ?_⟩
  have h_tc := h_blk.2
  revert h_tc
  rcases blk.terminator with ⟨kind, span⟩
  intro h_tc
  cases kind with
  | call func argOps _ _ _ =>
    intro tgt l h_res
    unfold MirLiftCore.termCallsInConePoly MirLiftCore.directCallInConePoly at h_tc
    dsimp only at h_tc
    cases h_fn : MirLiftCore.extractFnDefPath? func with
    | none => rw [h_fn] at h_tc; cases h_tc
    | some dp =>
      rw [h_fn, Bool.and_eq_true] at h_tc
      have h_cd := MirLiftCore.extractCalleeDefPath?_of_extractFnDefPath? h_fn
      unfold resolveCallTarget at h_res
      rw [h_cd] at h_res
      cases h_res
      have h_dp : dp ∈ cone := MirLiftCore.inCone_iff.mp h_tc.1
      rw [h_inv.1, h_inv.2.1]
      exact ⟨h_dp, noTraitImpl_of_callConeClosedPoly_lookup h_closed h_dp,
        noTraitImplInCone_toList h_no₂ dp h_dp, h_tc.2⟩
  | tailCall func argOps =>
    intro tgt l h_res
    unfold MirLiftCore.termCallsInConePoly MirLiftCore.directCallInConePoly at h_tc
    dsimp only at h_tc
    cases h_fn : MirLiftCore.extractFnDefPath? func with
    | none => rw [h_fn] at h_tc; cases h_tc
    | some dp =>
      rw [h_fn, Bool.and_eq_true] at h_tc
      have h_cd := MirLiftCore.extractCalleeDefPath?_of_extractFnDefPath? h_fn
      unfold resolveCallTarget at h_res
      rw [h_cd] at h_res
      cases h_res
      have h_dp : dp ∈ cone := MirLiftCore.inCone_iff.mp h_tc.1
      rw [h_inv.1, h_inv.2.1]
      exact ⟨h_dp, noTraitImpl_of_callConeClosedPoly_lookup h_closed h_dp,
        noTraitImplInCone_toList h_no₂ dp h_dp, h_tc.2⟩
  | _ => trivial

theorem closedInvLookupPoly_of_callerBodies {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {ti : List TraitImplEntry} {s s' : MachineState}
    (h_inv : ClosedInvLookupPoly cone root tbl ti s)
    (hc : s'.memory.callees = s.memory.callees)
    (hti : s'.memory.traitImpls = s.memory.traitImpls)
    (hac : s'.memory.activeCallee = s.memory.activeCallee)
    (hb : MirLiftCore.CallerBodiesEq s.memory.callStack s'.memory.callStack) :
    ClosedInvLookupPoly cone root tbl ti s' := by
  refine ⟨hc.trans h_inv.1, hti.trans h_inv.2.1, hac ▸ h_inv.2.2.1, ?_⟩
  intro f hf
  obtain ⟨f₀, hf₀, he⟩ := hb.mem hf
  exact he ▸ h_inv.2.2.2 f₀ hf₀

theorem nodeSuccs_closedInvLookupPoly_of_ctx {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {ti : List TraitImplEntry} {s : MachineState} {n : MirStepNode}
    (h_inv : ClosedInvLookupPoly cone root tbl ti s)
    (hfix : n = MirLiftCore.MirStepNode.mapMem
      (MirLiftCore.Memory.withCalleeCtx s.memory.callees s.memory.activeCallee
        s.memory.traitImpls) n)
    (hb : MirLiftCore.NodeSuccs
      (fun s' => MirLiftCore.CallerBodiesEq s.memory.callStack s'.memory.callStack) n) :
    MirLiftCore.NodeSuccs (ClosedInvLookupPoly cone root tbl ti) n := by
  refine MirLiftCore.NodeSuccs.mono ?_
    (MirLiftCore.NodeSuccs.and
      (MirLiftCore.nodeSuccs_of_fixed (P := fun s' => s' = MirLiftCore.MachineState.mapMem
        (MirLiftCore.Memory.withCalleeCtx s.memory.callees s.memory.activeCallee
          s.memory.traitImpls) s')
        hfix (fun _ h => h))
      hb)
  rintro s' ⟨hs', hb'⟩
  have hm : s'.memory =
      MirLiftCore.Memory.withCalleeCtx s.memory.callees s.memory.activeCallee
        s.memory.traitImpls s'.memory :=
    congrArg MachineState.memory hs'
  exact closedInvLookupPoly_of_callerBodies h_inv (by rw [hm]) (by rw [hm]) (by rw [hm]) hb'

theorem closedInvLookupPoly_return {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {ti : List TraitImplEntry} {s : MachineState}
    {caller : SavedCallerFrame} {rest : List SavedCallerFrame} {retVal : Value}
    {locals' : List LocalSlot} {mem' : Memory} {F : StackFrame}
    (h_inv : ClosedInvLookupPoly cone root tbl ti s) (h_cs : s.memory.callStack = caller :: rest)
    (h_w : writeReturnDestination caller.frame.locals (MirLiftCore.ccReturnCallerMem s caller rest)
      caller.destination retVal caller.callerBody.localDecls caller.callerBody.layouts =
        .ok locals' mem') :
    ClosedInvLookupPoly cone root tbl ti { frame := F, memory := mem' } := by
  obtain ⟨hc, hac, hti⟩ := MirLiftCore.writeReturnDestination_ctx_preserved h_w
  have hb := MirLiftCore.writeReturnDestination_callerBodies h_w
  refine ⟨hc.trans h_inv.1, hti.trans h_inv.2.1, ?_, ?_⟩
  · show InConeLookupPoly cone root tbl (mem'.activeCallee.getD root)
    rw [hac]
    exact h_inv.2.2.2 caller (by rw [h_cs]; exact List.Mem.head _)
  · intro f hf
    obtain ⟨f₀, hf₀, he⟩ := hb.mem hf
    exact he ▸ h_inv.2.2.2 f₀ (by rw [h_cs]; exact List.Mem.tail _ hf₀)

theorem closedInvLookupPoly_unwindFromCallStack {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {ti : List TraitImplEntry} :
    ∀ (stk : List SavedCallerFrame) (m : Memory), m.callees = tbl.toList → m.traitImpls = ti →
      (∀ f, f ∈ stk → InConeLookupPoly cone root tbl f.callerBody) →
      ∀ s', unwindFromCallStack stk m = .running s' → ClosedInvLookupPoly cone root tbl ti s'
  | [], _, _, _, _, _, h => by cases h
  | caller :: rest, m, hc, hti, hf, s', h => by
    unfold unwindFromCallStack at h
    dsimp only at h
    cases hr : caller.returnUnwind with
    | unreachable => rw [hr] at h; dsimp only at h; cases h
    | terminate => rw [hr] at h; dsimp only at h; cases h
    | continue_ =>
      rw [hr] at h
      dsimp only at h
      exact closedInvLookupPoly_unwindFromCallStack rest
        { m with
          callStack := rest
          activeCallee := some caller.callerBody
          activeProtectors := restoreCallerProtectors caller }
        hc hti (fun f hm => hf f (List.Mem.tail _ hm)) s' h
    | cleanup bb =>
      rw [hr] at h
      dsimp only at h
      cases h
      exact ⟨hc, hti, hf caller (List.Mem.head _), fun f hm => hf f (List.Mem.tail _ hm)⟩

private theorem nodeSuccs_unwindMatchLookupPoly {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {ti : List TraitImplEntry} (st : MirExecState)
    (h : ∀ s', st = .running s' → ClosedInvLookupPoly cone root tbl ti s') :
    MirLiftCore.NodeSuccs (ClosedInvLookupPoly cone root tbl ti)
      (match (generalizing := false) st with
        | .running nextState => MirStepNode.step nextState
        | .halted out => MirStepNode.retOutcome out
        | .faulted fk => MirStepNode.fail fk) := by
  cases st with
  | running s' => exact h s' rfl
  | halted _ => trivial
  | faulted _ => trivial

private theorem nodeSuccs_applyUnwindLookupPoly {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {ti : List TraitImplEntry} {s : MachineState}
    (h_inv : ClosedInvLookupPoly cone root tbl ti s) (l : List LocalSlot) (u : UnwindAction) :
    MirLiftCore.NodeSuccs (ClosedInvLookupPoly cone root tbl ti)
      (match applyUnwindAction s l s.memory u with
        | .running nextState => MirStepNode.step nextState
        | .halted out => MirStepNode.retOutcome out
        | .faulted fk => MirStepNode.fail fk) := by
  refine nodeSuccs_unwindMatchLookupPoly _ ?_
  intro s' hs'
  cases u with
  | unreachable => cases hs'
  | terminate => cases hs'
  | continue_ =>
    exact closedInvLookupPoly_unwindFromCallStack s.memory.callStack s.memory h_inv.1 h_inv.2.1
      h_inv.2.2.2 s' hs'
  | cleanup bb =>
    cases hs'
    exact h_inv

private theorem inConeLookupPoly_of_lookup {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {L : LayoutTable} {dp : DefPath} {typeArgs : List RigidTy}
    {ti : List TraitImplEntry} {calleeBody : CapturedMir}
    (h_dp : dp ∈ cone)
    (h_no : hasTraitImplForDefPath (ti ++ flatMapTraitImpls tbl.toList) dp = false)
    (h_lk : lookupCallee tbl.toList L dp typeArgs ti = some calleeBody) :
    InConeLookupPoly cone root tbl calleeBody := by
  obtain ⟨b₀, subst, hf, hinst⟩ := MirLiftCore.lookupCallee_eq_some_of_no_traitImpl h_no h_lk
  exact Or.inr ⟨dp, h_dp, b₀, subst, (OpaqueCalleeTable.lookupRaw_eq tbl dp).trans hf, hinst⟩

private theorem closedInvLookupPoly_push {cone : List DefPath} {root : CapturedMir}
    {tbl : OpaqueCalleeTable} {ti : List TraitImplEntry} {s : MachineState}
    {saved : SavedCallerFrame} {b : CapturedMir} {F : StackFrame}
    (h_inv : ClosedInvLookupPoly cone root tbl ti s)
    (h_saved : InConeLookupPoly cone root tbl saved.callerBody)
    (h_b : InConeLookupPoly cone root tbl b) :
    ClosedInvLookupPoly cone root tbl ti
      { frame := F,
        memory := { s.memory with
          callStack := saved :: s.memory.callStack
          activeCallee := some b } } := by
  refine ⟨h_inv.1, h_inv.2.1, h_b, ?_⟩
  intro f hf
  cases hf with
  | head => exact h_saved
  | tail _ hf => exact h_inv.2.2.2 f hf

theorem nodeSuccs_evalDirectRustIntrinsic?_lookupPoly {cone : List DefPath}
    {root : CapturedMir} {tbl : OpaqueCalleeTable} {ti : List TraitImplEntry} {s : MachineState}
    (h_inv : ClosedInvLookupPoly cone root tbl ti s) (currentBody : Option CapturedMir)
    (target : ResolvedCallTarget) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (unwind : UnwindAction)
    (h_cl : MirLiftCore.isNonSelectIntrinsicOpt (classifyRustIntrinsic? target.defPath) = true)
    (fallback : MirStepNode)
    (h_fb : MirLiftCore.NodeSuccs (ClosedInvLookupPoly cone root tbl ti) fallback) :
    MirLiftCore.NodeSuccs (ClosedInvLookupPoly cone root tbl ti)
      (match evalDirectRustIntrinsic? s currentBody target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb unwind with
       | some stepNode => stepNode
       | none => fallback) := by
  unfold evalDirectRustIntrinsic?
  cases h_k : classifyRustIntrinsic? target.defPath with
  | none => exact h_fb
  | some kind =>
    rw [h_k] at h_cl
    have h_step : ∀ (k : RustIntrinsicKind),
        MirLiftCore.NodeSuccs (ClosedInvLookupPoly cone root tbl ti)
          (evalNonSelectIntrinsicCall k s target bodyLocalDecls bodyLayouts
            argOps argVals locals' destination targetBb) := by
      intro k
      exact nodeSuccs_closedInvLookupPoly_of_ctx h_inv
        (MirLiftCore.evalNonSelectIntrinsicCall_calleeCtx_preserved k s target bodyLocalDecls
          bodyLayouts argOps argVals locals' destination targetBb)
        (MirLiftCore.evalNonSelectIntrinsicCall_callerBodies k s target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb)
    cases kind with
    | constEvalSelect => cases h_cl
    | _ => exact h_step _

theorem nodeSuccs_evalTerminatorLookupPoly {cone : List DefPath} {root : CapturedMir}
    {tbl t₂ : OpaqueCalleeTable} {ti : List TraitImplEntry} {s : MachineState} {term : Terminator}
    (h_inv : ClosedInvLookupPoly cone root tbl ti s)
    (h_term : MirLiftCore.TermConeSafePoly cone t₂.toList s (s.memory.activeCallee.getD root) term) :
    MirLiftCore.NodeSuccs (ClosedInvLookupPoly cone root tbl ti)
      (evalTerminator s term (some (s.memory.activeCallee.getD root))) := by
  have h_cur : InConeLookupPoly cone root tbl (s.memory.activeCallee.getD root) := h_inv.2.2.1
  rcases term with ⟨kind, span⟩
  cases kind with
  | goto target => exact h_inv
  | switchInt discr targets =>
    unfold evalTerminator; dsimp only
    repeat' (first | trivial | exact h_inv | split)
  | unwindResume =>
    unfold evalTerminator; dsimp only
    exact nodeSuccs_unwindMatchLookupPoly _
      (closedInvLookupPoly_unwindFromCallStack s.memory.callStack s.memory h_inv.1 h_inv.2.1
        h_inv.2.2.2)
  | unwindTerminate => trivial
  | return_ =>
    rw [MirLiftCore.ccEvalReturn_eq]
    unfold MirLiftCore.ccEvalReturn
    repeat' (first | trivial | exact closedInvLookupPoly_return h_inv ‹_› ‹_› | split)
  | unreachable => trivial
  | drop place target unwind =>
    unfold evalTerminator; dsimp only
    repeat' (first | trivial | exact h_inv | split)
  | assert cond expected target unwind =>
    unfold evalTerminator; dsimp only
    repeat' (first | trivial | exact h_inv | exact nodeSuccs_applyUnwindLookupPoly h_inv _ _ | split)
  | call func argOps destination target unwind =>
    have hq : MirLiftCore.CallTargetInConePoly cone t₂.toList s (s.memory.activeCallee.getD root)
        func (length argOps) := h_term
    cases target with
    | some targetBb =>
      unfold evalTerminator; dsimp only
      cases h_res : resolveCallTarget s func (length argOps)
          (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root)))
          (s.memory.activeCallee.getD root).layouts with
      | ub => trivial
      | unsupported => trivial
      | ok tgt localsAfterFunc =>
        obtain ⟨h_dp, h_no₁, _, h_cl⟩ := hq tgt localsAfterFunc h_res
        dsimp only
        cases evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
            (s.memory.activeCallee.getD root).layouts s.memory.callerLocals
            (callStack := s.memory.callStack) with
        | ub => trivial
        | unsupported => trivial
        | ok argVals locals' =>
          dsimp only
          cases h_lk : lookupCallee s.memory.callees (s.memory.activeCallee.getD root).layouts
              tgt.defPath tgt.typeArgs s.memory.traitImpls with
          | some calleeBody =>
            dsimp only
            cases checkCalleeTargetCompatible tgt calleeBody (length argVals) with
            | false => trivial
            | true =>
              rw [h_inv.1, h_inv.2.1] at h_lk h_no₁
              exact closedInvLookupPoly_push h_inv h_cur (inConeLookupPoly_of_lookup h_dp h_no₁ h_lk)
          | none =>
            dsimp only
            repeat' (first
              | trivial | exact h_inv
              | exact nodeSuccs_closedInvLookupPoly_of_ctx h_inv
                  (MirLiftCore.writeIntrinsicReturn_calleeCtx_preserved _ _ _ _ _)
                  (MirLiftCore.writeIntrinsicReturn_callerBodies _ _ _ _ _)
              | exact nodeSuccs_evalDirectRustIntrinsic?_lookupPoly h_inv _ _ _ _ _ _ _ _ _ _ h_cl _
                  (by
                    repeat' (first
                      | trivial | exact h_inv
                      | exact nodeSuccs_closedInvLookupPoly_of_ctx h_inv
                          (MirLiftCore.writeIntrinsicReturn_calleeCtx_preserved _ _ _ _ _)
                          (MirLiftCore.writeIntrinsicReturn_callerBodies _ _ _ _ _)
                      | split))
              | split)
    | none =>
      unfold evalTerminator; dsimp only
      cases h_res : resolveCallTarget s func (length argOps)
          (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root)))
          (s.memory.activeCallee.getD root).layouts with
      | ub => trivial
      | unsupported => trivial
      | ok tgt localsAfterFunc =>
        obtain ⟨h_dp, h_no₁, _, _⟩ := hq tgt localsAfterFunc h_res
        dsimp only
        cases evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
            (s.memory.activeCallee.getD root).layouts s.memory.callerLocals
            (callStack := s.memory.callStack) with
        | ub => trivial
        | unsupported => trivial
        | ok argVals locals' =>
          dsimp only
          cases h_lk : lookupCallee s.memory.callees (s.memory.activeCallee.getD root).layouts
              tgt.defPath tgt.typeArgs s.memory.traitImpls with
          | some calleeBody =>
            dsimp only
            cases checkCalleeTargetCompatible tgt calleeBody (length argVals) with
            | false => trivial
            | true =>
              rw [h_inv.1, h_inv.2.1] at h_lk h_no₁
              exact closedInvLookupPoly_push h_inv h_cur (inConeLookupPoly_of_lookup h_dp h_no₁ h_lk)
          | none =>
            dsimp only
            repeat' (first | trivial | exact nodeSuccs_applyUnwindLookupPoly h_inv _ _ | split)
  | tailCall func argOps =>
    have hq : MirLiftCore.CallTargetInConePoly cone t₂.toList s (s.memory.activeCallee.getD root)
        func (length argOps) := h_term
    unfold evalTerminator; dsimp only
    unfold evalTailCallTerminator; dsimp only
    cases h_res : resolveCallTarget s func (length argOps)
        (bodyLocalDeclsOf (some (s.memory.activeCallee.getD root)))
        (s.memory.activeCallee.getD root).layouts with
    | ub => trivial
    | unsupported => trivial
    | ok tgt localsAfterFunc =>
      obtain ⟨h_dp, h_no₁, _, _⟩ := hq tgt localsAfterFunc h_res
      dsimp only
      cases evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
          (s.memory.activeCallee.getD root).layouts s.memory.callerLocals
          (callStack := s.memory.callStack) with
      | ub => trivial
      | unsupported => trivial
      | ok argVals locals' =>
        dsimp only
        cases h_lk : lookupCallee s.memory.callees (s.memory.activeCallee.getD root).layouts
            tgt.defPath tgt.typeArgs s.memory.traitImpls with
        | some calleeBody =>
          dsimp only
          rw [h_inv.1, h_inv.2.1] at h_lk h_no₁
          repeat' (first
            | trivial
            | exact ⟨h_inv.1, h_inv.2.1, inConeLookupPoly_of_lookup h_dp h_no₁ h_lk, h_inv.2.2.2⟩
            | split)
        | none =>
          dsimp only
          repeat' (first | trivial | split)
  | _ => trivial

theorem nodeSuccs_stepMirFnLookupPoly {cone : List DefPath} {root : CapturedMir}
    {tbl t₂ : OpaqueCalleeTable} {ti : List TraitImplEntry} {s : MachineState}
    (h_closed : tbl.callConeClosedPoly cone root ti = true)
    (h_no₂ : ∀ dp, dp ∈ cone → hasTraitImplForDefPath (ti ++ t₂.traitImpls) dp = false)
    (h_inv : ClosedInvLookupPoly cone root tbl ti s) :
    MirLiftCore.NodeSuccs (ClosedInvLookupPoly cone root tbl ti) (stepMirFn root s) := by
  have h_safe := stepConeSafePoly_of_closedInvLookupPoly h_closed h_no₂ h_inv
  unfold stepMirFn; dsimp only
  split
  · trivial
  · cases h_bb : get? (s.memory.activeCallee.getD root).basicBlocks s.frame.blockIdx with
    | none => trivial
    | some blk =>
      obtain ⟨h_stmt, h_term⟩ := h_safe blk h_bb
      dsimp only
      cases h_st : get? blk.statements s.frame.stmtIdx with
      | some stmt =>
        dsimp only
        exact nodeSuccs_closedInvLookupPoly_of_ctx h_inv
          (MirLiftCore.evalStmt_calleeCtx_preserved s stmt _ _ (h_stmt stmt h_st))
          (MirLiftCore.evalStmt_callerBodies s stmt _ _)
      | none =>
        dsimp only
        by_cases h_end : (s.frame.stmtIdx == length blk.statements) = true
        · simp only [h_end, ite_true]
          exact nodeSuccs_evalTerminatorLookupPoly h_inv h_term
        · simp only [h_end, Bool.false_eq_true, ite_false]
          trivial

/-- **`tbl.toList`-free polymorphic syntactic closure implies `MirLiftCore.ConeReach`** for every
fuel bound. -/
theorem coneReach_of_closedInvLookupPoly {cone : List DefPath} {root : CapturedMir}
    {tbl t₂ : OpaqueCalleeTable} {ti : List TraitImplEntry}
    (h_closed : tbl.callConeClosedPoly cone root ti = true)
    (h_no₂ : ∀ dp, dp ∈ cone → hasTraitImplForDefPath (ti ++ t₂.traitImpls) dp = false) :
    ∀ (fuel : Nat) (s : MachineState), ClosedInvLookupPoly cone root tbl ti s →
      MirLiftCore.ConeReach root (MirLiftCore.StepConeSafePoly cone t₂.toList root) fuel (.running s)
  | 0, _, _ => trivial
  | fuel + 1, s, h_inv => by
    refine ⟨stepConeSafePoly_of_closedInvLookupPoly h_closed h_no₂ h_inv, ?_⟩
    have h_succ := nodeSuccs_stepMirFnLookupPoly h_closed h_no₂ h_inv
    revert h_succ
    cases stepMirFn root s with
    | ret _ => intro _; trivial
    | tau st' =>
      cases st' with
      | running s' => intro h; exact coneReach_of_closedInvLookupPoly h_closed h_no₂ fuel s' h
      | halted _ => intro _; cases fuel <;> trivial
      | faulted _ => intro _; cases fuel <;> trivial
    | vis e k =>
      rcases e with fk | obs | ⟨req⟩
      · intro _; trivial
      · intro h
        show MirLiftCore.ConeReach root _ fuel (k PUnit.unit)
        revert h
        show (match k PUnit.unit with
          | .running s' => ClosedInvLookupPoly cone root tbl ti s'
          | _ => True) → _
        cases k PUnit.unit with
        | running s' => intro h; exact coneReach_of_closedInvLookupPoly h_closed h_no₂ fuel s' h
        | halted _ => intro _; cases fuel <;> trivial
        | faulted _ => intro _; cases fuel <;> trivial
      · intro _; trivial

theorem closedInvLookupPoly_init_of_wf (cone : List DefPath) (body : CapturedMir) (args : List Value)
    (mem : Memory) {tbl : OpaqueCalleeTable} (h₁ : MirLiftCore.CalleeInitWf body mem tbl.toList)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = []) :
    ClosedInvLookupPoly cone body tbl body.traitImpls
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem tbl.toList) := by
  refine ⟨MirLiftCore.initMachineStateWithMemoryAndCallees_callees_of_wf body args mem h₁,
    MirLiftCore.initMachineStateWithMemoryAndCallees_traitImpls_of_wf body args mem h₁, ?_, ?_⟩
  · show InConeLookupPoly cone body tbl
      ((Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
        tbl.toList).memory.activeCallee.getD body)
    rw [initMachineStateWithMemoryAndCallees_activeCallee, h_ac]
    exact Or.inl rfl
  · intro f hf
    rw [initMachineStateWithMemoryAndCallees_callStack, h_cs] at hf
    cases hf

/-- **`tbl.toList`-free polymorphic syntactic `runCfgWithCallees` narrowing between opaque tables**
(discharged via `t₁.callConeClosedPoly`, which queries only `t₁.lookupRaw` and `t₁.traitImpls`). -/
theorem runCfgWithCallees_cone_narrow_of_callConeClosedPoly_wf (cone : List DefPath)
    (fuel : Nat) (body : CapturedMir) (args : List Value) (mem : Memory)
    {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : MirLiftCore.CalleeInitWf body mem t₁.toList)
    (h₂ : MirLiftCore.CalleeInitWf body mem t₂.toList)
    (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (h_closed : t₁.callConeClosedPoly cone body body.traitImpls = true)
    (h_no₂ : ∀ dp, dp ∈ cone →
      hasTraitImplForDefPath (body.traitImpls ++ t₂.traitImpls) dp = false)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = []) :
    MirLiftCore.runCfgWithCallees fuel body args mem t₂.toList =
      (MirLiftCore.runCfgWithCallees fuel body args mem t₁.toList).map
        (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList)) := by
  unfold MirLiftCore.runCfgWithCallees
  rw [MirLiftCore.initMachineStateWithMemoryAndCallees_withCallees_of_wf body args mem h₁ h₂]
  refine MirLiftCore.runMirExecBounded_cone_narrow_poly cone body t₂.toList fuel _
    (coneReach_of_closedInvLookupPoly h_closed h_no₂ fuel _
      (closedInvLookupPoly_init_of_wf cone body args mem h₁ h_ac h_cs)) ?_
  intro s hs
  cases hs
  rw [MirLiftCore.initMachineStateWithMemoryAndCallees_callees_of_wf body args mem h₁]
  exact calleesAgreeOn_of_agreesOn h_agree

/-- **`tbl.toList`-free polymorphic syntactic `wpMirExecSym` narrowing between opaque tables.** -/
theorem wpMirExecSym_cone_narrow_of_callConeClosedPoly_wf (cone : List DefPath) (fuel : Nat)
    (body : CapturedMir) (args : List Value) (mem : Memory) {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : MirLiftCore.CalleeInitWf body mem t₁.toList)
    (h₂ : MirLiftCore.CalleeInitWf body mem t₂.toList)
    (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (h_closed : t₁.callConeClosedPoly cone body body.traitImpls = true)
    (h_no₂ : ∀ dp, dp ∈ cone →
      hasTraitImplForDefPath (body.traitImpls ++ t₂.traitImpls) dp = false)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out,
      post (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList) out) ↔ post out) :
    Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₂.toList)) post ↔
      Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym fuel body
        (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₁.toList)) post := by
  rw [MirLiftCore.initMachineStateWithMemoryAndCallees_withCallees_of_wf body args mem h₁ h₂]
  refine MirLiftCore.wpMirExecSym_cone_narrow_poly cone body t₂.toList post h_post fuel _
    (coneReach_of_closedInvLookupPoly h_closed h_no₂ fuel _
      (closedInvLookupPoly_init_of_wf cone body args mem h₁ h_ac h_cs)) ?_
  intro s hs
  cases hs
  rw [MirLiftCore.initMachineStateWithMemoryAndCallees_callees_of_wf body args mem h₁]
  exact calleesAgreeOn_of_agreesOn h_agree

/-- **`tbl.toList`-free polymorphic syntactic `MirWpConverges` narrowing between opaque tables.** -/
theorem mirWpConverges_cone_narrow_of_callConeClosedPoly_wf (cone : List DefPath)
    (body : CapturedMir) (args : List Value) (mem : Memory) {t₁ t₂ : OpaqueCalleeTable}
    (h₁ : MirLiftCore.CalleeInitWf body mem t₁.toList)
    (h₂ : MirLiftCore.CalleeInitWf body mem t₂.toList)
    (h_agree : OpaqueCalleeTable.AgreesOn cone t₁ t₂)
    (h_closed : t₁.callConeClosedPoly cone body body.traitImpls = true)
    (h_no₂ : ∀ dp, dp ∈ cone →
      hasTraitImplForDefPath (body.traitImpls ++ t₂.traitImpls) dp = false)
    (h_ac : mem.activeCallee = none) (h_cs : mem.callStack = [])
    (post : MirOutcome → Prop)
    (h_post : ∀ out,
      post (MirLiftCore.MirOutcome.mapMem (MirLiftCore.Memory.withCallees t₂.toList) out) ↔ post out) :
    MirFuelFree.MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₂.toList) post ↔
      MirFuelFree.MirWpConverges body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
          t₁.toList) post := by
  rw [MirLiftCore.initMachineStateWithMemoryAndCallees_withCallees_of_wf body args mem h₁ h₂]
  have h_at : MirLiftCore.AgreesAt cone t₂.toList
      (.running (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees body args mem
        t₁.toList)) := by
    intro s hs
    cases hs
    rw [MirLiftCore.initMachineStateWithMemoryAndCallees_callees_of_wf body args mem h₁]
    exact calleesAgreeOn_of_agreesOn h_agree
  constructor
  · rintro ⟨fuel, h⟩
    exact ⟨fuel,
      (MirLiftCore.wpMirExecSym_cone_narrow_poly cone body t₂.toList post h_post fuel _
        (coneReach_of_closedInvLookupPoly h_closed h_no₂ fuel _
          (closedInvLookupPoly_init_of_wf cone body args mem h₁ h_ac h_cs))
        h_at).1 h⟩
  · rintro ⟨fuel, h⟩
    exact ⟨fuel,
      (MirLiftCore.wpMirExecSym_cone_narrow_poly cone body t₂.toList post h_post fuel _
        (coneReach_of_closedInvLookupPoly h_closed h_no₂ fuel _
          (closedInvLookupPoly_init_of_wf cone body args mem h₁ h_ac h_cs))
        h_at).2 h⟩

end Anneal.OpaqueCalleeTable
