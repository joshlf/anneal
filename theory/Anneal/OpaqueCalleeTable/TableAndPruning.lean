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

/-! `DecidableEq` without `BEq` on the trusted types, the sealed table and its `O(1)`
certificates, exact literal `switchInt` pruning, fuel-bounded evaluation, demanded-key
call-cone narrowing, and canary run summaries. -/

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
  | .uninit => 4

mutual
/-- Structural Boolean equality on the nested inductive `Value`. -/
def valueStructEq : Value → Value → Bool
  | .unit, .unit => true
  | .scalar a, .scalar b => decide (a = b)
  | .ptr p₁ s₁, .ptr p₂ s₂ => decide (p₁ = p₂) && decide (s₁ = s₂)
  | .aggregate v₁ fs₁, .aggregate v₂ fs₂ => decide (v₁ = v₂) && valueListStructEq fs₁ fs₂
  | .uninit, .uninit => true
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
    | .uninit, .uninit, _ => by show true = true ↔ _; simp
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

/-- `hasTraitImplForDefPath` distributes over `++`, separating caller-local `extra`
trait impls from the sealed table-wide `tbl.traitImpls` projection so free-generic
certificates never substitute the `M`-callee `tbl.traitImpls` list at use sites. -/
theorem hasTraitImplForDefPath_append (xs ys : List TraitImplEntry) (defPath : DefPath) :
    hasTraitImplForDefPath (xs ++ ys) defPath =
      (hasTraitImplForDefPath xs defPath || hasTraitImplForDefPath ys defPath) := by
  induction xs with
  | nil => simp [hasTraitImplForDefPath]
  | cons entry rest ih =>
    simp only [List.cons_append, hasTraitImplForDefPath]
    cases stringEq entry.traitRef.defPath defPath
    · simpa using ih
    · simp

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

/-- **`O(1)` certificate (free generic function with arbitrary caller `extra`, `tbl.toList`-free
and `impls`-list-free)**: combines a one-time per-table certificate
`hnoTbl : hasTraitImplForDefPath tbl.traitImpls defPath = false` with a caller-local check
`hnoExtra : hasTraitImplForDefPath extra defPath = false` (`O(|extra|)`), rewriting
`tbl.lookup callerLayouts defPath (firstArg :: restArgs) extra` in `O(1)` independent of
the number `M` of callees or `TraitImplEntry` items in `tbl`. -/
theorem lookupCallee_hit_free_poly_of_noImpl_opaque {tbl : OpaqueCalleeTable}
    {callerLayouts : LayoutTable} {defPath : DefPath} {firstArg : RigidTy}
    {restArgs : List RigidTy} {extra : List TraitImplEntry}
    {c : CapturedMir} {argLayouts : List TypeLayout}
    (hnoTbl : hasTraitImplForDefPath tbl.traitImpls defPath = false)
    (hnoExtra : hasTraitImplForDefPath extra defPath = false)
    (hraw : tbl.lookupRaw defPath = some c)
    (harity : (firstArg :: restArgs).length = c.typeParamCount)
    (hlay : instantiationLayouts? callerLayouts (firstArg :: restArgs) = some argLayouts) :
    tbl.lookup callerLayouts defPath (firstArg :: restArgs) extra =
      some (c.instantiate ((firstArg :: restArgs).zip argLayouts)) := by
  apply lookupCallee_hit_free_poly_opaque rfl _ hraw harity hlay
  rw [hasTraitImplForDefPath_append, hnoExtra, hnoTbl]
  rfl

/-- **`O(1)` miss certificate (absent free function, monomorphic or generic, `tbl.toList`-free)**:
from the sealed `tbl.traitImpls = impls` certificate, `hasTraitImplForDefPath (extra ++ impls)
defPath = false`, and `tbl.lookupRaw defPath = none`, `tbl.lookup` misses for *every* `typeArgs`
without unfolding `tbl.toList`. -/
theorem lookupCallee_miss_free_poly_opaque {tbl : OpaqueCalleeTable} {callerLayouts : LayoutTable}
    {defPath : DefPath} {typeArgs : List RigidTy} {extra impls : List TraitImplEntry}
    (htraits : tbl.traitImpls = impls)
    (hnoImpl : hasTraitImplForDefPath (extra ++ impls) defPath = false)
    (hraw : tbl.lookupRaw defPath = none) :
    tbl.lookup callerLayouts defPath typeArgs extra = none := by
  rw [← htraits, OpaqueCalleeTable.traitImpls_eq] at hnoImpl
  rw [OpaqueCalleeTable.lookupRaw_eq] at hraw
  apply lookupCallee_miss
  cases typeArgs with
  | nil => simp [resolveCalleeBodyAndArgs?, hraw]
  | cons firstArg restArgs =>
    have hnil : collectMatchingTraitImpls tbl.toList (extra ++ flatMapTraitImpls tbl.toList)
        defPath (firstArg :: restArgs) = [] :=
      collectMatchingTraitImpls_of_no_impl _ _ _ _ [] hnoImpl
    cases firstArg <;> simp only [resolveCalleeBodyAndArgs?, hnil, hraw]

/-- **`O(1)` miss certificate (absent free function with arbitrary caller `extra`,
`tbl.toList`-free and `impls`-list-free)**: combines `hasTraitImplForDefPath tbl.traitImpls
defPath = false`, `hasTraitImplForDefPath extra defPath = false`, and `tbl.lookupRaw defPath =
none` without substituting `tbl.traitImpls` at use sites. -/
theorem lookupCallee_miss_free_poly_of_noImpl_opaque {tbl : OpaqueCalleeTable}
    {callerLayouts : LayoutTable} {defPath : DefPath} {typeArgs : List RigidTy}
    {extra : List TraitImplEntry}
    (hnoTbl : hasTraitImplForDefPath tbl.traitImpls defPath = false)
    (hnoExtra : hasTraitImplForDefPath extra defPath = false)
    (hraw : tbl.lookupRaw defPath = none) :
    tbl.lookup callerLayouts defPath typeArgs extra = none := by
  apply lookupCallee_miss_free_poly_opaque rfl _ hraw
  rw [hasTraitImplForDefPath_append, hnoExtra, hnoTbl]
  rfl

/-- **`O(1)` miss certificate (arity-mismatched free generic function, `tbl.toList`-free)**:
`tbl.toList`-free form of `lookupCallee_miss_arity` over `tbl.traitImpls` and `tbl.lookupRaw`. -/
theorem lookupCallee_miss_free_poly_arity_opaque {tbl : OpaqueCalleeTable}
    {callerLayouts : LayoutTable} {defPath : DefPath} {firstArg : RigidTy}
    {restArgs : List RigidTy} {extra impls : List TraitImplEntry} {c : CapturedMir}
    (htraits : tbl.traitImpls = impls)
    (hnoImpl : hasTraitImplForDefPath (extra ++ impls) defPath = false)
    (hraw : tbl.lookupRaw defPath = some c)
    (harity : (firstArg :: restArgs).length ≠ c.typeParamCount) :
    tbl.lookup callerLayouts defPath (firstArg :: restArgs) extra = none := by
  rw [← htraits, OpaqueCalleeTable.traitImpls_eq] at hnoImpl
  exact lookupCallee_miss_arity (resolve_free_poly hnoImpl hraw) (by simp) harity

/-- **`O(1)` miss certificate (uninstantiable free generic function, `tbl.toList`-free)**:
`tbl.toList`-free form of `lookupCallee_miss_uninstantiable` over `tbl.traitImpls` and
`tbl.lookupRaw`. -/
theorem lookupCallee_miss_free_poly_uninstantiable_opaque {tbl : OpaqueCalleeTable}
    {callerLayouts : LayoutTable} {defPath : DefPath} {firstArg : RigidTy}
    {restArgs : List RigidTy} {extra impls : List TraitImplEntry} {c : CapturedMir}
    (htraits : tbl.traitImpls = impls)
    (hnoImpl : hasTraitImplForDefPath (extra ++ impls) defPath = false)
    (hraw : tbl.lookupRaw defPath = some c)
    (harity : (firstArg :: restArgs).length = c.typeParamCount)
    (hlay : instantiationLayouts? callerLayouts (firstArg :: restArgs) = none) :
    tbl.lookup callerLayouts defPath (firstArg :: restArgs) extra = none := by
  rw [← htraits, OpaqueCalleeTable.traitImpls_eq] at hnoImpl
  exact lookupCallee_miss_uninstantiable (resolve_free_poly hnoImpl hraw) (by simp) harity hlay

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

/-- **`O(1)` key miss certificate (absent free function, monomorphic or generic, `tbl.toList`-free)**:
the `CalleeKey` form of `lookupCallee_miss_free_poly_opaque`. -/
theorem lookupKey_miss_free_poly_opaque {tbl : OpaqueCalleeTable} {k : CalleeKey}
    {impls : List TraitImplEntry}
    (htraits : tbl.traitImpls = impls)
    (hnoImpl : hasTraitImplForDefPath (k.extraTraitImpls ++ impls) k.defPath = false)
    (hraw : tbl.lookupRaw k.defPath = none) :
    tbl.lookupKey k = none := by
  obtain ⟨L, dp, tys, ti⟩ := k
  simp only at hnoImpl hraw
  rw [OpaqueCalleeTable.lookupKey_eq]
  exact lookupCallee_miss_free_poly_opaque htraits hnoImpl hraw

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
      evalOperandsWithBodyCast
        localsAfterFunc
        argOps
        s.memory.borrows
        s.memory.globals
        bodyLayouts
        s.memory.callerLocals
        bodyLocalDecls
        s.memory.callStack
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
            MirStepNode.step
              (enterTailCalleeFrame
                (tailCalleeEntryMemory
                  s.memory.callStack
                  memAfterTeardown
                  nLocals
                  (length (initLocals calleeBody (calleeEntryArgs target calleeBody argVals))))
                calleeBody
                (calleeEntryArgs target calleeBody argVals))
        | .none =>
          match Bool.and target.isIndirect (isGenericClosureArityMismatch s.memory.callees target.defPath target.typeArgs) with
          | true => MirStepNode.unsupported
          | false =>
            MirStepNode.extCall
              { defPath := target.defPath, typeArgs := target.typeArgs, args := argVals,
                memory := memAfterTeardown }
              (resumeExternalTailCallWithAbi
                s.memory.rootUnwindCeiling
                (externalTargetCanUnwind target (operandTy bodyLocalDecls bodyLayouts func)))

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
        evalOperandsWithBodyCast
          localsAfterFunc
          argOps
          s.memory.borrows
          s.memory.globals
          bodyLayouts
          s.memory.callerLocals
          bodyLocalDecls
          s.memory.callStack
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
                  (calleeEntryArgs target calleeBody argVals)
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
              match isGenericClosureArityMismatch s.memory.callees target.defPath target.typeArgs with
              | true => MirStepNode.unsupported
              | false =>
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
        evalOperandsWithBodyCast
          localsAfterFunc
          argOps
          s.memory.borrows
          s.memory.globals
          bodyLayouts
          s.memory.callerLocals
          bodyLocalDecls
          s.memory.callStack
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
                  (calleeEntryArgs target calleeBody argVals))
        | .none =>
          -- A diverging call to `core::intrinsics::const_eval_select` (one whose
          -- `called_at_rt` returns `!`) fails closed with `MirStepNode.unsupported`
          -- inside `evalDivergingRustIntrinsic?`, while diverging calls to
          -- returning intrinsics turn normal returns into `MirStepNode.fail .ub`.
          -- Captured MIR never contains `const_eval_select`, because `rustc`
          -- replaces it with a direct call to `called_at_rt` before `optimized_mir`.
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
                  match
                    evalDivergingRustIntrinsic?
                      s
                      target
                      bodyLocalDecls
                      bodyLayouts
                      argOps
                      argVals
                      locals'
                      destination
                  with
                  | .some stepNode => stepNode
                  | .none =>
                    MirStepNode.extCall
                      { defPath := target.defPath, typeArgs := target.typeArgs, args := argVals, memory := s.memory }
                      (resumeExternalDivergingCall s locals' unwind)
          | true =>
            match isGenericClosureArityMismatch s.memory.callees target.defPath target.typeArgs with
            | true => MirStepNode.unsupported
            | false =>
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

/-- At an active terminator, `stepMirFnWith` *is* its terminator step. -/
theorem stepMirFnWith_of_activeTerminator
    (t : MachineState → Terminator → Option CapturedMir → MirStepNode)
    {body : CapturedMir} {s : MachineState} {term : Terminator} {cb : CapturedMir}
    (h : activeTerminator? body s = some (term, cb)) :
    stepMirFnWith t body s = t s term (some cb) := by
  unfold activeTerminator? at h
  unfold stepMirFnWith
  dsimp only at h ⊢
  cases hph : (s.memory.activeCallee.getD body).phase with
  | other name => simp only [hph] at h; nomatch h
  | runtimePostCleanup | runtimeOptimized =>
    simp only [hph] at h ⊢
    cases hbb : get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx with
    | none => simp only [hbb] at h; nomatch h
    | some bb =>
      simp only [hbb] at h ⊢
      cases hst : get? bb.statements s.frame.stmtIdx with
      | some st => simp only [hst] at h; nomatch h
      | none =>
        simp only [hst] at h ⊢
        by_cases hidx : (s.frame.stmtIdx == length bb.statements) = true
        · simp only [hidx, ite_true, Option.some.injEq, Prod.mk.injEq] at h ⊢
          rw [← h.1, ← h.2]
        · simp only [hidx, Bool.false_eq_true, ite_false] at h
          nomatch h

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

end Anneal.OpaqueCalleeTable
