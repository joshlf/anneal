-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Anneal.OpaqueCalleeTable
import Trusted.Rustc.V2026_08_01.Layout
import Trusted.Rustc.V2026_08_01.MirAst.Types
import Trusted.Rustc.V2026_08_01.MirAst.Body
import Trusted.Rustc.V2026_08_01.MirSemantics.Machine

/-!
# Demand-time compiler queries (`CompilerQueryEnv`) and receiver-driven dynamic dispatch

A finite-material, schema-versioned, demand-time compiler query environment over the real
`Trusted.Rustc.V2026_06_01` / `V2026_08_01` layout and MIR types
(`proofs-rs/lean-miri#64`, `#65`, `AeneasVerif/charon#1611`), and the end-to-end dynamic
dispatch step `receiver vtable pointer → UnOp.vtableMethodLookup → abiCompatible →
OpaqueCalleeTable.lookup → stepBranchPruned` built on `Anneal.OpaqueCalleeTable`.

* **Schemas and evidence.** `CompilerSchemaVersion` (`v2026_06_01`, `v2026_08_01` = Schema 12;
  `schema13`) with the decidable total order `SchemaLe`; three-way `QueryResult`
  (`ok` / `err` / `unsupported`); every V2026_08_01 and Schema-13 field of
  `CompilerQueryEnv` is schema-gated (`v08Layouts?`, `cfiEvidence?`, `syncEvidence?`,
  `vtableEvidence?`).
* **Dialect bridges.** Lossless `V2026_06_01 ↔ V2026_08_01` layout and `RigidTy` bridges and
  universal 21-constructor `computeLayout` commutation (`computeLayout_bridge_commutes`,
  `evalLayoutOf_v08_eq_v06`), decidable layout coherence (`isLayoutCoherent`), the canonical
  coherent upgrade `withBridgedV08Layouts`, `EnvExtends` over the schema-gated accessors, and
  `CoherentEnvExtends` (`evalLayoutOf_dialect_invariant_of_coherentExtends`).
* **Five query families** (`layoutOf`, `abiCompatible` with the CFI demand in the key,
  `syncStorageGuard`, `vtableMethodLookup` with the explicit trait-method binding in the key,
  `vtableSupertraitLookup`): fail-closed Schema-12 fallback
  (`query_schema12_unsupported_fallback`), schema monotonicity (`query_mono_schema`),
  eager-catalog and memo agreement, and exact `.ok` characterizations of all five.
* **Dynamic dispatch.** `DynCallSite` reads the receiver's vtable pointer at call time,
  chains supertrait hops through `UnOpExt.query?`, binds the called trait method explicitly
  (`expectedTraitMethod?`, so compiler-generated shims dispatch) or else falls back to the
  fail-closed item-name check `implementsCalledMethod`, and is checked by
  `DynCallSite.wellFormed` (`methodMatchesTrait`, generic supertraits). Registries are
  unambiguous (`DynCallRegistry.findSite?`), unregistered virtual calls fail closed
  (`demandsUnregisteredDyn`), and narrow-run certificates preserve whole runs under
  `EnvExtends` and call-cone narrowing.

Concrete canaries, axiom pins, and the module-wide axiom / namespace audit live in
`tests/mir/CompilerQueryAndOpaqueCalleeTests.lean`.
-/

namespace Anneal.CompilerQueryEnv

open Trusted.Effect (FailureKind Outcome)
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.OpaqueCalleeTable

/-! ## `DecidableEq` without `BEq` on the `Trusted` V2026_08_01 types

As for V2026_06_01 (`Anneal.OpaqueCalleeTable`), every instance is `DecidableEq` only; the
six enumeration-shaped types use `OpaqueCalleeTable.decEqOfCtorIdx`, so no global
`Trusted.Rustc.V2026_08_01.….ofNat` auxiliary is ever emitted, and the nested inductive
`RigidTy` uses an axiom-free Boolean reflection whose diagonal cases unfold by `show`. -/

/-- Left inverse of the V2026_08_01 `AbiPassMode.ctorIdx`. -/
def abiPassModeV08OfIdx : Nat → Trusted.Rustc.V2026_08_01.Layout.AbiPassMode
  | 0 => .ignore | 1 => .direct | 2 => .pair | _ => .indirect

instance instDecidableEqAbiPassModeV08 :
    DecidableEq Trusted.Rustc.V2026_08_01.Layout.AbiPassMode :=
  decEqOfCtorIdx Trusted.Rustc.V2026_08_01.Layout.AbiPassMode.ctorIdx abiPassModeV08OfIdx
    (fun a => by cases a <;> rfl)

/-- Left inverse of the V2026_08_01 `UintTy.ctorIdx`. -/
def uintTyV08OfIdx : Nat → Trusted.Rustc.V2026_08_01.MirAst.UintTy
  | 0 => .u8 | 1 => .u16 | 2 => .u32 | 3 => .u64 | 4 => .u128 | _ => .usize

instance instDecidableEqUintTyV08 : DecidableEq Trusted.Rustc.V2026_08_01.MirAst.UintTy :=
  decEqOfCtorIdx Trusted.Rustc.V2026_08_01.MirAst.UintTy.ctorIdx uintTyV08OfIdx
    (fun a => by cases a <;> rfl)

/-- Left inverse of the V2026_08_01 `IntTy.ctorIdx`. -/
def intTyV08OfIdx : Nat → Trusted.Rustc.V2026_08_01.MirAst.IntTy
  | 0 => .i8 | 1 => .i16 | 2 => .i32 | 3 => .i64 | 4 => .i128 | _ => .isize

instance instDecidableEqIntTyV08 : DecidableEq Trusted.Rustc.V2026_08_01.MirAst.IntTy :=
  decEqOfCtorIdx Trusted.Rustc.V2026_08_01.MirAst.IntTy.ctorIdx intTyV08OfIdx
    (fun a => by cases a <;> rfl)

/-- Left inverse of the V2026_08_01 `FloatTy.ctorIdx`. -/
def floatTyV08OfIdx : Nat → Trusted.Rustc.V2026_08_01.MirAst.FloatTy
  | 0 => .f16 | 1 => .f32 | 2 => .f64 | _ => .f128

instance instDecidableEqFloatTyV08 : DecidableEq Trusted.Rustc.V2026_08_01.MirAst.FloatTy :=
  decEqOfCtorIdx Trusted.Rustc.V2026_08_01.MirAst.FloatTy.ctorIdx floatTyV08OfIdx
    (fun a => by cases a <;> rfl)

/-- Left inverse of the V2026_08_01 `Mutability.ctorIdx`. -/
def mutabilityV08OfIdx : Nat → Trusted.Rustc.V2026_08_01.MirAst.Mutability
  | 0 => .not | _ => .mut

instance instDecidableEqMutabilityV08 :
    DecidableEq Trusted.Rustc.V2026_08_01.MirAst.Mutability :=
  decEqOfCtorIdx Trusted.Rustc.V2026_08_01.MirAst.Mutability.ctorIdx mutabilityV08OfIdx
    (fun a => by cases a <;> rfl)

/-- Left inverse of the V2026_08_01 `Safety.ctorIdx`. -/
def safetyV08OfIdx : Nat → Trusted.Rustc.V2026_08_01.MirAst.Safety
  | 0 => .safe | _ => .unsafe_

instance instDecidableEqSafetyV08 : DecidableEq Trusted.Rustc.V2026_08_01.MirAst.Safety :=
  decEqOfCtorIdx Trusted.Rustc.V2026_08_01.MirAst.Safety.ctorIdx safetyV08OfIdx
    (fun a => by cases a <;> rfl)

/-- Left inverse of the V2026_08_01 `UnOp.ctorIdx`. -/
def unOpV08OfIdx : Nat → Trusted.Rustc.V2026_08_01.MirAst.UnOp
  | 0 => .not | 1 => .neg | _ => .ptrMetadata

instance instDecidableEqUnOpV08 : DecidableEq Trusted.Rustc.V2026_08_01.MirAst.UnOp :=
  decEqOfCtorIdx Trusted.Rustc.V2026_08_01.MirAst.UnOp.ctorIdx unOpV08OfIdx
    (fun a => by cases a <;> rfl)

/-- Left inverse of the V2026_08_01 `BinOp.ctorIdx`. -/
def binOpV08OfIdx : Nat → Trusted.Rustc.V2026_08_01.MirAst.BinOp
  | 0 => .add | 1 => .addUnchecked | 2 => .addWithOverflow | 3 => .sub | 4 => .subUnchecked
  | 5 => .subWithOverflow | 6 => .mul | 7 => .mulUnchecked | 8 => .mulWithOverflow | 9 => .div
  | 10 => .rem | 11 => .bitXor | 12 => .bitAnd | 13 => .bitOr | 14 => .shl | 15 => .shlUnchecked
  | 16 => .shr | 17 => .shrUnchecked | 18 => .eq | 19 => .lt | 20 => .le | 21 => .ne | 22 => .ge
  | 23 => .gt | 24 => .cmp | _ => .offset

instance instDecidableEqBinOpV08 : DecidableEq Trusted.Rustc.V2026_08_01.MirAst.BinOp :=
  decEqOfCtorIdx Trusted.Rustc.V2026_08_01.MirAst.BinOp.ctorIdx binOpV08OfIdx
    (fun a => by cases a <;> rfl)

/-- Left inverse of the V2026_08_01 `RetagKind.ctorIdx`. -/
def retagKindV08OfIdx : Nat → Trusted.Rustc.V2026_08_01.MirAst.RetagKind
  | 0 => .fnEntry | 1 => .twoPhase | 2 => .raw | _ => .default

instance instDecidableEqRetagKindV08 : DecidableEq Trusted.Rustc.V2026_08_01.MirAst.RetagKind :=
  decEqOfCtorIdx Trusted.Rustc.V2026_08_01.MirAst.RetagKind.ctorIdx retagKindV08OfIdx
    (fun a => by cases a <;> rfl)

deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.Layout.Size
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.Layout.Align
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.Layout.WrappingRange
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.Layout.PrimitiveKind
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.Layout.ScalarLayout
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.Layout.FieldsShape
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.Layout.VariantsShape
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.Layout.BackendRepr
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.Layout.TypeLayout
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.Layout.ArgAbi
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.Layout.CallConv
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.Layout.FnAbi
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.Layout.LayoutTable
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.ScalarInt
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.ProvenancePtr
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirSemantics.MirObs

/-- Constructor tag of a V2026_08_01 `RigidTy`: `rigidTyV08StructEq_iff` dispatches on a single
diagonal `match` (off-diagonal constructor pairs are refuted by the match
compiler from `rigidTyV08Tag a = rigidTyV08Tag b`, avoiding a quadratic case split). -/
def rigidTyV08Tag : Trusted.Rustc.V2026_08_01.MirAst.RigidTy → Nat
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
def rigidTyV08StructEq : Trusted.Rustc.V2026_08_01.MirAst.RigidTy → Trusted.Rustc.V2026_08_01.MirAst.RigidTy → Bool
  | .param i n, .param j m => decide (i = j) && decide (n = m)
  | .alias d as, .alias e bs => decide (d = e) && rigidTyV08ListStructEq as bs
  | .bool, .bool => true
  | .char, .char => true
  | .int w, .int v => decide (w = v)
  | .uint w, .uint v => decide (w = v)
  | .float w, .float v => decide (w = v)
  | .never, .never => true
  | .str, .str => true
  | .tuple as, .tuple bs => rigidTyV08ListStructEq as bs
  | .array x n, .array y m => rigidTyV08StructEq x y && decide (n = m)
  | .slice x, .slice y => rigidTyV08StructEq x y
  | .ref m x, .ref n y => decide (m = n) && rigidTyV08StructEq x y
  | .rawPtr m x, .rawPtr n y => decide (m = n) && rigidTyV08StructEq x y
  | .adt d as, .adt e bs => decide (d = e) && rigidTyV08ListStructEq as bs
  | .fnDef d as, .fnDef e bs => decide (d = e) && rigidTyV08ListStructEq as bs
  | .fnPtr ins o sf cc, .fnPtr jns p tf dd =>
    rigidTyV08ListStructEq ins jns && rigidTyV08StructEq o p && decide (sf = tf) && decide (cc = dd)
  | .closure d as, .closure e bs => decide (d = e) && rigidTyV08ListStructEq as bs
  | .dynamic d, .dynamic e => decide (d = e)
  | .foreign d, .foreign e => decide (d = e)
  | .other d, .other e => decide (d = e)
  | _, _ => false

/-- Pointwise companion of `rigidTyV08StructEq`. -/
def rigidTyV08ListStructEq : List Trusted.Rustc.V2026_08_01.MirAst.RigidTy → List Trusted.Rustc.V2026_08_01.MirAst.RigidTy → Bool
  | [], [] => true
  | a :: as, b :: bs => rigidTyV08StructEq a b && rigidTyV08ListStructEq as bs
  | _, _ => false
end

/-- Off the constructor diagonal, `rigidTyV08StructEq` is `false` (one cheap case per
constructor pair; no recursion needed). -/
theorem rigidTyV08StructEq_of_tag_ne {a b : Trusted.Rustc.V2026_08_01.MirAst.RigidTy} (h : rigidTyV08Tag a ≠ rigidTyV08Tag b) :
    rigidTyV08StructEq a b = false := by
  cases a <;> cases b <;> first | rfl | exact absurd rfl h

mutual
/-- `rigidTyV08StructEq` decides `RigidTy` equality. Each diagonal case is unfolded by
`show` (definitional unfolding) rather than `simp [rigidTyV08StructEq]`, so no
equation lemmas are generated for the catch-all definition: Lean proves the
catch-all equation `rigidTyV08StructEq.eq_22` (and `eq_def`) with whatever simp set
the *ambient import closure* provides, and inside the `Anneal` root closure those
auto-generated lemmas depend on `Classical.choice` (caught by the module audit). -/
theorem rigidTyV08StructEq_iff (a b : Trusted.Rustc.V2026_08_01.MirAst.RigidTy) : rigidTyV08StructEq a b = true ↔ a = b :=
  if hTag : rigidTyV08Tag a = rigidTyV08Tag b then
    match a, b, hTag with
    | .param i n, .param j m, _ => by
      show (decide (i = j) && decide (n = m)) = true ↔ _
      simp
    | .alias d as, .alias e bs, _ => by
      have ih := rigidTyV08ListStructEq_iff as bs
      show (decide (d = e) && rigidTyV08ListStructEq as bs) = true ↔ _
      simp [ih]
    | .bool, .bool, _ => by show true = true ↔ _; simp
    | .char, .char, _ => by show true = true ↔ _; simp
    | .int w, .int v, _ => by show decide (w = v) = true ↔ _; simp
    | .uint w, .uint v, _ => by show decide (w = v) = true ↔ _; simp
    | .float w, .float v, _ => by show decide (w = v) = true ↔ _; simp
    | .never, .never, _ => by show true = true ↔ _; simp
    | .str, .str, _ => by show true = true ↔ _; simp
    | .tuple as, .tuple bs, _ => by
      have ih := rigidTyV08ListStructEq_iff as bs
      show rigidTyV08ListStructEq as bs = true ↔ _
      simp [ih]
    | .array x n, .array y m, _ => by
      have ih := rigidTyV08StructEq_iff x y
      show (rigidTyV08StructEq x y && decide (n = m)) = true ↔ _
      simp [ih]
    | .slice x, .slice y, _ => by
      have ih := rigidTyV08StructEq_iff x y
      show rigidTyV08StructEq x y = true ↔ _
      simp [ih]
    | .ref m x, .ref n y, _ => by
      have ih := rigidTyV08StructEq_iff x y
      show (decide (m = n) && rigidTyV08StructEq x y) = true ↔ _
      simp [ih]
    | .rawPtr m x, .rawPtr n y, _ => by
      have ih := rigidTyV08StructEq_iff x y
      show (decide (m = n) && rigidTyV08StructEq x y) = true ↔ _
      simp [ih]
    | .adt d as, .adt e bs, _ => by
      have ih := rigidTyV08ListStructEq_iff as bs
      show (decide (d = e) && rigidTyV08ListStructEq as bs) = true ↔ _
      simp [ih]
    | .fnDef d as, .fnDef e bs, _ => by
      have ih := rigidTyV08ListStructEq_iff as bs
      show (decide (d = e) && rigidTyV08ListStructEq as bs) = true ↔ _
      simp [ih]
    | .fnPtr ins o sf cc, .fnPtr jns p tf dd, _ => by
      have ih₁ := rigidTyV08ListStructEq_iff ins jns
      have ih₂ := rigidTyV08StructEq_iff o p
      show (rigidTyV08ListStructEq ins jns && rigidTyV08StructEq o p && decide (sf = tf) &&
        decide (cc = dd)) = true ↔ _
      simp [ih₁, ih₂, Bool.and_assoc]
    | .closure d as, .closure e bs, _ => by
      have ih := rigidTyV08ListStructEq_iff as bs
      show (decide (d = e) && rigidTyV08ListStructEq as bs) = true ↔ _
      simp [ih]
    | .dynamic d, .dynamic e, _ => by show decide (d = e) = true ↔ _; simp
    | .foreign d, .foreign e, _ => by show decide (d = e) = true ↔ _; simp
    | .other d, .other e, _ => by show decide (d = e) = true ↔ _; simp
  else by
    rw [rigidTyV08StructEq_of_tag_ne hTag]
    exact ⟨(fun h => nomatch h), fun e => absurd (congrArg rigidTyV08Tag e) hTag⟩

/-- Pointwise companion of `rigidTyV08StructEq_iff`. -/
theorem rigidTyV08ListStructEq_iff (as bs : List Trusted.Rustc.V2026_08_01.MirAst.RigidTy) :
    rigidTyV08ListStructEq as bs = true ↔ as = bs :=
  match as, bs with
  | [], [] => by show true = true ↔ _; simp
  | [], _ :: _ => by show false = true ↔ _; simp
  | _ :: _, [] => by show false = true ↔ _; simp
  | a :: as, b :: bs => by
    have ih₁ := rigidTyV08StructEq_iff a b
    have ih₂ := rigidTyV08ListStructEq_iff as bs
    show (rigidTyV08StructEq a b && rigidTyV08ListStructEq as bs) = true ↔ _
    simp [ih₁, ih₂]
end

/-- Axiom-free manual `DecidableEq` for the nested inductive V2026_08_01 `RigidTy`
(`deriving DecidableEq` does not support nested inductives). -/
instance instDecidableEqRigidTyV08 : DecidableEq Trusted.Rustc.V2026_08_01.MirAst.RigidTy :=
  fun a b => decidable_of_iff _ (rigidTyV08StructEq_iff a b)

deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.Ty
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.TraitRef
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.TraitImplEntry
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.ConstScalar
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.ConstValue
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.ConstOperand
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.MirPhaseTag
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.ContractRole
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.GenericParamDef
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.ProjectionElem
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.Place
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.Operand
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.NullOp
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.BorrowKind
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.CastKind
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.AggregateKind
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.Rvalue
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.NonDivergingIntrinsic
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.StatementKind
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.Statement
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.SwitchTargets
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.UnwindAction
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.TerminatorKind
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.Terminator
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.BasicBlockData
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.LocalDecl
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.CapturedAllocation
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirAst.CapturedMir

/-- Constructor tag of a V2026_08_01 `Value`. -/
def valueV08Tag : Trusted.Rustc.V2026_08_01.MirSemantics.Value → Nat
  | .unit => 0
  | .scalar _ => 1
  | .ptr .. => 2
  | .aggregate .. => 3

mutual
/-- Structural Boolean equality on the nested inductive V2026_08_01 `Value`. -/
def valueV08StructEq :
    Trusted.Rustc.V2026_08_01.MirSemantics.Value →
      Trusted.Rustc.V2026_08_01.MirSemantics.Value → Bool
  | .unit, .unit => true
  | .scalar a, .scalar b => decide (a = b)
  | .ptr p₁ s₁, .ptr p₂ s₂ => decide (p₁ = p₂) && decide (s₁ = s₂)
  | .aggregate v₁ fs₁, .aggregate v₂ fs₂ => decide (v₁ = v₂) && valueV08ListStructEq fs₁ fs₂
  | _, _ => false

/-- Pointwise companion of `valueV08StructEq`. -/
def valueV08ListStructEq :
    List Trusted.Rustc.V2026_08_01.MirSemantics.Value →
      List Trusted.Rustc.V2026_08_01.MirSemantics.Value → Bool
  | [], [] => true
  | a :: as, b :: bs => valueV08StructEq a b && valueV08ListStructEq as bs
  | _, _ => false
end

theorem valueV08StructEq_of_tag_ne
    {a b : Trusted.Rustc.V2026_08_01.MirSemantics.Value} (h : valueV08Tag a ≠ valueV08Tag b) :
    valueV08StructEq a b = false := by
  cases a <;> cases b <;> first | rfl | exact absurd rfl h

mutual
/-- `valueV08StructEq` decides V2026_08_01 `Value` equality (diagonal cases unfolded via
`show` so zero `Classical.choice` equation lemmas are synthesized). -/
theorem valueV08StructEq_iff
    (a b : Trusted.Rustc.V2026_08_01.MirSemantics.Value) :
    valueV08StructEq a b = true ↔ a = b :=
  if hTag : valueV08Tag a = valueV08Tag b then
    match a, b, hTag with
    | .unit, .unit, _ => by show true = true ↔ _; simp
    | .scalar x, .scalar y, _ => by show decide (x = y) = true ↔ _; simp
    | .ptr p₁ s₁, .ptr p₂ s₂, _ => by
      show (decide (p₁ = p₂) && decide (s₁ = s₂)) = true ↔ _
      simp
    | .aggregate v₁ fs₁, .aggregate v₂ fs₂, _ => by
      have ih := valueV08ListStructEq_iff fs₁ fs₂
      show (decide (v₁ = v₂) && valueV08ListStructEq fs₁ fs₂) = true ↔ _
      simp [ih]
  else by
    rw [valueV08StructEq_of_tag_ne hTag]
    exact ⟨(fun h => nomatch h), fun e => absurd (congrArg valueV08Tag e) hTag⟩

/-- Pointwise companion of `valueV08StructEq_iff`. -/
theorem valueV08ListStructEq_iff
    (as bs : List Trusted.Rustc.V2026_08_01.MirSemantics.Value) :
    valueV08ListStructEq as bs = true ↔ as = bs :=
  match as, bs with
  | [], [] => by show true = true ↔ _; simp
  | [], _ :: _ => by show false = true ↔ _; simp
  | _ :: _, [] => by show false = true ↔ _; simp
  | a :: as, b :: bs => by
    have ih₁ := valueV08StructEq_iff a b
    have ih₂ := valueV08ListStructEq_iff as bs
    show (valueV08StructEq a b && valueV08ListStructEq as bs) = true ↔ _
    simp [ih₁, ih₂]
end

/-- Axiom-free manual `DecidableEq` for the nested inductive V2026_08_01 `Value`. -/
instance instDecidableEqValueV08 :
    DecidableEq Trusted.Rustc.V2026_08_01.MirSemantics.Value :=
  fun a b => decidable_of_iff _ (valueV08StructEq_iff a b)

deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirSemantics.LocalSlot
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirSemantics.StackFrame
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirSemantics.TreeBorrowPerm
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirSemantics.BorrowEntry
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirSemantics.SavedCallerFrame
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirSemantics.FnPtrEntry
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirSemantics.Memory
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirSemantics.MachineState
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirSemantics.MirCallReq
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.MirSemantics.MirExecState

/-- `LawfulBEq` for V2026_08_01 `CapturedMir` through `instBEqOfDecidableEq`. -/
theorem capturedMirV08_beq_iff_eq
    {a b : Trusted.Rustc.V2026_08_01.MirAst.CapturedMir} : (a == b) = true ↔ a = b :=
  beq_iff_eq

/-- `LawfulBEq` for V2026_08_01 `MachineState` through `instBEqOfDecidableEq`. -/
theorem machineStateV08_beq_iff_eq
    {a b : Trusted.Rustc.V2026_08_01.MirSemantics.MachineState} : (a == b) = true ↔ a = b :=
  beq_iff_eq

/-- `LawfulBEq` for V2026_08_01 `TreeBorrowPerm` through `instBEqOfDecidableEq`: only
`DecidableEq` is derived here, so the redundant structural `BEq` of
`theory/Correspondence/V2026_08_01/L4_TreeBorrows.lean:61` is never needed. -/
theorem treeBorrowPermV08_beq_iff_eq
    {a b : Trusted.Rustc.V2026_08_01.MirSemantics.TreeBorrowPerm} : (a == b) = true ↔ a = b :=
  beq_iff_eq

/-- `BEq` on V2026_08_01 `RigidTy` is `instBEqOfDecidableEq`. -/
theorem rigidTyV08_beq_eq_decide
    (a b : Trusted.Rustc.V2026_08_01.MirAst.RigidTy) : (a == b) = decide (a = b) := rfl

/-- `LawfulBEq` for V2026_08_01 `RigidTy` through `instBEqOfDecidableEq`. -/
theorem rigidTyV08_beq_iff_eq
    {a b : Trusted.Rustc.V2026_08_01.MirAst.RigidTy} : (a == b) = true ↔ a = b :=
  beq_iff_eq

/-- `LawfulBEq` for V2026_08_01 `LayoutTable` through `instBEqOfDecidableEq`. -/
theorem layoutTableV08_beq_iff_eq
    {a b : Trusted.Rustc.V2026_08_01.Layout.LayoutTable} : (a == b) = true ↔ a = b :=
  beq_iff_eq

/-- `LawfulBEq` for V2026_08_01 `TraitImplEntry` through `instBEqOfDecidableEq`. -/
theorem traitImplEntryV08_beq_iff_eq
    {a b : Trusted.Rustc.V2026_08_01.MirAst.TraitImplEntry} : (a == b) = true ↔ a = b :=
  beq_iff_eq

/-- `LawfulBEq` for V2026_08_01 `FnAbi` through `instBEqOfDecidableEq`. -/
theorem fnAbiV08_beq_iff_eq
    {a b : Trusted.Rustc.V2026_08_01.Layout.FnAbi} : (a == b) = true ↔ a = b :=
  beq_iff_eq

/-! ## Multi-version demand-time `CompilerQueryEnv` -/

/-- Compiler schema version of the captured evidence (`proofs-rs/lean-miri#64`,
`#65`). -/
inductive CompilerSchemaVersion : Type where
  /-- Schema 12 producer, `rustc` 2026-06-01 dialect. -/
  | v2026_06_01
  /-- Schema 12 producer, `rustc` 2026-08-01 dialect (adds the V2026_08_01 layout dialect). -/
  | v2026_08_01
  /-- Schema 13 producer (adds CFI ABI evidence, sync-object storage regions, and
  `UnOp.vtableMethodLookup` vtable evidence). -/
  | schema13
  deriving DecidableEq, Repr

/-- Rank of a schema version in the upgrade order. -/
def CompilerSchemaVersion.rank : CompilerSchemaVersion → Nat
  | .v2026_06_01 => 0
  | .v2026_08_01 => 1
  | .schema13 => 2

/-- Schema upgrade order. -/
def SchemaLe (a b : CompilerSchemaVersion) : Prop := a.rank ≤ b.rank

instance instDecidableRelSchemaLe : DecidableRel SchemaLe := fun a b => Nat.decLe a.rank b.rank

theorem SchemaLe.refl (a : CompilerSchemaVersion) : SchemaLe a a := Nat.le_refl _

theorem SchemaLe.trans {a b c : CompilerSchemaVersion} (h₁ : SchemaLe a b) (h₂ : SchemaLe b c) :
    SchemaLe a c := Nat.le_trans h₁ h₂

theorem SchemaLe.antisymm {a b : CompilerSchemaVersion} (h₁ : SchemaLe a b) (h₂ : SchemaLe b a) :
    a = b := by
  cases a <;> cases b <;> simp_all [SchemaLe, CompilerSchemaVersion.rank]

theorem SchemaLe.total (a b : CompilerSchemaVersion) : SchemaLe a b ∨ SchemaLe b a :=
  Nat.le_total _ _

/-- Schema 13 evidence is available. -/
def CompilerSchemaVersion.hasSchema13 : CompilerSchemaVersion → Bool
  | .schema13 => true
  | _ => false

/-- The V2026_08_01 layout dialect is available. -/
def CompilerSchemaVersion.hasV08Layouts : CompilerSchemaVersion → Bool
  | .v2026_06_01 => false
  | _ => true

/-- Schema 12 producers. -/
def CompilerSchemaVersion.isSchema12 : CompilerSchemaVersion → Bool
  | .schema13 => false
  | _ => true

theorem hasSchema13_mono {a b : CompilerSchemaVersion} (h : SchemaLe a b)
    (ha : a.hasSchema13 = true) : b.hasSchema13 = true := by
  cases a <;> cases b <;>
    simp_all [SchemaLe, CompilerSchemaVersion.rank, CompilerSchemaVersion.hasSchema13]

theorem hasV08Layouts_mono {a b : CompilerSchemaVersion} (h : SchemaLe a b)
    (ha : a.hasV08Layouts = true) : b.hasV08Layouts = true := by
  cases a <;> cases b <;>
    simp_all [SchemaLe, CompilerSchemaVersion.rank, CompilerSchemaVersion.hasV08Layouts]

/-- Optional evidence that a query needs but the environment lacks. -/
inductive MissingEvidence : Type where
  /-- The V2026_08_01 layout dialect (schema < V2026_08_01 or no V08 table). -/
  | missingV08LayoutDialect
  /-- Schema-13 CFI type-id evidence. -/
  | missingCfiEvidence
  /-- Schema-13 synchronization-object storage regions (`lean-miri#65`). -/
  | missingSyncStorage
  /-- Schema-13 vtable dispatch entries (`charon#1611`). -/
  | missingVTableEvidence
  deriving DecidableEq, Repr

/-- A Schema-13 synchronization-object storage region `[offset, offset + size)` of
allocation `allocId` (`lean-miri#65`). -/
structure SyncStorageRegion : Type where
  allocId : AllocId
  offset : Nat
  size : Nat
  deriving DecidableEq, Repr

/-- Genuine semantic / ABI / bounds failures (never "evidence absent"). -/
inductive QueryErr : Type where
  | layoutUncomputable
  | unknownCalleeAbi (callee : DefPath)
  | callConvMismatch
  | argCountMismatch
  | argModeMismatch (idx : Nat)
  | argLayoutMismatch (idx : Nat)
  | retAbiMismatch
  | unwindMismatch
  /-- CFI type-id mismatch (a defined CFI trap, not UB). -/
  | cfiTypeIdMismatch
  | cfiCalleeUntagged (callee : DefPath)
  | cfiCallSiteUntagged
  | syncStorageOverlap (region : SyncStorageRegion)
  | vtableNotFound (vtableId : Nat)
  | vtableTraitMismatch
  | vtableSlotOutOfBounds (slotIdx : Nat)
  /-- The vtable slot is not bound to the trait method the lookup expects
  (`VTableMethodLookupOp.expectedTraitMethod?` vs. `VTableMethodEntry.slotTraitMethods`). -/
  | vtableSlotMethodMismatch (slotIdx : Nat)
  | vtableSupertraitNotFound (vtableId : Nat) (superTrait : TraitRef)
  | answerKindMismatch
  deriving DecidableEq

/-- Three-way demand-time query result. -/
inductive QueryResult (α : Type) : Type where
  | ok (val : α)
  | err (reason : QueryErr)
  | unsupported (missing : MissingEvidence)
  deriving DecidableEq

/-- Layout dialect requested by a `layoutOf` query. -/
inductive LayoutDialect : Type where
  | v2026_06_01
  | v2026_08_01
  deriving DecidableEq, Repr

/-- Schema-13 CFI evidence: `cfi_typeid` of each address-taken callee and of each
indirect call-site function-pointer type. -/
structure CfiTagSpec : Type where
  calleeTypeIds : List (DefPath × Nat)
  callSiteTypeIds : List (RigidTy × Nat)
  deriving DecidableEq

/-- Schema-13 vtable evidence (`charon#1611`): the method slots of vtable
`vtableId` for `traitRef`, plus direct supertrait vtable pointer slots
`(superTraitRef, superVTableId)` for supertrait upcasting / chained method lookup, and
the explicit trait-method binding of each method slot (`slotTraitMethods`, the
trait-method `DefPath` of the vtable field, as carried by `charon#1611`'s
`UnOp::VTableMethodLookup`; `[]` for evidence without bindings). -/
structure VTableMethodEntry : Type where
  vtableId : Nat
  traitRef : TraitRef
  methods : List (DefPath × List RigidTy)
  supertraits : List (TraitRef × Nat) := []
  /-- `slotTraitMethods[i]` is the trait method implemented by slot `i` (when bound). -/
  slotTraitMethods : List DefPath := []
  deriving DecidableEq

/-- Demand-time compiler queries. -/
inductive CompilerQuery : Type where
  /-- `layout_of(ty)` in a layout dialect. -/
  | layoutOf (dialect : LayoutDialect) (ty : Ty)
  /-- ABI compatibility of a call to `callee` under the caller-side `callerAbi`;
  `cfiCallSite = some fnPtrTy` requests the Schema-13 CFI check. -/
  | abiCompatible (callerAbi : FnAbi) (callee : DefPath) (cfiCallSite : Option RigidTy)
  /-- Sync-object storage guard for the byte access `[offset, offset + len)` of `allocId`. -/
  | syncStorageGuard (allocId : AllocId) (offset len : Nat)
  /-- `UnOp.vtableMethodLookup` (`charon#1611`); `expectedTraitMethod? = some m` additionally
  demands that slot `slotIdx` be bound to trait method `m` (the demand is part of the key). -/
  | vtableMethodLookup (vtableId : Nat) (traitRef : TraitRef) (slotIdx : Nat)
      (expectedTraitMethod? : Option DefPath)
  /-- Supertrait vtable pointer lookup (`charon#1611` supertrait upcast / chained
  method lookup): resolves the vtable allocation id for `superTrait` inside
  `vtableId` (`traitRef`). -/
  | vtableSupertraitLookup (vtableId : Nat) (traitRef superTrait : TraitRef)
  deriving DecidableEq

/-- Answers of demand-time queries. -/
inductive QueryAnswer : Type where
  | layout (l : TypeLayout)
  | abiOk
  | syncPermit
  | method (defPath : DefPath) (typeArgs : List RigidTy)
  | supertraitVTable (vtableId : Nat)
  deriving DecidableEq

/-- Memoization key of a demand-time query (`QueryKey`). -/
structure QueryKey : Type where
  schema : CompilerSchemaVersion
  query : CompilerQuery
  deriving DecidableEq

/-! ### V2026_08_01 → V2026_06_01 layout bridges -/


/-- Bridge a V2026_08_01 `Size`. -/
def bridgeSizeV08ToV06 (x : Trusted.Rustc.V2026_08_01.Layout.Size) : Size := ⟨x.bytes⟩

/-- Bridge a V2026_08_01 `Align`. -/
def bridgeAlignV08ToV06 (x : Trusted.Rustc.V2026_08_01.Layout.Align) : Align := ⟨x.bytes⟩

/-- Bridge a V2026_08_01 `WrappingRange`. -/
def bridgeWrappingRangeV08ToV06 (x : Trusted.Rustc.V2026_08_01.Layout.WrappingRange) :
    WrappingRange := ⟨x.start, x.end_⟩

/-- Bridge a V2026_08_01 `PrimitiveKind`. -/
def bridgePrimitiveKindV08ToV06 : Trusted.Rustc.V2026_08_01.Layout.PrimitiveKind → PrimitiveKind
  | .int bits signed => .int bits signed
  | .float bits => .float bits
  | .pointer addressSpace => .pointer addressSpace

/-- Bridge a V2026_08_01 `ScalarLayout`. -/
def bridgeScalarLayoutV08ToV06 : Trusted.Rustc.V2026_08_01.Layout.ScalarLayout → ScalarLayout
  | .initialized v r => .initialized (bridgePrimitiveKindV08ToV06 v) (bridgeWrappingRangeV08ToV06 r)
  | .union v => .union (bridgePrimitiveKindV08ToV06 v)

/-- Bridge a V2026_08_01 `FieldsShape`. -/
def bridgeFieldsShapeV08ToV06 : Trusted.Rustc.V2026_08_01.Layout.FieldsShape → FieldsShape
  | .primitive => .primitive
  | .union count => .union count
  | .array stride count => .array (bridgeSizeV08ToV06 stride) count
  | .arbitrary offsets memoryIndex => .arbitrary (offsets.map bridgeSizeV08ToV06) memoryIndex

/-- Bridge a V2026_08_01 `VariantsShape`. -/
def bridgeVariantsShapeV08ToV06 : Trusted.Rustc.V2026_08_01.Layout.VariantsShape → VariantsShape
  | .empty => .empty
  | .single index => .single index
  | .multiple tag tagField variants =>
    .multiple (bridgeScalarLayoutV08ToV06 tag) tagField (variants.map bridgeFieldsShapeV08ToV06)

/-- Bridge a V2026_08_01 `BackendRepr`. -/
def bridgeBackendReprV08ToV06 : Trusted.Rustc.V2026_08_01.Layout.BackendRepr → BackendRepr
  | .scalar x => .scalar (bridgeScalarLayoutV08ToV06 x)
  | .scalarPair a b => .scalarPair (bridgeScalarLayoutV08ToV06 a) (bridgeScalarLayoutV08ToV06 b)
  | .memory => .memory

/-- Bridge a V2026_08_01 `TypeLayout` to V2026_06_01. -/
def bridgeTypeLayoutV08ToV06 (l : Trusted.Rustc.V2026_08_01.Layout.TypeLayout) : TypeLayout :=
  { size := bridgeSizeV08ToV06 l.size
    align := bridgeAlignV08ToV06 l.align
    backendRepr := bridgeBackendReprV08ToV06 l.backendRepr
    fields := bridgeFieldsShapeV08ToV06 l.fields
    variants := bridgeVariantsShapeV08ToV06 l.variants
    isUninhabited := l.isUninhabited
    fieldLayouts := l.fieldLayouts }

/-- Bridge a V2026_08_01 `LayoutTable` to V2026_06_01. -/
def bridgeLayoutV08ToV06 (t : Trusted.Rustc.V2026_08_01.Layout.LayoutTable) : LayoutTable :=
  { pointerBits := t.pointerBits
    isLittleEndian := t.isLittleEndian
    entries := t.entries.map bridgeTypeLayoutV08ToV06 }

/-- Reverse bridge of `Size`. -/
def bridgeSizeV06ToV08 (x : Size) : Trusted.Rustc.V2026_08_01.Layout.Size := ⟨x.bytes⟩

/-- Reverse bridge of `Align`. -/
def bridgeAlignV06ToV08 (x : Align) : Trusted.Rustc.V2026_08_01.Layout.Align := ⟨x.bytes⟩

/-- Reverse bridge of `WrappingRange`. -/
def bridgeWrappingRangeV06ToV08 (x : WrappingRange) :
    Trusted.Rustc.V2026_08_01.Layout.WrappingRange := ⟨x.start, x.end_⟩

/-- Reverse bridge of `PrimitiveKind`. -/
def bridgePrimitiveKindV06ToV08 : PrimitiveKind → Trusted.Rustc.V2026_08_01.Layout.PrimitiveKind
  | .int bits signed => .int bits signed
  | .float bits => .float bits
  | .pointer addressSpace => .pointer addressSpace

/-- Reverse bridge of `ScalarLayout`. -/
def bridgeScalarLayoutV06ToV08 : ScalarLayout → Trusted.Rustc.V2026_08_01.Layout.ScalarLayout
  | .initialized v r => .initialized (bridgePrimitiveKindV06ToV08 v) (bridgeWrappingRangeV06ToV08 r)
  | .union v => .union (bridgePrimitiveKindV06ToV08 v)

/-- Reverse bridge of `FieldsShape`. -/
def bridgeFieldsShapeV06ToV08 : FieldsShape → Trusted.Rustc.V2026_08_01.Layout.FieldsShape
  | .primitive => .primitive
  | .union count => .union count
  | .array stride count => .array (bridgeSizeV06ToV08 stride) count
  | .arbitrary offsets memoryIndex => .arbitrary (offsets.map bridgeSizeV06ToV08) memoryIndex

/-- Reverse bridge of `VariantsShape`. -/
def bridgeVariantsShapeV06ToV08 : VariantsShape → Trusted.Rustc.V2026_08_01.Layout.VariantsShape
  | .empty => .empty
  | .single index => .single index
  | .multiple tag tagField variants =>
    .multiple (bridgeScalarLayoutV06ToV08 tag) tagField (variants.map bridgeFieldsShapeV06ToV08)

/-- Reverse bridge of `BackendRepr`. -/
def bridgeBackendReprV06ToV08 : BackendRepr → Trusted.Rustc.V2026_08_01.Layout.BackendRepr
  | .scalar x => .scalar (bridgeScalarLayoutV06ToV08 x)
  | .scalarPair a b => .scalarPair (bridgeScalarLayoutV06ToV08 a) (bridgeScalarLayoutV06ToV08 b)
  | .memory => .memory

/-- Reverse bridge of `TypeLayout`. -/
def bridgeTypeLayoutV06ToV08 (l : TypeLayout) : Trusted.Rustc.V2026_08_01.Layout.TypeLayout :=
  { size := bridgeSizeV06ToV08 l.size
    align := bridgeAlignV06ToV08 l.align
    backendRepr := bridgeBackendReprV06ToV08 l.backendRepr
    fields := bridgeFieldsShapeV06ToV08 l.fields
    variants := bridgeVariantsShapeV06ToV08 l.variants
    isUninhabited := l.isUninhabited
    fieldLayouts := l.fieldLayouts }

/-- Reverse bridge of `LayoutTable`. -/
def bridgeLayoutV06ToV08 (t : LayoutTable) : Trusted.Rustc.V2026_08_01.Layout.LayoutTable :=
  { pointerBits := t.pointerBits
    isLittleEndian := t.isLittleEndian
    entries := t.entries.map bridgeTypeLayoutV06ToV08 }

theorem bridgeScalarLayout_roundtrip (x : ScalarLayout) :
    bridgeScalarLayoutV08ToV06 (bridgeScalarLayoutV06ToV08 x) = x := by
  cases x with
  | initialized v r => cases v <;> rfl
  | union v => cases v <;> rfl

theorem bridgeFieldsShape_roundtrip (x : FieldsShape) :
    bridgeFieldsShapeV08ToV06 (bridgeFieldsShapeV06ToV08 x) = x := by
  cases x with
  | arbitrary offsets memoryIndex =>
    simp only [bridgeFieldsShapeV06ToV08, bridgeFieldsShapeV08ToV06, List.map_map]
    congr
    conv => rhs; rw [← List.map_id offsets]
    rfl
  | _ => rfl

/-- **Lossless bridge**: V2026_06_01 → V2026_08_01 → V2026_06_01 is the identity
on `TypeLayout`. -/
theorem bridgeTypeLayout_roundtrip (l : TypeLayout) :
    bridgeTypeLayoutV08ToV06 (bridgeTypeLayoutV06ToV08 l) = l := by
  obtain ⟨size, align, backendRepr, fields, variants, isUninhabited, fieldLayouts⟩ := l
  simp only [bridgeTypeLayoutV06ToV08, bridgeTypeLayoutV08ToV06]
  congr 1
  · cases backendRepr <;> simp [bridgeBackendReprV06ToV08, bridgeBackendReprV08ToV06,
      bridgeScalarLayout_roundtrip]
  · exact bridgeFieldsShape_roundtrip fields
  · cases variants with
    | multiple tag tagField vs =>
      simp only [bridgeVariantsShapeV06ToV08, bridgeVariantsShapeV08ToV06, List.map_map,
        bridgeScalarLayout_roundtrip]
      congr
      conv => rhs; rw [← List.map_id vs]
      apply List.map_congr_left
      intro x _
      exact bridgeFieldsShape_roundtrip x
    | _ => rfl

/-- **Lossless table bridge** on `LayoutTable`. -/
theorem bridgeLayout_roundtrip (t : LayoutTable) :
    bridgeLayoutV08ToV06 (bridgeLayoutV06ToV08 t) = t := by
  obtain ⟨pointerBits, isLittleEndian, entries⟩ := t
  simp only [bridgeLayoutV06ToV08, bridgeLayoutV08ToV06, List.map_map]
  congr
  conv => rhs; rw [← List.map_id entries]
  apply List.map_congr_left
  intro x _
  exact bridgeTypeLayout_roundtrip x

/-- Bridge a V2026_06_01 `CallConv` to V2026_08_01. -/
def bridgeCallConvV06ToV08 : CallConv → Trusted.Rustc.V2026_08_01.Layout.CallConv
  | .rust => .rust
  | .c => .c
  | .rustIntrinsic => .rustIntrinsic
  | .other name => .other name

/-- Bridge a V2026_06_01 `UintTy`. -/
def bridgeUintTyV06ToV08 : UintTy → Trusted.Rustc.V2026_08_01.MirAst.UintTy
  | .u8 => .u8 | .u16 => .u16 | .u32 => .u32 | .u64 => .u64 | .u128 => .u128 | .usize => .usize

/-- Bridge a V2026_06_01 `IntTy`. -/
def bridgeIntTyV06ToV08 : IntTy → Trusted.Rustc.V2026_08_01.MirAst.IntTy
  | .i8 => .i8 | .i16 => .i16 | .i32 => .i32 | .i64 => .i64 | .i128 => .i128 | .isize => .isize

/-- Bridge a V2026_06_01 `FloatTy`. -/
def bridgeFloatTyV06ToV08 : FloatTy → Trusted.Rustc.V2026_08_01.MirAst.FloatTy
  | .f16 => .f16 | .f32 => .f32 | .f64 => .f64 | .f128 => .f128

/-- Bridge a V2026_06_01 `Mutability`. -/
def bridgeMutabilityV06ToV08 : Mutability → Trusted.Rustc.V2026_08_01.MirAst.Mutability
  | .not => .not | .mut => .mut

/-- Bridge a V2026_06_01 `Safety`. -/
def bridgeSafetyV06ToV08 : Safety → Trusted.Rustc.V2026_08_01.MirAst.Safety
  | .safe => .safe | .unsafe_ => .unsafe_

mutual
/-- Bridge a V2026_06_01 `RigidTy` to V2026_08_01. -/
def bridgeRigidTyV06ToV08 : RigidTy → Trusted.Rustc.V2026_08_01.MirAst.RigidTy
  | .param idx name => .param idx name
  | .alias d args => .alias d (bridgeRigidTyListV06ToV08 args)
  | .bool => .bool
  | .char => .char
  | .int w => .int (bridgeIntTyV06ToV08 w)
  | .uint w => .uint (bridgeUintTyV06ToV08 w)
  | .float w => .float (bridgeFloatTyV06ToV08 w)
  | .never => .never
  | .str => .str
  | .tuple fields => .tuple (bridgeRigidTyListV06ToV08 fields)
  | .array elem len => .array (bridgeRigidTyV06ToV08 elem) len
  | .slice elem => .slice (bridgeRigidTyV06ToV08 elem)
  | .ref m p => .ref (bridgeMutabilityV06ToV08 m) (bridgeRigidTyV06ToV08 p)
  | .rawPtr m p => .rawPtr (bridgeMutabilityV06ToV08 m) (bridgeRigidTyV06ToV08 p)
  | .adt d args => .adt d (bridgeRigidTyListV06ToV08 args)
  | .fnDef d args => .fnDef d (bridgeRigidTyListV06ToV08 args)
  | .fnPtr ins out sf abi =>
    .fnPtr (bridgeRigidTyListV06ToV08 ins) (bridgeRigidTyV06ToV08 out) (bridgeSafetyV06ToV08 sf)
      (bridgeCallConvV06ToV08 abi)
  | .closure d upvars => .closure d (bridgeRigidTyListV06ToV08 upvars)
  | .dynamic t => .dynamic t
  | .foreign d => .foreign d
  | .other r => .other r

/-- Pointwise companion of `bridgeRigidTyV06ToV08`. -/
def bridgeRigidTyListV06ToV08 : List RigidTy → List Trusted.Rustc.V2026_08_01.MirAst.RigidTy
  | [] => []
  | t :: ts => bridgeRigidTyV06ToV08 t :: bridgeRigidTyListV06ToV08 ts
end

/-- Reverse bridge of `CallConv` from V2026_08_01 to V2026_06_01. -/
def bridgeCallConvV08ToV06 : Trusted.Rustc.V2026_08_01.Layout.CallConv → CallConv
  | .rust => .rust
  | .c => .c
  | .rustIntrinsic => .rustIntrinsic
  | .other name => .other name

/-- Reverse bridge of `UintTy` from V2026_08_01 to V2026_06_01. -/
def bridgeUintTyV08ToV06 : Trusted.Rustc.V2026_08_01.MirAst.UintTy → UintTy
  | .u8 => .u8 | .u16 => .u16 | .u32 => .u32 | .u64 => .u64 | .u128 => .u128 | .usize => .usize

/-- Reverse bridge of `IntTy` from V2026_08_01 to V2026_06_01. -/
def bridgeIntTyV08ToV06 : Trusted.Rustc.V2026_08_01.MirAst.IntTy → IntTy
  | .i8 => .i8 | .i16 => .i16 | .i32 => .i32 | .i64 => .i64 | .i128 => .i128 | .isize => .isize

/-- Reverse bridge of `FloatTy` from V2026_08_01 to V2026_06_01. -/
def bridgeFloatTyV08ToV06 : Trusted.Rustc.V2026_08_01.MirAst.FloatTy → FloatTy
  | .f16 => .f16 | .f32 => .f32 | .f64 => .f64 | .f128 => .f128

/-- Reverse bridge of `Mutability` from V2026_08_01 to V2026_06_01. -/
def bridgeMutabilityV08ToV06 : Trusted.Rustc.V2026_08_01.MirAst.Mutability → Mutability
  | .not => .not | .mut => .mut

/-- Reverse bridge of `Safety` from V2026_08_01 to V2026_06_01. -/
def bridgeSafetyV08ToV06 : Trusted.Rustc.V2026_08_01.MirAst.Safety → Safety
  | .safe => .safe | .unsafe_ => .unsafe_

mutual
/-- Reverse bridge a V2026_08_01 `RigidTy` to V2026_06_01. -/
def bridgeRigidTyV08ToV06 : Trusted.Rustc.V2026_08_01.MirAst.RigidTy → RigidTy
  | .param idx name => .param idx name
  | .alias d args => .alias d (bridgeRigidTyListV08ToV06 args)
  | .bool => .bool
  | .char => .char
  | .int w => .int (bridgeIntTyV08ToV06 w)
  | .uint w => .uint (bridgeUintTyV08ToV06 w)
  | .float w => .float (bridgeFloatTyV08ToV06 w)
  | .never => .never
  | .str => .str
  | .tuple fields => .tuple (bridgeRigidTyListV08ToV06 fields)
  | .array elem len => .array (bridgeRigidTyV08ToV06 elem) len
  | .slice elem => .slice (bridgeRigidTyV08ToV06 elem)
  | .ref m p => .ref (bridgeMutabilityV08ToV06 m) (bridgeRigidTyV08ToV06 p)
  | .rawPtr m p => .rawPtr (bridgeMutabilityV08ToV06 m) (bridgeRigidTyV08ToV06 p)
  | .adt d args => .adt d (bridgeRigidTyListV08ToV06 args)
  | .fnDef d args => .fnDef d (bridgeRigidTyListV08ToV06 args)
  | .fnPtr ins out sf abi =>
    .fnPtr (bridgeRigidTyListV08ToV06 ins) (bridgeRigidTyV08ToV06 out) (bridgeSafetyV08ToV06 sf)
      (bridgeCallConvV08ToV06 abi)
  | .closure d upvars => .closure d (bridgeRigidTyListV08ToV06 upvars)
  | .dynamic t => .dynamic t
  | .foreign d => .foreign d
  | .other r => .other r

/-- Pointwise companion of `bridgeRigidTyV08ToV06`. -/
def bridgeRigidTyListV08ToV06 : List Trusted.Rustc.V2026_08_01.MirAst.RigidTy → List RigidTy
  | [] => []
  | t :: ts => bridgeRigidTyV08ToV06 t :: bridgeRigidTyListV08ToV06 ts
end

theorem bridgeScalarLayout_roundtrip_v08
    (x : Trusted.Rustc.V2026_08_01.Layout.ScalarLayout) :
    bridgeScalarLayoutV06ToV08 (bridgeScalarLayoutV08ToV06 x) = x := by
  cases x with
  | initialized v r => cases v <;> rfl
  | union v => cases v <;> rfl

theorem bridgeFieldsShape_roundtrip_v08
    (x : Trusted.Rustc.V2026_08_01.Layout.FieldsShape) :
    bridgeFieldsShapeV06ToV08 (bridgeFieldsShapeV08ToV06 x) = x := by
  cases x with
  | arbitrary offsets memoryIndex =>
    simp only [bridgeFieldsShapeV08ToV06, bridgeFieldsShapeV06ToV08, List.map_map]
    congr
    conv => rhs; rw [← List.map_id offsets]
    rfl
  | _ => rfl

/-- **Lossless reverse bridge**: V2026_08_01 → V2026_06_01 → V2026_08_01 is the
identity on `TypeLayout`. -/
theorem bridgeTypeLayout_roundtrip_v08 (l : Trusted.Rustc.V2026_08_01.Layout.TypeLayout) :
    bridgeTypeLayoutV06ToV08 (bridgeTypeLayoutV08ToV06 l) = l := by
  obtain ⟨size, align, backendRepr, fields, variants, isUninhabited, fieldLayouts⟩ := l
  simp only [bridgeTypeLayoutV08ToV06, bridgeTypeLayoutV06ToV08]
  congr 1
  · cases backendRepr <;> simp [bridgeBackendReprV08ToV06, bridgeBackendReprV06ToV08,
      bridgeScalarLayout_roundtrip_v08]
  · exact bridgeFieldsShape_roundtrip_v08 fields
  · cases variants with
    | multiple tag tagField vs =>
      simp only [bridgeVariantsShapeV08ToV06, bridgeVariantsShapeV06ToV08, List.map_map,
        bridgeScalarLayout_roundtrip_v08]
      congr
      conv => rhs; rw [← List.map_id vs]
      apply List.map_congr_left
      intro x _
      exact bridgeFieldsShape_roundtrip_v08 x
    | _ => rfl

/-- **Lossless reverse table bridge** on V2026_08_01 `LayoutTable`. -/
theorem bridgeLayout_roundtrip_v08 (t : Trusted.Rustc.V2026_08_01.Layout.LayoutTable) :
    bridgeLayoutV06ToV08 (bridgeLayoutV08ToV06 t) = t := by
  obtain ⟨pointerBits, isLittleEndian, entries⟩ := t
  simp only [bridgeLayoutV08ToV06, bridgeLayoutV06ToV08, List.map_map]
  congr
  conv => rhs; rw [← List.map_id entries]
  apply List.map_congr_left
  intro x _
  exact bridgeTypeLayout_roundtrip_v08 x

mutual
/-- **Lossless `RigidTy` bridge**: V2026_06_01 → V2026_08_01 → V2026_06_01. -/
theorem bridgeRigidTy_roundtrip :
    (k : RigidTy) → bridgeRigidTyV08ToV06 (bridgeRigidTyV06ToV08 k) = k
  | .param _ _ => rfl
  | .alias d args => congrArg (RigidTy.alias d) (bridgeRigidTyList_roundtrip args)
  | .bool => rfl
  | .char => rfl
  | .int w => by cases w <;> rfl
  | .uint w => by cases w <;> rfl
  | .float w => by cases w <;> rfl
  | .never => rfl
  | .str => rfl
  | .tuple fields => congrArg RigidTy.tuple (bridgeRigidTyList_roundtrip fields)
  | .array elem len => congrArg (RigidTy.array · len) (bridgeRigidTy_roundtrip elem)
  | .slice elem => congrArg RigidTy.slice (bridgeRigidTy_roundtrip elem)
  | .ref m p => by cases m <;> exact congrArg (RigidTy.ref _) (bridgeRigidTy_roundtrip p)
  | .rawPtr m p => by cases m <;> exact congrArg (RigidTy.rawPtr _) (bridgeRigidTy_roundtrip p)
  | .adt d args => congrArg (RigidTy.adt d) (bridgeRigidTyList_roundtrip args)
  | .fnDef d args => congrArg (RigidTy.fnDef d) (bridgeRigidTyList_roundtrip args)
  | .fnPtr ins out sf abi => by
    cases sf <;> cases abi <;>
      exact congrArg2 (RigidTy.fnPtr · · _ _)
        (bridgeRigidTyList_roundtrip ins) (bridgeRigidTy_roundtrip out)
  | .closure d upvars => congrArg (RigidTy.closure d) (bridgeRigidTyList_roundtrip upvars)
  | .dynamic _ => rfl
  | .foreign _ => rfl
  | .other _ => rfl

theorem bridgeRigidTyList_roundtrip :
    (ks : List RigidTy) → bridgeRigidTyListV08ToV06 (bridgeRigidTyListV06ToV08 ks) = ks
  | [] => rfl
  | k :: ks =>
    congrArg2 List.cons (bridgeRigidTy_roundtrip k) (bridgeRigidTyList_roundtrip ks)
end

mutual
/-- **Lossless reverse `RigidTy` bridge**: V2026_08_01 → V2026_06_01 → V2026_08_01. -/
theorem bridgeRigidTy_roundtrip_v08 :
    (k : Trusted.Rustc.V2026_08_01.MirAst.RigidTy) →
      bridgeRigidTyV06ToV08 (bridgeRigidTyV08ToV06 k) = k
  | .param _ _ => rfl
  | .alias d args =>
    congrArg (Trusted.Rustc.V2026_08_01.MirAst.RigidTy.alias d)
      (bridgeRigidTyList_roundtrip_v08 args)
  | .bool => rfl
  | .char => rfl
  | .int w => by cases w <;> rfl
  | .uint w => by cases w <;> rfl
  | .float w => by cases w <;> rfl
  | .never => rfl
  | .str => rfl
  | .tuple fields =>
    congrArg Trusted.Rustc.V2026_08_01.MirAst.RigidTy.tuple
      (bridgeRigidTyList_roundtrip_v08 fields)
  | .array elem len =>
    congrArg (Trusted.Rustc.V2026_08_01.MirAst.RigidTy.array · len)
      (bridgeRigidTy_roundtrip_v08 elem)
  | .slice elem =>
    congrArg Trusted.Rustc.V2026_08_01.MirAst.RigidTy.slice
      (bridgeRigidTy_roundtrip_v08 elem)
  | .ref m p => by
    cases m <;>
      exact congrArg (Trusted.Rustc.V2026_08_01.MirAst.RigidTy.ref _)
        (bridgeRigidTy_roundtrip_v08 p)
  | .rawPtr m p => by
    cases m <;>
      exact congrArg (Trusted.Rustc.V2026_08_01.MirAst.RigidTy.rawPtr _)
        (bridgeRigidTy_roundtrip_v08 p)
  | .adt d args =>
    congrArg (Trusted.Rustc.V2026_08_01.MirAst.RigidTy.adt d)
      (bridgeRigidTyList_roundtrip_v08 args)
  | .fnDef d args =>
    congrArg (Trusted.Rustc.V2026_08_01.MirAst.RigidTy.fnDef d)
      (bridgeRigidTyList_roundtrip_v08 args)
  | .fnPtr ins out sf abi => by
    cases sf <;> cases abi <;>
      exact congrArg2 (Trusted.Rustc.V2026_08_01.MirAst.RigidTy.fnPtr · · _ _)
        (bridgeRigidTyList_roundtrip_v08 ins) (bridgeRigidTy_roundtrip_v08 out)
  | .closure d upvars =>
    congrArg (Trusted.Rustc.V2026_08_01.MirAst.RigidTy.closure d)
      (bridgeRigidTyList_roundtrip_v08 upvars)
  | .dynamic _ => rfl
  | .foreign _ => rfl
  | .other _ => rfl

theorem bridgeRigidTyList_roundtrip_v08 :
    (ks : List Trusted.Rustc.V2026_08_01.MirAst.RigidTy) →
      bridgeRigidTyListV06ToV08 (bridgeRigidTyListV08ToV06 ks) = ks
  | [] => rfl
  | k :: ks =>
    congrArg2 List.cons (bridgeRigidTy_roundtrip_v08 k) (bridgeRigidTyList_roundtrip_v08 ks)
end

/-- Bidirectional `RigidTy` bridge equivalence. -/
theorem bridgeRigidTy_iff_eq (k08 : Trusted.Rustc.V2026_08_01.MirAst.RigidTy) (k06 : RigidTy) :
    bridgeRigidTyV08ToV06 k08 = k06 ↔ k08 = bridgeRigidTyV06ToV08 k06 := by
  constructor
  · rintro rfl
    exact (bridgeRigidTy_roundtrip_v08 k08).symm
  · rintro rfl
    exact bridgeRigidTy_roundtrip k06

/-- Bridge a V2026_06_01 `TypeSubst` to V2026_08_01. -/
def bridgeTypeSubstV06ToV08 (args : TypeSubst) : Trusted.Rustc.V2026_08_01.MirAst.TypeSubst :=
  args.map fun (k, l) => (bridgeRigidTyV06ToV08 k, bridgeTypeLayoutV06ToV08 l)

theorem typeSubstLookup_bridge :
    ∀ (args : TypeSubst) (idx : Nat),
      Trusted.Rustc.V2026_08_01.MirAst.TypeSubst.lookup (bridgeTypeSubstV06ToV08 args) idx =
        (TypeSubst.lookup args idx).map fun (k, l) =>
          (bridgeRigidTyV06ToV08 k, bridgeTypeLayoutV06ToV08 l)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: rest, n + 1 => typeSubstLookup_bridge rest n

mutual
/-- `RigidTy.instantiate` commutes with the V2026_06_01 → V2026_08_01 bridge. -/
theorem rigidTyInstantiate_bridge (args : TypeSubst) :
    (k : RigidTy) →
      Trusted.Rustc.V2026_08_01.MirAst.RigidTy.instantiate (bridgeTypeSubstV06ToV08 args)
          (bridgeRigidTyV06ToV08 k) =
        bridgeRigidTyV06ToV08 (RigidTy.instantiate args k)
  | .param idx name => by
    simp only [bridgeRigidTyV06ToV08, Trusted.Rustc.V2026_08_01.MirAst.RigidTy.instantiate,
      RigidTy.instantiate, typeSubstLookup_bridge]
    cases TypeSubst.lookup args idx <;> rfl
  | .alias d a => by
    simp only [bridgeRigidTyV06ToV08, Trusted.Rustc.V2026_08_01.MirAst.RigidTy.instantiate,
      rigidTyInstantiateList_bridge args a]
  | .bool => rfl
  | .char => rfl
  | .int _ => rfl
  | .uint _ => rfl
  | .float _ => rfl
  | .never => rfl
  | .str => rfl
  | .tuple fs => by
    simp only [bridgeRigidTyV06ToV08, Trusted.Rustc.V2026_08_01.MirAst.RigidTy.instantiate,
      rigidTyInstantiateList_bridge args fs]
  | .array elem len => by
    simp only [bridgeRigidTyV06ToV08, Trusted.Rustc.V2026_08_01.MirAst.RigidTy.instantiate,
      rigidTyInstantiate_bridge args elem]
  | .slice elem => by
    simp only [bridgeRigidTyV06ToV08, Trusted.Rustc.V2026_08_01.MirAst.RigidTy.instantiate,
      rigidTyInstantiate_bridge args elem]
  | .ref m p => by
    simp only [bridgeRigidTyV06ToV08, Trusted.Rustc.V2026_08_01.MirAst.RigidTy.instantiate,
      rigidTyInstantiate_bridge args p]
  | .rawPtr m p => by
    simp only [bridgeRigidTyV06ToV08, Trusted.Rustc.V2026_08_01.MirAst.RigidTy.instantiate,
      rigidTyInstantiate_bridge args p]
  | .adt d a => by
    simp only [bridgeRigidTyV06ToV08, Trusted.Rustc.V2026_08_01.MirAst.RigidTy.instantiate,
      rigidTyInstantiateList_bridge args a]
  | .fnDef d a => by
    simp only [bridgeRigidTyV06ToV08, Trusted.Rustc.V2026_08_01.MirAst.RigidTy.instantiate,
      rigidTyInstantiateList_bridge args a]
  | .fnPtr ins out sf abi => by
    simp only [bridgeRigidTyV06ToV08, Trusted.Rustc.V2026_08_01.MirAst.RigidTy.instantiate,
      rigidTyInstantiateList_bridge args ins,
      rigidTyInstantiate_bridge args out]
  | .closure d upvars => by
    simp only [bridgeRigidTyV06ToV08, Trusted.Rustc.V2026_08_01.MirAst.RigidTy.instantiate,
      rigidTyInstantiateList_bridge args upvars]
  | .dynamic _ => rfl
  | .foreign _ => rfl
  | .other _ => rfl

theorem rigidTyInstantiateList_bridge (args : TypeSubst) :
    (ks : List RigidTy) →
      Trusted.Rustc.V2026_08_01.MirAst.RigidTy.instantiateList (bridgeTypeSubstV06ToV08 args)
          (bridgeRigidTyListV06ToV08 ks) =
        bridgeRigidTyListV06ToV08 (RigidTy.instantiateList args ks)
  | [] => rfl
  | k :: ks =>
    congrArg2 List.cons (rigidTyInstantiate_bridge args k) (rigidTyInstantiateList_bridge args ks)
end

theorem get?_map {α β : Type} (f : α → β) :
    ∀ (xs : List α) (idx : Nat), get? (xs.map f) idx = (get? xs idx).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, n + 1 => get?_map f xs n

theorem lookupFieldLayouts_bridge (entries : List TypeLayout) :
    ∀ (idxs : List Nat),
      Trusted.Rustc.V2026_08_01.Layout.lookupFieldLayouts
          (entries.map bridgeTypeLayoutV06ToV08) idxs =
        (lookupFieldLayouts entries idxs).map (List.map bridgeTypeLayoutV06ToV08)
  | [] => rfl
  | idx :: rest => by
    simp only [Trusted.Rustc.V2026_08_01.Layout.lookupFieldLayouts, lookupFieldLayouts,
      get?_map, lookupFieldLayouts_bridge entries rest]
    cases get? entries idx <;> cases lookupFieldLayouts entries rest <;> rfl

theorem computeArbitraryFieldsAux_bridge :
    ∀ (curOff curAlign idx : Nat) (fls : List TypeLayout),
      Trusted.Rustc.V2026_08_01.Layout.computeArbitraryFieldsAux curOff curAlign idx
          (fls.map bridgeTypeLayoutV06ToV08) =
        let (offs, memIdx, sz, al, uninh) := computeArbitraryFieldsAux curOff curAlign idx fls
        (offs.map bridgeSizeV06ToV08, memIdx, sz, al, uninh)
  | _, _, _, [] => rfl
  | curOff, curAlign, idx, fl :: rest => by
    simp only [List.map_cons, Trusted.Rustc.V2026_08_01.Layout.computeArbitraryFieldsAux,
      bridgeTypeLayoutV06ToV08, bridgeSizeV06ToV08, bridgeAlignV06ToV08]
    rw [computeArbitraryFieldsAux_bridge _ _ _ rest]
    rcases computeArbitraryFieldsAux
      (alignUp curOff (maxNat 1 fl.align.bytes) + fl.size.bytes)
      (maxNat curAlign (maxNat 1 fl.align.bytes)) (idx + 1) rest with
      ⟨offs, memIdx, sz, al, uninh⟩
    rfl

theorem computeUnionSizeAndAlign_bridge :
    ∀ (maxSz maxAl : Nat) (fls : List TypeLayout),
      Trusted.Rustc.V2026_08_01.Layout.computeUnionSizeAndAlign maxSz maxAl
          (fls.map bridgeTypeLayoutV06ToV08) =
        computeUnionSizeAndAlign maxSz maxAl fls
  | _, _, [] => rfl
  | _, _, _ :: rest => computeUnionSizeAndAlign_bridge _ _ rest

theorem computeAggregateBackendRepr_bridge (totalSize : Nat) :
    ∀ (fls : List TypeLayout),
      Trusted.Rustc.V2026_08_01.Layout.computeAggregateBackendRepr totalSize
          (fls.map bridgeTypeLayoutV06ToV08) =
        bridgeBackendReprV06ToV08 (computeAggregateBackendRepr totalSize fls)
  | [] => rfl
  | [fl0] => by
    simp only [List.map, Trusted.Rustc.V2026_08_01.Layout.computeAggregateBackendRepr,
      computeAggregateBackendRepr, bridgeTypeLayoutV06ToV08]
    cases Nat.beq totalSize 0 <;> rfl
  | [fl0, fl1] => by
    simp only [List.map, Trusted.Rustc.V2026_08_01.Layout.computeAggregateBackendRepr,
      computeAggregateBackendRepr, bridgeTypeLayoutV06ToV08]
    cases Nat.beq totalSize 0 <;> cases fl0.backendRepr <;> cases fl1.backendRepr <;> rfl
  | _ :: _ :: _ :: _ => rfl

theorem tagScalarByteWidth_bridge (tag : ScalarLayout) :
    Trusted.Rustc.V2026_08_01.Layout.tagScalarByteWidth (bridgeScalarLayoutV06ToV08 tag) =
      tagScalarByteWidth tag := by
  cases tag with
  | initialized v _ => cases v <;> rfl
  | union v => cases v <;> rfl

@[simp] theorem bridgeTypeLayoutV06ToV08_size_bytes (fl : TypeLayout) :
    (bridgeTypeLayoutV06ToV08 fl).size.bytes = fl.size.bytes := rfl

@[simp] theorem bridgeTypeLayoutV06ToV08_align_bytes (fl : TypeLayout) :
    (bridgeTypeLayoutV06ToV08 fl).align.bytes = fl.align.bytes := rfl

theorem recomputeVariantShapesAux_bridge (tagBytes : Nat) :
    ∀ (vs : List FieldsShape) (fls : List TypeLayout),
      Trusted.Rustc.V2026_08_01.Layout.recomputeVariantShapesAux tagBytes
          (vs.map bridgeFieldsShapeV06ToV08) (fls.map bridgeTypeLayoutV06ToV08) =
        let (shapes', maxSz, maxAl) := recomputeVariantShapesAux tagBytes vs fls
        (shapes'.map bridgeFieldsShapeV06ToV08, maxSz, maxAl)
  | [], _ => rfl
  | .primitive :: vRest, fls => by
    simp only [List.map_cons, bridgeFieldsShapeV06ToV08,
      Trusted.Rustc.V2026_08_01.Layout.recomputeVariantShapesAux]
    rw [recomputeVariantShapesAux_bridge tagBytes vRest fls]
  | .union c :: vRest, fls => by
    simp only [List.map_cons, bridgeFieldsShapeV06ToV08,
      Trusted.Rustc.V2026_08_01.Layout.recomputeVariantShapesAux]
    rw [recomputeVariantShapesAux_bridge tagBytes vRest fls]
  | .array s c :: vRest, fls => by
    simp only [List.map_cons, bridgeFieldsShapeV06ToV08,
      Trusted.Rustc.V2026_08_01.Layout.recomputeVariantShapesAux]
    rw [recomputeVariantShapesAux_bridge tagBytes vRest fls]
  | .arbitrary [] memIdx :: vRest, fls => by
    simp only [List.map_cons, List.map_nil, bridgeFieldsShapeV06ToV08,
      Trusted.Rustc.V2026_08_01.Layout.recomputeVariantShapesAux]
    rw [recomputeVariantShapesAux_bridge tagBytes vRest fls]
  | .arbitrary (_ :: _) memIdx :: vRest, [] => by
    have ih := recomputeVariantShapesAux_bridge tagBytes vRest []
    simp only [List.map_nil] at ih
    simp only [List.map_cons, List.map_nil, bridgeFieldsShapeV06ToV08,
      Trusted.Rustc.V2026_08_01.Layout.recomputeVariantShapesAux]
    rw [ih]
  | .arbitrary (_ :: _) memIdx :: vRest, [fl] => by
    have ih := recomputeVariantShapesAux_bridge tagBytes vRest [fl]
    simp only [List.map_cons, List.map_nil] at ih
    simp only [List.map_cons, List.map_nil, bridgeFieldsShapeV06ToV08,
      bridgeTypeLayoutV06ToV08_size_bytes, bridgeTypeLayoutV06ToV08_align_bytes,
      bridgeSizeV06ToV08,
      Trusted.Rustc.V2026_08_01.Layout.recomputeVariantShapesAux]
    rw [ih]
    rfl
  | .arbitrary (_ :: _) memIdx :: vRest, fl :: fl₂ :: pRest => by
    have ih := recomputeVariantShapesAux_bridge tagBytes vRest (fl₂ :: pRest)
    simp only [List.map_cons] at ih
    simp only [List.map_cons, bridgeFieldsShapeV06ToV08,
      bridgeTypeLayoutV06ToV08_size_bytes, bridgeTypeLayoutV06ToV08_align_bytes,
      bridgeSizeV06ToV08,
      Trusted.Rustc.V2026_08_01.Layout.recomputeVariantShapesAux]
    rw [ih]
    rfl

theorem recomputeFromFieldLayouts_bridge (extEntries : List TypeLayout) (l : TypeLayout) :
    Trusted.Rustc.V2026_08_01.Layout.TypeLayout.recomputeFromFieldLayouts
        (extEntries.map bridgeTypeLayoutV06ToV08) (bridgeTypeLayoutV06ToV08 l) =
      bridgeTypeLayoutV06ToV08 (TypeLayout.recomputeFromFieldLayouts extEntries l) := by
  obtain ⟨size, align, backendRepr, fields, variants, isUninhabited, fieldLayouts⟩ := l
  cases fieldLayouts with
  | nil => rfl
  | cons fIdx fRest =>
    dsimp only [bridgeTypeLayoutV06ToV08,
      Trusted.Rustc.V2026_08_01.Layout.TypeLayout.recomputeFromFieldLayouts,
      TypeLayout.recomputeFromFieldLayouts]
    rw [lookupFieldLayouts_bridge]
    cases lookupFieldLayouts extEntries (fIdx :: fRest) with
    | none => rfl
    | some fls =>
      dsimp only [Option.map]
      cases variants with
      | empty => rfl
      | single vIdx =>
        dsimp only [bridgeVariantsShapeV06ToV08]
        cases fields with
        | primitive =>
          cases fls with
          | nil => rfl
          | cons fl0 flRest => cases flRest <;> rfl
        | union count =>
          dsimp only [bridgeFieldsShapeV06ToV08]
          rw [computeUnionSizeAndAlign_bridge]
          rcases computeUnionSizeAndAlign 0 1 fls with ⟨totalSz, maxAl⟩
          rfl
        | array stride count =>
          cases fls <;> rfl
        | arbitrary offsets memIdx =>
          dsimp only [bridgeFieldsShapeV06ToV08]
          rw [computeArbitraryFieldsAux_bridge]
          rcases computeArbitraryFieldsAux 0 1 0 fls with ⟨offsets', memIdx', totalSz, maxAl, uninh⟩
          simp [bridgeSizeV06ToV08, bridgeAlignV06ToV08,
            computeAggregateBackendRepr_bridge]
      | multiple tag tagField vs =>
        dsimp only [bridgeVariantsShapeV06ToV08]
        rw [tagScalarByteWidth_bridge, recomputeVariantShapesAux_bridge]
        rcases recomputeVariantShapesAux (tagScalarByteWidth tag) vs fls with
          ⟨shapes', maxSz, maxAl⟩
        cases fields with
        | arbitrary offsets memIdx =>
          cases offsets <;> rfl
        | primitive => rfl
        | union _ => rfl
        | array _ _ => rfl

theorem bridgeUintTy_byteWidth (ptrBits : Nat) (w : UintTy) :
    Trusted.Rustc.V2026_08_01.MirAst.UintTy.byteWidth ptrBits (bridgeUintTyV06ToV08 w) =
      UintTy.byteWidth ptrBits w := by
  cases w <;> rfl

theorem bridgeIntTy_byteWidth (ptrBits : Nat) (w : IntTy) :
    Trusted.Rustc.V2026_08_01.MirAst.IntTy.byteWidth ptrBits (bridgeIntTyV06ToV08 w) =
      IntTy.byteWidth ptrBits w := by
  cases w <;> rfl

theorem bridgeFloatTy_byteWidth (w : FloatTy) :
    Trusted.Rustc.V2026_08_01.MirAst.FloatTy.byteWidth (bridgeFloatTyV06ToV08 w) =
      FloatTy.byteWidth w := by
  cases w <;> rfl

@[simp] theorem pow2Nat_bridge :
    ∀ n : Nat, Trusted.Rustc.V2026_08_01.MirAst.pow2Nat n = pow2Nat n
  | 0 => rfl
  | k + 1 => by simp [Trusted.Rustc.V2026_08_01.MirAst.pow2Nat, pow2Nat, pow2Nat_bridge k]

mutual
/-- **Universal cross-dialect `computeLayout` commutation**: V2026_08_01
`RigidTy.computeLayout` on bridged inputs equals bridging V2026_06_01
`RigidTy.computeLayout` across all 21 `RigidTy` constructors (primitives,
pointers, fat pointers, arrays, tuples, closures, and ADTs with `fieldLayouts`,
unions, and multi-variant enums). -/
theorem computeLayout_bridge_commutes (ptrBits : Nat) (extEntries : List TypeLayout)
    (args : TypeSubst) :
    ∀ (origLayout : Option TypeLayout) (k : RigidTy),
      Trusted.Rustc.V2026_08_01.MirAst.RigidTy.computeLayout ptrBits
          (extEntries.map bridgeTypeLayoutV06ToV08) (bridgeTypeSubstV06ToV08 args)
          (origLayout.map bridgeTypeLayoutV06ToV08) (bridgeRigidTyV06ToV08 k) =
        (RigidTy.computeLayout ptrBits extEntries args origLayout k).map
          bridgeTypeLayoutV06ToV08
  | origLayout, .param idx name => by
    simp only [bridgeRigidTyV06ToV08, Trusted.Rustc.V2026_08_01.MirAst.RigidTy.computeLayout,
      RigidTy.computeLayout, typeSubstLookup_bridge]
    cases TypeSubst.lookup args idx <;> rfl
  | _, .bool => rfl
  | _, .char => rfl
  | _, .uint w => by
    simp only [bridgeRigidTyV06ToV08, Trusted.Rustc.V2026_08_01.MirAst.RigidTy.computeLayout,
      RigidTy.computeLayout, bridgeUintTy_byteWidth, pow2Nat_bridge]
    rfl
  | _, .int w => by
    simp only [bridgeRigidTyV06ToV08, Trusted.Rustc.V2026_08_01.MirAst.RigidTy.computeLayout,
      RigidTy.computeLayout, bridgeIntTy_byteWidth, pow2Nat_bridge]
    rfl
  | _, .float w => by
    simp only [bridgeRigidTyV06ToV08, Trusted.Rustc.V2026_08_01.MirAst.RigidTy.computeLayout,
      RigidTy.computeLayout, bridgeFloatTy_byteWidth, pow2Nat_bridge]
    rfl
  | _, .never => rfl
  | _, .fnDef _ _ => rfl
  | _, .fnPtr _ _ _ _ => by
    simp only [bridgeRigidTyV06ToV08, Trusted.Rustc.V2026_08_01.MirAst.RigidTy.computeLayout,
      RigidTy.computeLayout, pow2Nat_bridge]
    rfl
  | _, .ref m pointee => by
    simp only [bridgeRigidTyV06ToV08, Trusted.Rustc.V2026_08_01.MirAst.RigidTy.computeLayout,
      RigidTy.computeLayout, rigidTyInstantiate_bridge, pow2Nat_bridge]
    cases RigidTy.instantiate args pointee <;> rfl
  | _, .rawPtr m pointee => by
    simp only [bridgeRigidTyV06ToV08, Trusted.Rustc.V2026_08_01.MirAst.RigidTy.computeLayout,
      RigidTy.computeLayout, rigidTyInstantiate_bridge, pow2Nat_bridge]
    cases RigidTy.instantiate args pointee <;> rfl
  | origLayout, .array elem len => by
    have ih := computeLayout_bridge_commutes ptrBits extEntries args none elem
    simp only [Option.map_none] at ih
    simp only [bridgeRigidTyV06ToV08, Trusted.Rustc.V2026_08_01.MirAst.RigidTy.computeLayout,
      RigidTy.computeLayout, ih]
    cases RigidTy.computeLayout ptrBits extEntries args none elem <;> rfl
  | origLayout, .tuple fields => by
    have ih := computeLayoutList_bridge_commutes ptrBits extEntries args fields
    simp only [bridgeRigidTyV06ToV08, Trusted.Rustc.V2026_08_01.MirAst.RigidTy.computeLayout,
      RigidTy.computeLayout, ih]
    cases RigidTy.computeLayoutList ptrBits extEntries args fields with
    | none => rfl
    | some fls =>
      dsimp only [Option.map]
      rw [computeArbitraryFieldsAux_bridge]
      rcases computeArbitraryFieldsAux 0 1 0 fls with ⟨offsets, memIdx, totalSz, maxAl, uninh⟩
      simp [bridgeTypeLayoutV06ToV08, bridgeSizeV06ToV08, bridgeAlignV06ToV08,
        bridgeFieldsShapeV06ToV08, bridgeVariantsShapeV06ToV08,
        computeAggregateBackendRepr_bridge]
  | origLayout, .adt d adtArgs => by
    have ih := computeLayoutList_bridge_commutes ptrBits extEntries args adtArgs
    simp only [bridgeRigidTyV06ToV08, Trusted.Rustc.V2026_08_01.MirAst.RigidTy.computeLayout,
      RigidTy.computeLayout, ih]
    cases origLayout with
    | none =>
      cases RigidTy.computeLayoutList ptrBits extEntries args adtArgs with
      | none => rfl
      | some fls =>
        dsimp only [Option.map]
        rw [computeArbitraryFieldsAux_bridge]
        rcases computeArbitraryFieldsAux 0 1 0 fls with ⟨offsets, memIdx, totalSz, maxAl, uninh⟩
        simp [bridgeTypeLayoutV06ToV08, bridgeSizeV06ToV08, bridgeAlignV06ToV08,
          bridgeFieldsShapeV06ToV08, bridgeVariantsShapeV06ToV08,
          computeAggregateBackendRepr_bridge]
    | some origL =>
      obtain ⟨size, align, backendRepr, fields, variants, isUninhabited, fieldLayouts⟩ := origL
      cases fieldLayouts with
      | cons fIdx fRest =>
        dsimp only [Option.map]
        exact congrArg Option.some (recomputeFromFieldLayouts_bridge extEntries _)
      | nil =>
        dsimp only [Option.map, bridgeTypeLayoutV06ToV08]
        cases RigidTy.computeLayoutList ptrBits extEntries args adtArgs with
        | none => rfl
        | some fls =>
          dsimp only []
          cases variants with
          | empty => rfl
          | single vIdx =>
            dsimp only [bridgeVariantsShapeV06ToV08]
            cases fields with
            | union count =>
              dsimp only [bridgeFieldsShapeV06ToV08]
              rw [computeUnionSizeAndAlign_bridge]
              rcases computeUnionSizeAndAlign 0 1 fls with ⟨totalSz, maxAl⟩
              rfl
            | primitive =>
              dsimp only [bridgeFieldsShapeV06ToV08]
              rw [computeArbitraryFieldsAux_bridge]
              rcases computeArbitraryFieldsAux 0 1 0 fls with
                ⟨offsets, memIdx, totalSz, maxAl, uninh⟩
              simp [bridgeSizeV06ToV08, bridgeAlignV06ToV08,
                computeAggregateBackendRepr_bridge]
            | array s c =>
              dsimp only [bridgeFieldsShapeV06ToV08]
              rw [computeArbitraryFieldsAux_bridge]
              rcases computeArbitraryFieldsAux 0 1 0 fls with
                ⟨offsets, memIdx, totalSz, maxAl, uninh⟩
              simp [bridgeSizeV06ToV08, bridgeAlignV06ToV08,
                computeAggregateBackendRepr_bridge]
            | arbitrary offs mIdx =>
              dsimp only [bridgeFieldsShapeV06ToV08]
              rw [computeArbitraryFieldsAux_bridge]
              rcases computeArbitraryFieldsAux 0 1 0 fls with
                ⟨offsets, memIdx, totalSz, maxAl, uninh⟩
              simp [bridgeSizeV06ToV08, bridgeAlignV06ToV08,
                computeAggregateBackendRepr_bridge]
          | multiple tag tagField vs =>
            dsimp only [bridgeVariantsShapeV06ToV08]
            rw [tagScalarByteWidth_bridge, recomputeVariantShapesAux_bridge]
            rcases recomputeVariantShapesAux (tagScalarByteWidth tag) vs fls with
              ⟨shapes', maxSz, maxAl⟩
            cases fields with
            | arbitrary offs mIdx =>
              cases offs <;> rfl
            | primitive => rfl
            | union _ => rfl
            | array _ _ => rfl
  | origLayout, .closure d upvars => by
    have ih := computeLayoutList_bridge_commutes ptrBits extEntries args upvars
    simp only [bridgeRigidTyV06ToV08, Trusted.Rustc.V2026_08_01.MirAst.RigidTy.computeLayout,
      RigidTy.computeLayout, ih]
    cases RigidTy.computeLayoutList ptrBits extEntries args upvars with
    | none => rfl
    | some fls =>
      dsimp only [Option.map]
      rw [computeArbitraryFieldsAux_bridge]
      rcases computeArbitraryFieldsAux 0 1 0 fls with ⟨offsets, memIdx, totalSz, maxAl, uninh⟩
      simp [bridgeTypeLayoutV06ToV08, bridgeSizeV06ToV08, bridgeAlignV06ToV08,
        bridgeFieldsShapeV06ToV08, bridgeVariantsShapeV06ToV08,
        computeAggregateBackendRepr_bridge]
  | _, .slice _ => rfl
  | _, .str => rfl
  | _, .dynamic _ => rfl
  | _, .alias _ _ => rfl
  | _, .foreign _ => rfl
  | _, .other _ => rfl

theorem computeLayoutList_bridge_commutes (ptrBits : Nat) (extEntries : List TypeLayout)
    (args : TypeSubst) :
    ∀ (ks : List RigidTy),
      Trusted.Rustc.V2026_08_01.MirAst.RigidTy.computeLayoutList ptrBits
          (extEntries.map bridgeTypeLayoutV06ToV08) (bridgeTypeSubstV06ToV08 args)
          (bridgeRigidTyListV06ToV08 ks) =
        (RigidTy.computeLayoutList ptrBits extEntries args ks).map
          (List.map bridgeTypeLayoutV06ToV08)
  | [] => rfl
  | k :: ks => by
    have ih₁ := computeLayout_bridge_commutes ptrBits extEntries args none k
    have ih₂ := computeLayoutList_bridge_commutes ptrBits extEntries args ks
    simp only [Option.map_none] at ih₁
    simp only [bridgeRigidTyListV06ToV08,
      Trusted.Rustc.V2026_08_01.MirAst.RigidTy.computeLayoutList,
      RigidTy.computeLayoutList, ih₁, ih₂]
    cases RigidTy.computeLayout ptrBits extEntries args none k <;>
      cases RigidTy.computeLayoutList ptrBits extEntries args ks <;> rfl
end

/-! ### The finite-material environment and its evaluator -/

/-- `o₂` extends `o₁`: present evidence is preserved, absent evidence may appear. -/
def OptionExtends {α : Type} (o₁ o₂ : Option α) : Prop := ∀ x, o₁ = some x → o₂ = some x

theorem OptionExtends.refl {α : Type} (o : Option α) : OptionExtends o o := fun _ h => h

theorem OptionExtends.trans {α : Type} {o₁ o₂ o₃ : Option α} (h₁ : OptionExtends o₁ o₂)
    (h₂ : OptionExtends o₂ o₃) : OptionExtends o₁ o₃ := fun x h => h₂ x (h₁ x h)

/-- Finite-material, schema-versioned demand-time compiler query environment. -/
structure CompilerQueryEnv : Type where
  /-- Producer schema version. -/
  schema : CompilerSchemaVersion
  /-- V2026_06_01 layout material. -/
  layoutsV06 : LayoutTable
  /-- V2026_08_01 layout material (gated by `schema.hasV08Layouts`). -/
  layoutsV08 : Option Trusted.Rustc.V2026_08_01.Layout.LayoutTable
  /-- Declared `FnAbi` table. -/
  fnAbis : List (DefPath × FnAbi)
  /-- Optional Schema-13 CFI ABI evidence. -/
  cfiTags : Option CfiTagSpec
  /-- Optional Schema-13 synchronization-object storage regions. -/
  syncRegions : Option (List SyncStorageRegion)
  /-- Optional Schema-13 vtable dispatch entries (`UnOp.vtableMethodLookup`). -/
  vtables : Option (List VTableMethodEntry)
  deriving DecidableEq

/-- V2026_08_01 layouts, if the schema admits them. -/
def CompilerQueryEnv.v08Layouts? (env : CompilerQueryEnv) :
    Option Trusted.Rustc.V2026_08_01.Layout.LayoutTable :=
  if env.schema.hasV08Layouts then env.layoutsV08 else none

/-- Schema-13 CFI evidence, if present. -/
def CompilerQueryEnv.cfiEvidence? (env : CompilerQueryEnv) : Option CfiTagSpec :=
  if env.schema.hasSchema13 then env.cfiTags else none

/-- Schema-13 sync-storage evidence, if present. -/
def CompilerQueryEnv.syncEvidence? (env : CompilerQueryEnv) : Option (List SyncStorageRegion) :=
  if env.schema.hasSchema13 then env.syncRegions else none

/-- Schema-13 vtable evidence, if present. -/
def CompilerQueryEnv.vtableEvidence? (env : CompilerQueryEnv) : Option (List VTableMethodEntry) :=
  if env.schema.hasSchema13 then env.vtables else none

/-- First entry for a `DefPath` key (uses `instBEqOfDecidableEq`-free `DecidableEq`). -/
def lookupDefPathAssoc {β : Type} : List (DefPath × β) → DefPath → Option β
  | [], _ => none
  | (k, v) :: rest, p => if k = p then some v else lookupDefPathAssoc rest p

/-- First entry for a `RigidTy` key. -/
def lookupTyAssoc {β : Type} : List (RigidTy × β) → RigidTy → Option β
  | [], _ => none
  | (k, v) :: rest, ty => if k = ty then some v else lookupTyAssoc rest ty

/-- `layout_of` in the V2026_06_01 dialect: `RigidTy.computeLayout` seeded with the
captured `LayoutTable` entry of `ty.layoutIdx`. -/
def computeLayoutV06 (tbl : LayoutTable) (ty : Ty) : Option TypeLayout :=
  RigidTy.computeLayout tbl.pointerBits tbl.entries [] (tbl.lookup ty.layoutIdx) ty.kind

/-- `layout_of` in the V2026_08_01 dialect (V2026_08_01 `RigidTy.computeLayout` on
the bridged type), bridged back to a V2026_06_01 `TypeLayout`. -/
def computeLayoutV08Bridged (tbl : Trusted.Rustc.V2026_08_01.Layout.LayoutTable) (ty : Ty) :
    Option TypeLayout :=
  (Trusted.Rustc.V2026_08_01.MirAst.RigidTy.computeLayout tbl.pointerBits tbl.entries []
      (tbl.lookup ty.layoutIdx) (bridgeRigidTyV06ToV08 ty.kind)).map bridgeTypeLayoutV08ToV06

/-- **Universal cross-dialect layout agreement (`V06 → V08`)**: for every
`tbl : LayoutTable` and every `ty : Ty`, `computeLayoutV08Bridged` on the bridged
table equals `computeLayoutV06`. -/
theorem computeLayoutV08Bridged_bridgeLayoutV06ToV08 (tbl : LayoutTable) (ty : Ty) :
    computeLayoutV08Bridged (bridgeLayoutV06ToV08 tbl) ty = computeLayoutV06 tbl ty := by
  unfold computeLayoutV08Bridged computeLayoutV06 bridgeLayoutV06ToV08
  have hLook :
      Trusted.Rustc.V2026_08_01.Layout.LayoutTable.lookup
        { pointerBits := tbl.pointerBits, isLittleEndian := tbl.isLittleEndian,
          entries := tbl.entries.map bridgeTypeLayoutV06ToV08 } ty.layoutIdx =
        (tbl.lookup ty.layoutIdx).map bridgeTypeLayoutV06ToV08 :=
    get?_map bridgeTypeLayoutV06ToV08 tbl.entries ty.layoutIdx
  have hComm := computeLayout_bridge_commutes tbl.pointerBits tbl.entries []
    (tbl.lookup ty.layoutIdx) ty.kind
  simp only [bridgeTypeSubstV06ToV08, List.map_nil] at hComm
  rw [hLook, hComm, Option.map_map]
  cases RigidTy.computeLayout tbl.pointerBits tbl.entries [] (tbl.lookup ty.layoutIdx) ty.kind with
  | none => rfl
  | some l => simp [Function.comp, bridgeTypeLayout_roundtrip]

/-- **Universal cross-dialect layout agreement (`V08 → V06`)**: for every
V2026_08_01 `tbl : LayoutTable` and every `ty : Ty`, `computeLayoutV08Bridged tbl ty`
equals `computeLayoutV06 (bridgeLayoutV08ToV06 tbl) ty`. -/
theorem computeLayoutV08Bridged_eq_computeLayoutV06_bridge
    (tbl : Trusted.Rustc.V2026_08_01.Layout.LayoutTable) (ty : Ty) :
    computeLayoutV08Bridged tbl ty = computeLayoutV06 (bridgeLayoutV08ToV06 tbl) ty := by
  rw [← computeLayoutV08Bridged_bridgeLayoutV06ToV08 (bridgeLayoutV08ToV06 tbl) ty,
    bridgeLayout_roundtrip_v08]

/-- Demand-time `layoutOf`. -/
def evalLayoutOf (env : CompilerQueryEnv) (dialect : LayoutDialect) (ty : Ty) :
    QueryResult QueryAnswer :=
  match dialect with
  | .v2026_06_01 =>
    match computeLayoutV06 env.layoutsV06 ty with
    | some l => .ok (.layout l)
    | none => .err .layoutUncomputable
  | .v2026_08_01 =>
    match env.v08Layouts? with
    | none => .unsupported .missingV08LayoutDialect
    | some tbl =>
      match computeLayoutV08Bridged tbl ty with
      | some l => .ok (.layout l)
      | none => .err .layoutUncomputable

/-- Exact bidirectional characterization of `evalLayoutOf` in the V2026_06_01 dialect: the
answer is `l` iff `computeLayoutV06` computes `l`. -/
theorem evalLayoutOf_v06_ok_iff (env : CompilerQueryEnv) (ty : Ty) (l : TypeLayout) :
    evalLayoutOf env .v2026_06_01 ty = .ok (.layout l) ↔
      computeLayoutV06 env.layoutsV06 ty = some l := by
  simp only [evalLayoutOf]
  cases computeLayoutV06 env.layoutsV06 ty with
  | none => simp
  | some l' => simp

/-- Exact bidirectional characterization of `evalLayoutOf` in the V2026_08_01 dialect: the
answer is `l` iff the environment carries a V2026_08_01 table whose bridged layout of `ty` is
`l` (a missing table is `.unsupported`, never `.ok`). -/
theorem evalLayoutOf_v08_ok_iff (env : CompilerQueryEnv) (ty : Ty) (l : TypeLayout) :
    evalLayoutOf env .v2026_08_01 ty = .ok (.layout l) ↔
      ∃ tbl, env.v08Layouts? = some tbl ∧ computeLayoutV08Bridged tbl ty = some l := by
  simp only [evalLayoutOf]
  cases env.v08Layouts? with
  | none => simp
  | some tbl =>
    simp only [Option.some.injEq, exists_eq_left']
    cases computeLayoutV08Bridged tbl ty with
    | none => simp
    | some l' => simp

/-- **Universal cross-dialect `evalLayoutOf` agreement**: whenever `env.v08Layouts?`
holds a V2026_08_01 table whose bridge equals `env.layoutsV06`, `evalLayoutOf`
in the `.v2026_08_01` dialect equals `evalLayoutOf` in the `.v2026_06_01` dialect
for *every* `ty : Ty`. -/
theorem evalLayoutOf_v08_eq_v06 (env : CompilerQueryEnv)
    (tblV08 : Trusted.Rustc.V2026_08_01.Layout.LayoutTable)
    (hv08 : env.v08Layouts? = some tblV08)
    (hbridge : bridgeLayoutV08ToV06 tblV08 = env.layoutsV06) (ty : Ty) :
    evalLayoutOf env .v2026_08_01 ty = evalLayoutOf env .v2026_06_01 ty := by
  simp only [evalLayoutOf, hv08, computeLayoutV08Bridged_eq_computeLayoutV06_bridge, hbridge]

/-- Bidirectional layout-table bridge equivalence: `bridgeLayoutV08ToV06 tblV08 = tblV06`
holds if and only if `tblV08 = bridgeLayoutV06ToV08 tblV06`. -/
theorem bridgeLayout_iff_eq (tblV08 : Trusted.Rustc.V2026_08_01.Layout.LayoutTable)
    (tblV06 : LayoutTable) :
    bridgeLayoutV08ToV06 tblV08 = tblV06 ↔ tblV08 = bridgeLayoutV06ToV08 tblV06 := by
  constructor
  · rintro rfl
    exact (bridgeLayout_roundtrip_v08 tblV08).symm
  · rintro rfl
    exact bridgeLayout_roundtrip tblV06

/-- **Cross-dialect layout-table coherence invariant**: whenever V2026_08_01 layout
material is active under the environment's schema (`env.v08Layouts? = some tblV08`),
its bridge to V2026_06_01 equals `env.layoutsV06` (equivalently, by
`bridgeLayout_iff_eq`, `tblV08 = bridgeLayoutV06ToV08 env.layoutsV06`). -/
def CompilerQueryEnv.isLayoutCoherent (env : CompilerQueryEnv) : Bool :=
  match env.v08Layouts? with
  | none => true
  | some tblV08 => decide (bridgeLayoutV08ToV06 tblV08 = env.layoutsV06)

/-- Any `.v2026_06_01` environment is vacuously layout-coherent (`v08Layouts? = none`). -/
theorem isLayoutCoherent_of_schema_v06 (env : CompilerQueryEnv)
    (hs : env.schema = .v2026_06_01) : env.isLayoutCoherent = true := by
  simp [CompilerQueryEnv.isLayoutCoherent, CompilerQueryEnv.v08Layouts?, hs,
    CompilerSchemaVersion.hasV08Layouts]

/-- Canonical smart upgrader that populates `layoutsV08` by bridging `env.layoutsV06`. -/
def CompilerQueryEnv.withBridgedV08Layouts (env : CompilerQueryEnv)
    (newSchema : CompilerSchemaVersion := env.schema) : CompilerQueryEnv :=
  { env with
    schema := newSchema
    layoutsV08 := some (bridgeLayoutV06ToV08 env.layoutsV06) }

/-- `withBridgedV08Layouts` always satisfies `isLayoutCoherent`. -/
theorem withBridgedV08Layouts_isLayoutCoherent (env : CompilerQueryEnv)
    (newSchema : CompilerSchemaVersion) :
    (env.withBridgedV08Layouts newSchema).isLayoutCoherent = true := by
  unfold CompilerQueryEnv.isLayoutCoherent CompilerQueryEnv.v08Layouts?
    CompilerQueryEnv.withBridgedV08Layouts
  cases newSchema.hasV08Layouts <;> simp [bridgeLayout_roundtrip]

/-- First per-argument ABI mismatch (pass mode, then layout). -/
def argAbiMismatch? : Nat → List ArgAbi → List ArgAbi → Option QueryErr
  | _, [], [] => none
  | i, a :: as, b :: bs =>
    if a.mode = b.mode then
      if a.layout = b.layout then argAbiMismatch? (i + 1) as bs else some (.argLayoutMismatch i)
    else some (.argModeMismatch i)
  | _, _, _ => some .argCountMismatch

/-- Exact characterization of `argAbiMismatch? i as bs = none`. -/
theorem argAbiMismatch?_eq_none_iff :
    ∀ (i : Nat) (as bs : List ArgAbi), argAbiMismatch? i as bs = none ↔ as = bs
  | _, [], [] => by simp [argAbiMismatch?]
  | _, [], _ :: _ => by simp [argAbiMismatch?]
  | _, _ :: _, [] => by simp [argAbiMismatch?]
  | i, ⟨la, ma⟩ :: as, ⟨lb, mb⟩ :: bs => by
    simp only [argAbiMismatch?, List.cons.injEq, ArgAbi.mk.injEq]
    by_cases hm : ma = mb
    · subst hm
      simp only [ite_true]
      by_cases hl : la = lb
      · subst hl
        simp [argAbiMismatch?_eq_none_iff (i + 1) as bs]
      · simp [hl]
    · simp [hm]

/-- First `FnAbi` mismatch: calling convention, arguments, return, unwinding. -/
def fnAbiMismatch? (caller callee : FnAbi) : Option QueryErr :=
  if caller.conv = callee.conv then
    match argAbiMismatch? 0 caller.args callee.args with
    | some e => some e
    | none =>
      if caller.ret = callee.ret then
        if callee.canUnwind = true ∧ caller.canUnwind = false then some .unwindMismatch else none
      else some .retAbiMismatch
  else some .callConvMismatch

/-- Exact characterization of `fnAbiMismatch? caller callee = none`. -/
theorem fnAbiMismatch?_eq_none_iff (caller callee : FnAbi) :
    fnAbiMismatch? caller callee = none ↔
      caller.conv = callee.conv ∧ caller.args = callee.args ∧ caller.ret = callee.ret ∧
        (callee.canUnwind = true → caller.canUnwind = true) := by
  unfold fnAbiMismatch?
  by_cases hc : caller.conv = callee.conv
  · simp only [hc, ite_true, true_and]
    cases ha : argAbiMismatch? 0 caller.args callee.args with
    | some e =>
      have hne : caller.args ≠ callee.args :=
        fun h => by rw [(argAbiMismatch?_eq_none_iff 0 _ _).mpr h] at ha; nomatch ha
      simp [hne]
    | none =>
      have heq : caller.args = callee.args := (argAbiMismatch?_eq_none_iff 0 _ _).mp ha
      simp only [heq, true_and]
      by_cases hr : caller.ret = callee.ret
      · simp only [hr, ite_true, true_and]
        cases callee.canUnwind <;> cases caller.canUnwind <;> simp
      · simp [hr]
  · simp [hc]

/-- CFI-independent ABI check against the declared `FnAbi` table. -/
def abiCore (env : CompilerQueryEnv) (callerAbi : FnAbi) (callee : DefPath) :
    QueryResult QueryAnswer :=
  match lookupDefPathAssoc env.fnAbis callee with
  | none => .err (.unknownCalleeAbi callee)
  | some calleeAbi =>
    match fnAbiMismatch? callerAbi calleeAbi with
    | some e => .err e
    | none => .ok .abiOk

/-- Exact characterization of `abiCore env callerAbi callee = .ok .abiOk`. -/
theorem abiCore_ok_iff (env : CompilerQueryEnv) (callerAbi : FnAbi) (callee : DefPath) :
    abiCore env callerAbi callee = .ok .abiOk ↔
      ∃ calleeAbi, lookupDefPathAssoc env.fnAbis callee = some calleeAbi ∧
        callerAbi.conv = calleeAbi.conv ∧ callerAbi.args = calleeAbi.args ∧
        callerAbi.ret = calleeAbi.ret ∧
        (calleeAbi.canUnwind = true → callerAbi.canUnwind = true) := by
  unfold abiCore
  cases h : lookupDefPathAssoc env.fnAbis callee with
  | none => simp
  | some calleeAbi =>
    simp only [Option.some.injEq, exists_eq_left']
    cases hm : fnAbiMismatch? callerAbi calleeAbi with
    | some e =>
      simp [← fnAbiMismatch?_eq_none_iff, hm]
    | none =>
      simp [← fnAbiMismatch?_eq_none_iff, hm]

/-- Demand-time `abiCompatible`. A CFI-instrumented call (`cfiCallSite = some _`)
first requires Schema-13 CFI evidence (failing closed with
`.unsupported .missingCfiEvidence`), because the CFI trap precedes the call;
then CFI type ids; then the ABI proper. -/
def evalAbiCompatible (env : CompilerQueryEnv) (callerAbi : FnAbi) (callee : DefPath)
    (cfiCallSite : Option RigidTy) : QueryResult QueryAnswer :=
  match cfiCallSite with
  | none => abiCore env callerAbi callee
  | some siteTy =>
    match env.cfiEvidence? with
    | none => .unsupported .missingCfiEvidence
    | some spec =>
      match lookupDefPathAssoc spec.calleeTypeIds callee, lookupTyAssoc spec.callSiteTypeIds siteTy with
      | none, _ => .err (.cfiCalleeUntagged callee)
      | some _, none => .err .cfiCallSiteUntagged
      | some calleeId, some siteId =>
        if calleeId = siteId then abiCore env callerAbi callee else .err .cfiTypeIdMismatch

/-- A byte access `[offset, offset + len)` of `allocId` begins inside, or crosses
into, a non-empty sync region `r` (`0 < r.size`). Zero-byte regions (`r.size = 0`)
denote empty intervals `[r.offset, r.offset)` and never block any access. -/
def SyncStorageRegion.blocks (r : SyncStorageRegion) (allocId offset len : Nat) : Bool :=
  decide (r.allocId = allocId) && decide (0 < r.size) &&
    ((decide (r.offset ≤ offset) && decide (offset < r.offset + r.size)) ||
      (decide (offset < r.offset) && decide (r.offset < offset + len)))

/-- A zero-byte `SyncStorageRegion` (`r.size = 0`) never blocks any byte access. -/
theorem syncStorageRegion_blocks_zero_size (r : SyncStorageRegion) (allocId offset len : Nat)
    (hz : r.size = 0) : r.blocks allocId offset len = false := by
  simp [SyncStorageRegion.blocks, hz]

/-- Demand-time sync-object storage guard (`lean-miri#65`). -/
def evalSyncStorageGuard (env : CompilerQueryEnv) (allocId offset len : Nat) :
    QueryResult QueryAnswer :=
  match env.syncEvidence? with
  | none => .unsupported .missingSyncStorage
  | some regions =>
    match regions.find? (fun r => r.blocks allocId offset len) with
    | some r => .err (.syncStorageOverlap r)
    | none => .ok .syncPermit

/-- Explicit trait-method binding check of a vtable slot: with no expected trait method the
slot is accepted (the dispatcher then falls back to the fail-closed byte-level item-name check
`implementsCalledMethod`); with `some m`, slot `slotIdx` must be bound to exactly `m`
(fail-closed: an unbound slot is a mismatch). -/
def slotBindingOk (slotTraitMethods : List DefPath) (slotIdx : Nat) :
    Option DefPath → Bool
  | none => true
  | some m => decide (slotTraitMethods[slotIdx]? = some m)

/-- Demand-time `UnOp.vtableMethodLookup` (`charon#1611`), checking the slot's explicit
trait-method binding when the lookup carries one. -/
def evalVTableMethodLookup (env : CompilerQueryEnv) (vtableId : Nat) (traitRef : TraitRef)
    (slotIdx : Nat) (expectedTraitMethod? : Option DefPath) : QueryResult QueryAnswer :=
  match env.vtableEvidence? with
  | none => .unsupported .missingVTableEvidence
  | some vtables =>
    match vtables.find? (fun e => decide (e.vtableId = vtableId)) with
    | none => .err (.vtableNotFound vtableId)
    | some e =>
      if e.traitRef = traitRef then
        match e.methods[slotIdx]? with
        | some (p, tys) =>
          match slotBindingOk e.slotTraitMethods slotIdx expectedTraitMethod? with
          | true => .ok (.method p tys)
          | false => .err (.vtableSlotMethodMismatch slotIdx)
        | none => .err (.vtableSlotOutOfBounds slotIdx)
      else .err .vtableTraitMismatch

/-- Demand-time supertrait vtable pointer lookup (`charon#1611` supertrait upcast /
chained vtable resolution): resolves the direct supertrait `superTrait`'s vtable
allocation id inside `vtableId` (`traitRef`). -/
def evalVTableSupertraitLookup (env : CompilerQueryEnv) (vtableId : Nat)
    (traitRef superTrait : TraitRef) : QueryResult QueryAnswer :=
  match env.vtableEvidence? with
  | none => .unsupported .missingVTableEvidence
  | some vtables =>
    match vtables.find? (fun e => decide (e.vtableId = vtableId)) with
    | none => .err (.vtableNotFound vtableId)
    | some e =>
      if e.traitRef = traitRef then
        match e.supertraits.find? (fun s => decide (s.1 = superTrait)) with
        | some (_, superVtId) => .ok (.supertraitVTable superVtId)
        | none => .err (.vtableSupertraitNotFound vtableId superTrait)
      else .err .vtableTraitMismatch

/-- Exact bidirectional characterization of `evalAbiCompatible ... = .ok .abiOk`
(combining `abiCore` with optional Schema-13 CFI type-id agreement). -/
theorem evalAbiCompatible_ok_iff (env : CompilerQueryEnv) (callerAbi : FnAbi)
    (callee : DefPath) (cfiCallSite : Option RigidTy) :
    evalAbiCompatible env callerAbi callee cfiCallSite = .ok .abiOk ↔
      abiCore env callerAbi callee = .ok .abiOk ∧
        match cfiCallSite with
        | none => True
        | some siteTy =>
          ∃ spec tag, env.cfiEvidence? = some spec ∧
            lookupDefPathAssoc spec.calleeTypeIds callee = some tag ∧
            lookupTyAssoc spec.callSiteTypeIds siteTy = some tag := by
  unfold evalAbiCompatible
  cases cfiCallSite with
  | none => simp
  | some siteTy =>
    dsimp only
    constructor
    · intro h
      cases hc : env.cfiEvidence? with
      | none => rw [hc] at h; nomatch h
      | some spec =>
        rw [hc] at h
        dsimp only at h
        cases hcallee : lookupDefPathAssoc spec.calleeTypeIds callee with
        | none => rw [hcallee] at h; nomatch h
        | some calleeId =>
          cases hsite : lookupTyAssoc spec.callSiteTypeIds siteTy with
          | none => rw [hcallee, hsite] at h; nomatch h
          | some siteId =>
            rw [hcallee, hsite] at h
            dsimp only at h
            by_cases heq : calleeId = siteId
            · subst heq
              simp only [ite_true] at h
              exact ⟨h, spec, calleeId, rfl, hcallee, hsite⟩
            · simp only [heq, ite_false] at h
              nomatch h
    · rintro ⟨habi, spec, tag, hc, hcallee, hsite⟩
      simp only [hc, hcallee, hsite, ite_true, habi]

/-- Exact bidirectional characterization of `evalSyncStorageGuard ... = .ok .syncPermit`. -/
theorem evalSyncStorageGuard_ok_iff (env : CompilerQueryEnv) (allocId offset len : Nat) :
    evalSyncStorageGuard env allocId offset len = .ok .syncPermit ↔
      ∃ regions, env.syncEvidence? = some regions ∧
        ∀ r ∈ regions, ¬ r.blocks allocId offset len = true := by
  unfold evalSyncStorageGuard
  cases hs : env.syncEvidence? with
  | none => simp
  | some regions =>
    simp only [Option.some.injEq, exists_eq_left', ← List.find?_eq_none]
    cases regions.find? (fun r => r.blocks allocId offset len) <;> simp

/-- Exact bidirectional characterization of `evalVTableMethodLookup ... = .ok (.method p tys)`
(including the explicit trait-method binding of the slot when one is expected). -/
theorem evalVTableMethodLookup_ok_iff (env : CompilerQueryEnv) (vtableId : Nat)
    (traitRef : TraitRef) (slotIdx : Nat) (expectedTraitMethod? : Option DefPath) (p : DefPath)
    (tys : List RigidTy) :
    evalVTableMethodLookup env vtableId traitRef slotIdx expectedTraitMethod? =
        .ok (.method p tys) ↔
      ∃ vtables e, env.vtableEvidence? = some vtables ∧
        vtables.find? (fun x => decide (x.vtableId = vtableId)) = some e ∧
        e.traitRef = traitRef ∧ e.methods[slotIdx]? = some (p, tys) ∧
        slotBindingOk e.slotTraitMethods slotIdx expectedTraitMethod? = true := by
  unfold evalVTableMethodLookup
  constructor
  · intro h
    cases hv : env.vtableEvidence? with
    | none => rw [hv] at h; nomatch h
    | some vtables =>
      rw [hv] at h
      dsimp only at h
      cases hf : vtables.find? (fun x => decide (x.vtableId = vtableId)) with
      | none => rw [hf] at h; nomatch h
      | some e =>
        rw [hf] at h
        dsimp only at h
        by_cases ht : e.traitRef = traitRef
        · simp only [ht, ite_true] at h
          cases hm : e.methods[slotIdx]? with
          | none => rw [hm] at h; nomatch h
          | some pt =>
            rcases pt with ⟨p', tys'⟩
            rw [hm] at h
            dsimp only at h
            cases hb : slotBindingOk e.slotTraitMethods slotIdx expectedTraitMethod? with
            | false =>
              rw [hb] at h
              nomatch h
            | true =>
              rw [hb] at h
              injection h with ha
              injection ha with hp htys
              subst hp; subst htys
              exact ⟨vtables, e, rfl, hf, ht, hm, hb⟩
        · simp only [ht, ite_false] at h
          nomatch h
  · rintro ⟨vtables, e, hv, hf, ht, hm, hb⟩
    simp only [hv, hf, ht, ite_true, hm, hb]

/-- Exact bidirectional characterization of
`evalVTableSupertraitLookup ... = .ok (.supertraitVTable superVtId)`. -/
theorem evalVTableSupertraitLookup_ok_iff (env : CompilerQueryEnv) (vtableId : Nat)
    (traitRef superTrait : TraitRef) (superVtId : Nat) :
    evalVTableSupertraitLookup env vtableId traitRef superTrait =
        .ok (.supertraitVTable superVtId) ↔
      ∃ vtables e st, env.vtableEvidence? = some vtables ∧
        vtables.find? (fun x => decide (x.vtableId = vtableId)) = some e ∧
        e.traitRef = traitRef ∧
        e.supertraits.find? (fun s => decide (s.1 = superTrait)) = some (st, superVtId) := by
  unfold evalVTableSupertraitLookup
  constructor
  · intro h
    cases hv : env.vtableEvidence? with
    | none => rw [hv] at h; nomatch h
    | some vtables =>
      rw [hv] at h
      dsimp only at h
      cases hf : vtables.find? (fun x => decide (x.vtableId = vtableId)) with
      | none => rw [hf] at h; nomatch h
      | some e =>
        rw [hf] at h
        dsimp only at h
        by_cases ht : e.traitRef = traitRef
        · simp only [ht, ite_true] at h
          cases hs : e.supertraits.find? (fun s => decide (s.1 = superTrait)) with
          | none => rw [hs] at h; nomatch h
          | some sv =>
            rcases sv with ⟨st', vt'⟩
            rw [hs] at h
            injection h with ha
            injection ha with hvt
            subst hvt
            exact ⟨vtables, e, st', rfl, hf, ht, hs⟩
        · simp only [ht, ite_false] at h
          nomatch h
  · rintro ⟨vtables, e, st, hv, hf, ht, hs⟩
    simp only [hv, hf, ht, ite_true, hs]

/-- **Pure demand-time evaluator** of all query families. -/
def evalCompilerQuery (env : CompilerQueryEnv) : CompilerQuery → QueryResult QueryAnswer
  | .layoutOf dialect ty => evalLayoutOf env dialect ty
  | .abiCompatible callerAbi callee cfiCallSite => evalAbiCompatible env callerAbi callee cfiCallSite
  | .syncStorageGuard allocId offset len => evalSyncStorageGuard env allocId offset len
  | .vtableMethodLookup vtableId traitRef slotIdx expectedTraitMethod? =>
    evalVTableMethodLookup env vtableId traitRef slotIdx expectedTraitMethod?
  | .vtableSupertraitLookup vtableId traitRef superTrait =>
    evalVTableSupertraitLookup env vtableId traitRef superTrait

/-- Queries answerable only from Schema-13 evidence. -/
def CompilerQuery.isSchema13Only : CompilerQuery → Bool
  | .abiCompatible _ _ (some _) => true
  | .syncStorageGuard .. => true
  | .vtableMethodLookup .. => true
  | .vtableSupertraitLookup .. => true
  | _ => false

/-- **Schema-12 fail-closed fallback**: under any Schema-12 environment (whatever
its optional fields hold), every Schema-13-only query is `.unsupported`. -/
theorem query_schema12_unsupported_fallback (env : CompilerQueryEnv) (q : CompilerQuery)
    (h12 : env.schema.isSchema12 = true) (hq : q.isSchema13Only = true) :
    ∃ m, evalCompilerQuery env q = .unsupported m := by
  have h13 : env.schema.hasSchema13 = false := by
    cases hs : env.schema <;> simp_all [CompilerSchemaVersion.isSchema12,
      CompilerSchemaVersion.hasSchema13]
  cases q with
  | layoutOf _ _ => simp [CompilerQuery.isSchema13Only] at hq
  | abiCompatible callerAbi callee cfiCallSite =>
    cases cfiCallSite with
    | none => simp [CompilerQuery.isSchema13Only] at hq
    | some siteTy =>
      exact ⟨.missingCfiEvidence, by
        simp [evalCompilerQuery, evalAbiCompatible, CompilerQueryEnv.cfiEvidence?, h13]⟩
  | syncStorageGuard allocId offset len =>
    exact ⟨.missingSyncStorage, by
      simp [evalCompilerQuery, evalSyncStorageGuard, CompilerQueryEnv.syncEvidence?, h13]⟩
  | vtableMethodLookup vtableId traitRef slotIdx expectedTraitMethod? =>
    exact ⟨.missingVTableEvidence, by
      simp [evalCompilerQuery, evalVTableMethodLookup, CompilerQueryEnv.vtableEvidence?, h13]⟩
  | vtableSupertraitLookup vtableId traitRef superTrait =>
    exact ⟨.missingVTableEvidence, by
      simp [evalCompilerQuery, evalVTableSupertraitLookup, CompilerQueryEnv.vtableEvidence?, h13]⟩

/-- Corollary: a Schema-12 environment never fabricates `.ok` for a Schema-13-only
query, whether its optional Schema-13 fields are `none` or (ignored by the schema
gate) populated by a misbehaving Schema-12 producer. -/
theorem query_schema12_never_ok (env : CompilerQueryEnv) (q : CompilerQuery)
    (h12 : env.schema.isSchema12 = true) (hq : q.isSchema13Only = true) (a : QueryAnswer) :
    evalCompilerQuery env q ≠ .ok a := by
  obtain ⟨m, hm⟩ := query_schema12_unsupported_fallback env q h12 hq
  rw [hm]
  exact fun h => nomatch h

/-- Sound environment extension: finite material preserved, schema upgraded,
and effective schema-gated optional evidence monotonically populated. -/
structure EnvExtends (env₁ env₂ : CompilerQueryEnv) : Prop where
  schema_le : SchemaLe env₁.schema env₂.schema
  layoutsV06_eq : env₂.layoutsV06 = env₁.layoutsV06
  layoutsV08_ext : OptionExtends env₁.v08Layouts? env₂.v08Layouts?
  fnAbis_eq : env₂.fnAbis = env₁.fnAbis
  cfi_ext : OptionExtends env₁.cfiEvidence? env₂.cfiEvidence?
  sync_ext : OptionExtends env₁.syncEvidence? env₂.syncEvidence?
  vtables_ext : OptionExtends env₁.vtableEvidence? env₂.vtableEvidence?

theorem EnvExtends.refl (env : CompilerQueryEnv) : EnvExtends env env :=
  ⟨SchemaLe.refl _, rfl, OptionExtends.refl _, rfl, OptionExtends.refl _,
    OptionExtends.refl _, OptionExtends.refl _⟩

theorem EnvExtends.trans {env₁ env₂ env₃ : CompilerQueryEnv} (h₁ : EnvExtends env₁ env₂)
    (h₂ : EnvExtends env₂ env₃) : EnvExtends env₁ env₃ :=
  ⟨SchemaLe.trans h₁.schema_le h₂.schema_le, h₂.layoutsV06_eq.trans h₁.layoutsV06_eq,
    h₁.layoutsV08_ext.trans h₂.layoutsV08_ext, h₂.fnAbis_eq.trans h₁.fnAbis_eq,
    h₁.cfi_ext.trans h₂.cfi_ext, h₁.sync_ext.trans h₂.sync_ext,
    h₁.vtables_ext.trans h₂.vtables_ext⟩

/-- Schema-gated evidence is monotone under raw field extension. -/
theorem gated_evidence_mono {α : Type} {f : CompilerSchemaVersion → Bool}
    (hf : ∀ a b, SchemaLe a b → f a = true → f b = true) {s₁ s₂ : CompilerSchemaVersion}
    {o₁ o₂ : Option α} (hs : SchemaLe s₁ s₂) (ho : OptionExtends o₁ o₂) {x : α}
    (h : (if f s₁ then o₁ else none) = some x) : (if f s₂ then o₂ else none) = some x := by
  cases hf₁ : f s₁ with
  | false => simp [hf₁] at h
  | true =>
    simp only [hf₁, ite_true] at h
    simp [hf _ _ hs hf₁, ho x h]

/-- Raw-field extension implies `EnvExtends` on schema-gated evidence. -/
theorem EnvExtends.of_raw {env₁ env₂ : CompilerQueryEnv}
    (hs : SchemaLe env₁.schema env₂.schema)
    (hl06 : env₂.layoutsV06 = env₁.layoutsV06)
    (hl08 : OptionExtends env₁.layoutsV08 env₂.layoutsV08)
    (hfn : env₂.fnAbis = env₁.fnAbis)
    (hcfi : OptionExtends env₁.cfiTags env₂.cfiTags)
    (hsync : OptionExtends env₁.syncRegions env₂.syncRegions)
    (hvt : OptionExtends env₁.vtables env₂.vtables) :
    EnvExtends env₁ env₂ :=
  ⟨hs, hl06,
    fun _ => gated_evidence_mono (fun _ _ => hasV08Layouts_mono) hs hl08,
    hfn,
    fun _ => gated_evidence_mono (fun _ _ => hasSchema13_mono) hs hcfi,
    fun _ => gated_evidence_mono (fun _ _ => hasSchema13_mono) hs hsync,
    fun _ => gated_evidence_mono (fun _ _ => hasSchema13_mono) hs hvt⟩

theorem v08Layouts_mono {env₁ env₂ : CompilerQueryEnv} (h : EnvExtends env₁ env₂)
    {t : Trusted.Rustc.V2026_08_01.Layout.LayoutTable} (ht : env₁.v08Layouts? = some t) :
    env₂.v08Layouts? = some t :=
  h.layoutsV08_ext t ht

theorem cfiEvidence_mono {env₁ env₂ : CompilerQueryEnv} (h : EnvExtends env₁ env₂)
    {x : CfiTagSpec} (hx : env₁.cfiEvidence? = some x) : env₂.cfiEvidence? = some x :=
  h.cfi_ext x hx

theorem syncEvidence_mono {env₁ env₂ : CompilerQueryEnv} (h : EnvExtends env₁ env₂)
    {x : List SyncStorageRegion} (hx : env₁.syncEvidence? = some x) :
    env₂.syncEvidence? = some x :=
  h.sync_ext x hx

theorem vtableEvidence_mono {env₁ env₂ : CompilerQueryEnv} (h : EnvExtends env₁ env₂)
    {x : List VTableMethodEntry} (hx : env₁.vtableEvidence? = some x) :
    env₂.vtableEvidence? = some x :=
  h.vtables_ext x hx

theorem abiCore_extends {env₁ env₂ : CompilerQueryEnv} (h : EnvExtends env₁ env₂)
    (callerAbi : FnAbi) (callee : DefPath) :
    abiCore env₂ callerAbi callee = abiCore env₁ callerAbi callee := by
  simp only [abiCore, h.fnAbis_eq]

/-- **Schema monotonicity**: every supported answer (`.ok` or `.err`) is preserved
by every sound environment extension. -/
theorem query_mono_schema {env₁ env₂ : CompilerQueryEnv} (h : EnvExtends env₁ env₂)
    (q : CompilerQuery) (hsup : ∀ m, evalCompilerQuery env₁ q ≠ .unsupported m) :
    evalCompilerQuery env₂ q = evalCompilerQuery env₁ q := by
  cases q with
  | layoutOf dialect ty =>
    cases dialect with
    | v2026_06_01 => simp only [evalCompilerQuery, evalLayoutOf, h.layoutsV06_eq]
    | v2026_08_01 =>
      cases ht : env₁.v08Layouts? with
      | none =>
        exact absurd (by simp [evalCompilerQuery, evalLayoutOf, ht]) (hsup .missingV08LayoutDialect)
      | some t => simp only [evalCompilerQuery, evalLayoutOf, ht, v08Layouts_mono h ht]
  | abiCompatible callerAbi callee cfiCallSite =>
    cases cfiCallSite with
    | none => simp only [evalCompilerQuery, evalAbiCompatible, abiCore_extends h]
    | some siteTy =>
      cases hc : env₁.cfiEvidence? with
      | none =>
        exact absurd (by simp [evalCompilerQuery, evalAbiCompatible, hc]) (hsup .missingCfiEvidence)
      | some spec =>
        simp only [evalCompilerQuery, evalAbiCompatible, hc, cfiEvidence_mono h hc,
          abiCore_extends h]
  | syncStorageGuard allocId offset len =>
    cases hs : env₁.syncEvidence? with
    | none =>
      exact absurd (by simp [evalCompilerQuery, evalSyncStorageGuard, hs]) (hsup .missingSyncStorage)
    | some regions => simp only [evalCompilerQuery, evalSyncStorageGuard, hs, syncEvidence_mono h hs]
  | vtableMethodLookup vtableId traitRef slotIdx expectedTraitMethod? =>
    cases hv : env₁.vtableEvidence? with
    | none =>
      exact absurd (by simp [evalCompilerQuery, evalVTableMethodLookup, hv])
        (hsup .missingVTableEvidence)
    | some vts => simp only [evalCompilerQuery, evalVTableMethodLookup, hv, vtableEvidence_mono h hv]
  | vtableSupertraitLookup vtableId traitRef superTrait =>
    cases hv : env₁.vtableEvidence? with
    | none =>
      exact absurd (by simp [evalCompilerQuery, evalVTableSupertraitLookup, hv])
        (hsup .missingVTableEvidence)
    | some vts =>
      simp only [evalCompilerQuery, evalVTableSupertraitLookup, hv, vtableEvidence_mono h hv]

/-- **Coherent cross-dialect `layoutOf` agreement**: under any layout-coherent
environment (`env.isLayoutCoherent = true`) where `.v2026_08_01` is supported,
`evalCompilerQuery env (.layoutOf .v2026_08_01 ty)` equals
`evalCompilerQuery env (.layoutOf .v2026_06_01 ty)` for *every* `ty : Ty`. -/
theorem evalLayoutOf_v08_eq_v06_of_coherent (env : CompilerQueryEnv)
    (hcoh : env.isLayoutCoherent = true) (ty : Ty)
    (hsup : ∀ m, evalCompilerQuery env (.layoutOf .v2026_08_01 ty) ≠ .unsupported m) :
    evalCompilerQuery env (.layoutOf .v2026_08_01 ty) =
      evalCompilerQuery env (.layoutOf .v2026_06_01 ty) := by
  unfold CompilerQueryEnv.isLayoutCoherent at hcoh
  cases hv08 : env.v08Layouts? with
  | none =>
    exact absurd (by simp [evalCompilerQuery, evalLayoutOf, hv08]) (hsup .missingV08LayoutDialect)
  | some tblV08 =>
    rw [hv08, decide_eq_true_eq] at hcoh
    exact evalLayoutOf_v08_eq_v06 env tblV08 hv08 hcoh ty

/-- If `env₁` is layout-coherent with active V08 layouts (`env₁.v08Layouts? = some _`),
every `EnvExtends env₁ env₂` preserves `isLayoutCoherent`. -/
theorem isLayoutCoherent_preserved_of_v08_present {env₁ env₂ : CompilerQueryEnv}
    (h : EnvExtends env₁ env₂) (hcoh : env₁.isLayoutCoherent = true)
    {tblV08 : Trusted.Rustc.V2026_08_01.Layout.LayoutTable}
    (hv08 : env₁.v08Layouts? = some tblV08) :
    env₂.isLayoutCoherent = true := by
  unfold CompilerQueryEnv.isLayoutCoherent at hcoh ⊢
  rw [hv08] at hcoh
  rw [v08Layouts_mono h hv08, h.layoutsV06_eq]
  exact hcoh

/-- Upgrading any layout-coherent environment via `withBridgedV08Layouts` to a
schema `newSchema` (`SchemaLe env.schema newSchema`) is a sound `EnvExtends`. -/
theorem withBridgedV08Layouts_extends (env : CompilerQueryEnv)
    (newSchema : CompilerSchemaVersion) (hs : SchemaLe env.schema newSchema)
    (hcoh : env.isLayoutCoherent = true) :
    EnvExtends env (env.withBridgedV08Layouts newSchema) := by
  refine ⟨hs, rfl, ?_, rfl,
    fun _ => gated_evidence_mono (fun _ _ => hasSchema13_mono) hs (OptionExtends.refl _),
    fun _ => gated_evidence_mono (fun _ _ => hasSchema13_mono) hs (OptionExtends.refl _),
    fun _ => gated_evidence_mono (fun _ _ => hasSchema13_mono) hs (OptionExtends.refl _)⟩
  intro tblV08 ht
  unfold CompilerQueryEnv.isLayoutCoherent at hcoh
  rw [ht, decide_eq_true_eq, bridgeLayout_iff_eq] at hcoh
  unfold CompilerQueryEnv.v08Layouts? at ht ⊢
  cases hf₁ : env.schema.hasV08Layouts with
  | false => simp [hf₁] at ht
  | true =>
    have hf₂ : newSchema.hasV08Layouts = true := hasV08Layouts_mono hs hf₁
    simp [CompilerQueryEnv.withBridgedV08Layouts, hf₂, hcoh]


/-- **Layout-coherent environment extension**: strengthens `EnvExtends env₁ env₂`
with cross-dialect layout coherence of `env₂` (`env₂.isLayoutCoherent = true`),
closing the `v2026_06_01 → v2026_08_01` upgrade gap where `env₁.v08Layouts? = none`. -/
structure CoherentEnvExtends (env₁ env₂ : CompilerQueryEnv) : Prop where
  extends_ : EnvExtends env₁ env₂
  coherent₂ : env₂.isLayoutCoherent = true

theorem CoherentEnvExtends.refl (env : CompilerQueryEnv) (hcoh : env.isLayoutCoherent = true) :
    CoherentEnvExtends env env :=
  ⟨EnvExtends.refl env, hcoh⟩

theorem CoherentEnvExtends.trans {env₁ env₂ env₃ : CompilerQueryEnv}
    (h₁₂ : CoherentEnvExtends env₁ env₂) (h₂₃ : CoherentEnvExtends env₂ env₃) :
    CoherentEnvExtends env₁ env₃ :=
  ⟨EnvExtends.trans h₁₂.extends_ h₂₃.extends_, h₂₃.coherent₂⟩

/-- Upgrading any layout-coherent environment via `withBridgedV08Layouts` is a
`CoherentEnvExtends`, even when `env.schema = .v2026_06_01` (`env.v08Layouts? = none`). -/
theorem withBridgedV08Layouts_coherentExtends (env : CompilerQueryEnv)
    (newSchema : CompilerSchemaVersion) (hs : SchemaLe env.schema newSchema)
    (hcoh : env.isLayoutCoherent = true) :
    CoherentEnvExtends env (env.withBridgedV08Layouts newSchema) :=
  ⟨withBridgedV08Layouts_extends env newSchema hs hcoh,
    withBridgedV08Layouts_isLayoutCoherent env newSchema⟩

/-- When `env₁` already has active V08 layouts (`env₁.v08Layouts? = some _`) and is
layout-coherent, any `EnvExtends env₁ env₂` is automatically a `CoherentEnvExtends`. -/
theorem coherentEnvExtends_of_v08_present {env₁ env₂ : CompilerQueryEnv}
    (h : EnvExtends env₁ env₂) (hcoh : env₁.isLayoutCoherent = true)
    {tblV08 : Trusted.Rustc.V2026_08_01.Layout.LayoutTable}
    (hv08 : env₁.v08Layouts? = some tblV08) :
    CoherentEnvExtends env₁ env₂ :=
  ⟨h, isLayoutCoherent_preserved_of_v08_present h hcoh hv08⟩

/-- **Cross-dialect + schema-upgrade `layoutOf` invariance**: under
`CoherentEnvExtends env₁ env₂`, any supported `.v2026_08_01` `layoutOf` query on
`env₂` agrees with the `.v2026_06_01` `layoutOf` query on `env₁`. -/
theorem evalLayoutOf_dialect_invariant_of_coherentExtends {env₁ env₂ : CompilerQueryEnv}
    (h : CoherentEnvExtends env₁ env₂) (ty : Ty)
    (hsup : ∀ m, evalCompilerQuery env₂ (.layoutOf .v2026_08_01 ty) ≠ .unsupported m) :
    evalCompilerQuery env₂ (.layoutOf .v2026_08_01 ty) =
      evalCompilerQuery env₁ (.layoutOf .v2026_06_01 ty) := by
  rw [evalLayoutOf_v08_eq_v06_of_coherent env₂ h.coherent₂ ty hsup]
  simp only [evalCompilerQuery, evalLayoutOf, h.extends_.layoutsV06_eq]

/-- `CoherentEnvExtends env₁ env₂` also implies that the source environment `env₁` is
layout-coherent (`env₁.isLayoutCoherent = true`): either `env₁.v08Layouts? = none` (vacuously
coherent) or `env₂` inherits `env₁`'s active V08 table and `env₂.isLayoutCoherent = true`
certifies it against `env₂.layoutsV06 = env₁.layoutsV06`. -/
theorem CoherentEnvExtends.coherent₁ {env₁ env₂ : CompilerQueryEnv}
    (h : CoherentEnvExtends env₁ env₂) : env₁.isLayoutCoherent = true := by
  unfold CompilerQueryEnv.isLayoutCoherent
  cases hv₁ : env₁.v08Layouts? with
  | none => rfl
  | some tblV08 =>
    have hv₂ := v08Layouts_mono h.extends_ hv₁
    have hcoh₂ := h.coherent₂
    unfold CompilerQueryEnv.isLayoutCoherent at hcoh₂
    rw [hv₂, h.extends_.layoutsV06_eq] at hcoh₂
    exact hcoh₂

/-- **Full 2-dialect `layoutOf` invariance under `CoherentEnvExtends`**: for *any* layout
dialects `d₁, d₂ : LayoutDialect` supported in `env₁` and `env₂` respectively,
`evalCompilerQuery env₂ (.layoutOf d₂ ty) = evalCompilerQuery env₁ (.layoutOf d₁ ty)`. -/
theorem evalLayoutOf_any_dialect_of_coherentExtends {env₁ env₂ : CompilerQueryEnv}
    (h : CoherentEnvExtends env₁ env₂) (d₁ d₂ : LayoutDialect) (ty : Ty)
    (hsup₁ : ∀ m, evalCompilerQuery env₁ (.layoutOf d₁ ty) ≠ .unsupported m)
    (hsup₂ : ∀ m, evalCompilerQuery env₂ (.layoutOf d₂ ty) ≠ .unsupported m) :
    evalCompilerQuery env₂ (.layoutOf d₂ ty) =
      evalCompilerQuery env₁ (.layoutOf d₁ ty) := by
  have hd₂ : evalCompilerQuery env₂ (.layoutOf d₂ ty) =
      evalCompilerQuery env₂ (.layoutOf .v2026_06_01 ty) := by
    cases d₂ with
    | v2026_06_01 => rfl
    | v2026_08_01 => exact evalLayoutOf_v08_eq_v06_of_coherent env₂ h.coherent₂ ty hsup₂
  have hd₁ : evalCompilerQuery env₁ (.layoutOf d₁ ty) =
      evalCompilerQuery env₁ (.layoutOf .v2026_06_01 ty) := by
    cases d₁ with
    | v2026_06_01 => rfl
    | v2026_08_01 => exact evalLayoutOf_v08_eq_v06_of_coherent env₁ h.coherent₁ ty hsup₁
  rw [hd₂, hd₁]
  simp only [evalCompilerQuery, evalLayoutOf, h.extends_.layoutsV06_eq]

/-- **Sync guard specification**: for any non-empty access (`0 < len`), the guard
rejects `r` if and only if `r` is a non-empty region (`0 < r.size`) of the same
allocation overlapping `[offset, offset + len)`. -/
theorem syncStorageRegion_blocks_iff_overlap (r : SyncStorageRegion) (allocId offset len : Nat)
    (hlen : 0 < len) :
    r.blocks allocId offset len = true ↔
      r.allocId = allocId ∧ 0 < r.size ∧ offset < r.offset + r.size ∧ r.offset < offset + len := by
  simp only [SyncStorageRegion.blocks, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨ha, hs⟩, (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)⟩
    · exact ⟨ha, hs, h₂, by omega⟩
    · exact ⟨ha, hs, by omega, h₂⟩
  · rintro ⟨ha, hs, h₁, h₂⟩
    refine ⟨⟨ha, hs⟩, ?_⟩
    by_cases hle : r.offset ≤ offset
    · exact Or.inl ⟨hle, h₁⟩
    · exact Or.inr ⟨by omega, h₂⟩

/-- Eager pre-enumerated V2026_06_01 layout catalog (the pre-`#64` pipeline). -/
def eagerLayoutCatalog (tbl : LayoutTable) (tys : List Ty) : List (Ty × TypeLayout) :=
  tys.filterMap fun ty => (computeLayoutV06 tbl ty).map fun l => (ty, l)

/-- Catalog lookup. -/
def catalogLookup (cat : List (Ty × TypeLayout)) (ty : Ty) : Option TypeLayout :=
  (cat.find? fun e => e.1 == ty).map (·.2)

theorem catalogLookup_eagerLayoutCatalog (tbl : LayoutTable) :
    ∀ (tys : List Ty) (ty : Ty), ty ∈ tys →
      catalogLookup (eagerLayoutCatalog tbl tys) ty = computeLayoutV06 tbl ty
  | [], _, hmem => nomatch hmem
  | t :: ts, ty, hmem => by
    by_cases hty : t = ty
    · subst hty
      cases hc : computeLayoutV06 tbl t with
      | none =>
        simp only [eagerLayoutCatalog, List.filterMap_cons, hc, Option.map_none]
        by_cases hts : t ∈ ts
        · exact (catalogLookup_eagerLayoutCatalog tbl ts t hts).trans hc
        · have hnone : ∀ e ∈ eagerLayoutCatalog tbl ts, e.1 ≠ t := by
            intro e he heq
            simp only [eagerLayoutCatalog, List.mem_filterMap, Option.map_eq_some_iff] at he
            obtain ⟨a, ha, l, _, rfl⟩ := he
            exact hts (heq ▸ ha)
          simp only [catalogLookup, Option.map_eq_none_iff, List.find?_eq_none, beq_iff_eq]
          exact fun e he => hnone e he
      | some l =>
        simp [catalogLookup, eagerLayoutCatalog, hc]
    · have hts : ty ∈ ts := by
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd h.symm hty
        · exact h
      have ih := catalogLookup_eagerLayoutCatalog tbl ts ty hts
      cases hc : computeLayoutV06 tbl t with
      | none =>
        simp only [eagerLayoutCatalog, List.filterMap_cons, hc]
        exact ih
      | some l =>
        have hb : (t == ty) = false := by simp [hty]
        simp only [catalogLookup, eagerLayoutCatalog, List.filterMap_cons, hc, Option.map_some,
          List.find?_cons, hb] at ih ⊢
        exact ih

/-- **Eager agreement**: for every pre-enumerated type, the demand-time V2026_06_01
`layoutOf` answer is exactly the eager catalog's (`.ok` on a catalog hit,
`.err .layoutUncomputable` where the eager pipeline also had no row). -/
theorem layoutOf_agrees_with_eager (env : CompilerQueryEnv) (tys : List Ty) (ty : Ty)
    (hmem : ty ∈ tys) :
    evalCompilerQuery env (.layoutOf .v2026_06_01 ty) =
      match catalogLookup (eagerLayoutCatalog env.layoutsV06 tys) ty with
      | some l => .ok (.layout l)
      | none => .err .layoutUncomputable := by
  rw [catalogLookup_eagerLayoutCatalog env.layoutsV06 tys ty hmem]
  rfl

/-- Memo table of demand-time answers. -/
def QueryMemo : Type := List (QueryKey × QueryResult QueryAnswer)

/-- Demand-time memoization of `qs` under `env`. -/
def memoize (env : CompilerQueryEnv) (qs : List CompilerQuery) : QueryMemo :=
  qs.map fun q => (⟨env.schema, q⟩, evalCompilerQuery env q)

/-- Memo lookup. -/
def memoLookup (memo : QueryMemo) (k : QueryKey) : Option (QueryResult QueryAnswer) :=
  (List.find? (fun e => e.1 == k) memo).map (·.2)

/-- Memoized answers are the demand-time answers (`QueryKey` `DecidableEq` +
`LawfulBEq` through `instBEqOfDecidableEq`). -/
theorem memoLookup_memoize (env : CompilerQueryEnv) :
    ∀ (qs : List CompilerQuery) (q : CompilerQuery), q ∈ qs →
      memoLookup (memoize env qs) ⟨env.schema, q⟩ = some (evalCompilerQuery env q)
  | [], _, hmem => nomatch hmem
  | x :: xs, q, hmem => by
    by_cases hx : x = q
    · subst hx
      simp [memoLookup, memoize]
    · have hq : q ∈ xs := by
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd h.symm hx
        · exact h
      have ih := memoLookup_memoize env xs q hq
      simp only [memoLookup, memoize, List.map_cons, List.find?_cons] at ih ⊢
      have hne : ((⟨env.schema, x⟩ : QueryKey) == ⟨env.schema, q⟩) = false := by
        simp [hx]
      rw [hne]
      exact ih


/-! ## End-to-end: `UnOp.vtableMethodLookup → abiCompatible → OpaqueCalleeTable.lookup → stepBranchPruned` -/

/-- `charon#1611` `UnOp.vtableMethodLookup traitRef slotIdx` with optional
supertrait vtable chain (`supertraitChain`). When `supertraitChain = []`, looks
up method `slotIdx` directly in `traitRef`'s vtable; when
`supertraitChain = [subTrait, ...]`, first walks supertrait vtable pointers
along `supertraitChain → traitRef` before looking up `slotIdx`.

`expectedTraitMethod?` is the trait-method `DefPath` that `charon#1611`'s
`UnOp::VTableMethodLookup` carries for the vtable field it reads. When present, the terminal
lookup demands that the slot be bound to that trait method (`slotBindingOk`), and slot/method
agreement holds by construction — so compiler-generated shims, whose impl path need not end
in the method's name, dispatch. When absent, dispatch falls back to the fail-closed
byte-level item-name check `implementsCalledMethod` (`slotMethodAgrees`). -/
structure VTableMethodLookupOp : Type where
  traitRef : TraitRef
  slotIdx : Nat
  supertraitChain : List TraitRef := []
  expectedTraitMethod? : Option DefPath := none
  deriving DecidableEq

/-- Unary operators of the lowered program: the trusted `UnOp` plus `charon#1611`'s
demand-time `vtableMethodLookup`. -/
inductive UnOpExt : Type where
  | base (op : UnOp)
  | vtableMethodLookup (op : VTableMethodLookupOp)
  deriving DecidableEq

/-- The initial demand-time compiler query a unary operator issues on a vtable
pointer (`none` for trusted base operators, which never consult the query
environment; `.vtableMethodLookup` when `supertraitChain = []`, and the first
`.vtableSupertraitLookup` hop when `supertraitChain` is non-empty). -/
def UnOpExt.query? : UnOpExt → ProvenancePtr → Option CompilerQuery
  | .base _, _ => none
  | .vtableMethodLookup op, vtablePtr =>
    match op.supertraitChain with
    | [] =>
      some (.vtableMethodLookup vtablePtr.allocId op.traitRef op.slotIdx op.expectedTraitMethod?)
    | curTrait :: rest =>
      some (.vtableSupertraitLookup vtablePtr.allocId curTrait (rest.headD op.traitRef))

/-- Walk a chain of `UnOp.vtableMethodLookup` supertrait vtable hops starting
at `vtId` before looking up method slot `slotIdx` on the final `traitRef`. Every
hop is one application of the `UnOp.vtableMethodLookup` operator to the current
vtable pointer: the query evaluated at each hop is exactly the one
`UnOpExt.query?` issues for the remaining chain (as in `charon#1611`, where each
supertrait hop and the final method read are separate `UnOp::VTableMethodLookup`
operations on the vtable pointer the previous one returned). The expected trait method is
checked at the terminal method read only. -/
def resolveVTableChain (env : CompilerQueryEnv) (traitRef : TraitRef) (slotIdx : Nat)
    (expectedTraitMethod? : Option DefPath) :
    List TraitRef → Nat → QueryResult (DefPath × List RigidTy)
  | [], vtId =>
    match (UnOpExt.vtableMethodLookup ⟨traitRef, slotIdx, [], expectedTraitMethod?⟩).query?
        ⟨vtId, 0⟩ with
    | none => .err .answerKindMismatch
    | some q =>
      match evalCompilerQuery env q with
      | .ok (.method p tys) => .ok (p, tys)
      | .ok _ => .err .answerKindMismatch
      | .err e => .err e
      | .unsupported m => .unsupported m
  | curTrait :: restChain, vtId =>
    match (UnOpExt.vtableMethodLookup
        ⟨traitRef, slotIdx, curTrait :: restChain, expectedTraitMethod?⟩).query? ⟨vtId, 0⟩ with
    | none => .err .answerKindMismatch
    | some q =>
      match evalCompilerQuery env q with
      | .ok (.supertraitVTable nextVtId) =>
        resolveVTableChain env traitRef slotIdx expectedTraitMethod? restChain nextVtId
      | .ok _ => .err .answerKindMismatch
      | .err e => .err e
      | .unsupported m => .unsupported m

/-- `resolveVTableChain` is monotone under `EnvExtends` for any supertrait chain. -/
theorem resolveVTableChain_mono {env₁ env₂ : CompilerQueryEnv} (h : EnvExtends env₁ env₂)
    (traitRef : TraitRef) (slotIdx : Nat) (expectedTraitMethod? : Option DefPath) :
    ∀ (chain : List TraitRef) (vtId : Nat),
      (∀ m, resolveVTableChain env₁ traitRef slotIdx expectedTraitMethod? chain vtId ≠
          .unsupported m) →
        resolveVTableChain env₂ traitRef slotIdx expectedTraitMethod? chain vtId =
          resolveVTableChain env₁ traitRef slotIdx expectedTraitMethod? chain vtId
  | [], vtId, hsup => by
    unfold resolveVTableChain at hsup ⊢
    simp only [UnOpExt.query?] at hsup ⊢
    generalize hq :
      CompilerQuery.vtableMethodLookup vtId traitRef slotIdx expectedTraitMethod? = q at hsup ⊢
    cases hv : evalCompilerQuery env₁ q with
    | unsupported m => exact absurd (by simp [hv]) (hsup m)
    | err e => rw [query_mono_schema h q (by simp [hv]), hv]
    | ok a =>
      rw [query_mono_schema h q (by simp [hv]), hv]
  | curTrait :: restChain, vtId, hsup => by
    unfold resolveVTableChain at hsup ⊢
    simp only [UnOpExt.query?] at hsup ⊢
    generalize hq :
      CompilerQuery.vtableSupertraitLookup vtId curTrait (restChain.headD traitRef) = q at hsup ⊢
    cases hv : evalCompilerQuery env₁ q with
    | unsupported m => exact absurd (by simp [hv]) (hsup m)
    | err e => rw [query_mono_schema h q (by simp [hv]), hv]
    | ok a =>
      rw [query_mono_schema h q (by simp [hv]), hv]
      rw [hv] at hsup
      cases a with
      | supertraitVTable nextVtId =>
        exact resolveVTableChain_mono h traitRef slotIdx expectedTraitMethod? restChain nextVtId hsup
      | _ => rfl

/-- A `dyn Trait` method call site, lowered as in `charon#1611`: the receiver's
vtable pointer (`PtrMetadata(recv)`) is held in local `vtableLocal` of the calling
frame and read *at call time*, so `UnOp.vtableMethodLookup lookupOp` is applied to
the runtime vtable pointer. Two receivers reaching the same call key dispatch to
their own `impl`s (`canary_dyn_two_receivers`). -/
structure DynCallSite : Type where
  /-- Local of the calling frame holding the receiver's vtable pointer. -/
  vtableLocal : Nat
  /-- The `UnOp.vtableMethodLookup` applied to it. -/
  lookupOp : VTableMethodLookupOp
  /-- Caller-side ABI of the trait method signature. -/
  callerAbi : FnAbi
  /-- CFI call-site function-pointer type, when CFI-instrumented. -/
  cfiCallSite : Option RigidTy
  /-- Call key `(defPath, typeArgs)` of the `dyn` call in the caller's terminator. -/
  dynKey : DefPath × List RigidTy
  /-- Optional `(callerDefPath, blockIdx)` scope pinning this site to a specific MIR basic-block
  terminator (`none` matches any caller/block calling `dynKey`). Scoping prevents a caller's site
  from hijacking an unregistered virtual call inside a callee frame and lets distinct SSA blocks
  call the same virtual method with different `vtableLocal` temporaries (`canary_dyn_scoped_ssa_and_cross_frame_registry`). -/
  callSiteLoc? : Option (DefPath × BasicBlockIdx) := none
  deriving DecidableEq

/-- Whether `site`'s optional `(callerDefPath, blockIdx)` scope matches the active frame at `s`
(`true` when `site.callSiteLoc? = none`). -/
def DynCallSite.matchesLoc (site : DynCallSite) (body : CapturedMir) (s : MachineState) : Bool :=
  match site.callSiteLoc? with
  | none => true
  | some loc => decide (((s.memory.activeCallee.getD body).defPath, s.frame.blockIdx) = loc)

/-- The receiver's runtime vtable pointer at `s`: local `site.vtableLocal` of the
active frame must hold an initialized pointer to the *start* of a *global* (non-stack-borrow)
allocation (`offsetBytes = 0` and `lookupBorrow s.memory.borrows p.tag = none`, matching
`Terminators.lean`'s `resolveCallTarget` provenance guard); otherwise the `dyn` call is UB.
In `MirSem`, stack borrows (`&local` / `&raw const local`) allocate Tree Borrows provenance tags
in `s.memory.borrows` inside the same `Nat` `allocId` domain as global/vtable allocation IDs
(`ProvenancePtr.tag p := p.allocId`), so omitting `lookupBorrow = none` would let a transmuted
stack pointer at offset `0` alias a global vtable (`canary_dyn_stack_borrow_vtable_is_ub`). -/
def DynCallSite.vtablePtr? (site : DynCallSite) (s : MachineState) : Option ProvenancePtr :=
  match get? s.frame.locals site.vtableLocal with
  | some (.init (.ptr p _)) =>
    if p.offsetBytes = 0 && (lookupBorrow s.memory.borrows p.tag).isNone then some p else none
  | _ => none

/-- A vtable pointer read by `DynCallSite.vtablePtr?` addresses the start of its allocation. -/
theorem DynCallSite.vtablePtr?_offset {site : DynCallSite} {s : MachineState}
    {vt : ProvenancePtr} (h : site.vtablePtr? s = some vt) : vt.offsetBytes = 0 := by
  unfold DynCallSite.vtablePtr? at h
  split at h
  · split at h
    · injection h with h
      subst h
      rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact hc.1
    · nomatch h
  · nomatch h

/-- A vtable pointer read by `DynCallSite.vtablePtr?` never carries a stack-borrow tag. -/
theorem DynCallSite.vtablePtr?_no_borrow {site : DynCallSite} {s : MachineState}
    {vt : ProvenancePtr} (h : site.vtablePtr? s = some vt) :
    lookupBorrow s.memory.borrows vt.tag = none := by
  unfold DynCallSite.vtablePtr? at h
  split at h
  · split at h
    · injection h with h
      subst h
      rename_i hc
      simp only [Bool.and_eq_true] at hc
      exact Option.isNone_iff_eq_none.mp hc.2
    · nomatch h
  · nomatch h

/-- The `dyn` trait of a call key: a virtual call `<dyn D as Trait>::method`
carries `dyn D` as its first generic argument (`none` for non-virtual keys). -/
def dynSelfTrait? (key : DefPath × List RigidTy) : Option DefPath :=
  match key.2 with
  | .dynamic d :: _ => some d
  | _ => none

/-- `lastPathSegmentAux prevColon seg bytes`: the last `::`-separated segment of the
UTF-8 bytes of a `DefPath` (`seg` is the current segment, reversed; `prevColon`
records a pending single `:`, byte `58`). Structural on `bytes`, so kernel- and
`decide`-evaluable on literals, like the trusted byte-wise `stringEq`. -/
def lastPathSegmentAux : Bool → List UInt8 → List UInt8 → List UInt8
  | prev, seg, [] => (if prev then (58 : UInt8) :: seg else seg).reverse
  | prev, seg, b :: rest =>
    if b.toNat = 58 then
      if prev then lastPathSegmentAux false [] rest else lastPathSegmentAux true seg rest
    else
      lastPathSegmentAux false (b :: if prev then (58 : UInt8) :: seg else seg) rest

/-- Last `::`-separated segment (the item name) of a `DefPath`. -/
def lastPathSegment (p : DefPath) : List UInt8 :=
  lastPathSegmentAux false [] p.toByteArray.data.toList

/-- The dispatched body implements the called trait method. Rust requires an impl
item to carry the name of the trait item it implements (and an inherited default
method *is* the trait item), so a vtable slot whose target's item name differs from
the called method's (or is empty) is never the right slot: the site's `slotIdx` does
not belong to the method in its call key. -/
def implementsCalledMethod (calledMethod target : DefPath) : Bool :=
  !(lastPathSegment calledMethod).isEmpty &&
    decide (lastPathSegment calledMethod = lastPathSegment target)

/-- Whether `calledMethod` is a method item of `traitDefPath` (`calledMethod =
traitDefPath ++ "::" ++ lastPathSegment calledMethod` with a non-empty method
segment). Without this check, a site for `<dyn Area as OtherTrait>::area` paired
with an `Area` vtable lookup passes the receiver-trait checks of `DynCallSite.wellFormed`
and `implementsCalledMethod` (because both end in `::area`!) and executes `Area::area`
for an `OtherTrait::area` call (`canary_dyn_wrong_trait_prefix_fails_closed`). -/
def methodMatchesTrait (calledMethod traitDefPath : DefPath) : Bool :=
  let seg := lastPathSegment calledMethod
  !seg.isEmpty &&
    decide (calledMethod.toByteArray.data.toList =
      traitDefPath.toByteArray.data.toList ++ [(58 : UInt8), (58 : UInt8)] ++ seg)

/-- The lookup's explicit trait-method binding, if any, names exactly the called method
`site.dynKey.1` (vacuously true when the lookup carries none). -/
def DynCallSite.expectedMethodMatches (site : DynCallSite) : Bool :=
  match site.lookupOp.expectedTraitMethod? with
  | some m => decide (m = site.dynKey.1)
  | none => true

/-- **Slot/method agreement** of a resolved vtable target path. The target path must carry a
non-empty item segment (`!(lastPathSegment target).isEmpty`). With an explicit trait-method
binding (`expectedTraitMethod? = some m`), the terminal `UnOp::VTableMethodLookup` has already
checked that the slot is bound to `m` (`slotBindingOk`), so agreement is `m = site.dynKey.1`
— independent of the target's impl item name, so compiler-generated shims dispatch. Without one,
the fail-closed byte-level item-name check `implementsCalledMethod` applies. -/
def slotMethodAgrees (site : DynCallSite) (target : DefPath) : Bool :=
  !(lastPathSegment target).isEmpty &&
    match site.lookupOp.expectedTraitMethod? with
    | some m => decide (m = site.dynKey.1)
    | none => implementsCalledMethod site.dynKey.1 target

/-- Without an explicit trait-method binding, slot/method agreement is the byte-level
item-name check. -/
theorem slotMethodAgrees_of_none {site : DynCallSite} (target : DefPath)
    (h : site.lookupOp.expectedTraitMethod? = none) :
    slotMethodAgrees site target = implementsCalledMethod site.dynKey.1 target := by
  simp only [slotMethodAgrees, h, implementsCalledMethod]
  by_cases heq : lastPathSegment site.dynKey.1 = lastPathSegment target <;> simp [heq]

/-- With an explicit trait-method binding naming the called method, slot/method agreement
holds for *every* non-empty-item target (including shims whose path does not end in the method
name). -/
theorem slotMethodAgrees_of_some {site : DynCallSite} (target : DefPath) {m : DefPath}
    (h : site.lookupOp.expectedTraitMethod? = some m) (hm : m = site.dynKey.1)
    (hne : (lastPathSegment target).isEmpty = false) :
    slotMethodAgrees site target = true := by
  simp [slotMethodAgrees, h, hm, hne]

/-- **Full vtable target validity**: the resolved `(defPath, typeArgs)` pair must be a concrete
implementation or concrete default-method instantiation (`(dynSelfTrait? target).isNone`, never
an uninstantiated `dyn` key that would fall through `stepBranchPruned` to an unlinked external
call!) and its path must satisfy `slotMethodAgrees`.

The `dyn` test is deliberately conservative: it also rejects a generic impl method instantiated
at a `dyn` type (e.g. `impl<T: ?Sized + Tr> Tr for Box<T>` at `T = dyn Tr`), since paths alone
cannot distinguish impl items from trait items; such sites fail closed (`unsupported`, a
completeness gap, never a soundness one; `canary_dyn_generic_impl_at_dyn_fails_closed`). -/
def vtableTargetAgrees (site : DynCallSite) (target : DefPath × List RigidTy) : Bool :=
  (dynSelfTrait? target).isNone && slotMethodAgrees site target.1

/-- A `dyn` call site is well formed when:
1. its call key is a virtual call whose receiver type `dyn D` names the trait of
   the *first* vtable the lookup reads (`d = firstTrait.defPath`),
2. the terminal `site.lookupOp.traitRef` and every supertrait hop in
   `site.lookupOp.supertraitChain` is a `dyn` vtable trait reference whose `Self`
   argument (`args.head?`) is `.dynamic tr.defPath` (rejecting non-`dyn` or mismatched
   `Self` arguments on intermediate or terminal vtable traits;
   `canary_dyn_terminal_trait_self_mismatch_fails_closed`),
3. the call key's full generic argument list `site.dynKey.2` equals
   `.dynamic d :: site.lookupOp.traitRef.args.tail` (`Self = dyn D` followed by
   the terminal trait's generic parameters, supporting generic supertraits
   `<dyn Sub as Conv<u32>>::conv` while rejecting mismatched generic parameters;
   `canary_dyn_trait_arg_mismatch_fails_closed`, `canary_dyn_generic_supertrait_chain`),
4. `site.dynKey.1` is a method of the terminal trait `site.lookupOp.traitRef.defPath`
   (`methodMatchesTrait site.dynKey.1 site.lookupOp.traitRef.defPath`;
   `canary_dyn_wrong_trait_prefix_fails_closed`), and
5. an explicit trait-method binding, if the lookup carries one, names exactly the called
   method (`expectedMethodMatches`). -/
def DynCallSite.wellFormed (site : DynCallSite) : Bool :=
  let firstTrait := site.lookupOp.supertraitChain.headD site.lookupOp.traitRef
  match dynSelfTrait? site.dynKey with
  | some d =>
    decide (d = firstTrait.defPath) &&
      (site.lookupOp.traitRef :: site.lookupOp.supertraitChain).all
        (fun tr => decide (tr.args.head? = some (.dynamic tr.defPath))) &&
      decide (site.dynKey.2 = .dynamic d :: site.lookupOp.traitRef.args.tail) &&
      methodMatchesTrait site.dynKey.1 site.lookupOp.traitRef.defPath &&
      site.expectedMethodMatches &&
      decide (site.callerAbi.conv ≠ .rustIntrinsic)
  | none => false

/-- Resolve a `dyn` call through the runtime vtable pointer `vtablePtr`:
`resolveVTableChain` (direct or supertrait-chained `UnOp.vtableMethodLookup`),
then `abiCompatible`. -/
def resolveDynTarget (env : CompilerQueryEnv) (site : DynCallSite) (vtablePtr : ProvenancePtr) :
    QueryResult (DefPath × List RigidTy) :=
  match resolveVTableChain env site.lookupOp.traitRef site.lookupOp.slotIdx
      site.lookupOp.expectedTraitMethod? site.lookupOp.supertraitChain vtablePtr.allocId with
  | .ok (p, tys) =>
    match evalCompilerQuery env (.abiCompatible site.callerAbi p site.cfiCallSite) with
    | .ok _ => .ok (p, tys)
    | .err e => .err e
    | .unsupported m => .unsupported m
  | .err e => .err e
  | .unsupported m => .unsupported m

/-- Resolver redirecting the `dyn` call key to the dispatched method in the opaque
table (every other key resolves through the table unchanged). -/
def redirectResolver (tbl : OpaqueCalleeTable) (dynKey target : DefPath × List RigidTy) :
    CalleeResolver :=
  fun callerLayouts p tys extra =>
    if (p, tys) = dynKey then tbl.lookup callerLayouts target.1 target.2 extra
    else tbl.lookup callerLayouts p tys extra

/-- `redirectResolver` at the redirected `dynKey` rewrites to `tbl.lookupKey` on `target`
without unfolding `tbl`. -/
theorem redirectResolver_apply_hit (tbl : OpaqueCalleeTable)
    (dynKey target : DefPath × List RigidTy) {k : CalleeKey}
    (hk : (k.defPath, k.typeArgs) = dynKey) :
    k.apply (redirectResolver tbl dynKey target) =
      tbl.lookupKey ⟨k.callerLayouts, target.1, target.2, k.extraTraitImpls⟩ := by
  simp only [CalleeKey.apply, redirectResolver, ite_eq_left_of_eq_true _ _ (eq_true hk),
    OpaqueCalleeTable.lookupKey_eq]

/-- `redirectResolver` away from `dynKey` rewrites to `tbl.lookupKey k` without unfolding `tbl`. -/
theorem redirectResolver_apply_ne (tbl : OpaqueCalleeTable)
    (dynKey target : DefPath × List RigidTy) {k : CalleeKey}
    (hk : (k.defPath, k.typeArgs) ≠ dynKey) :
    k.apply (redirectResolver tbl dynKey target) = tbl.lookupKey k := by
  simp only [CalleeKey.apply, redirectResolver, ite_eq_right_of_eq_false _ _ (eq_false hk),
    OpaqueCalleeTable.lookupKey_eq]

/-- Whether the active step at `s` demands `dynKey` (`(k.defPath, k.typeArgs) = dynKey`). -/
def demandsDynKey (dynKey : DefPath × List RigidTy) (body : CapturedMir) (s : MachineState) : Bool :=
  match demandedKey? body s with
  | some k => decide ((k.defPath, k.typeArgs) = dynKey)
  | none => false

/-- Callee-body compatibility check for a resolved dynamic dispatch target: enforces
`Terminators.lean`'s `checkCalleeTargetCompatible`, exact argument-count match against the
evaluated arguments, and ABI compatibility of the actual `CapturedMir` body `calleeBody.fnAbi`
against `site.callerAbi` (since `Terminators.lean` skips `checkCalleeTargetCompatible` when
`isIndirect = false` on direct-lowered `FnDef` virtual calls). -/
def dynCalleeBodyCompatible (site : DynCallSite) (callTarget : ResolvedCallTarget)
    (calleeBody : CapturedMir) (argCount : Nat) : Bool :=
  checkCalleeTargetCompatible callTarget calleeBody argCount &&
    decide (calleeBody.argCount = argCount) &&
    (fnAbiMismatch? site.callerAbi calleeBody.fnAbi).isNone

/-- Terminator step for a resolved dynamic call to `target = (implPath, implTypeArgs)`:
1. verifies `length argOps = site.callerAbi.args.length` (failing closed `.unsupported` if the
   site's `callerAbi` disagrees with the MIR call instruction's operand count),
2. checks `dynCalleeBodyCompatible` on a `resolve` hit (faulting `.ub` if `tbl`'s `CapturedMir`
   body contradicts `site.callerAbi`), and
3. on a `resolve` miss (`none`), emits `MirStepNode.extCall` with the **resolved vtable target**
   `(target.1, target.2)` — never falling through to `isDirectExactDivTarget` or
   `evalDirectRustIntrinsic?` on the unredirected virtual key `site.dynKey` and never reporting
   the uninstantiated trait method in `MirCallReq`. -/
def stepDynTerminator (resolve : CalleeResolver) (site : DynCallSite)
    (target : DefPath × List RigidTy) (s : MachineState) (term : Terminator)
    (cb : CapturedMir) : MirStepNode :=
  match term.kind with
  | .call func argOps destination (.some targetBb) unwind =>
    if length argOps = site.callerAbi.args.length then
      match resolveCallTarget s func (length argOps) cb.localDecls cb.layouts with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok callTarget localsAfterFunc =>
        match evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
            cb.layouts s.memory.callerLocals (callStack := s.memory.callStack) with
        | .ub => MirStepNode.fail .ub
        | .unsupported => MirStepNode.unsupported
        | .ok argVals locals' =>
          match resolve cb.layouts callTarget.defPath callTarget.typeArgs s.memory.traitImpls with
          | .some calleeBody =>
            if dynCalleeBodyCompatible site callTarget calleeBody (length argVals) then
              MirStepNode.step
                (pushCalleeFrame s cb locals' destination targetBb calleeBody argVals unwind)
            else
              MirStepNode.fail .ub
          | .none =>
            MirStepNode.extCall
              { defPath := target.1, typeArgs := target.2, args := argVals, memory := s.memory }
              (resumeExternalCall s locals' destination targetBb unwind)
    else
      MirStepNode.unsupported
  | .call func argOps destination .none unwind =>
    if length argOps = site.callerAbi.args.length then
      match resolveCallTarget s func (length argOps) cb.localDecls cb.layouts with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok callTarget localsAfterFunc =>
        match evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
            cb.layouts s.memory.callerLocals (callStack := s.memory.callStack) with
        | .ub => MirStepNode.fail .ub
        | .unsupported => MirStepNode.unsupported
        | .ok argVals locals' =>
          match resolve cb.layouts callTarget.defPath callTarget.typeArgs s.memory.traitImpls with
          | .some calleeBody =>
            if dynCalleeBodyCompatible site callTarget calleeBody (length argVals) then
              MirStepNode.step
                (pushDivergingCalleeFrame s cb locals' destination unwind calleeBody argVals)
            else
              MirStepNode.fail .ub
          | .none =>
            MirStepNode.extCall
              { defPath := target.1, typeArgs := target.2, args := argVals, memory := s.memory }
              (resumeExternalDivergingCall s locals' unwind)
    else
      MirStepNode.unsupported
  | .tailCall func argOps =>
    if length argOps = site.callerAbi.args.length then
      match resolveCallTarget s func (length argOps) cb.localDecls cb.layouts with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok callTarget localsAfterFunc =>
        match evalOperands localsAfterFunc argOps s.memory.borrows s.memory.globals
            cb.layouts s.memory.callerLocals (callStack := s.memory.callStack) with
        | .ub => MirStepNode.fail .ub
        | .unsupported => MirStepNode.unsupported
        | .ok argVals _ =>
          let depth := length s.memory.callStack
          let nLocals := length s.frame.locals
          match hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
              depth nLocals with
          | true => MirStepNode.fail .ub
          | false =>
            let memAfterTeardown : Memory :=
              { s.memory with borrows := disableFrameBorrows s.memory.borrows depth nLocals }
            match resolve cb.layouts callTarget.defPath callTarget.typeArgs s.memory.traitImpls with
            | .some calleeBody =>
              if dynCalleeBodyCompatible site callTarget calleeBody (length argVals) then
                MirStepNode.step (enterTailCalleeFrame memAfterTeardown calleeBody argVals)
              else
                MirStepNode.fail .ub
            | .none =>
              MirStepNode.extCall
                { defPath := target.1, typeArgs := target.2, args := argVals,
                  memory := memAfterTeardown }
                resumeExternalTailCall
    else
      MirStepNode.unsupported
  | _ => MirStepNode.unsupported

/-- Target-redirected branch-pruned step for a resolved dynamic dispatch target `target`:
executes `stepDynTerminator` when `s` demands `site.dynKey`, and `stepBranchPruned tbl.lookup`
on all other steps. -/
def stepDynPruned (tbl : OpaqueCalleeTable) (site : DynCallSite)
    (target : DefPath × List RigidTy) (body : CapturedMir) (s : MachineState) : MirStepNode :=
  if demandsDynKey site.dynKey body s then
    match activeTerminator? body s with
    | some (term, cb) =>
      stepDynTerminator (redirectResolver tbl site.dynKey target) site target s term cb
    | none => MirStepNode.unsupported
  else
    stepBranchPruned tbl.lookup body s

theorem stepDynTerminator_congr {r₁ r₂ : CalleeResolver} (site : DynCallSite)
    (target : DefPath × List RigidTy) (s : MachineState) (term : Terminator) (cb : CapturedMir)
    (h : ∀ k, terminatorKey? s term cb = some k → k.apply r₁ = k.apply r₂) :
    stepDynTerminator r₁ site target s term cb = stepDynTerminator r₂ site target s term cb := by
  obtain ⟨kind, span⟩ := term
  cases kind with
  | call func argOps destination tgt unwind =>
    by_cases har : length argOps = site.callerAbi.args.length
    · cases hrt : resolveCallTarget s func (length argOps) cb.localDecls cb.layouts with
      | ok callTarget locals =>
        have hk := h ⟨cb.layouts, callTarget.defPath, callTarget.typeArgs, s.memory.traitImpls⟩
          (by simp only [terminatorKey?, hrt])
        simp only [CalleeKey.apply] at hk
        cases tgt <;>
          simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt, hk]
      | ub =>
        cases tgt <;> simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt]
      | unsupported =>
        cases tgt <;> simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt]
    · cases tgt <;> simp only [stepDynTerminator, ite_eq_right_of_eq_false _ _ (eq_false har)]
  | tailCall func argOps =>
    by_cases har : length argOps = site.callerAbi.args.length
    · cases hrt : resolveCallTarget s func (length argOps) cb.localDecls cb.layouts with
      | ok callTarget locals =>
        have hk := h ⟨cb.layouts, callTarget.defPath, callTarget.typeArgs, s.memory.traitImpls⟩
          (by simp only [terminatorKey?, hrt])
        simp only [CalleeKey.apply] at hk
        simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt, hk]
      | ub => simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt]
      | unsupported => simp only [stepDynTerminator, ite_eq_left_of_eq_true _ _ (eq_true har), hrt]
    · simp only [stepDynTerminator, ite_eq_right_of_eq_false _ _ (eq_false har)]
  | _ => rfl

/-- `stepDynPruned` depends on `tbl` only through `redirectResolver` at `demandedKey? body s`. -/
theorem stepDynPruned_congr {narrowTbl fullTbl : OpaqueCalleeTable} (site : DynCallSite)
    (target : DefPath × List RigidTy) (body : CapturedMir) (s : MachineState)
    (h : ∀ k, demandedKey? body s = some k →
      k.apply (redirectResolver narrowTbl site.dynKey target) =
        k.apply (redirectResolver fullTbl site.dynKey target)) :
    stepDynPruned narrowTbl site target body s = stepDynPruned fullTbl site target body s := by
  unfold stepDynPruned
  cases hd : demandsDynKey site.dynKey body s with
  | true =>
    simp only [ite_true]
    cases hact : activeTerminator? body s with
    | none => rfl
    | some p =>
      rcases p with ⟨term, cb⟩
      exact stepDynTerminator_congr site target s term cb fun k hk =>
        h k (by simp [demandedKey?, hact, hk])
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    apply stepBranchPruned_congr
    intro k hk
    have hne : (k.defPath, k.typeArgs) ≠ site.dynKey := by
      intro he
      simp [demandsDynKey, hk, he] at hd
    have hk' := h k hk
    simp only [CalleeKey.apply, redirectResolver, ite_eq_right_of_eq_false _ _ (eq_false hne)]
      at hk' ⊢
    exact hk'

theorem stepDynTerminator_frames (resolve : CalleeResolver) (site : DynCallSite)
    (target : DefPath × List RigidTy) (s : MachineState) (term : Terminator) (cb : CapturedMir) :
    FramesStep s (stepDynTerminator resolve site target s term cb) := by
  obtain ⟨kind, span⟩ := term
  cases kind with
  | call func argOps destination tgt unwind =>
    cases tgt <;>
    · dsimp only [stepDynTerminator]
      split
      · cases resolveCallTarget s func (length argOps) cb.localDecls cb.layouts with
        | ub => exact True.intro
        | unsupported => exact True.intro
        | ok callTarget locals =>
          dsimp only
          cases evalOperands locals argOps s.memory.borrows s.memory.globals cb.layouts
              s.memory.callerLocals (callStack := s.memory.callStack) with
          | ub => exact True.intro
          | unsupported => exact True.intro
          | ok argVals locals' =>
            dsimp only
            cases resolve cb.layouts callTarget.defPath callTarget.typeArgs s.memory.traitImpls with
            | none => exact True.intro
            | some calleeBody =>
              dsimp only
              split
              · exact ⟨rfl, rfl⟩
              · exact True.intro
      · exact True.intro
  | tailCall func argOps =>
    dsimp only [stepDynTerminator]
    split
    · cases resolveCallTarget s func (length argOps) cb.localDecls cb.layouts with
      | ub => exact True.intro
      | unsupported => exact True.intro
      | ok callTarget locals =>
        dsimp only
        cases evalOperands locals argOps s.memory.borrows s.memory.globals cb.layouts
            s.memory.callerLocals (callStack := s.memory.callStack) with
        | ub => exact True.intro
        | unsupported => exact True.intro
        | ok argVals locals' =>
          dsimp only
          cases hasFrameDeallocProtectorConflict s.memory.borrows s.memory.activeProtectors
              (length s.memory.callStack) (length s.frame.locals) with
          | true => exact True.intro
          | false =>
            dsimp only
            cases resolve cb.layouts callTarget.defPath callTarget.typeArgs s.memory.traitImpls with
            | none => exact True.intro
            | some calleeBody =>
              dsimp only
              split
              · exact ⟨rfl, rfl⟩
              · exact True.intro
    · exact True.intro
  | _ => exact True.intro

theorem stepDynPruned_frames (tbl : OpaqueCalleeTable) (site : DynCallSite)
    (target : DefPath × List RigidTy) (body : CapturedMir) (s : MachineState) :
    FramesStep s (stepDynPruned tbl site target body s) := by
  unfold stepDynPruned
  cases demandsDynKey site.dynKey body s with
  | true =>
    simp only [ite_true]
    cases activeTerminator? body s with
    | none => exact True.intro
    | some p => exact stepDynTerminator_frames _ site target s p.1 p.2
  | false => exact stepBranchPruned_frames tbl.lookup body s

/-- **Unified dynamic-dispatch step**: receiver vtable pointer (read from the
calling frame) `→ UnOp.vtableMethodLookup → abiCompatible →
OpaqueCalleeTable.lookup → stepDynPruned`. An ill-formed site fails closed
(`MirStepNode.unsupported`: a configuration error, never attributed to the program),
a receiver without a vtable pointer — or whose vtable pointer does not address the start
of a non-stack allocation (`DynCallSite.vtablePtr?`) — is UB, missing evidence fails closed, a CFI
type-id mismatch is the defined CFI trap (`abort`), and every other semantic error is
UB. A resolved slot that fails `vtableTargetAgrees` (either still carrying a `dyn`
receiver type or failing `slotMethodAgrees`) and a slot whose explicit binding names
another trait method (`.vtableSlotMethodMismatch`) are configuration errors and fail
closed. -/
def dynDispatchStep (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable) (site : DynCallSite)
    (body : CapturedMir) (s : MachineState) : MirStepNode :=
  if site.wellFormed then
    match site.vtablePtr? s with
    | none => MirStepNode.fail .ub
    | some vt =>
      match resolveDynTarget env site vt with
      | .ok target =>
        if vtableTargetAgrees site target then
          stepDynPruned tbl site target body s
        else MirStepNode.unsupported
      | .err .cfiTypeIdMismatch => MirStepNode.retOutcome .abort
      | .err (.vtableSlotMethodMismatch _) => MirStepNode.unsupported
      | .err _ => MirStepNode.fail .ub
      | .unsupported _ => MirStepNode.unsupported
  else MirStepNode.unsupported

/-- `resolveDynTarget` is monotone under `EnvExtends` on supported answers (for
both direct and supertrait-chained vtable lookups). -/
theorem resolveDynTarget_mono {env₁ env₂ : CompilerQueryEnv} (h : EnvExtends env₁ env₂)
    (site : DynCallSite) (vt : ProvenancePtr)
    (hsup : ∀ m, resolveDynTarget env₁ site vt ≠ .unsupported m) :
    resolveDynTarget env₂ site vt = resolveDynTarget env₁ site vt := by
  unfold resolveDynTarget at hsup ⊢
  cases hv : resolveVTableChain env₁ site.lookupOp.traitRef site.lookupOp.slotIdx
      site.lookupOp.expectedTraitMethod? site.lookupOp.supertraitChain vt.allocId with
  | unsupported m => exact absurd (by simp [hv]) (hsup m)
  | err e =>
    rw [resolveVTableChain_mono h _ _ _ _ _ (by simp [hv]), hv]
  | ok pt =>
    rcases pt with ⟨p, tys⟩
    rw [resolveVTableChain_mono h _ _ _ _ _ (by simp [hv]), hv]
    rw [hv] at hsup
    dsimp only at hsup ⊢
    cases hb : evalCompilerQuery env₁ (.abiCompatible site.callerAbi p site.cfiCallSite) with
    | unsupported m => exact absurd (by simp [hb]) (hsup m)
    | err e => rw [query_mono_schema h _ (by simp [hb]), hb]
    | ok b => rw [query_mono_schema h _ (by simp [hb]), hb]

/-- The dynamic-dispatch step on a resolved receiver is a target-redirected pruned step. -/
theorem dynDispatchStep_eq_of_resolved {env : CompilerQueryEnv} {tbl : OpaqueCalleeTable}
    {site : DynCallSite} {body : CapturedMir} {s : MachineState} {vt : ProvenancePtr}
    {target : DefPath × List RigidTy} (hwf : site.wellFormed = true)
    (hvt : site.vtablePtr? s = some vt)
    (h : resolveDynTarget env site vt = .ok target)
    (htarget : vtableTargetAgrees site target = true) :
    dynDispatchStep env tbl site body s =
      stepDynPruned tbl site target body s := by
  simp only [dynDispatchStep, hwf, ite_true, hvt, h, htarget]

/-- An ill-formed site fails closed at every state, whatever the environment,
table, or receiver. -/
theorem dynDispatchStep_of_not_wellFormed (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    {site : DynCallSite} (body : CapturedMir) (s : MachineState)
    (hwf : site.wellFormed = false) :
    dynDispatchStep env tbl site body s = MirStepNode.unsupported := by
  simp only [dynDispatchStep, hwf, Bool.false_eq_true, ite_false]

/-- A resolved vtable slot that does not agree with the called method fails closed
(`MirStepNode.unsupported`), whatever the callee table holds. -/
theorem dynDispatchStep_of_method_mismatch (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    {site : DynCallSite} (body : CapturedMir) (s : MachineState) {vt : ProvenancePtr}
    {target : DefPath × List RigidTy} (hwf : site.wellFormed = true)
    (hvt : site.vtablePtr? s = some vt)
    (hr : resolveDynTarget env site vt = .ok target)
    (hname : slotMethodAgrees site target.1 = false) :
    dynDispatchStep env tbl site body s = MirStepNode.unsupported := by
  simp only [dynDispatchStep, vtableTargetAgrees, hwf, ite_true, hvt, hr, hname,
    Bool.and_false, Bool.false_eq_true, ite_false]

/-- A resolved vtable slot whose target still carries an uninstantiated `dyn` receiver type
fails closed (`MirStepNode.unsupported`) instead of falling through to an unlinked external
call. -/
theorem dynDispatchStep_of_dyn_target (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    {site : DynCallSite} (body : CapturedMir) (s : MachineState) {vt : ProvenancePtr}
    {target : DefPath × List RigidTy} (hwf : site.wellFormed = true)
    (hvt : site.vtablePtr? s = some vt)
    (hr : resolveDynTarget env site vt = .ok target)
    (hdyn : (dynSelfTrait? target).isSome = true) :
    dynDispatchStep env tbl site body s = MirStepNode.unsupported := by
  have hnone : (dynSelfTrait? target).isNone = false := by
    cases hopt : dynSelfTrait? target <;> simp_all
  simp only [dynDispatchStep, vtableTargetAgrees, hwf, ite_true, hvt, hr, hnone,
    Bool.false_and, Bool.false_eq_true, ite_false]

/-- Preservation under `EnvExtends` (supportedness is only required on a well-formed site for
the receiver vtable pointer actually present at `s`). -/
theorem dynDispatchStep_envExtends {env₁ env₂ : CompilerQueryEnv} (h : EnvExtends env₁ env₂)
    (tbl : OpaqueCalleeTable) (site : DynCallSite) (body : CapturedMir) (s : MachineState)
    (hsup : site.wellFormed = true → ∀ vt, site.vtablePtr? s = some vt →
      ∀ m, resolveDynTarget env₁ site vt ≠ .unsupported m) :
    dynDispatchStep env₂ tbl site body s = dynDispatchStep env₁ tbl site body s := by
  unfold dynDispatchStep
  cases hwf : site.wellFormed with
  | false => rfl
  | true =>
    simp only [ite_true]
    cases hvt : site.vtablePtr? s with
    | none => rfl
    | some vt => simp only [resolveDynTarget_mono h site vt (hsup hwf vt hvt)]

/-- Preservation under call-cone narrowing. -/
theorem dynDispatchStep_cone_narrow (env : CompilerQueryEnv)
    (narrowTbl fullTbl : OpaqueCalleeTable) (site : DynCallSite) (body : CapturedMir)
    (s : MachineState)
    (hcone : site.wellFormed = true → ∀ vt target, site.vtablePtr? s = some vt →
      resolveDynTarget env site vt = .ok target → vtableTargetAgrees site target = true →
      ∀ k, demandedKey? body s = some k →
        k.apply (redirectResolver narrowTbl site.dynKey target) =
          k.apply (redirectResolver fullTbl site.dynKey target)) :
    dynDispatchStep env narrowTbl site body s = dynDispatchStep env fullTbl site body s := by
  unfold dynDispatchStep
  cases hwf : site.wellFormed with
  | false => rfl
  | true =>
    simp only [ite_true]
    cases hvt : site.vtablePtr? s with
    | none => rfl
    | some vt =>
      dsimp only
      cases hr : resolveDynTarget env site vt with
      | ok target =>
        dsimp only
        cases hn : vtableTargetAgrees site target with
        | false => rfl
        | true => exact stepDynPruned_congr site target body s (hcone hwf vt target hvt hr hn)
      | err e => cases e <;> rfl
      | unsupported m => rfl

/-- **End-to-end integration theorem**: the dynamic-dispatch step is preserved
simultaneously under a sound environment extension and call-cone narrowing. -/
theorem dynDispatchStep_preserved {env₁ env₂ : CompilerQueryEnv}
    {narrowTbl fullTbl : OpaqueCalleeTable} {site : DynCallSite} {body : CapturedMir}
    {s : MachineState} (h : EnvExtends env₁ env₂)
    (hsup : site.wellFormed = true → ∀ vt, site.vtablePtr? s = some vt →
      ∀ m, resolveDynTarget env₁ site vt ≠ .unsupported m)
    (hcone : site.wellFormed = true → ∀ vt target, site.vtablePtr? s = some vt →
      resolveDynTarget env₁ site vt = .ok target → vtableTargetAgrees site target = true →
      ∀ k, demandedKey? body s = some k →
        k.apply (redirectResolver narrowTbl site.dynKey target) =
          k.apply (redirectResolver fullTbl site.dynKey target)) :
    dynDispatchStep env₂ narrowTbl site body s = dynDispatchStep env₁ fullTbl site body s := by
  rw [dynDispatchStep_envExtends h narrowTbl site body s hsup]
  exact dynDispatchStep_cone_narrow env₁ narrowTbl fullTbl site body s hcone

/-- Every `dynDispatchStep` preserves `memory.callees` and `memory.traitImpls` (`FramesStep s`). -/
theorem dynDispatchStep_frames (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    (site : DynCallSite) (body : CapturedMir) (s : MachineState) :
    FramesStep s (dynDispatchStep env tbl site body s) := by
  unfold dynDispatchStep
  cases site.wellFormed with
  | false => exact True.intro
  | true =>
    simp only [ite_true]
    cases site.vtablePtr? s with
    | none => exact True.intro
    | some vt =>
      dsimp only
      cases resolveDynTarget env site vt with
      | ok target =>
        dsimp only
        cases vtableTargetAgrees site target with
        | false => exact True.intro
        | true =>
          simp only [ite_true]
          exact stepDynPruned_frames tbl site target body s
      | err e => cases e <;> exact True.intro
      | unsupported _ => exact True.intro



/-! ### Demand-gated dynamic dispatch -/

/-- Whether the next step at `s` demands the `dyn` call site `site` (matching both `site.dynKey`
and `site.matchesLoc body s`). -/
def demandsDynSite (site : DynCallSite) (body : CapturedMir) (s : MachineState) : Bool :=
  match demandedKey? body s with
  | some k => decide ((k.defPath, k.typeArgs) = site.dynKey) && site.matchesLoc body s
  | none => false

/-- Whether the next step at `s` demands a *virtual* call key (first generic argument
`dyn D`) not handled by `site` at `s`: either a different virtual call key or a call to
`site.dynKey` outside `site.callSiteLoc?`. -/
def demandsUnregisteredDyn (site : DynCallSite) (body : CapturedMir) (s : MachineState) : Bool :=
  match demandedKey? body s with
  | some k =>
    (dynSelfTrait? (k.defPath, k.typeArgs)).isSome && !demandsDynSite site body s
  | none => false

/-- **Demand-gated dynamic-dispatch step**: the receiver's vtable pointer is read
and `resolveDynTarget` (`vtableMethodLookup` followed by `abiCompatible`) is issued
*only* when the active step at `s` actually demands `site.dynKey`. Any *other*
virtual call fails closed (`MirStepNode.unsupported`) instead of falling through to
the trusted static resolver, which has no vtable and would turn the `dyn` call into
an unlinked external call to the trait method's `DefPath`
(`canary_unregistered_dyn_fails_closed`). All remaining steps (literal switches,
non-virtual calls, calls on the other branch) step directly via
`stepBranchPruned tbl.lookup`. -/
def dynDemandStep (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable) (site : DynCallSite)
    (body : CapturedMir) (s : MachineState) : MirStepNode :=
  if demandsDynSite site body s then
    dynDispatchStep env tbl site body s
  else if demandsUnregisteredDyn site body s then
    MirStepNode.unsupported
  else
    stepBranchPruned tbl.lookup body s

/-- Every `dynDemandStep` preserves `memory.callees` and `memory.traitImpls` (`FramesStep s`). -/
theorem dynDemandStep_frames (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    (site : DynCallSite) (body : CapturedMir) (s : MachineState) :
    FramesStep s (dynDemandStep env tbl site body s) := by
  unfold dynDemandStep
  cases demandsDynSite site body s with
  | true => exact dynDispatchStep_frames env tbl site body s
  | false =>
    cases demandsUnregisteredDyn site body s with
    | true => exact True.intro
    | false => exact stepBranchPruned_frames tbl.lookup body s

/-- At any state that demands `site.dynKey` (such as `dynAtCall`), `dynDemandStep`
is definitionally `dynDispatchStep`. -/
theorem dynDemandStep_eq_dynDispatchStep_of_demanded (env : CompilerQueryEnv)
    (tbl : OpaqueCalleeTable) (site : DynCallSite) (body : CapturedMir) (s : MachineState)
    (h : demandsDynSite site body s = true) :
    dynDemandStep env tbl site body s = dynDispatchStep env tbl site body s := by
  simp [dynDemandStep, h]

/-- A step that does not demand `site.dynKey` never consults the redirect. -/
theorem stepBranchPruned_redirect_of_not_demanded (tbl : OpaqueCalleeTable) (site : DynCallSite)
    (body : CapturedMir) (s : MachineState) (target : DefPath × List RigidTy)
    (hnd : demandsDynKey site.dynKey body s = false) :
    stepBranchPruned (redirectResolver tbl site.dynKey target) body s =
      stepBranchPruned tbl.lookup body s := by
  apply stepBranchPruned_congr
  intro k hk
  have hne : ¬ (k.defPath, k.typeArgs) = site.dynKey := by
    intro he
    simp only [demandsDynKey, hk, he, decide_true, Bool.true_eq_false] at hnd
  simp only [CalleeKey.apply, redirectResolver, ite_eq_right_of_eq_false _ _ (eq_false hne)]

/-- **Demand gating is conservative**: wherever the eager dynamic-dispatch step
resolves the receiver's method (well-formed site, `.ok target` for the vtable
pointer at `s`) and the step demands no *unregistered* virtual call, the
demand-gated step is *identical* to it. The two differ only where the eager query
fails (missing receiver, `.err`, or `.unsupported`) and the step does not demand
the `dyn` key — demand gating only removes failures of calls that are not executed
(`canary_dyn_deadBranch_schema12_succeeds`) — or where an unregistered virtual call
is demanded, which demand gating fails closed. -/
theorem dynDemandStep_eq_dynDispatchStep_of_resolved {env : CompilerQueryEnv}
    {tbl : OpaqueCalleeTable} {site : DynCallSite} {body : CapturedMir} {s : MachineState}
    {vt : ProvenancePtr} {target : DefPath × List RigidTy} (hwf : site.wellFormed = true)
    (hvt : site.vtablePtr? s = some vt) (hr : resolveDynTarget env site vt = .ok target)
    (htarget : vtableTargetAgrees site target = true)
    (hu : demandsUnregisteredDyn site body s = false) :
    dynDemandStep env tbl site body s = dynDispatchStep env tbl site body s := by
  unfold dynDemandStep
  cases hd : demandsDynSite site body s with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, ite_false, hu]
    have hnk : demandsDynKey site.dynKey body s = false := by
      unfold demandsDynKey
      cases hk : demandedKey? body s with
      | none => rfl
      | some k =>
        by_cases he : (k.defPath, k.typeArgs) = site.dynKey
        · have hds : (dynSelfTrait? site.dynKey).isSome = true := by
            unfold DynCallSite.wellFormed at hwf
            cases hds' : dynSelfTrait? site.dynKey with
            | none => rw [hds'] at hwf; nomatch hwf
            | some _ => rfl
          simp only [demandsUnregisteredDyn, hk, hd, Bool.not_false, Bool.and_true, he, hds] at hu
          nomatch hu
        · simp [he]
    rw [dynDispatchStep_eq_of_resolved hwf hvt hr htarget]
    simp [stepDynPruned, hnk]

/-- A step that does not demand the `dyn` key is exactly the trusted `stepMirFn`
step (under the `memory.callees` frame condition): demand gating adds no new
semantics off the `dyn` call. -/
theorem dynDemandStep_eq_trusted_of_not_demanded (env : CompilerQueryEnv)
    (tbl : OpaqueCalleeTable) (site : DynCallSite) (body : CapturedMir) (s : MachineState)
    (hnd : demandsDynSite site body s = false) (hu : demandsUnregisteredDyn site body s = false)
    (hframe : tbl.toList = s.memory.callees) :
    dynDemandStep env tbl site body s = stepMirFn body s := by
  simp only [dynDemandStep, hnd, hu, Bool.false_eq_true, ite_false]
  exact stepBranchPruned_eq_trusted tbl body s hframe

/-- An unregistered virtual call fails closed under every environment and table. -/
theorem dynDemandStep_of_unregistered (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    (site : DynCallSite) (body : CapturedMir) (s : MachineState)
    (hu : demandsUnregisteredDyn site body s = true) :
    dynDemandStep env tbl site body s = MirStepNode.unsupported := by
  have hnd : demandsDynSite site body s = false := by
    unfold demandsUnregisteredDyn at hu
    cases hk : demandedKey? body s with
    | none => simp [hk] at hu
    | some k =>
      rw [hk] at hu
      cases hd : demandsDynSite site body s with
      | false => rfl
      | true => simp [hd] at hu
  simp only [dynDemandStep, hnd, hu, Bool.false_eq_true, ite_false, ite_true]

/-- Fuel-bounded multi-step evaluation with demand-gated dynamic dispatch. -/
def evalDynWithOpaqueCallees (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    (site : DynCallSite) (body : CapturedMir) (fuel : Nat) (s : MachineState) : RunResult :=
  runSteps (dynDemandStep env tbl site body) fuel s []

/-- **Unconditional multi-step trusted agreement for non-`dyn` runs**: when no visited state
along the run demands a virtual call (`demandsDynSite = false` and `demandsUnregisteredDyn = false`,
e.g. a virtual call sitting only on a pruned dead branch) and `s.memory.callees = tbl.toList`,
`evalDynWithOpaqueCallees` equals the iterated trusted `stepMirFn` with no per-step frame
obligation. -/
theorem evalDynWithOpaqueCallees_eq_trusted_of_no_dyn_unconditional (env : CompilerQueryEnv)
    (tbl : OpaqueCalleeTable) (site : DynCallSite) (body : CapturedMir) (fuel : Nat)
    (s : MachineState) (hcallees : s.memory.callees = tbl.toList)
    (hnodyn : ∀ s' ∈ runVisited (stepBranchPruned tbl.lookup body) fuel s,
      demandsDynSite site body s' = false ∧ demandsUnregisteredDyn site body s' = false) :
    evalDynWithOpaqueCallees env tbl site body fuel s = runSteps (stepMirFn body) fuel s [] := by
  have h_opaque : evalDynWithOpaqueCallees env tbl site body fuel s =
      evalWithOpaqueCallees tbl body fuel s := by
    unfold evalDynWithOpaqueCallees evalWithOpaqueCallees
    refine runSteps_congr_visited fuel s [] fun s' hs' => ?_
    obtain ⟨h₁, h₂⟩ := hnodyn s' hs'
    simp only [dynDemandStep, h₁, h₂, Bool.false_eq_true, ite_false]
  rw [h_opaque]
  exact evalWithOpaqueCallees_eq_trusted_unconditional tbl body fuel s hcallees

/-- Per-state side conditions under which one demand-gated step is preserved by
`EnvExtends env₁ env₂` and narrowing `fullTbl` to `narrowTbl`. -/
structure DynStepPreserved (env₁ : CompilerQueryEnv) (narrowTbl fullTbl : OpaqueCalleeTable)
    (site : DynCallSite) (body : CapturedMir) (s : MachineState) : Prop where
  /-- A demanded well-formed `dyn` call's query is supported by `env₁`. -/
  supported : site.wellFormed = true → demandsDynSite site body s = true →
    ∀ vt, site.vtablePtr? s = some vt → ∀ m, resolveDynTarget env₁ site vt ≠ .unsupported m
  /-- A demanded well-formed `dyn` call's valid redirected key agrees across the tables. -/
  dynCone : site.wellFormed = true → demandsDynSite site body s = true →
    ∀ vt target, site.vtablePtr? s = some vt → resolveDynTarget env₁ site vt = .ok target →
      vtableTargetAgrees site target = true → ∀ k, demandedKey? body s = some k →
        k.apply (redirectResolver narrowTbl site.dynKey target) =
          k.apply (redirectResolver fullTbl site.dynKey target)
  /-- Any non-virtual demanded key agrees across the tables (unregistered virtual calls fail
  closed on both sides without consulting either table). -/
  cone : demandsDynSite site body s = false → demandsUnregisteredDyn site body s = false →
    ∀ k, demandedKey? body s = some k → narrowTbl.lookupKey k = fullTbl.lookupKey k

/-- Single-step preservation of `dynDemandStep` under `EnvExtends` (supportedness
is only needed when `site.wellFormed = true` and `demandsDynSite site body s = true`) and
call-cone narrowing. -/
theorem dynDemandStep_preserved {env₁ env₂ : CompilerQueryEnv}
    {narrowTbl fullTbl : OpaqueCalleeTable} {site : DynCallSite} {body : CapturedMir}
    {s : MachineState} (h : EnvExtends env₁ env₂)
    (hp : DynStepPreserved env₁ narrowTbl fullTbl site body s) :
    dynDemandStep env₂ narrowTbl site body s = dynDemandStep env₁ fullTbl site body s := by
  unfold dynDemandStep
  cases hd : demandsDynSite site body s with
  | true =>
    simp only [ite_true]
    exact dynDispatchStep_preserved h (fun hwf => hp.supported hwf hd)
      (fun hwf => hp.dynCone hwf hd)
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    cases hu : demandsUnregisteredDyn site body s with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      exact stepBranchPruned_congr body s (hp.cone hd hu)

/-- **Multi-step end-to-end preservation**: if every state the `env₁`/`fullTbl`
run visits satisfies `DynStepPreserved`, the entire demand-gated dynamic-dispatch
run (receiver vtable pointer → `UnOp.vtableMethodLookup` → `abiCompatible` →
`OpaqueCalleeTable.lookup` → `stepBranchPruned`, every step) is preserved under
`EnvExtends env₁ env₂` and narrowing to `narrowTbl`. -/
theorem evalDynWithOpaqueCallees_preserved {env₁ env₂ : CompilerQueryEnv}
    {narrowTbl fullTbl : OpaqueCalleeTable} {site : DynCallSite} {body : CapturedMir}
    (h : EnvExtends env₁ env₂) (fuel : Nat) (s : MachineState)
    (hvisit : ∀ s' ∈ runVisited (dynDemandStep env₁ fullTbl site body) fuel s,
      DynStepPreserved env₁ narrowTbl fullTbl site body s') :
    evalDynWithOpaqueCallees env₂ narrowTbl site body fuel s =
      evalDynWithOpaqueCallees env₁ fullTbl site body fuel s :=
  runSteps_congr_visited fuel s [] (fun s' hs' => dynDemandStep_preserved h (hvisit s' hs'))

/-- Decidable per-state certificate for `DynStepPreserved` (what a client checks by
kernel evaluation along the run). Steps that fail closed without consulting the table
(ill-formed sites, invalid vtable targets, or unregistered virtual calls) immediately
return `true`. -/
def dynStepPreservedB (env₁ : CompilerQueryEnv) (narrowTbl fullTbl : OpaqueCalleeTable)
    (site : DynCallSite) (body : CapturedMir) (s : MachineState) : Bool :=
  match demandedKey? body s with
  | none => true
  | some k =>
    if decide ((k.defPath, k.typeArgs) = site.dynKey) && site.matchesLoc body s then
      if site.wellFormed then
        match site.vtablePtr? s with
        | none => true
        | some vt =>
          match resolveDynTarget env₁ site vt with
          | .ok target =>
            if vtableTargetAgrees site target then
              decide (k.apply (redirectResolver narrowTbl site.dynKey target) =
                k.apply (redirectResolver fullTbl site.dynKey target))
            else true
          | .err _ => true
          | .unsupported _ => false
      else true
    else if (dynSelfTrait? (k.defPath, k.typeArgs)).isSome then true
    else decide (narrowTbl.lookupKey k = fullTbl.lookupKey k)

/-- The decidable certificate is sound. -/
theorem dynStepPreserved_of_check {env₁ : CompilerQueryEnv} {narrowTbl fullTbl : OpaqueCalleeTable}
    {site : DynCallSite} {body : CapturedMir} {s : MachineState}
    (hc : dynStepPreservedB env₁ narrowTbl fullTbl site body s = true) :
    DynStepPreserved env₁ narrowTbl fullTbl site body s := by
  unfold dynStepPreservedB at hc
  cases hk : demandedKey? body s with
  | none =>
    refine ⟨fun _ hd => ?_, fun _ hd => ?_, fun _ _ k hk' => ?_⟩
    · simp [demandsDynSite, hk] at hd
    · simp [demandsDynSite, hk] at hd
    · rw [hk] at hk'
      exact nomatch hk'
  | some k =>
    rw [hk] at hc
    dsimp only at hc
    cases hm : (decide ((k.defPath, k.typeArgs) = site.dynKey) && site.matchesLoc body s) with
    | true =>
      simp only [hm, ite_true] at hc
      refine ⟨fun hwf _ vt hvt m hunsup => ?_, fun hwf _ vt target hvt hr hta k' hk' => ?_,
        fun hd => ?_⟩
      · simp only [hwf, ite_true, hvt, hunsup, Bool.false_eq_true] at hc
      · rw [hk] at hk'
        cases hk'
        simp only [hwf, ite_true, hvt, hr, hta, decide_eq_true_eq] at hc
        exact hc
      · simp [demandsDynSite, hk, hm] at hd
    | false =>
      simp only [hm, Bool.false_eq_true, ite_false] at hc
      refine ⟨fun _ hd => ?_, fun _ hd => ?_, fun _ hu k' hk' => ?_⟩
      · simp [demandsDynSite, hk, hm] at hd
      · simp [demandsDynSite, hk, hm] at hd
      · rw [hk] at hk'
        cases hk'
        have hv : (dynSelfTrait? (k.defPath, k.typeArgs)).isSome = false := by
          simp [demandsUnregisteredDyn, demandsDynSite, hk, hm] at hu
          simp [hu]
        simp only [hv, Bool.false_eq_true, ite_false] at hc
        exact of_decide_eq_true hc

/-- Multi-step preservation from per-state certificates checked along the run. -/
theorem evalDynWithOpaqueCallees_preserved_of_check {env₁ env₂ : CompilerQueryEnv}
    {narrowTbl fullTbl : OpaqueCalleeTable} {site : DynCallSite} {body : CapturedMir}
    (h : EnvExtends env₁ env₂) (fuel : Nat) (s : MachineState)
    (hcheck : (runVisited (dynDemandStep env₁ fullTbl site body) fuel s).all
      (dynStepPreservedB env₁ narrowTbl fullTbl site body) = true) :
    evalDynWithOpaqueCallees env₂ narrowTbl site body fuel s =
      evalDynWithOpaqueCallees env₁ fullTbl site body fuel s :=
  evalDynWithOpaqueCallees_preserved h fuel s
    (fun s' hs' => dynStepPreserved_of_check (List.all_eq_true.mp hcheck s' hs'))

/-- **Narrow-run multi-step end-to-end preservation**: states are collected along
the *narrowed* run `runVisited (dynDemandStep env₂ narrowTbl site body) fuel s`
(so `fullTbl` is never stepped to compute the visited-state list!). -/
theorem evalDynWithOpaqueCallees_preserved_of_narrow {env₁ env₂ : CompilerQueryEnv}
    {narrowTbl fullTbl : OpaqueCalleeTable} {site : DynCallSite} {body : CapturedMir}
    (h : EnvExtends env₁ env₂) (fuel : Nat) (s : MachineState)
    (hvisit : ∀ s' ∈ runVisited (dynDemandStep env₂ narrowTbl site body) fuel s,
      DynStepPreserved env₁ narrowTbl fullTbl site body s') :
    evalDynWithOpaqueCallees env₂ narrowTbl site body fuel s =
      evalDynWithOpaqueCallees env₁ fullTbl site body fuel s := by
  symm
  exact runSteps_congr_visited fuel s []
    (fun s' hs' => (dynDemandStep_preserved h (hvisit s' hs')).symm)

/-- Narrow-run multi-step preservation from per-state certificates checked along
the *narrowed* run (`runVisited` never steps `fullTbl`). -/
theorem evalDynWithOpaqueCallees_preserved_of_narrow_check {env₁ env₂ : CompilerQueryEnv}
    {narrowTbl fullTbl : OpaqueCalleeTable} {site : DynCallSite} {body : CapturedMir}
    (h : EnvExtends env₁ env₂) (fuel : Nat) (s : MachineState)
    (hcheck : (runVisited (dynDemandStep env₂ narrowTbl site body) fuel s).all
      (dynStepPreservedB env₁ narrowTbl fullTbl site body) = true) :
    evalDynWithOpaqueCallees env₂ narrowTbl site body fuel s =
      evalDynWithOpaqueCallees env₁ fullTbl site body fuel s :=
  evalDynWithOpaqueCallees_preserved_of_narrow h fuel s
    (fun s' hs' => dynStepPreserved_of_check (List.all_eq_true.mp hcheck s' hs'))


/-! ### Multi-site dynamic-dispatch registry (`DynCallRegistry`) -/

/-- A registry of virtual call sites (one `DynCallSite` per virtual call key in the
lowered program). -/
abbrev DynCallRegistry : Type := List DynCallSite

/-- The registered `DynCallSite` for call key `key` (`(defPath, typeArgs)`), if
exactly one site is registered for it. An ambiguous key (two or more sites) has no
site, so a virtual call on it fails closed instead of silently taking whichever
site comes first (`canary_dyn_registry_ambiguity_fails_closed`), mirroring the
trusted resolver's demand for a *unique* most-specific `impl`. -/
def DynCallRegistry.findSite? (reg : DynCallRegistry) (key : DefPath × List RigidTy) :
    Option DynCallSite :=
  match reg.filter (fun site => decide (site.dynKey = key)) with
  | [site] => some site
  | _ => none

/-- A registry is well formed when every registered site is well formed and no two
sites share a call key. -/
def DynCallRegistry.wellFormed (reg : DynCallRegistry) : Bool :=
  reg.all DynCallSite.wellFormed && decide (reg.map (·.dynKey)).Nodup

/-- Exact characterization of `DynCallRegistry.wellFormed`. -/
theorem DynCallRegistry.wellFormed_iff (reg : DynCallRegistry) :
    reg.wellFormed = true ↔
      (∀ site ∈ reg, site.wellFormed = true) ∧ (reg.map (·.dynKey)).Nodup := by
  simp [DynCallRegistry.wellFormed, List.all_eq_true]

theorem filter_dynKey_eq_nil_of_not_mem :
    ∀ (reg : DynCallRegistry) (key : DefPath × List RigidTy),
      key ∉ reg.map (·.dynKey) →
        reg.filter (fun s => decide (s.dynKey = key)) = []
  | [], _, _ => rfl
  | s :: rest, key, hnm => by
    rw [List.map_cons, List.mem_cons, not_or] at hnm
    have hne : decide (s.dynKey = key) = false := decide_eq_false (fun e => hnm.1 e.symm)
    simp only [List.filter_cons, hne, Bool.false_eq_true, ite_false]
    exact filter_dynKey_eq_nil_of_not_mem rest key hnm.2

theorem filter_dynKey_of_nodup :
    ∀ (reg : DynCallRegistry) {site : DynCallSite},
      (reg.map (·.dynKey)).Nodup → site ∈ reg →
        reg.filter (fun s => decide (s.dynKey = site.dynKey)) = [site]
  | [], _, _, hmem => nomatch hmem
  | s :: rest, site, hnd, hmem => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hmem with rfl | hrest
    · simp [filter_dynKey_eq_nil_of_not_mem rest site.dynKey hnd.1]
    · have hne : s.dynKey ≠ site.dynKey :=
        fun e => hnd.1 (e ▸ List.mem_map_of_mem hrest)
      simp [hne, filter_dynKey_of_nodup rest hnd.2 hrest]

/-- Every member of a well-formed registry is uniquely resolved by `findSite?` and is
itself well formed. -/
theorem DynCallRegistry.findSite?_eq_some_of_wellFormed {reg : DynCallRegistry}
    {site : DynCallSite} (hwf : reg.wellFormed = true) (hmem : site ∈ reg) :
    reg.findSite? site.dynKey = some site ∧ site.wellFormed = true := by
  obtain ⟨hall, hnd⟩ := (DynCallRegistry.wellFormed_iff reg).mp hwf
  refine ⟨?_, hall site hmem⟩
  unfold DynCallRegistry.findSite?
  rw [filter_dynKey_of_nodup reg hnd hmem]

/-- Any site returned by `findSite?` belongs to `reg`, matches `key`, and — when `reg` is
well formed — satisfies `site.wellFormed = true`. -/
theorem DynCallRegistry.wellFormed_of_findSite? {reg : DynCallRegistry}
    {key : DefPath × List RigidTy} {site : DynCallSite}
    (hfind : reg.findSite? key = some site) :
    site ∈ reg ∧ site.dynKey = key ∧ (reg.wellFormed = true → site.wellFormed = true) := by
  unfold DynCallRegistry.findSite? at hfind
  cases hf : reg.filter (fun s => decide (s.dynKey = key)) with
  | nil => rw [hf] at hfind; nomatch hfind
  | cons a rest =>
    cases rest with
    | nil =>
      rw [hf] at hfind
      injection hfind with ha
      subst ha
      have hm : a ∈ reg.filter (fun s => decide (s.dynKey = key)) := by rw [hf]; simp
      obtain ⟨hmem, hkey⟩ := List.mem_filter.mp hm
      exact ⟨hmem, of_decide_eq_true hkey,
        fun hwf => ((DynCallRegistry.wellFormed_iff reg).mp hwf).1 a hmem⟩
    | cons _ _ => rw [hf] at hfind; nomatch hfind

/-- **Duplicate registrations fail closed**: if two entries in `pre ++ s₁ :: mid ++ s₂ :: post`
share `dynKey = key`, the registry is ill formed (`wellFormed = false`) and `findSite? key = none`. -/
theorem DynCallRegistry.findSite?_eq_none_of_duplicate
    (pre mid post : List DynCallSite) {s₁ s₂ : DynCallSite} {key : DefPath × List RigidTy}
    (hk₁ : s₁.dynKey = key) (hk₂ : s₂.dynKey = key) :
    DynCallRegistry.wellFormed (pre ++ s₁ :: mid ++ s₂ :: post) = false ∧
      DynCallRegistry.findSite? (pre ++ s₁ :: mid ++ s₂ :: post) key = none := by
  have hlen : 2 ≤ ((pre ++ s₁ :: mid ++ s₂ :: post).filter
      (fun s => decide (s.dynKey = key))).length := by
    simp [List.filter_append, hk₁, hk₂]
    omega
  have hfind : DynCallRegistry.findSite? (pre ++ s₁ :: mid ++ s₂ :: post) key = none := by
    unfold DynCallRegistry.findSite?
    cases hf : (pre ++ s₁ :: mid ++ s₂ :: post).filter (fun s => decide (s.dynKey = key)) with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => rw [hf] at hlen; simp at hlen
      | cons b rest' => rfl
  refine ⟨?_, hfind⟩
  cases hwf : DynCallRegistry.wellFormed (pre ++ s₁ :: mid ++ s₂ :: post) with
  | false => rfl
  | true =>
    have hs₁ := (DynCallRegistry.findSite?_eq_some_of_wellFormed hwf
      (by simp : s₁ ∈ pre ++ s₁ :: mid ++ s₂ :: post)).1
    rw [hk₁, hfind] at hs₁
    nomatch hs₁

/-- Whether two `DynCallSite` registrations overlap (same `dynKey` and compatible scopes). -/
def DynCallSite.overlaps (s₁ s₂ : DynCallSite) : Bool :=
  decide (s₁.dynKey = s₂.dynKey) &&
    match s₁.callSiteLoc?, s₂.callSiteLoc? with
    | some l₁, some l₂ => decide (l₁ = l₂)
    | _, _ => true

/-- Location-aware registry lookup at active state `(body, s)`: returns `some site` iff
**exactly one** registered site matches both `key` and `site.matchesLoc body s`. -/
def DynCallRegistry.findSiteAt? (reg : DynCallRegistry) (body : CapturedMir)
    (s : MachineState) (key : DefPath × List RigidTy) : Option DynCallSite :=
  match reg.filter (fun site => decide (site.dynKey = key) && site.matchesLoc body s) with
  | [site] => some site
  | _ => none

/-- Pairwise non-overlapping check on a list of `DynCallSite`s. -/
def DynCallRegistry.noOverlaps : DynCallRegistry → Bool
  | [] => true
  | s :: rest => rest.all (fun s' => !s.overlaps s') && noOverlaps rest

/-- Location-scoped registry well-formedness: every site is well formed and no two sites have
overlapping `(dynKey, callSiteLoc?)` domains (generalizing `DynCallRegistry.wellFormed` to
support multiple SSA blocks or caller/callee functions calling the same virtual method with
distinct `vtableLocal` temporaries). -/
def DynCallRegistry.scopedWellFormed (reg : DynCallRegistry) : Bool :=
  reg.all DynCallSite.wellFormed && DynCallRegistry.noOverlaps reg

/-- When every site in `reg` is unscoped (`callSiteLoc? = none`), `findSiteAt?` coincides
with `findSite?`. -/
theorem DynCallRegistry.findSiteAt?_eq_findSite?_of_unscoped (reg : DynCallRegistry)
    (body : CapturedMir) (s : MachineState) (key : DefPath × List RigidTy)
    (hun : reg.all (fun site => site.callSiteLoc?.isNone) = true) :
    reg.findSiteAt? body s key = reg.findSite? key := by
  unfold DynCallRegistry.findSiteAt? DynCallRegistry.findSite?
  have hflt :
      reg.filter (fun site => decide (site.dynKey = key) && site.matchesLoc body s) =
        reg.filter (fun site => decide (site.dynKey = key)) := by
    induction reg with
    | nil => rfl
    | cons hd tl ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hun
      have hloc : hd.matchesLoc body s = true := by
        unfold DynCallSite.matchesLoc
        cases hopt : hd.callSiteLoc? with
        | none => rfl
        | some _ => rw [hopt] at hun; nomatch hun.1
      simp only [List.filter_cons, hloc, Bool.and_true, ih hun.2]
  rw [hflt]

/-- Multi-site demand-gated dynamic-dispatch step (location-aware via `findSiteAt?`):
- if the active step at `s` demands a call key uniquely resolved at `(body, s)` in `reg`,
  dispatch via that site's `dynDispatchStep`;
- if it demands an unregistered (or ambiguously registered) virtual call key
  (`dynSelfTrait?.isSome`), fail closed (`MirStepNode.unsupported`);
- otherwise step directly via `stepBranchPruned tbl.lookup`. -/
def dynRegistryStep (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable) (reg : DynCallRegistry)
    (body : CapturedMir) (s : MachineState) : MirStepNode :=
  match demandedKey? body s with
  | some k =>
    match reg.findSiteAt? body s (k.defPath, k.typeArgs) with
    | some site => dynDispatchStep env tbl site body s
    | none =>
      if (dynSelfTrait? (k.defPath, k.typeArgs)).isSome then
        MirStepNode.unsupported
      else
        stepBranchPruned tbl.lookup body s
  | none =>
    stepBranchPruned tbl.lookup body s

/-- Every `dynRegistryStep` preserves `memory.callees` and `memory.traitImpls` (`FramesStep s`). -/
theorem dynRegistryStep_frames (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    (reg : DynCallRegistry) (body : CapturedMir) (s : MachineState) :
    FramesStep s (dynRegistryStep env tbl reg body s) := by
  unfold dynRegistryStep
  cases demandedKey? body s with
  | none => exact stepBranchPruned_frames tbl.lookup body s
  | some k =>
    dsimp only
    cases reg.findSiteAt? body s (k.defPath, k.typeArgs) with
    | some site => exact dynDispatchStep_frames env tbl site body s
    | none =>
      cases (dynSelfTrait? (k.defPath, k.typeArgs)).isSome with
      | true => exact True.intro
      | false => exact stepBranchPruned_frames tbl.lookup body s

/-- When the active step demands a uniquely matching site `site` at `(body, s)`,
`dynRegistryStep` is `dynDispatchStep env tbl site body s`. -/
theorem dynRegistryStep_eq_dynDispatchStep_of_findSite (env : CompilerQueryEnv)
    (tbl : OpaqueCalleeTable) (reg : DynCallRegistry) (body : CapturedMir) (s : MachineState)
    {k : CalleeKey} {site : DynCallSite} (hk : demandedKey? body s = some k)
    (hfind : reg.findSiteAt? body s (k.defPath, k.typeArgs) = some site) :
    dynRegistryStep env tbl reg body s = dynDispatchStep env tbl site body s := by
  simp [dynRegistryStep, hk, hfind]

/-- Any virtual call key without a unique matching entry in `reg` at `(body, s)` (unregistered or
ambiguous) fails closed (`MirStepNode.unsupported`). -/
theorem dynRegistryStep_of_unregistered (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    (reg : DynCallRegistry) (body : CapturedMir) (s : MachineState) {k : CalleeKey}
    (hk : demandedKey? body s = some k)
    (hfind : reg.findSiteAt? body s (k.defPath, k.typeArgs) = none)
    (hdyn : (dynSelfTrait? (k.defPath, k.typeArgs)).isSome = true) :
    dynRegistryStep env tbl reg body s = MirStepNode.unsupported := by
  simp [dynRegistryStep, hk, hfind, hdyn]

/-- Fuel-bounded multi-step evaluation with a `DynCallRegistry`. -/
def evalDynRegistryWithOpaqueCallees (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    (reg : DynCallRegistry) (body : CapturedMir) (fuel : Nat) (s : MachineState) : RunResult :=
  runSteps (dynRegistryStep env tbl reg body) fuel s []

/-- A singleton registry `[site]` steps identically to single-site `dynDemandStep` (for both
unscoped and `callSiteLoc?`-scoped sites). -/
theorem dynRegistryStep_singleton (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    (site : DynCallSite) (body : CapturedMir) (s : MachineState) :
    dynRegistryStep env tbl [site] body s = dynDemandStep env tbl site body s := by
  unfold dynRegistryStep dynDemandStep demandsUnregisteredDyn demandsDynSite DynCallRegistry.findSiteAt?
  cases hk : demandedKey? body s with
  | none => rfl
  | some k =>
    dsimp only
    have hcomm : (decide (site.dynKey = (k.defPath, k.typeArgs)) && site.matchesLoc body s) =
        (decide ((k.defPath, k.typeArgs) = site.dynKey) && site.matchesLoc body s) := by
      congr 1
      by_cases heq : (k.defPath, k.typeArgs) = site.dynKey
      · simp [heq]
      · have hne : site.dynKey ≠ (k.defPath, k.typeArgs) := fun h => heq h.symm
        simp [heq, hne]
    rw [List.filter_cons, List.filter_nil, hcomm]
    by_cases hb : (decide ((k.defPath, k.typeArgs) = site.dynKey) && site.matchesLoc body s) = true
    · simp [hb]
    · simp [hb]

/-- Multi-step evaluation with a singleton registry `[site]` equals `evalDynWithOpaqueCallees`. -/
theorem evalDynRegistryWithOpaqueCallees_singleton (env : CompilerQueryEnv)
    (tbl : OpaqueCalleeTable) (site : DynCallSite) (body : CapturedMir)
    (fuel : Nat) (s : MachineState) :
    evalDynRegistryWithOpaqueCallees env tbl [site] body fuel s =
      evalDynWithOpaqueCallees env tbl site body fuel s := by
  unfold evalDynRegistryWithOpaqueCallees evalDynWithOpaqueCallees
  exact runSteps_congr_visited fuel s [] (fun s' _ => dynRegistryStep_singleton env tbl site body s')

/-- A step that demands no registered site and no unregistered virtual call is
literally the trusted `stepMirFn` under the `memory.callees` frame condition. -/
theorem dynRegistryStep_eq_trusted_of_no_dyn (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    (reg : DynCallRegistry) (body : CapturedMir) (s : MachineState)
    (hnone : ∀ k, demandedKey? body s = some k →
      reg.findSiteAt? body s (k.defPath, k.typeArgs) = none ∧
      (dynSelfTrait? (k.defPath, k.typeArgs)).isSome = false)
    (hframe : tbl.toList = s.memory.callees) :
    dynRegistryStep env tbl reg body s = stepMirFn body s := by
  unfold dynRegistryStep
  cases hk : demandedKey? body s with
  | none => exact stepBranchPruned_eq_trusted tbl body s hframe
  | some k =>
    obtain ⟨hfind, hvirt⟩ := hnone k hk
    simp only [hfind, hvirt, Bool.false_eq_true, ite_false]
    exact stepBranchPruned_eq_trusted tbl body s hframe

/-- **Unconditional multi-step trusted agreement for non-`dyn` registry runs**: when no visited
state along the run demands a registered site or virtual call and `s.memory.callees = tbl.toList`,
`evalDynRegistryWithOpaqueCallees` equals the iterated trusted `stepMirFn`. -/
theorem evalDynRegistryWithOpaqueCallees_eq_trusted_of_no_dyn_unconditional
    (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable) (reg : DynCallRegistry)
    (body : CapturedMir) (fuel : Nat) (s : MachineState) (hcallees : s.memory.callees = tbl.toList)
    (hnodyn : ∀ s' ∈ runVisited (stepBranchPruned tbl.lookup body) fuel s,
      ∀ k, demandedKey? body s' = some k →
        reg.findSiteAt? body s' (k.defPath, k.typeArgs) = none ∧
        (dynSelfTrait? (k.defPath, k.typeArgs)).isSome = false) :
    evalDynRegistryWithOpaqueCallees env tbl reg body fuel s =
      runSteps (stepMirFn body) fuel s [] := by
  have h_opaque : evalDynRegistryWithOpaqueCallees env tbl reg body fuel s =
      evalWithOpaqueCallees tbl body fuel s := by
    unfold evalDynRegistryWithOpaqueCallees evalWithOpaqueCallees
    refine runSteps_congr_visited fuel s [] fun s' hs' => ?_
    unfold dynRegistryStep
    cases hk : demandedKey? body s' with
    | none => rfl
    | some k =>
      obtain ⟨hfind, hvirt⟩ := hnodyn s' hs' k hk
      simp only [hfind, hvirt, Bool.false_eq_true, ite_false]
  rw [h_opaque]
  exact evalWithOpaqueCallees_eq_trusted_unconditional tbl body fuel s hcallees

/-- Decidable per-state preservation certificate for `dynRegistryStep`. -/
def dynRegistryStepPreservedB (env₁ : CompilerQueryEnv) (narrowTbl fullTbl : OpaqueCalleeTable)
    (reg : DynCallRegistry) (body : CapturedMir) (s : MachineState) : Bool :=
  match demandedKey? body s with
  | none => true
  | some k =>
    match reg.findSiteAt? body s (k.defPath, k.typeArgs) with
    | some site =>
      if site.wellFormed then
        match site.vtablePtr? s with
        | none => true
        | some vt =>
          match resolveDynTarget env₁ site vt with
          | .ok target =>
            if vtableTargetAgrees site target then
              decide (k.apply (redirectResolver narrowTbl site.dynKey target) =
                k.apply (redirectResolver fullTbl site.dynKey target))
            else true
          | .err _ => true
          | .unsupported _ => false
      else true
    | none =>
      if (dynSelfTrait? (k.defPath, k.typeArgs)).isSome then true
      else decide (narrowTbl.lookupKey k = fullTbl.lookupKey k)

/-- Single-step preservation of `dynRegistryStep` when `dynRegistryStepPreservedB` holds. -/
theorem dynRegistryStep_preserved_of_check {env₁ env₂ : CompilerQueryEnv}
    {narrowTbl fullTbl : OpaqueCalleeTable} {reg : DynCallRegistry}
    {body : CapturedMir} {s : MachineState} (h : EnvExtends env₁ env₂)
    (hc : dynRegistryStepPreservedB env₁ narrowTbl fullTbl reg body s = true) :
    dynRegistryStep env₂ narrowTbl reg body s = dynRegistryStep env₁ fullTbl reg body s := by
  unfold dynRegistryStep
  unfold dynRegistryStepPreservedB at hc
  cases hk : demandedKey? body s with
  | none =>
    exact stepBranchPruned_congr body s (fun k hk' => by rw [hk] at hk'; nomatch hk')
  | some k =>
    rw [hk] at hc
    dsimp only at hc ⊢
    cases hf : reg.findSiteAt? body s (k.defPath, k.typeArgs) with
    | some site =>
      rw [hf] at hc
      dsimp only at hc
      apply dynDispatchStep_preserved h
      · intro hwf vt hvt m hm
        simp only [hwf, ite_true, hvt, hm, Bool.false_eq_true] at hc
      · intro hwf vt target hvt hr hta k' hk'
        rw [hk] at hk'
        cases hk'
        simp only [hwf, ite_true, hvt, hr, hta, decide_eq_true_eq] at hc
        exact hc
    | none =>
      rw [hf] at hc
      dsimp only at hc
      cases hv : (dynSelfTrait? (k.defPath, k.typeArgs)).isSome with
      | true => rfl
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        simp only [hv, Bool.false_eq_true, ite_false, decide_eq_true_eq] at hc
        exact stepBranchPruned_congr body s (fun k' hk' => by
          rw [hk] at hk'
          cases hk'
          exact hc)

/-- Multi-step preservation of `evalDynRegistryWithOpaqueCallees` checked along the
narrowed run (`runVisited` steps only `narrowTbl`). -/
theorem evalDynRegistryWithOpaqueCallees_preserved_of_narrow_check
    {env₁ env₂ : CompilerQueryEnv} {narrowTbl fullTbl : OpaqueCalleeTable}
    {reg : DynCallRegistry} {body : CapturedMir}
    (h : EnvExtends env₁ env₂) (fuel : Nat) (s : MachineState)
    (hcheck : (runVisited (dynRegistryStep env₂ narrowTbl reg body) fuel s).all
      (dynRegistryStepPreservedB env₁ narrowTbl fullTbl reg body) = true) :
    evalDynRegistryWithOpaqueCallees env₂ narrowTbl reg body fuel s =
      evalDynRegistryWithOpaqueCallees env₁ fullTbl reg body fuel s := by
  symm
  exact runSteps_congr_visited fuel s []
    (fun s' hs' => (dynRegistryStep_preserved_of_check h (List.all_eq_true.mp hcheck s' hs')).symm)


end Anneal.CompilerQueryEnv
