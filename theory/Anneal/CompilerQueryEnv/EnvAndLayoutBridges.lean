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
OpaqueCalleeTable.lookup → stepDynPruned` built on `Anneal.OpaqueCalleeTable`.

* **Schemas and evidence.** `CompilerSchemaVersion` (`v2026_06_01`, `v2026_08_01` = Schema 12;
  `schema13`) with the decidable total order `SchemaLe`; three-way `QueryResult`
  (`ok` / `err` / `unsupported`); every V2026_08_01 and Schema-13 field of
  `CompilerQueryEnv` is schema-gated (`v08Layouts?`, `cfiEvidence?`, `syncEvidence?`,
  `vtableEvidence?`).
* **Dialect bridges.** `V2026_06_01 ↔ V2026_08_01` layout and `RigidTy` bridges, lossless
  except for the V2026_06_01-only explicit variant discriminants (`bridgeTypeLayout_roundtrip_erase`,
  `bridgeLayout_roundtrip_iff`), and universal 21-constructor `computeLayout` commutation
  (`computeLayout_bridge_commutes`, `computeLayout_discrFree`, `evalLayoutOf_v08_eq_v06`),
  decidable layout coherence (`isLayoutCoherent`), the canonical upgrade
  `withBridgedV08Layouts` (coherent exactly on discriminant-free tables,
  `withBridgedV08Layouts_isLayoutCoherent_iff`), `EnvExtends` over the schema-gated accessors, and
  `CoherentEnvExtends` (`evalLayoutOf_dialect_invariant_of_coherentExtends`).
* **Five query families** (`layoutOf`, `abiCompatible` with the CFI demand in the key,
  `syncStorageGuard`, `vtableMethodLookup` with the explicit trait-method binding in the key,
  `vtableSupertraitLookup`): fail-closed Schema-12 fallback
  (`query_schema12_unsupported_fallback`), schema monotonicity (`query_mono_schema`),
  eager-catalog and memo agreement, and exact `.ok` characterizations of all five.
* **Dynamic dispatch.** `DynCallSite` reads the receiver's vtable pointer at call time (the
  start of a non-stack allocation, else UB), chains supertrait hops through `UnOpExt.query?`,
  binds the called trait method explicitly (`expectedTraitMethod?`, so compiler-generated shims
  dispatch) or else falls back to the fail-closed item-name check `implementsCalledMethod`, and
  is checked by `DynCallSite.wellFormed` (`methodMatchesTrait`, generic supertraits). The call
  itself is `stepDynTerminator`, whose every successful step is the resolver-parametric trusted
  call step with only the virtual key redirected to the vtable-resolved target
  (`stepTerminatorWith_of_stepDynTerminator_step`, `dynDispatchStep_step_spec`). Sites are
  scoped to a function and block (`callSiteLoc?`; unscoped sites to the root function) and to
  direct calls, registries are unambiguous (`DynCallRegistry.findSite?`; location-scoped
  `findSiteAt?` with unique resolution under `scopedWellFormed` / the root-aware
  `scopedWellFormedFor`), unregistered virtual calls fail closed (`demandsUnregisteredDyn`), and
  narrow-run certificates (decidable, demand-collected, or `OpaqueCalleeTable.AgreesOn`-based)
  preserve whole runs under `EnvExtends` and call-cone narrowing.

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

/-! `DecidableEq` without `BEq` on the V2026_08_01 types, schemas and evidence, the
V2026_06_01 / V2026_08_01 layout and `RigidTy` bridges, the finite-material environment,
its five query families, and environment extension. -/

/-! ## `DecidableEq` without `BEq` on the `Trusted` V2026_08_01 types

As for V2026_06_01 (`Anneal.OpaqueCalleeTable`), every instance is `DecidableEq` only; the
nine enumeration-shaped types use `OpaqueCalleeTable.decEqOfCtorIdx`, so no global
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

/-- `l` with its explicit per-variant discriminants (`TypeLayout.variantDiscriminants`, a
V2026_06_01-only field: the V2026_08_01 `TypeLayout` has no counterpart) erased. -/
def eraseVariantDiscriminants (l : TypeLayout) : TypeLayout :=
  { l with variantDiscriminants := [] }

/-- No layout of `es` carries explicit per-variant discriminants: exactly the layouts the
V2026_06_01 → V2026_08_01 → V2026_06_01 bridge keeps unchanged
(`bridgeTypeLayout_roundtrip_iff`). -/
abbrev LayoutsDiscrFree (es : List TypeLayout) : Prop := ∀ l ∈ es, l.variantDiscriminants = []

/-- The V2026_08_01 → V2026_06_01 bridge never invents explicit variant discriminants. -/
@[simp] theorem bridgeTypeLayoutV08ToV06_variantDiscriminants
    (l : Trusted.Rustc.V2026_08_01.Layout.TypeLayout) :
    (bridgeTypeLayoutV08ToV06 l).variantDiscriminants = [] := rfl

/-- Every entry of a bridged V2026_08_01 table is discriminant-free. -/
theorem bridgeLayoutV08ToV06_discrFree (t : Trusted.Rustc.V2026_08_01.Layout.LayoutTable) :
    LayoutsDiscrFree (bridgeLayoutV08ToV06 t).entries := by
  intro l hl
  obtain ⟨l₀, -, rfl⟩ := List.mem_map.mp hl
  rfl

/-- **Exact V2026_06_01 → V2026_08_01 → V2026_06_01 bridge** on `TypeLayout`: every field
survives except the V2026_06_01-only explicit variant discriminants, which are erased. -/
theorem bridgeTypeLayout_roundtrip_erase (l : TypeLayout) :
    bridgeTypeLayoutV08ToV06 (bridgeTypeLayoutV06ToV08 l) = eraseVariantDiscriminants l := by
  obtain ⟨size, align, backendRepr, fields, variants, isUninhabited, fieldLayouts,
    variantDiscriminants⟩ := l
  simp only [bridgeTypeLayoutV06ToV08, bridgeTypeLayoutV08ToV06, eraseVariantDiscriminants]
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

/-- **Lossless bridge on discriminant-free layouts**: V2026_06_01 → V2026_08_01 →
V2026_06_01 is the identity on every `TypeLayout` without explicit variant discriminants. -/
theorem bridgeTypeLayout_roundtrip (l : TypeLayout) (hl : l.variantDiscriminants = []) :
    bridgeTypeLayoutV08ToV06 (bridgeTypeLayoutV06ToV08 l) = l := by
  rw [bridgeTypeLayout_roundtrip_erase]
  obtain ⟨size, align, backendRepr, fields, variants, isUninhabited, fieldLayouts,
    variantDiscriminants⟩ := l
  dsimp only at hl
  subst hl
  rfl

/-- The type-layout bridge round-trips **exactly** on the discriminant-free layouts. -/
theorem bridgeTypeLayout_roundtrip_iff (l : TypeLayout) :
    bridgeTypeLayoutV08ToV06 (bridgeTypeLayoutV06ToV08 l) = l ↔ l.variantDiscriminants = [] :=
  ⟨fun h => h ▸ bridgeTypeLayoutV08ToV06_variantDiscriminants _, bridgeTypeLayout_roundtrip l⟩

/-- **Lossless table bridge** on discriminant-free `LayoutTable`s. -/
theorem bridgeLayout_roundtrip (t : LayoutTable) (ht : LayoutsDiscrFree t.entries) :
    bridgeLayoutV08ToV06 (bridgeLayoutV06ToV08 t) = t := by
  obtain ⟨pointerBits, isLittleEndian, entries⟩ := t
  simp only [bridgeLayoutV06ToV08, bridgeLayoutV08ToV06, List.map_map]
  congr
  conv => rhs; rw [← List.map_id entries]
  apply List.map_congr_left
  intro x hx
  exact bridgeTypeLayout_roundtrip x (ht x hx)

/-- The table bridge round-trips **exactly** on the discriminant-free tables. -/
theorem bridgeLayout_roundtrip_iff (t : LayoutTable) :
    bridgeLayoutV08ToV06 (bridgeLayoutV06ToV08 t) = t ↔ LayoutsDiscrFree t.entries :=
  ⟨fun h => h ▸ bridgeLayoutV08ToV06_discrFree _, bridgeLayout_roundtrip t⟩

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

theorem get?_mem {α : Type} : ∀ (xs : List α) (i : Nat) (x : α), get? xs i = some x → x ∈ xs
  | [], _, _, h => by cases h
  | y :: ys, 0, x, h => by
    have : y = x := Option.some.inj h
    subst this
    exact List.Mem.head _
  | _ :: ys, n + 1, x, h => List.Mem.tail _ (get?_mem ys n x h)

theorem lookupFieldLayouts_mem (es : List TypeLayout) :
    ∀ (idxs : List Nat) (fls : List TypeLayout), lookupFieldLayouts es idxs = some fls →
      ∀ x ∈ fls, x ∈ es
  | [], fls, h => by
    have : fls = [] := (Option.some.inj h).symm
    subst this
    intro x hx
    cases hx
  | idx :: rest, fls, h => by
    unfold lookupFieldLayouts at h
    cases hg : get? es idx with
    | none => rw [hg] at h; cases h
    | some fl =>
      cases hr : lookupFieldLayouts es rest with
      | none => rw [hg, hr] at h; cases h
      | some fls' =>
        rw [hg, hr] at h
        have : fls = fl :: fls' := (Option.some.inj h).symm
        subst this
        intro x hx
        cases hx with
        | head => exact get?_mem es idx fl hg
        | tail _ hx => exact lookupFieldLayouts_mem es rest fls' hr x hx

/-- `recomputeFromFieldLayouts` keeps a discriminant-free layout discriminant-free over
discriminant-free external entries. -/
theorem recomputeFromFieldLayouts_discrFree (es : List TypeLayout) (l : TypeLayout)
    (hes : LayoutsDiscrFree es) (hl : l.variantDiscriminants = []) :
    (TypeLayout.recomputeFromFieldLayouts es l).variantDiscriminants = [] := by
  unfold TypeLayout.recomputeFromFieldLayouts
  split
  · exact hl
  · cases hlk : lookupFieldLayouts es l.fieldLayouts with
    | none => exact hl
    | some fls =>
      dsimp only
      repeat' (first | exact hl | rfl | split)
      all_goals (rename_i fl0; exact hes fl0 (lookupFieldLayouts_mem es _ _ hlk _ (List.Mem.head _)))

/-- **`layout_of` never invents explicit variant discriminants**: every V2026_06_01
`RigidTy.computeLayout` result (empty substitution) over discriminant-free external entries and
a discriminant-free seed layout is discriminant-free. -/
theorem computeLayout_discrFree (ptrBits : Nat) (es : List TypeLayout) (hes : LayoutsDiscrFree es) :
    ∀ (orig : Option TypeLayout) (k : RigidTy) (l : TypeLayout),
      (∀ o, orig = some o → o.variantDiscriminants = []) →
      RigidTy.computeLayout ptrBits es [] orig k = some l → l.variantDiscriminants = []
  | orig, k, l, horig, h => by
    cases k <;> simp only [RigidTy.computeLayout] at h
    all_goals (repeat' (first
      | exact horig _ h
      | (injection h with h; subst h; first | rfl | (exact horig _ ‹_›) | skip)
      | split at h))
    all_goals first
      | exact recomputeFromFieldLayouts_discrFree es _ hes (horig _ rfl)
      | exact horig _ rfl
      | (dsimp only; exact horig _ rfl)

/-- `computeLayoutV06` over a discriminant-free table is discriminant-free. -/
theorem computeLayoutV06_discrFree (tbl : LayoutTable) (htbl : LayoutsDiscrFree tbl.entries)
    (ty : Ty) (l : TypeLayout) (h : computeLayoutV06 tbl ty = some l) :
    l.variantDiscriminants = [] :=
  computeLayout_discrFree tbl.pointerBits tbl.entries htbl _ ty.kind l
    (fun o ho => htbl o (get?_mem _ _ _ ho)) h

/-- **Exact cross-dialect layout agreement (`V06 → V08`)**: for every `tbl : LayoutTable` and
every `ty : Ty`, `computeLayoutV08Bridged` on the bridged table is `computeLayoutV06` with the
V2026_06_01-only explicit variant discriminants erased. -/
theorem computeLayoutV08Bridged_bridgeLayoutV06ToV08 (tbl : LayoutTable) (ty : Ty) :
    computeLayoutV08Bridged (bridgeLayoutV06ToV08 tbl) ty =
      (computeLayoutV06 tbl ty).map eraseVariantDiscriminants := by
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
  | some l => simp [Function.comp, bridgeTypeLayout_roundtrip_erase]

/-- **Universal cross-dialect layout agreement (`V06 → V08`) on discriminant-free tables**:
for every discriminant-free `tbl : LayoutTable` and every `ty : Ty`, `computeLayoutV08Bridged`
on the bridged table equals `computeLayoutV06`. -/
theorem computeLayoutV08Bridged_bridgeLayoutV06ToV08_of_discrFree (tbl : LayoutTable)
    (htbl : LayoutsDiscrFree tbl.entries) (ty : Ty) :
    computeLayoutV08Bridged (bridgeLayoutV06ToV08 tbl) ty = computeLayoutV06 tbl ty := by
  rw [computeLayoutV08Bridged_bridgeLayoutV06ToV08]
  cases h : computeLayoutV06 tbl ty with
  | none => rfl
  | some l =>
    have hl := computeLayoutV06_discrFree tbl htbl ty l h
    obtain ⟨size, align, backendRepr, fields, variants, isUninhabited, fieldLayouts,
      variantDiscriminants⟩ := l
    dsimp only at hl
    subst hl
    rfl

/-- **Universal cross-dialect layout agreement (`V08 → V06`)**: for every
V2026_08_01 `tbl : LayoutTable` and every `ty : Ty`, `computeLayoutV08Bridged tbl ty`
equals `computeLayoutV06 (bridgeLayoutV08ToV06 tbl) ty`. -/
theorem computeLayoutV08Bridged_eq_computeLayoutV06_bridge
    (tbl : Trusted.Rustc.V2026_08_01.Layout.LayoutTable) (ty : Ty) :
    computeLayoutV08Bridged tbl ty = computeLayoutV06 (bridgeLayoutV08ToV06 tbl) ty := by
  rw [← computeLayoutV08Bridged_bridgeLayoutV06ToV08_of_discrFree (bridgeLayoutV08ToV06 tbl)
    (bridgeLayoutV08ToV06_discrFree tbl) ty, bridgeLayout_roundtrip_v08]

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
holds if and only if `tblV08 = bridgeLayoutV06ToV08 tblV06` and `tblV06` carries no explicit
variant discriminants (which no V2026_08_01 table can express). -/
theorem bridgeLayout_iff_eq (tblV08 : Trusted.Rustc.V2026_08_01.Layout.LayoutTable)
    (tblV06 : LayoutTable) :
    bridgeLayoutV08ToV06 tblV08 = tblV06 ↔
      tblV08 = bridgeLayoutV06ToV08 tblV06 ∧ LayoutsDiscrFree tblV06.entries := by
  constructor
  · rintro rfl
    exact ⟨(bridgeLayout_roundtrip_v08 tblV08).symm, bridgeLayoutV08ToV06_discrFree tblV08⟩
  · rintro ⟨rfl, hdf⟩
    exact bridgeLayout_roundtrip tblV06 hdf

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

/-- `withBridgedV08Layouts` satisfies `isLayoutCoherent` whenever `env.layoutsV06` carries
no explicit variant discriminants (`withBridgedV08Layouts_isLayoutCoherent_iff`). -/
theorem withBridgedV08Layouts_isLayoutCoherent (env : CompilerQueryEnv)
    (newSchema : CompilerSchemaVersion) (hdf : LayoutsDiscrFree env.layoutsV06.entries) :
    (env.withBridgedV08Layouts newSchema).isLayoutCoherent = true := by
  unfold CompilerQueryEnv.isLayoutCoherent CompilerQueryEnv.v08Layouts?
    CompilerQueryEnv.withBridgedV08Layouts
  cases newSchema.hasV08Layouts <;> simp [bridgeLayout_roundtrip _ hdf]

/-- Exact coherence of the smart upgrader into a V2026_08_01-layout schema: coherent iff
`env.layoutsV06` carries no explicit variant discriminants. -/
theorem withBridgedV08Layouts_isLayoutCoherent_iff (env : CompilerQueryEnv)
    (newSchema : CompilerSchemaVersion) (hs : newSchema.hasV08Layouts = true) :
    (env.withBridgedV08Layouts newSchema).isLayoutCoherent = true ↔
      LayoutsDiscrFree env.layoutsV06.entries := by
  unfold CompilerQueryEnv.isLayoutCoherent CompilerQueryEnv.v08Layouts?
    CompilerQueryEnv.withBridgedV08Layouts
  simp only [hs, ite_true, decide_eq_true_eq]
  exact bridgeLayout_roundtrip_iff env.layoutsV06

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

/-- Upgrading any layout-coherent environment whose V2026_06_01 table carries no explicit
variant discriminants via `withBridgedV08Layouts` is a `CoherentEnvExtends`, even when
`env.schema = .v2026_06_01` (`env.v08Layouts? = none`). -/
theorem withBridgedV08Layouts_coherentExtends (env : CompilerQueryEnv)
    (newSchema : CompilerSchemaVersion) (hs : SchemaLe env.schema newSchema)
    (hcoh : env.isLayoutCoherent = true) (hdf : LayoutsDiscrFree env.layoutsV06.entries) :
    CoherentEnvExtends env (env.withBridgedV08Layouts newSchema) :=
  ⟨withBridgedV08Layouts_extends env newSchema hs hcoh,
    withBridgedV08Layouts_isLayoutCoherent env newSchema hdf⟩

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

end Anneal.CompilerQueryEnv
