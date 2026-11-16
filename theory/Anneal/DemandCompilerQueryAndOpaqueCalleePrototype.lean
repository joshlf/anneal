import Lean
import Trusted.Rustc.V2026_06_01.Layout
import Trusted.Rustc.V2026_06_01.MirAst.Types
import Trusted.Rustc.V2026_06_01.MirAst.Rvalues
import Trusted.Rustc.V2026_06_01.MirAst.Terminators
import Trusted.Rustc.V2026_06_01.MirAst.Body
import Trusted.Rustc.V2026_06_01.MirSemantics.Terminators
import Trusted.Rustc.V2026_06_01.MirSemantics.Machine
import Trusted.Rustc.V2026_08_01.Layout
import Trusted.Rustc.V2026_08_01.MirAst.Types
import Trusted.Rustc.V2026_08_01.MirAst.Body
import Trusted.Rustc.V2026_08_01.MirSemantics.Machine

/-!
# Demand-time compiler queries and the opaque callee table (Track P prototype)

Prototype for `ws-proto-demand-time-compiler-queries-and-opaque-callee-table`
(paired Track A workstream `ws-demand-time-compiler-queries-and-opaque-callee-table`).
Everything is stated over the real `Trusted.Rustc.V2026_06_01` / `V2026_08_01`
MIR, layout, and machine-state types.

* **Part A** (`bensherman` cl/1022361495, cl/1022375904): an `@[irreducible]`
  `OpaqueCalleeTable` backed by `List CapturedMir` whose `lookup` is *exactly*
  `Trusted.Rustc.V2026_06_01.MirSemantics.lookupCallee`
  (`opaqueCalleeTable_lookup_eq_trusted`), `O(1)` rewrite certificates
  (`lookupCallee_hit_mono`, `lookupCallee_hit`, `lookupCallee_trait_hit`,
  `lookupCallee_miss`), a literal-discriminant `switchInt` pruning step
  (`stepBranchPruned`) that is *equal* to the trusted `stepMirFn`
  (`stepBranchPruned_eq_trusted`), fuel-bounded runs
  (`evalWithOpaqueCallees_eq_evalWithListCallees`), and demanded-key call-cone
  narrowing (`evalWithOpaqueCallees_cone_narrow`) with dead-arm, polymorphic,
  trait-dispatch, and negative canaries.
* **Part B** (`proofs-rs/lean-miri#64`, `#65`, `AeneasVerif/charon#1611`): a
  finite-material, schema-versioned, demand-time `CompilerQueryEnv` with
  fail-closed `.unsupported` evidence gating (`query_schema12_unsupported_fallback`),
  monotonicity under `EnvExtends` (`query_mono_schema`), eager-catalog agreement
  (`layoutOf_agrees_with_eager`), V2026_08_01 → V2026_06_01 layout bridges, and an
  end-to-end `UnOp.vtableMethodLookup → abiCompatible → OpaqueCalleeTable.lookup →
  stepBranchPruned` dynamic-dispatch step preserved under both `EnvExtends` and
  call-cone narrowing.
* **Part C** (`tholenst` cl/1022563952): `DecidableEq` (never `BEq`) on every
  prototype key/query type, axiom-free manual `DecidableEq RigidTy`, `LawfulBEq`
  via `instBEqOfDecidableEq`, a worked shadowing demonstration, `#guard_msgs`
  axiom pins, and a bottom-of-file `run_cmd` axiom audit of every constant in this
  module.
-/

namespace Anneal.DemandCompilerQueryAndOpaqueCalleePrototype

open Trusted.Effect (FailureKind Outcome)
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## Part C (foundations): `DecidableEq` without `BEq` on real `Trusted` types

Every instance below is `DecidableEq` only. No `BEq` instance is derived or
registered for any type (the single `BEq` value, `ShadowingDemo.structuralBEq`,
exists only to demonstrate the hazard and is a `local instance` confined to one
section), so `a == b` always elaborates through `instBEqOfDecidableEq` and the core
`instLawfulBEq` applies (`beq_iff_eq`). -/

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
def decEqOfCtorIdxProto {α : Type} (idx : α → Nat) (ofIdx : Nat → α)
    (h : ∀ a, ofIdx (idx a) = a) : DecidableEq α := fun a b =>
  if hab : idx a = idx b then isTrue (by rw [← h a, hab, h b])
  else isFalse (fun e => hab (congrArg idx e))

/-- Left inverse of `AbiPassMode.ctorIdx`. -/
def abiPassModeOfIdxProto : Nat → AbiPassMode
  | 0 => .ignore | 1 => .direct | 2 => .pair | _ => .indirect

instance instDecidableEqAbiPassModeProto : DecidableEq AbiPassMode :=
  decEqOfCtorIdxProto AbiPassMode.ctorIdx abiPassModeOfIdxProto (fun a => by cases a <;> rfl)

/-- Left inverse of `UintTy.ctorIdx`. -/
def uintTyOfIdxProto : Nat → UintTy
  | 0 => .u8 | 1 => .u16 | 2 => .u32 | 3 => .u64 | 4 => .u128 | _ => .usize

instance instDecidableEqUintTyProto : DecidableEq UintTy :=
  decEqOfCtorIdxProto UintTy.ctorIdx uintTyOfIdxProto (fun a => by cases a <;> rfl)

/-- Left inverse of `IntTy.ctorIdx`. -/
def intTyOfIdxProto : Nat → IntTy
  | 0 => .i8 | 1 => .i16 | 2 => .i32 | 3 => .i64 | 4 => .i128 | _ => .isize

instance instDecidableEqIntTyProto : DecidableEq IntTy :=
  decEqOfCtorIdxProto IntTy.ctorIdx intTyOfIdxProto (fun a => by cases a <;> rfl)

/-- Left inverse of `FloatTy.ctorIdx`. -/
def floatTyOfIdxProto : Nat → FloatTy
  | 0 => .f16 | 1 => .f32 | 2 => .f64 | _ => .f128

instance instDecidableEqFloatTyProto : DecidableEq FloatTy :=
  decEqOfCtorIdxProto FloatTy.ctorIdx floatTyOfIdxProto (fun a => by cases a <;> rfl)

/-- Left inverse of `Mutability.ctorIdx`. -/
def mutabilityOfIdxProto : Nat → Mutability
  | 0 => .not | _ => .mut

instance instDecidableEqMutabilityProto : DecidableEq Mutability :=
  decEqOfCtorIdxProto Mutability.ctorIdx mutabilityOfIdxProto (fun a => by cases a <;> rfl)

/-- Left inverse of `Safety.ctorIdx`. -/
def safetyOfIdxProto : Nat → Safety
  | 0 => .safe | _ => .unsafe_

instance instDecidableEqSafetyProto : DecidableEq Safety :=
  decEqOfCtorIdxProto Safety.ctorIdx safetyOfIdxProto (fun a => by cases a <;> rfl)

/-- Left inverse of `UnOp.ctorIdx`. -/
def unOpOfIdxProto : Nat → UnOp
  | 0 => .not | 1 => .neg | _ => .ptrMetadata

instance instDecidableEqUnOpProto : DecidableEq UnOp :=
  decEqOfCtorIdxProto UnOp.ctorIdx unOpOfIdxProto (fun a => by cases a <;> rfl)

/-- Left inverse of `BinOp.ctorIdx`. -/
def binOpOfIdxProto : Nat → BinOp
  | 0 => .add | 1 => .addUnchecked | 2 => .addWithOverflow | 3 => .sub | 4 => .subUnchecked
  | 5 => .subWithOverflow | 6 => .mul | 7 => .mulUnchecked | 8 => .mulWithOverflow | 9 => .div
  | 10 => .rem | 11 => .bitXor | 12 => .bitAnd | 13 => .bitOr | 14 => .shl | 15 => .shlUnchecked
  | 16 => .shr | 17 => .shrUnchecked | 18 => .eq | 19 => .lt | 20 => .le | 21 => .ne | 22 => .ge
  | 23 => .gt | 24 => .cmp | _ => .offset

instance instDecidableEqBinOpProto : DecidableEq BinOp :=
  decEqOfCtorIdxProto BinOp.ctorIdx binOpOfIdxProto (fun a => by cases a <;> rfl)

/-- Left inverse of `RetagKind.ctorIdx`. -/
def retagKindOfIdxProto : Nat → RetagKind
  | 0 => .fnEntry | 1 => .twoPhase | 2 => .raw | _ => .default

instance instDecidableEqRetagKindProto : DecidableEq RetagKind :=
  decEqOfCtorIdxProto RetagKind.ctorIdx retagKindOfIdxProto (fun a => by cases a <;> rfl)

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
instance instDecidableEqRigidTyProto : DecidableEq RigidTy :=
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
instance instDecidableEqValueProto : DecidableEq Value :=
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

/-- `decide` evaluates `DecidableEq RigidTy` both on and off the constructor
diagonal (including at top level). -/
theorem rigidTy_decide_canary :
    RigidTy.bool ≠ RigidTy.uint .u32 ∧
      RigidTy.fnPtr [] .bool .safe .rust ≠ RigidTy.fnPtr [] (.uint .u32) .safe .rust ∧
      RigidTy.adt "a::B" [.bool, .array (.uint .u32) 3] = RigidTy.adt "a::B" [.bool, .array (.uint .u32) 3] ∧
      RigidTy.ref .not (.param 0 "T") ≠ RigidTy.ref .mut (.param 0 "T") := by
  decide

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
theorem listByteEq_sound_proto : ∀ (xs ys : List UInt8), listByteEq xs ys = true → xs = ys
  | [], [], _ => rfl
  | b₁ :: bs₁, b₂ :: bs₂, h => by
    unfold listByteEq at h
    cases hb : Nat.beq b₁.toBitVec.toNat b₂.toBitVec.toNat with
    | false => rw [hb] at h; nomatch h
    | true =>
      rw [hb] at h
      have hByte : b₁ = b₂ :=
        UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true hb))
      rw [hByte, listByteEq_sound_proto bs₁ bs₂ h]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

/-- Reflexivity of the trusted byte-wise `listByteEq`. -/
theorem listByteEq_refl_proto : ∀ (xs : List UInt8), listByteEq xs xs = true
  | [] => rfl
  | b :: bs => by simp [listByteEq, listByteEq_refl_proto bs]

/-- Trusted byte-wise `stringEq` is `DefPath` (string) equality. -/
theorem stringEq_eq_true_iff_proto {a b : String} : stringEq a b = true ↔ a = b := by
  constructor
  · intro h
    unfold stringEq at h
    exact String.toByteArray_inj.mp
      (ByteArray.ext (Array.toList_inj.mp (listByteEq_sound_proto _ _ h)))
  · rintro rfl
    unfold stringEq
    exact listByteEq_refl_proto _

/-- Trusted `stringEq` coincides with `decide (a = b)`. -/
theorem stringEq_eq_decide_proto (a b : String) : stringEq a b = decide (a = b) := by
  cases h : stringEq a b
  · have hne : ¬ a = b := fun hab => by
      rw [stringEq_eq_true_iff_proto.mpr hab] at h
      nomatch h
    simp [hne]
  · simp [stringEq_eq_true_iff_proto.mp h]

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
  simp [findCallee?, stringEq_eq_true_iff_proto.mpr h]

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
    · exact absurd (stringEq_eq_true_iff_proto.mp hs) h
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
    · exact absurd (stringEq_eq_true_iff_proto.mp hs) hoverride
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
    stringEq_eq_true_iff_proto.mpr hdefault
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

/-- `()` layout. -/
def protoUnitLayout : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory, fields := .arbitrary [] [],
    variants := .single 0, isUninhabited := false }

/-- `bool` layout. -/
def protoBoolLayout : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩, backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 1⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- `u32` layout (as computed by `RigidTy.computeLayout`). -/
def protoU32Layout : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 4294967295⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- Shared x86_64 layout table: `0 ↦ ()`, `1 ↦ bool`, `2 ↦ u32`. -/
def protoLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [protoUnitLayout, protoBoolLayout, protoU32Layout] }

/-- `bool` at layout index `1`. -/
def protoBoolTy : Ty := ⟨.bool, 1⟩

/-- `u32` at layout index `2`. -/
def protoU32Ty : Ty := ⟨.uint .u32, 2⟩

/-- `extern "Rust" fn() -> u32`. -/
def protoRetU32Abi : FnAbi :=
  { args := [], ret := ⟨protoU32Layout, .direct⟩, conv := .rust, canUnwind := true }

/-- `const v_u32`. -/
def protoU32Const (v : Nat) : Operand := .constant ⟨protoU32Ty, .scalar (.int ⟨v, 4⟩)⟩

/-- Literal `bool` constant operand. -/
def protoBoolConst (b : Bool) : Operand :=
  .constant ⟨protoBoolTy, .scalar (.int ⟨if b then 1 else 0, 1⟩)⟩

/-- Function-item operand `p::<tys>`. -/
def protoFnItem (p : DefPath) (tys : List RigidTy) : Operand :=
  .constant ⟨⟨.fnDef p tys, 0⟩, .zeroSized⟩

/-- Return place `_0`. -/
def protoRetPlace : Place := ⟨0, []⟩

/-- Captured leaf callee `fn() -> u32 { _0 = const v; return }`, generic over
`typeParams` (unused) type parameters and carrying `traitImpls`. -/
def protoLeaf (p : DefPath) (v : Nat) (typeParams : Nat) (traitImpls : List TraitImplEntry) :
    CapturedMir :=
  { defPath := p, phase := .runtimePostCleanup, role := .subject, argCount := 0,
    localDecls := [⟨.mut, protoU32Ty, some "_0"⟩],
    basicBlocks :=
      [⟨[⟨.assign protoRetPlace (.use (protoU32Const v)), "leaf:0"⟩], ⟨.return_, "leaf:1"⟩, false⟩],
    fnAbi := protoRetU32Abi, layouts := protoLayouts, allocations := [],
    typeParamCount := typeParams,
    genericParams := if typeParams = 0 then [] else [⟨0, "T"⟩],
    traitImpls := traitImpls }

/-- Call block `_0 = p::<tys>() -> target`. -/
def protoCallBlock (p : DefPath) (tys : List RigidTy) (target : BasicBlockIdx) : BasicBlockData :=
  ⟨[], ⟨.call (protoFnItem p tys) [] protoRetPlace (some target) .continue_, "call"⟩, false⟩

/-- Panicking callee `g_dead`: `fn() -> u32 { core::panicking::panic() }`. -/
def protoGDead : CapturedMir :=
  { defPath := "proto::g_dead", phase := .runtimePostCleanup, role := .subject, argCount := 0,
    localDecls := [⟨.mut, protoU32Ty, some "_0"⟩],
    basicBlocks :=
      [⟨[], ⟨.call (protoFnItem "core::panicking::panic" []) [] protoRetPlace none .continue_,
        "g_dead:0"⟩, false⟩],
    fnAbi := protoRetU32Abi, layouts := protoLayouts, allocations := [] }

/-- Live monomorphic callee. -/
def protoLiveF : CapturedMir := protoLeaf "proto::live_f" 7 0 []

/-- Unrelated captured callees padding the full table. -/
def protoFillerA : CapturedMir := protoLeaf "proto::filler_a" 1 0 []

/-- Unrelated captured callee padding the full table. -/
def protoFillerB : CapturedMir := protoLeaf "proto::filler_b" 2 0 []

/-- Root `fn() -> u32 { if LIT { _0 = live() } else { _0 = dead() } }`:
`bb0: switchInt(const LIT) -> [0: bb2, otherwise: bb1]`, `bb1: _0 = live() -> bb3`,
`bb2: _0 = dead() -> bb3`, `bb3: return`. -/
def protoLitIfRoot (lit : Bool) (liveP : DefPath) (liveTys : List RigidTy) (deadP : DefPath) :
    CapturedMir :=
  { defPath := "proto::root", phase := .runtimePostCleanup, role := .subject, argCount := 0,
    localDecls := [⟨.mut, protoU32Ty, some "_0"⟩],
    basicBlocks := [
      ⟨[], ⟨.switchInt (protoBoolConst lit) ⟨[(0, 2)], 1⟩, "root:if"⟩, false⟩,
      protoCallBlock liveP liveTys 3,
      protoCallBlock deadP [] 3,
      ⟨[], ⟨.return_, "root:ret"⟩, false⟩ ],
    fnAbi := protoRetU32Abi, layouts := protoLayouts, allocations := [] }

/-- Dead-arm canary root: `if true { live_f() } else { g_dead() }`. -/
def canaryRoot : CapturedMir := protoLitIfRoot true "proto::live_f" [] "proto::g_dead"

/-- Initial machine state of `canaryRoot`. -/
def canaryInit : MachineState := initMachineState canaryRoot []

/-- Full table (fillers, the panicking `g_dead`, and `live_f`). -/
def canaryFullTbl : OpaqueCalleeTable :=
  .ofList [protoFillerA, protoGDead, protoLiveF, protoFillerB]

/-- Narrowed table: `g_dead` (dead arm only) and fillers excluded. -/
def canaryNarrowTbl : OpaqueCalleeTable := .ofList [protoLiveF]

/-- Broken table: the live callee is missing. -/
def canaryBrokenTbl : OpaqueCalleeTable := .ofList [protoFillerA, protoGDead, protoFillerB]

/-- Key of the live call. -/
def canaryLiveKey : CalleeKey := ⟨protoLayouts, "proto::live_f", [], []⟩

/-- Only the live call is demanded: the dead arm's `g_dead` never is. -/
theorem canary_deadArm_demandedKeys :
    demandedKeys canaryFullTbl.lookup canaryRoot 8 canaryInit = [canaryLiveKey] := by
  decide +kernel

/-- Non-vacuity: the tables genuinely differ on `g_dead`. -/
theorem canary_deadArm_tables_differ :
    canaryFullTbl.lookup protoLayouts "proto::g_dead" [] [] = some protoGDead ∧
      canaryNarrowTbl.lookup protoLayouts "proto::g_dead" [] [] = none := by
  refine ⟨lookupCallee_hit_mono ?_ rfl, lookupCallee_miss_direct ?_⟩
  · unfold canaryFullTbl
    rw [lookupRaw_ofList_cons_miss (by decide)]
    exact lookupRaw_ofList_cons_hit rfl
  · unfold canaryNarrowTbl
    rw [lookupRaw_ofList_cons_miss (by decide), OpaqueCalleeTable.lookupRaw_eq,
      OpaqueCalleeTable.toList_ofList]
    rfl

/-- `live_f` resolves identically in both tables (`O(1)` certificates). -/
theorem canary_liveKey_agrees :
    canaryNarrowTbl.lookupKey canaryLiveKey = canaryFullTbl.lookupKey canaryLiveKey := by
  rw [OpaqueCalleeTable.lookupKey_eq, OpaqueCalleeTable.lookupKey_eq]
  simp only [canaryLiveKey]
  rw [lookupCallee_hit_mono (c := protoLiveF) ?_ rfl, lookupCallee_hit_mono (c := protoLiveF) ?_ rfl]
  · unfold canaryFullTbl
    rw [lookupRaw_ofList_cons_miss (by decide), lookupRaw_ofList_cons_miss (by decide)]
    exact lookupRaw_ofList_cons_hit rfl
  · exact lookupRaw_ofList_cons_hit rfl

/-- **Dead-arm cone canary**: dropping the panicking dead-arm callee `g_dead`
(and unrelated callees) leaves the run unchanged. -/
theorem canary_deadArm_cone_narrow :
    evalWithOpaqueCallees canaryNarrowTbl canaryRoot 8 canaryInit =
      evalWithOpaqueCallees canaryFullTbl canaryRoot 8 canaryInit := by
  apply evalWithOpaqueCallees_cone_narrow
  rw [canary_deadArm_demandedKeys]
  intro k hk
  simp only [List.mem_singleton] at hk
  subst hk
  exact canary_liveKey_agrees

/-- The canary genuinely executes: one branch event, then `live_f` returns `7`. -/
theorem canary_deadArm_halts :
    (evalWithOpaqueCallees canaryFullTbl canaryRoot 8 canaryInit).summary =
      ⟨.halted, [.event 1], some 7, none⟩ := by
  decide +kernel

/-- Initial state of `canaryRoot` with `canaryFullTbl.toList` linked in
`memory.callees` (`initMachineStateWithCallees`). -/
def canaryInitWithCallees : MachineState :=
  initMachineStateWithCallees canaryRoot [] canaryFullTbl.toList

/-- **Concrete instantiation of `evalWithOpaqueCallees_eq_trusted`**: when the
initial state links `canaryFullTbl.toList` in `memory.callees`, every visited
state along the run preserves `s'.memory.callees = canaryFullTbl.toList`, and
`evalWithOpaqueCallees` is *identical* to the iterated trusted `stepMirFn`. -/
theorem canary_evalWithOpaqueCallees_eq_trusted :
    evalWithOpaqueCallees canaryFullTbl canaryRoot 8 canaryInitWithCallees =
      runSteps (stepMirFn canaryRoot) 8 canaryInitWithCallees [] := by
  apply evalWithOpaqueCallees_eq_trusted
  decide +kernel

/-- Contrast: on `canaryInit` (`initMachineState`, where `memory.callees = []`),
the trusted `stepMirFn` halts at an external call to `proto::live_f`, whereas on
`canaryInitWithCallees` it halts normally returning `7`. -/
theorem canary_trusted_stepMirFn_requires_linked_callees :
    (runSteps (stepMirFn canaryRoot) 8 canaryInit []).summary =
      ⟨.external, [.event 1], none, some "proto::live_f"⟩ ∧
    (runSteps (stepMirFn canaryRoot) 8 canaryInitWithCallees []).summary =
      ⟨.halted, [.event 1], some 7, none⟩ := by
  decide +kernel

/-- Negative canary: dropping the *live* callee changes the outcome (the cone
hypothesis is necessary). -/
theorem canary_liveArm_required :
    (evalWithOpaqueCallees canaryBrokenTbl canaryRoot 8 canaryInit).summary =
      ⟨.external, [.event 1], none, some "proto::live_f"⟩ := by
  decide +kernel

/- Opacity witness: at default transparency `whnf` leaves opaque-table lookups
(`lookupRaw`, `lookup`), the per-table `traitImpls` certificate carrier, and the
`toList` seal stuck (no `O(|callees|)` `findCallee?` / `lookupCallee` /
`flatMapTraitImpls` unfolding); only an explicit `.all` transparency sees through
the seal. -/
open Lean Meta in
run_meta do
  let raw := mkApp2 (mkConst ``OpaqueCalleeTable.lookupRaw) (mkConst ``canaryFullTbl)
    (mkStrLit "proto::live_f")
  let full := mkApp5 (mkConst ``OpaqueCalleeTable.lookup) (mkConst ``canaryFullTbl)
    (mkConst ``protoLayouts) (mkStrLit "proto::live_f")
    (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``RigidTy))
    (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``TraitImplEntry))
  let impls := mkApp (mkConst ``OpaqueCalleeTable.traitImpls) (mkConst ``canaryFullTbl)
  let asList := mkApp (mkConst ``OpaqueCalleeTable.toList) (mkConst ``canaryFullTbl)
  for (e, head) in [(raw, ``OpaqueCalleeTable.lookupRaw), (full, ``OpaqueCalleeTable.lookup),
      (impls, ``OpaqueCalleeTable.traitImpls), (asList, ``OpaqueCalleeTable.toList)] do
    let r ← whnf e
    unless r.isAppOf head do
      throwError "opacity witness failed: whnf unfolded the opaque table to {r}"
    let r' ← withTransparency .all (whnf e)
    if r'.isAppOf head then
      throwError "opacity witness self-test failed: `.all` transparency did not unfold {e}"

/-! #### Multi-callee canary: polymorphic instantiation + `TraitImplEntry` dispatch -/

/-- `Self` type of the trait-dispatch canary. -/
def protoCircleTy : RigidTy := .adt "proto::Circle" []

/-- `impl Area for Circle` override entry for trait method `proto::Area::area`. -/
def protoAreaEntry : TraitImplEntry :=
  ⟨⟨"proto::Area::area", [protoCircleTy]⟩, "proto::<impl Area for Circle>::area"⟩

/-- Generic callee `fn poly<T>() -> u32` (instantiated via `CapturedMir.instantiate`). -/
def protoPoly : CapturedMir := protoLeaf "proto::poly" 9 1 []

/-- Override body `<Circle as Area>::area`. -/
def protoCircleArea : CapturedMir := protoLeaf "proto::<impl Area for Circle>::area" 31 0 []

/-- Captured `impl Area for Circle` block body carrying the `TraitImplEntry`; it is
never called, yet trait resolution reads its entry through `flatMapTraitImpls`. -/
def protoAreaImplHolder : CapturedMir := protoLeaf "proto::<impl Area for Circle>" 0 0 [protoAreaEntry]

/-- `if false { g_dead() } else { _0 = poly::<u32>(); _0 = <Circle as Area>::area() }`:
`bb0: switchInt(const false) -> [0: bb1, otherwise: bb4]`, `bb1: poly::<u32>() -> bb2`,
`bb2: Area::area::<Circle>() -> bb3`, `bb3: return`, `bb4: g_dead() -> bb3`. -/
def multiRoot : CapturedMir :=
  { defPath := "proto::root2", phase := .runtimePostCleanup, role := .subject, argCount := 0,
    localDecls := [⟨.mut, protoU32Ty, some "_0"⟩],
    basicBlocks := [
      ⟨[], ⟨.switchInt (protoBoolConst false) ⟨[(0, 1)], 4⟩, "root2:if"⟩, false⟩,
      protoCallBlock "proto::poly" [.uint .u32] 2,
      protoCallBlock "proto::Area::area" [protoCircleTy] 3,
      ⟨[], ⟨.return_, "root2:ret"⟩, false⟩,
      protoCallBlock "proto::g_dead" [] 3 ],
    fnAbi := protoRetU32Abi, layouts := protoLayouts, allocations := [] }

/-- Initial state of `multiRoot`. -/
def multiInit : MachineState := initMachineState multiRoot []

/-- Full table. -/
def multiFullTbl : OpaqueCalleeTable :=
  .ofList [protoFillerA, protoGDead, protoPoly, protoAreaImplHolder, protoFillerB, protoCircleArea]

/-- Demanded-key narrowing: keeps the `impl` block carrying the `TraitImplEntry`. -/
def multiNarrowTbl : OpaqueCalleeTable := .ofList [protoPoly, protoAreaImplHolder, protoCircleArea]

/-- Naive "executed `DefPath`s only" narrowing: drops the never-called `impl` block. -/
def multiNaiveTbl : OpaqueCalleeTable := .ofList [protoPoly, protoCircleArea]

/-- Key of the polymorphic call. -/
def multiPolyKey : CalleeKey := ⟨protoLayouts, "proto::poly", [.uint .u32], []⟩

/-- Key of the trait-method call. -/
def multiAreaKey : CalleeKey := ⟨protoLayouts, "proto::Area::area", [protoCircleTy], []⟩

/-- Exactly the polymorphic and trait-dispatch calls are demanded (not `g_dead`). -/
theorem canary_multi_demandedKeys :
    demandedKeys multiFullTbl.lookup multiRoot 12 multiInit = [multiPolyKey, multiAreaKey] := by
  decide +kernel

/-- The multi-callee run executes both live calls and returns `31`. -/
theorem canary_multi_halts :
    (evalWithOpaqueCallees multiFullTbl multiRoot 12 multiInit).summary =
      ⟨.halted, [.event 0], some 31, none⟩ := by
  decide +kernel

/-- `u32` instantiation layout certificate. -/
theorem canary_u32_instantiationLayouts :
    instantiationLayouts? protoLayouts [.uint .u32] = some [protoU32Layout] := by
  decide

/-- Polymorphic resolution certificate in a table. -/
theorem canary_poly_resolve (tbl : List CapturedMir)
    (h : resolveCalleeBodyAndArgs? tbl "proto::poly" [.uint .u32] [] = some (protoPoly, [.uint .u32])) :
    (OpaqueCalleeTable.ofList tbl).lookupKey multiPolyKey =
      some (protoPoly.instantiate ([RigidTy.uint .u32].zip [protoU32Layout])) := by
  rw [OpaqueCalleeTable.lookupKey_eq]
  exact lookupCallee_hit (by rw [OpaqueCalleeTable.toList_ofList]; exact h) rfl rfl
    canary_u32_instantiationLayouts

/-- The polymorphic key agrees across the full and narrowed tables (`O(1)`
`lookupCallee_hit_poly` certificates over `lookupRaw`, without unfolding
`resolveCalleeBodyAndArgs?` over the raw list). -/
theorem canary_multi_polyKey_agrees :
    multiNarrowTbl.lookupKey multiPolyKey = multiFullTbl.lookupKey multiPolyKey := by
  rw [OpaqueCalleeTable.lookupKey_eq, OpaqueCalleeTable.lookupKey_eq]
  simp only [multiPolyKey]
  rw [lookupCallee_hit_poly (c := protoPoly) (by decide) (by decide +kernel) ?_
      (by decide) rfl canary_u32_instantiationLayouts,
    lookupCallee_hit_poly (c := protoPoly) (by decide) (by decide +kernel) ?_
      (by decide) rfl canary_u32_instantiationLayouts]
  · unfold multiFullTbl
    rw [lookupRaw_ofList_cons_miss (by decide), lookupRaw_ofList_cons_miss (by decide)]
    exact lookupRaw_ofList_cons_hit rfl
  · exact lookupRaw_ofList_cons_hit rfl

/-- `impl Area for Circle` is the unique most-specific override in both tables. -/
theorem canary_area_winner_narrow :
    filterMostSpecificTraitImpls (traitMatches multiNarrowTbl [] "proto::Area::area" [protoCircleTy])
      (traitMatches multiNarrowTbl [] "proto::Area::area" [protoCircleTy]) =
        [(protoAreaEntry, some [])] := by
  decide +kernel

/-- Same winner in the full table. -/
theorem canary_area_winner_full :
    filterMostSpecificTraitImpls (traitMatches multiFullTbl [] "proto::Area::area" [protoCircleTy])
      (traitMatches multiFullTbl [] "proto::Area::area" [protoCircleTy]) =
        [(protoAreaEntry, some [])] := by
  decide +kernel

/-- The trait-dispatch key agrees across the full and narrowed tables
(`O(1)` `lookupCallee_trait_hit` certificates). -/
theorem canary_multi_areaKey_agrees :
    multiNarrowTbl.lookupKey multiAreaKey = multiFullTbl.lookupKey multiAreaKey := by
  rw [OpaqueCalleeTable.lookupKey_eq, OpaqueCalleeTable.lookupKey_eq]
  simp only [multiAreaKey]
  rw [lookupCallee_trait_hit (c := protoCircleArea) (by decide) canary_area_winner_narrow ?_
      (by decide) rfl,
    lookupCallee_trait_hit (c := protoCircleArea) (by decide) canary_area_winner_full ?_
      (by decide) rfl]
  · unfold multiFullTbl
    rw [lookupRaw_ofList_cons_miss (by decide), lookupRaw_ofList_cons_miss (by decide),
      lookupRaw_ofList_cons_miss (by decide), lookupRaw_ofList_cons_miss (by decide),
      lookupRaw_ofList_cons_miss (by decide)]
    exact lookupRaw_ofList_cons_hit rfl
  · unfold multiNarrowTbl
    rw [lookupRaw_ofList_cons_miss (by decide), lookupRaw_ofList_cons_miss (by decide)]
    exact lookupRaw_ofList_cons_hit rfl

/-- **Multi-callee cone canary** (polymorphic + trait dispatch, dead-arm `g_dead`
excluded). -/
theorem canary_multi_cone_narrow :
    evalWithOpaqueCallees multiNarrowTbl multiRoot 12 multiInit =
      evalWithOpaqueCallees multiFullTbl multiRoot 12 multiInit := by
  apply evalWithOpaqueCallees_cone_narrow
  rw [canary_multi_demandedKeys]
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact canary_multi_polyKey_agrees
  · exact canary_multi_areaKey_agrees

/-- **Soundness corner case**: narrowing to the *executed* `DefPath`s (every body
that runs is kept) still breaks trait dispatch, because the dropped, never-called
`impl` block contributed the `TraitImplEntry` via `flatMapTraitImpls`. Cone
narrowing must preserve demanded lookup *results*, not reachable `DefPath`s. -/
theorem canary_naiveNarrow_breaks_trait_dispatch :
    (evalWithOpaqueCallees multiNaiveTbl multiRoot 12 multiInit).summary =
      ⟨.external, [.event 0], none, some "proto::Area::area"⟩ := by
  decide +kernel

/-- Generic `impl<T> Area for Wrapper<T>` entry (`traitRef.args = [Wrapper<T>]`). -/
def protoWrapperGenericEntry : TraitImplEntry :=
  ⟨⟨"proto::Area::area", [.adt "proto::Wrapper" [.param 0 "T"]]⟩,
    "proto::<impl<T> Area for Wrapper<T>>::area"⟩

/-- Specialized `impl Area for Wrapper<u32>` entry (`traitRef.args = [Wrapper<u32>]`). -/
def protoWrapperU32Entry : TraitImplEntry :=
  ⟨⟨"proto::Area::area", [.adt "proto::Wrapper" [.uint .u32]]⟩,
    "proto::<impl Area for Wrapper<u32>>::area"⟩

/-- Explicit default-method inheritance entry `impl Area for Square` (`implPath = defPath`). -/
def protoSquareDefaultEntry : TraitImplEntry :=
  ⟨⟨"proto::Area::area", [.adt "proto::Square" []]⟩, "proto::Area::area"⟩

/-- Default trait method body `fn Area::area<Self>() -> u32 { 11 }` (`typeParamCount = 1`). -/
def protoDefaultArea : CapturedMir := protoLeaf "proto::Area::area" 11 1 []

/-- Generic override body `fn <impl<T> Area for Wrapper<T>>::area<T>() -> u32 { 22 }`. -/
def protoWrapperGenericArea : CapturedMir :=
  protoLeaf "proto::<impl<T> Area for Wrapper<T>>::area" 22 1 []

/-- Specialized monomorphic override body `fn <impl Area for Wrapper<u32>>::area() -> u32 { 33 }`. -/
def protoWrapperU32Area : CapturedMir :=
  protoLeaf "proto::<impl Area for Wrapper<u32>>::area" 33 0 []

/-- Opaque callee table with default trait method, generic override, and specialized override. -/
def protoSpecTbl : OpaqueCalleeTable :=
  .ofList [protoDefaultArea, protoWrapperGenericArea, protoWrapperU32Area]

/-- Registered `TraitImplEntry` records exercising specificity and default inheritance. -/
def protoSpecExtra : List TraitImplEntry :=
  [protoWrapperGenericEntry, protoWrapperU32Entry, protoSquareDefaultEntry]

/-- **Specificity, polymorphic override, and default-method inheritance canary**:
1. On `Wrapper<u32>`, both `impl<T> Area for Wrapper<T>` and `impl Area for Wrapper<u32>`
   match `traitMatches` (2 candidates), and `filterMostSpecificTraitImpls` selects the
   strictly more specific `Wrapper<u32>` override (`lookupCallee_trait_hit`).
2. On `Wrapper<bool>`, the generic `impl<T> Area for Wrapper<T>` wins and is instantiated
   at `T = bool` (`lookupCallee_trait_hit_poly`).
3. On `Square`, `protoSquareDefaultEntry` (`implPath = "proto::Area::area"`) inherits the
   default trait method body `protoDefaultArea` and instantiates `Self = Square`
   (`lookupCallee_trait_default_hit`). -/
theorem canary_trait_specificity_and_default_inheritance :
    (traitMatches protoSpecTbl protoSpecExtra "proto::Area::area"
        [.adt "proto::Wrapper" [.uint .u32]]).length = 2 ∧
    protoSpecTbl.lookup protoLayouts "proto::Area::area"
        [.adt "proto::Wrapper" [.uint .u32]] protoSpecExtra =
      some protoWrapperU32Area ∧
    protoSpecTbl.lookup protoLayouts "proto::Area::area"
        [.adt "proto::Wrapper" [.bool]] protoSpecExtra =
      some (protoWrapperGenericArea.instantiate [(.bool, protoBoolLayout)]) ∧
    protoSpecTbl.lookup protoLayouts "proto::Area::area"
        [.adt "proto::Square" []] protoSpecExtra =
      some (protoDefaultArea.instantiate [(.adt "proto::Square" [], protoUnitLayout)]) := by
  refine ⟨by decide +kernel, ?_, ?_, ?_⟩
  · apply lookupCallee_trait_hit (winner := protoWrapperU32Entry) (by decide) (by decide +kernel)
      ?_ (by decide) rfl
    unfold protoSpecTbl
    rw [lookupRaw_ofList_cons_miss (by decide), lookupRaw_ofList_cons_miss (by decide)]
    exact lookupRaw_ofList_cons_hit rfl
  · apply lookupCallee_trait_hit_poly (winner := protoWrapperGenericEntry) (implArgs := [.bool])
      (argLayouts := [protoBoolLayout]) (by decide) (by decide +kernel) ?_ (by decide) rfl rfl
      (by decide)
    unfold protoSpecTbl
    rw [lookupRaw_ofList_cons_miss (by decide)]
    exact lookupRaw_ofList_cons_hit rfl
  · apply lookupCallee_trait_default_hit (winner := protoSquareDefaultEntry) (implArgs := [.adt "proto::Square" []])
      (argLayouts := [protoUnitLayout]) (by decide) (by decide +kernel) rfl ?_ rfl (by decide)
    unfold protoSpecTbl
    exact lookupRaw_ofList_cons_hit rfl

/-- **Free generic certificate canary**: `proto::poly` has no `TraitImplEntry` in
`multiFullTbl` (which does register `impl Area for Circle`), so *one* per-`defPath`
certificate (`hno`) plus one raw certificate resolve both the concrete
instantiation `poly::<u32>` and a still-generic caller's `poly::<T>`
(`.param 0 "T"`, outside `lookupCallee_hit_poly`) to the instantiated body. -/
theorem canary_free_poly_param_and_concrete :
    multiFullTbl.lookup protoLayouts "proto::poly" [.uint .u32] [] =
      some (protoPoly.instantiate [(.uint .u32, protoU32Layout)]) ∧
    multiFullTbl.lookup protoLayouts "proto::poly" [.param 0 "T"] [] =
      some (protoPoly.instantiate [(.param 0 "T", protoUnitLayout)]) := by
  have hno : hasTraitImplForDefPath ([] ++ flatMapTraitImpls multiFullTbl.toList)
      "proto::poly" = false := by
    decide +kernel
  have hraw : multiFullTbl.lookupRaw "proto::poly" = some protoPoly := by
    unfold multiFullTbl
    rw [lookupRaw_ofList_cons_miss (by decide), lookupRaw_ofList_cons_miss (by decide)]
    exact lookupRaw_ofList_cons_hit rfl
  have hlayP : instantiationLayouts? protoLayouts [.param 0 "T"] = some [protoUnitLayout] := by
    decide
  exact ⟨lookupCallee_hit_free_poly hno hraw rfl canary_u32_instantiationLayouts,
    lookupCallee_hit_free_poly hno hraw rfl hlayP⟩

/-- One-time per-table `traitImpls` certificate for `multiFullTbl`: emitted once
for the table and reused across all free-generic and trait-method call sites without
ever unfolding `multiFullTbl.toList` again. -/
theorem multiFullTbl_traitImpls : multiFullTbl.traitImpls = [protoAreaEntry] := by
  unfold multiFullTbl
  rw [traitImpls_ofList]
  rfl

/-- **`tbl.toList`-free free-generic certificate canary**: reuses the per-table
`multiFullTbl_traitImpls` certificate (`multiFullTbl.traitImpls = [protoAreaEntry]`)
so `hno` checks only the 1-entry `TraitImplEntry` list `[protoAreaEntry]`
without ever unfolding `multiFullTbl.toList`. -/
theorem canary_free_poly_opaque_cert :
    multiFullTbl.lookup protoLayouts "proto::poly" [.uint .u32] [] =
      some (protoPoly.instantiate [(.uint .u32, protoU32Layout)]) ∧
    multiFullTbl.lookup protoLayouts "proto::poly" [.param 0 "T"] [] =
      some (protoPoly.instantiate [(.param 0 "T", protoUnitLayout)]) := by
  have hno : hasTraitImplForDefPath ([] ++ [protoAreaEntry]) "proto::poly" = false := by
    decide
  have hraw : multiFullTbl.lookupRaw "proto::poly" = some protoPoly := by
    unfold multiFullTbl
    rw [lookupRaw_ofList_cons_miss (by decide), lookupRaw_ofList_cons_miss (by decide)]
    exact lookupRaw_ofList_cons_hit rfl
  have hlayP : instantiationLayouts? protoLayouts [.param 0 "T"] = some [protoUnitLayout] := by
    decide
  exact ⟨lookupCallee_hit_free_poly_opaque multiFullTbl_traitImpls hno hraw rfl
      canary_u32_instantiationLayouts,
    lookupCallee_hit_free_poly_opaque multiFullTbl_traitImpls hno hraw rfl hlayP⟩

/-- **`tbl.toList`-free trait-dispatch certificate canary**: resolves
`<Circle as Area>::area` on `multiFullTbl` using *only* the one-time table
certificate `multiFullTbl_traitImpls`, `collectMatchingTraitImplsWith_cons_hit_mono`,
and the `O(1)` `lookupRaw` certificate for `protoCircleArea` — zero `tbl.toList`
unfolding and zero `decide +kernel` over the callee list. -/
theorem canary_trait_cert_no_toList :
    multiFullTbl.lookup protoLayouts "proto::Area::area" [protoCircleTy] [] =
      some protoCircleArea := by
  have himpl : multiFullTbl.lookupRaw "proto::<impl Area for Circle>::area" =
      some protoCircleArea := by
    unfold multiFullTbl
    rw [lookupRaw_ofList_cons_miss (by decide), lookupRaw_ofList_cons_miss (by decide),
      lookupRaw_ofList_cons_miss (by decide), lookupRaw_ofList_cons_miss (by decide),
      lookupRaw_ofList_cons_miss (by decide)]
    exact lookupRaw_ofList_cons_hit rfl
  have hcollect :
      collectMatchingTraitImplsWith multiFullTbl.lookupRaw ([] ++ [protoAreaEntry])
        "proto::Area::area" [protoCircleTy] [] = [(protoAreaEntry, some [])] := by
    rw [List.nil_append,
      collectMatchingTraitImplsWith_cons_hit_mono (c := protoCircleArea)
        (by decide) rfl (by decide) himpl (by decide) rfl]
    rfl
  exact lookupCallee_trait_hit_cert (winner := protoAreaEntry) (by decide)
    multiFullTbl_traitImpls hcollect (by decide) himpl (by decide) rfl

/-- One-time `traitImpls` certificate for `protoSpecTbl`. -/
theorem protoSpecTbl_traitImpls : protoSpecTbl.traitImpls = [] := by
  unfold protoSpecTbl
  rw [traitImpls_ofList]
  rfl

/-- **`tbl.toList`-free polymorphic & default-method trait-dispatch certificate canary**:
resolves both `<Wrapper<bool> as Area>::area` (polymorphic `TraitImplEntry` override)
and `<Square as Area>::area` (default trait method inheritance) on `protoSpecTbl`
using `lookupCallee_trait_hit_poly_cert`, `lookupCallee_trait_default_hit_cert`,
`collectMatchingTraitImplsWith_cons_hit_poly`,
`collectMatchingTraitImplsWith_cons_hit_default`, and `collectMatchingTraitImplsWith_cons_ne_args`
without ever unfolding `protoSpecTbl.toList`. -/
theorem canary_trait_poly_and_default_cert_no_toList :
    protoSpecTbl.lookup protoLayouts "proto::Area::area"
        [.adt "proto::Wrapper" [.bool]] protoSpecExtra =
      some (protoWrapperGenericArea.instantiate [(.bool, protoBoolLayout)]) ∧
    protoSpecTbl.lookup protoLayouts "proto::Area::area"
        [.adt "proto::Square" []] protoSpecExtra =
      some (protoDefaultArea.instantiate [(.adt "proto::Square" [], protoUnitLayout)]) := by
  have hdefRaw : protoSpecTbl.lookupRaw "proto::Area::area" = some protoDefaultArea := by
    unfold protoSpecTbl
    exact lookupRaw_ofList_cons_hit rfl
  have hgenRaw : protoSpecTbl.lookupRaw "proto::<impl<T> Area for Wrapper<T>>::area" =
      some protoWrapperGenericArea := by
    unfold protoSpecTbl
    rw [lookupRaw_ofList_cons_miss (by decide)]
    exact lookupRaw_ofList_cons_hit rfl
  have hcollectPoly :
      collectMatchingTraitImplsWith protoSpecTbl.lookupRaw (protoSpecExtra ++ [])
        "proto::Area::area" [.adt "proto::Wrapper" [.bool]] [] =
          [(protoWrapperGenericEntry, some [.bool])] := by
    unfold protoSpecExtra
    rw [List.append_nil,
      collectMatchingTraitImplsWith_cons_hit_poly (c := protoWrapperGenericArea)
        (subst := [(0, .bool)]) (methodTypeArgs := []) (implHeaderArgs := [.bool])
        (by decide) rfl (by decide) (by decide) hgenRaw (by decide) (by decide),
      collectMatchingTraitImplsWith_cons_ne_args (by decide) (by decide),
      collectMatchingTraitImplsWith_cons_ne_args (by decide) (by decide)]
    rfl
  have hcollectDef :
      collectMatchingTraitImplsWith protoSpecTbl.lookupRaw (protoSpecExtra ++ [])
        "proto::Area::area" [.adt "proto::Square" []] [] =
          [(protoSquareDefaultEntry, some [.adt "proto::Square" []])] := by
    unfold protoSpecExtra
    rw [List.append_nil,
      collectMatchingTraitImplsWith_cons_ne_args (by decide) (by decide),
      collectMatchingTraitImplsWith_cons_ne_args (by decide) (by decide),
      collectMatchingTraitImplsWith_cons_hit_default (c := protoDefaultArea)
        (subst := []) (methodTypeArgs := []) (implHeaderArgs := [])
        (by decide) rfl (by decide) (by decide) hdefRaw (by decide) (by decide)]
    rfl
  refine ⟨?_, ?_⟩
  · exact lookupCallee_trait_hit_poly_cert (winner := protoWrapperGenericEntry)
      (implArgs := [.bool]) (argLayouts := [protoBoolLayout])
      (by decide) protoSpecTbl_traitImpls hcollectPoly (by decide) hgenRaw
      (by decide) rfl rfl (by decide)
  · exact lookupCallee_trait_default_hit_cert (winner := protoSquareDefaultEntry)
      (implArgs := [.adt "proto::Square" []]) (argLayouts := [protoUnitLayout])
      (by decide) protoSpecTbl_traitImpls hcollectDef (by decide) rfl hdefRaw
      rfl (by decide)

/-! ## Part B: multi-version demand-time `CompilerQueryEnv` -/

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
`(superTraitRef, superVTableId)` for supertrait upcasting / chained method lookup. -/
structure VTableMethodEntry : Type where
  vtableId : Nat
  traitRef : TraitRef
  methods : List (DefPath × List RigidTy)
  supertraits : List (TraitRef × Nat) := []
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
  /-- `UnOp.vtableMethodLookup` (`charon#1611`). -/
  | vtableMethodLookup (vtableId : Nat) (traitRef : TraitRef) (slotIdx : Nat)
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

deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.Layout.Size
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.Layout.Align
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.Layout.WrappingRange
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.Layout.PrimitiveKind
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.Layout.ScalarLayout
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.Layout.FieldsShape
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.Layout.VariantsShape
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.Layout.BackendRepr
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.Layout.TypeLayout
deriving instance DecidableEq for Trusted.Rustc.V2026_08_01.Layout.LayoutTable


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

theorem get?_map_proto {α β : Type} (f : α → β) :
    ∀ (xs : List α) (idx : Nat), get? (xs.map f) idx = (get? xs idx).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, n + 1 => get?_map_proto f xs n

theorem lookupFieldLayouts_bridge (entries : List TypeLayout) :
    ∀ (idxs : List Nat),
      Trusted.Rustc.V2026_08_01.Layout.lookupFieldLayouts
          (entries.map bridgeTypeLayoutV06ToV08) idxs =
        (lookupFieldLayouts entries idxs).map (List.map bridgeTypeLayoutV06ToV08)
  | [] => rfl
  | idx :: rest => by
    simp only [Trusted.Rustc.V2026_08_01.Layout.lookupFieldLayouts, lookupFieldLayouts,
      get?_map_proto, lookupFieldLayouts_bridge entries rest]
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
    get?_map_proto bridgeTypeLayoutV06ToV08 tbl.entries ty.layoutIdx
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

/-- Exact bidirectional characterization of `evalLayoutOf` in the V2026_06_01 dialect
(A4: completes the `.ok` characterizations of B4's `_ok_iff` family for `layoutOf`):
the answer is `l` iff `computeLayoutV06` computes `l`. -/
theorem evalLayoutOf_v06_ok_iff (env : CompilerQueryEnv) (ty : Ty) (l : TypeLayout) :
    evalLayoutOf env .v2026_06_01 ty = .ok (.layout l) ↔
      computeLayoutV06 env.layoutsV06 ty = some l := by
  simp only [evalLayoutOf]
  cases computeLayoutV06 env.layoutsV06 ty with
  | none => simp
  | some l' => simp

/-- Exact bidirectional characterization of `evalLayoutOf` in the V2026_08_01 dialect
(A4): the answer is `l` iff the environment carries a V2026_08_01 table whose bridged
layout of `ty` is `l` (a missing table is `.unsupported`, never `.ok`). -/
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

/-- Demand-time `UnOp.vtableMethodLookup` (`charon#1611`). -/
def evalVTableMethodLookup (env : CompilerQueryEnv) (vtableId : Nat) (traitRef : TraitRef)
    (slotIdx : Nat) : QueryResult QueryAnswer :=
  match env.vtableEvidence? with
  | none => .unsupported .missingVTableEvidence
  | some vtables =>
    match vtables.find? (fun e => decide (e.vtableId = vtableId)) with
    | none => .err (.vtableNotFound vtableId)
    | some e =>
      if e.traitRef = traitRef then
        match e.methods[slotIdx]? with
        | some (p, tys) => .ok (.method p tys)
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

/-- Exact bidirectional characterization of `evalVTableMethodLookup ... = .ok (.method p tys)`. -/
theorem evalVTableMethodLookup_ok_iff (env : CompilerQueryEnv) (vtableId : Nat)
    (traitRef : TraitRef) (slotIdx : Nat) (p : DefPath) (tys : List RigidTy) :
    evalVTableMethodLookup env vtableId traitRef slotIdx = .ok (.method p tys) ↔
      ∃ vtables e, env.vtableEvidence? = some vtables ∧
        vtables.find? (fun x => decide (x.vtableId = vtableId)) = some e ∧
        e.traitRef = traitRef ∧ e.methods[slotIdx]? = some (p, tys) := by
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
            injection h with ha
            injection ha with hp htys
            subst hp; subst htys
            exact ⟨vtables, e, rfl, hf, ht, hm⟩
        · simp only [ht, ite_false] at h
          nomatch h
  · rintro ⟨vtables, e, hv, hf, ht, hm⟩
    simp only [hv, hf, ht, ite_true, hm]

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
  | .vtableMethodLookup vtableId traitRef slotIdx => evalVTableMethodLookup env vtableId traitRef slotIdx
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
  | vtableMethodLookup vtableId traitRef slotIdx =>
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
  | vtableMethodLookup vtableId traitRef slotIdx =>
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

/-- **Negative coherence canary**: if a decoder populates an incoherent V2026_08_01
`LayoutTable` (`pointerBits = 32` while `layoutsV06.pointerBits = 64`),
`isLayoutCoherent` is `false` and `.v2026_08_01` `layoutOf` disagrees with
`.v2026_06_01` `layoutOf` on `&u32` (`4` bytes vs. `8` bytes). -/
theorem incoherence_breaks_dialect_agreement_canary :
    let badEnv : CompilerQueryEnv :=
      { schema := .v2026_08_01
        layoutsV06 := protoLayouts
        layoutsV08 := some { bridgeLayoutV06ToV08 protoLayouts with pointerBits := 32 }
        fnAbis := [], cfiTags := none, syncRegions := none, vtables := none }
    let refU32 : Ty := ⟨.ref .not (.uint .u32), 0⟩
    badEnv.isLayoutCoherent = false ∧
      evalCompilerQuery badEnv (.layoutOf .v2026_06_01 refU32) ≠
        evalCompilerQuery badEnv (.layoutOf .v2026_08_01 refU32) ∧
      (badEnv.withBridgedV08Layouts .v2026_08_01).isLayoutCoherent = true ∧
      evalCompilerQuery (badEnv.withBridgedV08Layouts .v2026_08_01) (.layoutOf .v2026_06_01 refU32) =
        evalCompilerQuery (badEnv.withBridgedV08Layouts .v2026_08_01) (.layoutOf .v2026_08_01 refU32) := by
  decide

/-- **Negative `EnvExtends` coherence canary**: when `env₁` is a `v2026_06_01`
environment (`env₁.v08Layouts? = none`, so `env₁.isLayoutCoherent = true` vacuously),
plain `EnvExtends env₁ env₂` only requires `OptionExtends none env₂.v08Layouts?`
(`True`) and therefore allows upgrading `env₁` to an *incoherent* `v2026_08_01`
environment `env₂` (`env₂.isLayoutCoherent = false`) whose V08 `layoutOf` answer
disagrees with `env₁`'s V06 `layoutOf` answer. -/
theorem envExtends_allows_incoherent_v08_upgrade_canary :
    let env₁ : CompilerQueryEnv :=
      { schema := .v2026_06_01
        layoutsV06 := protoLayouts
        layoutsV08 := none
        fnAbis := [], cfiTags := none, syncRegions := none, vtables := none }
    let env₂ : CompilerQueryEnv :=
      { schema := .v2026_08_01
        layoutsV06 := protoLayouts
        layoutsV08 := some { bridgeLayoutV06ToV08 protoLayouts with pointerBits := 32 }
        fnAbis := [], cfiTags := none, syncRegions := none, vtables := none }
    let refU32 : Ty := ⟨.ref .not (.uint .u32), 0⟩
    env₁.isLayoutCoherent = true ∧
      EnvExtends env₁ env₂ ∧
      env₂.isLayoutCoherent = false ∧
      evalCompilerQuery env₂ (.layoutOf .v2026_08_01 refU32) ≠
        evalCompilerQuery env₁ (.layoutOf .v2026_06_01 refU32) := by
  refine ⟨by decide, ?_, by decide, by decide⟩
  exact ⟨by decide, rfl, (fun _ h => nomatch h), rfl, (fun _ h => nomatch h),
    (fun _ h => nomatch h), (fun _ h => nomatch h)⟩

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

/-- The alternative "schema-triggered" CFI semantics (CFI auto-checked whenever
`env.schema = .schema13`, even if the query did not request it). -/
def evalAbiAutoCfi (env : CompilerQueryEnv) (callerAbi : FnAbi) (callee : DefPath)
    (cfiCallSite : Option RigidTy) : QueryResult QueryAnswer :=
  match cfiCallSite, env.schema.hasSchema13 with
  | none, false => abiCore env callerAbi callee
  | site, _ =>
    match env.cfiEvidence? with
    | none => .unsupported .missingCfiEvidence
    | some spec =>
      match lookupDefPathAssoc spec.calleeTypeIds callee,
          lookupTyAssoc spec.callSiteTypeIds (site.getD (.fnPtr [] (.uint .u32) .safe .rust)) with
      | some a, some b => if a = b then abiCore env callerAbi callee else .err .cfiTypeIdMismatch
      | none, _ => .err (.cfiCalleeUntagged callee)
      | _, none => .err .cfiCallSiteUntagged

/-- Design-rationale environment (Schema 12). -/
def autoCfiEnv₁ : CompilerQueryEnv :=
  { schema := .v2026_06_01, layoutsV06 := protoLayouts, layoutsV08 := none,
    fnAbis := [("proto::f", protoRetU32Abi)], cfiTags := none, syncRegions := none,
    vtables := none }

/-- Its Schema-13 extension with CFI evidence that does not tag `proto::f`. -/
def autoCfiEnv₂ : CompilerQueryEnv :=
  { autoCfiEnv₁ with schema := .schema13, cfiTags := some ⟨[], []⟩ }

/-- **Why the CFI demand is part of the query key**: schema-triggered CFI checking
breaks monotonicity (a supported Schema-12 answer changes after a sound
upgrade), while `evalAbiCompatible` (CFI only when requested) satisfies
`query_mono_schema`. -/
theorem autoCfi_breaks_mono :
    EnvExtends autoCfiEnv₁ autoCfiEnv₂ ∧
      evalAbiAutoCfi autoCfiEnv₁ protoRetU32Abi "proto::f" none = .ok .abiOk ∧
      evalAbiAutoCfi autoCfiEnv₂ protoRetU32Abi "proto::f" none =
        .err (.cfiCalleeUntagged "proto::f") ∧
      evalCompilerQuery autoCfiEnv₂ (.abiCompatible protoRetU32Abi "proto::f" none) =
        evalCompilerQuery autoCfiEnv₁ (.abiCompatible protoRetU32Abi "proto::f" none) := by
  refine ⟨⟨by decide, rfl, OptionExtends.refl _, rfl, (fun _ h => nomatch h),
    OptionExtends.refl _, OptionExtends.refl _⟩, by decide, by decide, by decide⟩

/-! ### Part B canaries -/

/-- Schema-V2026_08_01 environment whose V08 material is the bridged V06 table. -/
def bridgeEnv : CompilerQueryEnv :=
  { schema := .v2026_08_01, layoutsV06 := protoLayouts,
    layoutsV08 := some (bridgeLayoutV06ToV08 protoLayouts), fnAbis := [], cfiTags := none,
    syncRegions := none, vtables := none }

/-- Cross-dialect agreement: V2026_06_01 and (bridged) V2026_08_01
`RigidTy.computeLayout` agree on scalar, aggregate, array, and pointer types. -/
theorem layoutOf_dialects_agree_canary :
    [protoU32Ty, protoBoolTy, (⟨.tuple [.bool, .uint .u32], 0⟩ : Ty), ⟨.array (.uint .u32) 3, 0⟩,
        ⟨.ref .not (.uint .u32), 0⟩, ⟨.ref .mut .str, 0⟩, ⟨.int .i64, 0⟩, ⟨.float .f64, 0⟩].all
      (fun ty => evalCompilerQuery bridgeEnv (.layoutOf .v2026_06_01 ty) ==
        evalCompilerQuery bridgeEnv (.layoutOf .v2026_08_01 ty)) = true := by
  decide

/-- `(bool, u32)` has size 8 / align 4 with fields at offsets 0 and 4; a V08
`layoutOf` under a V2026_06_01 producer fails closed. -/
theorem layoutOf_canary :
    (match evalCompilerQuery bridgeEnv (.layoutOf .v2026_06_01 ⟨.tuple [.bool, .uint .u32], 0⟩) with
      | .ok (.layout l) => some (l.size.bytes, l.align.bytes, l.fields)
      | _ => none) = some (8, 4, .arbitrary [⟨0⟩, ⟨4⟩] [0, 1]) ∧
    evalCompilerQuery { bridgeEnv with schema := .v2026_06_01 } (.layoutOf .v2026_08_01 protoU32Ty) =
      .unsupported .missingV08LayoutDialect ∧
    evalCompilerQuery bridgeEnv (.layoutOf .v2026_06_01 ⟨.str, 7⟩) = .err .layoutUncomputable := by
  decide

/-- ABI mismatch canaries (each a schema-independent `.err`). -/
theorem abiCompatible_canary :
    evalCompilerQuery autoCfiEnv₁ (.abiCompatible protoRetU32Abi "proto::f" none) = .ok .abiOk ∧
    evalCompilerQuery autoCfiEnv₁ (.abiCompatible { protoRetU32Abi with conv := .c } "proto::f" none) =
      .err .callConvMismatch ∧
    evalCompilerQuery autoCfiEnv₁
        (.abiCompatible { protoRetU32Abi with args := [⟨protoU32Layout, .direct⟩] } "proto::f" none) =
      .err .argCountMismatch ∧
    evalCompilerQuery autoCfiEnv₁
        (.abiCompatible { protoRetU32Abi with ret := ⟨protoBoolLayout, .direct⟩ } "proto::f" none) =
      .err .retAbiMismatch ∧
    evalCompilerQuery autoCfiEnv₁
        (.abiCompatible { protoRetU32Abi with canUnwind := false } "proto::f" none) =
      .err .unwindMismatch ∧
    evalCompilerQuery autoCfiEnv₁ (.abiCompatible protoRetU32Abi "proto::nope" none) =
      .err (.unknownCalleeAbi "proto::nope") := by
  decide

/-- Schema-13 environment with CFI type ids. -/
def cfiEnv : CompilerQueryEnv :=
  { autoCfiEnv₁ with
    schema := .schema13
    cfiTags := some ⟨[("proto::f", 42)], [(.fnPtr [] (.uint .u32) .safe .rust, 42),
      (.fnPtr [.bool] (.uint .u32) .safe .rust, 7)]⟩ }

/-- CFI canaries: matching type ids pass, mismatches are the CFI trap, and Schema
12 fails closed. -/
theorem cfi_canary :
    evalCompilerQuery cfiEnv (.abiCompatible protoRetU32Abi "proto::f"
      (some (.fnPtr [] (.uint .u32) .safe .rust))) = .ok .abiOk ∧
    evalCompilerQuery cfiEnv (.abiCompatible protoRetU32Abi "proto::f"
      (some (.fnPtr [.bool] (.uint .u32) .safe .rust))) = .err .cfiTypeIdMismatch ∧
    evalCompilerQuery cfiEnv (.abiCompatible protoRetU32Abi "proto::f"
      (some (.fnPtr [] .bool .safe .rust))) = .err .cfiCallSiteUntagged ∧
    evalCompilerQuery autoCfiEnv₁ (.abiCompatible protoRetU32Abi "proto::f"
      (some (.fnPtr [] (.uint .u32) .safe .rust))) = .unsupported .missingCfiEvidence := by
  decide

/-! ## End-to-end: `UnOp.vtableMethodLookup → abiCompatible → OpaqueCalleeTable.lookup → stepBranchPruned` -/

/-- `charon#1611` `UnOp.vtableMethodLookup traitRef slotIdx` with optional
supertrait vtable chain (`supertraitChain`). When `supertraitChain = []`, looks
up method `slotIdx` directly in `traitRef`'s vtable; when
`supertraitChain = [subTrait, ...]`, first walks supertrait vtable pointers
along `supertraitChain → traitRef` before looking up `slotIdx`. -/
structure VTableMethodLookupOp : Type where
  traitRef : TraitRef
  slotIdx : Nat
  supertraitChain : List TraitRef := []
  deriving DecidableEq

/-- Prototype unary operators: the trusted `UnOp` plus `charon#1611`'s demand-time
`vtableMethodLookup`. -/
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
    | [] => some (.vtableMethodLookup vtablePtr.allocId op.traitRef op.slotIdx)
    | curTrait :: rest =>
      some (.vtableSupertraitLookup vtablePtr.allocId curTrait (rest.headD op.traitRef))

/-- Walk a chain of `UnOp.vtableMethodLookup` supertrait vtable hops starting
at `vtId` before looking up method slot `slotIdx` on the final `traitRef`. Every
hop is one application of the `UnOp.vtableMethodLookup` operator to the current
vtable pointer: the query evaluated at each hop is exactly the one
`UnOpExt.query?` issues for the remaining chain (as in `charon#1611`, where each
supertrait hop and the final method read are separate `UnOp::VTableMethodLookup`
operations on the vtable pointer the previous one returned). -/
def resolveVTableChain (env : CompilerQueryEnv) (traitRef : TraitRef) (slotIdx : Nat) :
    List TraitRef → Nat → QueryResult (DefPath × List RigidTy)
  | [], vtId =>
    match (UnOpExt.vtableMethodLookup ⟨traitRef, slotIdx, []⟩).query? ⟨vtId, 0⟩ with
    | none => .err .answerKindMismatch
    | some q =>
      match evalCompilerQuery env q with
      | .ok (.method p tys) => .ok (p, tys)
      | .ok _ => .err .answerKindMismatch
      | .err e => .err e
      | .unsupported m => .unsupported m
  | curTrait :: restChain, vtId =>
    match (UnOpExt.vtableMethodLookup ⟨traitRef, slotIdx, curTrait :: restChain⟩).query?
        ⟨vtId, 0⟩ with
    | none => .err .answerKindMismatch
    | some q =>
      match evalCompilerQuery env q with
      | .ok (.supertraitVTable nextVtId) =>
        resolveVTableChain env traitRef slotIdx restChain nextVtId
      | .ok _ => .err .answerKindMismatch
      | .err e => .err e
      | .unsupported m => .unsupported m

/-- `resolveVTableChain` is monotone under `EnvExtends` for any supertrait chain. -/
theorem resolveVTableChain_mono {env₁ env₂ : CompilerQueryEnv} (h : EnvExtends env₁ env₂)
    (traitRef : TraitRef) (slotIdx : Nat) :
    ∀ (chain : List TraitRef) (vtId : Nat),
      (∀ m, resolveVTableChain env₁ traitRef slotIdx chain vtId ≠ .unsupported m) →
        resolveVTableChain env₂ traitRef slotIdx chain vtId =
          resolveVTableChain env₁ traitRef slotIdx chain vtId
  | [], vtId, hsup => by
    unfold resolveVTableChain at hsup ⊢
    simp only [UnOpExt.query?] at hsup ⊢
    generalize hq : CompilerQuery.vtableMethodLookup vtId traitRef slotIdx = q at hsup ⊢
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
        exact resolveVTableChain_mono h traitRef slotIdx restChain nextVtId hsup
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
  deriving DecidableEq

/-- The receiver's runtime vtable pointer at `s`: local `site.vtableLocal` of the
active frame must hold an initialized pointer (otherwise the `dyn` call is UB). -/
def DynCallSite.vtablePtr? (site : DynCallSite) (s : MachineState) : Option ProvenancePtr :=
  match get? s.frame.locals site.vtableLocal with
  | some (.init (.ptr p _)) => some p
  | _ => none

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
the called method's is never the right slot: the site's `slotIdx` does not belong
to the method in its call key. -/
def implementsCalledMethod (calledMethod target : DefPath) : Bool :=
  decide (lastPathSegment calledMethod = lastPathSegment target)

/-- Whether `calledMethod` is a method item of `traitDefPath` (`calledMethod =
traitDefPath ++ "::" ++ lastPathSegment calledMethod` with a non-empty method
segment). Without this check, a site for `<dyn Area as OtherTrait>::area` paired
with an `Area` vtable lookup passes both A3's `DynCallSite.wellFormed` and
`implementsCalledMethod` (because both end in `::area`!) and executes `Area::area`
for an `OtherTrait::area` call (`canary_dyn_wrong_trait_prefix_fails_closed`). -/
def methodMatchesTrait (calledMethod traitDefPath : DefPath) : Bool :=
  let seg := lastPathSegment calledMethod
  !seg.isEmpty &&
    decide (calledMethod.toByteArray.data.toList =
      traitDefPath.toByteArray.data.toList ++ [(58 : UInt8), (58 : UInt8)] ++ seg)

/-- A `dyn` call site is well formed when:
1. its call key is a virtual call whose receiver type `dyn D` names the trait of
   the *first* vtable the lookup reads (`d = firstTrait.defPath` and
   `firstTrait.args.head? = some (.dynamic d)`),
2. the call key's full generic argument list `site.dynKey.2` equals
   `.dynamic d :: site.lookupOp.traitRef.args.tail` (`Self = dyn D` followed by
   the terminal trait's generic parameters, supporting generic supertraits
   `<dyn Sub as Conv<u32>>::conv` while rejecting mismatched generic parameters;
   `canary_dyn_trait_arg_mismatch_fails_closed`, `canary_dyn_generic_supertrait_chain`),
3. the terminal trait reference `site.lookupOp.traitRef.args` is non-empty, and
4. `site.dynKey.1` is a method of the terminal trait `site.lookupOp.traitRef.defPath`
   (`methodMatchesTrait site.dynKey.1 site.lookupOp.traitRef.defPath`;
   `canary_dyn_wrong_trait_prefix_fails_closed`). -/
def DynCallSite.wellFormed (site : DynCallSite) : Bool :=
  let firstTrait := site.lookupOp.supertraitChain.headD site.lookupOp.traitRef
  match dynSelfTrait? site.dynKey with
  | some d =>
    decide (d = firstTrait.defPath) &&
      decide (firstTrait.args.head? = some (.dynamic d)) &&
      decide (site.dynKey.2 = .dynamic d :: site.lookupOp.traitRef.args.tail) &&
      !site.lookupOp.traitRef.args.isEmpty &&
      methodMatchesTrait site.dynKey.1 site.lookupOp.traitRef.defPath
  | none => false

/-- Resolve a `dyn` call through the runtime vtable pointer `vtablePtr`:
`resolveVTableChain` (direct or supertrait-chained `UnOp.vtableMethodLookup`),
then `abiCompatible`. -/
def resolveDynTarget (env : CompilerQueryEnv) (site : DynCallSite) (vtablePtr : ProvenancePtr) :
    QueryResult (DefPath × List RigidTy) :=
  match resolveVTableChain env site.lookupOp.traitRef site.lookupOp.slotIdx
      site.lookupOp.supertraitChain vtablePtr.allocId with
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

/-- **Unified dynamic-dispatch step**: receiver vtable pointer (read from the
calling frame) `→ UnOp.vtableMethodLookup → abiCompatible →
OpaqueCalleeTable.lookup → stepBranchPruned`. An ill-formed site (call key not a
virtual call on the first vtable's trait) fails closed (`MirStepNode.unsupported`:
a configuration error, never attributed to the program), a receiver without a
vtable pointer is UB, missing evidence fails closed, a CFI type-id mismatch is the
defined CFI trap (`abort`), and every other semantic error is UB. A resolved slot
whose target does not implement the called method (`implementsCalledMethod`: the
site's slot index belongs to another method) also fails closed. -/
def dynDispatchStep (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable) (site : DynCallSite)
    (body : CapturedMir) (s : MachineState) : MirStepNode :=
  if site.wellFormed then
    match site.vtablePtr? s with
    | none => MirStepNode.fail .ub
    | some vt =>
      match resolveDynTarget env site vt with
      | .ok target =>
        if implementsCalledMethod site.dynKey.1 target.1 then
          stepBranchPruned (redirectResolver tbl site.dynKey target) body s
        else MirStepNode.unsupported
      | .err .cfiTypeIdMismatch => MirStepNode.retOutcome .abort
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
      site.lookupOp.supertraitChain vt.allocId with
  | unsupported m => exact absurd (by simp [hv]) (hsup m)
  | err e =>
    rw [resolveVTableChain_mono h _ _ _ _ (by simp [hv]), hv]
  | ok pt =>
    rcases pt with ⟨p, tys⟩
    rw [resolveVTableChain_mono h _ _ _ _ (by simp [hv]), hv]
    rw [hv] at hsup
    dsimp only at hsup ⊢
    cases hb : evalCompilerQuery env₁ (.abiCompatible site.callerAbi p site.cfiCallSite) with
    | unsupported m => exact absurd (by simp [hb]) (hsup m)
    | err e => rw [query_mono_schema h _ (by simp [hb]), hb]
    | ok b => rw [query_mono_schema h _ (by simp [hb]), hb]

/-- The dynamic-dispatch step on a resolved receiver is a branch-pruned step. -/
theorem dynDispatchStep_eq_of_resolved {env : CompilerQueryEnv} {tbl : OpaqueCalleeTable}
    {site : DynCallSite} {body : CapturedMir} {s : MachineState} {vt : ProvenancePtr}
    {target : DefPath × List RigidTy} (hwf : site.wellFormed = true)
    (hvt : site.vtablePtr? s = some vt)
    (h : resolveDynTarget env site vt = .ok target)
    (hname : implementsCalledMethod site.dynKey.1 target.1 = true) :
    dynDispatchStep env tbl site body s =
      stepBranchPruned (redirectResolver tbl site.dynKey target) body s := by
  simp only [dynDispatchStep, hwf, ite_true, hvt, h, hname]

/-- An ill-formed site fails closed at every state, whatever the environment,
table, or receiver. -/
theorem dynDispatchStep_of_not_wellFormed (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    {site : DynCallSite} (body : CapturedMir) (s : MachineState)
    (hwf : site.wellFormed = false) :
    dynDispatchStep env tbl site body s = MirStepNode.unsupported := by
  simp only [dynDispatchStep, hwf, Bool.false_eq_true, ite_false]

/-- A resolved vtable slot whose target item name does not match the called method
fails closed (`MirStepNode.unsupported`), whatever the callee table holds. -/
theorem dynDispatchStep_of_method_mismatch (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    {site : DynCallSite} (body : CapturedMir) (s : MachineState) {vt : ProvenancePtr}
    {target : DefPath × List RigidTy} (hwf : site.wellFormed = true)
    (hvt : site.vtablePtr? s = some vt)
    (hr : resolveDynTarget env site vt = .ok target)
    (hname : implementsCalledMethod site.dynKey.1 target.1 = false) :
    dynDispatchStep env tbl site body s = MirStepNode.unsupported := by
  simp only [dynDispatchStep, hwf, ite_true, hvt, hr, hname, Bool.false_eq_true, ite_false]

/-- Preservation under `EnvExtends` (supportedness is only required of the
receiver vtable pointer actually present at `s`). -/
theorem dynDispatchStep_envExtends {env₁ env₂ : CompilerQueryEnv} (h : EnvExtends env₁ env₂)
    (tbl : OpaqueCalleeTable) (site : DynCallSite) (body : CapturedMir) (s : MachineState)
    (hsup : ∀ vt, site.vtablePtr? s = some vt → ∀ m, resolveDynTarget env₁ site vt ≠ .unsupported m) :
    dynDispatchStep env₂ tbl site body s = dynDispatchStep env₁ tbl site body s := by
  unfold dynDispatchStep
  cases hwf : site.wellFormed with
  | false => rfl
  | true =>
    simp only [ite_true]
    cases hvt : site.vtablePtr? s with
    | none => rfl
    | some vt => simp only [resolveDynTarget_mono h site vt (hsup vt hvt)]

/-- Preservation under call-cone narrowing. -/
theorem dynDispatchStep_cone_narrow (env : CompilerQueryEnv)
    (narrowTbl fullTbl : OpaqueCalleeTable) (site : DynCallSite) (body : CapturedMir)
    (s : MachineState)
    (hcone : ∀ vt target, site.vtablePtr? s = some vt → resolveDynTarget env site vt = .ok target →
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
        cases hn : implementsCalledMethod site.dynKey.1 target.1 with
        | false => rfl
        | true => exact stepBranchPruned_congr body s (hcone vt target hvt hr)
      | err e => cases e <;> rfl
      | unsupported m => rfl

/-- **End-to-end integration theorem**: the dynamic-dispatch step is preserved
simultaneously under a sound environment extension and call-cone narrowing. -/
theorem dynDispatchStep_preserved {env₁ env₂ : CompilerQueryEnv}
    {narrowTbl fullTbl : OpaqueCalleeTable} {site : DynCallSite} {body : CapturedMir}
    {s : MachineState} (h : EnvExtends env₁ env₂)
    (hsup : ∀ vt, site.vtablePtr? s = some vt → ∀ m, resolveDynTarget env₁ site vt ≠ .unsupported m)
    (hcone : ∀ vt target, site.vtablePtr? s = some vt → resolveDynTarget env₁ site vt = .ok target →
      ∀ k, demandedKey? body s = some k →
        k.apply (redirectResolver narrowTbl site.dynKey target) =
          k.apply (redirectResolver fullTbl site.dynKey target)) :
    dynDispatchStep env₂ narrowTbl site body s = dynDispatchStep env₁ fullTbl site body s := by
  rw [dynDispatchStep_envExtends h narrowTbl site body s hsup]
  exact dynDispatchStep_cone_narrow env₁ narrowTbl fullTbl site body s hcone

/-! ### End-to-end canary -/

/-- `Area` trait reference with `Self = dyn Area`. -/
def dynTraitRef : TraitRef := ⟨"proto::Area", [.dynamic "proto::Area"]⟩

/-- `*const ()` (receiver vtable pointers; layout index `0`). -/
def protoVtPtrTy : Ty := ⟨.rawPtr .not (.tuple []), 0⟩

/-- The `dyn Area` call site (receiver vtable pointer in local `_1`, slot `0`, not
CFI-instrumented). -/
def dynSite : DynCallSite :=
  { vtableLocal := 1, lookupOp := ⟨dynTraitRef, 0, []⟩, callerAbi := protoRetU32Abi,
    cfiCallSite := none, dynKey := ("proto::Area::area", [.dynamic "proto::Area"]) }

/-- `fn(vt: *const ()) -> u32 { if true { <dyn Area>::area() } else { g_dead() } }`. -/
def dynRoot : CapturedMir :=
  { protoLitIfRoot true "proto::Area::area" [.dynamic "proto::Area"] "proto::g_dead" with
    argCount := 1, localDecls := [⟨.mut, protoU32Ty, some "_0"⟩, ⟨.not, protoVtPtrTy, some "vt"⟩] }

/-- Initial state of `dynRoot`, called with a `Circle` receiver (vtable `7`). -/
def dynInit : MachineState := initMachineState dynRoot [.ptr ⟨7, 0⟩ 0]

/-- State at the live `dyn` call (after the literal switch). -/
def dynAtCall : MachineState :=
  { dynInit with frame := { blockIdx := 1, stmtIdx := 0, locals := dynInit.frame.locals } }

/-- `dynAtCall` is not hand-made: it is exactly the state the pruned literal
switch reaches from `dynInit` (after emitting branch event `1`), under any
resolver. -/
theorem dynAtCall_reached (r : CalleeResolver) :
    viewStepNode (stepBranchPruned r dynRoot dynInit) = .cont (some (.event 1)) (.running dynAtCall) :=
  rfl

/-- The receiver's vtable pointer at the call is read from the frame: vtable `7`. -/
theorem dyn_vtablePtr_atCall : dynSite.vtablePtr? dynAtCall = some ⟨7, 0⟩ := rfl

/-- `dynSite` is well formed: its call key `<dyn Area as Area>::area` is a virtual
call on `Area`, the trait of the receiver's vtable. -/
theorem dynSite_wellFormed : dynSite.wellFormed = true := by decide

/-- Schema-12 environment (no vtable evidence). -/
def dynEnv12 : CompilerQueryEnv :=
  { schema := .v2026_08_01, layoutsV06 := protoLayouts,
    layoutsV08 := some (bridgeLayoutV06ToV08 protoLayouts),
    fnAbis := [("proto::<impl Area for Circle>::area", protoRetU32Abi),
      ("proto::<impl Area for Square>::area", protoRetU32Abi)],
    cfiTags := none, syncRegions := none, vtables := none }

/-- Schema-13 extension with vtable evidence (`7 ↦ Circle`, `9 ↦ Square`). -/
def dynEnv13 : CompilerQueryEnv :=
  { dynEnv12 with
    schema := .schema13
    vtables := some [⟨7, dynTraitRef, [("proto::<impl Area for Circle>::area", [])], []⟩,
      ⟨9, dynTraitRef, [("proto::<impl Area for Square>::area", [])], []⟩] }

/-- A further extension populating sync-storage regions. -/
def dynEnv13Sync : CompilerQueryEnv := { dynEnv13 with syncRegions := some [⟨3, 4, 8⟩] }

/-- `impl Area for Square { fn area() -> u32 { 44 } }`. -/
def protoSquareArea : CapturedMir := protoLeaf "proto::<impl Area for Square>::area" 44 0 []

/-- Full and narrowed tables for the `dyn` canary. -/
def dynFullTbl : OpaqueCalleeTable :=
  .ofList [protoFillerA, protoGDead, protoCircleArea, protoSquareArea, protoFillerB]

/-- Narrowed `dyn` table. -/
def dynNarrowTbl : OpaqueCalleeTable := .ofList [protoCircleArea]

/-- Schema 12 fails closed on the `dyn` call. -/
theorem dyn_schema12_unsupported :
    resolveDynTarget dynEnv12 dynSite ⟨7, 0⟩ = .unsupported .missingVTableEvidence := by decide

/-- Schema 13 dispatches the `Circle` receiver to `<Circle as Area>::area`. -/
theorem dyn_schema13_resolves :
    resolveDynTarget dynEnv13 dynSite ⟨7, 0⟩ = .ok ("proto::<impl Area for Circle>::area", []) := by
  decide

theorem dyn_envExtends_12_13 : EnvExtends dynEnv12 dynEnv13 :=
  ⟨by decide, rfl, OptionExtends.refl _, rfl, OptionExtends.refl _, OptionExtends.refl _,
    (fun _ h => nomatch h)⟩

theorem dyn_envExtends_13_sync : EnvExtends dynEnv13 dynEnv13Sync :=
  ⟨by decide, rfl, OptionExtends.refl _, rfl, OptionExtends.refl _, (fun _ h => nomatch h),
    OptionExtends.refl _⟩

/-- `DefPath` of the active callee after a continuing step. -/
def StepView.activeCalleePath? : StepView → Option DefPath
  | .cont _ (.running s') => s'.memory.activeCallee.map (·.defPath)
  | _ => none

/-- The Schema-13 dynamic-dispatch step enters `<Circle as Area>::area`. -/
theorem dyn_step_enters_impl :
    (viewStepNode (dynDispatchStep dynEnv13 dynFullTbl dynSite dynRoot dynAtCall)).activeCalleePath? =
      some "proto::<impl Area for Circle>::area" := by
  decide +kernel

/-- The Schema-12 dynamic-dispatch step is the fail-closed `unsupported` node. -/
theorem dyn_step_schema12_fails_closed :
    dynDispatchStep dynEnv12 dynFullTbl dynSite dynRoot dynAtCall = MirStepNode.unsupported := by
  simp only [dynDispatchStep, dynSite_wellFormed, ite_true, dyn_vtablePtr_atCall,
    dyn_schema12_unsupported]

/-- A `dyn` call whose receiver local holds no pointer is UB (fail-closed: no
vtable lookup, no call). -/
theorem dyn_step_missing_receiver_ub :
    dynDispatchStep dynEnv13 dynFullTbl { dynSite with vtableLocal := 0 } dynRoot dynAtCall =
      MirStepNode.fail .ub :=
  rfl

/-- The live `dyn` call is the only demanded key at the call state. -/
theorem dyn_demandedKey :
    demandedKey? dynRoot dynAtCall =
      some ⟨protoLayouts, "proto::Area::area", [.dynamic "proto::Area"], []⟩ := by
  decide +kernel

/-- **End-to-end canary**: the Schema-13 dynamic-dispatch step is preserved when the
environment is further extended (sync regions) *and* the callee table is narrowed
to the dispatched method (dropping the dead-arm `g_dead`, `Square`, and fillers). -/
theorem dyn_step_preserved :
    dynDispatchStep dynEnv13Sync dynNarrowTbl dynSite dynRoot dynAtCall =
      dynDispatchStep dynEnv13 dynFullTbl dynSite dynRoot dynAtCall := by
  apply dynDispatchStep_preserved dyn_envExtends_13_sync
  · intro vt hvt
    rw [dyn_vtablePtr_atCall] at hvt
    cases hvt
    rw [dyn_schema13_resolves]
    exact fun _ h => nomatch h
  · intro vt target hvt ht k hk
    rw [dyn_vtablePtr_atCall] at hvt
    cases hvt
    rw [dyn_schema13_resolves] at ht
    cases ht
    rw [dyn_demandedKey] at hk
    cases hk
    simp only [CalleeKey.apply, redirectResolver, dynSite, ite_true]
    rw [lookupCallee_hit_mono (c := protoCircleArea) ?_ rfl,
      lookupCallee_hit_mono (c := protoCircleArea) ?_ rfl]
    · unfold dynFullTbl
      rw [lookupRaw_ofList_cons_miss (by decide), lookupRaw_ofList_cons_miss (by decide)]
      exact lookupRaw_ofList_cons_hit rfl
    · exact lookupRaw_ofList_cons_hit rfl

/-- Monotonicity canary: Schema-13-only answers appear after the upgrade, while
supported Schema-12 answers are unchanged; vtable errors are exact. -/
theorem query_mono_canary :
    evalCompilerQuery dynEnv12 (.vtableMethodLookup 7 dynTraitRef 0) =
      .unsupported .missingVTableEvidence ∧
    evalCompilerQuery dynEnv13 (.vtableMethodLookup 7 dynTraitRef 0) =
      .ok (.method "proto::<impl Area for Circle>::area" []) ∧
    evalCompilerQuery dynEnv13
        (.abiCompatible protoRetU32Abi "proto::<impl Area for Circle>::area" none) =
      evalCompilerQuery dynEnv12
        (.abiCompatible protoRetU32Abi "proto::<impl Area for Circle>::area" none) ∧
    evalCompilerQuery dynEnv13 (.vtableMethodLookup 7 dynTraitRef 1) =
      .err (.vtableSlotOutOfBounds 1) ∧
    evalCompilerQuery dynEnv13 (.vtableMethodLookup 7 ⟨"proto::Other", []⟩ 0) =
      .err .vtableTraitMismatch ∧
    evalCompilerQuery dynEnv13 (.vtableMethodLookup 8 dynTraitRef 0) = .err (.vtableNotFound 8) := by
  decide

/-- Sync-storage guard canaries over region `[4, 12)` of allocation `3` (plus a
zero-byte region `[6, 6)` at offset `6`, which never blocks a spanning access). -/
theorem syncStorageGuard_canary :
    evalCompilerQuery dynEnv13Sync (.syncStorageGuard 3 6 1) =
      .err (.syncStorageOverlap ⟨3, 4, 8⟩) ∧
    evalCompilerQuery dynEnv13Sync (.syncStorageGuard 3 2 4) =
      .err (.syncStorageOverlap ⟨3, 4, 8⟩) ∧
    evalCompilerQuery dynEnv13Sync (.syncStorageGuard 3 0 4) = .ok .syncPermit ∧
    evalCompilerQuery dynEnv13Sync (.syncStorageGuard 3 12 4) = .ok .syncPermit ∧
    evalCompilerQuery dynEnv13Sync (.syncStorageGuard 4 6 1) = .ok .syncPermit ∧
    evalCompilerQuery { dynEnv13 with syncRegions := some [⟨3, 6, 0⟩] }
        (.syncStorageGuard 3 0 12) = .ok .syncPermit ∧
    evalCompilerQuery dynEnv13 (.syncStorageGuard 3 6 1) = .unsupported .missingSyncStorage := by
  decide

/-- Schema-gated `EnvExtends` canary: a Schema-12 environment whose raw `vtables`
field holds ignored garbage still extends cleanly to `dynEnv13` (`EnvExtends`),
and `query_mono_schema` preserves its supported answers. -/
theorem envExtends_schema12_ignored_fields_canary :
    let noisy12 : CompilerQueryEnv :=
      { dynEnv12 with vtables := some [⟨999, ⟨"proto::Noise", []⟩, [], []⟩] }
    EnvExtends noisy12 dynEnv13 ∧
      evalCompilerQuery noisy12 (.vtableMethodLookup 7 dynTraitRef 0) =
        .unsupported .missingVTableEvidence ∧
      evalCompilerQuery dynEnv13
          (.abiCompatible protoRetU32Abi "proto::<impl Area for Circle>::area" none) =
        evalCompilerQuery noisy12
          (.abiCompatible protoRetU32Abi "proto::<impl Area for Circle>::area" none) := by
  refine ⟨⟨by decide, rfl, OptionExtends.refl _, rfl, OptionExtends.refl _, OptionExtends.refl _,
    (fun _ h => nomatch h)⟩, by decide, by decide⟩

/-- A CFI-instrumented `dyn` call whose call-site type id mismatches is the
defined CFI trap (`abort`), not UB and not a call. -/
theorem dyn_cfi_trap :
    dynDispatchStep { dynEnv13 with cfiTags := some ⟨[("proto::<impl Area for Circle>::area", 1)],
        [(.fnPtr [] (.uint .u32) .safe .rust, 2)]⟩ } dynFullTbl
      { dynSite with cfiCallSite := some (.fnPtr [] (.uint .u32) .safe .rust) } dynRoot dynAtCall =
      MirStepNode.retOutcome .abort := by
  rfl

/-! ### Demand-gated dynamic dispatch -/

/-- Whether the next step at `s` demands the `dyn` call site `site.dynKey`. -/
def demandsDynSite (site : DynCallSite) (body : CapturedMir) (s : MachineState) : Bool :=
  match demandedKey? body s with
  | some k => decide ((k.defPath, k.typeArgs) = site.dynKey)
  | none => false

/-- Whether the next step at `s` demands a *virtual* call key (first generic argument
`dyn D`) other than `site.dynKey`: a `dyn` call no registered site resolves. -/
def demandsUnregisteredDyn (site : DynCallSite) (body : CapturedMir) (s : MachineState) : Bool :=
  match demandedKey? body s with
  | some k =>
    (dynSelfTrait? (k.defPath, k.typeArgs)).isSome && !decide ((k.defPath, k.typeArgs) = site.dynKey)
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
    (hnd : demandsDynSite site body s = false) :
    stepBranchPruned (redirectResolver tbl site.dynKey target) body s =
      stepBranchPruned tbl.lookup body s := by
  apply stepBranchPruned_congr
  intro k hk
  have hne : ¬ (k.defPath, k.typeArgs) = site.dynKey := by
    intro he
    simp only [demandsDynSite, hk, he, decide_true, Bool.true_eq_false] at hnd
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
    (hname : implementsCalledMethod site.dynKey.1 target.1 = true)
    (hu : demandsUnregisteredDyn site body s = false) :
    dynDemandStep env tbl site body s = dynDispatchStep env tbl site body s := by
  unfold dynDemandStep
  cases hd : demandsDynSite site body s with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, ite_false, hu]
    rw [dynDispatchStep_eq_of_resolved hwf hvt hr hname,
      stepBranchPruned_redirect_of_not_demanded tbl site body s target hd]

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
    unfold demandsDynSite
    cases hk : demandedKey? body s with
    | none => rfl
    | some k =>
      rw [hk] at hu
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hu
      exact decide_eq_false hu.2
  simp only [dynDemandStep, hnd, hu, Bool.false_eq_true, ite_false, ite_true]

/-- Fuel-bounded multi-step evaluation with demand-gated dynamic dispatch. -/
def evalDynWithOpaqueCallees (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    (site : DynCallSite) (body : CapturedMir) (fuel : Nat) (s : MachineState) : RunResult :=
  runSteps (dynDemandStep env tbl site body) fuel s []

/-- Per-state side conditions under which one demand-gated step is preserved by
`EnvExtends env₁ env₂` and narrowing `fullTbl` to `narrowTbl`. -/
structure DynStepPreserved (env₁ : CompilerQueryEnv) (narrowTbl fullTbl : OpaqueCalleeTable)
    (site : DynCallSite) (body : CapturedMir) (s : MachineState) : Prop where
  /-- A demanded `dyn` call's query is supported by `env₁`. -/
  supported : demandsDynSite site body s = true → ∀ vt, site.vtablePtr? s = some vt →
    ∀ m, resolveDynTarget env₁ site vt ≠ .unsupported m
  /-- A demanded `dyn` call's redirected key agrees across the tables. -/
  dynCone : demandsDynSite site body s = true → ∀ vt target, site.vtablePtr? s = some vt →
    resolveDynTarget env₁ site vt = .ok target → ∀ k, demandedKey? body s = some k →
      k.apply (redirectResolver narrowTbl site.dynKey target) =
        k.apply (redirectResolver fullTbl site.dynKey target)
  /-- Any other demanded key agrees across the tables. -/
  cone : demandsDynSite site body s = false → ∀ k, demandedKey? body s = some k →
    narrowTbl.lookupKey k = fullTbl.lookupKey k

/-- Single-step preservation of `dynDemandStep` under `EnvExtends` (supportedness
is only needed when `demandsDynSite site body s = true`) and call-cone narrowing. -/
theorem dynDemandStep_preserved {env₁ env₂ : CompilerQueryEnv}
    {narrowTbl fullTbl : OpaqueCalleeTable} {site : DynCallSite} {body : CapturedMir}
    {s : MachineState} (h : EnvExtends env₁ env₂)
    (hp : DynStepPreserved env₁ narrowTbl fullTbl site body s) :
    dynDemandStep env₂ narrowTbl site body s = dynDemandStep env₁ fullTbl site body s := by
  unfold dynDemandStep
  cases hd : demandsDynSite site body s with
  | true =>
    simp only [ite_true]
    exact dynDispatchStep_preserved h (hp.supported hd) (hp.dynCone hd)
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    cases hu : demandsUnregisteredDyn site body s with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      exact stepBranchPruned_congr body s (hp.cone hd)

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
kernel evaluation along the run). -/
def dynStepPreservedB (env₁ : CompilerQueryEnv) (narrowTbl fullTbl : OpaqueCalleeTable)
    (site : DynCallSite) (body : CapturedMir) (s : MachineState) : Bool :=
  match demandedKey? body s with
  | none => true
  | some k =>
    if (k.defPath, k.typeArgs) = site.dynKey then
      match site.vtablePtr? s with
      | none => true
      | some vt =>
        match resolveDynTarget env₁ site vt with
        | .ok target =>
          decide (k.apply (redirectResolver narrowTbl site.dynKey target) =
            k.apply (redirectResolver fullTbl site.dynKey target))
        | .err _ => true
        | .unsupported _ => false
    else decide (narrowTbl.lookupKey k = fullTbl.lookupKey k)

/-- The decidable certificate is sound. -/
theorem dynStepPreserved_of_check {env₁ : CompilerQueryEnv} {narrowTbl fullTbl : OpaqueCalleeTable}
    {site : DynCallSite} {body : CapturedMir} {s : MachineState}
    (hc : dynStepPreservedB env₁ narrowTbl fullTbl site body s = true) :
    DynStepPreserved env₁ narrowTbl fullTbl site body s := by
  unfold dynStepPreservedB at hc
  cases hk : demandedKey? body s with
  | none =>
    refine ⟨fun hd => ?_, fun hd => ?_, fun _ k hk' => ?_⟩
    · simp [demandsDynSite, hk] at hd
    · simp [demandsDynSite, hk] at hd
    · rw [hk] at hk'
      exact nomatch hk'
  | some k =>
    rw [hk] at hc
    dsimp only at hc
    by_cases he : (k.defPath, k.typeArgs) = site.dynKey
    · rw [ite_eq_left_of_eq_true _ _ (eq_true he)] at hc
      refine ⟨fun _ vt hvt m hm => ?_, fun _ vt target hvt hr k' hk' => ?_, fun hd => ?_⟩
      · simp only [hvt, hm, Bool.false_eq_true] at hc
      · rw [hk] at hk'
        cases hk'
        simp only [hvt, hr, decide_eq_true_eq] at hc
        exact hc
      · simp [demandsDynSite, hk, he] at hd
    · rw [ite_eq_right_of_eq_false _ _ (eq_false he)] at hc
      refine ⟨fun hd => ?_, fun hd => ?_, fun _ k' hk' => ?_⟩
      · simp [demandsDynSite, hk, he] at hd
      · simp [demandsDynSite, hk, he] at hd
      · rw [hk] at hk'
        cases hk'
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

/-- **Full multi-step end-to-end dynamic-dispatch canary (Schema 13)**: starting
from `dynInit` (`bb0: if true { <dyn Area>::area() } else { g_dead() }`),
`evalDynWithOpaqueCallees` prunes the dead branch `g_dead`, reads the receiver's
vtable pointer, resolves `UnOp.vtableMethodLookup` + `abiCompatible` on demand at
`bb1`, enters `<Circle as Area>::area` in the narrowed opaque table, and halts
returning `31`; the narrowed/extended run equals the full run by the narrow-run
multi-step theorem (`runVisited` steps only `dynNarrowTbl`). -/
theorem canary_dyn_e2e_full_run_schema13 :
    (evalDynWithOpaqueCallees dynEnv13 dynNarrowTbl dynSite dynRoot 12 dynInit).summary =
      ⟨.halted, [.event 1], some 31, none⟩ ∧
    evalDynWithOpaqueCallees dynEnv13Sync dynNarrowTbl dynSite dynRoot 12 dynInit =
      evalDynWithOpaqueCallees dynEnv13 dynFullTbl dynSite dynRoot 12 dynInit :=
  ⟨by decide +kernel,
    evalDynWithOpaqueCallees_preserved_of_narrow_check dyn_envExtends_13_sync 12 dynInit
      (by decide +kernel)⟩

/-- `if false { <dyn Area>::area() } else { live_f() }`: the `dyn Area` call is on
the dead literal-`false` branch, while the live branch calls `live_f`. -/
def dynDeadBranchRoot : CapturedMir :=
  { defPath := "proto::dyn_dead_root", phase := .runtimePostCleanup, role := .subject, argCount := 0,
    localDecls := [⟨.mut, protoU32Ty, some "_0"⟩],
    basicBlocks := [
      ⟨[], ⟨.switchInt (protoBoolConst false) ⟨[(0, 2)], 1⟩, "root:if"⟩, false⟩,
      protoCallBlock "proto::Area::area" [.dynamic "proto::Area"] 3,
      protoCallBlock "proto::live_f" [] 3,
      ⟨[], ⟨.return_, "root:ret"⟩, false⟩ ],
    fnAbi := protoRetU32Abi, layouts := protoLayouts, allocations := [] }

/-- Initial state of `dynDeadBranchRoot`. -/
def dynDeadBranchInit : MachineState := initMachineState dynDeadBranchRoot []

/-- **Synergy canary (Dead-Branch Pruning + Demand-Time Schema-12 Queries)**:
when `<dyn Area>::area()` lies in the dead arm of `if false`, `evalDynWithOpaqueCallees`
under Schema 12 (`dynEnv12`, which lacks Schema-13 vtable evidence!) never
demands `vtableMethodLookup` and executes the live branch `live_f()` to `.halted 7`
on the narrowed `[protoLiveF]` table; preservation across `dynEnv12 → dynEnv13` and
`canaryNarrowTbl ↔ canaryFullTbl` is proved through
`evalDynWithOpaqueCallees_preserved_of_narrow_check`. -/
theorem canary_dyn_deadBranch_schema12_succeeds :
    (evalDynWithOpaqueCallees dynEnv12 canaryNarrowTbl dynSite
        dynDeadBranchRoot 12 dynDeadBranchInit).summary =
      ⟨.halted, [.event 0], some 7, none⟩ ∧
    evalDynWithOpaqueCallees dynEnv12 canaryNarrowTbl dynSite
        dynDeadBranchRoot 12 dynDeadBranchInit =
      evalDynWithOpaqueCallees dynEnv13 canaryFullTbl dynSite
        dynDeadBranchRoot 12 dynDeadBranchInit := by
  refine ⟨by decide +kernel, ?_⟩
  have h1 :
      evalDynWithOpaqueCallees dynEnv13 canaryNarrowTbl dynSite
          dynDeadBranchRoot 12 dynDeadBranchInit =
        evalDynWithOpaqueCallees dynEnv12 canaryNarrowTbl dynSite
          dynDeadBranchRoot 12 dynDeadBranchInit :=
    evalDynWithOpaqueCallees_preserved_of_narrow_check
      dyn_envExtends_12_13 12 dynDeadBranchInit (by decide +kernel)
  have h2 :
      evalDynWithOpaqueCallees dynEnv13 canaryNarrowTbl dynSite
          dynDeadBranchRoot 12 dynDeadBranchInit =
        evalDynWithOpaqueCallees dynEnv13 canaryFullTbl dynSite
          dynDeadBranchRoot 12 dynDeadBranchInit :=
    evalDynWithOpaqueCallees_preserved_of_narrow_check
      (EnvExtends.refl dynEnv13) 12 dynDeadBranchInit (by decide +kernel)
  exact h1.symm.trans h2

/-! ### Receiver-driven dispatch: one call key, two receivers -/

/-- `fn(vt_circle, vt_square: *const ()) -> u32`: the *same* `dyn Area` call key is
reached twice with different receivers in one run
(`bb0: StorageLive(vt); vt = copy vt_circle; _0 = <dyn Area>::area() -> bb1`,
`bb1: vt = copy vt_square; _0 = <dyn Area>::area() -> bb2`, `bb2: return`). -/
def dyn2Root : CapturedMir :=
  { defPath := "proto::dyn_two_receivers", phase := .runtimePostCleanup, role := .subject,
    argCount := 2,
    localDecls := [⟨.mut, protoU32Ty, some "_0"⟩, ⟨.not, protoVtPtrTy, some "vt_circle"⟩,
      ⟨.not, protoVtPtrTy, some "vt_square"⟩, ⟨.mut, protoVtPtrTy, some "vt"⟩],
    basicBlocks := [
      ⟨[⟨.storageLive 3, "dyn2:live"⟩, ⟨.assign ⟨3, []⟩ (.use (.copy ⟨1, []⟩)), "dyn2:vt0"⟩],
        ⟨.call (protoFnItem "proto::Area::area" [.dynamic "proto::Area"]) [] protoRetPlace
          (some 1) .continue_, "dyn2:call0"⟩, false⟩,
      ⟨[⟨.assign ⟨3, []⟩ (.use (.copy ⟨2, []⟩)), "dyn2:vt1"⟩],
        ⟨.call (protoFnItem "proto::Area::area" [.dynamic "proto::Area"]) [] protoRetPlace
          (some 2) .continue_, "dyn2:call1"⟩, false⟩,
      ⟨[], ⟨.return_, "dyn2:ret"⟩, false⟩ ],
    fnAbi := protoRetU32Abi, layouts := protoLayouts, allocations := [] }

/-- `dyn2Root` called with a `Circle` receiver (vtable `7`) and a `Square` receiver
(vtable `9`). -/
def dyn2Init : MachineState := initMachineState dyn2Root [.ptr ⟨7, 0⟩ 0, .ptr ⟨9, 0⟩ 0]

/-- The two-receiver call site reads the receiver vtable pointer from local `vt` (`_3`). -/
def dyn2Site : DynCallSite := { dynSite with vtableLocal := 3 }

/-- Narrowed table holding exactly the two dispatched `impl` bodies. -/
def dyn2NarrowTbl : OpaqueCalleeTable := .ofList [protoCircleArea, protoSquareArea]

/-- **Receiver-driven dispatch canary**: in one Schema-13 run the same `dyn Area`
call key is reached with a `Circle` receiver and then a `Square` receiver; the
vtable pointer read from the frame at each call dispatches to the right `impl`, so
the run returns `44` (`Square`'s area, from the last call). Reading a fixed
receiver (`vtableLocal := 1`, as a receiver-independent site would) wrongly sends
both calls to `Circle` (`31`), and Schema 12 fails closed at the first `dyn` call. -/
theorem canary_dyn_two_receivers :
    (evalDynWithOpaqueCallees dynEnv13 dynFullTbl dyn2Site dyn2Root 16 dyn2Init).summary =
      ⟨.halted, [], some 44, none⟩ ∧
    (evalDynWithOpaqueCallees dynEnv13 dynFullTbl { dyn2Site with vtableLocal := 1 } dyn2Root 16
        dyn2Init).summary = ⟨.halted, [], some 31, none⟩ ∧
    evalDynWithOpaqueCallees dynEnv12 dynFullTbl dyn2Site dyn2Root 16 dyn2Init =
      .faulted .unsupported [] := by
  decide +kernel

/-- **Multi-step preservation on the two-receiver run**: the whole run under the
further-extended environment and the two-`impl` narrowed table equals the full
run, by `evalDynWithOpaqueCallees_preserved_of_narrow_check` (`runVisited` steps
only `dyn2NarrowTbl`). -/
theorem canary_dyn_two_receivers_preserved :
    evalDynWithOpaqueCallees dynEnv13Sync dyn2NarrowTbl dyn2Site dyn2Root 16 dyn2Init =
      evalDynWithOpaqueCallees dynEnv13 dynFullTbl dyn2Site dyn2Root 16 dyn2Init :=
  evalDynWithOpaqueCallees_preserved_of_narrow_check dyn_envExtends_13_sync 16 dyn2Init
    (by decide +kernel)

/-! ### Chained supertrait vtable lookup (`charon#1611`) -/

/-- Subtrait `SubArea : Area` with `Self = dyn SubArea`. -/
def dynSubTraitRef : TraitRef := ⟨"proto::SubArea", [.dynamic "proto::SubArea"]⟩

/-- Schema-13 environment where vtable `11` (`dyn SubArea` for `Circle`) links its
supertrait `Area` to vtable `7` (`dyn Area` for `Circle`). -/
def dynSubEnv13 : CompilerQueryEnv :=
  { dynEnv13 with
    vtables := some [
      ⟨7, dynTraitRef, [("proto::<impl Area for Circle>::area", [])], []⟩,
      ⟨9, dynTraitRef, [("proto::<impl Area for Square>::area", [])], []⟩,
      ⟨11, dynSubTraitRef, [], [(dynTraitRef, 7)]⟩ ] }

/-- `fn(vt: *const ()) -> u32 { if true { <dyn SubArea as Area>::area() } else { g_dead() } }`:
the supertrait method `Area::area` called on a `dyn SubArea` receiver (call key
`(Area::area, [dyn SubArea])`, as rustc emits it). -/
def dynSubRoot : CapturedMir :=
  { protoLitIfRoot true "proto::Area::area" [.dynamic "proto::SubArea"] "proto::g_dead" with
    argCount := 1, localDecls := [⟨.mut, protoU32Ty, some "_0"⟩, ⟨.not, protoVtPtrTy, some "vt"⟩] }

/-- Call site of `dynSubRoot`'s virtual call: the receiver's `dyn SubArea` vtable is
read first, chaining `SubArea → Area` before looking up `Area::area` at slot `0`. -/
def dynSubSite : DynCallSite :=
  { dynSite with
    lookupOp := ⟨dynTraitRef, 0, [dynSubTraitRef]⟩
    dynKey := ("proto::Area::area", [.dynamic "proto::SubArea"]) }

/-- `dynSubSite` is well formed: the call's receiver type `dyn SubArea` names the
trait of the first vtable the chain reads. -/
theorem dynSubSite_wellFormed : dynSubSite.wellFormed = true := by decide

/-- Initial state of `dynSubRoot` called with a `dyn SubArea` receiver (vtable `11`). -/
def dynSubInit : MachineState := initMachineState dynSubRoot [.ptr ⟨11, 0⟩ 0]

/-- **Chained supertrait vtable canary (`charon#1611`)**:
1. `UnOpExt.query?` on `dynSubSite` issues `.vtableSupertraitLookup 11 dynSubTraitRef dynTraitRef`
   as its initial query (the first hop of `resolveVTableChain`), resolving to
   `.ok (.supertraitVTable 7)`.
2. `resolveDynTarget` chains `11 (SubArea) → 7 (Area) → <Circle as Area>::area`.
3. Schema 12 (`dynEnv12`) fails closed with `.unsupported .missingVTableEvidence`.
4. A hop from a vtable without the requested supertrait link (vtable `7` of `Area`
   has `supertraits = []`) is `.err (.vtableSupertraitNotFound 7 dynSubTraitRef)`.
5. `evalDynWithOpaqueCallees` on `dynSubInit` halts returning `31` on the narrowed
   table `dynNarrowTbl`, and equals the full-table run by
   `evalDynWithOpaqueCallees_preserved_of_narrow_check`. -/
theorem canary_dyn_supertrait_chain :
    (UnOpExt.vtableMethodLookup dynSubSite.lookupOp).query? ⟨11, 0⟩ =
      some (.vtableSupertraitLookup 11 dynSubTraitRef dynTraitRef) ∧
    evalCompilerQuery dynSubEnv13 (.vtableSupertraitLookup 11 dynSubTraitRef dynTraitRef) =
      .ok (.supertraitVTable 7) ∧
    resolveDynTarget dynSubEnv13 dynSubSite ⟨11, 0⟩ =
      .ok ("proto::<impl Area for Circle>::area", []) ∧
    resolveDynTarget dynEnv12 dynSubSite ⟨11, 0⟩ =
      .unsupported .missingVTableEvidence ∧
    evalCompilerQuery dynSubEnv13 (.vtableSupertraitLookup 7 dynTraitRef dynSubTraitRef) =
      .err (.vtableSupertraitNotFound 7 dynSubTraitRef) ∧
    (evalDynWithOpaqueCallees dynSubEnv13 dynNarrowTbl dynSubSite dynSubRoot 12 dynSubInit).summary =
      ⟨.halted, [.event 1], some 31, none⟩ ∧
    evalDynWithOpaqueCallees { dynSubEnv13 with syncRegions := some [⟨3, 4, 8⟩] }
        dynNarrowTbl dynSubSite dynSubRoot 12 dynSubInit =
      evalDynWithOpaqueCallees dynSubEnv13 dynFullTbl dynSubSite dynSubRoot 12 dynSubInit := by
  have hExt : EnvExtends dynSubEnv13 { dynSubEnv13 with syncRegions := some [⟨3, 4, 8⟩] } :=
    ⟨by decide, rfl, OptionExtends.refl _, rfl, OptionExtends.refl _, (fun _ h => nomatch h),
      OptionExtends.refl _⟩
  refine ⟨rfl, by decide, by decide, by decide, by decide, by decide +kernel,
    evalDynWithOpaqueCallees_preserved_of_narrow_check hExt 12 dynSubInit (by decide +kernel)⟩

/-- The site B2's supertrait canary used: a `<dyn Area as Area>::area` call key
paired with a lookup that starts at the receiver's `dyn SubArea` vtable. -/
def dynMismatchSite : DynCallSite := { dynSite with lookupOp := ⟨dynTraitRef, 0, [dynSubTraitRef]⟩ }

/-- **Ill-formed site canary**: the vtable chain alone would happily resolve
`dynMismatchSite` (a `dyn Area` call dispatched through a `dyn SubArea` vtable
chain), but the site's call key does not name the trait of the receiver's vtable,
so it is ill formed and the run fails closed at the virtual call. -/
theorem canary_dyn_site_mismatch_fails_closed :
    dynMismatchSite.wellFormed = false ∧
    resolveDynTarget dynSubEnv13 dynMismatchSite ⟨11, 0⟩ =
      .ok ("proto::<impl Area for Circle>::area", []) ∧
    (evalDynWithOpaqueCallees dynSubEnv13 dynFullTbl dynMismatchSite dynRoot 12
        (initMachineState dynRoot [.ptr ⟨11, 0⟩ 0])).summary =
      ⟨.faulted, [.event 1], none, none⟩ := by
  decide +kernel

/-- A site for an unrelated virtual call (`<dyn Shape as Shape>::perimeter`). -/
def dynOtherSite : DynCallSite :=
  { dynSite with
    lookupOp := ⟨⟨"proto::Shape", [.dynamic "proto::Shape"]⟩, 0, []⟩
    dynKey := ("proto::Shape::perimeter", [.dynamic "proto::Shape"]) }

/-- **Unregistered virtual calls fail closed**: without vtable dispatch, the trusted
static resolver turns `<dyn Area as Area>::area` into an unlinked external call to
the trait method's `DefPath` (`dyn Area` has no layout, so no body instantiates).
`evalDynWithOpaqueCallees` with a site for a *different* virtual call refuses it
(`.unsupported`) instead. -/
theorem canary_unregistered_dyn_fails_closed :
    (evalWithOpaqueCallees dynFullTbl dynRoot 12 dynInit).summary =
      ⟨.external, [.event 1], none, some "proto::Area::area"⟩ ∧
    (evalDynWithOpaqueCallees dynEnv13 dynFullTbl dynOtherSite dynRoot 12 dynInit).summary =
      ⟨.faulted, [.event 1], none, none⟩ := by
  decide +kernel

/-- Root calling `<dyn Area as Area<u32>>::area` (`typeArgs = [dyn Area, u32]`). -/
def dynArgMismatchRoot : CapturedMir :=
  { protoLitIfRoot true "proto::Area::area" [.dynamic "proto::Area", .uint .u32] "proto::g_dead" with
    argCount := 1, localDecls := [⟨.mut, protoU32Ty, some "_0"⟩, ⟨.not, protoVtPtrTy, some "vt"⟩] }

/-- Site whose `dynKey` has generic trait arguments `[dyn Area, u32]` while its
vtable lookup targets `⟨"proto::Area", [dyn Area]⟩`: `firstTrait.defPath` matches
`"proto::Area"` (so A2's `.defPath`-only `wellFormed` check returned `true`),
but `dynKey.2 ≠ firstTrait.args`. -/
def dynArgMismatchSite : DynCallSite :=
  { dynSite with dynKey := ("proto::Area::area", [.dynamic "proto::Area", .uint .u32]) }

/-- **Generic trait-argument mismatch canary**: `dynArgMismatchSite` has matching
trait `DefPath` `"proto::Area"` and resolves at the raw vtable level, but its generic
argument list `[dyn Area, u32]` does not match the vtable's `[dyn Area]`, so B3's
strengthened `DynCallSite.wellFormed` rejects it (`false`) and execution fails closed
(`.faulted` via `MirStepNode.unsupported`). -/
theorem canary_dyn_trait_arg_mismatch_fails_closed :
    decide ((dynSelfTrait? dynArgMismatchSite.dynKey) =
      some (dynArgMismatchSite.lookupOp.supertraitChain.headD
        dynArgMismatchSite.lookupOp.traitRef).defPath) = true ∧
    dynArgMismatchSite.wellFormed = false ∧
    resolveDynTarget dynEnv13 dynArgMismatchSite ⟨7, 0⟩ =
      .ok ("proto::<impl Area for Circle>::area", []) ∧
    (evalDynWithOpaqueCallees dynEnv13 dynFullTbl dynArgMismatchSite dynArgMismatchRoot 12
        (initMachineState dynArgMismatchRoot [.ptr ⟨7, 0⟩ 0])).summary =
      ⟨.faulted, [.event 1], none, none⟩ := by
  decide +kernel

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

/-- Multi-site demand-gated dynamic-dispatch step:
- if the active step at `s` demands a call key registered in `reg`, dispatch via
  that site's `dynDispatchStep`;
- if it demands an unregistered virtual call key (`dynSelfTrait?.isSome`), fail
  closed (`MirStepNode.unsupported`);
- otherwise step directly via `stepBranchPruned tbl.lookup`. -/
def dynRegistryStep (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable) (reg : DynCallRegistry)
    (body : CapturedMir) (s : MachineState) : MirStepNode :=
  match demandedKey? body s with
  | some k =>
    match reg.findSite? (k.defPath, k.typeArgs) with
    | some site => dynDispatchStep env tbl site body s
    | none =>
      if (dynSelfTrait? (k.defPath, k.typeArgs)).isSome then
        MirStepNode.unsupported
      else
        stepBranchPruned tbl.lookup body s
  | none =>
    stepBranchPruned tbl.lookup body s

/-- Fuel-bounded multi-step evaluation with a `DynCallRegistry`. -/
def evalDynRegistryWithOpaqueCallees (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    (reg : DynCallRegistry) (body : CapturedMir) (fuel : Nat) (s : MachineState) : RunResult :=
  runSteps (dynRegistryStep env tbl reg body) fuel s []

/-- A singleton registry `[site]` steps identically to single-site `dynDemandStep`. -/
theorem dynRegistryStep_singleton (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable)
    (site : DynCallSite) (body : CapturedMir) (s : MachineState) :
    dynRegistryStep env tbl [site] body s = dynDemandStep env tbl site body s := by
  unfold dynRegistryStep dynDemandStep demandsDynSite demandsUnregisteredDyn DynCallRegistry.findSite?
  cases hk : demandedKey? body s with
  | none => rfl
  | some k =>
    dsimp only
    by_cases heq : (k.defPath, k.typeArgs) = site.dynKey
    · have h1 : decide (site.dynKey = (k.defPath, k.typeArgs)) = true := decide_eq_true heq.symm
      have h2 : decide ((k.defPath, k.typeArgs) = site.dynKey) = true := decide_eq_true heq
      simp only [List.filter_cons, List.filter_nil, h1, h2, ite_true]
    · have h1 : decide (site.dynKey = (k.defPath, k.typeArgs)) = false :=
        decide_eq_false (fun h => heq h.symm)
      have h2 : decide ((k.defPath, k.typeArgs) = site.dynKey) = false := decide_eq_false heq
      simp only [List.filter_cons, List.filter_nil, h1, h2, Bool.false_eq_true, ite_false,
        Bool.not_false, Bool.and_true]

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
      reg.findSite? (k.defPath, k.typeArgs) = none ∧
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

/-- Decidable per-state preservation certificate for `dynRegistryStep`. -/
def dynRegistryStepPreservedB (env₁ : CompilerQueryEnv) (narrowTbl fullTbl : OpaqueCalleeTable)
    (reg : DynCallRegistry) (body : CapturedMir) (s : MachineState) : Bool :=
  match demandedKey? body s with
  | none => true
  | some k =>
    match reg.findSite? (k.defPath, k.typeArgs) with
    | some site =>
      match site.vtablePtr? s with
      | none => true
      | some vt =>
        match resolveDynTarget env₁ site vt with
        | .ok target =>
          decide (k.apply (redirectResolver narrowTbl site.dynKey target) =
            k.apply (redirectResolver fullTbl site.dynKey target))
        | .err _ => true
        | .unsupported _ => false
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
    cases hf : reg.findSite? (k.defPath, k.typeArgs) with
    | some site =>
      rw [hf] at hc
      dsimp only at hc
      apply dynDispatchStep_preserved h
      · intro vt hvt m hm
        simp only [hvt, hm, Bool.false_eq_true] at hc
      · intro vt target hvt hr k' hk'
        rw [hk] at hk'
        cases hk'
        simp only [hvt, hr, decide_eq_true_eq] at hc
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

/-- `<impl SubArea for Circle>::bonus() -> u32 { 10 }`. -/
def protoCircleBonus : CapturedMir :=
  protoLeaf "proto::<impl SubArea for Circle>::bonus" 10 0
    [⟨⟨"proto::SubArea::bonus", [protoCircleTy]⟩, "proto::<impl SubArea for Circle>::bonus"⟩]

/-- Schema-13 environment where vtable `11` (`dyn SubArea` for `Circle`) has its own
method `<impl SubArea for Circle>::bonus` at slot `0` *and* links supertrait `Area`
to vtable `7` (`dyn Area` for `Circle`). -/
def dynMultiSiteEnv13 : CompilerQueryEnv :=
  { dynSubEnv13 with
    fnAbis := [
      ("proto::<impl Area for Circle>::area", protoRetU32Abi),
      ("proto::<impl Area for Square>::area", protoRetU32Abi),
      ("proto::<impl SubArea for Circle>::bonus", protoRetU32Abi) ],
    vtables := some [
      ⟨7, dynTraitRef, [("proto::<impl Area for Circle>::area", [])], []⟩,
      ⟨9, dynTraitRef, [("proto::<impl Area for Square>::area", [])], []⟩,
      ⟨11, dynSubTraitRef, [("proto::<impl SubArea for Circle>::bonus", [])],
        [(dynTraitRef, 7)]⟩ ] }

/-- Call site for the subtrait's own virtual method `<dyn SubArea as SubArea>::bonus`
(direct vtable `11` slot `0`, no supertrait hop). -/
def dynSubBonusSite : DynCallSite :=
  { vtableLocal := 1
    lookupOp := ⟨dynSubTraitRef, 0, []⟩
    callerAbi := protoRetU32Abi
    cfiCallSite := none
    dynKey := ("proto::SubArea::bonus", [.dynamic "proto::SubArea"]) }

/-- Two-site registry covering both `<dyn SubArea as SubArea>::bonus` (direct) and
`<dyn SubArea as Area>::area` (supertrait hop `SubArea → Area`). -/
def dynTwoSiteRegistry : DynCallRegistry := [dynSubBonusSite, dynSubSite]

/-- Program making *two distinct virtual calls* in one execution:
`bb0` calls `<dyn SubArea as SubArea>::bonus` (jumping to `bb1`) and `bb1` calls
`<dyn SubArea as Area>::area` (jumping to `bb2: return`). -/
def dynMultiSiteRoot : CapturedMir :=
  { defPath := "proto::dyn_multi_site_root", phase := .runtimePostCleanup, role := .subject,
    argCount := 1,
    localDecls := [⟨.mut, protoU32Ty, some "_0"⟩, ⟨.not, protoVtPtrTy, some "vt"⟩],
    basicBlocks := [
      protoCallBlock "proto::SubArea::bonus" [.dynamic "proto::SubArea"] 1,
      protoCallBlock "proto::Area::area" [.dynamic "proto::SubArea"] 2,
      ⟨[], ⟨.return_, "multi:ret"⟩, false⟩ ],
    fnAbi := protoRetU32Abi, layouts := protoLayouts, allocations := [] }

/-- Initial state of `dynMultiSiteRoot` with a `dyn SubArea` receiver (vtable `11`). -/
def dynMultiSiteInit : MachineState := initMachineState dynMultiSiteRoot [.ptr ⟨11, 0⟩ 0]

/-- Narrowed callee table for `dynMultiSiteRoot` (holding `protoCircleBonus` and `protoCircleArea`). -/
def dynMultiSiteNarrowTbl : OpaqueCalleeTable := .ofList [protoCircleBonus, protoCircleArea]

/-- Full callee table for `dynMultiSiteRoot` (adding unused callees `protoLiveF`, `protoGDead`, `protoSquareArea`). -/
def dynMultiSiteFullTbl : OpaqueCalleeTable :=
  .ofList [protoLiveF, protoGDead, protoCircleBonus, protoCircleArea, protoSquareArea]

/-- **Multi-site dynamic-dispatch registry canary**:
1. `dynTwoSiteRegistry` is well formed (`true`).
2. `evalDynRegistryWithOpaqueCallees` executes *both* virtual call keys
   (`<dyn SubArea as SubArea>::bonus` via direct vtable `11` and
   `<dyn SubArea as Area>::area` via supertrait chain `11 → 7`) and halts returning `31`.
3. Single-site `evalDynWithOpaqueCallees` with only `dynSubBonusSite` or only
   `dynSubSite` fails closed (`.faulted`) at whichever virtual call key is unregistered.
4. The multi-site run is preserved under `EnvExtends` and call-cone narrowing
   (`dynMultiSiteNarrowTbl` vs. `dynMultiSiteFullTbl`) via
   `evalDynRegistryWithOpaqueCallees_preserved_of_narrow_check`. -/
theorem canary_dyn_multi_site_registry :
    dynTwoSiteRegistry.wellFormed = true ∧
    (evalDynRegistryWithOpaqueCallees dynMultiSiteEnv13 dynMultiSiteNarrowTbl
        dynTwoSiteRegistry dynMultiSiteRoot 16 dynMultiSiteInit).summary =
      ⟨.halted, [], some 31, none⟩ ∧
    (evalDynWithOpaqueCallees dynMultiSiteEnv13 dynMultiSiteFullTbl
        dynSubBonusSite dynMultiSiteRoot 16 dynMultiSiteInit).summary =
      ⟨.faulted, [], none, none⟩ ∧
    (evalDynWithOpaqueCallees dynMultiSiteEnv13 dynMultiSiteFullTbl
        dynSubSite dynMultiSiteRoot 16 dynMultiSiteInit).summary =
      ⟨.faulted, [], none, none⟩ ∧
    evalDynRegistryWithOpaqueCallees
        { dynMultiSiteEnv13 with syncRegions := some [⟨3, 4, 8⟩] }
        dynMultiSiteNarrowTbl dynTwoSiteRegistry dynMultiSiteRoot 16 dynMultiSiteInit =
      evalDynRegistryWithOpaqueCallees
        dynMultiSiteEnv13 dynMultiSiteFullTbl dynTwoSiteRegistry dynMultiSiteRoot 16
        dynMultiSiteInit := by
  have hExt : EnvExtends dynMultiSiteEnv13
      { dynMultiSiteEnv13 with syncRegions := some [⟨3, 4, 8⟩] } :=
    ⟨by decide, rfl, OptionExtends.refl _, rfl, OptionExtends.refl _, (fun _ h => nomatch h),
      OptionExtends.refl _⟩
  refine ⟨by decide, by decide +kernel, by decide +kernel, by decide +kernel,
    evalDynRegistryWithOpaqueCallees_preserved_of_narrow_check hExt 16 dynMultiSiteInit
      (by decide +kernel)⟩

/-- Root calling `<dyn Area as Area>::perimeter`. -/
def dynPerimeterRoot : CapturedMir :=
  { protoLitIfRoot true "proto::Area::perimeter" [.dynamic "proto::Area"] "proto::g_dead" with
    argCount := 1, localDecls := [⟨.mut, protoU32Ty, some "_0"⟩, ⟨.not, protoVtPtrTy, some "vt"⟩] }

/-- A well-formed site for `<dyn Area as Area>::perimeter` whose lookup reads slot `0`
of the `Area` vtable, which holds `area`'s implementation. -/
def dynSlotMismatchSite : DynCallSite :=
  { dynSite with dynKey := ("proto::Area::perimeter", [.dynamic "proto::Area"]) }

/-- **Slot/method mismatch canary**: `dynSlotMismatchSite` passes B3's
`DynCallSite.wellFormed` (right trait, right arguments) and its slot resolves, but
the slot holds `<impl Area for Circle>::area`, not a `perimeter` implementation.
B3's step ran it anyway — the redirected pruned step halts returning `31`, `area`'s
value, for a `perimeter` call — while the guarded step fails closed. -/
theorem canary_dyn_slot_method_mismatch_fails_closed :
    dynSlotMismatchSite.wellFormed = true ∧
    resolveDynTarget dynEnv13 dynSlotMismatchSite ⟨7, 0⟩ =
      .ok ("proto::<impl Area for Circle>::area", []) ∧
    implementsCalledMethod "proto::Area::perimeter" "proto::<impl Area for Circle>::area" = false ∧
    implementsCalledMethod "proto::Area::area" "proto::<impl Area for Circle>::area" = true ∧
    implementsCalledMethod "proto::SubArea::bonus" "proto::<impl SubArea for Circle>::bonus" = true ∧
    (runSteps (stepBranchPruned (redirectResolver dynFullTbl dynSlotMismatchSite.dynKey
        ("proto::<impl Area for Circle>::area", [])) dynPerimeterRoot) 12
        (initMachineState dynPerimeterRoot [.ptr ⟨7, 0⟩ 0]) []).summary =
      ⟨.halted, [.event 1], some 31, none⟩ ∧
    (evalDynWithOpaqueCallees dynEnv13 dynFullTbl dynSlotMismatchSite dynPerimeterRoot 12
        (initMachineState dynPerimeterRoot [.ptr ⟨7, 0⟩ 0])).summary =
      ⟨.faulted, [.event 1], none, none⟩ := by
  decide +kernel

/-- A second site registered for `dynSite`'s call key (pointing at slot `1`). -/
def dynDuplicateSite : DynCallSite := { dynSite with lookupOp := ⟨dynTraitRef, 1, []⟩ }

/-- **Registry ambiguity canary**: with two sites registered for the same call key,
B3's first-match lookup silently dispatched through whichever came first; the
registry is now ill formed (`wellFormed = false`, duplicate key), the key has no
site, and the virtual call fails closed. The unambiguous registry still runs. -/
theorem canary_dyn_registry_ambiguity_fails_closed :
    DynCallRegistry.wellFormed [dynSite, dynDuplicateSite] = false ∧
    DynCallRegistry.findSite? [dynSite, dynDuplicateSite] dynSite.dynKey = none ∧
    (evalDynRegistryWithOpaqueCallees dynEnv13 dynFullTbl [dynSite, dynDuplicateSite]
        dynRoot 12 dynInit).summary = ⟨.faulted, [.event 1], none, none⟩ ∧
    DynCallRegistry.wellFormed [dynSite] = true ∧
    (evalDynRegistryWithOpaqueCallees dynEnv13 dynFullTbl [dynSite] dynRoot 12 dynInit).summary =
      ⟨.halted, [.event 1], some 31, none⟩ := by
  decide +kernel

/-- Root calling `<dyn Area as OtherTrait>::area`: same method suffix `::area` as
`Area::area`, but on a *different* trait `proto::OtherTrait`. -/
def dynWrongTraitPrefixRoot : CapturedMir :=
  { protoLitIfRoot true "proto::OtherTrait::area" [.dynamic "proto::Area"] "proto::g_dead" with
    argCount := 1, localDecls := [⟨.mut, protoU32Ty, some "_0"⟩, ⟨.not, protoVtPtrTy, some "vt"⟩] }

/-- Site for `<dyn Area as OtherTrait>::area` reading `Area`'s vtable slot `0`
(`"proto::<impl Area for Circle>::area"`). It passes A3's `implementsCalledMethod`
(both paths end in `::area`!) and A3's `d = firstTrait.defPath` / `dynKey.2 = firstTrait.args`
checks, so A3 would dispatch `OtherTrait::area` to `<impl Area for Circle>::area`! -/
def dynWrongTraitPrefixSite : DynCallSite :=
  { dynSite with dynKey := ("proto::OtherTrait::area", [.dynamic "proto::Area"]) }

/-- **Cross-trait method-suffix collision canary**: `dynWrongTraitPrefixSite` calls
`"proto::OtherTrait::area"` while reading `Area`'s vtable slot `0`. Both paths end
in `::area`, so `implementsCalledMethod` is `true` and `resolveDynTarget` succeeds,
but `methodMatchesTrait "proto::OtherTrait::area" "proto::Area"` is `false`, so B4's
`DynCallSite.wellFormed` rejects the site (`false`) and execution fails closed. -/
theorem canary_dyn_wrong_trait_prefix_fails_closed :
    implementsCalledMethod dynWrongTraitPrefixSite.dynKey.1
      "proto::<impl Area for Circle>::area" = true ∧
    methodMatchesTrait dynWrongTraitPrefixSite.dynKey.1
      dynWrongTraitPrefixSite.lookupOp.traitRef.defPath = false ∧
    dynWrongTraitPrefixSite.wellFormed = false ∧
    resolveDynTarget dynEnv13 dynWrongTraitPrefixSite ⟨7, 0⟩ =
      .ok ("proto::<impl Area for Circle>::area", []) ∧
    (evalDynWithOpaqueCallees dynEnv13 dynFullTbl dynWrongTraitPrefixSite
        dynWrongTraitPrefixRoot 12
        (initMachineState dynWrongTraitPrefixRoot [.ptr ⟨7, 0⟩ 0])).summary =
      ⟨.faulted, [.event 1], none, none⟩ := by
  decide +kernel

/-- Generic supertrait `Conv<u32>` with `Self = dyn Conv` (`args = [dyn Conv, u32]`). -/
def dynConvU32TraitRef : TraitRef :=
  ⟨"proto::Conv", [.dynamic "proto::Conv", .uint .u32]⟩

/-- `<impl Conv<u32> for Circle>::conv() -> u32 { 55 }`. -/
def protoCircleConvU32 : CapturedMir :=
  protoLeaf "proto::<impl Conv<u32> for Circle>::conv" 55 0
    [⟨⟨"proto::Conv::conv", [protoCircleTy, .uint .u32]⟩,
      "proto::<impl Conv<u32> for Circle>::conv"⟩]

/-- Schema-13 environment where vtable `11` (`dyn SubArea` for `Circle`) links
generic supertrait `Conv<u32>` to vtable `13`. -/
def dynGenSuperEnv13 : CompilerQueryEnv :=
  { dynSubEnv13 with
    fnAbis := [
      ("proto::<impl Area for Circle>::area", protoRetU32Abi),
      ("proto::<impl Area for Square>::area", protoRetU32Abi),
      ("proto::<impl Conv<u32> for Circle>::conv", protoRetU32Abi) ],
    vtables := some [
      ⟨7, dynTraitRef, [("proto::<impl Area for Circle>::area", [])], []⟩,
      ⟨11, dynSubTraitRef, [], [(dynTraitRef, 7), (dynConvU32TraitRef, 13)]⟩,
      ⟨13, dynConvU32TraitRef, [("proto::<impl Conv<u32> for Circle>::conv", [])], []⟩ ] }

/-- Root calling the generic supertrait method `<dyn SubArea as Conv<u32>>::conv`
(call key `("proto::Conv::conv", [dyn SubArea, u32])`). -/
def dynGenSuperRoot : CapturedMir :=
  { protoLitIfRoot true "proto::Conv::conv" [.dynamic "proto::SubArea", .uint .u32] "proto::g_dead" with
    argCount := 1, localDecls := [⟨.mut, protoU32Ty, some "_0"⟩, ⟨.not, protoVtPtrTy, some "vt"⟩] }

/-- Call site for `<dyn SubArea as Conv<u32>>::conv` chaining `SubArea → Conv<u32>`. -/
def dynGenSuperSite : DynCallSite :=
  { vtableLocal := 1
    lookupOp := ⟨dynConvU32TraitRef, 0, [dynSubTraitRef]⟩
    callerAbi := protoRetU32Abi
    cfiCallSite := none
    dynKey := ("proto::Conv::conv", [.dynamic "proto::SubArea", .uint .u32]) }

/-- Mismatched generic supertrait site `<dyn SubArea as Conv<u64>>::conv` paired with
the `Conv<u32>` vtable chain. -/
def dynGenSuperBadSite : DynCallSite :=
  { dynGenSuperSite with
    dynKey := ("proto::Conv::conv", [.dynamic "proto::SubArea", .uint .u64]) }

/-- Narrowed and full tables for `dynGenSuperRoot`. -/
def dynGenSuperNarrowTbl : OpaqueCalleeTable := .ofList [protoCircleConvU32]
def dynGenSuperFullTbl : OpaqueCalleeTable :=
  .ofList [protoLiveF, protoGDead, protoCircleArea, protoCircleConvU32]

/-- **Generic supertrait vtable chain canary (closing A3 Item 4)**:
1. `dynGenSuperSite` (`<dyn SubArea as Conv<u32>>::conv`, where `firstTrait = SubArea`
   has args `[dyn SubArea]` while the supertrait `Conv<u32>` has args `[dyn Conv, u32]`)
   was rejected by B3/A3's `dynKey.2 = firstTrait.args`, but is accepted (`wellFormed = true`)
   by B4's `dynKey.2 = .dynamic d :: traitRef.args.tail`.
2. `evalDynWithOpaqueCallees` chains `11 (SubArea) → 13 (Conv<u32>) → <impl Conv<u32> for Circle>::conv`
   and halts returning `55` on `dynGenSuperNarrowTbl` (and equals the full-table run via
   `evalDynWithOpaqueCallees_preserved_of_narrow_check`).
3. Mismatched supertrait type arguments (`dynGenSuperBadSite`: `Conv<u64>` vs. `Conv<u32>`)
   have `wellFormed = false`. -/
theorem canary_dyn_generic_supertrait_chain :
    decide (dynGenSuperSite.dynKey.2 =
      (dynGenSuperSite.lookupOp.supertraitChain.headD
        dynGenSuperSite.lookupOp.traitRef).args) = false ∧
    dynGenSuperSite.wellFormed = true ∧
    dynGenSuperBadSite.wellFormed = false ∧
    (evalDynWithOpaqueCallees dynGenSuperEnv13 dynGenSuperNarrowTbl dynGenSuperSite
        dynGenSuperRoot 12 (initMachineState dynGenSuperRoot [.ptr ⟨11, 0⟩ 0])).summary =
      ⟨.halted, [.event 1], some 55, none⟩ ∧
    evalDynWithOpaqueCallees { dynGenSuperEnv13 with syncRegions := some [⟨3, 4, 8⟩] }
        dynGenSuperNarrowTbl dynGenSuperSite dynGenSuperRoot 12
        (initMachineState dynGenSuperRoot [.ptr ⟨11, 0⟩ 0]) =
      evalDynWithOpaqueCallees dynGenSuperEnv13 dynGenSuperFullTbl dynGenSuperSite
        dynGenSuperRoot 12 (initMachineState dynGenSuperRoot [.ptr ⟨11, 0⟩ 0]) := by
  have hExt : EnvExtends dynGenSuperEnv13
      { dynGenSuperEnv13 with syncRegions := some [⟨3, 4, 8⟩] } :=
    ⟨by decide, rfl, OptionExtends.refl _, rfl, OptionExtends.refl _, (fun _ h => nomatch h),
      OptionExtends.refl _⟩
  refine ⟨by decide, by decide, by decide, by decide +kernel,
    evalDynWithOpaqueCallees_preserved_of_narrow_check hExt 12
      (initMachineState dynGenSuperRoot [.ptr ⟨11, 0⟩ 0]) (by decide +kernel)⟩

/-! ## Part C: worked `BEq`-shadowing demonstration (`tholenst` cl/1022563952) -/

namespace ShadowingDemo

/-- A key type that, like every prototype key, derives only `DecidableEq`. -/
inductive DemoKey : Type where
  | unit
  | idx (n : Nat)
  deriving DecidableEq

/-- Non-shadowed: `==` on `DemoKey` is `instBEqOfDecidableEq`, i.e. `decide`. -/
theorem demoKey_beq_eq_decide (a b : DemoKey) : (a == b) = decide (a = b) := rfl

/-- Non-shadowed: `beq_iff_eq` fires under `simp` via the core `instLawfulBEq`. -/
theorem demoKey_beq_iff (a b : DemoKey) : (a == b) = true ↔ a = b := by simp

/-- The structural `BEq` that a redundant `BEq` derivation next to `DecidableEq`
would install. -/
@[instance_reducible]
def structuralBEq : BEq DemoKey :=
  ⟨fun a b =>
    match a, b with
    | .unit, .unit => true
    | .idx m, .idx n => Nat.beq m n
    | _, _ => false⟩

-- Without the redundant instance, `LawfulBEq DemoKey` is the core `instLawfulBEq`.
/-- info: instLawfulBEq -/
#guard_msgs in
#synth LawfulBEq DemoKey

section Shadowed
attribute [local instance] structuralBEq

/-- With the redundant instance in scope, `==` elaborates to the structural `BEq`
(no longer `decide (· = ·)`). -/
theorem shadowed_beq_is_structural (m n : Nat) :
    (DemoKey.idx m == DemoKey.idx n) = Nat.beq m n := rfl

-- ...and `LawfulBEq DemoKey` can no longer be synthesized, so `beq_iff_eq`
-- (and every `LawfulBEq`-keyed `List`/`Option` lemma) silently stops applying.
/--
error: failed to synthesize
  LawfulBEq DemoKey

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs (whitespace := lax) in
#synth LawfulBEq DemoKey

end Shadowed

/-- Real `Trusted` type audit connection (`theory/Correspondence/V2026_06_01/L4_TreeBorrows.lean:80`):
with `DecidableEq TreeBorrowPerm` alone, `LawfulBEq TreeBorrowPerm` is synthesized
via `instLawfulBEq` and `beq_iff_eq` holds. -/
theorem treeBorrowPerm_beq_iff_eq (a b : TreeBorrowPerm) : (a == b) = true ↔ a = b := by simp

/-- info: instLawfulBEq -/
#guard_msgs in
#synth LawfulBEq TreeBorrowPerm

/-- The redundant structural `BEq TreeBorrowPerm` derived at
`theory/Correspondence/V2026_06_01/L4_TreeBorrows.lean:80`. -/
@[instance_reducible]
def structuralBEqTreeBorrowPerm : BEq TreeBorrowPerm :=
  ⟨fun a b =>
    match a, b with
    | .cell, .cell => true
    | .reservedFrz true, .reservedFrz true => true
    | .reservedFrz false, .reservedFrz false => true
    | .reservedIM, .reservedIM => true
    | .unique, .unique => true
    | .frozen, .frozen => true
    | .disabled, .disabled => true
    | _, _ => false⟩

section ShadowedTreeBorrowPerm
attribute [local instance] structuralBEqTreeBorrowPerm

-- Installing the redundant `BEq TreeBorrowPerm` shadows `instBEqOfDecidableEq`
-- and breaks `LawfulBEq TreeBorrowPerm` synthesis.
/--
error: failed to synthesize
  LawfulBEq TreeBorrowPerm

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs (whitespace := lax) in
#synth LawfulBEq TreeBorrowPerm

end ShadowedTreeBorrowPerm

end ShadowingDemo

/-! ## `#guard_msgs` axiom pins on headline theorems -/

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.opaqueCalleeTable_lookup_eq_trusted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms opaqueCalleeTable_lookup_eq_trusted

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.lookupCallee_hit_mono' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms lookupCallee_hit_mono

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.lookupCallee_hit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lookupCallee_hit

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.lookupCallee_trait_hit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms lookupCallee_trait_hit

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.lookupCallee_miss' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms lookupCallee_miss

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.lookupRaw_ofList_of_mem_nodup' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lookupRaw_ofList_of_mem_nodup

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.stepTerminatorWith_prune_exact' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stepTerminatorWith_prune_exact

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.stepBranchPruned_eq_trusted' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stepBranchPruned_eq_trusted

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.evalWithOpaqueCallees_eq_evalWithListCallees' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalWithOpaqueCallees_eq_evalWithListCallees

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.evalWithOpaqueCallees_cone_narrow' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalWithOpaqueCallees_cone_narrow

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.canary_deadArm_cone_narrow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_deadArm_cone_narrow

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.canary_deadArm_halts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_deadArm_halts

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.canary_liveArm_required' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_liveArm_required

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.canary_multi_cone_narrow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_multi_cone_narrow

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.canary_naiveNarrow_breaks_trait_dispatch' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_naiveNarrow_breaks_trait_dispatch

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.query_schema12_unsupported_fallback' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms query_schema12_unsupported_fallback

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.query_mono_schema' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms query_mono_schema

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.layoutOf_agrees_with_eager' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms layoutOf_agrees_with_eager

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.syncStorageRegion_blocks_iff_overlap' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms syncStorageRegion_blocks_iff_overlap

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.bridgeTypeLayout_roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bridgeTypeLayout_roundtrip

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.autoCfi_breaks_mono' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms autoCfi_breaks_mono

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.memoLookup_memoize' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms memoLookup_memoize

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.dynDispatchStep_preserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dynDispatchStep_preserved

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.dyn_step_preserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dyn_step_preserved

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.dyn_step_enters_impl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dyn_step_enters_impl

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.rigidTyStructEq_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms rigidTyStructEq_iff

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.rigidTy_beq_iff_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms rigidTy_beq_iff_eq

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.stringEq_eq_true_iff_proto' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms stringEq_eq_true_iff_proto

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.valueStructEq_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms valueStructEq_iff

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.lookupCallee_hit_poly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lookupCallee_hit_poly

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.lookupCallee_trait_hit_poly' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lookupCallee_trait_hit_poly

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.lookupCallee_trait_default_hit' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lookupCallee_trait_default_hit

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.canary_trait_specificity_and_default_inheritance' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_trait_specificity_and_default_inheritance

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.canary_evalWithOpaqueCallees_eq_trusted' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_evalWithOpaqueCallees_eq_trusted

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.computeLayout_bridge_commutes' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms computeLayout_bridge_commutes

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.computeLayoutV08Bridged_eq_computeLayoutV06_bridge' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms computeLayoutV08Bridged_eq_computeLayoutV06_bridge

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.evalLayoutOf_v08_eq_v06' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalLayoutOf_v08_eq_v06

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.fnAbiMismatch?_eq_none_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms fnAbiMismatch?_eq_none_iff

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.abiCore_ok_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms abiCore_ok_iff

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.syncStorageRegion_blocks_zero_size' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms syncStorageRegion_blocks_zero_size

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.dynDemandStep_preserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dynDemandStep_preserved

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.canary_dyn_e2e_full_run_schema13' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_dyn_e2e_full_run_schema13

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.canary_dyn_deadBranch_schema12_succeeds' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_dyn_deadBranch_schema12_succeeds

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.decEqOfCtorIdxProto' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms decEqOfCtorIdxProto

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.instDecidableEqBinOpProto' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms instDecidableEqBinOpProto

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.lookupCallee_hit_free_poly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lookupCallee_hit_free_poly

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.canary_free_poly_param_and_concrete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_free_poly_param_and_concrete

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.dynDemandStep_eq_dynDispatchStep_of_resolved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dynDemandStep_eq_dynDispatchStep_of_resolved

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.dynDemandStep_eq_trusted_of_not_demanded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dynDemandStep_eq_trusted_of_not_demanded

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.evalDynWithOpaqueCallees_preserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalDynWithOpaqueCallees_preserved

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.dynStepPreserved_of_check' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms dynStepPreserved_of_check

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.evalDynWithOpaqueCallees_preserved_of_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalDynWithOpaqueCallees_preserved_of_check

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.canary_dyn_two_receivers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_dyn_two_receivers

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.canary_dyn_two_receivers_preserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_dyn_two_receivers_preserved

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.dyn_step_missing_receiver_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dyn_step_missing_receiver_ub

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.lookupCallee_hit_free_poly_opaque' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lookupCallee_hit_free_poly_opaque

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.lookupCallee_trait_hit_cert' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lookupCallee_trait_hit_cert

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.canary_trait_cert_no_toList' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_trait_cert_no_toList

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.evalLayoutOf_v08_eq_v06_of_coherent' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalLayoutOf_v08_eq_v06_of_coherent

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.withBridgedV08Layouts_extends' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms withBridgedV08Layouts_extends

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.incoherence_breaks_dialect_agreement_canary' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms incoherence_breaks_dialect_agreement_canary

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.resolveVTableChain_mono' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms resolveVTableChain_mono

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.evalDynWithOpaqueCallees_preserved_of_narrow_check' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalDynWithOpaqueCallees_preserved_of_narrow_check

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.canary_dyn_supertrait_chain' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_dyn_supertrait_chain

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.dynDispatchStep_of_not_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dynDispatchStep_of_not_wellFormed

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.dynDemandStep_of_unregistered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dynDemandStep_of_unregistered

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.canary_dyn_site_mismatch_fails_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_dyn_site_mismatch_fails_closed

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.canary_unregistered_dyn_fails_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_unregistered_dyn_fails_closed

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.lookupCallee_trait_hit_poly_cert' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lookupCallee_trait_hit_poly_cert

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.lookupCallee_trait_default_hit_cert' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lookupCallee_trait_default_hit_cert

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.canary_trait_poly_and_default_cert_no_toList' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_trait_poly_and_default_cert_no_toList

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.envExtends_allows_incoherent_v08_upgrade_canary' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms envExtends_allows_incoherent_v08_upgrade_canary

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.evalLayoutOf_dialect_invariant_of_coherentExtends' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalLayoutOf_dialect_invariant_of_coherentExtends

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.canary_dyn_trait_arg_mismatch_fails_closed' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_dyn_trait_arg_mismatch_fails_closed

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.dynRegistryStep_singleton' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dynRegistryStep_singleton

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.evalDynRegistryWithOpaqueCallees_preserved_of_narrow_check' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalDynRegistryWithOpaqueCallees_preserved_of_narrow_check

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.canary_dyn_multi_site_registry' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_dyn_multi_site_registry

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.implementsCalledMethod' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms implementsCalledMethod

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.canary_dyn_slot_method_mismatch_fails_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_dyn_slot_method_mismatch_fails_closed

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.canary_dyn_registry_ambiguity_fails_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_dyn_registry_ambiguity_fails_closed

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.evalAbiCompatible_ok_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms evalAbiCompatible_ok_iff

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.evalSyncStorageGuard_ok_iff' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalSyncStorageGuard_ok_iff

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.evalVTableMethodLookup_ok_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms evalVTableMethodLookup_ok_iff

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.evalVTableSupertraitLookup_ok_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms evalVTableSupertraitLookup_ok_iff

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.methodMatchesTrait' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms methodMatchesTrait

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.dynDispatchStep_of_method_mismatch' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dynDispatchStep_of_method_mismatch

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.canary_dyn_wrong_trait_prefix_fails_closed' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_dyn_wrong_trait_prefix_fails_closed

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.canary_dyn_generic_supertrait_chain' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms canary_dyn_generic_supertrait_chain

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.evalLayoutOf_v06_ok_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms evalLayoutOf_v06_ok_iff

/-- info: 'Anneal.DemandCompilerQueryAndOpaqueCalleePrototype.evalLayoutOf_v08_ok_iff' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalLayoutOf_v08_ok_iff

end Anneal.DemandCompilerQueryAndOpaqueCalleePrototype

/-! ## Bottom-of-file axiom audit

Traverses every constant this module adds (`Environment.constants.map₂`: the
`Anneal.DemandCompilerQueryAndOpaqueCalleePrototype` namespace plus
`deriving`-generated auxiliaries) and fails elaboration if:
1. any declaration uses an axiom outside `[propext, Quot.sound]`, or
2. any declaration is emitted outside the `Anneal.DemandCompilerQueryAndOpaqueCalleePrototype`
   namespace (`leaked` check, catching orphan enumeration `T.ofNat` / `T.ofNat_ctorIdx`
   collisions with `Trusted.*` at elaboration time).
Non-vacuity: the auditor must flag `Classical.choice` (via `Classical.em`), `sorryAx`,
and `Lean.ofReduceBool`, and must have covered a minimum number of constants and
theorems. -/

open Lean in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Quot.sound]
  let forbiddenOf (n : Name) : Elab.Command.CommandElabM (Array Name) := do
    return (← Lean.collectAxioms n).filter (fun ax => !allowed.contains ax)
  for (probe, ax) in [(``Classical.em, ``Classical.choice), (``sorryAx, ``sorryAx),
      (``Lean.ofReduceBool, ``Lean.ofReduceBool)] do
    unless (← forbiddenOf probe).contains ax do
      throwError "axiom audit self-test failed: {probe} not flagged for {ax}"
  let pfx := `Anneal.DemandCompilerQueryAndOpaqueCalleePrototype
  let mut constants : Nat := 0
  let mut inNamespace : Nat := 0
  let mut theorems : Nat := 0
  let mut leaked : Array Name := #[]
  let mut bad : Array (Name × Array Name) := #[]
  for (n, ci) in env.constants.map₂.toList do
    constants := constants + 1
    let un := (Lean.privateToUserName? n).getD n
    if pfx.isPrefixOf un then
      inNamespace := inNamespace + 1
    else
      let last := un.eraseMacroScopes.getString!
      let isRealizedEq :=
        last == "eq_def" || last == "splitter" || last == "else_eq" ||
          last.startsWith "eq_" || last.startsWith "_sparseCasesOn_"
      unless un.hasMacroScopes || isRealizedEq do
        leaked := leaked.push un
    if ci matches .thmInfo _ then theorems := theorems + 1
    let f ← forbiddenOf n
    unless f.isEmpty do bad := bad.push (n, f)
  unless bad.isEmpty do
    throwError "axiom audit: forbidden axioms {bad}"
  unless leaked.isEmpty do
    throwError "namespace hygiene audit: constants declared outside {pfx}: {leaked}"
  unless inNamespace ≥ 1400 && theorems ≥ 140 do
    throwError "axiom audit coverage too low: {constants} constants ({inNamespace} in namespace), {theorems} theorems"
