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

deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.Layout.Size
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.Layout.Align
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.Layout.WrappingRange
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.Layout.PrimitiveKind
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.Layout.ScalarLayout
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.Layout.FieldsShape
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.Layout.VariantsShape
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.Layout.BackendRepr
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.Layout.TypeLayout
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.Layout.AbiPassMode
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.Layout.ArgAbi
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.Layout.CallConv
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.Layout.FnAbi
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.Layout.LayoutTable
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.UintTy
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.IntTy
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.FloatTy
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.Mutability
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.Safety
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.UnOp
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
/-- `rigidTyStructEq` decides `RigidTy` equality. -/
theorem rigidTyStructEq_iff (a b : RigidTy) : rigidTyStructEq a b = true ↔ a = b :=
  if hTag : rigidTyTag a = rigidTyTag b then
    match a, b, hTag with
    | .param i n, .param j m, _ => by simp [rigidTyStructEq]
    | .alias d as, .alias e bs, _ => by
      have ih := rigidTyListStructEq_iff as bs
      simp [rigidTyStructEq, ih]
    | .bool, .bool, _ => by simp [rigidTyStructEq]
    | .char, .char, _ => by simp [rigidTyStructEq]
    | .int w, .int v, _ => by simp [rigidTyStructEq]
    | .uint w, .uint v, _ => by simp [rigidTyStructEq]
    | .float w, .float v, _ => by simp [rigidTyStructEq]
    | .never, .never, _ => by simp [rigidTyStructEq]
    | .str, .str, _ => by simp [rigidTyStructEq]
    | .tuple as, .tuple bs, _ => by
      have ih := rigidTyListStructEq_iff as bs
      simp [rigidTyStructEq, ih]
    | .array x n, .array y m, _ => by
      have ih := rigidTyStructEq_iff x y
      simp [rigidTyStructEq, ih]
    | .slice x, .slice y, _ => by
      have ih := rigidTyStructEq_iff x y
      simp [rigidTyStructEq, ih]
    | .ref m x, .ref n y, _ => by
      have ih := rigidTyStructEq_iff x y
      simp [rigidTyStructEq, ih]
    | .rawPtr m x, .rawPtr n y, _ => by
      have ih := rigidTyStructEq_iff x y
      simp [rigidTyStructEq, ih]
    | .adt d as, .adt e bs, _ => by
      have ih := rigidTyListStructEq_iff as bs
      simp [rigidTyStructEq, ih]
    | .fnDef d as, .fnDef e bs, _ => by
      have ih := rigidTyListStructEq_iff as bs
      simp [rigidTyStructEq, ih]
    | .fnPtr ins o sf cc, .fnPtr jns p tf dd, _ => by
      have ih₁ := rigidTyListStructEq_iff ins jns
      have ih₂ := rigidTyStructEq_iff o p
      simp [rigidTyStructEq, ih₁, ih₂, Bool.and_assoc]
    | .closure d as, .closure e bs, _ => by
      have ih := rigidTyListStructEq_iff as bs
      simp [rigidTyStructEq, ih]
    | .dynamic d, .dynamic e, _ => by simp [rigidTyStructEq]
    | .foreign d, .foreign e, _ => by simp [rigidTyStructEq]
    | .other d, .other e, _ => by simp [rigidTyStructEq]
  else by
    rw [rigidTyStructEq_of_tag_ne hTag]
    exact ⟨(fun h => nomatch h), fun e => absurd (congrArg rigidTyTag e) hTag⟩

/-- Pointwise companion of `rigidTyStructEq_iff`. -/
theorem rigidTyListStructEq_iff (as bs : List RigidTy) :
    rigidTyListStructEq as bs = true ↔ as = bs :=
  match as, bs with
  | [], [] => by simp [rigidTyListStructEq]
  | [], _ :: _ => by simp [rigidTyListStructEq]
  | _ :: _, [] => by simp [rigidTyListStructEq]
  | a :: as, b :: bs => by
    have ih₁ := rigidTyStructEq_iff a b
    have ih₂ := rigidTyListStructEq_iff as bs
    simp [rigidTyListStructEq, ih₁, ih₂]
end

/-- Axiom-free manual `DecidableEq` for the nested inductive `RigidTy`
(`deriving DecidableEq` does not support nested inductives). -/
instance instDecidableEqRigidTyProto : DecidableEq RigidTy :=
  fun a b => decidable_of_iff _ (rigidTyStructEq_iff a b)

deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.Ty
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.TraitRef
deriving instance DecidableEq for Trusted.Rustc.V2026_06_01.MirAst.TraitImplEntry

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

end OpaqueCalleeTable

attribute [irreducible] OpaqueCalleeTable OpaqueCalleeTable.ofList OpaqueCalleeTable.toList
  OpaqueCalleeTable.lookupRaw OpaqueCalleeTable.lookup

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

/-- Negative canary: dropping the *live* callee changes the outcome (the cone
hypothesis is necessary). -/
theorem canary_liveArm_required :
    (evalWithOpaqueCallees canaryBrokenTbl canaryRoot 8 canaryInit).summary =
      ⟨.external, [.event 1], none, some "proto::live_f"⟩ := by
  decide +kernel

/- Opacity witness: at default transparency `whnf` leaves opaque-table lookups
stuck (no `O(|callees|)` `findCallee?` / `lookupCallee` unfolding); only an
explicit `.all` transparency sees through the seal. -/
open Lean Meta in
run_meta do
  let raw := mkApp2 (mkConst ``OpaqueCalleeTable.lookupRaw) (mkConst ``canaryFullTbl)
    (mkStrLit "proto::live_f")
  let full := mkApp5 (mkConst ``OpaqueCalleeTable.lookup) (mkConst ``canaryFullTbl)
    (mkConst ``protoLayouts) (mkStrLit "proto::live_f")
    (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``RigidTy))
    (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``TraitImplEntry))
  for (e, head) in [(raw, ``OpaqueCalleeTable.lookupRaw), (full, ``OpaqueCalleeTable.lookup)] do
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

/-- The polymorphic key agrees across the full and narrowed tables. -/
theorem canary_multi_polyKey_agrees :
    multiNarrowTbl.lookupKey multiPolyKey = multiFullTbl.lookupKey multiPolyKey := by
  unfold multiNarrowTbl multiFullTbl
  rw [canary_poly_resolve _ (by rfl), canary_poly_resolve _ (by rfl)]

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
  | answerKindMismatch
  deriving DecidableEq, Repr

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
`vtableId` for `traitRef`. -/
structure VTableMethodEntry : Type where
  vtableId : Nat
  traitRef : TraitRef
  methods : List (DefPath × List RigidTy)
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
  deriving DecidableEq

/-- Answers of demand-time queries. -/
inductive QueryAnswer : Type where
  | layout (l : TypeLayout)
  | abiOk
  | syncPermit
  | method (defPath : DefPath) (typeArgs : List RigidTy)
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

/-- First per-argument ABI mismatch (pass mode, then layout). -/
def argAbiMismatch? : Nat → List ArgAbi → List ArgAbi → Option QueryErr
  | _, [], [] => none
  | i, a :: as, b :: bs =>
    if a.mode = b.mode then
      if a.layout = b.layout then argAbiMismatch? (i + 1) as bs else some (.argLayoutMismatch i)
    else some (.argModeMismatch i)
  | _, _, _ => some .argCountMismatch

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

/-- CFI-independent ABI check against the declared `FnAbi` table. -/
def abiCore (env : CompilerQueryEnv) (callerAbi : FnAbi) (callee : DefPath) :
    QueryResult QueryAnswer :=
  match lookupDefPathAssoc env.fnAbis callee with
  | none => .err (.unknownCalleeAbi callee)
  | some calleeAbi =>
    match fnAbiMismatch? callerAbi calleeAbi with
    | some e => .err e
    | none => .ok .abiOk

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
into, sync region `r`. -/
def SyncStorageRegion.blocks (r : SyncStorageRegion) (allocId offset len : Nat) : Bool :=
  decide (r.allocId = allocId) &&
    ((decide (r.offset ≤ offset) && decide (offset < r.offset + r.size)) ||
      (decide (offset < r.offset) && decide (r.offset < offset + len)))

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

/-- **Pure demand-time evaluator** of all four query families. -/
def evalCompilerQuery (env : CompilerQueryEnv) : CompilerQuery → QueryResult QueryAnswer
  | .layoutOf dialect ty => evalLayoutOf env dialect ty
  | .abiCompatible callerAbi callee cfiCallSite => evalAbiCompatible env callerAbi callee cfiCallSite
  | .syncStorageGuard allocId offset len => evalSyncStorageGuard env allocId offset len
  | .vtableMethodLookup vtableId traitRef slotIdx => evalVTableMethodLookup env vtableId traitRef slotIdx

/-- Queries answerable only from Schema-13 evidence. -/
def CompilerQuery.isSchema13Only : CompilerQuery → Bool
  | .abiCompatible _ _ (some _) => true
  | .syncStorageGuard .. => true
  | .vtableMethodLookup .. => true
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
optional evidence only populated. -/
structure EnvExtends (env₁ env₂ : CompilerQueryEnv) : Prop where
  schema_le : SchemaLe env₁.schema env₂.schema
  layoutsV06_eq : env₂.layoutsV06 = env₁.layoutsV06
  layoutsV08_ext : OptionExtends env₁.layoutsV08 env₂.layoutsV08
  fnAbis_eq : env₂.fnAbis = env₁.fnAbis
  cfi_ext : OptionExtends env₁.cfiTags env₂.cfiTags
  sync_ext : OptionExtends env₁.syncRegions env₂.syncRegions
  vtables_ext : OptionExtends env₁.vtables env₂.vtables

theorem EnvExtends.refl (env : CompilerQueryEnv) : EnvExtends env env :=
  ⟨SchemaLe.refl _, rfl, OptionExtends.refl _, rfl, OptionExtends.refl _,
    OptionExtends.refl _, OptionExtends.refl _⟩

theorem EnvExtends.trans {env₁ env₂ env₃ : CompilerQueryEnv} (h₁ : EnvExtends env₁ env₂)
    (h₂ : EnvExtends env₂ env₃) : EnvExtends env₁ env₃ :=
  ⟨SchemaLe.trans h₁.schema_le h₂.schema_le, h₂.layoutsV06_eq.trans h₁.layoutsV06_eq,
    h₁.layoutsV08_ext.trans h₂.layoutsV08_ext, h₂.fnAbis_eq.trans h₁.fnAbis_eq,
    h₁.cfi_ext.trans h₂.cfi_ext, h₁.sync_ext.trans h₂.sync_ext,
    h₁.vtables_ext.trans h₂.vtables_ext⟩

/-- Schema-gated evidence is monotone under extension. -/
theorem gated_evidence_mono {α : Type} {f : CompilerSchemaVersion → Bool}
    (hf : ∀ a b, SchemaLe a b → f a = true → f b = true) {s₁ s₂ : CompilerSchemaVersion}
    {o₁ o₂ : Option α} (hs : SchemaLe s₁ s₂) (ho : OptionExtends o₁ o₂) {x : α}
    (h : (if f s₁ then o₁ else none) = some x) : (if f s₂ then o₂ else none) = some x := by
  cases hf₁ : f s₁ with
  | false => simp [hf₁] at h
  | true =>
    simp only [hf₁, ite_true] at h
    simp [hf _ _ hs hf₁, ho x h]

theorem v08Layouts_mono {env₁ env₂ : CompilerQueryEnv} (h : EnvExtends env₁ env₂)
    {t : Trusted.Rustc.V2026_08_01.Layout.LayoutTable} (ht : env₁.v08Layouts? = some t) :
    env₂.v08Layouts? = some t :=
  gated_evidence_mono (fun _ _ => hasV08Layouts_mono) h.schema_le h.layoutsV08_ext ht

theorem cfiEvidence_mono {env₁ env₂ : CompilerQueryEnv} (h : EnvExtends env₁ env₂)
    {x : CfiTagSpec} (hx : env₁.cfiEvidence? = some x) : env₂.cfiEvidence? = some x :=
  gated_evidence_mono (fun _ _ => hasSchema13_mono) h.schema_le h.cfi_ext hx

theorem syncEvidence_mono {env₁ env₂ : CompilerQueryEnv} (h : EnvExtends env₁ env₂)
    {x : List SyncStorageRegion} (hx : env₁.syncEvidence? = some x) :
    env₂.syncEvidence? = some x :=
  gated_evidence_mono (fun _ _ => hasSchema13_mono) h.schema_le h.sync_ext hx

theorem vtableEvidence_mono {env₁ env₂ : CompilerQueryEnv} (h : EnvExtends env₁ env₂)
    {x : List VTableMethodEntry} (hx : env₁.vtableEvidence? = some x) :
    env₂.vtableEvidence? = some x :=
  gated_evidence_mono (fun _ _ => hasSchema13_mono) h.schema_le h.vtables_ext hx

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

/-- **Sync guard specification**: for non-empty accesses and regions, the guard
rejects exactly the accesses overlapping a region of the same allocation. -/
theorem syncStorageRegion_blocks_iff_overlap (r : SyncStorageRegion) (allocId offset len : Nat)
    (hlen : 0 < len) (hsize : 0 < r.size) :
    r.blocks allocId offset len = true ↔
      r.allocId = allocId ∧ offset < r.offset + r.size ∧ r.offset < offset + len := by
  simp only [SyncStorageRegion.blocks, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨ha, (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)⟩
    · exact ⟨ha, h₂, by omega⟩
    · exact ⟨ha, by omega, h₂⟩
  · rintro ⟨ha, h₁, h₂⟩
    refine ⟨ha, ?_⟩
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

/-- `charon#1611` `UnOp.vtableMethodLookup traitRef slotIdx`. -/
structure VTableMethodLookupOp : Type where
  traitRef : TraitRef
  slotIdx : Nat
  deriving DecidableEq

/-- Prototype unary operators: the trusted `UnOp` plus `charon#1611`'s demand-time
`vtableMethodLookup`. -/
inductive UnOpExt : Type where
  | base (op : UnOp)
  | vtableMethodLookup (op : VTableMethodLookupOp)
  deriving DecidableEq

/-- The demand-time compiler query a unary operator issues on a vtable pointer
(`none` for trusted base operators, which never consult the query environment). -/
def UnOpExt.query? : UnOpExt → ProvenancePtr → Option CompilerQuery
  | .base _, _ => none
  | .vtableMethodLookup op, vtablePtr =>
    some (.vtableMethodLookup vtablePtr.allocId op.traitRef op.slotIdx)

/-- A `dyn Trait` method call site. -/
structure DynCallSite : Type where
  /-- vtable pointer of the `dyn Trait` receiver. -/
  vtablePtr : ProvenancePtr
  /-- The `UnOp.vtableMethodLookup` applied to it. -/
  lookupOp : VTableMethodLookupOp
  /-- Caller-side ABI of the trait method signature. -/
  callerAbi : FnAbi
  /-- CFI call-site function-pointer type, when CFI-instrumented. -/
  cfiCallSite : Option RigidTy
  /-- Call key `(defPath, typeArgs)` of the `dyn` call in the caller's terminator. -/
  dynKey : DefPath × List RigidTy
  deriving DecidableEq

/-- Resolve a `dyn` call: `UnOp.vtableMethodLookup`, then `abiCompatible`. -/
def resolveDynTarget (env : CompilerQueryEnv) (site : DynCallSite) :
    QueryResult (DefPath × List RigidTy) :=
  match (UnOpExt.vtableMethodLookup site.lookupOp).query? site.vtablePtr with
  | none => .err .answerKindMismatch
  | some q =>
    match evalCompilerQuery env q with
    | .ok (.method p tys) =>
      match evalCompilerQuery env (.abiCompatible site.callerAbi p site.cfiCallSite) with
      | .ok _ => .ok (p, tys)
      | .err e => .err e
      | .unsupported m => .unsupported m
    | .ok _ => .err .answerKindMismatch
    | .err e => .err e
    | .unsupported m => .unsupported m

/-- Resolver redirecting the `dyn` call key to the dispatched method in the opaque
table (every other key resolves through the table unchanged). -/
def redirectResolver (tbl : OpaqueCalleeTable) (dynKey target : DefPath × List RigidTy) :
    CalleeResolver :=
  fun callerLayouts p tys extra =>
    if (p, tys) = dynKey then tbl.lookup callerLayouts target.1 target.2 extra
    else tbl.lookup callerLayouts p tys extra

/-- **Unified dynamic-dispatch step**: `UnOp.vtableMethodLookup → abiCompatible →
OpaqueCalleeTable.lookup → stepBranchPruned`. Missing evidence fails closed
(`MirStepNode.unsupported`), a CFI type-id mismatch is the defined CFI trap
(`abort`), and every other semantic error is UB. -/
def dynDispatchStep (env : CompilerQueryEnv) (tbl : OpaqueCalleeTable) (site : DynCallSite)
    (body : CapturedMir) (s : MachineState) : MirStepNode :=
  match resolveDynTarget env site with
  | .ok target => stepBranchPruned (redirectResolver tbl site.dynKey target) body s
  | .err .cfiTypeIdMismatch => MirStepNode.retOutcome .abort
  | .err _ => MirStepNode.fail .ub
  | .unsupported _ => MirStepNode.unsupported

/-- `resolveDynTarget` is monotone under `EnvExtends` on supported answers. -/
theorem resolveDynTarget_mono {env₁ env₂ : CompilerQueryEnv} (h : EnvExtends env₁ env₂)
    (site : DynCallSite) (hsup : ∀ m, resolveDynTarget env₁ site ≠ .unsupported m) :
    resolveDynTarget env₂ site = resolveDynTarget env₁ site := by
  unfold resolveDynTarget at hsup ⊢
  simp only [UnOpExt.query?] at hsup ⊢
  generalize hq : CompilerQuery.vtableMethodLookup site.vtablePtr.allocId site.lookupOp.traitRef
    site.lookupOp.slotIdx = q at hsup ⊢
  cases hv : evalCompilerQuery env₁ q with
  | unsupported m => exact absurd (by simp [hv]) (hsup m)
  | err e =>
    rw [query_mono_schema h q (by simp [hv]), hv]
  | ok a =>
    rw [query_mono_schema h q (by simp [hv]), hv]
    rw [hv] at hsup
    cases a with
    | method p tys =>
      simp only at hsup ⊢
      cases hb : evalCompilerQuery env₁ (.abiCompatible site.callerAbi p site.cfiCallSite) with
      | unsupported m => exact absurd (by simp [hb]) (hsup m)
      | err e => rw [query_mono_schema h _ (by simp [hb]), hb]
      | ok b => rw [query_mono_schema h _ (by simp [hb]), hb]
    | _ => rfl

/-- The dynamic-dispatch step on a resolved target is a branch-pruned step. -/
theorem dynDispatchStep_eq_of_resolved {env : CompilerQueryEnv} {tbl : OpaqueCalleeTable}
    {site : DynCallSite} {body : CapturedMir} {s : MachineState} {target : DefPath × List RigidTy}
    (h : resolveDynTarget env site = .ok target) :
    dynDispatchStep env tbl site body s =
      stepBranchPruned (redirectResolver tbl site.dynKey target) body s := by
  unfold dynDispatchStep
  rw [h]

/-- Preservation under `EnvExtends`. -/
theorem dynDispatchStep_envExtends {env₁ env₂ : CompilerQueryEnv} (h : EnvExtends env₁ env₂)
    (tbl : OpaqueCalleeTable) (site : DynCallSite) (body : CapturedMir) (s : MachineState)
    (hsup : ∀ m, resolveDynTarget env₁ site ≠ .unsupported m) :
    dynDispatchStep env₂ tbl site body s = dynDispatchStep env₁ tbl site body s := by
  unfold dynDispatchStep
  rw [resolveDynTarget_mono h site hsup]

/-- Preservation under call-cone narrowing. -/
theorem dynDispatchStep_cone_narrow (env : CompilerQueryEnv)
    (narrowTbl fullTbl : OpaqueCalleeTable) (site : DynCallSite) (body : CapturedMir)
    (s : MachineState)
    (hcone : ∀ target, resolveDynTarget env site = .ok target →
      ∀ k, demandedKey? body s = some k →
        k.apply (redirectResolver narrowTbl site.dynKey target) =
          k.apply (redirectResolver fullTbl site.dynKey target)) :
    dynDispatchStep env narrowTbl site body s = dynDispatchStep env fullTbl site body s := by
  unfold dynDispatchStep
  cases hr : resolveDynTarget env site with
  | ok target => exact stepBranchPruned_congr body s (hcone target hr)
  | err e => cases e <;> rfl
  | unsupported m => rfl

/-- **End-to-end integration theorem**: the dynamic-dispatch step is preserved
simultaneously under a sound environment extension and call-cone narrowing. -/
theorem dynDispatchStep_preserved {env₁ env₂ : CompilerQueryEnv}
    {narrowTbl fullTbl : OpaqueCalleeTable} {site : DynCallSite} {body : CapturedMir}
    {s : MachineState} (h : EnvExtends env₁ env₂)
    (hsup : ∀ m, resolveDynTarget env₁ site ≠ .unsupported m)
    (hcone : ∀ target, resolveDynTarget env₁ site = .ok target →
      ∀ k, demandedKey? body s = some k →
        k.apply (redirectResolver narrowTbl site.dynKey target) =
          k.apply (redirectResolver fullTbl site.dynKey target)) :
    dynDispatchStep env₂ narrowTbl site body s = dynDispatchStep env₁ fullTbl site body s := by
  rw [dynDispatchStep_envExtends h narrowTbl site body s hsup]
  exact dynDispatchStep_cone_narrow env₁ narrowTbl fullTbl site body s hcone

/-! ### End-to-end canary -/

/-- `Area` trait reference with `Self = dyn Area`. -/
def dynTraitRef : TraitRef := ⟨"proto::Area", [.dynamic "proto::Area"]⟩

/-- The `dyn Area` call site (vtable `7`, slot `0`, not CFI-instrumented). -/
def dynSite : DynCallSite :=
  { vtablePtr := ⟨7, 0⟩, lookupOp := ⟨dynTraitRef, 0⟩, callerAbi := protoRetU32Abi,
    cfiCallSite := none, dynKey := ("proto::Area::area", [.dynamic "proto::Area"]) }

/-- `if true { <dyn Area>::area() } else { g_dead() }`. -/
def dynRoot : CapturedMir :=
  protoLitIfRoot true "proto::Area::area" [.dynamic "proto::Area"] "proto::g_dead"

/-- Initial state of `dynRoot`. -/
def dynInit : MachineState := initMachineState dynRoot []

/-- State at the live `dyn` call (after the literal switch). -/
def dynAtCall : MachineState :=
  { dynInit with frame := { blockIdx := 1, stmtIdx := 0, locals := dynInit.frame.locals } }

/-- `dynAtCall` is not hand-made: it is exactly the state the pruned literal
switch reaches from `dynInit` (after emitting branch event `1`), under any
resolver. -/
theorem dynAtCall_reached (r : CalleeResolver) :
    viewStepNode (stepBranchPruned r dynRoot dynInit) = .cont (some (.event 1)) (.running dynAtCall) :=
  rfl

/-- Schema-12 environment (no vtable evidence). -/
def dynEnv12 : CompilerQueryEnv :=
  { schema := .v2026_08_01, layoutsV06 := protoLayouts,
    layoutsV08 := some (bridgeLayoutV06ToV08 protoLayouts),
    fnAbis := [("proto::<impl Area for Circle>::area", protoRetU32Abi)], cfiTags := none,
    syncRegions := none, vtables := none }

/-- Schema-13 extension with vtable evidence. -/
def dynEnv13 : CompilerQueryEnv :=
  { dynEnv12 with
    schema := .schema13
    vtables := some [⟨7, dynTraitRef, [("proto::<impl Area for Circle>::area", [])]⟩] }

/-- A further extension populating sync-storage regions. -/
def dynEnv13Sync : CompilerQueryEnv := { dynEnv13 with syncRegions := some [⟨3, 4, 8⟩] }

/-- Full and narrowed tables for the `dyn` canary. -/
def dynFullTbl : OpaqueCalleeTable :=
  .ofList [protoFillerA, protoGDead, protoCircleArea, protoFillerB]

/-- Narrowed `dyn` table. -/
def dynNarrowTbl : OpaqueCalleeTable := .ofList [protoCircleArea]

/-- Schema 12 fails closed on the `dyn` call. -/
theorem dyn_schema12_unsupported :
    resolveDynTarget dynEnv12 dynSite = .unsupported .missingVTableEvidence := by decide

/-- Schema 13 dispatches to `<Circle as Area>::area`. -/
theorem dyn_schema13_resolves :
    resolveDynTarget dynEnv13 dynSite = .ok ("proto::<impl Area for Circle>::area", []) := by
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
  rw [dynDispatchStep, dyn_schema12_unsupported]

/-- The live `dyn` call is the only demanded key at the call state. -/
theorem dyn_demandedKey :
    demandedKey? dynRoot dynAtCall =
      some ⟨protoLayouts, "proto::Area::area", [.dynamic "proto::Area"], []⟩ := by
  decide +kernel

/-- **End-to-end canary**: the Schema-13 dynamic-dispatch step is preserved when the
environment is further extended (sync regions) *and* the callee table is narrowed
to the dispatched method (dropping the dead-arm `g_dead` and fillers). -/
theorem dyn_step_preserved :
    dynDispatchStep dynEnv13Sync dynNarrowTbl dynSite dynRoot dynAtCall =
      dynDispatchStep dynEnv13 dynFullTbl dynSite dynRoot dynAtCall := by
  apply dynDispatchStep_preserved dyn_envExtends_13_sync
  · rw [dyn_schema13_resolves]
    exact fun _ h => nomatch h
  · intro target ht k hk
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

/-- Sync-storage guard canaries over region `[4, 12)` of allocation `3`. -/
theorem syncStorageGuard_canary :
    evalCompilerQuery dynEnv13Sync (.syncStorageGuard 3 6 1) =
      .err (.syncStorageOverlap ⟨3, 4, 8⟩) ∧
    evalCompilerQuery dynEnv13Sync (.syncStorageGuard 3 2 4) =
      .err (.syncStorageOverlap ⟨3, 4, 8⟩) ∧
    evalCompilerQuery dynEnv13Sync (.syncStorageGuard 3 0 4) = .ok .syncPermit ∧
    evalCompilerQuery dynEnv13Sync (.syncStorageGuard 3 12 4) = .ok .syncPermit ∧
    evalCompilerQuery dynEnv13Sync (.syncStorageGuard 4 6 1) = .ok .syncPermit ∧
    evalCompilerQuery dynEnv13 (.syncStorageGuard 3 6 1) = .unsupported .missingSyncStorage := by
  decide

/-- A CFI-instrumented `dyn` call whose call-site type id mismatches is the
defined CFI trap (`abort`), not UB and not a call. -/
theorem dyn_cfi_trap :
    dynDispatchStep { dynEnv13 with cfiTags := some ⟨[("proto::<impl Area for Circle>::area", 1)],
        [(.fnPtr [] (.uint .u32) .safe .rust, 2)]⟩ } dynFullTbl
      { dynSite with cfiCallSite := some (.fnPtr [] (.uint .u32) .safe .rust) } dynRoot dynAtCall =
      MirStepNode.retOutcome .abort := by
  rfl

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

end Anneal.DemandCompilerQueryAndOpaqueCalleePrototype

/-! ## Bottom-of-file axiom audit

Traverses every constant this module adds (`Environment.constants.map₂`: the
`Anneal.DemandCompilerQueryAndOpaqueCalleePrototype` namespace plus
`deriving`-generated auxiliaries) and fails elaboration if any uses an axiom
outside `[propext, Quot.sound]`. Non-vacuity:
the auditor must flag `Classical.choice` (via `Classical.em`), `sorryAx`, and
`Lean.ofReduceBool`, and must have covered a minimum number of constants and
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
  let mut bad : Array (Name × Array Name) := #[]
  -- Every constant this module adds (including `deriving`-generated auxiliaries in
  -- the derived types' namespaces) is audited.
  for (n, ci) in env.constants.map₂.toList do
    constants := constants + 1
    if pfx.isPrefixOf ((Lean.privateToUserName? n).getD n) then inNamespace := inNamespace + 1
    if ci matches .thmInfo _ then theorems := theorems + 1
    let f ← forbiddenOf n
    unless f.isEmpty do bad := bad.push (n, f)
  unless bad.isEmpty do
    throwError "axiom audit: forbidden axioms {bad}"
  unless inNamespace ≥ 1000 && theorems ≥ 90 do
    throwError "axiom audit coverage too low: {constants} constants ({inNamespace} in namespace), {theorems} theorems"
