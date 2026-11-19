/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/
import Trusted.Sequence
import Trusted.Layout
import Trusted.MirAst
import Trusted.MirSemantics

/-!
# `V2026_06_01` ↔ `LeanMiri` correspondence TCB (definitions and claims)

This module is the human-audited correspondence TCB (`docs/mir-correspondence-design.md`
§1.3). It contains **only** semantic definitions and the top-level claim
propositions; every proof (helper lemmas, inductions, simulations, canaries)
lives in the untrusted `theory/Anneal/Mir/Correspondence/` modules, and
`Anneal.Mir.Correspondence.Claims` proves each claim below by name.

Contents:

1. **Structural equality and canonical interning** (`rigidTyBEq`, `tyBEq`,
   `indexOf?`, `insertIfAbsent`, `typesAreCanonical`): computable, proof-free
   Boolean equality (no `Classical.choice`, no new instances on existing
   `Trusted` types).
2. **Type-interning codec** (`encodeProg` / `decodeProg`) between the deep
   `Trusted.Rustc.V2026_06_01.MirAst` syntax (`V2026Prog`) and the
   `TyId`-indexed reference syntax (`RefProg`) for every syntax type
   (`ProjectionElem`, `Place`, `ConstOperand`, `Operand`, `AggregateKind`,
   `Rvalue`, `NonDivergingIntrinsic`, `StatementKind`, `Statement`,
   `TerminatorKind`, `Terminator`, `BasicBlockData`, `LocalDecl`,
   `CapturedMir`, and multi-body programs). Every `Ty` occurrence becomes a
   `TyId` into one canonical, duplicate-free `TypeTable.types`, and every
   structural `RigidTy` (children before parents) is interned into
   `TypeTable.kinds`, pre-seeded with `()`, `bool`, `usize` at `KindId`s
   `0`, `1`, `2`.
3. **Demand-time `LayoutQuery`** (`evalLayoutQuery`): every reference-machine
   layout hook is answered on demand from `(TypeTable, LayoutTable)`; nothing
   is pre-materialized, and dangling identifiers fail closed (`missingHook`).
4. **Shared byte-level machine** (`PState`: frames of local slots, a heap of
   real `AbstractByte`s, a Tree Borrows table of real `BorrowEntry`s updated
   with Trusted's `treeBorrowNodeAccess`, and LeanMiri's `pendingMoveDeinit`
   latch). `M_anneal` (`annealStep`, `annealObs`) deinitializes moved places
   eagerly; `M_ref` (`refStepCore`, `refObs`) runs LeanMiri's two-phase
   protocol (`evalOperand` sets the latch, `readImmediate` /
   `copyRuntimePlaceNoValidate` consume it) on `encodeProg p`, resolving types
   through `evalLayoutQuery`.
5. **Top-level claims**: `CodecRoundtripClaim`,
   `LayoutQueryCorrespondenceClaim`, `CorrespondenceClaim`,
   `FaultEquivalenceClaim`, `MiriMoveDeinitWiringClaim`, and
   `TrustedProjectedMoveDeinitClaim` (a live bridge to
   `Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand` and `evalOperands`).
-/

namespace Trusted.Correspondence

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

set_option linter.constructorNameAsVariable false

/-! ## Part 0 — Structural Boolean equality on the `V2026_06_01` type syntax -/

/-- Boolean equality on calling conventions (`CallConv.other` compares names). -/
def callConvBEq : CallConv → CallConv → Bool
  | .rust, .rust => true
  | .c, .c => true
  | .rustIntrinsic, .rustIntrinsic => true
  | .other a, .other b => decide (a = b)
  | _, _ => false

mutual
/-- Structural Boolean equality on `RigidTy`: the constructors agree and every
field agrees (children compared recursively). Integer, float, mutability and
safety tags are compared with Trusted's `intTyEq`, `uintTyEq`, `floatTyEq`,
`mutabilityEq` and `safetyEq`. -/
def rigidTyBEq : RigidTy → RigidTy → Bool
  | .param i n, .param j m => decide (i = j) && decide (n = m)
  | .alias p a, .alias q b => decide (p = q) && rigidTyListBEq a b
  | .bool, .bool => true
  | .char, .char => true
  | .int w, .int v => intTyEq w v
  | .uint w, .uint v => uintTyEq w v
  | .float w, .float v => floatTyEq w v
  | .never, .never => true
  | .str, .str => true
  | .tuple a, .tuple b => rigidTyListBEq a b
  | .array e n, .array f m => rigidTyBEq e f && decide (n = m)
  | .slice e, .slice f => rigidTyBEq e f
  | .ref m p, .ref n q => mutabilityEq m n && rigidTyBEq p q
  | .rawPtr m p, .rawPtr n q => mutabilityEq m n && rigidTyBEq p q
  | .adt p a, .adt q b => decide (p = q) && rigidTyListBEq a b
  | .fnDef p a, .fnDef q b => decide (p = q) && rigidTyListBEq a b
  | .fnPtr i o s cc, .fnPtr j p t dd =>
      rigidTyListBEq i j && rigidTyBEq o p && safetyEq s t && callConvBEq cc dd
  | .closure p a, .closure q b => decide (p = q) && rigidTyListBEq a b
  | .dynamic p, .dynamic q => decide (p = q)
  | .foreign p, .foreign q => decide (p = q)
  | .other r, .other s => decide (r = s)
  | _, _ => false
/-- Pointwise structural Boolean equality on `List RigidTy` (equal lengths). -/
def rigidTyListBEq : List RigidTy → List RigidTy → Bool
  | [], [] => true
  | a :: as, b :: bs => rigidTyBEq a b && rigidTyListBEq as bs
  | _, _ => false
end

/-- Structural Boolean equality on `Ty`: equal structural kind and equal
compiler `LayoutIdx`. -/
def tyBEq (a b : Ty) : Bool :=
  rigidTyBEq a.kind b.kind && decide (a.layoutIdx = b.layoutIdx)

/-- Boolean equality on `DefPath`s (string equality). -/
def defPathBEq (a b : DefPath) : Bool := decide (a = b)

/-! ## Part 1 — List helpers and canonical interning -/

/-- Structural `0`-based list lookup (`none` when out of bounds). -/
def nth? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => nth? xs n

/-- Generic list decoder: decode every element with `f`, failing if any
element fails. -/
def decodeList {α β : Type} (f : β → Option α) : List β → Option (List α)
  | [] => some []
  | b :: bs =>
    match f b, decodeList f bs with
    | some a, some as => some (a :: as)
    | _, _ => none

/-- First index of `a` in `xs` under the Boolean equality `eq`. -/
def indexOf? {α : Type} (eq : α → α → Bool) : List α → α → Option Nat
  | [], _ => none
  | x :: xs, a =>
    match eq x a with
    | true => some 0
    | false => (indexOf? eq xs a).map (· + 1)

/-- Append `a` to `xs` unless an `eq`-equal entry is already present
(canonical interning: existing entries never move). -/
def insertIfAbsent {α : Type} (eq : α → α → Bool) (a : α) : List α → List α
  | [] => [a]
  | x :: xs =>
    match eq x a with
    | true => x :: xs
    | false => x :: insertIfAbsent eq a xs

/-- Intern every element of the second list, left to right, into the first. -/
def insertAll {α : Type} (eq : α → α → Bool) : List α → List α → List α
  | acc, [] => acc
  | acc, y :: ys => insertAll eq (insertIfAbsent eq y acc) ys

/-- Interned identifier of `a` in `xs` (its first index; `0` when absent, which
never happens for interned values). -/
def lookupId {α : Type} (eq : α → α → Bool) (xs : List α) (a : α) : Nat :=
  (indexOf? eq xs a).getD 0

/-- `xs` has no two `eq`-equal entries (`typesAreCanonical` in PR #257). -/
def typesAreCanonical {α : Type} (eq : α → α → Bool) : List α → Bool
  | [] => true
  | x :: xs => (indexOf? eq xs x).isNone && typesAreCanonical eq xs

/-! ## Part 2 — Type tables and bottom-up (post-order) kind interning -/

/-- Interned `Ty` identifier (`Miri.MIR.TyId`): an index into
`TypeTable.types`. -/
abbrev TyId := Nat

/-- Interned structural `RigidTy` identifier: an index into `TypeTable.kinds`. -/
abbrev KindId := Nat

/-- The single source of truth for the types of a `RefProg`: `kinds` interns
every structural `RigidTy` (children before parents) and `types` interns every
`Ty` occurrence (structural kind plus compiler `LayoutIdx`). -/
structure TypeTable where
  /-- Canonical structural kinds, bottom-up (post-order). -/
  kinds : List RigidTy
  /-- Canonical `Ty` entries indexed by `TyId`. -/
  types : List Ty

mutual
/-- Post-order (children first) enumeration of a kind and all of its
structural sub-kinds. -/
def rigidTyPostorder : RigidTy → List RigidTy
  | .param i n => [.param i n]
  | .alias p a => rigidTyPostorderList a ++ [.alias p a]
  | .bool => [.bool]
  | .char => [.char]
  | .int w => [.int w]
  | .uint w => [.uint w]
  | .float w => [.float w]
  | .never => [.never]
  | .str => [.str]
  | .tuple a => rigidTyPostorderList a ++ [.tuple a]
  | .array e n => rigidTyPostorder e ++ [.array e n]
  | .slice e => rigidTyPostorder e ++ [.slice e]
  | .ref m p => rigidTyPostorder p ++ [.ref m p]
  | .rawPtr m p => rigidTyPostorder p ++ [.rawPtr m p]
  | .adt p a => rigidTyPostorderList a ++ [.adt p a]
  | .fnDef p a => rigidTyPostorderList a ++ [.fnDef p a]
  | .fnPtr i o s cc => rigidTyPostorderList i ++ rigidTyPostorder o ++ [.fnPtr i o s cc]
  | .closure p a => rigidTyPostorderList a ++ [.closure p a]
  | .dynamic p => [.dynamic p]
  | .foreign p => [.foreign p]
  | .other r => [.other r]
/-- Post-order enumeration of a list of kinds. -/
def rigidTyPostorderList : List RigidTy → List RigidTy
  | [] => []
  | k :: ks => rigidTyPostorder k ++ rigidTyPostorderList ks
end

/-- Intern a `Ty`: all of its structural kinds bottom-up into `kinds`, then the
`Ty` itself into `types`. -/
def internTy (tt : TypeTable) (ty : Ty) : TypeTable :=
  { kinds := insertAll rigidTyBEq tt.kinds (rigidTyPostorder ty.kind)
    types := insertIfAbsent tyBEq ty tt.types }

/-- Intern a list of `Ty` occurrences left to right. -/
def internTys : TypeTable → List Ty → TypeTable
  | tt, [] => tt
  | tt, ty :: tys => internTys (internTy tt ty) tys

/-- Pre-seeded built-in kinds (`KindId` `0 = ()`, `1 = bool`, `2 = usize`) for
`ExecutionMachine`'s `unitLayout` / `boolLayout` / `usizeLayout` queries. -/
def initTypeTable : TypeTable :=
  { kinds := [.tuple [], .bool, .uint .usize], types := [] }

/-- Table extension: both tables grow only by appending. -/
def TypeTable.Extends (tt tt' : TypeTable) : Prop :=
  (∃ l, tt'.kinds = tt.kinds ++ l) ∧ (∃ l, tt'.types = tt.types ++ l)

/-- Table invariant: both tables are canonical (duplicate-free), and every
interned `Ty` has its kind and all of its kind's structural sub-kinds
interned in `kinds`. -/
def TypeTable.Good (tt : TypeTable) : Prop :=
  typesAreCanonical rigidTyBEq tt.kinds = true ∧ typesAreCanonical tyBEq tt.types = true ∧
  ∀ ty ∈ tt.types, rigidTyPostorder ty.kind ⊆ tt.kinds

/-- Intern a list of structural `RigidTy`s (bottom-up post-order) into `kinds`
without adding `Ty` entries (used for `CapturedMir.traitImpls` type
arguments). -/
def internKinds (tt : TypeTable) (ks : List RigidTy) : TypeTable :=
  { kinds := insertAll rigidTyBEq tt.kinds (rigidTyPostorderList ks), types := tt.types }

/-- Encode a `Ty` as its interned `TyId`. -/
def encodeType (tt : TypeTable) (ty : Ty) : TyId := lookupId tyBEq tt.types ty

/-- Decode a `TyId` (fails closed on out-of-bounds identifiers). -/
def decodeType (tt : TypeTable) (t : TyId) : Option Ty := nth? tt.types t

/-! ## Part 3 — Reference-indexed `V2026_06_01` syntax (`RefProg`) -/

/-- `ProjectionElem` with every `Ty` replaced by a `TyId`. -/
inductive RefProjectionElem : Type where
  | deref : RefProjectionElem
  | field (field : FieldIdx) (ty : TyId) : RefProjectionElem
  | index (idx : Local) : RefProjectionElem
  | constantIndex (offset : Nat) (minLength : Nat) (fromEnd : Bool) : RefProjectionElem
  | subslice (fromIdx : Nat) (toIdx : Nat) (fromEnd : Bool) : RefProjectionElem
  | downcast (variantName : Option String) (variant : VariantIdx) : RefProjectionElem
  | opaqueCast (ty : TyId) : RefProjectionElem
  | unwrapUnsafeBinder (ty : TyId) : RefProjectionElem

/-- Reference place. -/
structure RefPlace : Type where
  local_ : Local
  projection : List RefProjectionElem

/-- Reference constant operand. -/
structure RefConstOperand : Type where
  ty : TyId
  val : ConstValue

/-- Reference operand. -/
inductive RefOperand : Type where
  | copy (place : RefPlace) : RefOperand
  | move (place : RefPlace) : RefOperand
  | constant (c : RefConstOperand) : RefOperand

/-- Reference aggregate kind. -/
inductive RefAggregateKind : Type where
  | array (elemTy : TyId) : RefAggregateKind
  | tuple : RefAggregateKind
  | adt (defPath : DefPath) (variantIdx : VariantIdx) (activeField : Option FieldIdx) :
      RefAggregateKind
  | closure (defPath : DefPath) : RefAggregateKind
  | coroutine (defPath : DefPath) : RefAggregateKind
  | rawPtr (pointeeTy : TyId) (mutability : Mutability) : RefAggregateKind

/-- Reference rvalue (all 15 `Rvalue` constructors). -/
inductive RefRvalue : Type where
  | use (op : RefOperand) : RefRvalue
  | repeat (op : RefOperand) (count : Nat) : RefRvalue
  | ref (borrowKind : BorrowKind) (place : RefPlace) : RefRvalue
  | threadLocalRef (defPath : DefPath) : RefRvalue
  | rawPtr (mutability : Mutability) (place : RefPlace) : RefRvalue
  | len (place : RefPlace) : RefRvalue
  | cast (kind : CastKind) (op : RefOperand) (targetTy : TyId) : RefRvalue
  | binaryOp (op : BinOp) (lhs : RefOperand) (rhs : RefOperand) : RefRvalue
  | nullaryOp (op : NullOp) (ty : TyId) : RefRvalue
  | unaryOp (op : UnOp) (val : RefOperand) : RefRvalue
  | discriminant (place : RefPlace) : RefRvalue
  | aggregate (kind : RefAggregateKind) (operands : List RefOperand) : RefRvalue
  | shallowInitBox (op : RefOperand) (contentTy : TyId) : RefRvalue
  | copyForDeref (place : RefPlace) : RefRvalue
  | wrapUnsafeBinder (op : RefOperand) (targetTy : TyId) : RefRvalue

/-- Reference non-diverging intrinsic. -/
inductive RefNonDivergingIntrinsic : Type where
  | assume (op : RefOperand) : RefNonDivergingIntrinsic
  | copyNonOverlapping (src : RefOperand) (dst : RefOperand) (count : RefOperand) :
      RefNonDivergingIntrinsic

/-- Reference statement kind (all 12 `StatementKind` constructors). -/
inductive RefStatementKind : Type where
  | assign (place : RefPlace) (rvalue : RefRvalue) : RefStatementKind
  | setDiscriminant (place : RefPlace) (variantIdx : VariantIdx) : RefStatementKind
  | deinit (place : RefPlace) : RefStatementKind
  | storageLive (local_ : Local) : RefStatementKind
  | storageDead (local_ : Local) : RefStatementKind
  | retag (kind : RetagKind) (place : RefPlace) : RefStatementKind
  | placeMention (place : RefPlace) : RefStatementKind
  | intrinsic (intrinsic : RefNonDivergingIntrinsic) : RefStatementKind
  | coverage : RefStatementKind
  | constEvalCounter : RefStatementKind
  | backwardIncompatibleDropHint (place : RefPlace) : RefStatementKind
  | nop : RefStatementKind

/-- Reference statement. -/
structure RefStatement : Type where
  kind : RefStatementKind
  span : String

/-- Reference terminator kind (all 11 `TerminatorKind` constructors). -/
inductive RefTerminatorKind : Type where
  | goto (target : BasicBlockIdx) : RefTerminatorKind
  | switchInt (discr : RefOperand) (targets : SwitchTargets) : RefTerminatorKind
  | unwindResume : RefTerminatorKind
  | unwindTerminate : RefTerminatorKind
  | return_ : RefTerminatorKind
  | unreachable : RefTerminatorKind
  | drop (place : RefPlace) (target : BasicBlockIdx) (unwind : UnwindAction) : RefTerminatorKind
  | call (func : RefOperand) (args : List RefOperand) (destination : RefPlace)
      (target : Option BasicBlockIdx) (unwind : UnwindAction) : RefTerminatorKind
  | tailCall (func : RefOperand) (args : List RefOperand) : RefTerminatorKind
  | assert (cond : RefOperand) (expected : Bool) (target : BasicBlockIdx)
      (unwind : UnwindAction) : RefTerminatorKind
  | inlineAsm (template : String) (targets : List BasicBlockIdx) (unwind : UnwindAction) :
      RefTerminatorKind

/-- Reference terminator. -/
structure RefTerminator : Type where
  kind : RefTerminatorKind
  span : String

/-- Reference basic block. -/
structure RefBasicBlock : Type where
  statements : List RefStatement
  terminator : RefTerminator
  isCleanup : Bool

/-- Reference local declaration. -/
structure RefLocalDecl : Type where
  mutability : Mutability
  ty : TyId
  debugName : Option String

/-- Reference body: every `CapturedMir` field, with `TyId`-indexed syntax. -/
structure RefBody : Type where
  defPath : DefPath
  phase : MirPhaseTag
  role : ContractRole
  argCount : Nat
  localDecls : List RefLocalDecl
  basicBlocks : List RefBasicBlock
  fnAbi : FnAbi
  layouts : LayoutTable
  allocations : List CapturedAllocation
  typeParamCount : Nat
  genericParams : List GenericParamDef
  traitImpls : List TraitImplEntry

/-- Multi-body `V2026_06_01` program (`M_anneal` input): bodies and the entry
body index. -/
structure V2026Prog : Type where
  bodies : List CapturedMir
  entry : Nat

/-- Multi-body reference program (`M_ref` input) with one shared type table. -/
structure RefProg : Type where
  bodies : List RefBody
  entry : Nat
  types : TypeTable

/-! ### `Ty` occurrences of every syntax node -/

/-- `Ty` occurrences of a projection element. -/
def projElemTys : ProjectionElem → List Ty
  | .field _ ty => [ty]
  | .opaqueCast ty => [ty]
  | .unwrapUnsafeBinder ty => [ty]
  | _ => []

/-- `Ty` occurrences of a place. -/
def placeTys (p : Place) : List Ty := p.projection.flatMap projElemTys

/-- `Ty` occurrences of an operand. -/
def operandTys : Operand → List Ty
  | .copy p => placeTys p
  | .move p => placeTys p
  | .constant c => [c.ty]

/-- `Ty` occurrences of an aggregate kind. -/
def aggKindTys : AggregateKind → List Ty
  | .array t => [t]
  | .rawPtr t _ => [t]
  | _ => []

/-- `Ty` occurrences of an rvalue. -/
def rvalueTys : Rvalue → List Ty
  | .use op => operandTys op
  | .repeat op _ => operandTys op
  | .ref _ p => placeTys p
  | .threadLocalRef _ => []
  | .rawPtr _ p => placeTys p
  | .len p => placeTys p
  | .cast _ op t => operandTys op ++ [t]
  | .binaryOp _ l r => operandTys l ++ operandTys r
  | .nullaryOp _ t => [t]
  | .unaryOp _ op => operandTys op
  | .discriminant p => placeTys p
  | .aggregate k ops => aggKindTys k ++ ops.flatMap operandTys
  | .shallowInitBox op t => operandTys op ++ [t]
  | .copyForDeref p => placeTys p
  | .wrapUnsafeBinder op t => operandTys op ++ [t]

/-- `Ty` occurrences of a non-diverging intrinsic. -/
def intrinsicTys : NonDivergingIntrinsic → List Ty
  | .assume op => operandTys op
  | .copyNonOverlapping a b c => operandTys a ++ operandTys b ++ operandTys c

/-- `Ty` occurrences of a statement kind. -/
def stmtKindTys : StatementKind → List Ty
  | .assign p rv => placeTys p ++ rvalueTys rv
  | .setDiscriminant p _ => placeTys p
  | .deinit p => placeTys p
  | .storageLive _ => []
  | .storageDead _ => []
  | .retag _ p => placeTys p
  | .placeMention p => placeTys p
  | .intrinsic i => intrinsicTys i
  | .coverage => []
  | .constEvalCounter => []
  | .backwardIncompatibleDropHint p => placeTys p
  | .nop => []

/-- `Ty` occurrences of a statement. -/
def stmtTys (s : Statement) : List Ty := stmtKindTys s.kind

/-- `Ty` occurrences of a terminator kind. -/
def termKindTys : TerminatorKind → List Ty
  | .goto _ => []
  | .switchInt d _ => operandTys d
  | .unwindResume => []
  | .unwindTerminate => []
  | .return_ => []
  | .unreachable => []
  | .drop p _ _ => placeTys p
  | .call f args d _ _ => operandTys f ++ args.flatMap operandTys ++ placeTys d
  | .tailCall f args => operandTys f ++ args.flatMap operandTys
  | .assert c _ _ _ => operandTys c
  | .inlineAsm _ _ _ => []

/-- `Ty` occurrences of a basic block. -/
def blockTys (b : BasicBlockData) : List Ty :=
  b.statements.flatMap stmtTys ++ termKindTys b.terminator.kind

/-- `Ty` occurrences of a body (local declarations, then basic blocks). -/
def bodyTys (b : CapturedMir) : List Ty :=
  b.localDecls.map LocalDecl.ty ++ b.basicBlocks.flatMap blockTys

/-- `Ty` occurrences of a program. -/
def progTys (p : V2026Prog) : List Ty := p.bodies.flatMap bodyTys

/-- Structural `RigidTy` arguments appearing in `CapturedMir.traitImpls`. -/
def bodyTraitKinds (b : CapturedMir) : List RigidTy :=
  b.traitImpls.flatMap (fun ti => ti.traitRef.args)

/-- Structural `RigidTy` trait-impl arguments of a program. -/
def progTraitKinds (p : V2026Prog) : List RigidTy :=
  p.bodies.flatMap bodyTraitKinds

/-! ### Encoder -/

/-- Encode a projection element. -/
def encodeProjElem (tt : TypeTable) : ProjectionElem → RefProjectionElem
  | .deref => .deref
  | .field f ty => .field f (encodeType tt ty)
  | .index i => .index i
  | .constantIndex o m e => .constantIndex o m e
  | .subslice f t e => .subslice f t e
  | .downcast n v => .downcast n v
  | .opaqueCast ty => .opaqueCast (encodeType tt ty)
  | .unwrapUnsafeBinder ty => .unwrapUnsafeBinder (encodeType tt ty)

/-- Encode a place. -/
def encodePlace (tt : TypeTable) (p : Place) : RefPlace :=
  ⟨p.local_, p.projection.map (encodeProjElem tt)⟩

/-- Encode an operand. -/
def encodeOperand (tt : TypeTable) : Operand → RefOperand
  | .copy p => .copy (encodePlace tt p)
  | .move p => .move (encodePlace tt p)
  | .constant c => .constant ⟨encodeType tt c.ty, c.val⟩

/-- Encode an aggregate kind. -/
def encodeAggKind (tt : TypeTable) : AggregateKind → RefAggregateKind
  | .array t => .array (encodeType tt t)
  | .tuple => .tuple
  | .adt p v f => .adt p v f
  | .closure p => .closure p
  | .coroutine p => .coroutine p
  | .rawPtr t m => .rawPtr (encodeType tt t) m

/-- Encode an rvalue. -/
def encodeRvalue (tt : TypeTable) : Rvalue → RefRvalue
  | .use op => .use (encodeOperand tt op)
  | .repeat op n => .repeat (encodeOperand tt op) n
  | .ref bk p => .ref bk (encodePlace tt p)
  | .threadLocalRef d => .threadLocalRef d
  | .rawPtr m p => .rawPtr m (encodePlace tt p)
  | .len p => .len (encodePlace tt p)
  | .cast k op t => .cast k (encodeOperand tt op) (encodeType tt t)
  | .binaryOp o l r => .binaryOp o (encodeOperand tt l) (encodeOperand tt r)
  | .nullaryOp o t => .nullaryOp o (encodeType tt t)
  | .unaryOp o op => .unaryOp o (encodeOperand tt op)
  | .discriminant p => .discriminant (encodePlace tt p)
  | .aggregate k ops => .aggregate (encodeAggKind tt k) (ops.map (encodeOperand tt))
  | .shallowInitBox op t => .shallowInitBox (encodeOperand tt op) (encodeType tt t)
  | .copyForDeref p => .copyForDeref (encodePlace tt p)
  | .wrapUnsafeBinder op t => .wrapUnsafeBinder (encodeOperand tt op) (encodeType tt t)

/-- Encode a non-diverging intrinsic. -/
def encodeIntrinsic (tt : TypeTable) : NonDivergingIntrinsic → RefNonDivergingIntrinsic
  | .assume op => .assume (encodeOperand tt op)
  | .copyNonOverlapping a b c =>
    .copyNonOverlapping (encodeOperand tt a) (encodeOperand tt b) (encodeOperand tt c)

/-- Encode a statement kind. -/
def encodeStmtKind (tt : TypeTable) : StatementKind → RefStatementKind
  | .assign p rv => .assign (encodePlace tt p) (encodeRvalue tt rv)
  | .setDiscriminant p v => .setDiscriminant (encodePlace tt p) v
  | .deinit p => .deinit (encodePlace tt p)
  | .storageLive l => .storageLive l
  | .storageDead l => .storageDead l
  | .retag k p => .retag k (encodePlace tt p)
  | .placeMention p => .placeMention (encodePlace tt p)
  | .intrinsic i => .intrinsic (encodeIntrinsic tt i)
  | .coverage => .coverage
  | .constEvalCounter => .constEvalCounter
  | .backwardIncompatibleDropHint p => .backwardIncompatibleDropHint (encodePlace tt p)
  | .nop => .nop

/-- Encode a statement. -/
def encodeStmt (tt : TypeTable) (s : Statement) : RefStatement :=
  ⟨encodeStmtKind tt s.kind, s.span⟩

/-- Encode a terminator kind. -/
def encodeTermKind (tt : TypeTable) : TerminatorKind → RefTerminatorKind
  | .goto t => .goto t
  | .switchInt d ts => .switchInt (encodeOperand tt d) ts
  | .unwindResume => .unwindResume
  | .unwindTerminate => .unwindTerminate
  | .return_ => .return_
  | .unreachable => .unreachable
  | .drop p t u => .drop (encodePlace tt p) t u
  | .call f args d t u =>
    .call (encodeOperand tt f) (args.map (encodeOperand tt)) (encodePlace tt d) t u
  | .tailCall f args => .tailCall (encodeOperand tt f) (args.map (encodeOperand tt))
  | .assert c e t u => .assert (encodeOperand tt c) e t u
  | .inlineAsm s ts u => .inlineAsm s ts u

/-- Encode a terminator. -/
def encodeTerminator (tt : TypeTable) (t : Terminator) : RefTerminator :=
  ⟨encodeTermKind tt t.kind, t.span⟩

/-- Encode a basic block. -/
def encodeBlock (tt : TypeTable) (b : BasicBlockData) : RefBasicBlock :=
  ⟨b.statements.map (encodeStmt tt), encodeTerminator tt b.terminator, b.isCleanup⟩

/-- Encode a local declaration. -/
def encodeLocalDecl (tt : TypeTable) (d : LocalDecl) : RefLocalDecl :=
  ⟨d.mutability, encodeType tt d.ty, d.debugName⟩

/-- Encode a body (every non-type field is copied unchanged). -/
def encodeBody (tt : TypeTable) (b : CapturedMir) : RefBody :=
  { defPath := b.defPath, phase := b.phase, role := b.role, argCount := b.argCount
    localDecls := b.localDecls.map (encodeLocalDecl tt)
    basicBlocks := b.basicBlocks.map (encodeBlock tt)
    fnAbi := b.fnAbi, layouts := b.layouts, allocations := b.allocations
    typeParamCount := b.typeParamCount, genericParams := b.genericParams
    traitImpls := b.traitImpls }

/-- The program's canonical type table: starting from `initTypeTable`, intern
every `Ty` occurrence (`progTys`), then every `CapturedMir.traitImpls`
`RigidTy` argument, all in bottom-up post-order. -/
def collectProgTypes (p : V2026Prog) : TypeTable :=
  internKinds (internTys initTypeTable (progTys p)) (progTraitKinds p)

/-- Total encoder `V2026Prog → RefProg`. -/
def encodeProg (p : V2026Prog) : RefProg :=
  let tt := collectProgTypes p
  ⟨p.bodies.map (encodeBody tt), p.entry, tt⟩

/-! ### Decoder -/

/-- Decode a projection element. -/
def decodeProjElem (tt : TypeTable) : RefProjectionElem → Option ProjectionElem
  | .deref => some .deref
  | .field f t => (decodeType tt t).map (.field f)
  | .index i => some (.index i)
  | .constantIndex o m e => some (.constantIndex o m e)
  | .subslice f t e => some (.subslice f t e)
  | .downcast n v => some (.downcast n v)
  | .opaqueCast t => (decodeType tt t).map .opaqueCast
  | .unwrapUnsafeBinder t => (decodeType tt t).map .unwrapUnsafeBinder

/-- Decode a place. -/
def decodePlace (tt : TypeTable) (p : RefPlace) : Option Place :=
  (decodeList (decodeProjElem tt) p.projection).map (fun proj => ⟨p.local_, proj⟩)

/-- Decode an operand. -/
def decodeOperand (tt : TypeTable) : RefOperand → Option Operand
  | .copy p => (decodePlace tt p).map .copy
  | .move p => (decodePlace tt p).map .move
  | .constant c => (decodeType tt c.ty).map (fun ty => .constant ⟨ty, c.val⟩)

/-- Decode an aggregate kind. -/
def decodeAggKind (tt : TypeTable) : RefAggregateKind → Option AggregateKind
  | .array t => (decodeType tt t).map .array
  | .tuple => some .tuple
  | .adt p v f => some (.adt p v f)
  | .closure p => some (.closure p)
  | .coroutine p => some (.coroutine p)
  | .rawPtr t m => (decodeType tt t).map (fun ty => .rawPtr ty m)

/-- Decode an rvalue. -/
def decodeRvalue (tt : TypeTable) : RefRvalue → Option Rvalue
  | .use op => (decodeOperand tt op).map .use
  | .repeat op n => (decodeOperand tt op).map (fun o => .repeat o n)
  | .ref bk p => (decodePlace tt p).map (.ref bk)
  | .threadLocalRef d => some (.threadLocalRef d)
  | .rawPtr m p => (decodePlace tt p).map (.rawPtr m)
  | .len p => (decodePlace tt p).map .len
  | .cast k op t =>
    (decodeOperand tt op).bind (fun o => (decodeType tt t).map (fun ty => .cast k o ty))
  | .binaryOp o l r =>
    (decodeOperand tt l).bind (fun l' => (decodeOperand tt r).map (fun r' => .binaryOp o l' r'))
  | .nullaryOp o t => (decodeType tt t).map (.nullaryOp o)
  | .unaryOp o op => (decodeOperand tt op).map (.unaryOp o)
  | .discriminant p => (decodePlace tt p).map .discriminant
  | .aggregate k ops =>
    (decodeAggKind tt k).bind (fun k' => (decodeList (decodeOperand tt) ops).map (.aggregate k'))
  | .shallowInitBox op t =>
    (decodeOperand tt op).bind (fun o => (decodeType tt t).map (fun ty => .shallowInitBox o ty))
  | .copyForDeref p => (decodePlace tt p).map .copyForDeref
  | .wrapUnsafeBinder op t =>
    (decodeOperand tt op).bind (fun o => (decodeType tt t).map (fun ty => .wrapUnsafeBinder o ty))

/-- Decode a non-diverging intrinsic. -/
def decodeIntrinsic (tt : TypeTable) : RefNonDivergingIntrinsic → Option NonDivergingIntrinsic
  | .assume op => (decodeOperand tt op).map .assume
  | .copyNonOverlapping a b c =>
    (decodeOperand tt a).bind (fun a' => (decodeOperand tt b).bind (fun b' =>
      (decodeOperand tt c).map (fun c' => .copyNonOverlapping a' b' c')))

/-- Decode a statement kind. -/
def decodeStmtKind (tt : TypeTable) : RefStatementKind → Option StatementKind
  | .assign p rv => (decodePlace tt p).bind (fun p' => (decodeRvalue tt rv).map (.assign p'))
  | .setDiscriminant p v => (decodePlace tt p).map (fun p' => .setDiscriminant p' v)
  | .deinit p => (decodePlace tt p).map .deinit
  | .storageLive l => some (.storageLive l)
  | .storageDead l => some (.storageDead l)
  | .retag k p => (decodePlace tt p).map (.retag k)
  | .placeMention p => (decodePlace tt p).map .placeMention
  | .intrinsic i => (decodeIntrinsic tt i).map .intrinsic
  | .coverage => some .coverage
  | .constEvalCounter => some .constEvalCounter
  | .backwardIncompatibleDropHint p => (decodePlace tt p).map .backwardIncompatibleDropHint
  | .nop => some .nop

/-- Decode a statement. -/
def decodeStmt (tt : TypeTable) (s : RefStatement) : Option Statement :=
  (decodeStmtKind tt s.kind).map (fun k => ⟨k, s.span⟩)

/-- Decode a terminator kind. -/
def decodeTermKind (tt : TypeTable) : RefTerminatorKind → Option TerminatorKind
  | .goto t => some (.goto t)
  | .switchInt d ts => (decodeOperand tt d).map (fun d' => .switchInt d' ts)
  | .unwindResume => some .unwindResume
  | .unwindTerminate => some .unwindTerminate
  | .return_ => some .return_
  | .unreachable => some .unreachable
  | .drop p t u => (decodePlace tt p).map (fun p' => .drop p' t u)
  | .call f args d t u =>
    (decodeOperand tt f).bind (fun f' => (decodeList (decodeOperand tt) args).bind (fun a' =>
      (decodePlace tt d).map (fun d' => .call f' a' d' t u)))
  | .tailCall f args =>
    (decodeOperand tt f).bind (fun f' => (decodeList (decodeOperand tt) args).map (.tailCall f'))
  | .assert c e t u => (decodeOperand tt c).map (fun c' => .assert c' e t u)
  | .inlineAsm s ts u => some (.inlineAsm s ts u)

/-- Decode a terminator. -/
def decodeTerminator (tt : TypeTable) (t : RefTerminator) : Option Terminator :=
  (decodeTermKind tt t.kind).map (fun k => ⟨k, t.span⟩)

/-- Decode a basic block. -/
def decodeBlock (tt : TypeTable) (b : RefBasicBlock) : Option BasicBlockData :=
  (decodeList (decodeStmt tt) b.statements).bind (fun ss =>
    (decodeTerminator tt b.terminator).map (fun t => ⟨ss, t, b.isCleanup⟩))

/-- Decode a local declaration. -/
def decodeLocalDecl (tt : TypeTable) (d : RefLocalDecl) : Option LocalDecl :=
  (decodeType tt d.ty).map (fun ty => ⟨d.mutability, ty, d.debugName⟩)

/-- Decode a body. -/
def decodeBody (tt : TypeTable) (b : RefBody) : Option CapturedMir :=
  (decodeList (decodeLocalDecl tt) b.localDecls).bind (fun ds =>
    (decodeList (decodeBlock tt) b.basicBlocks).map (fun bbs =>
      { defPath := b.defPath, phase := b.phase, role := b.role, argCount := b.argCount
        localDecls := ds, basicBlocks := bbs, fnAbi := b.fnAbi, layouts := b.layouts
        allocations := b.allocations, typeParamCount := b.typeParamCount
        genericParams := b.genericParams, traitImpls := b.traitImpls }))

/-- Total decoder (fails closed on dangling `TyId`s). -/
def decodeProg (rp : RefProg) : Option V2026Prog :=
  (decodeList (decodeBody rp.types) rp.bodies).map (fun bs => ⟨bs, rp.entry⟩)

/-! ## Part 4 — Demand-time `LayoutQuery` hook (`proofs-rs/lean-miri#64`)

`MiriRefMachine`'s `localLayout`, `scalarTypeClass`, `castTypeInfo`,
`pointeeTypes`, and `retagTypeShape` hooks are answered *on demand* from the
single source `(TypeTable, LayoutTable)`; nothing is pre-materialized. -/

/-- Scalar classification used by `scalarTypeClass` / `castTypeInfo`. -/
inductive ScalarClass : Type where
  | bool | char | int (signed : Bool) | float | ptr | unit
  deriving DecidableEq

/-- Scalar class of a kind (`none` for aggregates). -/
def scalarClassOfKind : RigidTy → Option ScalarClass
  | .bool => some .bool
  | .char => some .char
  | .int _ => some (.int true)
  | .uint _ => some (.int false)
  | .float _ => some .float
  | .ref _ _ => some .ptr
  | .rawPtr _ _ => some .ptr
  | .fnPtr _ _ _ _ => some .ptr
  | .tuple [] => some .unit
  | _ => none

/-- Retag shape (`retagTypeShape`). -/
inductive RetagShape : Type where
  | none | sharedRef (freeze : Bool) | mutRef | rawPtr
  deriving DecidableEq

/-- Retag shape of a kind (shared references record whether their pointee is
`Freeze`, via Trusted's `rigidTyIsFreeze`). -/
def retagShapeOfKind : RigidTy → RetagShape
  | .ref .not p => .sharedRef (rigidTyIsFreeze defaultTyEqFuel p)
  | .ref .mut _ => .mutRef
  | .rawPtr _ _ => .rawPtr
  | _ => .none

/-- Table-independent synthesized layout (via Trusted's `RigidTy.computeLayout`),
used for pointees, array elements and sub-slices. -/
def pointeeLayoutOf (ptrBits : Nat) (k : RigidTy) : Option TypeLayout :=
  RigidTy.computeLayout ptrBits [] [] .none k

/-- Demand-time layout queries. -/
inductive LayoutQuery : Type where
  | localLayout (ty : TyId)
  | scalarTypeClass (ty : TyId)
  | castTypeInfo (src dst : TyId)
  | pointeeTypes (ty : TyId)
  | retagTypeShape (ty : TyId)
  | builtinLayout (k : KindId)

/-- Layout-query answers. -/
inductive LayoutAnswer : Type where
  | layout (kind : RigidTy) (l : TypeLayout)
  | scalar (c : ScalarClass) (sizeBytes : Nat)
  | cast (src dst : ScalarClass) (srcBytes dstBytes : Nat)
  | pointee (kind : KindId) (layout : Option TypeLayout)
  | retag (s : RetagShape)

/-- Results: answers, or fail-closed `missingHook` (dangling `TyId` /
`LayoutIdx` / un-interned pointee) and `blocked` (query not applicable). -/
inductive LayoutResult : Type where
  | ok (a : LayoutAnswer)
  | missingHook
  | blocked

/-- Single-source lookup of a `TyId`'s `Ty` and its compiler layout. -/
def tyLayout (tt : TypeTable) (L : LayoutTable) (t : TyId) : Option (Ty × TypeLayout) :=
  match nth? tt.types t with
  | none => none
  | some ty =>
    match nth? L.entries ty.layoutIdx with
    | none => none
    | some l => some (ty, l)

/-- The demand-time query evaluator. -/
def evalLayoutQuery (tt : TypeTable) (L : LayoutTable) : LayoutQuery → LayoutResult
  | .localLayout t =>
    match tyLayout tt L t with
    | none => .missingHook
    | some (ty, l) => .ok (.layout ty.kind l)
  | .scalarTypeClass t =>
    match tyLayout tt L t with
    | none => .missingHook
    | some (ty, l) =>
      match scalarClassOfKind ty.kind with
      | none => .blocked
      | some c => .ok (.scalar c l.size.bytes)
  | .castTypeInfo s d =>
    match tyLayout tt L s, tyLayout tt L d with
    | some (sty, sl), some (dty, dl) =>
      match scalarClassOfKind sty.kind, scalarClassOfKind dty.kind with
      | some sc, some dc => .ok (.cast sc dc sl.size.bytes dl.size.bytes)
      | _, _ => .blocked
    | _, _ => .missingHook
  | .pointeeTypes t =>
    match nth? tt.types t with
    | none => .missingHook
    | some ty =>
      match ty.kind with
      | .ref _ pk | .rawPtr _ pk =>
        match indexOf? rigidTyBEq tt.kinds pk with
        | none => .missingHook
        | some k => .ok (.pointee k (pointeeLayoutOf L.pointerBits pk))
      | _ => .blocked
  | .retagTypeShape t =>
    match nth? tt.types t with
    | none => .missingHook
    | some ty => .ok (.retag (retagShapeOfKind ty.kind))
  | .builtinLayout k =>
    match nth? tt.kinds k with
    | none => .missingHook
    | some kind =>
      match pointeeLayoutOf L.pointerBits kind with
      | none => .blocked
      | some l => .ok (.layout kind l)

/-- Eager `O(|types|)` pre-materialization (the design `#64` replaces); used
only to state that the demand-time hook refines it pointwise. -/
def eagerLayoutTable (tt : TypeTable) (L : LayoutTable) : List (Option (RigidTy × TypeLayout)) :=
  tt.types.map (fun ty => (nth? L.entries ty.layoutIdx).map (fun l => (ty.kind, l)))

/-! ## Part 5 — Shared byte-level machine (`AbstractByte`, Tree Borrows)

Both `M_anneal` and `M_ref` run on `PState`: frames of local slots
(`imm` = LeanMiri `LocalValue.live (.immediate _)`, `mem` = `.live (.indirect
mplace)`), a byte heap of real `AbstractByte`s, and a Tree Borrows table of
real `BorrowEntry`s updated with Trusted's `treeBorrowNodeAccess`. The field
`pendingMoveDeinit` is LeanMiri's `MachineState.pendingMoveDeinit`
(`MachineHooks.lean`); `M_anneal` never sets it. -/

/-- Raw bytes. -/
abbrev Bytes := List AbstractByte

/-- Undefined-behavior reasons (canaries check *which* UB fires). -/
inductive UBReason : Type where
  | invalidUninitBytes | deadLocal | danglingPointer | outOfBounds | treeBorrows
  | invalidPointer | overlappingCopy | unreachable | divergingReturn | badControlFlow
  deriving DecidableEq

/-- The two fault poles (`.undefined` ↔ `.ub`, `.unsupported` ↔ `.blocked`). -/
inductive Fault : Type where
  | ub (why : UBReason)
  | unsupported
  deriving DecidableEq

/-- Resolved type: structural kind and compiler layout. -/
abbrev SemTy := RigidTy × TypeLayout

/-- Local slot: dead, an immediate byte string, or a memory-backed local living
in heap allocation `alloc`. -/
inductive PSlot : Type where
  | dead
  | imm (b : Bytes)
  | mem (alloc : Nat)

/-- Memory place: allocation, byte window, and access provenance (`none` =
direct access to the local, i.e. through the allocation's root tag). -/
structure MPlace : Type where
  alloc : Nat
  offset : Nat
  size : Nat
  tag : Option Nat

/-- An assignment or call destination, evaluated **before** the rvalue or call
arguments (rustc `eval_rvalue_into_place` / `Call.evalCallTerminator` first
runs `eval_place(dest)`, and `copyRuntimePlaceNoValidate` receives an
already-resolved `RuntimePlace`). -/
inductive DestPlace : Type where
  | imm (l : Local)
  | mem (mp : MPlace)

/-- Call-stack frame (`retDest` caches the pre-resolved caller destination for
`TerminatorKind.call`, matching `Miri.Interpreter.Frame.returnPlace`). -/
structure PFrame : Type where
  body : Nat
  block : Nat
  stmt : Nat
  locals : List PSlot
  retDest : Option DestPlace := none

/-- Shared machine state. -/
structure PState : Type where
  frames : List PFrame
  heap : List (Option Bytes)
  borrows : List BorrowEntry
  nextTag : Nat
  pendingMoveDeinit : Bool

/-- `n` uninitialized bytes. -/
def uninitBytes (n : Nat) : Bytes := List.replicate n .uninit

/-- Point update (`none` when out of bounds). -/
def setNth? {α : Type} : List α → Nat → α → Option (List α)
  | [], _, _ => none
  | _ :: xs, 0, v => some (v :: xs)
  | x :: xs, n + 1, v => (setNth? xs n v).map (x :: ·)

/-- The byte window `[off, off + len)` of `b`. -/
def sliceBytes (b : Bytes) (off len : Nat) : Bytes := (b.drop off).take len

/-- Overwrite `b` with `w` starting at byte `off`. -/
def overwriteBytes (b : Bytes) (off : Nat) (w : Bytes) : Bytes :=
  b.take off ++ w ++ b.drop (off + w.length)

/-- LeanMiri `OpTy`: an already-loaded immediate or a reference to memory. -/
inductive OpTy : Type where
  | immediate (b : Bytes)
  | indirect (mp : MPlace)

/-- Tree Borrows relative position of an access through `tag` w.r.t. `e`
(`none` is the allocation's root tag, foreign to every borrow). -/
def tbRelatedness (all : List BorrowEntry) (tag : Option Nat) (e : BorrowEntry) :
    TreeBorrowRelatedness :=
  match tag with
  | none => .foreignAccess
  | some t =>
    match isBorrowDescendantOrSelf all t e.tag with
    | true => .localAccess
    | false => .foreignAccess

/-- Apply a Tree Borrows access to every entry of the list that overlaps the
window (`none` = undefined behavior). -/
def tbAccessAux (kind : TreeBorrowAccessKind) (all : List BorrowEntry) (alloc : Nat)
    (tag : Option Nat) (off len : Nat) : List BorrowEntry → Option (List BorrowEntry)
  | [] => some []
  | e :: es =>
    match tbAccessAux kind all alloc tag off len es with
    | none => none
    | some es' =>
      match Nat.beq e.targetLocal alloc && byteRangesOverlapBool e.rangeOffset e.rangeLen off len with
      | true =>
        let tr := treeBorrowNodeAccess kind (tbRelatedness all tag e) e.perm false
        match treeBorrowTransitionIsUB tr with
        | true => none
        | false => some (applyTreeBorrowTransition e tr :: es')
      | false => some (e :: es')

/-- Perform a Tree Borrows access of `kind` on every overlapping entry
(`none` = undefined behavior). -/
def tbAccess (kind : TreeBorrowAccessKind) (borrows : List BorrowEntry) (alloc : Nat)
    (tag : Option Nat) (off len : Nat) : Option (List BorrowEntry) :=
  tbAccessAux kind borrows alloc tag off len borrows

/-- Live allocation contents (`none` for dangling / freed allocations). -/
def heapGet (st : PState) (a : Nat) : Option Bytes :=
  match nth? st.heap a with
  | some (some b) => some b
  | _ => none

/-- Replace allocation `a`'s contents. -/
def putHeap (st : PState) (a : Nat) (b : Bytes) : Except Fault PState :=
  match setNth? st.heap a (some b) with
  | none => .error (.ub .danglingPointer)
  | some h => .ok { st with heap := h }

/-- Typed load with a Tree Borrows read access. -/
def loadMPlace (st : PState) (mp : MPlace) : Except Fault (Bytes × PState) :=
  match heapGet st mp.alloc with
  | none => .error (.ub .danglingPointer)
  | some b =>
    match Nat.ble (mp.offset + mp.size) b.length with
    | false => .error (.ub .outOfBounds)
    | true =>
      match tbAccess .read st.borrows mp.alloc mp.tag mp.offset mp.size with
      | none => .error (.ub .treeBorrows)
      | some bs => .ok (sliceBytes b mp.offset mp.size, { st with borrows := bs })

/-- Store with a Tree Borrows **write** access. -/
def storeMPlace (st : PState) (mp : MPlace) (w : Bytes) : Except Fault PState :=
  match heapGet st mp.alloc with
  | none => .error (.ub .danglingPointer)
  | some b =>
    match Nat.ble (mp.offset + mp.size) b.length && Nat.beq w.length mp.size with
    | false => .error (.ub .outOfBounds)
    | true =>
      match tbAccess .write st.borrows mp.alloc mp.tag mp.offset mp.size with
      | none => .error (.ub .treeBorrows)
      | some bs => putHeap { st with borrows := bs } mp.alloc (overwriteBytes b mp.offset w)

/-- The `deinitMovedPlace` write: `.uninit` over the moved window with **no**
Tree Borrows transition. -/
def deinitMPlaceRaw (st : PState) (mp : MPlace) : Except Fault PState :=
  match heapGet st mp.alloc with
  | none => .error (.ub .danglingPointer)
  | some b =>
    match Nat.ble (mp.offset + mp.size) b.length with
    | false => .error (.ub .outOfBounds)
    | true => putHeap st mp.alloc (overwriteBytes b mp.offset (uninitBytes mp.size))

/-- Set local `l` of the top frame. -/
def setLocalE (st : PState) (l : Local) (v : PSlot) : Except Fault PState :=
  match st.frames with
  | [] => .error .unsupported
  | fr :: rest =>
    match setNth? fr.locals l v with
    | none => .error (.ub .deadLocal)
    | some ls => .ok { st with frames := { fr with locals := ls } :: rest }

/-- Kinds kept as immediates (scalars, pointers, ZST unit); all others are
memory-backed. -/
def isImmKind : RigidTy → Bool
  | .bool | .char | .int _ | .uint _ | .float _ | .ref _ _ | .rawPtr _ _
  | .fnPtr _ _ _ _ | .fnDef _ _ | .never => true
  | .tuple [] => true
  | _ => false

/-- Validity of loaded bytes at a kind (`invalidUninitBytes` otherwise). -/
def validateBytes (k : RigidTy) (b : Bytes) : Bool :=
  match k with
  | .bool =>
    match decodeLittleEndianBytes b with
    | some (v, _) => Nat.beq b.length 1 && Nat.ble v 1
    | none => false
  | .char | .int _ | .uint _ | .float _ | .ref _ _ | .rawPtr _ _ | .fnPtr _ _ _ _ =>
    match decodeLittleEndianBytes b with
    | some _ => !(Nat.beq b.length 0)
    | none => false
  | _ => true

/-- Fault on invalid bytes. -/
def checkValid (ty : SemTy) (b : Bytes) : Except Fault Unit :=
  match validateBytes ty.1 b with
  | true => .ok ()
  | false => .error (.ub .invalidUninitBytes)

/-- 8-byte little-endian pointer with `(alloc, tag)` provenance on every byte. -/
def ptrBytes (alloc tag off : Nat) : Bytes := encodeLittleEndianBytes off 8 (some (alloc, tag))

/-- Decode an 8-byte pointer into `(alloc, tag, offset)`. -/
def decodePtr (b : Bytes) : Option (Nat × Nat × Nat) :=
  match Nat.beq b.length 8, decodeLittleEndianBytes b with
  | true, some (off, some (a, t)) => some (a, t, off)
  | _, _ => none

/-! ### Resolved ("semantic") syntax shared by both machines -/

/-- Resolved projection. -/
inductive SemProj : Type where
  | deref
  | field (i : Nat) (ty : SemTy)
  | index (l : Local)
  | constantIndex (offset minLength : Nat) (fromEnd : Bool)
  | subslice (fromIdx toIdx : Nat) (fromEnd : Bool)
  | unsupported

/-- Resolved place: base local, its resolved type, and resolved projections. -/
structure SemPlace : Type where
  local_ : Local
  ty : SemTy
  projs : List SemProj

/-- Resolved operand. -/
inductive SemOperand : Type where
  | copy (p : SemPlace)
  | move (p : SemPlace)
  | const (b : Bytes) (ty : SemTy)

/-- Resolved rvalue. -/
inductive SemRvalue : Type where
  | use (op : SemOperand)
  | binaryOp (o : BinOp) (l r : SemOperand)
  | aggregate (ops : List SemOperand)
  | ref (mutbl : Bool) (p : SemPlace)
  | rawPtr (p : SemPlace)
  | unsupported

/-- Resolved statement. -/
inductive SemStmt : Type where
  | assign (dest : SemPlace) (rv : SemRvalue)
  | deinit (p : SemPlace)
  | storageLive (l : Local) (ty : SemTy)
  | storageDead (l : Local)
  | nop
  | unsupported

/-- Caller-side return / unwind site of a call. -/
structure ReturnSite : Type where
  dest : SemPlace
  target : Option Nat
  unwind : UnwindAction

/-- Resolved terminator. -/
inductive SemTerm : Type where
  | goto (bb : Nat)
  | ret (retTy : SemTy) (site : Option ReturnSite)
  | switchInt (d : SemOperand) (ts : SwitchTargets)
  | assert (c : SemOperand) (expected : Bool) (target : Nat) (unwind : UnwindAction)
  | call (callee : Option Nat) (calleeArgCount : Nat) (calleeLocals : List SemTy)
      (args : List SemOperand) (dest : SemPlace)
  | unwindResume (site : Option ReturnSite)
  | unreachable
  | unsupported

/-- A fetched instruction (with the body's pointer width). -/
inductive Instr : Type where
  | stmt (ptrBits : Nat) (s : SemStmt)
  | term (ptrBits : Nat) (t : SemTerm)

/-! ### Places -/

/-- Byte offset of field `i` in layout `l`. -/
def fieldOffset (l : TypeLayout) (i : Nat) : Option Nat :=
  match l.fields with
  | .arbitrary offsets _ => (nth? offsets i).map Size.bytes
  | .array stride _ => some (i * stride.bytes)
  | _ => none

/-- The memory place a pointer value of type `ty` points to. -/
def derefTarget (ptrBits : Nat) (b : Bytes) (ty : SemTy) : Except Fault (MPlace × SemTy) :=
  match ty.1 with
  | .ref _ pk | .rawPtr _ pk =>
    match pointeeLayoutOf ptrBits pk with
    | none => .error .unsupported
    | some pl =>
      match decodePtr b with
      | none => .error (.ub .invalidPointer)
      | some (a, t, off) => .ok (⟨a, off, pl.size.bytes, some t⟩, (pk, pl))
  | _ => .error .unsupported

/-- Read an immediate `usize` index local. -/
def readUsizeLocal (fr : PFrame) (l : Local) : Except Fault Nat :=
  match nth? fr.locals l with
  | some (.imm b) =>
    match decodeLittleEndianBytes b with
    | some (v, _) => .ok v
    | none => .error (.ub .invalidUninitBytes)
  | some (.mem _) => .error .unsupported
  | _ => .error (.ub .deadLocal)

/-- Element `idx` of an array place. -/
def elemAt (ptrBits : Nat) (mp : MPlace) (ty : SemTy) (idx : Nat) : Except Fault (MPlace × SemTy) :=
  match ty.1, ty.2.fields with
  | .array elem n, .array stride _ =>
    match Nat.blt idx n with
    | false => .error (.ub .outOfBounds)
    | true =>
      match pointeeLayoutOf ptrBits elem with
      | none => .error .unsupported
      | some el => .ok (⟨mp.alloc, mp.offset + idx * stride.bytes, el.size.bytes, mp.tag⟩, (elem, el))
  | _, _ => .error .unsupported

/-- Walk resolved projections over a memory place. -/
def walkProjs (ptrBits : Nat) (st : PState) (fr : PFrame) :
    MPlace → SemTy → List SemProj → Except Fault (MPlace × SemTy)
  | mp, ty, [] => .ok (mp, ty)
  | mp, ty, .field i fty :: rest =>
    match fieldOffset ty.2 i with
    | none => .error .unsupported
    | some fo => walkProjs ptrBits st fr ⟨mp.alloc, mp.offset + fo, fty.2.size.bytes, mp.tag⟩ fty rest
  | mp, ty, .constantIndex off _ fromEnd :: rest =>
    match ty.1 with
    | .array _ n =>
      match elemAt ptrBits mp ty (if fromEnd then n - off else off) with
      | .error e => .error e
      | .ok (mp', ty') => walkProjs ptrBits st fr mp' ty' rest
    | _ => .error .unsupported
  | mp, ty, .index l :: rest =>
    match readUsizeLocal fr l with
    | .error e => .error e
    | .ok idx =>
      match elemAt ptrBits mp ty idx with
      | .error e => .error e
      | .ok (mp', ty') => walkProjs ptrBits st fr mp' ty' rest
  | mp, ty, .subslice f t fromEnd :: rest =>
    match ty.1, ty.2.fields with
    | .array elem n, .array stride _ =>
      let hi := if fromEnd then n - t else t
      match Nat.ble f hi && Nat.ble hi n with
      | false => .error (.ub .outOfBounds)
      | true =>
        match pointeeLayoutOf ptrBits (.array elem (hi - f)) with
        | none => .error .unsupported
        | some kl =>
          walkProjs ptrBits st fr ⟨mp.alloc, mp.offset + f * stride.bytes, kl.size.bytes, mp.tag⟩
            (.array elem (hi - f), kl) rest
    | _, _ => .error .unsupported
  | mp, ty, .deref :: rest =>
    match heapGet st mp.alloc with
    | none => .error (.ub .danglingPointer)
    | some b =>
      match derefTarget ptrBits (sliceBytes b mp.offset mp.size) ty with
      | .error e => .error e
      | .ok (mp', ty') => walkProjs ptrBits st fr mp' ty' rest
  | _, _, .unsupported :: _ => .error .unsupported

/-- LeanMiri `evalPlaceToOp`: unprojected immediate locals yield
`.immediate`; everything in memory (including every `*ptr`) yields
`.indirect mplace`. Independent of `pendingMoveDeinit`. -/
def evalPlaceToOp (ptrBits : Nat) (st : PState) (p : SemPlace) : Except Fault (OpTy × SemTy) :=
  match st.frames with
  | [] => .error .unsupported
  | fr :: _ =>
    match nth? fr.locals p.local_ with
    | none => .error (.ub .deadLocal)
    | some .dead => .error (.ub .deadLocal)
    | some (.imm b) =>
      match p.projs with
      | [] => .ok (.immediate b, p.ty)
      | .deref :: rest =>
        match derefTarget ptrBits b p.ty with
        | .error e => .error e
        | .ok (mp, ty) =>
          match walkProjs ptrBits st fr mp ty rest with
          | .error e => .error e
          | .ok (mp', ty') => .ok (.indirect mp', ty')
      | _ :: _ => .error .unsupported
    | some (.mem a) =>
      match walkProjs ptrBits st fr ⟨a, 0, p.ty.2.size.bytes, none⟩ p.ty p.projs with
      | .error e => .error e
      | .ok (mp, ty) => .ok (.indirect mp, ty)

/-- Read the bytes of an `OpTy` (memory reads are Tree Borrows reads). -/
def readOpBytes (st : PState) : OpTy → Except Fault (Bytes × PState)
  | .immediate b => .ok (b, st)
  | .indirect mp => loadMPlace st mp

/-- Write a value to a place (direct local writes to memory-backed locals are
Tree Borrows writes through the root tag). -/
def writePlace (ptrBits : Nat) (st : PState) (dest : SemPlace) (b : Bytes) : Except Fault PState :=
  match evalPlaceToOp ptrBits st dest with
  | .error e => .error e
  | .ok (.immediate _, _) => setLocalE st dest.local_ (.imm b)
  | .ok (.indirect mp, _) => storeMPlace st mp b

/-- Resolve an assignment or call destination (and its type) against the
current state. -/
def resolveDest (ptrBits : Nat) (st : PState) (dest : SemPlace) : Except Fault (DestPlace × SemTy) :=
  match evalPlaceToOp ptrBits st dest with
  | .error e => .error e
  | .ok (.immediate _, ty) => .ok (.imm dest.local_, ty)
  | .ok (.indirect mp, ty) => .ok (.mem mp, ty)

/-- Write to a pre-resolved destination (memory destinations are Tree Borrows
writes). -/
def writeDest (st : PState) (d : DestPlace) (b : Bytes) : Except Fault PState :=
  match d with
  | .imm l => setLocalE st l (.imm b)
  | .mem mp => storeMPlace st mp b

/-- `copyRuntimePlaceNoValidate`'s padded (memory-copy) branch is taken for
memory-repr values read from memory. -/
def usesMemoryPath (ty : SemTy) : OpTy → Bool
  | .indirect _ =>
    match ty.2.backendRepr with
    | .memory => true
    | _ => false
  | .immediate _ => false

/-- Do two memory places overlap? -/
def placesOverlap (a b : MPlace) : Bool :=
  Nat.beq a.alloc b.alloc && byteRangesOverlapBool a.offset a.size b.offset b.size

/-- Memory-copy path (`copy.memoryCopy`), rejecting overlapping source and
destination windows (`mem_copy(.., nonoverlapping = true)`). -/
def copyMemPath (st : PState) (src : MPlace) (d : DestPlace) : Except Fault PState :=
  match d with
  | .imm _ => .error .unsupported
  | .mem dmp =>
    match loadMPlace st src with
    | .error e => .error e
    | .ok (b, st₁) =>
      match placesOverlap src dmp with
      | true => .error (.ub .overlappingCopy)
      | false => storeMPlace st₁ dmp b

/-- Clear the `pendingMoveDeinit` latch. -/
def clearLatch (st : PState) : PState := { st with pendingMoveDeinit := false }

/-! ### `M_anneal`: eager, value-level move deinitialization (no latch) -/

/-- `M_anneal` operand read: a move reads the place and deinitializes it
immediately (an unprojected immediate local becomes `.uninit` bytes; a memory
place gets `.uninit` bytes after the read, with no Tree Borrows access). -/
def annealReadOperand (ptrBits : Nat) (st : PState) (op : SemOperand) :
    Except Fault (Bytes × PState) :=
  match op with
  | .const b ty =>
    match checkValid ty b with
    | .error e => .error e
    | .ok () => .ok (b, clearLatch st)
  | .copy p =>
    match evalPlaceToOp ptrBits (clearLatch st) p with
    | .error e => .error e
    | .ok (o, ty) =>
      match readOpBytes (clearLatch st) o with
      | .error e => .error e
      | .ok (b, st₁) =>
        match checkValid ty b with
        | .error e => .error e
        | .ok () => .ok (b, st₁)
  | .move p =>
    match evalPlaceToOp ptrBits (clearLatch st) p with
    | .error e => .error e
    | .ok (.immediate b, ty) =>
      match p.projs with
      | [] =>
        match setLocalE (clearLatch st) p.local_ (.imm (uninitBytes b.length)) with
        | .error e => .error e
        | .ok st₁ =>
          match checkValid ty b with
          | .error e => .error e
          | .ok () => .ok (b, clearLatch st₁)
      | _ :: _ => .error .unsupported
    | .ok (.indirect mp, ty) =>
      match loadMPlace (clearLatch st) mp with
      | .error e => .error e
      | .ok (b, st₁) =>
        match checkValid ty b with
        | .error e => .error e
        | .ok () =>
          match deinitMPlaceRaw st₁ mp with
          | .error e => .error e
          | .ok st₂ => .ok (b, st₂)

/-- `M_anneal` `dest = use(op)` into a pre-resolved destination. -/
def annealAssignUse (ptrBits : Nat) (st : PState) (op : SemOperand) (d : DestPlace) :
    Except Fault PState :=
  match op with
  | .const b ty =>
    match checkValid ty b with
    | .error e => .error e
    | .ok () => writeDest (clearLatch st) d b
  | .copy p =>
    match evalPlaceToOp ptrBits (clearLatch st) p with
    | .error e => .error e
    | .ok (o, ty) =>
      match o, usesMemoryPath ty o with
      | .indirect src, true => copyMemPath (clearLatch st) src d
      | _, _ =>
        match readOpBytes (clearLatch st) o with
        | .error e => .error e
        | .ok (b, st₁) =>
          match checkValid ty b with
          | .error e => .error e
          | .ok () => writeDest st₁ d b
  | .move p =>
    match evalPlaceToOp ptrBits (clearLatch st) p with
    | .error e => .error e
    | .ok (.immediate b, ty) =>
      match p.projs with
      | [] =>
        match setLocalE (clearLatch st) p.local_ (.imm (uninitBytes b.length)) with
        | .error e => .error e
        | .ok st₁ =>
          match checkValid ty b with
          | .error e => .error e
          | .ok () => writeDest (clearLatch st₁) d b
      | _ :: _ => .error .unsupported
    | .ok (.indirect src, ty) =>
      match usesMemoryPath ty (.indirect src) with
      | true =>
        match copyMemPath (clearLatch st) src d with
        | .error e => .error e
        | .ok st₁ => deinitMPlaceRaw st₁ src
      | false =>
        match loadMPlace (clearLatch st) src with
        | .error e => .error e
        | .ok (b, st₁) =>
          match checkValid ty b with
          | .error e => .error e
          | .ok () =>
            match deinitMPlaceRaw st₁ src with
            | .error e => .error e
            | .ok st₂ => writeDest st₂ d b

/-! ### `M_ref`: LeanMiri with the `d9b41b58b` two-phase protocol -/

/-- `OperandMachine.evalOperand` with `deinitMovedPlace := dm`. With `dm =
false`, `move` is exactly `copy`. With `dm = true`, an unprojected immediate
move replaces the local by `.uninit` bytes, and an indirect move only **sets**
the `pendingMoveDeinit` latch (the consumer deinitializes after reading). -/
def refEvalOperand (dm : Bool) (ptrBits : Nat) (st : PState) (op : SemOperand) :
    Except Fault (OpTy × SemTy × PState) :=
  match op with
  | .const b ty => .ok (.immediate b, ty, if dm then clearLatch st else st)
  | .copy p =>
    match evalPlaceToOp ptrBits (if dm then clearLatch st else st) p with
    | .error e => .error e
    | .ok (o, ty) => .ok (o, ty, if dm then clearLatch st else st)
  | .move p =>
    match dm with
    | false =>
      match evalPlaceToOp ptrBits st p with
      | .error e => .error e
      | .ok (o, ty) => .ok (o, ty, st)
    | true =>
      match evalPlaceToOp ptrBits (clearLatch st) p with
      | .error e => .error e
      | .ok (.immediate b, ty) =>
        match p.projs with
        | [] =>
          match setLocalE (clearLatch st) p.local_ (.imm (uninitBytes b.length)) with
          | .error e => .error e
          | .ok st₁ => .ok (.immediate b, ty, clearLatch st₁)
        | _ :: _ => .error .unsupported
      | .ok (.indirect mp, ty) =>
        .ok (.indirect mp, ty, { clearLatch st with pendingMoveDeinit := true })

/-- `takePendingMoveDeinit` (`ExecutionMachine.projectionHooks` /
`PlaceMachine.placeHooks`): read-and-clear the latch (always `false` when
`deinitMovedPlace = false`). -/
def takePendingMoveDeinit (dm : Bool) (st : PState) : Bool × PState :=
  (dm && st.pendingMoveDeinit, clearLatch st)

/-- `PlaceMachine.readImmediate`: consume the latch, read, and deinitialize an
indirect source **after** the read. -/
def refReadImmediate (dm : Bool) (st : PState) (o : OpTy) (ty : SemTy) :
    Except Fault (Bytes × PState) :=
  match readOpBytes (takePendingMoveDeinit dm st).2 o with
  | .error e => .error e
  | .ok (b, st₁) =>
    match checkValid ty b with
    | .error e => .error e
    | .ok () =>
      match (takePendingMoveDeinit dm st).1, o with
      | true, .indirect mp =>
        match deinitMPlaceRaw st₁ mp with
        | .error e => .error e
        | .ok st₂ => .ok (b, st₂)
      | _, _ => .ok (b, st₁)

/-- `Place.copyRuntimePlaceNoValidate`: consume the latch; the immediate branch
deinitializes the source before the destination write, the memory branch
after the copy. -/
def refCopyRuntimePlaceNoValidate (dm : Bool) (st : PState) (o : OpTy)
    (ty : SemTy) (d : DestPlace) : Except Fault PState :=
  match o, usesMemoryPath ty o with
  | .indirect src, true =>
    match copyMemPath (takePendingMoveDeinit dm st).2 src d with
    | .error e => .error e
    | .ok st₁ =>
      match (takePendingMoveDeinit dm st).1 with
      | true => deinitMPlaceRaw st₁ src
      | false => .ok st₁
  | _, _ =>
    match readOpBytes (takePendingMoveDeinit dm st).2 o with
    | .error e => .error e
    | .ok (b, st₁) =>
      match checkValid ty b with
      | .error e => .error e
      | .ok () =>
        match (takePendingMoveDeinit dm st).1, o with
        | true, .indirect src =>
          match deinitMPlaceRaw st₁ src with
          | .error e => .error e
          | .ok st₂ => writeDest st₂ d b
        | _, _ => writeDest st₁ d b

/-- `M_ref` operand read: `evalOperand` (phase 1) then `readImmediate`
(phase 2). -/
def twoPhaseReadOperand (dm : Bool) (ptrBits : Nat) (st : PState) (op : SemOperand) :
    Except Fault (Bytes × PState) :=
  match refEvalOperand dm ptrBits st op with
  | .error e => .error e
  | .ok (o, ty, st₁) => refReadImmediate dm st₁ o ty

/-- `M_ref` `dest = use(op)`: `evalOperand` (phase 1) then
`copyRuntimePlaceNoValidate` (phase 2). -/
def twoPhaseAssignUse (dm : Bool) (ptrBits : Nat) (st : PState) (op : SemOperand)
    (d : DestPlace) : Except Fault PState :=
  match refEvalOperand dm ptrBits st op with
  | .error e => .error e
  | .ok (o, ty, st₁) => refCopyRuntimePlaceNoValidate dm st₁ o ty d

/-- Evaluate and consume operands left to right with `f`. -/
def readOperandsWith (f : Nat → PState → SemOperand → Except Fault (Bytes × PState)) (pb : Nat) :
    PState → List SemOperand → Except Fault (List Bytes × PState)
  | st, [] => .ok ([], st)
  | st, op :: ops =>
    match f pb st op with
    | .error e => .error e
    | .ok (b, st₁) =>
      match readOperandsWith f pb st₁ ops with
      | .error e => .error e
      | .ok (bs, st₂) => .ok (b :: bs, st₂)

/-- How a machine evaluates and consumes operands. -/
structure OperandStrategy : Type where
  readOperand : Nat → PState → SemOperand → Except Fault (Bytes × PState)
  assignUse : Nat → PState → SemOperand → DestPlace → Except Fault PState
  /-- Call-argument evaluation (`Call.evalCalleeAndArgs` + `passArgument`), given the
  resolved callee (`some bodyIdx` or `none`) and the call's destination place; by
  default every argument is evaluated *and consumed* left to right through
  `readOperand` before callee resolution (`kani#5172`). -/
  callArgs : Nat → PState → Option Nat → List SemOperand → SemPlace →
      Except Fault (List Bytes × PState) :=
    fun pb st _ ops _ => readOperandsWith readOperand pb st ops

/-- `M_anneal`'s operand strategy (eager deinitialization). -/
def eagerStrategy : OperandStrategy :=
  { readOperand := annealReadOperand, assignUse := annealAssignUse }

/-- `M_ref`'s operand strategy (two-phase latch protocol with
`deinitMovedPlace := dm`). -/
def twoPhaseStrategy (dm : Bool) : OperandStrategy :=
  { readOperand := twoPhaseReadOperand dm, assignUse := twoPhaseAssignUse dm }

/-! ### Statements and terminators (shared) -/

/-- Evaluate and consume operands left to right with a strategy. -/
def readOperands (S : OperandStrategy) (pb : Nat) :
    PState → List SemOperand → Except Fault (List Bytes × PState) :=
  readOperandsWith S.readOperand pb

/-- Binary operations on little-endian byte strings (the modeled subset). -/
def evalBinOpBytes (o : BinOp) (lb rb : Bytes) : Except Fault Bytes :=
  match decodeLittleEndianBytes lb, decodeLittleEndianBytes rb with
  | some (lv, _), some (rv, _) =>
    match o with
    | .add => .ok (encodeLittleEndianBytes (lv + rv) lb.length .none)
    | .sub => .ok (encodeLittleEndianBytes (lv + 2 ^ (8 * lb.length) - rv) lb.length .none)
    | .eq => .ok [.init (if lv = rv then 1 else 0) .none]
    | .ne => .ok [.init (if lv = rv then 0 else 1) .none]
    | .lt => .ok [.init (if lv < rv then 1 else 0) .none]
    | _ => .error .unsupported
  | _, _ => .error (.ub .invalidUninitBytes)

/-- Place the field byte strings at their layout offsets. -/
def buildAggregateAux (l : TypeLayout) : Nat → Bytes → List Bytes → Except Fault Bytes
  | _, acc, [] => .ok acc
  | i, acc, fb :: rest =>
    match fieldOffset l i with
    | none => .error .unsupported
    | some off => buildAggregateAux l (i + 1) (overwriteBytes acc off fb) rest

/-- Build an aggregate's bytes (padding stays uninitialized). -/
def buildAggregate (l : TypeLayout) (fields : List Bytes) : Except Fault Bytes :=
  buildAggregateAux l 0 (uninitBytes l.size.bytes) fields

/-- Taking a reference / raw pointer forces an immediate local into memory. -/
def forceAllocation (st : PState) (l : Local) : Except Fault PState :=
  match st.frames with
  | [] => .error .unsupported
  | fr :: rest =>
    match nth? fr.locals l with
    | some (.imm b) =>
      match setNth? fr.locals l (.mem st.heap.length) with
      | none => .error (.ub .deadLocal)
      | some ls => .ok { st with heap := st.heap ++ [some b], frames := { fr with locals := ls } :: rest }
    | some (.mem _) => .ok st
    | _ => .error (.ub .deadLocal)

/-- The memory place of a place (forcing an unprojected local into memory). -/
def placeToMPlace (pb : Nat) (st : PState) (p : SemPlace) : Except Fault (MPlace × PState) :=
  match (match p.projs with
         | [] => forceAllocation st p.local_
         | _ :: _ => .ok st) with
  | .error e => .error e
  | .ok st₁ =>
    match evalPlaceToOp pb st₁ p with
    | .error e => .error e
    | .ok (.immediate _, _) => .error .unsupported
    | .ok (.indirect mp, _) => .ok (mp, st₁)

/-- Reference creation: a fresh tag (`.frozen` for `&`, `.reservedFrz false`
for `&mut`) after a reborrow read through the parent tag. -/
def createRef (st : PState) (mutbl : Bool) (mp : MPlace) : Except Fault (Bytes × PState) :=
  match tbAccess .read st.borrows mp.alloc mp.tag mp.offset mp.size with
  | none => .error (.ub .treeBorrows)
  | some bs =>
    let parent : Option Nat :=
      match mp.tag with
      | some pt => if pt = 0 then none else some pt
      | none => none
    let e : BorrowEntry :=
      { tag := st.nextTag, targetLocal := mp.alloc, targetProjection := []
        perm := if mutbl then .reservedFrz false else .frozen
        rangeOffset := mp.offset, rangeLen := mp.size, protector := none, parentTag := parent }
    .ok (ptrBytes mp.alloc st.nextTag mp.offset,
      { st with borrows := bs ++ [e], nextTag := st.nextTag + 1 })

/-- Advance to the next statement of the top frame. -/
def advance (st : PState) : PState :=
  match st.frames with
  | [] => st
  | fr :: rest => { st with frames := { fr with stmt := fr.stmt + 1 } :: rest }

/-- Jump to the start of basic block `bb` of the top frame. -/
def jump (st : PState) (bb : Nat) : PState :=
  match st.frames with
  | [] => st
  | fr :: rest => { st with frames := { fr with block := bb, stmt := 0 } :: rest }

/-- Execute a resolved statement with an operand strategy. The destination of
an assignment is resolved first. -/
def execStmt (S : OperandStrategy) (pb : Nat) (st : PState) : SemStmt → Except Fault PState
  | .assign dest rv =>
    match resolveDest pb st dest with
    | .error e => .error e
    | .ok (d, dty) =>
      match rv with
      | .use op => S.assignUse pb st op d
      | .binaryOp o l r =>
        match S.readOperand pb st l with
        | .error e => .error e
        | .ok (lb, st₁) =>
          match S.readOperand pb st₁ r with
          | .error e => .error e
          | .ok (rb, st₂) =>
            match evalBinOpBytes o lb rb with
            | .error e => .error e
            | .ok res => writeDest st₂ d res
      | .aggregate ops =>
        match readOperands S pb st ops with
        | .error e => .error e
        | .ok (bs, st₁) =>
          match buildAggregate dty.2 bs with
          | .error e => .error e
          | .ok b => writeDest st₁ d b
      | .ref mutbl p =>
        match placeToMPlace pb st p with
        | .error e => .error e
        | .ok (mp, st₁) =>
          match createRef st₁ mutbl mp with
          | .error e => .error e
          | .ok (b, st₂) =>
            let d' := match d, p.projs with
              | .imm l, [] => if Nat.beq l p.local_ then .mem mp else d
              | _, _ => d
            writeDest st₂ d' b
      | .rawPtr p =>
        match placeToMPlace pb st p with
        | .error e => .error e
        | .ok (mp, st₁) =>
          let d' := match d, p.projs with
            | .imm l, [] => if Nat.beq l p.local_ then .mem mp else d
            | _, _ => d
          writeDest st₁ d' (ptrBytes mp.alloc (mp.tag.getD 0) mp.offset)
      | .unsupported => .error .unsupported
  | .deinit p =>
    match evalPlaceToOp pb st p with
    | .error e => .error e
    | .ok (.immediate b, _) => setLocalE st p.local_ (.imm (uninitBytes b.length))
    | .ok (.indirect mp, _) => storeMPlace st mp (uninitBytes mp.size)
  | .storageLive l ty =>
    match isImmKind ty.1 with
    | true => setLocalE st l (.imm (uninitBytes ty.2.size.bytes))
    | false =>
      setLocalE { st with heap := st.heap ++ [some (uninitBytes ty.2.size.bytes)] } l
        (.mem st.heap.length)
  | .storageDead l =>
    match st.frames with
    | [] => .error .unsupported
    | fr :: _ =>
      match nth? fr.locals l with
      | some (.mem a) =>
        match setNth? st.heap a none with
        | none => .error (.ub .danglingPointer)
        | some h => setLocalE { st with heap := h } l .dead
      | _ => setLocalE st l .dead
  | .nop => .ok st
  | .unsupported => .error .unsupported

/-- One-step outcome. -/
inductive StepOut : Type where
  | running (st : PState)
  | returned (b : Bytes)
  | panicked
  | fault (f : Fault)

/-- Free the memory-backed locals of a popped frame. -/
def freeFrameAllocs (heap : List (Option Bytes)) : List PSlot → List (Option Bytes)
  | [] => heap
  | .mem a :: rest => freeFrameAllocs ((setNth? heap a none).getD heap) rest
  | _ :: rest => freeFrameAllocs heap rest

/-- Pop the top frame (freeing its memory-backed locals). -/
def popFrame (st : PState) : PState :=
  match st.frames with
  | [] => st
  | fr :: rest => { st with frames := rest, heap := freeFrameAllocs st.heap fr.locals }

/-- Allocate a callee's locals (`_1..=argCount` from the argument bytes). -/
def allocLocals (argCount : Nat) (args : List Bytes) :
    Nat → List (Option Bytes) → List SemTy → List PSlot × List (Option Bytes)
  | _, heap, [] => ([], heap)
  | i, heap, ty :: tys =>
    let init : Bytes :=
      match Nat.ble 1 i && Nat.ble i argCount with
      | true => (nth? args (i - 1)).getD (uninitBytes ty.2.size.bytes)
      | false => uninitBytes ty.2.size.bytes
    match isImmKind ty.1 with
    | true =>
      let r := allocLocals argCount args (i + 1) heap tys
      (.imm init :: r.1, r.2)
    | false =>
      let r := allocLocals argCount args (i + 1) (heap ++ [some init]) tys
      (.mem heap.length :: r.1, r.2)

/-- `SwitchInt` target for value `v`. -/
def findSwitchTarget (v : Nat) : List (Nat × Nat) → Nat → Nat
  | [], o => o
  | (c, t) :: rest, o => if v = c then t else findSwitchTarget v rest o

/-- Execute a resolved terminator with an operand strategy. -/
def execTerm (S : OperandStrategy) (pb : Nat) (st : PState) : SemTerm → StepOut
  | .goto bb => .running (jump st bb)
  | .ret retTy site =>
    match evalPlaceToOp pb st ⟨0, retTy, []⟩ with
    | .error e => .fault e
    | .ok (o, _) =>
      match readOpBytes st o with
      | .error e => .fault e
      | .ok (b, st₁) =>
        match checkValid retTy b with
        | .error e => .fault e
        | .ok () =>
          match site with
          | none => .returned b
          | some rs =>
            let wr :=
              match st₁.frames with
              | fr :: _ =>
                match fr.retDest with
                | some d => writeDest (popFrame st₁) d b
                | none => writePlace pb (popFrame st₁) rs.dest b
              | [] => writePlace pb (popFrame st₁) rs.dest b
            match wr with
            | .error e => .fault e
            | .ok st₃ =>
              match rs.target with
              | none => .fault (.ub .divergingReturn)
              | some t => .running (jump st₃ t)
  | .switchInt d ts =>
    match S.readOperand pb st d with
    | .error e => .fault e
    | .ok (b, st₁) =>
      match decodeLittleEndianBytes b with
      | none => .fault (.ub .invalidUninitBytes)
      | some (v, _) => .running (jump st₁ (findSwitchTarget v ts.branches ts.otherwise))
  | .assert c expected target unwind =>
    match S.readOperand pb st c with
    | .error e => .fault e
    | .ok (b, st₁) =>
      match decodeLittleEndianBytes b with
      | none => .fault (.ub .invalidUninitBytes)
      | some (v, _) =>
        match decide (Nat.beq v 1 = expected) with
        | true => .running (jump st₁ target)
        | false =>
          match unwind with
          | .cleanup bb => .running (jump st₁ bb)
          | _ => .panicked
  | .call callee argc calleeLocals args dest =>
    match resolveDest pb st dest with
    | .error e => .fault e
    | .ok (d, _) =>
      match S.callArgs pb st callee args dest with
      | .error e => .fault e
      | .ok (bs, st₁) =>
        match callee with
        | none => .fault .unsupported
        | some bi =>
          let r := allocLocals argc bs 0 st₁.heap calleeLocals
          .running { st₁ with frames := ⟨bi, 0, 0, r.1, some d⟩ :: st₁.frames, heap := r.2 }
  | .unwindResume site =>
    match site with
    | none => .panicked
    | some rs =>
      match rs.unwind with
      | .cleanup bb => .running (jump (popFrame st) bb)
      | _ => .panicked
  | .unreachable => .fault (.ub .unreachable)
  | .unsupported => .fault .unsupported

/-- Run one fetched instruction. -/
def runInstr (S : OperandStrategy) (st : PState) : Instr → StepOut
  | .stmt pb s =>
    match execStmt S pb st s with
    | .error f => .fault f
    | .ok st' => .running (advance st')
  | .term pb t => execTerm S pb st t

/-! ## Part 6 — The two machines: fetch, resolve, step, run

`M_anneal` resolves deep `Ty`s against each body's `LayoutTable`; `M_ref`
resolves `TyId`s through the demand-time `evalLayoutQuery`. -/

/-! ### `M_anneal` resolution (deep `V2026_06_01` syntax) -/

/-- Resolve a deep `Ty` against a layout table. -/
def annealResolveTy (L : LayoutTable) (ty : Ty) : Option SemTy :=
  (nth? L.entries ty.layoutIdx).map (fun l => (ty.kind, l))

/-- Resolve a projection element. -/
def annealResolveProj (L : LayoutTable) : ProjectionElem → Option SemProj
  | .deref => some .deref
  | .field i ty => (annealResolveTy L ty).map (.field i)
  | .index l => some (.index l)
  | .constantIndex o m e => some (.constantIndex o m e)
  | .subslice f t e => some (.subslice f t e)
  | .downcast _ _ => some .unsupported
  | .opaqueCast _ => some .unsupported
  | .unwrapUnsafeBinder _ => some .unsupported

/-- Resolve a place. -/
def annealResolvePlace (b : CapturedMir) (p : Place) : Option SemPlace :=
  match nth? b.localDecls p.local_ with
  | none => none
  | some d =>
    match annealResolveTy b.layouts d.ty, decodeList (annealResolveProj b.layouts) p.projection with
    | some ty, some projs => some ⟨p.local_, ty, projs⟩
    | _, _ => none

/-- Resolve a constant (zero-sized and integer scalars; everything else,
including pointer constants into global allocations, fails closed). -/
def constSem (sty : Option SemTy) (v : ConstValue) : Option SemOperand :=
  match sty with
  | none => none
  | some ty =>
    match v with
    | .zeroSized => some (.const [] ty)
    | .scalar (.int si) => some (.const (encodeLittleEndianBytes si.bits si.sizeBytes .none) ty)
    | _ => none

/-- Resolve an operand. -/
def annealResolveOperand (b : CapturedMir) : Operand → Option SemOperand
  | .copy p => (annealResolvePlace b p).map .copy
  | .move p => (annealResolvePlace b p).map .move
  | .constant c => constSem (annealResolveTy b.layouts c.ty) c.val

/-- Is a borrow kind mutable? -/
def borrowIsMut : BorrowKind → Bool
  | .shared => false
  | .mut _ => true

/-- Resolve an rvalue (the modeled subset; other rvalues are `.unsupported`). -/
def annealResolveRvalue (b : CapturedMir) : Rvalue → Option SemRvalue
  | .use op => (annealResolveOperand b op).map .use
  | .binaryOp o l r =>
    match annealResolveOperand b l, annealResolveOperand b r with
    | some l', some r' => some (.binaryOp o l' r')
    | _, _ => none
  | .aggregate _ ops => (decodeList (annealResolveOperand b) ops).map .aggregate
  | .ref bk p => (annealResolvePlace b p).map (.ref (borrowIsMut bk))
  | .rawPtr _ p => (annealResolvePlace b p).map .rawPtr
  | _ => some .unsupported

/-- Resolve a statement. -/
def annealResolveStmt (b : CapturedMir) (s : Statement) : SemStmt :=
  match s.kind with
  | .assign p rv =>
    match annealResolvePlace b p, annealResolveRvalue b rv with
    | some p', some rv' => .assign p' rv'
    | _, _ => .unsupported
  | .deinit p =>
    match annealResolvePlace b p with
    | some p' => .deinit p'
    | none => .unsupported
  | .storageLive l =>
    match (nth? b.localDecls l).bind (fun d => annealResolveTy b.layouts d.ty) with
    | some ty => .storageLive l ty
    | none => .unsupported
  | .storageDead l => .storageDead l
  | .nop => .nop
  | .coverage => .nop
  | .constEvalCounter => .nop
  | _ => .unsupported

/-- Resolve every local declaration type of a body. -/
def annealResolveLocals (b : CapturedMir) : Option (List SemTy) :=
  decodeList (fun d => annealResolveTy b.layouts d.ty) b.localDecls

/-- The `DefPath` of a `fnDef` kind. -/
def fnDefPath? (k : RigidTy) : Option DefPath :=
  match k with
  | .fnDef path _ => some path
  | _ => none

/-- Callee of a `Call`: a constant `fnDef` resolved by `DefPath` among the
program's bodies (`none` = unresolved / external callee). -/
def annealCallee (p : V2026Prog) (func : Operand) : Option Nat :=
  match func with
  | .constant c => (fnDefPath? c.ty.kind).bind (indexOf? defPathBEq (p.bodies.map CapturedMir.defPath))
  | _ => none

/-- Return / unwind site of the caller frame: `none` = resolution failure,
`some none` = root frame. -/
def annealSite (p : V2026Prog) (frames : List PFrame) : Option (Option ReturnSite) :=
  match frames with
  | [] => none
  | [_] => some none
  | _ :: caller :: _ =>
    match nth? p.bodies caller.body with
    | none => none
    | some cb =>
      match nth? cb.basicBlocks caller.block with
      | none => none
      | some bb =>
        match bb.terminator.kind with
        | .call _ _ dest target unwind =>
          (annealResolvePlace cb dest).map (fun d => some ⟨d, target, unwind⟩)
        | _ => none

/-- Resolve a terminator. -/
def annealResolveTerm (p : V2026Prog) (frames : List PFrame) (b : CapturedMir)
    (t : Terminator) : SemTerm :=
  match t.kind with
  | .goto bb => .goto bb
  | .return_ =>
    match (nth? b.localDecls 0).bind (fun d => annealResolveTy b.layouts d.ty),
        annealSite p frames with
    | some ty, some site => .ret ty site
    | _, _ => .unsupported
  | .switchInt d ts =>
    match annealResolveOperand b d with
    | some d' => .switchInt d' ts
    | none => .unsupported
  | .assert c e tgt u =>
    match annealResolveOperand b c with
    | some c' => .assert c' e tgt u
    | none => .unsupported
  | .call f args dest _ _ =>
    match annealResolvePlace b dest, decodeList (annealResolveOperand b) args with
    | some dest', some args' =>
      match annealCallee p f with
      | none => .call none 0 [] args' dest'
      | some bi =>
        match (nth? p.bodies bi).bind (fun cb => (annealResolveLocals cb).map (cb.argCount, ·)) with
        | some (argc, tys) => .call (some bi) argc tys args' dest'
        | none => .unsupported
    | _, _ => .unsupported
  | .unwindResume =>
    match annealSite p frames with
    | some site => .unwindResume site
    | none => .unsupported
  | .unreachable => .unreachable
  | _ => .unsupported

/-- `M_anneal` fetch: the next statement or terminator of the top frame. -/
def annealFetch (p : V2026Prog) (st : PState) : Except Fault Instr :=
  match st.frames with
  | [] => .error .unsupported
  | fr :: _ =>
    match nth? p.bodies fr.body with
    | none => .error .unsupported
    | some b =>
      match nth? b.basicBlocks fr.block with
      | none => .error (.ub .badControlFlow)
      | some bb =>
        match nth? bb.statements fr.stmt with
        | some s => .ok (.stmt b.layouts.pointerBits (annealResolveStmt b s))
        | none =>
          match Nat.beq fr.stmt bb.statements.length with
          | true => .ok (.term b.layouts.pointerBits (annealResolveTerm p st.frames b bb.terminator))
          | false => .error (.ub .badControlFlow)

/-- `M_anneal` small step. -/
def annealStep (p : V2026Prog) (st : PState) : StepOut :=
  match annealFetch p st with
  | .error f => .fault f
  | .ok i => runInstr eagerStrategy st i

/-! ### `M_ref` resolution (`TyId` syntax + demand-time `LayoutQuery`) -/

/-- Resolve a `TyId` through the demand-time `localLayout` query. -/
def refResolveTy (tt : TypeTable) (L : LayoutTable) (t : TyId) : Option SemTy :=
  match evalLayoutQuery tt L (.localLayout t) with
  | .ok (.layout k l) => some (k, l)
  | _ => none

/-- Resolve a reference projection element. -/
def refResolveProj (tt : TypeTable) (L : LayoutTable) : RefProjectionElem → Option SemProj
  | .deref => some .deref
  | .field i t => (refResolveTy tt L t).map (.field i)
  | .index l => some (.index l)
  | .constantIndex o m e => some (.constantIndex o m e)
  | .subslice f t e => some (.subslice f t e)
  | .downcast _ _ => some .unsupported
  | .opaqueCast _ => some .unsupported
  | .unwrapUnsafeBinder _ => some .unsupported

/-- Resolve a reference place. -/
def refResolvePlace (tt : TypeTable) (b : RefBody) (p : RefPlace) : Option SemPlace :=
  match nth? b.localDecls p.local_ with
  | none => none
  | some d =>
    match refResolveTy tt b.layouts d.ty, decodeList (refResolveProj tt b.layouts) p.projection with
    | some ty, some projs => some ⟨p.local_, ty, projs⟩
    | _, _ => none

/-- Resolve a reference operand. -/
def refResolveOperand (tt : TypeTable) (b : RefBody) : RefOperand → Option SemOperand
  | .copy p => (refResolvePlace tt b p).map .copy
  | .move p => (refResolvePlace tt b p).map .move
  | .constant c => constSem (refResolveTy tt b.layouts c.ty) c.val

/-- Resolve a reference rvalue. -/
def refResolveRvalue (tt : TypeTable) (b : RefBody) : RefRvalue → Option SemRvalue
  | .use op => (refResolveOperand tt b op).map .use
  | .binaryOp o l r =>
    match refResolveOperand tt b l, refResolveOperand tt b r with
    | some l', some r' => some (.binaryOp o l' r')
    | _, _ => none
  | .aggregate _ ops => (decodeList (refResolveOperand tt b) ops).map .aggregate
  | .ref bk p => (refResolvePlace tt b p).map (.ref (borrowIsMut bk))
  | .rawPtr _ p => (refResolvePlace tt b p).map .rawPtr
  | _ => some .unsupported

/-- Resolve a reference statement. -/
def refResolveStmt (tt : TypeTable) (b : RefBody) (s : RefStatement) : SemStmt :=
  match s.kind with
  | .assign p rv =>
    match refResolvePlace tt b p, refResolveRvalue tt b rv with
    | some p', some rv' => .assign p' rv'
    | _, _ => .unsupported
  | .deinit p =>
    match refResolvePlace tt b p with
    | some p' => .deinit p'
    | none => .unsupported
  | .storageLive l =>
    match (nth? b.localDecls l).bind (fun d => refResolveTy tt b.layouts d.ty) with
    | some ty => .storageLive l ty
    | none => .unsupported
  | .storageDead l => .storageDead l
  | .nop => .nop
  | .coverage => .nop
  | .constEvalCounter => .nop
  | _ => .unsupported

/-- Resolve every local declaration `TyId` of a reference body. -/
def refResolveLocals (tt : TypeTable) (b : RefBody) : Option (List SemTy) :=
  decodeList (fun d => refResolveTy tt b.layouts d.ty) b.localDecls

/-- Callee of a reference `Call` (decoding the constant's `TyId`). -/
def refCallee (rp : RefProg) (func : RefOperand) : Option Nat :=
  match func with
  | .constant c =>
    ((nth? rp.types.types c.ty).bind (fun ty => fnDefPath? ty.kind)).bind
      (indexOf? defPathBEq (rp.bodies.map RefBody.defPath))
  | _ => none

/-- Return / unwind site of the caller frame (reference syntax). -/
def refSite (rp : RefProg) (frames : List PFrame) : Option (Option ReturnSite) :=
  match frames with
  | [] => none
  | [_] => some none
  | _ :: caller :: _ =>
    match nth? rp.bodies caller.body with
    | none => none
    | some cb =>
      match nth? cb.basicBlocks caller.block with
      | none => none
      | some bb =>
        match bb.terminator.kind with
        | .call _ _ dest target unwind =>
          (refResolvePlace rp.types cb dest).map (fun d => some ⟨d, target, unwind⟩)
        | _ => none

/-- Resolve a reference terminator. -/
def refResolveTerm (rp : RefProg) (frames : List PFrame) (b : RefBody) (t : RefTerminator) :
    SemTerm :=
  match t.kind with
  | .goto bb => .goto bb
  | .return_ =>
    match (nth? b.localDecls 0).bind (fun d => refResolveTy rp.types b.layouts d.ty),
        refSite rp frames with
    | some ty, some site => .ret ty site
    | _, _ => .unsupported
  | .switchInt d ts =>
    match refResolveOperand rp.types b d with
    | some d' => .switchInt d' ts
    | none => .unsupported
  | .assert c e tgt u =>
    match refResolveOperand rp.types b c with
    | some c' => .assert c' e tgt u
    | none => .unsupported
  | .call f args dest _ _ =>
    match refResolvePlace rp.types b dest, decodeList (refResolveOperand rp.types b) args with
    | some dest', some args' =>
      match refCallee rp f with
      | none => .call none 0 [] args' dest'
      | some bi =>
        match (nth? rp.bodies bi).bind
            (fun cb => (refResolveLocals rp.types cb).map (cb.argCount, ·)) with
        | some (argc, tys) => .call (some bi) argc tys args' dest'
        | none => .unsupported
    | _, _ => .unsupported
  | .unwindResume =>
    match refSite rp frames with
    | some site => .unwindResume site
    | none => .unsupported
  | .unreachable => .unreachable
  | _ => .unsupported

/-- `M_ref` fetch. -/
def refFetch (rp : RefProg) (st : PState) : Except Fault Instr :=
  match st.frames with
  | [] => .error .unsupported
  | fr :: _ =>
    match nth? rp.bodies fr.body with
    | none => .error .unsupported
    | some b =>
      match nth? b.basicBlocks fr.block with
      | none => .error (.ub .badControlFlow)
      | some bb =>
        match nth? bb.statements fr.stmt with
        | some s => .ok (.stmt b.layouts.pointerBits (refResolveStmt rp.types b s))
        | none =>
          match Nat.beq fr.stmt bb.statements.length with
          | true => .ok (.term b.layouts.pointerBits (refResolveTerm rp st.frames b bb.terminator))
          | false => .error (.ub .badControlFlow)

/-- `M_ref`-style step with an arbitrary operand strategy. -/
def refStepCoreWith (S : OperandStrategy) (rp : RefProg) (st : PState) : StepOut :=
  match refFetch rp st with
  | .error f => .fault f
  | .ok i => runInstr S st i

/-- `M_ref` step on the shared core state (`ExecutionMachine.step` without
the step budget), with `deinitMovedPlace := dm`. -/
def refStepCore (dm : Bool) (rp : RefProg) (st : PState) : StepOut :=
  refStepCoreWith (twoPhaseStrategy dm) rp st

/-! ### Step budgets, outcomes, runs -/

/-- `M_ref` state: core state plus `stepsExecuted` / `maxSteps`
(`Limits.maxSteps`). -/
structure RefState : Type where
  core : PState
  stepsExecuted : Nat
  maxSteps : Nat

/-- `M_ref` outcome. -/
inductive RefOutcome : Type where
  | running (rs : RefState)
  | returned (b : Bytes)
  | panicked
  | ub (why : UBReason)
  | blocked
  | exhaustedStepLimit

/-- Map a fault to the corresponding `M_ref` outcome. -/
def faultToRefOutcome : Fault → RefOutcome
  | .ub why => .ub why
  | .unsupported => .blocked

/-- `M_ref` step: the budget is checked first. -/
def refStep (dm : Bool) (rp : RefProg) (rs : RefState) : RefOutcome :=
  match Nat.blt rs.stepsExecuted rs.maxSteps with
  | false => .exhaustedStepLimit
  | true =>
    match refStepCore dm rp rs.core with
    | .running st' => .running ⟨st', rs.stepsExecuted + 1, rs.maxSteps⟩
    | .returned b => .returned b
    | .panicked => .panicked
    | .fault f => faultToRefOutcome f

/-- Run `M_anneal` for at most `n` steps. -/
def annealRun (p : V2026Prog) : Nat → PState → StepOut
  | 0, st => .running st
  | n + 1, st =>
    match annealStep p st with
    | .running st' => annealRun p n st'
    | o => o

/-- Run `M_ref` for at most `n` budgeted steps. -/
def refRunFuel (dm : Bool) (rp : RefProg) : Nat → RefState → RefOutcome
  | 0, rs => .running rs
  | n + 1, rs =>
    match refStep dm rp rs with
    | .running rs' => refRunFuel dm rp n rs'
    | o => o

/-- Entry state from resolved entry-body local types. -/
def initFromLocals (entry : Nat) (argCount : Nat) (args : List Bytes) (tys : List SemTy) : PState :=
  let r := allocLocals argCount args 0 [] tys
  { frames := [⟨entry, 0, 0, r.1, none⟩], heap := r.2, borrows := [], nextTag := 1,
    pendingMoveDeinit := false }

/-- `M_anneal` entry state. -/
def annealInit (p : V2026Prog) (args : List Bytes) : Except Fault PState :=
  match nth? p.bodies p.entry with
  | none => .error .unsupported
  | some b =>
    match annealResolveLocals b with
    | none => .error .unsupported
    | some tys => .ok (initFromLocals p.entry b.argCount args tys)

/-- `M_ref` entry state. -/
def refInit (rp : RefProg) (args : List Bytes) : Except Fault PState :=
  match nth? rp.bodies rp.entry with
  | none => .error .unsupported
  | some b =>
    match refResolveLocals rp.types b with
    | none => .error .unsupported
    | some tys => .ok (initFromLocals rp.entry b.argCount args tys)

/-- Observable result of a bounded run. -/
inductive Obs : Type where
  | returned (v : Option Nat) (len : Nat)
  | panicked
  | ub (why : UBReason)
  | unsupported
  | exhausted
  deriving DecidableEq

/-- Observation of returned bytes (decoded value and length). -/
def bytesObs (b : Bytes) : Obs := .returned ((decodeLittleEndianBytes b).map Prod.fst) b.length

/-- Observation of an `M_anneal` outcome. -/
def stepOutObs : StepOut → Obs
  | .running _ => .exhausted
  | .returned b => bytesObs b
  | .panicked => .panicked
  | .fault (.ub why) => .ub why
  | .fault .unsupported => .unsupported

/-- Observation of an `M_ref` outcome. -/
def refOutcomeObs : RefOutcome → Obs
  | .running _ => .exhausted
  | .returned b => bytesObs b
  | .panicked => .panicked
  | .ub why => .ub why
  | .blocked => .unsupported
  | .exhaustedStepLimit => .exhausted

/-- Run `M_anneal` for at most `fuel` steps. -/
def annealObs (p : V2026Prog) (args : List Bytes) (fuel : Nat) : Obs :=
  match annealInit p args with
  | .error (.ub why) => .ub why
  | .error .unsupported => .unsupported
  | .ok st => stepOutObs (annealRun p fuel st)

/-- Run `M_ref` (`deinitMoves := dm`) with step budget `maxSteps`. -/
def refObs (dm : Bool) (rp : RefProg) (args : List Bytes) (maxSteps : Nat) : Obs :=
  match refInit rp args with
  | .error (.ub why) => .ub why
  | .error .unsupported => .unsupported
  | .ok st => refOutcomeObs (refRunFuel dm rp (maxSteps + 1) ⟨st, 0, maxSteps⟩)

/-- Observation of a fault. -/
def faultObs : Fault → Obs
  | .ub why => .ub why
  | .unsupported => .unsupported

/-! ## Part 6b — Simulation invariant and well-formedness -/

/-- Simulation invariant: the reference core state *is* the Anneal state. -/
def SimulationInv (s : PState) (rs : RefState) : Prop := rs.core = s

/-- Well-formedness of a `V2026_06_01` program (`M_anneal` input): the entry
body exists, every body is at `MirPhaseTag.runtimePostCleanup` and passes
`CapturedMir.wellFormed`, and every local declaration resolves in its body's
`LayoutTable`. -/
def ProgWellFormed (p : V2026Prog) : Prop :=
  p.entry < p.bodies.length ∧
  ∀ b ∈ p.bodies,
    b.phase = .runtimePostCleanup ∧ b.wellFormed = true ∧
    ∀ d ∈ b.localDecls, ∃ st, annealResolveTy b.layouts d.ty = some st

/-- Reference program well-formedness (`M_ref` input): canonical type table,
entry body in bounds, every body at `MirPhaseTag.runtimePostCleanup`, and
every local declaration `TyId` answers `.ok (.layout k l)` under the
demand-time `evalLayoutQuery`. -/
def RefProgWellFormed (rp : RefProg) : Prop :=
  rp.types.Good ∧
  rp.entry < rp.bodies.length ∧
  ∀ rb ∈ rp.bodies,
    rb.phase = .runtimePostCleanup ∧
    ∀ rd ∈ rb.localDecls, ∃ k l,
      evalLayoutQuery rp.types rb.layouts (.localLayout rd.ty) = .ok (.layout k l)

/-- Does a Tree Borrows entry overlap a pre-resolved destination window?
(Immediate destinations are not in the heap and overlap nothing.) -/
def entryOverlapsDest (e : BorrowEntry) : DestPlace → Bool
  | .imm _ => false
  | .mem mp =>
    Nat.beq e.targetLocal mp.alloc && byteRangesOverlapBool e.rangeOffset e.rangeLen mp.offset mp.size

/-! ## Top-level claims

Each claim is a plain `Prop` over the definitions above (and Trusted's
`MirAst` / `MirSemantics`); `Anneal.Mir.Correspondence.Claims` proves each one
by name. -/

/-- **Codec round trip.** For every program `p`:

1. decoding `encodeProg p` recovers `p` exactly (so no syntax is dropped,
   reordered, or laundered into another constructor);
2. `encodeProg` is injective;
3. the type table of `encodeProg p` is `Good` (canonical kinds and types,
   every type's sub-kinds interned);
4. nominal `TyId` equality coincides with structural `Ty` equality on the
   interned types;
5. the built-in kinds `()`, `bool`, `usize` sit at `KindId`s `0`, `1`, `2`;
6. every `Ty` occurrence of `p` is interned;
7. every `CapturedMir.traitImpls` `RigidTy` argument has its full bottom-up
   post-order interned in `kinds`;
8. no statement is laundered into (or out of) a dormant `nop`; and
9. out-of-bounds `TyId`s fail closed (`none`) in `decodeType`. -/
def CodecRoundtripClaim : Prop :=
  (∀ p : V2026Prog, decodeProg (encodeProg p) = some p) ∧
  Function.Injective encodeProg ∧
  (∀ p : V2026Prog, (encodeProg p).types.Good) ∧
  (∀ (p : V2026Prog) (i j : TyId) (ty₁ ty₂ : Ty),
    nth? (encodeProg p).types.types i = some ty₁ →
    nth? (encodeProg p).types.types j = some ty₂ → (i = j ↔ ty₁ = ty₂)) ∧
  (∀ p : V2026Prog,
    nth? (encodeProg p).types.kinds 0 = some (.tuple []) ∧
    nth? (encodeProg p).types.kinds 1 = some .bool ∧
    nth? (encodeProg p).types.kinds 2 = some (.uint .usize)) ∧
  (∀ p : V2026Prog, ∀ ty ∈ progTys p, ty ∈ (encodeProg p).types.types) ∧
  (∀ p : V2026Prog, ∀ k ∈ progTraitKinds p, rigidTyPostorder k ⊆ (encodeProg p).types.kinds) ∧
  (∀ (tt : TypeTable) (s : Statement), ((encodeStmt tt s).kind = .nop ↔ s.kind = .nop)) ∧
  (∀ (tt : TypeTable) (t : TyId), tt.types.length ≤ t → decodeType tt t = none)

/-- **Demand-time layout queries.**

1. `encodeProg` maps well-formed programs to well-formed reference programs;
2. on every type occurrence of every body, `M_ref`'s demand-time resolution of
   the encoded `TyId` equals `M_anneal`'s deep resolution;
3. out-of-bounds `TyId`s and `KindId`s fail closed (`missingHook`) across all
   six `LayoutQuery` constructors;
4. dangling `LayoutIdx`s fail closed (`missingHook`) across `localLayout`,
   `scalarTypeClass`, and `castTypeInfo`;
5. every successful answer is preserved by prefix extension of the type and
   layout tables (call-cone narrowing / multi-body growth);
6. `localLayout` refines the eager pre-materialized table pointwise;
7. `scalarTypeClass` is exactly the scalar classification of the
   `localLayout` answer;
8. `pointeeTypes` is total on interned pointer types of encoded programs;
9. the pre-seeded `()` kind has a `0`-byte layout; and
10. `ProgWellFormed` is satisfiable by a program with locals and blocks. -/
def LayoutQueryCorrespondenceClaim : Prop :=
  (∀ p : V2026Prog, ProgWellFormed p → RefProgWellFormed (encodeProg p)) ∧
  (∀ (p : V2026Prog) (b : CapturedMir), b ∈ p.bodies → ∀ ty ∈ bodyTys b,
    refResolveTy (encodeProg p).types b.layouts (encodeType (encodeProg p).types ty) =
      annealResolveTy b.layouts ty) ∧
  (∀ (tt : TypeTable) (L : LayoutTable) (t : TyId), tt.types.length ≤ t →
    evalLayoutQuery tt L (.localLayout t) = .missingHook ∧
    evalLayoutQuery tt L (.scalarTypeClass t) = .missingHook ∧
    evalLayoutQuery tt L (.pointeeTypes t) = .missingHook ∧
    evalLayoutQuery tt L (.retagTypeShape t) = .missingHook ∧
    ∀ d : TyId, evalLayoutQuery tt L (.castTypeInfo t d) = .missingHook ∧
      evalLayoutQuery tt L (.castTypeInfo d t) = .missingHook) ∧
  (∀ (tt : TypeTable) (L : LayoutTable) (k : KindId), tt.kinds.length ≤ k →
    evalLayoutQuery tt L (.builtinLayout k) = .missingHook) ∧
  (∀ (tt : TypeTable) (L : LayoutTable) (t : TyId) (ty : Ty),
    nth? tt.types t = some ty → L.entries.length ≤ ty.layoutIdx →
    evalLayoutQuery tt L (.localLayout t) = .missingHook ∧
    evalLayoutQuery tt L (.scalarTypeClass t) = .missingHook ∧
    ∀ d : TyId, evalLayoutQuery tt L (.castTypeInfo t d) = .missingHook ∧
      evalLayoutQuery tt L (.castTypeInfo d t) = .missingHook) ∧
  (∀ (tt tt' : TypeTable) (L L' : LayoutTable) (q : LayoutQuery) (a : LayoutAnswer),
    tt.Extends tt' → L'.pointerBits = L.pointerBits → (∃ l, L'.entries = L.entries ++ l) →
    evalLayoutQuery tt L q = .ok a → evalLayoutQuery tt' L' q = .ok a) ∧
  (∀ (tt : TypeTable) (L : LayoutTable) (t : TyId) (k : RigidTy) (l : TypeLayout),
    evalLayoutQuery tt L (.localLayout t) = .ok (.layout k l) ↔
      nth? (eagerLayoutTable tt L) t = some (some (k, l))) ∧
  (∀ (tt : TypeTable) (L : LayoutTable) (t : TyId) (c : ScalarClass) (n : Nat),
    evalLayoutQuery tt L (.scalarTypeClass t) = .ok (.scalar c n) ↔
      ∃ k l, evalLayoutQuery tt L (.localLayout t) = .ok (.layout k l) ∧
        scalarClassOfKind k = some c ∧ l.size.bytes = n) ∧
  (∀ (p : V2026Prog) (L : LayoutTable) (t : TyId) (ty : Ty) (m : Mutability) (pk : RigidTy),
    nth? (encodeProg p).types.types t = some ty →
    (ty.kind = .ref m pk ∨ ty.kind = .rawPtr m pk) →
    ∃ k, evalLayoutQuery (encodeProg p).types L (.pointeeTypes t) =
      .ok (.pointee k (pointeeLayoutOf L.pointerBits pk))) ∧
  (∀ (p : V2026Prog) (L : LayoutTable), ∃ l,
    evalLayoutQuery (encodeProg p).types L (.builtinLayout 0) = .ok (.layout (.tuple []) l) ∧
      l.size.bytes = 0) ∧
  (∃ p : V2026Prog, ProgWellFormed p ∧
    ∃ b ∈ p.bodies, b.localDecls ≠ [] ∧ b.basicBlocks ≠ [])

/-- Bijectivity of `SimulationInv` and its preservation in both directions by
every step of `M_anneal` on `p` and `M_ref` (`deinitMoves = true`) on
`encodeProg p`. -/
def SimulationInvBijective (p : V2026Prog) : Prop :=
  (∀ s s' rs, SimulationInv s rs → SimulationInv s' rs → s = s') ∧
  (∀ s rs rs', SimulationInv s rs → SimulationInv s rs' →
    rs.stepsExecuted = rs'.stepsExecuted → rs.maxSteps = rs'.maxSteps → rs = rs') ∧
  (∀ s k m, ∃ rs, SimulationInv s rs ∧ rs.stepsExecuted = k ∧ rs.maxSteps = m) ∧
  (∀ s rs s', SimulationInv s rs → rs.stepsExecuted < rs.maxSteps →
    annealStep p s = .running s' →
    ∃ rs', refStep true (encodeProg p) rs = .running rs' ∧ SimulationInv s' rs') ∧
  (∀ s rs rs', SimulationInv s rs → refStep true (encodeProg p) rs = .running rs' →
    annealStep p s = .running rs'.core)

/-- **Correspondence (`deinitMoves = true`).**

1. On every state, one `M_ref` step on `encodeProg p` is exactly one
   `M_anneal` step on `p`;
2. whole-program observations agree for every argument vector and budget;
3. the entry states agree;
4. `SimulationInv` is bijective and preserved by every step;
5. the correspondence is not vacuous (some program returns a value, and some
   program faults with UB, in `M_ref`); and
6. the `deinitMoves` flag is essential: with `deinitMoves = false` the
   observations differ on some program. -/
def CorrespondenceClaim : Prop :=
  (∀ (p : V2026Prog) (st : PState), refStepCore true (encodeProg p) st = annealStep p st) ∧
  (∀ (p : V2026Prog) (args : List Bytes) (fuel : Nat),
    refObs true (encodeProg p) args fuel = annealObs p args fuel) ∧
  (∀ (p : V2026Prog) (args : List Bytes), refInit (encodeProg p) args = annealInit p args) ∧
  (∀ p : V2026Prog, SimulationInvBijective p) ∧
  (∃ (p : V2026Prog) (args : List Bytes) (fuel : Nat) (v : Option Nat) (len : Nat),
    refObs true (encodeProg p) args fuel = .returned v len) ∧
  (∃ (p : V2026Prog) (args : List Bytes) (fuel : Nat) (why : UBReason),
    refObs true (encodeProg p) args fuel = .ub why) ∧
  ¬ (∀ (p : V2026Prog) (args : List Bytes) (fuel : Nat),
    refObs false (encodeProg p) args fuel = annealObs p args fuel)

/-- **Bidirectional fault equivalence (`deinitMoves = true`).**

1. For every program, argument vector and budget, each observation pole
   (`.ub why`, `.unsupported`, `.returned v len`, `.panicked`) is reached by
   `M_anneal` on `p` iff it is reached by `M_ref` on `encodeProg p`;
2. `M_anneal` reaches a fault under some budget iff `M_ref` reaches the
   corresponding fault under some budget; and
3. both poles are inhabited: some program faults with UB, and some program is
   reported unsupported, in both machines. -/
def FaultEquivalenceClaim : Prop :=
  (∀ (p : V2026Prog) (args : List Bytes) (fuel : Nat),
    (∀ why, annealObs p args fuel = .ub why ↔ refObs true (encodeProg p) args fuel = .ub why) ∧
    (annealObs p args fuel = .unsupported ↔ refObs true (encodeProg p) args fuel = .unsupported) ∧
    (∀ v len, annealObs p args fuel = .returned v len ↔
      refObs true (encodeProg p) args fuel = .returned v len) ∧
    (annealObs p args fuel = .panicked ↔ refObs true (encodeProg p) args fuel = .panicked)) ∧
  (∀ (p : V2026Prog) (args : List Bytes) (f : Fault),
    (∃ n, annealObs p args n = faultObs f) ↔
      (∃ maxSteps, refObs true (encodeProg p) args maxSteps = faultObs f)) ∧
  (∃ (p : V2026Prog) (args : List Bytes) (fuel : Nat) (why : UBReason),
    annealObs p args fuel = .ub why ∧ refObs true (encodeProg p) args fuel = .ub why) ∧
  (∃ (p : V2026Prog) (args : List Bytes) (fuel : Nat),
    annealObs p args fuel = .unsupported ∧ refObs true (encodeProg p) args fuel = .unsupported)

/-- The `deinitMovedPlace` latch wiring of the reference machine
(`withValidation` / `operandHooks` / `takePendingMoveDeinit` invariants):

1. the reference strategy threads the same `deinitMoves` flag to
   `evalOperand` and both consumers;
2. constant and copy operands always reset the latch;
3. an indirect move sets it;
4. an unprojected immediate move resets it (and only unprojected immediate
   moves stay immediate);
5. `takePendingMoveDeinit` returns `deinitMoves && latch` and clears the
   latch; and
6. with `deinitMoves = false` the latch is never consulted. -/
def MiriMoveDeinitWiring (dm : Bool) (pb : Nat) (st : PState) : Prop :=
  (twoPhaseStrategy dm).readOperand = twoPhaseReadOperand dm ∧
  (twoPhaseStrategy dm).assignUse = twoPhaseAssignUse dm ∧
  (∀ b ty o ty' st', refEvalOperand true pb st (.const b ty) = .ok (o, ty', st') →
    st'.pendingMoveDeinit = false) ∧
  (∀ p o ty st', refEvalOperand true pb st (.copy p) = .ok (o, ty, st') →
    st'.pendingMoveDeinit = false) ∧
  (∀ p mp ty st', refEvalOperand true pb st (.move p) = .ok (.indirect mp, ty, st') →
    st'.pendingMoveDeinit = true) ∧
  (∀ p b ty st', refEvalOperand true pb st (.move p) = .ok (.immediate b, ty, st') →
    st'.pendingMoveDeinit = false ∧ p.projs = []) ∧
  ((takePendingMoveDeinit dm st).1 = (dm && st.pendingMoveDeinit) ∧
    (takePendingMoveDeinit dm st).2.pendingMoveDeinit = false) ∧
  (takePendingMoveDeinit false st).1 = false

/-- **`deinitMovedPlace` wiring.**

1. With `deinitMoves = true` the two-phase protocol is extensionally the eager
   `M_anneal` operand strategy;
2. the latch wiring `MiriMoveDeinitWiring` holds for every flag, pointer width
   and state;
3. with `deinitMoves = false`, `move` is identical to `copy` at
   `evalOperand` and at both consumers (upstream `lean-miri` behavior);
4. every reachable `M_anneal` state, and every reachable `M_ref` state of an
   encoded program, has a clear latch (phase 2 always consumes what phase 1
   latched);
5. the latch is genuinely set mid-step: some indirect move sets it;
6. moving out of a place (in particular `*ptr`) is a Tree Borrows read: it
   leaves the borrow table exactly as the corresponding `copy` and keeps every
   `.frozen` tag `.frozen`;
7. an assignment `dest = move p` leaves every `.frozen` entry that does not
   overlap the destination window literally unchanged;
8. (*non-vacuity of 4 for `M_anneal`*) some program reaches, from its entry
   state, a `.running` `M_anneal` state in which a phase-1 move evaluation
   (`refEvalOperand true`) *sets* the latch, while the full `M_anneal` step
   from that state leaves it clear again;
9. (*non-vacuity of 4 for `M_ref`*) the same for a bounded, budgeted `M_ref`
   run of `encodeProg p` (`refRunFuel` from the `refInit` entry state, then one
   `refStep`); and
10. (*non-vacuity of 6 and 7*) in such a reachable state, moving out of a
    memory place succeeds both as an operand read and as an assignment
    `dest = move p`, while a `.frozen` borrow entry overlaps the moved
    window but not the destination. -/
def MiriMoveDeinitWiringClaim : Prop :=
  twoPhaseStrategy true = eagerStrategy ∧
  (∀ (dm : Bool) (pb : Nat) (st : PState), MiriMoveDeinitWiring dm pb st) ∧
  (∀ (pb : Nat) (st : PState) (p : SemPlace) (d : DestPlace),
    refEvalOperand false pb st (.move p) = refEvalOperand false pb st (.copy p) ∧
    twoPhaseReadOperand false pb st (.move p) = twoPhaseReadOperand false pb st (.copy p) ∧
    twoPhaseAssignUse false pb st (.move p) d = twoPhaseAssignUse false pb st (.copy p) d) ∧
  (∀ (p : V2026Prog) (args : List Bytes) (n : Nat) (st₀ st : PState),
    annealInit p args = .ok st₀ → annealRun p n st₀ = .running st →
    st.pendingMoveDeinit = false) ∧
  (∀ (p : V2026Prog) (args : List Bytes) (n maxSteps : Nat) (st₀ : PState) (rs : RefState),
    refInit (encodeProg p) args = .ok st₀ →
    refRunFuel true (encodeProg p) n ⟨st₀, 0, maxSteps⟩ = .running rs →
    rs.core.pendingMoveDeinit = false) ∧
  (∃ (pb : Nat) (st : PState) (p : SemPlace) (mp : MPlace) (ty : SemTy) (st' : PState),
    st.pendingMoveDeinit = false ∧
    refEvalOperand true pb st (.move p) = .ok (.indirect mp, ty, st') ∧
    st'.pendingMoveDeinit = true) ∧
  (∀ (pb : Nat) (st : PState) (p : SemPlace) (b : Bytes) (st₁ : PState),
    twoPhaseReadOperand true pb st (.move p) = .ok (b, st₁) →
    (∃ st₂, twoPhaseReadOperand true pb st (.copy p) = .ok (b, st₂) ∧
      st₂.borrows = st₁.borrows) ∧
    ∀ i e, nth? st.borrows i = some e → e.perm = .frozen →
      ∃ e', nth? st₁.borrows i = some e' ∧ e'.tag = e.tag ∧ e'.perm = .frozen) ∧
  (∀ (pb : Nat) (st : PState) (p : SemPlace) (d : DestPlace) (st₁ : PState),
    twoPhaseAssignUse true pb st (.move p) d = .ok st₁ →
    ∀ i e, nth? st.borrows i = some e → e.perm = .frozen → entryOverlapsDest e d = false →
      nth? st₁.borrows i = some e) ∧
  -- 8. non-vacuity of 4 for `M_anneal` (reachable state; the latch is set mid-step)
  (∃ (p : V2026Prog) (args : List Bytes) (n : Nat) (st₀ st : PState) (pb : Nat) (q : SemPlace)
      (mp : MPlace) (ty : SemTy) (stMid st' : PState),
    annealInit p args = .ok st₀ ∧ annealRun p n st₀ = .running st ∧
    refEvalOperand true pb st (.move q) = .ok (.indirect mp, ty, stMid) ∧
    stMid.pendingMoveDeinit = true ∧
    annealStep p st = .running st' ∧ st'.pendingMoveDeinit = false) ∧
  -- 9. non-vacuity of 4 for `M_ref` (reachable budgeted state; the latch is set mid-step)
  (∃ (p : V2026Prog) (args : List Bytes) (n maxSteps : Nat) (st₀ : PState) (rs rs' : RefState)
      (pb : Nat) (q : SemPlace) (mp : MPlace) (ty : SemTy) (stMid : PState),
    refInit (encodeProg p) args = .ok st₀ ∧
    refRunFuel true (encodeProg p) n ⟨st₀, 0, maxSteps⟩ = .running rs ∧
    refEvalOperand true pb rs.core (.move q) = .ok (.indirect mp, ty, stMid) ∧
    stMid.pendingMoveDeinit = true ∧
    refStep true (encodeProg p) rs = .running rs' ∧ rs'.core.pendingMoveDeinit = false) ∧
  -- 10. non-vacuity of 6 and 7 (reachable state, `.frozen` sibling over the moved window)
  (∃ (p : V2026Prog) (args : List Bytes) (n : Nat) (st₀ st : PState) (pb : Nat) (q : SemPlace)
      (mp : MPlace) (ty : SemTy) (stMid : PState) (b : Bytes) (st₁ : PState) (d : DestPlace)
      (st₂ : PState) (i : Nat) (e : BorrowEntry),
    annealInit p args = .ok st₀ ∧ annealRun p n st₀ = .running st ∧
    refEvalOperand true pb st (.move q) = .ok (.indirect mp, ty, stMid) ∧
    twoPhaseReadOperand true pb st (.move q) = .ok (b, st₁) ∧
    twoPhaseAssignUse true pb st (.move q) d = .ok st₂ ∧
    nth? st.borrows i = some e ∧ e.perm = .frozen ∧
    entryOverlapsDest e (.mem mp) = true ∧ entryOverlapsDest e d = false)

/-- A `u8` scalar value (used by the concrete witnesses below). -/
def u8Value (n : Nat) : Value := .scalar { bits := n, sizeBytes := 1 }

/-- `u8` primitive layout (`1` byte) for the live `evalOperand` union and
typed-pointer bridge claims. -/
def claimU8Layout : TypeLayout :=
  { size := { bytes := 1 }, align := { bytes := 1 },
    backendRepr := .scalar (.initialized (.int 8 false) { start := 0, end_ := 255 }),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- `u16` primitive layout (`2` bytes) for the live `evalOperand` union claim. -/
def claimU16Layout : TypeLayout :=
  { size := { bytes := 2 }, align := { bytes := 2 },
    backendRepr := .scalar (.initialized (.int 16 false) { start := 0, end_ := 65535 }),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- `union U { a: u8, b: u16 }` layout (`2` bytes, both fields at offset `0`). -/
def claimUnionULayout : TypeLayout :=
  { size := { bytes := 2 }, align := { bytes := 2 }, backendRepr := .memory,
    fields := .union 2, variants := .single 0, isUninhabited := false, fieldLayouts := [0, 1] }

/-- Layout table for `union U { a: u8, b: u16 }`. -/
def claimUnionLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [claimU8Layout, claimU16Layout, claimUnionULayout] }

/-- `u8` type (`layoutIdx = 0`). -/
def claimU8Ty : Ty := { kind := .uint .u8, layoutIdx := 0 }

/-- `u16` type (`layoutIdx = 1`). -/
def claimU16Ty : Ty := { kind := .uint .u16, layoutIdx := 1 }

/-- Local declarations `_0 : u8, _1 : U` for the union claim. -/
def claimUnionDecls : List LocalDecl :=
  [{ mutability := .mut, ty := claimU8Ty, debugName := none },
   { mutability := .mut, ty := { kind := .adt "U" [], layoutIdx := 2 }, debugName := none }]

/-- `(u8, u8)` tuple layout (`2` bytes, fields at offsets `0` and `1`). -/
def claimPairLayout : TypeLayout :=
  { size := ⟨2⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .arbitrary [⟨0⟩, ⟨1⟩] [0, 1], variants := .single 0, isUninhabited := false,
    fieldLayouts := [0, 0] }

/-- `[(u8, u8); 2]` array layout (`4` bytes, stride `2`). -/
def claimPairArrLayout : TypeLayout :=
  { size := ⟨4⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .array ⟨2⟩ 2, variants := .single 0, isUninhabited := false, fieldLayouts := [1] }

/-- Thin-pointer layout (`8` bytes). -/
def claimPtrLayout : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false, fieldLayouts := [] }

/-- Layout table for the typed thin-pointer deref claim (`[(u8, u8); 2]`). -/
def claimPairArrLayouts : LayoutTable :=
  { emptyLayoutTable with
    entries := [
      { size := ⟨1⟩, align := ⟨1⟩, backendRepr := .memory, fields := .primitive,
        variants := .single 0, isUninhabited := false, fieldLayouts := [] },
      claimPairLayout, claimPairArrLayout, claimPtrLayout] }

/-- Local declarations `_0 : u8, _1 : [(u8, u8); 2], _2 : *mut (u8, u8), _3 : &(u8, u8)`. -/
def claimPairArrDecls : List LocalDecl :=
  [{ mutability := .mut, ty := claimU8Ty, debugName := .none },
   { mutability := .mut, ty := { kind := .array (.tuple [.uint .u8, .uint .u8]) 2, layoutIdx := 2 },
     debugName := .none },
   { mutability := .mut, ty := { kind := .rawPtr .mut (.tuple [.uint .u8, .uint .u8]), layoutIdx := 3 },
     debugName := .none },
   { mutability := .not, ty := { kind := .ref .not (.tuple [.uint .u8, .uint .u8]), layoutIdx := 3 },
     debugName := .none }]

/-- Shared borrow table for the `Deref` move claims (`tag 2` active on `_1`,
`tag 3` `.frozen` on `_1`). -/
def claimDerefBorrows : List BorrowEntry :=
  [{ tag := 2, targetLocal := 1, targetProjection := [], perm := .active },
   { tag := 3, targetLocal := 1, targetProjection := [], perm := .frozen }]

/-- **Live bridge to `Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand`.**

(a) Moving an unprojected root local returns its value and sets the slot to
    `.uninit` in both legacy (`false`) and `deinitProjectedMoves := true` modes
    (and re-reading it in `true` mode faults with `.ub`), while copying it
    leaves `locals` unchanged.

(b) In the default mode (`deinitProjectedMoves := false`), moving a projected
    place (field, element, subslice, downcast, cast, or `Deref`) is identical
    to copying it.

(c) With `deinitProjectedMoves := true` (Episode 1), moves genuinely
    deinitialize projected, union, and dereferenced places:

    1. (*field moves, all states*) moving field `idx` of an initialized
       aggregate local (in a context without local declarations) returns the
       field, after which re-reading that field faults with `.ub` while every
       other field (without a moved-out leaf) is still read unchanged;
    2. (*`constantIndex` element moves, all states*) the same for a
       `constantIndex` element of an initialized array local;
    3. (*dynamic `.index` element moves, all states*) the same for an
       `.index idxLocal` element of an initialized array local when `idxLocal`
       holds `usize` index `idx` (`l ≠ idxLocal`);
    4. (*subslice move*) moving `_1[1..3]` (or `_1[1..-1]` with
       `fromEnd := true`) out of `_1 = [10, 11, 12, 13]` returns `[11, 12]`;
       afterwards `_1[1]` and `_1[2]` fault with `.ub` while `_1[0] = 10` and
       `_1[3] = 13` stay readable, and the whole array faults;
    5. (*union field move & re-init*) moving `_1.a` (`u8`) out of
       `union U { a: u8, b: u16 } = U { b: 0x0302 }` returns `2` and
       deinitializes byte `0` (`deinitUnionSubPlace`): re-reading `_1.a` or the
       overlapping `_1.b` faults with `.ub`, the whole union remains readable as
       its raw byte overlay, re-initializing `_1.a = 9` makes `_1.b` read
       `0x0309`, and legacy `false` mode keeps `_1` unchanged;
    6. (*untyped `Deref` move*) with `_2 = &raw mut _1` (active tag `2`) and
       `_3 = &_1` (`.frozen` tag `3`), moving `*_2` out of `_1 = 5` returns
       `5` and deinitializes `_1`; afterwards reading `*_2`, `*_3` (whose tag
       is still `.frozen`: the borrow table is untouched) or `_1` faults with
       `.ub`;
    7. (*typed thin-pointer `Deref` + field move*) with `_1 = [(1, 2), (3, 4)]`
       and `_2 : *mut (u8, u8)` at byte offset `2` (`&raw mut _1[1]`), moving
       `(*_2).0` (`deinitTypedThinPtrDeref`) returns `3` and deinitializes
       exactly `_1[1].0`: `(*_2).1 = 4`, `(*_3).1 = 4`, and `_1[0] = (1, 2)`
       stay readable while `(*_2).0`, `*_3`, `_1[1]`, and `_1` fault with `.ub`;
    8. (*slice fat-pointer `Deref` element and subslice moves*) with
       `_1 = [10, 11, 12, 13]` and slice fat pointer `_2 : *mut [u8]`, moving
       `(*_2)[1]` (`deinitSliceFatPtrDeref`) returns `11` and deinitializes
       `_1[1]`, and moving `(*_2)[1..3]` returns `[11, 12]` and deinitializes
       `_1[1..3]` while keeping `_1[0] = 10` and `_1[3] = 13` readable;
    9. (*read guard, all states*) every read in this mode faults on a value
       that contains a moved-out leaf;
   10. (*non-vacuity of 9*) a default-mode copy can indeed return a value
       containing a moved-out leaf;
   11. (*`D4` multi-operand left-to-right field evaluation on `evalOperands`,
       all states*) for any initialized aggregate local, `[copy _l.idx, move _l.idx]`
       returns `[v, v]` and deinitializes field `idx`, `[move _l.idx, copy _l.idx]`
       and `[move _l.idx, move _l.idx]` fault with `.ub`, `[move _l.idx, copy _l.j]`
       (`j ≠ idx`) returns `[v, w]`, and legacy `false` mode returns `[v, v]` on
       `[move _l.idx, copy _l.idx]`;
   12. (*`D7` multi-operand `Deref` evaluation on `evalOperands` with a sibling
       `.frozen` borrow*) on untyped `*mut u8` (`_2`) with sibling `&u8` (`_3`
       `.frozen`), `[copy (*_2), move (*_2)]` and `[copy (*_3), move (*_2)]`
       return `[5, 5]` and deinitialize `_1`, while `[move (*_2), copy (*_2)]`
       and `[move (*_2), copy (*_3)]` fault with `.ub` (versus `[5, 5]` in legacy
       `false` mode); and on typed `*mut (u8, u8)` (`_2` at byte offset `2`) with
       sibling `&(u8, u8)` (`_3` `.frozen`), `[copy (*_2).0, move (*_2).0]`
       returns `[3, 3]`, `[move (*_2).0, copy (*_2).0]` and
       `[move (*_2).0, copy (*_3).0]` fault with `.ub`, and
       `[move (*_2).0, copy (*_3).1]` returns `[3, 4]` while preserving the
       sibling `.frozen` borrow;
   13. (*root moves in every typed context, all states*) for any local
       declarations, copying an initialized root local `_l` (without a moved-out
       leaf) returns its value; if the moved value is not zero-sized
       (`moveValueIsZeroSized`), moving `_l` returns it and sets the slot to
       `.uninit`, `[copy _l, move _l]` returns `[v, v]`, and `[move _l, copy _l]` /
       `[move _l, move _l]` fault with `.ub`; if it is zero-sized (a `0`-byte
       declared type) the move deinitializes nothing and `[move _l, copy _l]`
       returns `[v, v]` with `locals` unchanged;
   14. (*non-vacuity of the zero-sized polarity of 13*) some typed context holds
       a non-`unit` value that is zero-sized there (but not in the untyped
       context) and survives `[move _l, copy _l]`;
   15. (*projected field moves in every non-union typed context, all states*) for
       any local declarations in which `_l.idx` does not touch a union, copying an
       initialized aggregate field `_l.idx` (without a moved-out leaf) returns its
       value; if the moved field is not zero-sized (`moveValueIsZeroSized`), moving
       `_l.idx` returns it and deinitializes only that field so `[copy _l.idx,
       move _l.idx]` returns `[v, v]`, `[move _l.idx, copy _l.idx]` and `[move _l.idx,
       move _l.idx]` fault with `.ub`, and `[move _l.idx, copy _l.j]` returns
       `[v, w]` on every non-union sibling field `j ≠ idx`; if the moved field is
       zero-sized, moving `_l.idx` leaves the aggregate intact so both
       `[move _l.idx, copy _l.idx]` and `[move _l.idx, copy _l]` succeed; and
   16. (*non-vacuity of both polarities of 15*) on a typed aggregate `_1 : ((), u8)`
       whose `0`-byte field holds `.aggregate 0 [] ≠ .unit`, `[move _1.0, copy _1]`
       succeeds in the typed context while faulting with `.ub` in the untyped
       context, and `[move _1.1, copy _1]` faults with `.ub`. -/
def TrustedProjectedMoveDeinitClaim : Prop :=
  -- (a) root moves (legacy `false` and `deinitProjectedMoves := true`)
  (∀ (locals locals' : List LocalSlot) (l : Local) (v : Value) (borrows : List BorrowEntry)
      (globals : List CapturedAllocation) (layouts : LayoutTable)
      (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
      (callStack : List SavedCallerFrame),
    Trusted.Sequence.get? locals l = some (.init v) →
    Trusted.Sequence.set? locals l .uninit = some locals' →
    evalOperand locals (.move ⟨l, []⟩) borrows globals layouts callerLocals localDecls callStack =
      .ok v locals' ∧
    evalOperand locals (.copy ⟨l, []⟩) borrows globals layouts callerLocals localDecls callStack =
      .ok v locals ∧
    (v ≠ .unit → valueContainsMovedUninit v = false →
      evalOperand locals (.move ⟨l, []⟩) borrows globals layouts callerLocals [] callStack true =
        .ok v locals' ∧
      evalOperand locals (.copy ⟨l, []⟩) borrows globals layouts callerLocals [] callStack true =
        .ok v locals ∧
      evalOperand locals' (.copy ⟨l, []⟩) borrows globals layouts callerLocals [] callStack true =
        .ub)) ∧
  -- (b) legacy projected move = copy
  (∀ (locals : List LocalSlot) (l : Local) (e : ProjectionElem) (es : List ProjectionElem)
      (borrows : List BorrowEntry) (globals : List CapturedAllocation) (layouts : LayoutTable)
      (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
      (callStack : List SavedCallerFrame),
    evalOperand locals (.move ⟨l, e :: es⟩) borrows globals layouts callerLocals localDecls
        callStack false =
      evalOperand locals (.copy ⟨l, e :: es⟩) borrows globals layouts callerLocals localDecls
        callStack false) ∧
  -- (c1) field moves
  (∀ (locals : List LocalSlot) (l : Local) (variant : VariantIdx) (fields : List Value)
      (idx : FieldIdx) (fty : Ty) (v : Value) (borrows : List BorrowEntry)
      (globals : List CapturedAllocation) (layouts : LayoutTable)
      (callerLocals : List LocalSlot) (callStack : List SavedCallerFrame),
    Trusted.Sequence.get? locals l = some (.init (.aggregate variant fields)) →
    Trusted.Sequence.get? fields idx = some v →
    v ≠ .unit → valueContainsMovedUninit v = false →
    ∃ locals',
      evalOperand locals (.move ⟨l, [.field idx fty]⟩) borrows globals layouts callerLocals []
        callStack true = .ok v locals' ∧
      evalOperand locals' (.copy ⟨l, [.field idx fty]⟩) borrows globals layouts callerLocals []
        callStack true = .ub ∧
      ∀ (j : FieldIdx) (jty : Ty) (w : Value), j ≠ idx →
        Trusted.Sequence.get? fields j = some w → valueContainsMovedUninit w = false →
        evalOperand locals' (.copy ⟨l, [.field j jty]⟩) borrows globals layouts callerLocals []
          callStack true = .ok w locals') ∧
  -- (c2) constantIndex element moves
  (∀ (locals : List LocalSlot) (l : Local) (elems : List Value) (idx minLen : Nat) (v : Value)
      (borrows : List BorrowEntry) (globals : List CapturedAllocation) (layouts : LayoutTable)
      (callerLocals : List LocalSlot) (callStack : List SavedCallerFrame),
    Trusted.Sequence.get? locals l = some (.init (.aggregate 0 elems)) →
    minLen ≤ elems.length →
    Trusted.Sequence.get? elems idx = some v →
    v ≠ .unit → valueContainsMovedUninit v = false →
    ∃ locals',
      evalOperand locals (.move ⟨l, [.constantIndex idx minLen false]⟩) borrows globals layouts
        callerLocals [] callStack true = .ok v locals' ∧
      evalOperand locals' (.copy ⟨l, [.constantIndex idx minLen false]⟩) borrows globals layouts
        callerLocals [] callStack true = .ub ∧
      ∀ (j : Nat) (w : Value), j ≠ idx →
        Trusted.Sequence.get? elems j = some w → valueContainsMovedUninit w = false →
        evalOperand locals' (.copy ⟨l, [.constantIndex j minLen false]⟩) borrows globals layouts
          callerLocals [] callStack true = .ok w locals') ∧
  -- (c3) dynamic `.index` element moves
  (∀ (locals : List LocalSlot) (l idxLocal : Local) (elems : List Value) (idx : Nat) (v : Value)
      (borrows : List BorrowEntry) (globals : List CapturedAllocation) (layouts : LayoutTable)
      (callerLocals : List LocalSlot) (callStack : List SavedCallerFrame),
    l ≠ idxLocal →
    Trusted.Sequence.get? locals l = some (.init (.aggregate 0 elems)) →
    Trusted.Sequence.get? locals idxLocal = some (.init (.scalar { bits := idx, sizeBytes := 8 })) →
    Trusted.Sequence.get? elems idx = some v →
    v ≠ .unit → valueContainsMovedUninit v = false →
    ∃ locals',
      evalOperand locals (.move ⟨l, [.index idxLocal]⟩) borrows globals layouts
        callerLocals [] callStack true = .ok v locals' ∧
      evalOperand locals' (.copy ⟨l, [.index idxLocal]⟩) borrows globals layouts
        callerLocals [] callStack true = .ub ∧
      ∀ (j : Nat) (w : Value), j ≠ idx →
        Trusted.Sequence.get? elems j = some w → valueContainsMovedUninit w = false →
        evalOperand locals' (.copy ⟨l, [.constantIndex j 0 false]⟩) borrows globals layouts
          callerLocals [] callStack true = .ok w locals') ∧
  -- (c4) subslice move (`fromEnd := false` and `fromEnd := true`)
  (∃ locals' : List LocalSlot,
    evalOperand [.uninit, .init (.aggregate 0 [u8Value 10, u8Value 11, u8Value 12, u8Value 13])]
        (.move ⟨1, [.subslice 1 3 false]⟩) [] [] emptyLayoutTable [] [] [] true =
      .ok (.aggregate 0 [u8Value 11, u8Value 12]) locals' ∧
    evalOperand [.uninit, .init (.aggregate 0 [u8Value 10, u8Value 11, u8Value 12, u8Value 13])]
        (.move ⟨1, [.subslice 1 1 true]⟩) [] [] emptyLayoutTable [] [] [] true =
      .ok (.aggregate 0 [u8Value 11, u8Value 12]) locals' ∧
    evalOperand locals' (.copy ⟨1, [.constantIndex 1 4 false]⟩) [] [] emptyLayoutTable [] [] []
      true = .ub ∧
    evalOperand locals' (.copy ⟨1, [.constantIndex 2 4 false]⟩) [] [] emptyLayoutTable [] [] []
      true = .ub ∧
    evalOperand locals' (.copy ⟨1, [.constantIndex 0 4 false]⟩) [] [] emptyLayoutTable [] [] []
      true = .ok (u8Value 10) locals' ∧
    evalOperand locals' (.copy ⟨1, [.constantIndex 3 4 false]⟩) [] [] emptyLayoutTable [] [] []
      true = .ok (u8Value 13) locals' ∧
    evalOperand locals' (.copy ⟨1, []⟩) [] [] emptyLayoutTable [] [] [] true = .ub) ∧
  -- (c5) union field move and re-initialization (`deinitUnionSubPlace`)
  (∃ locals' locals'' : List LocalSlot,
    evalOperand [.uninit, .init (.aggregate 0 [.unit, .scalar ⟨770, 2⟩])]
        (.move ⟨1, [.field 0 claimU8Ty]⟩) [] [] claimUnionLayouts [] claimUnionDecls [] true =
      .ok (u8Value 2) locals' ∧
    evalOperand locals' (.copy ⟨1, [.field 0 claimU8Ty]⟩) [] [] claimUnionLayouts []
      claimUnionDecls [] true = .ub ∧
    evalOperand locals' (.copy ⟨1, [.field 1 claimU16Ty]⟩) [] [] claimUnionLayouts []
      claimUnionDecls [] true = .ub ∧
    evalOperand locals' (.copy ⟨1, []⟩) [] [] claimUnionLayouts [] claimUnionDecls [] true =
      .ok (.aggregate 0 [.unit, .unit, .aggregate 0 [.scalar ⟨0, 0⟩, .scalar ⟨3, 1⟩]]) locals' ∧
    writePlaceValue locals' [] ⟨1, [.field 0 claimU8Ty]⟩ (u8Value 9) claimUnionDecls
      claimUnionLayouts = .ok locals'' ∧
    evalOperand locals'' (.copy ⟨1, [.field 1 claimU16Ty]⟩) [] [] claimUnionLayouts []
      claimUnionDecls [] true = .ok (.scalar ⟨777, 2⟩) locals'' ∧
    evalOperand [.uninit, .init (.aggregate 0 [.unit, .scalar ⟨770, 2⟩])]
        (.move ⟨1, [.field 0 claimU8Ty]⟩) [] [] claimUnionLayouts [] claimUnionDecls [] false =
      .ok (u8Value 2) [.uninit, .init (.aggregate 0 [.unit, .scalar ⟨770, 2⟩])]) ∧
  -- (c6) untyped `Deref` move with a sibling `.frozen` borrow
  (∃ locals' : List LocalSlot,
    evalOperand
        [.uninit, .init (u8Value 5), .init (.ptr { allocId := 2, offsetBytes := 0 } 8),
          .init (.ptr { allocId := 3, offsetBytes := 0 } 8)]
        (.move ⟨2, [.deref]⟩) claimDerefBorrows [] emptyLayoutTable [] [] [] true =
      .ok (u8Value 5) locals' ∧
    Trusted.Sequence.get? locals' 1 = some .uninit ∧
    evalOperand locals' (.copy ⟨2, [.deref]⟩) claimDerefBorrows [] emptyLayoutTable [] [] []
      true = .ub ∧
    evalOperand locals' (.copy ⟨3, [.deref]⟩) claimDerefBorrows [] emptyLayoutTable [] [] []
      true = .ub ∧
    evalOperand locals' (.copy ⟨1, []⟩) [] [] emptyLayoutTable [] [] [] true = .ub) ∧
  -- (c7) typed thin-pointer `Deref` + field move (`deinitTypedThinPtrDeref`)
  (∃ locals' : List LocalSlot,
    evalOperand
        [.uninit,
          .init (.aggregate 0 [.aggregate 0 [u8Value 1, u8Value 2],
            .aggregate 0 [u8Value 3, u8Value 4]]),
          .init (.ptr { allocId := 2, offsetBytes := 2 } 8),
          .init (.ptr { allocId := 3, offsetBytes := 2 } 8)]
        (.move ⟨2, [.deref, .field 0 claimU8Ty]⟩) claimDerefBorrows [] claimPairArrLayouts []
        claimPairArrDecls [] true = .ok (u8Value 3) locals' ∧
    evalOperand locals' (.copy ⟨2, [.deref, .field 1 claimU8Ty]⟩) claimDerefBorrows []
      claimPairArrLayouts [] claimPairArrDecls [] true = .ok (u8Value 4) locals' ∧
    evalOperand locals' (.copy ⟨3, [.deref, .field 1 claimU8Ty]⟩) claimDerefBorrows []
      claimPairArrLayouts [] claimPairArrDecls [] true = .ok (u8Value 4) locals' ∧
    evalOperand locals' (.copy ⟨1, [.constantIndex 0 2 false]⟩) claimDerefBorrows []
      claimPairArrLayouts [] claimPairArrDecls [] true =
        .ok (.aggregate 0 [u8Value 1, u8Value 2]) locals' ∧
    evalOperand locals' (.copy ⟨2, [.deref, .field 0 claimU8Ty]⟩) claimDerefBorrows []
      claimPairArrLayouts [] claimPairArrDecls [] true = .ub ∧
    evalOperand locals' (.copy ⟨3, [.deref]⟩) claimDerefBorrows [] claimPairArrLayouts []
      claimPairArrDecls [] true = .ub ∧
    evalOperand locals' (.copy ⟨1, [.constantIndex 1 2 false]⟩) claimDerefBorrows []
      claimPairArrLayouts [] claimPairArrDecls [] true = .ub ∧
    evalOperand locals' (.copy ⟨1, []⟩) claimDerefBorrows [] claimPairArrLayouts []
      claimPairArrDecls [] true = .ub) ∧
  -- (c8) slice fat-pointer `Deref` element and subslice moves (`deinitSliceFatPtrDeref`)
  (∃ localsElem localsSub : List LocalSlot,
    let initSliceLocals : List LocalSlot :=
      [.uninit,
        .init (.aggregate 0 [u8Value 10, u8Value 11, u8Value 12, u8Value 13]),
        .init (.aggregate 0 [.ptr { allocId := 2, offsetBytes := 0 } 8,
          .scalar { bits := 4, sizeBytes := 8 }])]
    evalOperand initSliceLocals (.move ⟨2, [.deref, .constantIndex 1 4 false]⟩) claimDerefBorrows
      [] emptyLayoutTable [] [] [] true = .ok (u8Value 11) localsElem ∧
    evalOperand localsElem (.copy ⟨2, [.deref, .constantIndex 0 4 false]⟩) claimDerefBorrows
      [] emptyLayoutTable [] [] [] true = .ok (u8Value 10) localsElem ∧
    evalOperand localsElem (.copy ⟨2, [.deref, .constantIndex 2 4 false]⟩) claimDerefBorrows
      [] emptyLayoutTable [] [] [] true = .ok (u8Value 12) localsElem ∧
    evalOperand localsElem (.copy ⟨2, [.deref, .constantIndex 3 4 false]⟩) claimDerefBorrows
      [] emptyLayoutTable [] [] [] true = .ok (u8Value 13) localsElem ∧
    evalOperand localsElem (.copy ⟨2, [.deref, .constantIndex 1 4 false]⟩) claimDerefBorrows
      [] emptyLayoutTable [] [] [] true = .ub ∧
    evalOperand initSliceLocals (.move ⟨2, [.deref, .subslice 1 3 false]⟩) claimDerefBorrows
      [] emptyLayoutTable [] [] [] true =
        .ok (.aggregate 0 [u8Value 11, u8Value 12]) localsSub ∧
    evalOperand localsSub (.copy ⟨1, [.constantIndex 0 4 false]⟩) claimDerefBorrows
      [] emptyLayoutTable [] [] [] true = .ok (u8Value 10) localsSub ∧
    evalOperand localsSub (.copy ⟨1, [.constantIndex 1 4 false]⟩) claimDerefBorrows
      [] emptyLayoutTable [] [] [] true = .ub ∧
    evalOperand localsSub (.copy ⟨1, [.constantIndex 2 4 false]⟩) claimDerefBorrows
      [] emptyLayoutTable [] [] [] true = .ub ∧
    evalOperand localsSub (.copy ⟨1, [.constantIndex 3 4 false]⟩) claimDerefBorrows
      [] emptyLayoutTable [] [] [] true = .ok (u8Value 13) localsSub) ∧
  -- (c9) read guard
  (∀ (locals : List LocalSlot) (p : Place) (borrows : List BorrowEntry)
      (globals : List CapturedAllocation) (layouts : LayoutTable)
      (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
      (callStack : List SavedCallerFrame) (v : Value) (locals' : List LocalSlot),
    evalOperand locals (.copy p) borrows globals layouts callerLocals localDecls callStack =
      .ok v locals' →
    valueContainsMovedUninit v = true →
    evalOperand locals (.copy p) borrows globals layouts callerLocals localDecls callStack true =
        .ub ∧
      evalOperand locals (.move p) borrows globals layouts callerLocals localDecls callStack
        true = .ub) ∧
  -- (c10) non-vacuity of (c9)
  (∃ (locals : List LocalSlot) (p : Place) (v : Value) (locals' : List LocalSlot),
    evalOperand locals (.copy p) [] [] emptyLayoutTable [] [] [] = .ok v locals' ∧
    valueContainsMovedUninit v = true) ∧
  -- (c11) D4 multi-operand left-to-right field evaluation on live `evalOperands`
  (∀ (locals : List LocalSlot) (l : Local) (variant : VariantIdx) (fields : List Value)
      (idx : FieldIdx) (fty : Ty) (v : Value) (borrows : List BorrowEntry)
      (globals : List CapturedAllocation) (layouts : LayoutTable)
      (callerLocals : List LocalSlot) (callStack : List SavedCallerFrame),
    Trusted.Sequence.get? locals l = some (.init (.aggregate variant fields)) →
    Trusted.Sequence.get? fields idx = some v →
    v ≠ .unit → valueContainsMovedUninit v = false →
    ∃ locals',
      evalOperands locals [.copy ⟨l, [.field idx fty]⟩, .move ⟨l, [.field idx fty]⟩]
        borrows globals layouts callerLocals [] callStack true = .ok [v, v] locals' ∧
      evalOperands locals [.move ⟨l, [.field idx fty]⟩, .copy ⟨l, [.field idx fty]⟩]
        borrows globals layouts callerLocals [] callStack true = .ub ∧
      evalOperands locals [.move ⟨l, [.field idx fty]⟩, .move ⟨l, [.field idx fty]⟩]
        borrows globals layouts callerLocals [] callStack true = .ub ∧
      evalOperands locals [.move ⟨l, [.field idx fty]⟩, .copy ⟨l, [.field idx fty]⟩]
        borrows globals layouts callerLocals [] callStack false = .ok [v, v] locals ∧
      ∀ (j : FieldIdx) (jty : Ty) (w : Value), j ≠ idx →
        Trusted.Sequence.get? fields j = some w → valueContainsMovedUninit w = false →
        evalOperands locals [.move ⟨l, [.field idx fty]⟩, .copy ⟨l, [.field j jty]⟩]
          borrows globals layouts callerLocals [] callStack true = .ok [v, w] locals') ∧
  -- (c12) D7 multi-operand `Deref` evaluation on live `evalOperands` with a sibling `.frozen` borrow
  (∃ localsDeref localsTyped : List LocalSlot,
    let initDeref : List LocalSlot :=
      [.uninit, .init (u8Value 5), .init (.ptr { allocId := 2, offsetBytes := 0 } 8),
        .init (.ptr { allocId := 3, offsetBytes := 0 } 8)]
    let initTyped : List LocalSlot :=
      [.uninit,
        .init (.aggregate 0 [.aggregate 0 [u8Value 1, u8Value 2],
          .aggregate 0 [u8Value 3, u8Value 4]]),
        .init (.ptr { allocId := 2, offsetBytes := 2 } 8),
        .init (.ptr { allocId := 3, offsetBytes := 2 } 8)]
    evalOperands initDeref [.copy ⟨2, [.deref]⟩, .move ⟨2, [.deref]⟩] claimDerefBorrows []
      emptyLayoutTable [] [] [] true = .ok [u8Value 5, u8Value 5] localsDeref ∧
    evalOperands initDeref [.copy ⟨3, [.deref]⟩, .move ⟨2, [.deref]⟩] claimDerefBorrows []
      emptyLayoutTable [] [] [] true = .ok [u8Value 5, u8Value 5] localsDeref ∧
    evalOperands initDeref [.move ⟨2, [.deref]⟩, .copy ⟨2, [.deref]⟩] claimDerefBorrows []
      emptyLayoutTable [] [] [] true = .ub ∧
    evalOperands initDeref [.move ⟨2, [.deref]⟩, .copy ⟨3, [.deref]⟩] claimDerefBorrows []
      emptyLayoutTable [] [] [] true = .ub ∧
    evalOperands initDeref [.move ⟨2, [.deref]⟩, .copy ⟨2, [.deref]⟩] claimDerefBorrows []
      emptyLayoutTable [] [] [] false = .ok [u8Value 5, u8Value 5] initDeref ∧
    evalOperands initTyped
      [.copy ⟨2, [.deref, .field 0 claimU8Ty]⟩, .move ⟨2, [.deref, .field 0 claimU8Ty]⟩]
      claimDerefBorrows [] claimPairArrLayouts [] claimPairArrDecls [] true =
        .ok [u8Value 3, u8Value 3] localsTyped ∧
    evalOperands initTyped
      [.move ⟨2, [.deref, .field 0 claimU8Ty]⟩, .copy ⟨2, [.deref, .field 0 claimU8Ty]⟩]
      claimDerefBorrows [] claimPairArrLayouts [] claimPairArrDecls [] true = .ub ∧
    evalOperands initTyped
      [.move ⟨2, [.deref, .field 0 claimU8Ty]⟩, .copy ⟨3, [.deref, .field 0 claimU8Ty]⟩]
      claimDerefBorrows [] claimPairArrLayouts [] claimPairArrDecls [] true = .ub ∧
    evalOperands initTyped
      [.move ⟨2, [.deref, .field 0 claimU8Ty]⟩, .copy ⟨3, [.deref, .field 1 claimU8Ty]⟩]
      claimDerefBorrows [] claimPairArrLayouts [] claimPairArrDecls [] true =
        .ok [u8Value 3, u8Value 4] localsTyped) ∧
  -- (c13) root moves in every typed context (any `localDecls`), both zero-sized
  --       polarities, and their left-to-right order on live `evalOperands`
  (∀ (locals locals' : List LocalSlot) (l : Local) (v : Value) (borrows : List BorrowEntry)
      (globals : List CapturedAllocation) (layouts : LayoutTable)
      (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
      (callStack : List SavedCallerFrame),
    Trusted.Sequence.get? locals l = some (.init v) →
    Trusted.Sequence.set? locals l .uninit = some locals' →
    valueContainsMovedUninit v = false →
    evalOperand locals (.copy ⟨l, []⟩) borrows globals layouts callerLocals localDecls callStack
      true = .ok v locals ∧
    (moveValueIsZeroSized localDecls layouts (placeTyResolved localDecls layouts ⟨l, []⟩) v =
        false →
      evalOperand locals (.move ⟨l, []⟩) borrows globals layouts callerLocals localDecls
        callStack true = .ok v locals' ∧
      evalOperands locals [.copy ⟨l, []⟩, .move ⟨l, []⟩] borrows globals layouts callerLocals
        localDecls callStack true = .ok [v, v] locals' ∧
      evalOperands locals [.move ⟨l, []⟩, .copy ⟨l, []⟩] borrows globals layouts callerLocals
        localDecls callStack true = .ub ∧
      evalOperands locals [.move ⟨l, []⟩, .move ⟨l, []⟩] borrows globals layouts callerLocals
        localDecls callStack true = .ub) ∧
    (moveValueIsZeroSized localDecls layouts (placeTyResolved localDecls layouts ⟨l, []⟩) v =
        true →
      evalOperand locals (.move ⟨l, []⟩) borrows globals layouts callerLocals localDecls
        callStack true = .ok v locals ∧
      evalOperands locals [.move ⟨l, []⟩, .copy ⟨l, []⟩] borrows globals layouts callerLocals
        localDecls callStack true = .ok [v, v] locals)) ∧
  -- (c14) non-vacuity of the zero-sized polarity of (c13) for a non-`unit` value
  --       that the untyped context would deinitialize
  (∃ (locals : List LocalSlot) (l : Local) (v : Value) (layouts : LayoutTable)
      (localDecls : List LocalDecl),
    v ≠ .unit ∧ Trusted.Sequence.get? locals l = some (.init v) ∧
    moveValueIsZeroSized localDecls layouts (placeTyResolved localDecls layouts ⟨l, []⟩) v =
      true ∧
    moveValueIsZeroSized [] layouts (placeTyResolved [] layouts ⟨l, []⟩) v = false ∧
    evalOperands locals [.move ⟨l, []⟩, .copy ⟨l, []⟩] [] [] layouts [] localDecls [] true =
      .ok [v, v] locals) ∧
  -- (c15) projected field moves in every non-union typed context (any `localDecls`),
  --       both zero-sized polarities, sibling preservation, and live `evalOperands` order
  (∀ (locals : List LocalSlot) (l : Local) (variant : VariantIdx) (fields : List Value)
      (idx : FieldIdx) (fty : Ty) (v : Value) (borrows : List BorrowEntry)
      (globals : List CapturedAllocation) (layouts : LayoutTable)
      (callerLocals : List LocalSlot) (localDecls : List LocalDecl)
      (callStack : List SavedCallerFrame),
    Trusted.Sequence.get? locals l = some (.init (.aggregate variant fields)) →
    Trusted.Sequence.get? fields idx = some v →
    placeTouchesUnion localDecls layouts ⟨l, [.field idx fty]⟩ = false →
    valueContainsMovedUninit v = false →
    evalOperand locals (.copy ⟨l, [.field idx fty]⟩) borrows globals layouts callerLocals
      localDecls callStack true = .ok v locals ∧
    (moveValueIsZeroSized localDecls layouts
        (placeTyResolved localDecls layouts ⟨l, [.field idx fty]⟩) v = false →
      ∃ locals',
        evalOperand locals (.move ⟨l, [.field idx fty]⟩) borrows globals layouts callerLocals
          localDecls callStack true = .ok v locals' ∧
        evalOperands locals [.copy ⟨l, [.field idx fty]⟩, .move ⟨l, [.field idx fty]⟩]
          borrows globals layouts callerLocals localDecls callStack true = .ok [v, v] locals' ∧
        evalOperands locals [.move ⟨l, [.field idx fty]⟩, .copy ⟨l, [.field idx fty]⟩]
          borrows globals layouts callerLocals localDecls callStack true = .ub ∧
        evalOperands locals [.move ⟨l, [.field idx fty]⟩, .move ⟨l, [.field idx fty]⟩]
          borrows globals layouts callerLocals localDecls callStack true = .ub ∧
        ∀ (j : FieldIdx) (jty : Ty) (w : Value), j ≠ idx →
          Trusted.Sequence.get? fields j = some w →
          placeTouchesUnion localDecls layouts ⟨l, [.field j jty]⟩ = false →
          valueContainsMovedUninit w = false →
          evalOperands locals [.move ⟨l, [.field idx fty]⟩, .copy ⟨l, [.field j jty]⟩]
            borrows globals layouts callerLocals localDecls callStack true =
              .ok [v, w] locals') ∧
    (moveValueIsZeroSized localDecls layouts
        (placeTyResolved localDecls layouts ⟨l, [.field idx fty]⟩) v = true →
      evalOperand locals (.move ⟨l, [.field idx fty]⟩) borrows globals layouts callerLocals
        localDecls callStack true = .ok v locals ∧
      evalOperands locals [.move ⟨l, [.field idx fty]⟩, .copy ⟨l, [.field idx fty]⟩]
        borrows globals layouts callerLocals localDecls callStack true = .ok [v, v] locals ∧
      (valueListContainsMovedUninit fields = false →
        evalOperands locals [.move ⟨l, [.field idx fty]⟩, .copy ⟨l, []⟩]
          borrows globals layouts callerLocals localDecls callStack true =
            .ok [v, .aggregate variant fields] locals))) ∧
  -- (c16) non-vacuity of both polarities of (c15) on `_1 : ((), u8)`
  (∃ (locals : List LocalSlot) (l : Local) (fty0 fty1 : Ty) (v0 v1 root : Value)
      (layouts : LayoutTable) (localDecls : List LocalDecl),
    v0 ≠ .unit ∧
    Trusted.Sequence.get? locals l = some (.init root) ∧
    placeTouchesUnion localDecls layouts ⟨l, [.field 0 fty0]⟩ = false ∧
    placeTouchesUnion localDecls layouts ⟨l, [.field 1 fty1]⟩ = false ∧
    moveValueIsZeroSized localDecls layouts
      (placeTyResolved localDecls layouts ⟨l, [.field 0 fty0]⟩) v0 = true ∧
    moveValueIsZeroSized [] layouts
      (placeTyResolved [] layouts ⟨l, [.field 0 fty0]⟩) v0 = false ∧
    moveValueIsZeroSized localDecls layouts
      (placeTyResolved localDecls layouts ⟨l, [.field 1 fty1]⟩) v1 = false ∧
    evalOperands locals [.move ⟨l, [.field 0 fty0]⟩, .copy ⟨l, []⟩] [] [] layouts [] localDecls
      [] true = .ok [v0, root] locals ∧
    evalOperands locals [.move ⟨l, [.field 0 fty0]⟩, .copy ⟨l, []⟩] [] [] layouts [] []
      [] true = .ub ∧
    evalOperands locals [.move ⟨l, [.field 1 fty1]⟩, .copy ⟨l, []⟩] [] [] layouts [] localDecls
      [] true = .ub)

end Trusted.Correspondence
