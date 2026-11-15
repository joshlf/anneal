-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Anneal.PureLift.MirLiftCoreInterop

/-!
# `PureLift` ↔ Trusted `V2026_06_01` Operational Bridge (`V2026_06_01Bridge`)

Connects the MIR-agnostic `PureLift` adapter interfaces (`SpatialModel`,
`OperationalAdapter`, `SpatialCodec`) to the trusted
`Trusted.Rustc.V2026_06_01.MirSemantics` machine (`MachineState`: stack-frame
`LocalSlot`s plus a `Memory` carrying the Tree Borrows table), with no shadow
machine state:

1. **Symbolic-to-concrete refinement (`StdValRefines`).** `PureLift` evaluates
   symbolically over its canonical lawful value algebra `stdValAlg` (`StdVal`),
   whose oracle-carrying symbolic booleans `symBool b` produce `.choice` values
   and `BackTarget.choice` diamond loans. Trusted `Value`s have no symbolic
   constructor (so a `ValAlgebra Value` would short-circuit every
   `branchExplicitJoin` and never build a `.choice`); instead `StdValRefines
   tagOf v mv` relates a symbolic value to the trusted runtime value of the
   run selected by its oracles (a `choice (symBool b) vt vf` is refined by the
   taken arm), with naturals refined by fixed-width scalars and borrow handles
   by pointers whose provenance tag is `tagOf lid`.
2. **Lawful field lenses over trusted aggregates (`valuePathLens`).**
   `valueFieldLens f` reads field `f` of a `Value.aggregate` and writes it with
   `MirLiftCore.setSpineChecked?` (equal to the trusted `Sequence.set?`);
   `valuePathLens_lawful` gives the three lens laws for every field path and
   `valuePathLens_put_get_sibling` frames disjoint sibling sub-places.
3. **`mirSpatialModel`.** `ownSubPlace ms l path owner perm v` holds when the
   live MIR place `_l.path` (`placeValue?`) refines `v` and the Tree Borrows
   table of `ms.memory` grants the access that `perm` describes (`BorrowAt`: a
   live entry for tag `tagOf lid` rooted at exactly `_l.path` with a
   mutation-granting `unique`/`reserved` state for unique loans and `frozen`
   for shared ones).
4. **`mirOperationalAdapter` and `mir_pure_lift_sound`.** `ExecutesTo` is exact
   `k`-step reachability of the live step function `PureMirExec.mirStep body`
   (`stepOperationalAdapter`), `StateRel` is `spatialBindingsHold
   mirSpatialModel` plus the local-slot refinement `mirLocalsRel`, and
   `FinalLoansRel` (`MirReturnRel`) is a live normal `return` whose value
   refines the PureLift return value. `mir_pure_lift_sound` instantiates
   `pure_lift_sound` and concludes fuel-free `MirFuelFree.MirWpConverges`;
   `mir_pure_lift_sound_of_evalFuel` discharges the simulation obligation from
   one bounded live run.
5. **Byte-window `SpatialCodec`s (`MirTypedByteCodec`).** A fixed-width
   `SepLogicLenses.ByteLensCodec α n` that agrees with the trusted operational
   byte codec `encodeValueToBytes` / `decodeValueFromBytes` at MIR type `ty`
   lifts to a `SpatialCodec StdVal` (`MirTypedByteCodec.spatialCodec`, built on
   `spatialCodecOfByteLensCodec`). Freezing writes exactly the place's trusted
   byte window (`placeByteWindow?`, `spatialCodec_freeze_eq_placeByteWindow`,
   `TypedAt`), unpinning decodes a window iff the trusted decoder does
   (`spatialCodec_unpin_iff_mir_decode`), and the `Anneal.BitValidity` zerocopy
   marker traits `IsTryFromBytes` / `IsIntoBytes` / `IsFromBytes` are derived
   for the codec's type (`MirTypedByteCodec.isTryFromBytes`, `.isIntoBytes`,
   `.isFromBytes`, `.not_isFromBytes`). Instances: `u32MirCodec` (exact-width
   little-endian `u32`) and `boolMirCodec` (Rust `bool`, rejecting `0x02`);
   `FixedByteCodecBridge.mirTypedByteCodecOfMirValueCodec` lifts every
   provenance-free `ByteCodec.MirValueCodec` (a `FixedByteCodec` agreeing with
   the trusted codec) to a `MirTypedByteCodec`.
6. **State-level pin lifecycle over live MIR.** `spatialPinnedBlockHolds`
   relates a pinned loan (with its exact codec) and its writable block to the
   live byte window and live mutation-granting tag of the pinned place.
   `freeze_spatialPinnedBlockHolds`: a successful `freezeToSpatialInState` of a
   loan embedding `x`, while the live place holds `toValue x`, establishes it
   (the new block is the place's trusted byte window).
   `unpin_eq_live_mir_decode`: from the relation at a `zerocopy::IntoBytes`
   type, a successful `unpinFromSpatialInState` restores the loan to the value
   the trusted decoder reads from the live window, and
   `unpin_restores_mirStateRel` re-establishes `mirStateRel`;
   `mutate_spatialPinnedBlockHolds` carries the relation across a spatial
   mutation and the matching live store. Supporting inversions:
   `freezeToSpatialInState_ok_inv`, `mutateSpatialInState_ok_inv`,
   `reabsorbFromSpatialInState_ok_inv`, `findSpatialBlock_append_fresh`,
   `findSpatialBlock_mutateSpatialBlockAt`, `findLoan_updateLoan_self`.
7. **Frame rules (unpinned-sibling isolation).** `spatialBindingsHold_transfer`:
   loan bindings survive any symbolic step that leaves their loans untouched and
   any live step that leaves their places' values (`placeValue?`, finer than the
   whole local slot, so sibling-field stores qualify) and the Tree Borrows table
   unchanged. Instances: `freeze_preserves_bindings`,
   `mutate_preserves_bindings`, `unpin_preserves_bindings`, and
   `unpin_restores_mirStateRel_frame`, which restores the full relation for the
   unpinned loan together with every disjoint sibling binding.

End-to-end regressions over concrete `CapturedMir` bodies live in
`tests/mir/PureLiftV2026BridgeTests.lean`.
-/

namespace Anneal.PureLift.V2026_06_01Bridge

open Anneal.PureLift
open Anneal.PureLift.MirLiftCoreInterop
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. Symbolic-to-Concrete Value Refinement (`StdValRefines`) -/

/-- `StdValRefines tagOf v mv`: the trusted runtime value `mv` concretizes the
symbolic `PureLift` value `v`. Naturals are refined by any fixed-width scalar
that holds them, booleans by Rust's `0`/`1` byte scalars, pairs by two-field
tuples, symbolic booleans `symBool b` by their oracle `b`, branch joins
`choice (symBool b) vt vf` by the arm that `b` selects, and borrow handles
`refVal lid path` by pointers carrying provenance tag `tagOf lid`. -/
inductive StdValRefines (tagOf : LoanId → Nat) : StdVal → Value → Prop where
  | unit : StdValRefines tagOf .unit .unit
  | unitAgg : StdValRefines tagOf .unit (.aggregate 0 [])
  | nat {n sz : Nat} (h : n < 256 ^ sz) :
      StdValRefines tagOf (.nat n) (.scalar ⟨n, sz⟩)
  | bool (b : Bool) :
      StdValRefines tagOf (.bool b) (.scalar ⟨if b then 1 else 0, 1⟩)
  | symBool (b : Bool) :
      StdValRefines tagOf (.symBool b) (.scalar ⟨if b then 1 else 0, 1⟩)
  | pair {a b : StdVal} {ma mb : Value} :
      StdValRefines tagOf a ma → StdValRefines tagOf b mb →
      StdValRefines tagOf (.pair a b) (.aggregate 0 [ma, mb])
  | choiceTrue {vt vf : StdVal} {mv : Value} :
      StdValRefines tagOf vt mv →
      StdValRefines tagOf (.choice (.symBool true) vt vf) mv
  | choiceFalse {vt vf : StdVal} {mv : Value} :
      StdValRefines tagOf vf mv →
      StdValRefines tagOf (.choice (.symBool false) vt vf) mv
  | ref {lid : LoanId} {path : SubPath} {p : ProvenancePtr} {sz : Nat} :
      path = [] → p.allocId = tagOf lid → p.offsetBytes = 0 →
      StdValRefines tagOf (.refVal lid path) (.ptr p sz)

/-- Extract `(lid, path)` from a `StdVal.refVal lid path`. -/
def stdRefVal? (v : StdVal) : Option (LoanId × SubPath) :=
  match v with
  | ⟨_, .refVal lid path⟩ => some (lid, path)
  | _ => none

/-- Inversion for `StdValRefines` on a borrow handle: `path = []`, and `mv` is a
pointer with provenance tag `tagOf lid` and zero byte offset. -/
theorem StdValRefines.ref_inv {tagOf : LoanId → Nat} {v : StdVal} {mv : Value}
    (h : StdValRefines tagOf v mv) {lid : LoanId} {path : SubPath}
    (hr : stdRefVal? v = some (lid, path)) :
    path = [] ∧ Exists fun p => Exists fun sz =>
      mv = .ptr p sz ∧ p.allocId = tagOf lid ∧ p.offsetBytes = 0 := by
  cases h with
  | ref hp ha ho =>
    injection hr with hr
    injection hr with hlid hpath
    subst hlid
    subst hpath
    exact ⟨hp, _, _, rfl, ha, ho⟩
  | _ => exact nomatch hr

/-- `tagOf` maps distinct `LoanId`s to distinct provenance tags. -/
def TagOfInjective (tagOf : LoanId → Nat) : Prop :=
  ∀ l1 l2 : LoanId, tagOf l1 = tagOf l2 → l1 = l2

/-- Under an injective provenance-tag mapping, distinct loan handles never
refine the same runtime pointer, and every refined handle has empty sub-path
offset (`path = []`). -/
theorem StdValRefines.ref_disjoint_of_injective {tagOf : LoanId → Nat}
    (hInj : TagOfInjective tagOf) {l1 l2 : LoanId} {p1 p2 : SubPath} {mv : Value}
    (h1 : StdValRefines tagOf (.refVal l1 p1) mv)
    (h2 : StdValRefines tagOf (.refVal l2 p2) mv) :
    l1 = l2 ∧ p1 = p2 := by
  obtain ⟨hp1, ptr1, sz1, hmv1, ha1, _⟩ := h1.ref_inv (lid := l1) (path := p1) rfl
  obtain ⟨hp2, ptr2, sz2, hmv2, ha2, _⟩ := h2.ref_inv (lid := l2) (path := p2) rfl
  rw [hmv1] at hmv2
  injection hmv2 with hPtr _
  subst hPtr
  exact ⟨hInj l1 l2 (ha1.symm.trans ha2), hp1.trans hp2.symm⟩

/-- A symbolic branch join under oracle `b` is refined by every refinement of
its selected arm (`zipStdVal` builds a `.choice` on symbolic conditions). -/
theorem StdValRefines.zip_symBool {tagOf : LoanId → Nat} {b : Bool}
    {vt vf : StdVal} {mv : Value}
    (h : StdValRefines tagOf (if b then vt else vf) mv) :
    StdValRefines tagOf (zipStdVal (.symBool b) vt vf) mv := by
  cases b with
  | true => exact .choiceTrue h
  | false => exact .choiceFalse h

/-- A natural is refined only by a scalar holding exactly that natural. -/
theorem StdValRefines.nat_inv {tagOf : LoanId → Nat} {v : StdVal} {mv : Value}
    (h : StdValRefines tagOf v mv) {n : Nat} (hn : stdNatVal? v = some n) :
    Exists fun sz => mv = .scalar ⟨n, sz⟩ ∧ n < 256 ^ sz := by
  cases h with
  | nat hlt =>
    injection hn with hn
    subst hn
    exact ⟨_, rfl, hlt⟩
  | _ => exact nomatch hn

/-! ## 2. Lawful Field Lenses over Trusted Aggregates (`valuePathLens`) -/

section SpineLemmas

open Anneal.MirLiftCore (setSpineChecked?)

variable {α : Type}

theorem setSpineChecked?_getElem?_self :
    ∀ (xs : List α) (i : Nat) (a : α) (ys : List α),
      setSpineChecked? xs i a = some ys → ys[i]? = some a
  | [], _, _, _, h => nomatch h
  | _ :: _, 0, _, _, h => by
    injection h with h
    subst h
    rfl
  | x :: xs, i + 1, a, ys, h => by
    unfold setSpineChecked? at h
    cases hRest : setSpineChecked? xs i a with
    | none => rw [hRest] at h; exact nomatch h
    | some zs =>
      rw [hRest] at h
      injection h with h
      subst h
      exact setSpineChecked?_getElem?_self xs i a zs hRest

theorem setSpineChecked?_getElem?_ne :
    ∀ (xs : List α) (i : Nat) (a : α) (ys : List α) (j : Nat),
      setSpineChecked? xs i a = some ys → j ≠ i → ys[j]? = xs[j]?
  | [], _, _, _, _, h, _ => nomatch h
  | _ :: _, 0, _, _, 0, _, hNe => absurd rfl hNe
  | _ :: _, 0, _, _, _ + 1, h, _ => by
    injection h with h
    subst h
    rfl
  | x :: xs, i + 1, a, ys, j, h, hNe => by
    unfold setSpineChecked? at h
    cases hRest : setSpineChecked? xs i a with
    | none => rw [hRest] at h; exact nomatch h
    | some zs =>
      rw [hRest] at h
      injection h with h
      subst h
      cases j with
      | zero => rfl
      | succ j =>
        exact setSpineChecked?_getElem?_ne xs i a zs j hRest
          (fun hEq => hNe (congrArg (· + 1) hEq))

theorem setSpineChecked?_of_getElem? :
    ∀ (xs : List α) (i : Nat) (a : α),
      xs[i]? = some a → setSpineChecked? xs i a = some xs
  | [], _, _, h => nomatch h
  | x :: xs, 0, a, h => by
    injection h with h
    subst h
    rfl
  | x :: xs, i + 1, a, h => by
    unfold setSpineChecked?
    rw [setSpineChecked?_of_getElem? xs i a h]

theorem setSpineChecked?_twice :
    ∀ (xs : List α) (i : Nat) (a₁ a₂ : α) (ys : List α),
      setSpineChecked? xs i a₁ = some ys →
      setSpineChecked? ys i a₂ = setSpineChecked? xs i a₂
  | [], _, _, _, _, h => nomatch h
  | _ :: _, 0, _, _, _, h => by
    injection h with h
    subst h
    rfl
  | x :: xs, i + 1, a₁, a₂, ys, h => by
    unfold setSpineChecked? at h
    cases hRest : setSpineChecked? xs i a₁ with
    | none => rw [hRest] at h; exact nomatch h
    | some zs =>
      rw [hRest] at h
      injection h with h
      subst h
      unfold setSpineChecked?
      rw [setSpineChecked?_twice xs i a₁ a₂ zs hRest]

end SpineLemmas

/-- Field `f` of a trusted aggregate `Value`. -/
def valueField? (f : Nat) : Value → Option Value
  | .aggregate _ fs => fs[f]?
  | _ => none

/-- Replace field `f` of a trusted aggregate `Value` by `a` through
`MirLiftCore.setSpineChecked?` (equal to the trusted `Sequence.set?`), keeping
the variant index. -/
def valueSetField? (f : Nat) (v a : Value) : Option Value :=
  match v with
  | .aggregate var fs =>
    match Anneal.MirLiftCore.setSpineChecked? fs f a with
    | some fs' => some (.aggregate var fs')
    | none => none
  | _ => none

/-- Single-field lens over trusted aggregate values. -/
def valueFieldLens (f : Nat) : Lens Value Value where
  get := valueField? f
  put := valueSetField? f

theorem valueFieldLens_lawful (f : Nat) :
    LawfulLens Value Value (valueFieldLens f) where
  get_put := by
    intro s a h
    cases s with
    | aggregate var fs =>
      change fs[f]? = some a at h
      change valueSetField? f (.aggregate var fs) a = some (.aggregate var fs)
      dsimp only [valueSetField?]
      rw [setSpineChecked?_of_getElem? fs f a h]
    | _ => exact nomatch h
  put_get := by
    intro s a s' h
    cases s with
    | aggregate var fs =>
      change valueSetField? f (.aggregate var fs) a = some s' at h
      dsimp only [valueSetField?] at h
      cases hSet : Anneal.MirLiftCore.setSpineChecked? fs f a with
      | none => rw [hSet] at h; exact nomatch h
      | some fs' =>
        rw [hSet] at h
        injection h with h
        subst h
        exact setSpineChecked?_getElem?_self fs f a fs' hSet
    | _ => exact nomatch h
  put_put := by
    intro s a₁ a₂ s₁ h
    cases s with
    | aggregate var fs =>
      change valueSetField? f (.aggregate var fs) a₁ = some s₁ at h
      change valueSetField? f s₁ a₂ = valueSetField? f (.aggregate var fs) a₂
      dsimp only [valueSetField?] at h
      cases hSet : Anneal.MirLiftCore.setSpineChecked? fs f a₁ with
      | none => rw [hSet] at h; exact nomatch h
      | some fs' =>
        rw [hSet] at h
        injection h with h
        subst h
        dsimp only [valueSetField?]
        rw [setSpineChecked?_twice fs f a₁ a₂ fs' hSet]
    | _ => exact nomatch h

/-- Writing field `f` leaves every other field `g ≠ f` unchanged. -/
theorem valueField?_valueSetField?_ne {f g : Nat} {s a s' : Value}
    (hNe : g ≠ f) (h : valueSetField? f s a = some s') :
    valueField? g s' = valueField? g s := by
  cases s with
  | aggregate var fs =>
    dsimp only [valueSetField?] at h
    cases hSet : Anneal.MirLiftCore.setSpineChecked? fs f a with
    | none => rw [hSet] at h; exact nomatch h
    | some fs' =>
      rw [hSet] at h
      injection h with h
      subst h
      exact setSpineChecked?_getElem?_ne fs f a fs' g hSet hNe
  | _ => exact nomatch h

/-- Field-path lens over trusted aggregate values (`PureLift` `SubPath`
projections of MIR places). -/
def valuePathLens : SubPath → Lens Value Value
  | [] => Lens.id Value
  | f :: ps => Lens.comp (valueFieldLens f) (valuePathLens ps)

/-- Every field-path lens over trusted values satisfies `get_put`, `put_get`,
and `put_put`. -/
theorem valuePathLens_lawful : ∀ path : SubPath,
    LawfulLens Value Value (valuePathLens path)
  | [] => Lens.id_lawful Value
  | f :: ps =>
    Lens.comp_lawful (valueFieldLens f) (valuePathLens ps)
      (valueFieldLens_lawful f) (valuePathLens_lawful ps)

/-- **Sibling sub-place framing**: updating the sub-place at `f :: p` leaves
the sub-place at every sibling path `g :: q` (`g ≠ f`) unchanged. -/
theorem valuePathLens_put_get_sibling {f g : Nat} (p q : SubPath)
    {s a s' : Value} (hNe : g ≠ f)
    (h : (valuePathLens (f :: p)).put s a = some s') :
    (valuePathLens (g :: q)).get s' = (valuePathLens (g :: q)).get s := by
  simp only [valuePathLens, Lens.comp, valueFieldLens] at h ⊢
  cases hF : valueField? f s with
  | none => simp only [hF] at h; exact nomatch h
  | some c =>
    simp only [hF] at h
    cases hP : (valuePathLens p).put c a with
    | none => simp only [hP] at h; exact nomatch h
    | some c' =>
      simp only [hP] at h
      rw [valueField?_valueSetField?_ne hNe h]

/-! ## 3. Live MIR Places and Tree Borrows Entries -/

/-- Field path of a MIR place projection consisting only of `.field`
elements. -/
def fieldPathOfProjection? : List ProjectionElem → Option SubPath
  | [] => some []
  | .field f _ :: rest =>
    match fieldPathOfProjection? rest with
    | some p => some (f :: p)
    | none => none
  | _ :: _ => none

/-- First Tree Borrows entry for provenance tag `tag`. -/
def findBorrowEntry? (tag : Nat) : List BorrowEntry → Option BorrowEntry
  | [] => none
  | e :: es => if Nat.beq e.tag tag then some e else findBorrowEntry? tag es

/-- `findBorrowEntry?` agrees identically with the trusted Tree Borrows table
lookup `lookupBorrow`. -/
theorem findBorrowEntry?_eq_lookupBorrow (tag : Nat) :
    ∀ (es : List BorrowEntry), findBorrowEntry? tag es = lookupBorrow es tag
  | [] => rfl
  | e :: es => by
    unfold findBorrowEntry? lookupBorrow
    cases Nat.beq e.tag tag with
    | true => rfl
    | false => exact findBorrowEntry?_eq_lookupBorrow tag es

/-- Tree Borrows states whose child writes are never undefined behavior:
`Unique`, unconflicted `ReservedFrz`, and `ReservedIM`. A conflicted
`ReservedFrz` is excluded (conservatively) because a child write through it is
undefined behavior while it is protected. -/
def mutGranting : TreeBorrowPerm → Bool
  | .unique => true
  | .reservedFrz conflicted => !conflicted
  | .reservedIM => true
  | _ => false

/-- The read-only Tree Borrows state of a shared reference (`Frozen`). -/
def frozenPerm : TreeBorrowPerm → Bool
  | .frozen => true
  | _ => false

/-- `BorrowAt ms tag l path ok`: the Tree Borrows table of `ms` has a live
entry for provenance tag `tag` rooted at exactly the MIR place `_l.path`
whose permission satisfies `ok`. -/
def BorrowAt (ms : MachineState) (tag : Nat) (l : Local) (path : SubPath)
    (ok : TreeBorrowPerm → Bool) : Prop :=
  Exists fun e =>
    findBorrowEntry? tag ms.memory.borrows = some e ∧
    e.targetLocal = l ∧
    fieldPathOfProjection? e.targetProjection = some path ∧
    ok e.perm = true

/-- Look up a MIR local slot in the active stack frame, falling back to
`ms.memory.callerLocals` for caller-owned places (`l ≥ ms.frame.locals.length`),
matching the trusted `readPlaceByProjection` / `writePlaceByProjection`
resolution in `Trusted.Rustc.V2026_06_01.MirSemantics`. -/
def lookupLocalSlot? (ms : MachineState) (l : Local) : Option LocalSlot :=
  match ms.frame.locals[l]? with
  | some slot => some slot
  | none => ms.memory.callerLocals[l]?

/-- Value of the live MIR place `_l.path` in the active stack frame or
`ms.memory.callerLocals`. -/
def placeValue? (ms : MachineState) (l : Local) (path : SubPath) : Option Value :=
  match lookupLocalSlot? ms l with
  | some (.init v) => (valuePathLens path).get v
  | _ => none

/-! ## 4. `SpatialModel` over the Live MIR Machine (`mirSpatialModel`) -/

/-- `PureLift` sub-place ownership realized on the trusted MIR machine: the
place `_l.path` holds a value refining `v`, and the Tree Borrows table grants
the access described by `perm` (normalized with `getPathPerm []`, as in
`m3SpatialModel`): a unique loan needs a live mutation-granting entry for its
tag at exactly that place, a shared loan a live `frozen` one, and a place no
loan names (`.unborrowed`, or `.split` when child borrows cover only strict
sub-places) needs a live mutation-granting entry for the owning loan. -/
def mirSpatialModel (tagOf : LoanId → Nat) :
    SpatialModel StdVal MachineState Local where
  ownSubPlace ms l path owner perm v :=
    (Exists fun mv => placeValue? ms l path = some mv ∧ StdValRefines tagOf v mv) ∧
    match getPathPerm [] perm with
    | .unborrowed => BorrowAt ms (tagOf owner) l path mutGranting
    | .mutLocked lid => BorrowAt ms (tagOf lid) l path mutGranting
    | .mutJoined mLids sLids =>
      (Exists fun lid => elemLoanId lid mLids = true ∧
        BorrowAt ms (tagOf lid) l path mutGranting) ∨
      (Exists fun lid => elemLoanId lid sLids = true ∧
        BorrowAt ms (tagOf lid) l path frozenPerm)
    | .shared lids =>
      ∀ lid, elemLoanId lid lids = true → BorrowAt ms (tagOf lid) l path frozenPerm
    | .split _ => BorrowAt ms (tagOf owner) l path mutGranting
  frameHolds frame ms := frame ms
  disjointSubPlaces l1 p1 l2 p2 := l1 ≠ l2 ∨ subPathDisjoint p1 p2 = true

/-- `subPathDisjoint` is symmetric. -/
theorem subPathDisjoint_comm : ∀ (p q : SubPath),
    subPathDisjoint p q = subPathDisjoint q p
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    show (if x == y then subPathDisjoint xs ys else true) =
      (if y == x then subPathDisjoint ys xs else true)
    by_cases hxy : x = y
    · subst hxy
      rw [subPathDisjoint_comm xs ys]
    · have h1 : (x == y) = false := by simp [hxy]
      have h2 : (y == x) = false := by simp [Ne.symm hxy]
      rw [h1, h2]
      rfl

/-- Sub-place disjointness in `mirSpatialModel` is symmetric. -/
theorem mirSpatialModel_disjoint_symm (tagOf : LoanId → Nat) {l1 l2 : Local}
    {p1 p2 : SubPath}
    (h : (mirSpatialModel tagOf).disjointSubPlaces l1 p1 l2 p2) :
    (mirSpatialModel tagOf).disjointSubPlaces l2 p2 l1 p1 := by
  rcases h with h | h
  · exact Or.inl (Ne.symm h)
  · exact Or.inr ((subPathDisjoint_comm p2 p1).trans h)

/-- Sibling field places of one local are disjoint. -/
theorem mirSpatialModel_disjoint_siblings (tagOf : LoanId → Nat) (l : Local)
    {f g : Nat} (hNe : f ≠ g) (p q : SubPath) :
    (mirSpatialModel tagOf).disjointSubPlaces l (f :: p) l (g :: q) := by
  refine Or.inr ?_
  show (if f == g then subPathDisjoint p q else true) = true
  have h : (f == g) = false := by simp [hNe]
  rw [h]
  rfl

/-- `ownSubPlace` depends only on the place's resolved local slot and the Tree
Borrows table: any machine step that preserves both preserves the ownership
claim. -/
theorem mirSpatialModel_ownSubPlace_congr (tagOf : LoanId → Nat)
    {ms ms' : MachineState} {l : Local} {path : SubPath} {owner : LoanId}
    {perm : PermTree} {v : StdVal}
    (hSlot : lookupLocalSlot? ms' l = lookupLocalSlot? ms l)
    (hBorrows : ms'.memory.borrows = ms.memory.borrows)
    (h : (mirSpatialModel tagOf).ownSubPlace ms l path owner perm v) :
    (mirSpatialModel tagOf).ownSubPlace ms' l path owner perm v := by
  have hPlace : placeValue? ms' l path = placeValue? ms l path := by
    unfold placeValue?
    rw [hSlot]
  have hAt : ∀ tag ok, BorrowAt ms' tag l path ok = BorrowAt ms tag l path ok := by
    intro tag ok
    unfold BorrowAt
    rw [hBorrows]
  simp only [mirSpatialModel] at h ⊢
  simp only [hPlace, hAt]
  exact h

/-! ## 5. `OperationalAdapter` over Live MIR and the Adequacy Theorem -/

/-- Post-return caller machine state with the callee frame popped (`locals := []`)
and final memory `mem`, so `lookupLocalSlot?` resolves caller-owned `&mut` root
places in `mem.callerLocals`. -/
def callerExitState (mem : Memory) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [] }, memory := mem }

/-- `PureLift` output `out` is realized by the next live step of `body` from
`ms`: a normal root `return` whose value refines `out.ret` and whose final
memory realizes `out.mutFinals` against `rootAddrs` via
`spatialFinalBindingsHold` (checking `out.mutFinals = []` when `rootAddrs = []`,
and checking each root `&mut` parameter's final value and live mutation-granting
Tree Borrows entry in `mem.callerLocals` otherwise). -/
def MirReturnRel (tagOf : LoanId → Nat) (body : CapturedMir)
    (out : FuncOut StdVal) (ms : MachineState)
    (rootAddrs : List (LoanId × Local × SubPath) := []) : Prop :=
  Exists fun mv => Exists fun mem =>
    PureMirExec.mirStep body ms = .done (.normal (mv, mem)) ∧
    StdValRefines tagOf out.ret mv ∧
    spatialFinalBindingsHold (mirSpatialModel tagOf) rootAddrs out (callerExitState mem)

/-- Every unborrowed `PureLift` local `i` is refined by the live MIR local
`_(i+1)` (MIR local `_0` is the return place). -/
def mirLocalsRel (tagOf : LoanId → Nat) (st : SymState StdVal)
    (ms : MachineState) : Prop :=
  ∀ (i : Nat) (c : PlaceCell StdVal),
    st.locals[i]? = some c → getPathPerm [] c.perm = .unborrowed →
    Exists fun mv =>
      ms.frame.locals[i + 1]? = some (.init mv) ∧ StdValRefines tagOf c.val mv

/-- Machine-state relation of `mirOperationalAdapter`: `PureLift` loan
bindings are realized on the live Tree Borrows table and every unborrowed local
is refined by its MIR slot. -/
def mirStateRel (tagOf : LoanId → Nat) (bindings : List (LoanId × Local × SubPath))
    (st : SymState StdVal) (ms : MachineState) : Prop :=
  spatialBindingsHold (mirSpatialModel tagOf) bindings st ms ∧ mirLocalsRel tagOf st ms

/-- `PureLift` `OperationalAdapter` over the live trusted `V2026_06_01` MIR
machine: `ExecutesTo` is exact `k`-step reachability of `PureMirExec.mirStep
body`, and `FinalLoansRel` checks both `out.ret` and `spatialFinalBindingsHold`
for `rootAddrs`. -/
def mirOperationalAdapter (tagOf : LoanId → Nat) (body : CapturedMir)
    (bindings : List (LoanId × Local × SubPath))
    (rootAddrs : List (LoanId × Local × SubPath) := []) :
    OperationalAdapter MachineState StdVal :=
  stepOperationalAdapter (PureMirExec.mirStep body)
    (mirStateRel tagOf bindings) (fun out ms => MirReturnRel tagOf body out ms rootAddrs)

/-- Fuel-free post-condition of a lifted MIR run: a normal return whose value
refines `out.ret`, whose final memory realizes `out.mutFinals` against
`rootAddrs` via `spatialFinalBindingsHold`, and where `out` satisfies `post`. -/
def LiftedMirPost (tagOf : LoanId → Nat) (post : FuncOut StdVal → Prop)
    (o : MirOutcome)
    (rootAddrs : List (LoanId × Local × SubPath) := []) : Prop :=
  Exists fun out => Exists fun mv => Exists fun mem =>
    o = .normal (mv, mem) ∧ StdValRefines tagOf out.ret mv ∧
    spatialFinalBindingsHold (mirSpatialModel tagOf) rootAddrs out (callerExitState mem) ∧
    post out

/-- **Adequacy over live `V2026_06_01` MIR (`mir_pure_lift_sound`)**:
`pure_lift_sound` instantiated with `mirOperationalAdapter` proves that `body`
converges from `m0` (fuel-free `MirFuelFree.MirWpConverges`) to a normal return
refining `out.ret` and realizing `out.mutFinals` at `rootAddrs` for a `PureLift`
output `out` that satisfies `post`. -/
theorem mir_pure_lift_sound (tagOf : LoanId → Nat) (body : CapturedMir)
    (bindings : List (LoanId × Local × SubPath))
    (params : List (ParamInput StdVal)) (plan : FlowPlan StdVal)
    (retExpr : RvalOp StdVal) (post : FuncOut StdVal → Prop) (m0 : MachineState)
    (rootAddrs : List (LoanId × Local × SubPath) := [])
    (hInit : Exists fun st0 =>
      initFnState stdValAlg params = .ok st0 ∧ mirStateRel tagOf bindings st0 m0)
    (hSpec : HoldsFnSpec (evalFnValue stdValAlg params plan retExpr) post)
    (hSim : ∀ st0 out,
      initFnState stdValAlg params = .ok st0 → mirStateRel tagOf bindings st0 m0 →
      evalFnValue stdValAlg params plan retExpr = .ok out →
      Exists fun k => Exists fun mFinal =>
        StepPath (PureMirExec.mirStep body) m0 k mFinal ∧
        MirReturnRel tagOf body out mFinal rootAddrs) :
    Anneal.MirFuelFree.MirWpConverges body m0
      (fun o => LiftedMirPost tagOf post o rootAddrs) :=
  pure_lift_mirWpConverges (mirStateRel tagOf bindings)
    (fun out ms => MirReturnRel tagOf body out ms rootAddrs)
    stdValAlg params plan retExpr post m0 hInit hSpec hSim
    (fun o => LiftedMirPost tagOf post o rootAddrs)
    (fun _ out hRel hPost =>
      match hRel with
      | ⟨mv, mem, hDone, hRef, hFinals⟩ =>
        PureMirExec.mirWpConverges_of_wpConverges
          (PureMirExec.WpConverges.of_done hDone ⟨out, mv, mem, rfl, hRef, hFinals, hPost⟩))

/-- A bounded live run that halts yields an exact step path to the halting
state. -/
theorem exists_stepPath_of_evalFuel_halted {σ α : Type}
    {step : σ → PureMirExec.Step σ α} :
    ∀ {k : Nat} {s : σ} {v : α}, PureMirExec.evalFuel step k s = .halted v →
      Exists fun n => Exists fun t => StepPath step s n t ∧ step t = .done v
  | 0, _, _, h => nomatch h
  | k + 1, s, v, h => by
    unfold PureMirExec.evalFuel at h
    cases hs : step s with
    | cont s' =>
      rw [hs] at h
      obtain ⟨n, t, hPath, hDone⟩ := exists_stepPath_of_evalFuel_halted h
      exact ⟨n + 1, t, .cons hs hPath, hDone⟩
    | done w =>
      rw [hs] at h
      injection h with h
      subst h
      exact ⟨0, s, .refl s, hs⟩
    | fault => rw [hs] at h; exact nomatch h

/-- **`mir_pure_lift_sound` from one bounded live run**: if the `PureLift`
evaluation succeeds with output `out` satisfying `post`, the entry state is
related, and a bounded run of the live MIR machine halts normally with a value
refining `out.ret` and final memory realizing `out.mutFinals` at `rootAddrs`,
then `body` converges fuel-free to `LiftedMirPost`. -/
theorem mir_pure_lift_sound_of_evalFuel (tagOf : LoanId → Nat) (body : CapturedMir)
    (bindings : List (LoanId × Local × SubPath))
    (params : List (ParamInput StdVal)) (plan : FlowPlan StdVal)
    (retExpr : RvalOp StdVal) (post : FuncOut StdVal → Prop) (m0 : MachineState)
    (out : FuncOut StdVal) (mv : Value) (mem : Memory) (fuel : Nat)
    (rootAddrs : List (LoanId × Local × SubPath) := [])
    (hInit : Exists fun st0 =>
      initFnState stdValAlg params = .ok st0 ∧ mirStateRel tagOf bindings st0 m0)
    (hEval : evalFnValue stdValAlg params plan retExpr = .ok out)
    (hPost : post out)
    (hRun : PureMirExec.evalFuel (PureMirExec.mirStep body) fuel m0 =
      .halted (.normal (mv, mem)))
    (hRef : StdValRefines tagOf out.ret mv)
    (hFinals : spatialFinalBindingsHold (mirSpatialModel tagOf) rootAddrs out
      (callerExitState mem)) :
    Anneal.MirFuelFree.MirWpConverges body m0
      (fun o => LiftedMirPost tagOf post o rootAddrs) := by
  refine mir_pure_lift_sound tagOf body bindings params plan retExpr post m0 rootAddrs hInit
    (by rw [hEval]; exact hPost) ?_
  intro _ out' _ _ hEval'
  rw [hEval] at hEval'
  injection hEval' with hOut
  subst hOut
  obtain ⟨n, t, hPath, hDone⟩ := exists_stepPath_of_evalFuel_halted hRun
  exact ⟨n, t, hPath, mv, mem, hDone, hRef, hFinals⟩

/-- Run `k` silent steps of a deterministic machine (`none` if it halts or
faults first). -/
def runSilentSteps {σ α : Type} (step : σ → PureMirExec.Step σ α) : Nat → σ → Option σ
  | 0, s => some s
  | k + 1, s =>
    match step s with
    | .cont s' => runSilentSteps step k s'
    | _ => none

/-- A successful silent run is an exact step path. -/
theorem stepPath_of_runSilentSteps {σ α : Type} {step : σ → PureMirExec.Step σ α} :
    ∀ {k : Nat} {s t : σ}, runSilentSteps step k s = some t → StepPath step s k t
  | 0, s, t, h => by
    injection h with h
    subst h
    exact .refl s
  | k + 1, s, t, h => by
    unfold runSilentSteps at h
    cases hs : step s with
    | cont s' =>
      rw [hs] at h
      exact .cons hs (stepPath_of_runSilentSteps h)
    | done _ => rw [hs] at h; exact nomatch h
    | fault => rw [hs] at h; exact nomatch h

/-- Checkable pointwise form of `mirLocalsRel` over the `PureLift` locals and
the MIR argument/temporary slots `_1, _2, …`. -/
def LocalsRefine (tagOf : LoanId → Nat) :
    List (PlaceCell StdVal) → List LocalSlot → Prop
  | [], _ => True
  | c :: cs, slot :: slots =>
    (getPathPerm [] c.perm = .unborrowed →
      Exists fun mv => slot = .init mv ∧ StdValRefines tagOf c.val mv) ∧
    LocalsRefine tagOf cs slots
  | _ :: _, [] => False

theorem localsRefine_getElem? {tagOf : LoanId → Nat} :
    ∀ (cs : List (PlaceCell StdVal)) (slots : List LocalSlot),
      LocalsRefine tagOf cs slots →
      ∀ (i : Nat) (c : PlaceCell StdVal), cs[i]? = some c →
        getPathPerm [] c.perm = .unborrowed →
        Exists fun mv => slots[i]? = some (.init mv) ∧ StdValRefines tagOf c.val mv
  | [], _, _, _, _, hc, _ => nomatch hc
  | _ :: _, [], h, _, _, _, _ => nomatch h
  | c :: cs, s :: ss, h, 0, c', hc, hU => by
    injection hc with hc
    subst hc
    obtain ⟨mv, hs, hr⟩ := h.1 hU
    exact ⟨mv, by rw [hs]; rfl, hr⟩
  | _ :: cs, _ :: ss, h, i + 1, c', hc, hU =>
    localsRefine_getElem? cs ss h.2 i c' hc hU

/-- `LocalsRefine` against the frame's slots after the return place `_0`
establishes `mirLocalsRel`. -/
theorem mirLocalsRel_of_localsRefine {tagOf : LoanId → Nat} {st : SymState StdVal}
    {ms : MachineState} (h : LocalsRefine tagOf st.locals ms.frame.locals.tail) :
    mirLocalsRel tagOf st ms := by
  intro i c hc hU
  cases hl : ms.frame.locals with
  | nil =>
    rw [hl] at h
    cases hcs : st.locals with
    | nil => rw [hcs] at hc; exact nomatch hc
    | cons _ _ => rw [hcs] at h; exact nomatch h
  | cons s0 rest =>
    rw [hl] at h
    obtain ⟨mv, hs, hr⟩ := localsRefine_getElem? st.locals rest h i c hc hU
    exact ⟨mv, by rw [List.getElem?_cons_succ]; exact hs, hr⟩

/-- **Join-point synchronization over live MIR**: a header-targeted live run
(`PureMirExec.runMirToBlock`) that reaches the join block `target` in a state
`msJoin` realizing the post-join `PureLift` state `stJoin` is a live `StepsTo`
segment from the entry state into that realized join state. -/
theorem stepsTo_join_of_runMirToBlock {body : CapturedMir}
    {target : BasicBlockIdx} {m0 msJoin : MachineState} {tagOf : LoanId → Nat}
    {bindings : List (LoanId × Local × SubPath)} {stJoin : SymState StdVal}
    (hRun : PureMirExec.runMirToBlock body target m0 = .reached msJoin)
    (hRel : mirStateRel tagOf bindings stJoin msJoin) :
    PureMirExec.StepsTo (PureMirExec.mirStep body) m0
      (fun ms => ms = msJoin ∧ mirStateRel tagOf bindings stJoin ms ∧
        ms.frame.blockIdx = target ∧ ms.frame.stmtIdx = 0) := by
  have hAt := PureMirExec.runMirToBlock_reached_block_and_stmt hRun
  exact stepsTo_of_runMirToBlock_reached hRun ⟨rfl, hRel, hAt.1, hAt.2⟩

/-- Convergence factored through a realized join state: the live run reaches
the join block in a state realizing `stJoin`, and the live machine converges
from that join state. -/
theorem mirWpConverges_of_runMirToBlock_join {body : CapturedMir}
    {target : BasicBlockIdx} {m0 msJoin : MachineState} {tagOf : LoanId → Nat}
    {bindings : List (LoanId × Local × SubPath)} {stJoin : SymState StdVal}
    {Post : MirOutcome → Prop}
    (hRun : PureMirExec.runMirToBlock body target m0 = .reached msJoin)
    (hRel : mirStateRel tagOf bindings stJoin msJoin)
    (hCont : ∀ ms, ms = msJoin → mirStateRel tagOf bindings stJoin ms →
      Anneal.MirFuelFree.MirWpConverges body ms Post) :
    Anneal.MirFuelFree.MirWpConverges body m0 Post :=
  PureMirExec.mirWpConverges_of_stepsTo_bind (stepsTo_join_of_runMirToBlock hRun hRel)
    (fun ms hms => hCont ms hms.1 hms.2.1)

/-! ## 6. Byte-Window `SpatialCodec`s over Trusted Operational Byte Codecs -/

/-- A fixed-width byte codec `codec` on `α` that agrees with the trusted
operational byte codec of MIR type `ty` (`encodeValueToBytes` /
`decodeValueFromBytes` at `defaultCodecFuel`) through the embedding `toValue`:
the `SepLogicLenses.ByteLensCodec` counterpart of `ByteCodec.MirValueCodec`,
with provenance-free encodings so frozen windows are raw-byte spatial cells. -/
structure MirTypedByteCodec (layouts : LayoutTable) (ty : Ty) (α : Type) (n : Nat) :
    Type where
  codec : Anneal.SepLogicLenses.ByteLensCodec α n
  toValue : α → Value
  ofValue : Value → Option α
  ofValue_toValue : ∀ x : α, ofValue (toValue x) = some x
  tySize_eq : rigidTyByteSize layouts ty = some n
  encode_toValue : ∀ x : α,
    encodeValueToBytes defaultCodecFuel layouts ty (toValue x) = some (codec.encode x)
  decode_eq_map : ∀ bs : List AbstractByte,
    decodeValueFromBytes defaultCodecFuel layouts ty bs = (codec.decode bs).map toValue
  encode_provenanceFree : ∀ x : α, provenanceFree (codec.encode x) = true

namespace MirTypedByteCodec

variable {layouts : LayoutTable} {ty : Ty} {α : Type} {n : Nat}

/-- `toValue` is injective. -/
theorem toValue_injective (m : MirTypedByteCodec layouts ty α n) {x y : α}
    (h : m.toValue x = m.toValue y) : x = y := by
  have hx := m.ofValue_toValue x
  rw [h, m.ofValue_toValue y] at hx
  exact (Option.some.inj hx).symm

/-- `zerocopy::TryFromBytes`: every successful trusted decode at `ty` is the
embedding of a codec value. -/
theorem isTryFromBytes (m : MirTypedByteCodec layouts ty α n) :
    Anneal.BitValidity.IsTryFromBytes layouts ty
      (fun v => Exists fun x => m.toValue x = v ∧ m.ofValue v = some x) := by
  refine ⟨n, m.tySize_eq, ?_⟩
  intro bs v hDec
  rw [m.decode_eq_map bs] at hDec
  cases hC : m.codec.decode bs with
  | none => rw [hC] at hDec; exact nomatch hDec
  | some x =>
    rw [hC] at hDec
    injection hDec with hV
    subst hV
    exact ⟨x, rfl, m.ofValue_toValue x⟩

/-- `zerocopy::IntoBytes`: if every trusted encoding at `ty` is a codec
encoding and codec encodings are fully initialized, then `ty` is
`IsIntoBytes`. -/
theorem isIntoBytes (m : MirTypedByteCodec layouts ty α n)
    (hInit : ∀ x : α, Anneal.BitValidity.allBytesInitialized (m.codec.encode x) = true)
    (hWitness : ∀ (v : Value) (bs : List AbstractByte),
      encodeValueToBytes defaultCodecFuel layouts ty v = some bs →
      Exists fun x => bs = m.codec.encode x) :
    Anneal.BitValidity.IsIntoBytes layouts ty := by
  refine ⟨n, m.tySize_eq, ?_⟩
  intro v bs hEnc
  obtain ⟨x, hx⟩ := hWitness v bs hEnc
  subst hx
  exact ⟨m.codec.encode_len x, hInit x⟩

/-- `zerocopy::FromBytes`: a codec that decodes every initialized `n`-byte
window makes `ty` `IsFromBytes`. -/
theorem isFromBytes (m : MirTypedByteCodec layouts ty α n)
    (hSurj : ∀ bs : List AbstractByte, bs.length = n →
      Anneal.BitValidity.allBytesInitialized bs = true →
      Exists fun x => m.codec.decode bs = some x) :
    Anneal.BitValidity.IsFromBytes layouts ty := by
  refine ⟨n, m.tySize_eq, ?_⟩
  intro bs hLen hInit
  obtain ⟨x, hx⟩ := hSurj bs hLen hInit
  exact ⟨m.toValue x, by rw [m.decode_eq_map bs, hx]; rfl⟩

/-- Negative `zerocopy::FromBytes` bridge: one initialized `n`-byte window that
the codec rejects refutes `IsFromBytes`. -/
theorem not_isFromBytes (m : MirTypedByteCodec layouts ty α n)
    (bs : List AbstractByte) (hLen : bs.length = n)
    (hInit : Anneal.BitValidity.allBytesInitialized bs = true)
    (hNone : m.codec.decode bs = none) :
    ¬ Anneal.BitValidity.IsFromBytes layouts ty := by
  intro ⟨sz, hSz, hDec⟩
  rw [m.tySize_eq] at hSz
  injection hSz with hEq
  subst hEq
  obtain ⟨v, hv⟩ := hDec bs hLen hInit
  rw [m.decode_eq_map bs, hNone] at hv
  exact nomatch hv

/-- `SpatialCodec` over `PureLift` values induced by a MIR-typed byte codec and
an embedding `embed` of `α` into `StdVal` (`spatialCodecOfByteLensCodec`). -/
def spatialCodec (m : MirTypedByteCodec layouts ty α n) (cid : Nat)
    (embed : α → StdVal) (embed? : StdVal → Option α)
    (embed_embed? : ∀ (v : StdVal) (x : α), embed? v = some x → embed x = v) :
    SpatialCodec StdVal :=
  spatialCodecOfByteLensCodec cid m.codec m.encode_provenanceFree embed embed?
    embed_embed?

/-- **Freeze writes the trusted byte window**: freezing a value in the codec's
image produces exactly the raw-byte cells of the trusted operational encoding
`encodeValueToBytes` of its MIR value at `ty`. -/
theorem spatialCodec_freeze_window (m : MirTypedByteCodec layouts ty α n)
    (cid : Nat) (embed : α → StdVal) (embed? : StdVal → Option α)
    (embed_embed? : ∀ (v : StdVal) (x : α), embed? v = some x → embed x = v)
    (v : StdVal) (x : α) (hv : embed? v = some x) :
    abstractBytesOfCells ((m.spatialCodec cid embed embed? embed_embed?).encode v) =
      encodeValueToBytes defaultCodecFuel layouts ty (m.toValue x) := by
  rw [m.encode_toValue x]
  unfold spatialCodec spatialCodecOfByteLensCodec
  simp only [hv]
  obtain ⟨cs, hcs⟩ := cellsOfAbstractBytes_isSome (Val := StdVal) (m.codec.encode x)
    (m.encode_provenanceFree x)
  rw [hcs]
  exact abstractBytesOfCells_cellsOfAbstractBytes (m.codec.encode x) cs hcs

/-- Frozen windows of fully initialized codec encodings carry no `.uninit`
cell, so the `freezeToSpatialInState` initialization guard passes (the
`IntoBytes` side-condition). -/
theorem spatialCodec_freeze_initialized (m : MirTypedByteCodec layouts ty α n)
    (cid : Nat) (embed : α → StdVal) (embed? : StdVal → Option α)
    (embed_embed? : ∀ (v : StdVal) (x : α), embed? v = some x → embed x = v)
    (v : StdVal) (x : α) (hv : embed? v = some x)
    (hInit : Anneal.BitValidity.allBytesInitialized (m.codec.encode x) = true) :
    hasUninitCell ((m.spatialCodec cid embed embed? embed_embed?).encode v) = false :=
  spatialCodecOfByteLensCodec_hasUninitCell_false cid m.codec m.encode_provenanceFree
    embed embed? embed_embed? v x hv hInit

/-- **Unpin agrees with the trusted decoder**: an `n`-cell window decodes under
the spatial codec to `embed x` iff the trusted `decodeValueFromBytes` at `ty`
decodes its bytes to `toValue x`, and every successful unpin is of that form. -/
theorem spatialCodec_unpin_iff_mir_decode (m : MirTypedByteCodec layouts ty α n)
    (cid : Nat) (embed : α → StdVal) (embed? : StdVal → Option α)
    (embed_embed? : ∀ (v : StdVal) (x : α), embed? v = some x → embed x = v)
    (cells : List (CellVal StdVal)) (bs : List AbstractByte)
    (hBytes : abstractBytesOfCells cells = some bs) (hLen : cells.length = n) :
    (∀ v', (m.spatialCodec cid embed embed? embed_embed?).decode cells = some v' →
      Exists fun x => v' = embed x ∧
        decodeValueFromBytes defaultCodecFuel layouts ty bs = some (m.toValue x)) ∧
    (∀ x, decodeValueFromBytes defaultCodecFuel layouts ty bs = some (m.toValue x) →
      (m.spatialCodec cid embed embed? embed_embed?).decode cells = some (embed x)) := by
  have hBsLen : bs.length = n := (abstractBytesOfCells_length cells bs hBytes).trans hLen
  refine ⟨?_, ?_⟩
  · intro v' hDec
    obtain ⟨bs', x, hBytes', hC, hv'⟩ :=
      spatialCodecOfByteLensCodec_decode_in_subdomain cid m.codec m.encode_provenanceFree
        embed embed? embed_embed? cells v' hLen hDec
    rw [hBytes] at hBytes'
    injection hBytes' with hEq
    subst hEq
    refine ⟨x, hv', ?_⟩
    rw [m.decode_eq_map bs, hC]
    rfl
  · intro x hDec
    rw [m.decode_eq_map bs] at hDec
    have hC : m.codec.decode bs = some x := by
      cases hC : m.codec.decode bs with
      | none => rw [hC] at hDec; exact nomatch hDec
      | some y =>
        rw [hC] at hDec
        injection hDec with hEq
        exact congrArg some (m.toValue_injective hEq)
    unfold spatialCodec spatialCodecOfByteLensCodec
    simp only [decodeByteLensFallback?_of_length_eq n cells hLen, hBytes, hBsLen,
      Nat.beq_refl, hC, ↓reduceIte]

end MirTypedByteCodec

/-- Trusted byte window of the MIR place `_l.path` at static type `ty`: the
operational encoding `encodeValueToBytes` of its value, or `size` `.uninit`
bytes for a live but uninitialized local (`MaybeUninit` storage). -/
def placeByteWindow? (layouts : LayoutTable) (ty : Ty) (ms : MachineState)
    (l : Local) (path : SubPath) : Option (List AbstractByte) :=
  match lookupLocalSlot? ms l, path with
  | some (.init v), _ =>
    match (valuePathLens path).get v with
    | some sub => encodeValueToBytes defaultCodecFuel layouts ty sub
    | none => none
  | some .uninit, [] =>
    match rigidTyByteSize layouts ty with
    | some sz => some (replicateUninitBytes sz)
    | none => none
  | _, _ => none

/-- Mid-pin state relation connecting a spatially pinned loan `lid` (in phase
`LoanPhase.spatialPinned bid codec`, with exactly the codec `codec` and an
unborrowed loan cell `isUnborrowed e.cell.perm = true`) and its writable, unsplit
raw-byte `SpatialBlock` in `st.spatial` (located by `findSpatialBlock`, as
`reabsorbFromSpatialInState` does) to the live MIR byte window
`placeByteWindow? layouts ty ms l path` and live mutation-granting Tree Borrows
entry `BorrowAt ms (tagOf lid) l path mutGranting`. -/
def spatialPinnedBlockHolds (tagOf : LoanId → Nat) (layouts : LayoutTable)
    (ty : Ty) (lid : LoanId) (bid : BlockId) (codec : SpatialCodec StdVal)
    (l : Local) (path : SubPath) (st : SymState StdVal) (ms : MachineState) : Prop :=
  Exists fun e => Exists fun blk => Exists fun rest => Exists fun bs =>
    findLoan lid st.loans = some e ∧
    (match e.phase with
     | .spatialPinned b c => b = bid ∧ c = codec ∧ isUnborrowed e.cell.perm = true
     | _ => False) ∧
    findSpatialBlock st.spatial bid = some (blk, rest) ∧
    blk.originLoan = lid ∧ blk.perm = .readWrite ∧ blk.provenanceTag = bid ∧
    blk.activeSubSplits = 0 ∧
    abstractBytesOfCells blk.cells = some bs ∧
    placeByteWindow? layouts ty ms l path = some bs ∧
    BorrowAt ms (tagOf lid) l path mutGranting

/-- **Frozen block = live MIR byte window**: when the MIR place `_l.path` holds
`toValue x`, freezing any `PureLift` value that embeds `x` produces exactly
that place's trusted byte window, and the window is `TypedAt` `x` at offset
`0` under the codec. -/
theorem spatialCodec_freeze_eq_placeByteWindow
    {layouts : LayoutTable} {ty : Ty} {α : Type} {n : Nat}
    (m : MirTypedByteCodec layouts ty α n)
    (cid : Nat) (embed : α → StdVal) (embed? : StdVal → Option α)
    (embed_embed? : ∀ (v : StdVal) (x : α), embed? v = some x → embed x = v)
    (ms : MachineState) (l : Local) (path : SubPath) (v : StdVal) (x : α)
    (hv : embed? v = some x) (hPlace : placeValue? ms l path = some (m.toValue x)) :
    placeByteWindow? layouts ty ms l path = some (m.codec.encode x) ∧
    abstractBytesOfCells ((m.spatialCodec cid embed embed? embed_embed?).encode v) =
      some (m.codec.encode x) ∧
    Anneal.SepLogicLenses.TypedAt m.codec 0 x (m.codec.encode x) := by
  have hWin : placeByteWindow? layouts ty ms l path = some (m.codec.encode x) := by
    unfold placeValue? at hPlace
    unfold placeByteWindow?
    cases hSlot : lookupLocalSlot? ms l with
    | none => rw [hSlot] at hPlace; exact nomatch hPlace
    | some slot =>
      rw [hSlot] at hPlace
      cases slot with
      | init w =>
        dsimp only at hPlace ⊢
        rw [hPlace]
        exact m.encode_toValue x
      | uninit => exact nomatch hPlace
      | dead => exact nomatch hPlace
  refine ⟨hWin, ?_, ?_⟩
  · rw [m.spatialCodec_freeze_window cid embed embed? embed_embed? v x hv]
    exact m.encode_toValue x
  · have h := Anneal.SepLogicLenses.typedAt_append_encode m.codec [] [] x
    simp only [List.nil_append, List.append_nil, List.length_nil] at h
    exact h

/-! ### State-Level `freezeToSpatialInState` / `unpinFromSpatialInState` Bridges -/

section PinLifecycle

theorem findLoan_cons {Val : Type} (lid : LoanId) (e : LoanEntry Val)
    (es : List (LoanEntry Val)) :
    findLoan lid (e :: es) = if e.id == lid then some e else findLoan lid es := rfl

theorem updateLoan_cons {Val : Type} (lid : LoanId) (f : LoanEntry Val → LoanEntry Val)
    (e : LoanEntry Val) (es : List (LoanEntry Val)) :
    updateLoan lid f (e :: es) =
      if e.id == lid then f e :: updateLoan lid f es else e :: updateLoan lid f es := rfl

/-- Updating loan `lid` with an identifier-preserving `f` maps its lookup. -/
theorem findLoan_updateLoan_self {Val : Type} (lid : LoanId)
    (f : LoanEntry Val → LoanEntry Val) (hf : ∀ e, (f e).id = e.id) :
    ∀ loans : List (LoanEntry Val),
      findLoan lid (updateLoan lid f loans) = (findLoan lid loans).map f
  | [] => rfl
  | e :: es => by
    rw [updateLoan_cons, findLoan_cons]
    cases h : e.id == lid with
    | true => simp only [↓reduceIte, findLoan_cons, hf e, h, Option.map_some]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, findLoan_cons, h]
      exact findLoan_updateLoan_self lid f hf es

/-- Updating loan `lid` leaves every other loan `lid' ≠ lid` unchanged. -/
theorem findLoan_updateLoan_ne {Val : Type} {lid lid' : LoanId}
    (hNe : lid' ≠ lid) (f : LoanEntry Val → LoanEntry Val)
    (hf : ∀ e, (f e).id = e.id) :
    ∀ loans : List (LoanEntry Val),
      findLoan lid' (updateLoan lid f loans) = findLoan lid' loans
  | [] => rfl
  | e :: es => by
    rw [updateLoan_cons, findLoan_cons]
    cases h : e.id == lid with
    | true =>
      have hId : e.id = lid := eq_of_beq h
      have hFalse : (e.id == lid') = false := by
        cases h' : e.id == lid' with
        | false => rfl
        | true => exact False.elim (hNe ((eq_of_beq h').symm.trans hId))
      simp only [↓reduceIte, findLoan_cons, hf e, hFalse, Bool.false_eq_true]
      exact findLoan_updateLoan_ne hNe f hf es
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, findLoan_cons]
      cases e.id == lid' with
      | true => rfl
      | false => exact findLoan_updateLoan_ne hNe f hf es

theorem getPathPerm_nil_of_isUnborrowed {t : PermTree} (h : isUnborrowed t = true) :
    getPathPerm [] t = .unborrowed := by
  unfold isUnborrowed at h
  unfold getPathPerm
  cases ht : toEntries t with
  | nil => rfl
  | cons _ _ => rw [ht] at h; exact nomatch h

theorem countSpatialBlockId_cons {Val : Type} (bid : BlockId) (b : SpatialBlock Val)
    (bs : List (SpatialBlock Val)) :
    countSpatialBlockId bid (b :: bs) =
      if b.blockId == bid then countSpatialBlockId bid bs + 1
      else countSpatialBlockId bid bs := rfl

/-- Fold step of `findSpatialBlock`. -/
def spatialFindStep {Val : Type} (bid : BlockId) (b : SpatialBlock Val)
    (acc : Bool × Option (SpatialBlock Val) × List (SpatialBlock Val)) :
    Bool × Option (SpatialBlock Val) × List (SpatialBlock Val) :=
  match acc with
  | (dup, foundOpt, rest) =>
    if b.blockId == bid then
      match foundOpt with
      | some _ => (true, foundOpt, rest)
      | none => (dup, some b, rest)
    else
      (dup, foundOpt, b :: rest)

/-- Result extraction of `findSpatialBlock`. -/
def spatialFindFinish {Val : Type} :
    Bool × Option (SpatialBlock Val) × List (SpatialBlock Val) →
      Option (SpatialBlock Val × List (SpatialBlock Val))
  | (false, some found, updated) => some (found, updated)
  | _ => none

theorem findSpatialBlock_eq_fold {Val : Type} (blocks : List (SpatialBlock Val))
    (bid : BlockId) :
    findSpatialBlock blocks bid =
      spatialFindFinish (blocks.foldr (spatialFindStep bid) (false, none, [])) := rfl

theorem foldr_spatialFindStep_fresh {Val : Type} (bid : BlockId) (blk : SpatialBlock Val) :
    ∀ sp : List (SpatialBlock Val), countSpatialBlockId bid sp = 0 →
      sp.foldr (spatialFindStep bid) (false, some blk, []) = (false, some blk, sp)
  | [], _ => rfl
  | b :: bs, hFresh => by
    rw [countSpatialBlockId_cons] at hFresh
    cases h : b.blockId == bid with
    | true => rw [h] at hFresh; exact nomatch hFresh
    | false =>
      rw [h] at hFresh
      rw [List.foldr_cons, foldr_spatialFindStep_fresh bid blk bs hFresh]
      unfold spatialFindStep
      simp only [h, Bool.false_eq_true, ↓reduceIte]

/-- Appending a block with a fresh identifier makes `findSpatialBlock` return it
together with the untouched prefix. -/
theorem findSpatialBlock_append_fresh {Val : Type} (sp : List (SpatialBlock Val))
    (blk : SpatialBlock Val) (hFresh : countSpatialBlockId blk.blockId sp = 0) :
    findSpatialBlock (sp ++ [blk]) blk.blockId = some (blk, sp) := by
  rw [findSpatialBlock_eq_fold, List.foldr_append, List.foldr_cons, List.foldr_nil]
  have hb : (blk.blockId == blk.blockId) = true := decide_eq_true rfl
  have hStep : spatialFindStep blk.blockId blk (false, none, []) = (false, some blk, []) := by
    unfold spatialFindStep
    simp only [hb, ↓reduceIte]
  rw [hStep, foldr_spatialFindStep_fresh blk.blockId blk sp hFresh]
  rfl

/-- Structure of a successful `freezeToSpatialInState`. -/
theorem freezeToSpatialInState_ok_inv {Val : Type} {alg : ValAlgebra Val} {lid : LoanId}
    {codec : SpatialCodec Val} {st st' : SymState Val}
    (h : freezeToSpatialInState alg lid codec st = .ok st') :
    Exists fun e =>
      findLoan lid st.loans = some e ∧
      isUnborrowed e.cell.perm = true ∧
      countSpatialBlockId st.nextSpatialTag st.spatial = 0 ∧
      st'.locals = st.locals ∧
      st'.loans =
        updateLoan lid (fun x => ⟨x.id, .spatialPinned st.nextSpatialTag codec, x.cell, x.target⟩)
          st.loans ∧
      st'.spatial =
        st.spatial ++
          [⟨st.nextSpatialTag, lid, .readWrite, st.nextSpatialTag, 0, codec.encode e.cell.val⟩] := by
  obtain ⟨locals, loans, rgs, deps, sp, tag⟩ := st
  unfold freezeToSpatialInState at h
  dsimp only at h
  split at h
  · exact nomatch h
  · split at h
    · exact nomatch h
    · rename_i e hFind
      split at h
      · exact nomatch h
      · rename_i hGuard
        split at h
        · exact nomatch h
        · split at h
          · exact nomatch h
          · rename_i hNo
            injection h with h
            subst h
            refine ⟨e, hFind, ?_, ?_, rfl, rfl, rfl⟩
            · cases hUnb : isUnborrowed e.cell.perm with
              | true => rfl
              | false =>
                exact absurd (by simp [hUnb] :
                  (!e.phase.isActiveMut || !isUnborrowed e.cell.perm ||
                    !noActiveChildLoanEdgesIn alg lid loans ||
                    !noActiveChildRegionEdges lid rgs) = true) hGuard
            · cases hc : countSpatialBlockId tag sp with
              | zero => rfl
              | succ k => exact absurd (by simp [hasSpatialBlockId, hc]) hNo

/-- Fold step of `mutateSpatialBlockAt`. -/
def spatialBlockWritable {Val : Type} (b : SpatialBlock Val) : Bool :=
  match b.perm with
  | .readWrite => true
  | .readOnly => false

def spatialMutateOk {Val : Type} (tag : Nat) (newCells : List (CellVal Val))
    (b : SpatialBlock Val) : Bool :=
  b.provenanceTag == tag && spatialBlockWritable b &&
    b.activeSubSplits == 0 && newCells.length == b.cells.length

def spatialMutatedBlock {Val : Type} (newCells : List (CellVal Val))
    (b : SpatialBlock Val) : SpatialBlock Val :=
  ⟨b.blockId, b.originLoan, b.perm, b.provenanceTag, b.activeSubSplits, newCells⟩

def spatialMutateStep {Val : Type} (bid : BlockId) (tag : Nat)
    (newCells : List (CellVal Val)) (b : SpatialBlock Val)
    (acc : Bool × Bool × List (SpatialBlock Val)) :
    Bool × Bool × List (SpatialBlock Val) :=
  match acc with
  | (dup, found, rest) =>
    if b.blockId == bid then
      if found then
        (true, true, rest)
      else if spatialMutateOk tag newCells b then
        (dup, true, spatialMutatedBlock newCells b :: rest)
      else
        (true, true, rest)
    else
      (dup, found, b :: rest)

def spatialMutateFinish {Val : Type} :
    Bool × Bool × List (SpatialBlock Val) → Option (List (SpatialBlock Val))
  | (false, true, updated) => some updated
  | _ => none

theorem mutateSpatialBlockAt_eq_fold {Val : Type} (bid : BlockId) (tag : Nat)
    (newCells : List (CellVal Val)) (blocks : List (SpatialBlock Val)) :
    mutateSpatialBlockAt bid tag newCells blocks =
      spatialMutateFinish
        (blocks.foldr (spatialMutateStep bid tag newCells) (false, false, [])) := rfl

/-- Lockstep fold simulation between `mutateSpatialBlockAt` (`spatialMutateStep`)
and `findSpatialBlock` (`spatialFindStep`) across any spatial heaplet suffix. -/
theorem foldr_spatialMutateStep_sim {Val : Type} (bid : BlockId) (tag : Nat)
    (newCells : List (CellVal Val)) :
    ∀ (sp : List (SpatialBlock Val)),
      let fAcc := sp.foldr (spatialFindStep bid) (false, none, [])
      let mAcc := sp.foldr (spatialMutateStep bid tag newCells) (false, false, [])
      mAcc.1 = false →
      match mAcc.2.1 with
      | false =>
        fAcc = (false, none, sp) ∧ mAcc.2.2 = sp
      | true =>
        Exists fun blk => Exists fun rest =>
          fAcc = (false, some blk, rest) ∧
          spatialMutateOk tag newCells blk = true ∧
          mAcc.2.2.foldr (spatialFindStep bid) (false, none, []) =
            (false, some (spatialMutatedBlock newCells blk), rest)
  | [] => fun _ => ⟨rfl, rfl⟩
  | b :: bs => by
    have ih := foldr_spatialMutateStep_sim bid tag newCells bs
    dsimp only [List.foldr_cons] at ih ⊢
    generalize hfBs : bs.foldr (spatialFindStep bid) (false, none, []) = fBs at ih ⊢
    generalize hmBs : bs.foldr (spatialMutateStep bid tag newCells) (false, false, []) = mBs
      at ih ⊢
    obtain ⟨dupF, foundOpt, restF⟩ := fBs
    obtain ⟨dupM, foundM, restM⟩ := mBs
    dsimp only [spatialFindStep, spatialMutateStep] at ih ⊢
    cases hBid : b.blockId == bid with
    | true =>
      simp only [↓reduceIte]
      cases foundM with
      | true =>
        intro hNoDup
        exact nomatch hNoDup
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases hOk : spatialMutateOk tag newCells b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          intro hNoDup
          exact nomatch hNoDup
        | true =>
          simp only [↓reduceIte]
          intro hNoDup
          obtain ⟨hfEq, hmEq⟩ := ih hNoDup
          injection hfEq with h1 h2
          injection h2 with hOpt hRestF
          rw [h1, hOpt, hRestF] at hfBs
          refine ⟨b, bs, by rw [hOpt, h1, hRestF], hOk, ?_⟩
          rw [hmEq, List.foldr_cons, hfBs]
          unfold spatialFindStep spatialMutatedBlock
          simp only [hBid, ↓reduceIte]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      intro hNoDup
      have ih' := ih hNoDup
      cases foundM with
      | false =>
        obtain ⟨hfEq, hmEq⟩ := ih'
        injection hfEq with h1 h2
        injection h2 with hOpt hRestF
        exact ⟨by rw [h1, hOpt, hRestF], by rw [hmEq]⟩
      | true =>
        obtain ⟨blk, rest, hfEq, hOk, hUpd⟩ := ih'
        injection hfEq with h1 h2
        injection h2 with hOpt hRestF
        refine ⟨blk, b :: rest, by rw [h1, hOpt, hRestF], hOk, ?_⟩
        rw [List.foldr_cons, hUpd]
        unfold spatialFindStep
        simp only [hBid, Bool.false_eq_true, ↓reduceIte]

/-- A successful `mutateSpatialBlockAt bid tag newCells sp = some sp'` locates a
unique writable, unsplit block `blk` via `findSpatialBlock sp bid = some (blk, rest)`
with `blk.provenanceTag = tag` and `newCells.length = blk.cells.length`, and updates
that block in place so `findSpatialBlock sp' bid = some (spatialMutatedBlock newCells blk, rest)`. -/
theorem findSpatialBlock_mutateSpatialBlockAt {Val : Type} {bid : BlockId} {tag : Nat}
    {newCells : List (CellVal Val)} {sp sp' : List (SpatialBlock Val)}
    (hMut : mutateSpatialBlockAt bid tag newCells sp = some sp') :
    Exists fun blk => Exists fun rest =>
      findSpatialBlock sp bid = some (blk, rest) ∧
      spatialMutateOk tag newCells blk = true ∧
      findSpatialBlock sp' bid = some (spatialMutatedBlock newCells blk, rest) := by
  rw [mutateSpatialBlockAt_eq_fold] at hMut
  have hSim := foldr_spatialMutateStep_sim bid tag newCells sp
  dsimp only at hSim
  revert hMut hSim
  generalize sp.foldr (spatialMutateStep bid tag newCells) (false, false, []) = mAcc
  obtain ⟨dupM, foundM, restM⟩ := mAcc
  cases dupM with
  | true =>
    intro hMut _
    exact nomatch hMut
  | false =>
    cases foundM with
    | false =>
      intro hMut _
      exact nomatch hMut
    | true =>
      intro hMut hSim
      injection hMut with hRestEq
      subst hRestEq
      obtain ⟨blk, rest, hfAcc, hOk, hUpd⟩ := hSim rfl
      refine ⟨blk, rest, ?_, hOk, ?_⟩
      · rw [findSpatialBlock_eq_fold, hfAcc]
        rfl
      · rw [findSpatialBlock_eq_fold, hUpd]
        rfl

/-- Structure of a successful `mutateSpatialInState`. -/
theorem mutateSpatialInState_ok_inv {Val : Type} {bid : BlockId} {tag : Nat}
    {newCells : List (CellVal Val)} {st st' : SymState Val}
    (h : mutateSpatialInState bid tag newCells st = .ok st') :
    st'.locals = st.locals ∧
    st'.loans = st.loans ∧
    mutateSpatialBlockAt bid tag newCells st.spatial = some st'.spatial := by
  obtain ⟨locals, loans, rgs, deps, sp, nextTag⟩ := st
  unfold mutateSpatialInState at h
  dsimp only at h
  cases hM : mutateSpatialBlockAt bid tag newCells sp with
  | none => rw [hM] at h; exact nomatch h
  | some sp' =>
    rw [hM] at h
    injection h with h
    subst h
    exact ⟨rfl, rfl, rfl⟩

/-- Structure of a successful `reabsorbFromSpatialInState`
(`unpinFromSpatialInState`): the pinned codec decodes the located block. -/
theorem reabsorbFromSpatialInState_ok_inv {Val : Type} {alg : ValAlgebra Val} {lid : LoanId}
    {codec : SpatialCodec Val} {st st' : SymState Val}
    (h : reabsorbFromSpatialInState alg lid codec st = .ok st') :
    Exists fun e => Exists fun bid => Exists fun c => Exists fun blk =>
    Exists fun rest => Exists fun v' =>
      findLoan lid st.loans = some e ∧ e.phase = .spatialPinned bid c ∧
      findSpatialBlock st.spatial bid = some (blk, rest) ∧
      c.decode blk.cells = some v' ∧
      st'.locals = st.locals ∧
      st'.loans =
        updateLoan lid (fun x => ⟨x.id, .activeMut, ⟨v', x.cell.perm⟩, x.target⟩) st.loans := by
  obtain ⟨locals, loans, rgs, deps, sp, tag⟩ := st
  unfold reabsorbFromSpatialInState at h
  dsimp only at h
  cases hU : hasUniqueLoanId lid loans with
  | false => simp only [hU, Bool.not_false, ↓reduceIte] at h; exact nomatch h
  | true =>
    simp only [hU, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    cases hF : findLoan lid loans with
    | none => simp only [hF] at h; exact nomatch h
    | some e =>
      simp only [hF] at h
      cases hP : e.phase with
      | spatialPinned bid c =>
        simp only [hP] at h
        cases hId : (c.codecId != codec.codecId) with
        | true => simp only [hId, ↓reduceIte] at h; exact nomatch h
        | false =>
          simp only [hId, Bool.false_eq_true, ↓reduceIte] at h
          cases hB : findSpatialBlock sp bid with
          | none => simp only [hB] at h; exact nomatch h
          | some p =>
            obtain ⟨blk, rest⟩ := p
            simp only [hB] at h
            cases hW : blk.perm with
            | readOnly =>
              simp only [hW, Bool.and_false, Bool.false_and, Bool.false_eq_true,
                ↓reduceIte] at h
              exact nomatch h
            | readWrite =>
              simp only [hW] at h
              cases hD : c.decode blk.cells with
              | none => simp only [hD, ite_self] at h; exact nomatch h
              | some v' =>
                simp only [hD] at h
                refine ⟨e, bid, c, blk, rest, v', rfl, hP, hB, hD, ?_⟩
                split at h
                · split at h
                  · exact nomatch h
                  · injection h with h
                    subst h
                    exact ⟨rfl, rfl⟩
                · exact nomatch h
      | activeShared => simp only [hP] at h; exact nomatch h
      | activeMut => simp only [hP] at h; exact nomatch h
      | ended => simp only [hP] at h; exact nomatch h

theorem replicateUninitBytes_length : ∀ n : Nat, (replicateUninitBytes n).length = n
  | 0 => rfl
  | k + 1 => congrArg Nat.succ (replicateUninitBytes_length k)

/-- Every trusted byte window of a place at a `zerocopy::IntoBytes` type has the
type's byte width (both the encoding of an initialized place and the `.uninit`
window of live uninitialized storage). -/
theorem placeByteWindow?_length {layouts : LayoutTable} {ty : Ty} {n : Nat}
    (hSize : rigidTyByteSize layouts ty = some n)
    (hInto : Anneal.BitValidity.IsIntoBytes layouts ty)
    {ms : MachineState} {l : Local} {path : SubPath} {bs : List AbstractByte}
    (h : placeByteWindow? layouts ty ms l path = some bs) : bs.length = n := by
  obtain ⟨sz, hSz, hEnc⟩ := hInto
  rw [hSize] at hSz
  injection hSz with hSz
  subst hSz
  unfold placeByteWindow? at h
  split at h
  · split at h
    · exact (hEnc _ bs h).1
    · exact nomatch h
  · rw [hSize] at h
    injection h with h
    subst h
    exact replicateUninitBytes_length n
  · exact nomatch h

/-- **`freezeToSpatialInState` materializes the live byte window**: freezing a
loan whose value embeds `x` with a MIR-typed spatial codec, while the live MIR
place `_l.path` holds `toValue x` under a live mutation-granting tag for the
loan, establishes the mid-pin relation `spatialPinnedBlockHolds` against the
same machine state: the new block's bytes are exactly the place's trusted
operational byte window. -/
theorem freeze_spatialPinnedBlockHolds {layouts : LayoutTable} {ty : Ty} {α : Type}
    {n : Nat} (m : MirTypedByteCodec layouts ty α n) (cid : Nat)
    (embed : α → StdVal) (embed? : StdVal → Option α)
    (embed_embed? : ∀ (v : StdVal) (x : α), embed? v = some x → embed x = v)
    (tagOf : LoanId → Nat) (alg : ValAlgebra StdVal) (lid : LoanId)
    {st st' : SymState StdVal} {ms : MachineState} {l : Local} {path : SubPath} {x : α}
    (hFreeze :
      freezeToSpatialInState alg lid (m.spatialCodec cid embed embed? embed_embed?) st =
        .ok st')
    (hLoan : Exists fun e => findLoan lid st.loans = some e ∧ embed? e.cell.val = some x)
    (hPlace : placeValue? ms l path = some (m.toValue x))
    (hBorrow : BorrowAt ms (tagOf lid) l path mutGranting) :
    spatialPinnedBlockHolds tagOf layouts ty lid st.nextSpatialTag
      (m.spatialCodec cid embed embed? embed_embed?) l path st' ms := by
  obtain ⟨e, hFind, hUnb, hFresh, _, hLoans, hSpatial⟩ := freezeToSpatialInState_ok_inv hFreeze
  obtain ⟨e0, hFind0, hx⟩ := hLoan
  rw [hFind] at hFind0
  injection hFind0 with hEq
  subst hEq
  obtain ⟨hWin, hCells, _⟩ := spatialCodec_freeze_eq_placeByteWindow m cid embed embed?
    embed_embed? ms l path e.cell.val x hx hPlace
  refine ⟨⟨e.id, .spatialPinned st.nextSpatialTag (m.spatialCodec cid embed embed? embed_embed?),
      e.cell, e.target⟩,
    ⟨st.nextSpatialTag, lid, .readWrite, st.nextSpatialTag, 0,
      (m.spatialCodec cid embed embed? embed_embed?).encode e.cell.val⟩,
    st.spatial, m.codec.encode x, ?_, ⟨rfl, rfl, hUnb⟩, ?_, rfl, rfl, rfl, rfl, hCells, hWin,
    hBorrow⟩
  · rw [hLoans, findLoan_updateLoan_self lid
      (fun x => ⟨x.id, .spatialPinned st.nextSpatialTag
        (m.spatialCodec cid embed embed? embed_embed?), x.cell, x.target⟩)
      (fun _ => rfl), hFind]
    rfl
  · rw [hSpatial]
    exact findSpatialBlock_append_fresh st.spatial _ hFresh

/-- **`mutateSpatialInState` preserves `spatialPinnedBlockHolds` across a live
MIR store**: if `spatialPinnedBlockHolds` holds at `(st, ms)`,
`mutateSpatialInState bid tag newCells st = .ok st'`, `newCells` is a raw-byte
window `abstractBytesOfCells newCells = some bs'`, and the post-store live MIR
state `ms'` has `placeByteWindow? layouts ty ms' l path = some bs'` and a live
mutation-granting Tree Borrows entry for `lid`, then `spatialPinnedBlockHolds`
holds at `(st', ms')`. -/
theorem mutate_spatialPinnedBlockHolds {layouts : LayoutTable} {ty : Ty}
    {tagOf : LoanId → Nat} {lid : LoanId} {bid : BlockId} {tag : Nat}
    {codec : SpatialCodec StdVal} {l : Local} {path : SubPath}
    {newCells : List (CellVal StdVal)} {bs' : List AbstractByte}
    {st st' : SymState StdVal} {ms ms' : MachineState}
    (hPin : spatialPinnedBlockHolds tagOf layouts ty lid bid codec l path st ms)
    (hMut : mutateSpatialInState bid tag newCells st = .ok st')
    (hBytes' : abstractBytesOfCells newCells = some bs')
    (hWin' : placeByteWindow? layouts ty ms' l path = some bs')
    (hBorrow' : BorrowAt ms' (tagOf lid) l path mutGranting) :
    spatialPinnedBlockHolds tagOf layouts ty lid bid codec l path st' ms' := by
  obtain ⟨e, blk, rest, _, hFind, hPhase, hBlk, hOrig, hPerm, hTag, hSplits, _, _, _⟩ := hPin
  obtain ⟨_, hLoans, hMutSp⟩ := mutateSpatialInState_ok_inv hMut
  obtain ⟨blk1, rest1, hBlk1, _, hBlkUpd⟩ := findSpatialBlock_mutateSpatialBlockAt hMutSp
  rw [hBlk] at hBlk1
  injection hBlk1 with hPair
  injection hPair with hBlkEq hRestEq
  subst hBlkEq
  subst hRestEq
  refine ⟨e, spatialMutatedBlock newCells blk, rest, bs', ?_, hPhase, hBlkUpd,
    hOrig, hPerm, hTag, hSplits, hBytes', hWin', hBorrow'⟩
  rw [hLoans]
  exact hFind

/-- **Negative width-preservation law for `mutateSpatialInState` on a pinned
block**: at an `IsIntoBytes` type `ty` of byte width `n`, any spatial mutation
whose cell slice length differs from `n` is rejected (`.fail`). -/
theorem mutateSpatialInState_fail_of_length_ne {layouts : LayoutTable} {ty : Ty}
    {n : Nat} (hSize : rigidTyByteSize layouts ty = some n)
    (hInto : Anneal.BitValidity.IsIntoBytes layouts ty)
    {tagOf : LoanId → Nat} {lid : LoanId} {bid : BlockId} {tag : Nat}
    {codec : SpatialCodec StdVal} {l : Local} {path : SubPath}
    {newCells : List (CellVal StdVal)} {st : SymState StdVal} {ms : MachineState}
    (hPin : spatialPinnedBlockHolds tagOf layouts ty lid bid codec l path st ms)
    (hNe : newCells.length ≠ n) :
    mutateSpatialInState bid tag newCells st = .fail := by
  cases hMut : mutateSpatialInState bid tag newCells st with
  | fail => rfl
  | ok st' =>
    obtain ⟨_, blk, _, bs, _, _, hBlk, _, _, _, _, hBytes, hWin, _⟩ := hPin
    obtain ⟨_, _, hMutSp⟩ := mutateSpatialInState_ok_inv hMut
    obtain ⟨blk1, _, hBlk1, hOk, _⟩ := findSpatialBlock_mutateSpatialBlockAt hMutSp
    rw [hBlk] at hBlk1
    injection hBlk1 with hPair
    injection hPair with hBlkEq _
    subst hBlkEq
    have hBsLen : bs.length = n := placeByteWindow?_length hSize hInto hWin
    have hBlkLen : blk.cells.length = n :=
      (abstractBytesOfCells_length blk.cells bs hBytes).symm.trans hBsLen
    unfold spatialMutateOk at hOk
    rw [hBlkLen] at hOk
    have hLenBeq : (newCells.length == n) = false := by
      cases hB : newCells.length == n with
      | false => rfl
      | true => exact False.elim (hNe (eq_of_beq hB))
    rw [hLenBeq, Bool.and_false] at hOk
    exact nomatch hOk

/-- **`unpinFromSpatialInState` decodes exactly the live MIR window**: if the
mid-pin relation holds against `ms` for a MIR-typed spatial codec at a
`zerocopy::IntoBytes` type, then a successful unpin restores loan `lid` to an
active mutable loan whose value is `embed x`, where the trusted decoder
`decodeValueFromBytes` reads `toValue x` from the live place's byte window. -/
theorem unpin_eq_live_mir_decode {layouts : LayoutTable} {ty : Ty} {α : Type}
    {n : Nat} (m : MirTypedByteCodec layouts ty α n) (cid : Nat)
    (embed : α → StdVal) (embed? : StdVal → Option α)
    (embed_embed? : ∀ (v : StdVal) (x : α), embed? v = some x → embed x = v)
    (hInto : Anneal.BitValidity.IsIntoBytes layouts ty)
    (tagOf : LoanId → Nat) (alg : ValAlgebra StdVal) (lid : LoanId) (bid : BlockId)
    (codec' : SpatialCodec StdVal)
    {st st' : SymState StdVal} {ms : MachineState} {l : Local} {path : SubPath}
    (hPin : spatialPinnedBlockHolds tagOf layouts ty lid bid
      (m.spatialCodec cid embed embed? embed_embed?) l path st ms)
    (hUnpin : unpinFromSpatialInState alg lid codec' st = .ok st') :
    Exists fun x => Exists fun bs => Exists fun e' =>
      placeByteWindow? layouts ty ms l path = some bs ∧
      decodeValueFromBytes defaultCodecFuel layouts ty bs = some (m.toValue x) ∧
      findLoan lid st'.loans = some e' ∧ e'.phase = .activeMut ∧ e'.cell.val = embed x ∧
      isUnborrowed e'.cell.perm = true := by
  obtain ⟨e, blk, rest, bs, hFind, hPhase, hBlk, _, _, _, _, hBytes, hWin, _⟩ := hPin
  obtain ⟨e1, bid1, c, blk1, rest1, v', hFind1, hPhase1, hBlk1, hDec, _, hLoans⟩ :=
    reabsorbFromSpatialInState_ok_inv hUnpin
  rw [hFind] at hFind1
  injection hFind1 with hEq
  subst hEq
  rw [hPhase1] at hPhase
  obtain ⟨hBid, hC, hUnb⟩ := hPhase
  subst hBid
  subst hC
  rw [hBlk] at hBlk1
  injection hBlk1 with hPair
  injection hPair with hBlkEq _
  subst hBlkEq
  have hBsLen : bs.length = n := placeByteWindow?_length m.tySize_eq hInto hWin
  have hLen : blk.cells.length = n :=
    (abstractBytesOfCells_length blk.cells bs hBytes).symm.trans hBsLen
  obtain ⟨x, hv', hMir⟩ :=
    (m.spatialCodec_unpin_iff_mir_decode cid embed embed? embed_embed? blk.cells bs hBytes
      hLen).1 v' hDec
  refine ⟨x, bs, ⟨e.id, .activeMut, ⟨v', e.cell.perm⟩, e.target⟩, hWin, hMir, ?_, rfl, hv', hUnb⟩
  rw [hLoans, findLoan_updateLoan_self lid
    (fun x => ⟨x.id, .activeMut, ⟨v', x.cell.perm⟩, x.target⟩) (fun _ => rfl), hFind]
  rfl

/-- **`unpinFromSpatialInState` restores `mirStateRel`**: when the mid-pin
relation holds at `ms`, `unpinFromSpatialInState` succeeds, the live place
`_l.path` holds `m.toValue y` (refined by `embed y`), and `mirLocalsRel` holds at
`(st, ms)`, the post-unpin state `st'` satisfies `mirStateRel tagOf [(lid, l, path)] st' ms`. -/
theorem unpin_restores_mirStateRel {layouts : LayoutTable} {ty : Ty} {α : Type}
    {n : Nat} (m : MirTypedByteCodec layouts ty α n) (cid : Nat)
    (embed : α → StdVal) (embed? : StdVal → Option α)
    (embed_embed? : ∀ (v : StdVal) (x : α), embed? v = some x → embed x = v)
    (hInto : Anneal.BitValidity.IsIntoBytes layouts ty)
    (tagOf : LoanId → Nat) (alg : ValAlgebra StdVal) (lid : LoanId) (bid : BlockId)
    (codec' : SpatialCodec StdVal)
    {st st' : SymState StdVal} {ms : MachineState} {l : Local} {path : SubPath} {y : α}
    (hPin : spatialPinnedBlockHolds tagOf layouts ty lid bid
      (m.spatialCodec cid embed embed? embed_embed?) l path st ms)
    (hUnpin : unpinFromSpatialInState alg lid codec' st = .ok st')
    (hPlace : placeValue? ms l path = some (m.toValue y))
    (hRef : StdValRefines tagOf (embed y) (m.toValue y))
    (hLocals : mirLocalsRel tagOf st ms) :
    mirStateRel tagOf [(lid, l, path)] st' ms := by
  obtain ⟨x, bs, e', hWin, hMir, hFind', hPhase', hVal', hUnb'⟩ :=
    unpin_eq_live_mir_decode m cid embed embed? embed_embed? hInto tagOf alg lid bid
      codec' hPin hUnpin
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hBorrow⟩ := hPin
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hLocEq, _⟩ := reabsorbFromSpatialInState_ok_inv hUnpin
  have hWinY : placeByteWindow? layouts ty ms l path = some (m.codec.encode y) := by
    unfold placeValue? at hPlace
    unfold placeByteWindow?
    cases hSlot : lookupLocalSlot? ms l with
    | none => rw [hSlot] at hPlace; exact nomatch hPlace
    | some slot =>
      rw [hSlot] at hPlace
      cases slot with
      | init w =>
        dsimp only at hPlace ⊢
        rw [hPlace]
        exact m.encode_toValue y
      | uninit => exact nomatch hPlace
      | dead => exact nomatch hPlace
  rw [hWinY] at hWin
  injection hWin with hBsEq
  subst hBsEq
  rw [m.decode_eq_map (m.codec.encode y), m.codec.decode_encode y] at hMir
  injection hMir with hValEq
  have hxy : x = y := m.toValue_injective hValEq.symm
  subst hxy
  refine ⟨⟨⟨trivial, trivial⟩, ?_, trivial⟩, ?_⟩
  · simp only [hFind']
    refine ⟨by rw [hPhase']; rfl, ?_⟩
    have hEff : effectiveBoundLoanPerm lid e'.phase e'.cell.perm = .mutLocked lid := by
      unfold effectiveBoundLoanPerm
      rw [getPathPerm_nil_of_isUnborrowed hUnb', hPhase']
    rw [hEff, hVal']
    exact ⟨⟨m.toValue x, hPlace, hRef⟩, hBorrow⟩
  · intro i c hc hU
    rw [hLocEq] at hc
    exact hLocals i c hc hU

/-! ### Frame Rules: Other Loan Bindings Survive the Pin Lifecycle -/

/-- Fold step of `listFold`. -/
def listFoldStep {α β : Type} (cons : α → List α → β → β) (x : α)
    (acc : List α × β) : List α × β :=
  match acc with
  | (tail, ih) => (x :: tail, cons x tail ih)

theorem listFold_eq_fold {α β : Type} (nil : β) (cons : α → List α → β → β)
    (xs : List α) : listFold nil cons xs = (xs.foldr (listFoldStep cons) ([], nil)).2 := rfl

theorem foldr_listFoldStep_fst {α β : Type} (nil : β) (cons : α → List α → β → β) :
    ∀ xs : List α, (xs.foldr (listFoldStep cons) ([], nil)).1 = xs
  | [] => rfl
  | x :: xs => by
    rw [List.foldr_cons]
    have ih := foldr_listFoldStep_fst nil cons xs
    revert ih
    generalize xs.foldr (listFoldStep cons) ([], nil) = acc
    obtain ⟨t, r⟩ := acc
    intro ih
    dsimp only at ih
    subst ih
    rfl

/-- `listFold` unfolds on a cons cell, passing the actual tail. -/
theorem listFold_cons {α β : Type} (nil : β) (cons : α → List α → β → β) (x : α)
    (xs : List α) : listFold nil cons (x :: xs) = cons x xs (listFold nil cons xs) := by
  rw [listFold_eq_fold, listFold_eq_fold, List.foldr_cons]
  have hfst := foldr_listFoldStep_fst nil cons xs
  revert hfst
  generalize xs.foldr (listFoldStep cons) ([], nil) = acc
  obtain ⟨t, r⟩ := acc
  intro hfst
  dsimp only at hfst
  subst hfst
  rfl

/-- `ownSubPlace` of `mirSpatialModel` depends only on the bound place's live
value and the live Tree Borrows table (finer than
`mirSpatialModel_ownSubPlace_congr`: the rest of the local, e.g. a sibling
field, may change). -/
theorem mirSpatialModel_ownSubPlace_transfer (tagOf : LoanId → Nat)
    {ms ms' : MachineState} {l : Local} {path : SubPath} {owner : LoanId}
    {perm : PermTree} {v : StdVal}
    (hPlace : placeValue? ms' l path = placeValue? ms l path)
    (hBorrows : ms'.memory.borrows = ms.memory.borrows)
    (h : (mirSpatialModel tagOf).ownSubPlace ms l path owner perm v) :
    (mirSpatialModel tagOf).ownSubPlace ms' l path owner perm v := by
  have hAt : ∀ tag ok, BorrowAt ms' tag l path ok = BorrowAt ms tag l path ok := by
    intro tag ok
    unfold BorrowAt
    rw [hBorrows]
  simp only [mirSpatialModel] at h ⊢
  simp only [hPlace, hAt]
  exact h

/-- **Frame rule for loan bindings**: `spatialBindingsHold` survives any
symbolic step that leaves the bound loans untouched together with any live MIR
step that leaves every bound place's value and the Tree Borrows table
unchanged. -/
theorem spatialBindingsHold_transfer (tagOf : LoanId → Nat)
    {st st' : SymState StdVal} {ms ms' : MachineState}
    (hBorrows : ms'.memory.borrows = ms.memory.borrows) :
    ∀ bindings : List (LoanId × Local × SubPath),
      (∀ b, b ∈ bindings → findLoan b.1 st'.loans = findLoan b.1 st.loans) →
      (∀ b, b ∈ bindings → placeValue? ms' b.2.1 b.2.2 = placeValue? ms b.2.1 b.2.2) →
      spatialBindingsHold (mirSpatialModel tagOf) bindings st ms →
      spatialBindingsHold (mirSpatialModel tagOf) bindings st' ms'
  | [], _, _, h => h
  | (lid, l, path) :: bs, hL, hP, h => by
    obtain ⟨hDisj, hFold⟩ := h
    have hDisjTail : spatialBindingsDisjoint (mirSpatialModel tagOf) bs := by
      have h' := hDisj
      unfold spatialBindingsDisjoint at h'
      rw [listFold_cons] at h'
      exact h'.2
    rw [listFold_cons] at hFold
    obtain ⟨hHead, hTail⟩ := hFold
    have ih := spatialBindingsHold_transfer tagOf hBorrows bs
      (fun b hb => hL b (List.mem_cons_of_mem _ hb))
      (fun b hb => hP b (List.mem_cons_of_mem _ hb)) ⟨hDisjTail, hTail⟩
    refine ⟨hDisj, ?_⟩
    rw [listFold_cons]
    refine ⟨?_, ih.2⟩
    have hLid : findLoan lid st'.loans = findLoan lid st.loans :=
      hL (lid, l, path) (List.mem_cons_self ..)
    have hPl : placeValue? ms' l path = placeValue? ms l path :=
      hP (lid, l, path) (List.mem_cons_self ..)
    rw [hLid]
    cases hF : findLoan lid st.loans with
    | none => rw [hF] at hHead; exact hHead
    | some e =>
      rw [hF] at hHead
      exact ⟨hHead.1, mirSpatialModel_ownSubPlace_transfer tagOf hPl hBorrows hHead.2⟩

/-- A successful freeze of `lid` leaves every other loan untouched. -/
theorem findLoan_freeze_ne {Val : Type} {alg : ValAlgebra Val} {lid lid' : LoanId}
    {codec : SpatialCodec Val} {st st' : SymState Val}
    (h : freezeToSpatialInState alg lid codec st = .ok st') (hNe : lid' ≠ lid) :
    findLoan lid' st'.loans = findLoan lid' st.loans := by
  obtain ⟨_, _, _, _, _, hLoans, _⟩ := freezeToSpatialInState_ok_inv h
  rw [hLoans]
  exact findLoan_updateLoan_ne hNe
    (fun x => ⟨x.id, .spatialPinned st.nextSpatialTag codec, x.cell, x.target⟩)
    (fun _ => rfl) st.loans

/-- A successful spatial mutation leaves every loan untouched. -/
theorem findLoan_mutate {Val : Type} {bid : BlockId} {tag : Nat}
    {newCells : List (CellVal Val)} {st st' : SymState Val} (lid' : LoanId)
    (h : mutateSpatialInState bid tag newCells st = .ok st') :
    findLoan lid' st'.loans = findLoan lid' st.loans := by
  rw [(mutateSpatialInState_ok_inv h).2.1]

/-- A successful unpin of `lid` leaves every other loan untouched. -/
theorem findLoan_unpin_ne {Val : Type} {alg : ValAlgebra Val} {lid lid' : LoanId}
    {codec : SpatialCodec Val} {st st' : SymState Val}
    (h : unpinFromSpatialInState alg lid codec st = .ok st') (hNe : lid' ≠ lid) :
    findLoan lid' st'.loans = findLoan lid' st.loans := by
  obtain ⟨_, _, _, _, _, v', _, _, _, _, _, hLoans⟩ := reabsorbFromSpatialInState_ok_inv h
  rw [hLoans]
  exact findLoan_updateLoan_ne hNe
    (fun x => ⟨x.id, .activeMut, ⟨v', x.cell.perm⟩, x.target⟩) (fun _ => rfl) st.loans

/-- **Unpinned-sibling isolation through freeze** (on a fixed live state). -/
theorem freeze_preserves_bindings (tagOf : LoanId → Nat) {alg : ValAlgebra StdVal}
    {lid : LoanId} {codec : SpatialCodec StdVal} {st st' : SymState StdVal}
    {ms : MachineState} (bindings : List (LoanId × Local × SubPath))
    (hFreeze : freezeToSpatialInState alg lid codec st = .ok st')
    (hNotIn : ∀ b, b ∈ bindings → b.1 ≠ lid)
    (h : spatialBindingsHold (mirSpatialModel tagOf) bindings st ms) :
    spatialBindingsHold (mirSpatialModel tagOf) bindings st' ms :=
  spatialBindingsHold_transfer tagOf rfl bindings
    (fun b hb => findLoan_freeze_ne hFreeze (hNotIn b hb)) (fun _ _ => rfl) h

/-- **Unpinned-sibling isolation through a spatial mutation and a live store**:
bindings of other loans survive `mutateSpatialInState` together with any live
store that leaves their places and the Tree Borrows table unchanged. -/
theorem mutate_preserves_bindings (tagOf : LoanId → Nat) {bid : BlockId} {tag : Nat}
    {newCells : List (CellVal StdVal)} {st st' : SymState StdVal} {ms ms' : MachineState}
    (bindings : List (LoanId × Local × SubPath))
    (hMut : mutateSpatialInState bid tag newCells st = .ok st')
    (hBorrows : ms'.memory.borrows = ms.memory.borrows)
    (hPlaces : ∀ b, b ∈ bindings → placeValue? ms' b.2.1 b.2.2 = placeValue? ms b.2.1 b.2.2)
    (h : spatialBindingsHold (mirSpatialModel tagOf) bindings st ms) :
    spatialBindingsHold (mirSpatialModel tagOf) bindings st' ms' :=
  spatialBindingsHold_transfer tagOf hBorrows bindings
    (fun b _ => findLoan_mutate b.1 hMut) hPlaces h

/-- **Unpinned-sibling isolation through unpin** (on a fixed live state). -/
theorem unpin_preserves_bindings (tagOf : LoanId → Nat) {alg : ValAlgebra StdVal}
    {lid : LoanId} {codec : SpatialCodec StdVal} {st st' : SymState StdVal}
    {ms : MachineState} (bindings : List (LoanId × Local × SubPath))
    (hUnpin : unpinFromSpatialInState alg lid codec st = .ok st')
    (hNotIn : ∀ b, b ∈ bindings → b.1 ≠ lid)
    (h : spatialBindingsHold (mirSpatialModel tagOf) bindings st ms) :
    spatialBindingsHold (mirSpatialModel tagOf) bindings st' ms :=
  spatialBindingsHold_transfer tagOf rfl bindings
    (fun b hb => findLoan_unpin_ne hUnpin (hNotIn b hb)) (fun _ _ => rfl) h

/-- Extending a disjoint binding list by a binding disjoint from every existing
one keeps it disjoint. -/
theorem spatialBindingsDisjoint_cons (tagOf : LoanId → Nat) (lid : LoanId) (l : Local)
    (path : SubPath) (bindings : List (LoanId × Local × SubPath))
    (hNew : ∀ b, b ∈ bindings → (mirSpatialModel tagOf).disjointSubPlaces l path b.2.1 b.2.2)
    (hOld : spatialBindingsDisjoint (mirSpatialModel tagOf) bindings) :
    spatialBindingsDisjoint (mirSpatialModel tagOf) ((lid, l, path) :: bindings) := by
  have key : ∀ bs : List (LoanId × Local × SubPath),
      (∀ b, b ∈ bs → (mirSpatialModel tagOf).disjointSubPlaces l path b.2.1 b.2.2) →
      listFold True
        (fun entry _ ihInner =>
          match entry with
          | (_, addr2, path2) =>
            (mirSpatialModel tagOf).disjointSubPlaces l path addr2 path2 ∧ ihInner)
        bs := by
    intro bs
    induction bs with
    | nil => intro _; trivial
    | cons b bs ih =>
      intro h
      rw [listFold_cons]
      exact ⟨h b (List.mem_cons_self ..), ih (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))⟩
  unfold spatialBindingsDisjoint
  rw [listFold_cons]
  exact ⟨key bindings hNew, hOld⟩

/-- **`unpinFromSpatialInState` restores the full relation with unpinned
siblings**: unpinning `lid` at `ms` re-establishes `mirStateRel` for the
unpinned binding together with every other loan binding that held during the
pin and is disjoint from the pinned place. -/
theorem unpin_restores_mirStateRel_frame {layouts : LayoutTable} {ty : Ty} {α : Type}
    {n : Nat} (m : MirTypedByteCodec layouts ty α n) (cid : Nat)
    (embed : α → StdVal) (embed? : StdVal → Option α)
    (embed_embed? : ∀ (v : StdVal) (x : α), embed? v = some x → embed x = v)
    (hInto : Anneal.BitValidity.IsIntoBytes layouts ty)
    (tagOf : LoanId → Nat) (alg : ValAlgebra StdVal) (lid : LoanId) (bid : BlockId)
    (codec' : SpatialCodec StdVal)
    {st st' : SymState StdVal} {ms : MachineState} {l : Local} {path : SubPath} {y : α}
    (bindings : List (LoanId × Local × SubPath))
    (hPin : spatialPinnedBlockHolds tagOf layouts ty lid bid
      (m.spatialCodec cid embed embed? embed_embed?) l path st ms)
    (hUnpin : unpinFromSpatialInState alg lid codec' st = .ok st')
    (hPlace : placeValue? ms l path = some (m.toValue y))
    (hRef : StdValRefines tagOf (embed y) (m.toValue y))
    (hLocals : mirLocalsRel tagOf st ms)
    (hOthers : spatialBindingsHold (mirSpatialModel tagOf) bindings st ms)
    (hNotIn : ∀ b, b ∈ bindings → b.1 ≠ lid)
    (hDisj : ∀ b, b ∈ bindings → (mirSpatialModel tagOf).disjointSubPlaces l path b.2.1 b.2.2) :
    mirStateRel tagOf ((lid, l, path) :: bindings) st' ms := by
  obtain ⟨⟨_, hSingle⟩, hLocals'⟩ :=
    unpin_restores_mirStateRel m cid embed embed? embed_embed? hInto tagOf alg lid bid codec'
      hPin hUnpin hPlace hRef hLocals
  have hOthers' := unpin_preserves_bindings tagOf bindings hUnpin hNotIn hOthers
  refine ⟨⟨spatialBindingsDisjoint_cons tagOf lid l path bindings hDisj hOthers.1, ?_⟩,
    hLocals'⟩
  rw [listFold_cons] at hSingle ⊢
  exact ⟨hSingle.1, hOthers'.2⟩

end PinLifecycle

/-! ### Concrete codecs: exact-width little-endian `u32` and Rust `bool` -/

/-- MIR type `u32`. -/
def u32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }

/-- MIR type `bool`. -/
def boolTy : Ty := { kind := .bool, layoutIdx := 0 }

/-- Exact-width (4-byte) little-endian `u32` byte codec, decoding exactly the
windows the trusted `u32` decoder accepts (any provenance is ignored, as in
`decodeScalarBytes`). -/
def u32ExactLE : Anneal.SepLogicLenses.ByteLensCodec {v : Nat // v < 256 ^ 4} 4 where
  encode v := encodeLittleEndianBytes v.val 4 none
  decode bs :=
    match Nat.beq bs.length 4 with
    | false => none
    | true =>
      match decodeLittleEndianBytes bs with
      | some (v, _) => if h : v < 256 ^ 4 then some ⟨v, h⟩ else none
      | none => none
  encode_len v := Anneal.SepLogicLenses.ByteLensCodec.length_encodeLE v.val 4 none
  decode_encode v := by
    have hLen : (encodeLittleEndianBytes v.val 4 none).length = 4 :=
      Anneal.SepLogicLenses.ByteLensCodec.length_encodeLE v.val 4 none
    have hd := Anneal.SepLogicLenses.ByteLensCodec.decodeLE_encodeLE 4 v.val none v.property
    cases he : decodeLittleEndianBytes (encodeLittleEndianBytes v.val 4 none) with
    | none => rw [he] at hd; exact nomatch hd
    | some p =>
      obtain ⟨w, rp⟩ := p
      rw [he] at hd
      have hw : w = v.val := Option.some.inj hd
      subst hw
      simp only [hLen, Nat.beq_refl]
      exact dite_eq_left v.property

/-- `u32ExactLE` decodes a 4-byte window whose little-endian value is below
`256 ^ 4`. -/
theorem u32ExactLE_decode_of (bs : List AbstractByte) (bits : Nat)
    (prov : Option (Nat × Nat)) (hLen : bs.length = 4)
    (hLE : decodeLittleEndianBytes bs = some (bits, prov)) (hLt : bits < 256 ^ 4) :
    u32ExactLE.decode bs = some ⟨bits, hLt⟩ := by
  have hBeq : Nat.beq bs.length 4 = true := by rw [hLen]; rfl
  unfold u32ExactLE
  simp only [hBeq, hLE]
  exact dite_eq_left hLt

/-- `u32` as a MIR-typed byte codec: `x ↦ .scalar ⟨x, 4⟩`, agreeing with the
trusted operational `u32` byte codec at every layout table. -/
def u32MirCodec (layouts : LayoutTable) :
    MirTypedByteCodec layouts u32Ty {v : Nat // v < 256 ^ 4} 4 where
  codec := u32ExactLE
  toValue x := .scalar ⟨x.val, 4⟩
  ofValue v :=
    match v with
    | .scalar sv =>
      match Nat.beq sv.sizeBytes 4 with
      | true => if h : sv.bits < 256 ^ 4 then some ⟨sv.bits, h⟩ else none
      | false => none
    | _ => none
  ofValue_toValue x := dite_eq_left x.property
  tySize_eq := rfl
  encode_toValue _ := rfl
  decode_eq_map bs := by
    have hLenDef : Trusted.Sequence.length bs = bs.length := rfl
    show (match Nat.beq (Trusted.Sequence.length bs) 4 with
      | false => none
      | true =>
        match decodeScalarBytes bs false with
        | some (sv, _) => some (Value.scalar sv)
        | none => none) =
      Option.map (fun x : {v : Nat // v < 256 ^ 4} => Value.scalar ⟨x.val, 4⟩)
        (match Nat.beq bs.length 4 with
        | false => none
        | true =>
          match decodeLittleEndianBytes bs with
          | some (v, _) => if h : v < 256 ^ 4 then some ⟨v, h⟩ else none
          | none => none)
    rw [hLenDef]
    cases hLen : Nat.beq bs.length 4 with
    | false => rfl
    | true =>
      have hLenEq : bs.length = 4 := Nat.eq_of_beq_eq_true hLen
      dsimp only
      unfold decodeScalarBytes
      rw [hLenDef, hLenEq]
      dsimp only
      cases hLE : decodeLittleEndianBytes bs with
      | none => rfl
      | some bp =>
        obtain ⟨bits, prov⟩ := bp
        have hMod := Anneal.BitValidity.decodeLittleEndianBytes_lt_scalarModulus bs bits prov hLE
        rw [hLenDef, hLenEq, Anneal.Scalars.scalarModulus_eq_two_pow] at hMod
        have hLt : bits < 256 ^ 4 := by
          have h256 : (256 : Nat) ^ 4 = 2 ^ (8 * 4) := rfl
          rw [h256]
          exact hMod
        dsimp only
        rw [dite_eq_left hLt]
        rfl
  encode_provenanceFree x := provenanceFree_encodeLittleEndianBytes 4 x.val

/-- Exact Rust `bool` byte codec (`false ↦ 0x00`, `true ↦ 0x01`), rejecting
`.uninit`, wrong widths, and every other bit pattern (such as `0x02`), exactly
as the trusted `bool` decoder does. -/
def boolExact : Anneal.SepLogicLenses.ByteLensCodec Bool 1 where
  encode b :=
    match b with
    | false => [.init (UInt8.ofNat 0) none]
    | true => [.init (UInt8.ofNat 1) none]
  decode bs :=
    match bs with
    | [.init b _] =>
      match Nat.beq b.toBitVec.toNat 0 with
      | true => some false
      | false =>
        match Nat.beq b.toBitVec.toNat 1 with
        | true => some true
        | false => none
    | _ => none
  encode_len b := by cases b <;> rfl
  decode_encode b := by cases b <;> rfl

/-- Rust `bool` as a MIR-typed byte codec: `b ↦ .scalar ⟨b ? 1 : 0, 1⟩`. -/
def boolMirCodec (layouts : LayoutTable) : MirTypedByteCodec layouts boolTy Bool 1 where
  codec := boolExact
  toValue b := .scalar ⟨if b then 1 else 0, 1⟩
  ofValue v :=
    match v with
    | .scalar sv =>
      if Nat.beq sv.sizeBytes 1 then
        if Nat.beq sv.bits 0 then some false
        else if Nat.beq sv.bits 1 then some true
        else none
      else none
    | _ => none
  ofValue_toValue b := by cases b <;> rfl
  tySize_eq := rfl
  encode_toValue b := by cases b <;> rfl
  decode_eq_map bs := by
    cases bs with
    | nil => rfl
    | cons b0 rest =>
      cases b0 with
      | uninit => rfl
      | init b prov =>
        cases rest with
        | cons _ _ => rfl
        | nil =>
          show (match Nat.beq b.toBitVec.toNat 0 with
            | true => some (Value.scalar ⟨0, 1⟩)
            | false =>
              match Nat.beq b.toBitVec.toNat 1 with
              | true => some (Value.scalar ⟨1, 1⟩)
              | false => none) =
            Option.map (fun b : Bool => Value.scalar ⟨if b then 1 else 0, 1⟩)
              (match Nat.beq b.toBitVec.toNat 0 with
              | true => some false
              | false =>
                match Nat.beq b.toBitVec.toNat 1 with
                | true => some true
                | false => none)
          cases Nat.beq b.toBitVec.toNat 0 <;> cases Nat.beq b.toBitVec.toNat 1 <;> rfl
  encode_provenanceFree b := by cases b <;> rfl

/-- Embedding of `u32` codec values into `StdVal` naturals. -/
def u32Embed (x : {v : Nat // v < 256 ^ 4}) : StdVal := .nat x.val

/-- Partial inverse of `u32Embed`. -/
def u32Embed? (v : StdVal) : Option {v : Nat // v < 256 ^ 4} :=
  match stdNatVal? v with
  | some k => if h : k < 256 ^ 4 then some ⟨k, h⟩ else none
  | none => none

theorem u32Embed_embed? (v : StdVal) (x : {v : Nat // v < 256 ^ 4})
    (h : u32Embed? v = some x) : u32Embed x = v := by
  cases v with
  | mk fuel tree =>
    cases tree with
    | nat k =>
      unfold u32Embed? at h
      change (if h : k < 256 ^ 4 then some ⟨k, h⟩ else none) = some x at h
      by_cases hk : k < 256 ^ 4
      · rw [dite_eq_left hk] at h
        injection h with h
        subst h
        rfl
      · rw [dite_eq_right hk] at h
        exact nomatch h
    | _ => exact nomatch h

/-- `u32` `SpatialCodec` over `StdVal` (codec id `32`). -/
def u32SpatialCodec (layouts : LayoutTable) : SpatialCodec StdVal :=
  (u32MirCodec layouts).spatialCodec 32 u32Embed u32Embed? u32Embed_embed?

/-- Embedding of Rust `bool` values into `StdVal` booleans. -/
def boolEmbed (b : Bool) : StdVal := .bool b

theorem boolEmbed_embed? (v : StdVal) (b : Bool) (h : stdAsBool v = some b) :
    boolEmbed b = v := by
  cases v with
  | mk fuel tree =>
    cases tree with
    | bool c =>
      change some c = some b at h
      injection h with h
      subst h
      rfl
    | _ => exact nomatch h

/-- Rust `bool` `SpatialCodec` over `StdVal` (codec id `1`). -/
def boolSpatialCodec (layouts : LayoutTable) : SpatialCodec StdVal :=
  (boolMirCodec layouts).spatialCodec 1 boolEmbed stdAsBool boolEmbed_embed?

/-- Every codec value is refined by its MIR embedding. -/
theorem u32Embed_refines (tagOf : LoanId → Nat) (layouts : LayoutTable)
    (x : {v : Nat // v < 256 ^ 4}) :
    StdValRefines tagOf (u32Embed x) ((u32MirCodec layouts).toValue x) :=
  .nat x.property

theorem boolEmbed_refines (tagOf : LoanId → Nat) (layouts : LayoutTable) (b : Bool) :
    StdValRefines tagOf (boolEmbed b) ((boolMirCodec layouts).toValue b) :=
  .bool b

/-- The trusted little-endian decoder succeeds on every fully initialized byte
list. -/
theorem decodeLittleEndianBytes_isSome_of_init : ∀ (bs : List AbstractByte),
    Anneal.BitValidity.allBytesInitialized bs = true →
    Exists fun r => decodeLittleEndianBytes bs = some r
  | [], _ => ⟨_, rfl⟩
  | .uninit :: _, h => nomatch h
  | .init b p :: rest, h => by
    obtain ⟨⟨hi, rp⟩, hr⟩ := decodeLittleEndianBytes_isSome_of_init rest h
    refine ⟨(Nat.add b.toBitVec.toNat (Nat.mul 256 hi), mergeByteProvenance p rp), ?_⟩
    show (match decodeLittleEndianBytes rest with
      | some (highBits, restProv) =>
        some (Nat.add b.toBitVec.toNat (Nat.mul 256 highBits),
          mergeByteProvenance p restProv)
      | none => none) = _
    rw [hr]

/-- `u32` is `zerocopy::FromBytes` (every initialized 4-byte window decodes). -/
theorem u32_isFromBytes (layouts : LayoutTable) :
    Anneal.BitValidity.IsFromBytes layouts u32Ty := by
  refine (u32MirCodec layouts).isFromBytes ?_
  intro bs hLen hInit
  have hBeq : Nat.beq bs.length 4 = true := by rw [hLen]; rfl
  obtain ⟨⟨bits, prov⟩, hLE⟩ := decodeLittleEndianBytes_isSome_of_init bs hInit
  have hMod := Anneal.BitValidity.decodeLittleEndianBytes_lt_scalarModulus bs bits prov hLE
  have hLenDef : Trusted.Sequence.length bs = bs.length := rfl
  rw [hLenDef, hLen, Anneal.Scalars.scalarModulus_eq_two_pow] at hMod
  have hLt : bits < 256 ^ 4 := by
    have h256 : (256 : Nat) ^ 4 = 2 ^ (8 * 4) := rfl
    rw [h256]
    exact hMod
  exact ⟨⟨bits, hLt⟩, u32ExactLE_decode_of bs bits prov hLen hLE hLt⟩

/-- `u32` is `zerocopy::IntoBytes` (every trusted `u32` encoding is 4
initialized bytes). -/
theorem u32_isIntoBytes (layouts : LayoutTable) :
    Anneal.BitValidity.IsIntoBytes layouts u32Ty := by
  refine ⟨4, rfl, ?_⟩
  intro v bs hEnc
  cases v with
  | scalar sv =>
    change (match Nat.beq sv.sizeBytes 4 with
      | true => encodeScalarBytes sv none
      | false => none) = some bs at hEnc
    cases hSz : Nat.beq sv.sizeBytes 4 with
    | false => rw [hSz] at hEnc; exact nomatch hEnc
    | true =>
      rw [hSz] at hEnc
      have hSzEq : sv.sizeBytes = 4 := Nat.eq_of_beq_eq_true hSz
      unfold encodeScalarBytes at hEnc
      rw [hSzEq] at hEnc
      injection hEnc with hBs
      subst hBs
      exact ⟨Anneal.SepLogicLenses.ByteLensCodec.length_encodeLE sv.bits 4 none,
        allBytesInitialized_encodeLittleEndianBytes 4 sv.bits⟩
  | _ => exact nomatch hEnc

/-- Rust `bool` is `zerocopy::IntoBytes`, via the codec-witness bridge
`MirTypedByteCodec.isIntoBytes`. -/
theorem bool_isIntoBytes (layouts : LayoutTable) :
    Anneal.BitValidity.IsIntoBytes layouts boolTy := by
  refine (boolMirCodec layouts).isIntoBytes (fun b => by cases b <;> rfl) ?_
  intro v bs hEnc
  cases v with
  | scalar sv =>
    change (match Nat.beq sv.sizeBytes 1 with
      | false => none
      | true =>
        match Nat.beq sv.bits 0 with
        | true => some [.init (UInt8.ofNat 0) none]
        | false =>
          match Nat.beq sv.bits 1 with
          | true => some [.init (UInt8.ofNat 1) none]
          | false => none) = some bs at hEnc
    cases h1 : Nat.beq sv.sizeBytes 1 with
    | false => rw [h1] at hEnc; exact nomatch hEnc
    | true =>
      rw [h1] at hEnc
      cases h0 : Nat.beq sv.bits 0 with
      | true =>
        rw [h0] at hEnc
        injection hEnc with hBs
        exact ⟨false, hBs.symm⟩
      | false =>
        rw [h0] at hEnc
        cases h1' : Nat.beq sv.bits 1 with
        | false => rw [h1'] at hEnc; exact nomatch hEnc
        | true =>
          rw [h1'] at hEnc
          injection hEnc with hBs
          exact ⟨true, hBs.symm⟩
  | _ => exact nomatch hEnc

/-- `bool` is `zerocopy::TryFromBytes` (every trusted decode is a Rust `bool`)
but not `zerocopy::FromBytes` (`0x02` is initialized yet invalid). -/
theorem bool_tryFromBytes_not_fromBytes (layouts : LayoutTable) :
    Anneal.BitValidity.IsTryFromBytes layouts boolTy
      (fun v => Exists fun b => (boolMirCodec layouts).toValue b = v ∧
        (boolMirCodec layouts).ofValue v = some b) ∧
    ¬ Anneal.BitValidity.IsFromBytes layouts boolTy :=
  ⟨(boolMirCodec layouts).isTryFromBytes,
   (boolMirCodec layouts).not_isFromBytes [.init (UInt8.ofNat 2) none] rfl rfl rfl⟩

/-- Concatenating two provenance-free byte windows preserves
`provenanceFree`. -/
theorem provenanceFree_append :
    ∀ (bs1 bs2 : List AbstractByte),
      provenanceFree bs1 = true → provenanceFree bs2 = true →
      provenanceFree (bs1 ++ bs2) = true
  | [], _, _, h2 => h2
  | b :: rest, bs2, h1, h2 => by
    cases b with
    | uninit => exact provenanceFree_append rest bs2 h1 h2
    | init _ p =>
      cases p with
      | none => exact provenanceFree_append rest bs2 h1 h2
      | some _ => exact nomatch h1

/-- Multi-field aggregate `(u32, u32)` 8-byte little-endian codec built via
`SepLogicLenses.ByteLensCodec.prod`, connected to live MIR tuple byte windows via
`placeByteWindow?_u32Pair_fieldsTyped`. -/
def u32PairExactLE :
    Anneal.SepLogicLenses.ByteLensCodec
      ({v : Nat // v < 256 ^ 4} × {v : Nat // v < 256 ^ 4}) 8 :=
  Anneal.SepLogicLenses.ByteLensCodec.prod u32ExactLE u32ExactLE

theorem u32PairExactLE_provenanceFree
    (p : {v : Nat // v < 256 ^ 4} × {v : Nat // v < 256 ^ 4}) :
    provenanceFree (u32PairExactLE.encode p) = true :=
  provenanceFree_append _ _
    (provenanceFree_encodeLittleEndianBytes 4 p.1.val)
    (provenanceFree_encodeLittleEndianBytes 4 p.2.val)

/-- Embedding of `(u32, u32)` codec pairs into `StdVal.pair`. -/
def u32PairEmbed (p : {v : Nat // v < 256 ^ 4} × {v : Nat // v < 256 ^ 4}) : StdVal :=
  .pair (.nat p.1.val) (.nat p.2.val)

/-- Partial inverse of `u32PairEmbed`. -/
def u32PairEmbed? (v : StdVal) :
    Option ({v : Nat // v < 256 ^ 4} × {v : Nat // v < 256 ^ 4}) :=
  match v with
  | ⟨_, .pairBranch _ _ (.nat a) (.nat b)⟩ =>
    if ha : a < 256 ^ 4 then
      if hb : b < 256 ^ 4 then some (⟨a, ha⟩, ⟨b, hb⟩) else none
    else none
  | _ => none

theorem u32PairEmbed_embed? (v : StdVal)
    (p : {v : Nat // v < 256 ^ 4} × {v : Nat // v < 256 ^ 4})
    (h : u32PairEmbed? v = some p) : u32PairEmbed p = v := by
  cases v with
  | mk f t =>
    cases t with
    | pairBranch fl fr ta tb =>
      cases ta with
      | nat a =>
        cases tb with
        | nat b =>
          unfold u32PairEmbed? at h
          dsimp only at h
          by_cases ha : a < 256 ^ 4
          · rw [dite_eq_left ha] at h
            by_cases hb : b < 256 ^ 4
            · rw [dite_eq_left hb] at h
              injection h with h
              subst h
              rfl
            · rw [dite_eq_right hb] at h
              exact nomatch h
          · rw [dite_eq_right ha] at h
            exact nomatch h
        | _ => exact nomatch h
      | _ => exact nomatch h
    | _ => exact nomatch h

/-- Multi-field `(u32, u32)` `SpatialCodec` over `StdVal` (codec id `64`). -/
def u32PairSpatialCodec : SpatialCodec StdVal :=
  spatialCodecOfByteLensCodec 64 u32PairExactLE u32PairExactLE_provenanceFree
    u32PairEmbed u32PairEmbed? u32PairEmbed_embed?

/-- **Multi-field aggregate `FieldsTyped` bridge**: every encoded `(u32, u32)`
window satisfies `SepLogicLenses.FieldsTyped u32ExactLE 0 u32ExactLE 4` at
disjoint field offsets `0` and `4`. -/
theorem u32PairExactLE_encode_fieldsTyped
    (x y : {v : Nat // v < 256 ^ 4}) :
    Anneal.SepLogicLenses.FieldsTyped u32ExactLE 0 u32ExactLE 4
      (u32PairExactLE.encode (x, y)) ∧
    Anneal.SepLogicLenses.TypedAt u32ExactLE 0 x (u32PairExactLE.encode (x, y)) ∧
    Anneal.SepLogicLenses.TypedAt u32ExactLE 4 y (u32PairExactLE.encode (x, y)) := by
  have h0 : Anneal.SepLogicLenses.TypedAt u32ExactLE 0 x (u32PairExactLE.encode (x, y)) := by
    have h := Anneal.SepLogicLenses.typedAt_append_encode u32ExactLE [] (u32ExactLE.encode y) x
    simp only [List.nil_append, List.length_nil] at h
    exact h
  have h4 : Anneal.SepLogicLenses.TypedAt u32ExactLE 4 y (u32PairExactLE.encode (x, y)) := by
    have h := Anneal.SepLogicLenses.typedAt_append_encode u32ExactLE (u32ExactLE.encode x) [] y
    rw [u32ExactLE.encode_len x, List.append_nil] at h
    exact h
  exact ⟨⟨⟨x, h0⟩, ⟨y, h4⟩⟩, h0, h4⟩

/-- MIR tuple type `(u32, u32)` at layout index `idx`. -/
def u32PairTy (idx : Nat := 0) : Ty :=
  { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := idx }

theorem appendAbstractBytes_eq_append :
    ∀ (xs ys : List AbstractByte), appendAbstractBytes xs ys = xs ++ ys
  | [], _ => rfl
  | x :: xs, ys => congrArg (x :: ·) (appendAbstractBytes_eq_append xs ys)

/-- **Live MIR tuple byte window = `u32PairExactLE.encode` (`FieldsTyped`)**:
when the live MIR place `_l.path` holds `.aggregate 0 [.scalar ⟨x.val, 4⟩,
.scalar ⟨y.val, 4⟩]` and `LayoutTable.lookup layouts idx = none` (so the trusted
encoder uses sequential field layout `encodeSeqFieldsWith`), the place's trusted
byte window `placeByteWindow?` is `some (u32PairExactLE.encode (x, y))`, which
satisfies `SepLogicLenses.FieldsTyped u32ExactLE 0 u32ExactLE 4` at field
offsets `0` and `4`. -/
theorem placeByteWindow?_u32Pair_fieldsTyped {layouts : LayoutTable} {idx : Nat}
    (hLookup : LayoutTable.lookup layouts idx = none)
    (ms : MachineState) (l : Local) (path : SubPath)
    (x y : {v : Nat // v < 256 ^ 4})
    (hPlace :
      placeValue? ms l path =
        some (.aggregate 0 [.scalar ⟨x.val, 4⟩, .scalar ⟨y.val, 4⟩])) :
    Exists fun bs =>
      placeByteWindow? layouts (u32PairTy idx) ms l path = some bs ∧
      bs = u32PairExactLE.encode (x, y) ∧
      Anneal.SepLogicLenses.FieldsTyped u32ExactLE 0 u32ExactLE 4 bs := by
  refine ⟨u32PairExactLE.encode (x, y), ?_, rfl,
    (u32PairExactLE_encode_fieldsTyped x y).1⟩
  unfold placeValue? at hPlace
  unfold placeByteWindow?
  cases hSlot : lookupLocalSlot? ms l with
  | none => rw [hSlot] at hPlace; exact nomatch hPlace
  | some slot =>
    rw [hSlot] at hPlace
    cases slot with
    | init w =>
      dsimp only at hPlace ⊢
      rw [hPlace]
      show (match LayoutTable.lookup layouts idx with
        | some l => _
        | none =>
          encodeSeqFieldsWith
            (fun k fv => encodeValueToBytes 15 layouts { kind := k, layoutIdx := 0 } fv)
            [.uint .u32, .uint .u32]
            [.scalar ⟨x.val, 4⟩, .scalar ⟨y.val, 4⟩]) =
        some (u32ExactLE.encode x ++ u32ExactLE.encode y)
      rw [hLookup]
      show some (appendAbstractBytes (u32ExactLE.encode x)
        (appendAbstractBytes (u32ExactLE.encode y) [])) =
        some (u32ExactLE.encode x ++ u32ExactLE.encode y)
      rw [appendAbstractBytes_eq_append, appendAbstractBytes_eq_append, List.append_nil]
    | uninit => exact nomatch hPlace
    | dead => exact nomatch hPlace

/-! ### Niche Codec: `NonZeroU32` (`0 < v < 256 ^ 4`, rejecting `0`) -/

/-- Exact-width 4-byte little-endian `NonZeroU32` codec (`0 < v < 256 ^ 4`),
rejecting all-zero bytes `[0, 0, 0, 0]` as well as `.uninit` and wrong widths. -/
def nonZeroU32ExactLE :
    Anneal.SepLogicLenses.ByteLensCodec {v : Nat // 0 < v ∧ v < 256 ^ 4} 4 where
  encode v := encodeLittleEndianBytes v.val 4 none
  decode bs :=
    match u32ExactLE.decode bs with
    | some ⟨v, hLt⟩ => if hPos : 0 < v then some ⟨v, ⟨hPos, hLt⟩⟩ else none
    | none => none
  encode_len v := Anneal.SepLogicLenses.ByteLensCodec.length_encodeLE v.val 4 none
  decode_encode v := by
    have hDec : u32ExactLE.decode (encodeLittleEndianBytes v.val 4 none) =
        some ⟨v.val, v.property.2⟩ :=
      u32ExactLE.decode_encode ⟨v.val, v.property.2⟩
    change (match u32ExactLE.decode (encodeLittleEndianBytes v.val 4 none) with
      | some ⟨w, hLt⟩ => if hPos : 0 < w then some ⟨w, ⟨hPos, hLt⟩⟩ else none
      | none => none) = some v
    rw [hDec]
    exact dite_eq_left v.property.1

theorem nonZeroU32ExactLE_provenanceFree (v : {v : Nat // 0 < v ∧ v < 256 ^ 4}) :
    provenanceFree (nonZeroU32ExactLE.encode v) = true :=
  provenanceFree_encodeLittleEndianBytes 4 v.val

def nonZeroU32Embed (x : {v : Nat // 0 < v ∧ v < 256 ^ 4}) : StdVal := .nat x.val

def nonZeroU32Embed? (v : StdVal) : Option {v : Nat // 0 < v ∧ v < 256 ^ 4} :=
  match stdNatVal? v with
  | some k =>
    if hPos : 0 < k then
      if hLt : k < 256 ^ 4 then some ⟨k, ⟨hPos, hLt⟩⟩ else none
    else none
  | none => none

theorem nonZeroU32Embed_embed? (v : StdVal) (x : {v : Nat // 0 < v ∧ v < 256 ^ 4})
    (h : nonZeroU32Embed? v = some x) : nonZeroU32Embed x = v := by
  cases v with
  | mk fuel tree =>
    cases tree with
    | nat k =>
      unfold nonZeroU32Embed? at h
      dsimp only [stdNatVal?] at h
      by_cases hPos : 0 < k
      · rw [dite_eq_left hPos] at h
        by_cases hLt : k < 256 ^ 4
        · rw [dite_eq_left hLt] at h
          injection h with h
          subst h
          rfl
        · rw [dite_eq_right hLt] at h
          exact nomatch h
      · rw [dite_eq_right hPos] at h
        exact nomatch h
    | _ => exact nomatch h

/-- `NonZeroU32` `SpatialCodec` over `StdVal` (codec id `33`). -/
def nonZeroU32SpatialCodec : SpatialCodec StdVal :=
  spatialCodecOfByteLensCodec 33 nonZeroU32ExactLE nonZeroU32ExactLE_provenanceFree
    nonZeroU32Embed nonZeroU32Embed? nonZeroU32Embed_embed?

end Anneal.PureLift.V2026_06_01Bridge
