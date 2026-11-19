-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import Trusted.MirAst
import Trusted.MirSemantics
import Anneal.PureLift.Lens
import Anneal.PureLift.PermTree
import Anneal.PureLift.LoanGraph
import Anneal.PureLift.SpatialPin
import Anneal.PureLift.Plan
import Anneal.PureLift.BlockCfg
import Anneal.PureLift.Adapter

namespace Anneal.PureLift

open Trusted

/-!
# Bridge Between `PureLift` and `Trusted` MIR Semantics (`MirBridge.lean`)

Connects the language- and MIR-agnostic `Anneal.PureLift` transformation to the
trusted `Runtime(PostCleanup)` MIR syntax (`Trusted/MirAst.lean`) and
small-step operational semantics (`Trusted/MirSemantics.lean`):

1. **Value Algebra and Lawful Field Lenses (`mirValAlg`):** instantiates
   `ValAlgebra Trusted.MirVal`, proves the three bidirectional lens laws
   (`get_put`, `put_get`, `put_put`) for `Trusted.getMirField` and
   `Trusted.setMirField` over arbitrary `Trusted.MirVal` struct and tuple
   spines (`mirFieldLens_lawful`), and derives lawful nested sub-path lenses
   (`mirSubPathLens_lawful`).
2. **Small-Step Operational Adapter (`mirOperationalAdapter`):** connects
   `Trusted.stepMirCore` and `Trusted.runMirSteps` to `OperationalAdapter` and
   the adequacy theorem `pure_lift_sound` (`mir_pure_lift_sound`) for
   functions that return values (`evalFnValue`) and whose reference
   parameters borrow whole caller slots (`MirArgsMatch`).
3. **MIR Workloads (`M-1` through `M-5`):** for concrete `Trusted.MirBody`
   programs (mutable reference mutation, `add_assign`; disjoint struct field
   swapping, `swap_fields`; conditional reborrowing across `SwitchInt` basic
   blocks, one concrete run per arm, `select_add`; and loop accumulation,
   `loop_accumulate`), each `*_verified` theorem shows that `PureLift` and
   `Trusted.runMirSteps` agree on the given inputs. The MIR run is established
   by executing the body step by step (`*_runsTo`), and that result
   discharges the simulation hypothesis `hSim` of `mir_pure_lift_sound`; the
   theorem does not derive the MIR run from `PureLift`. `M-5` checks that both
   semantics reject two invalid borrow-lifecycle programs.
-/

/-! ## Unfolding lemmas for `Trusted` `Nat.recCompiled` helpers -/

/-- Base-case unfolding of `Trusted.getSpineAt` on `.fieldCons` at index `0`. -/
theorem getSpineAt_zero_fieldCons (h t : MirVal) :
    getSpineAt 0 (.fieldCons h t) = some h := rfl

/-- Step-case unfolding of `Trusted.getSpineAt` on `.fieldCons` at `idx + 1`. -/
theorem getSpineAt_succ_fieldCons (idx : Nat) (h t : MirVal) :
    getSpineAt (idx + 1) (.fieldCons h t) = getSpineAt idx t := rfl

/-- Base-case unfolding of `Trusted.setSpineAt` on `.fieldCons` at index `0`. -/
theorem setSpineAt_zero_fieldCons (newVal h t : MirVal) :
    setSpineAt 0 newVal (.fieldCons h t) = some (.fieldCons newVal t) := rfl

/-- Step-case unfolding of `Trusted.setSpineAt` on `.fieldCons` at `idx + 1`. -/
theorem setSpineAt_succ_fieldCons (idx : Nat) (newVal h t : MirVal) :
    setSpineAt (idx + 1) newVal (.fieldCons h t) =
      match setSpineAt idx newVal t with
      | some t' => some (.fieldCons h t')
      | none => none := rfl

/-- Step-case unfolding of `Trusted.stepMirLoop` at `fuel + 1`. -/
theorem stepMirLoop_succ (body : MirBody) (fuel : Nat) (st : MirState) :
    stepMirLoop body (fuel + 1) st =
      match stepMirCore body st with
      | .stepped next => stepMirLoop body fuel next
      | .returned ret => .returned ret
      | .fault => .fault := rfl

/-! ## Value Algebra and Spine Lens Laws for `Trusted.MirVal` -/

/-- Conditional branch value selector on `Trusted.MirVal`. -/
def mirZipVal (cond vt vf : MirVal) : MirVal :=
  match cond with
  | ⟨_, .bool b⟩ => if b then vt else vf
  | ⟨_, .int n⟩ => if n != 0 then vt else vf
  | _ => vf

/-- `getSpineAt` followed by `setSpineAt` with the retrieved element restores
the original spine. -/
theorem getSpineAt_setSpineAt (idx : Nat) :
    ∀ (spine v : MirVal),
      getSpineAt idx spine = some v →
      setSpineAt idx v spine = some spine := by
  induction idx with
  | zero =>
    intro spine v hGet
    cases spine with
    | mk fs ts =>
      cases ts with
      | fieldCons h t =>
        change getSpineAt 0 (.fieldCons ⟨_, h⟩ ⟨_, t⟩) = some v at hGet
        rw [getSpineAt_zero_fieldCons] at hGet
        injection hGet with hEq
        subst hEq
        rfl
      | uninit => cases hGet
      | int _ => cases hGet
      | bool _ => cases hGet
      | unit => cases hGet
      | adt _ _ => cases hGet
      | ref _ _ _ _ _ => cases hGet
  | succ i ih =>
    intro spine v hGet
    cases spine with
    | mk fs ts =>
      cases ts with
      | fieldCons h t =>
        change getSpineAt (i + 1) (.fieldCons ⟨_, h⟩ ⟨_, t⟩) = some v at hGet
        rw [getSpineAt_succ_fieldCons] at hGet
        change
          setSpineAt (i + 1) v (.fieldCons ⟨_, h⟩ ⟨_, t⟩) =
            some (.fieldCons ⟨_, h⟩ ⟨_, t⟩)
        rw [setSpineAt_succ_fieldCons, ih ⟨_, t⟩ v hGet]
      | uninit => cases hGet
      | int _ => cases hGet
      | bool _ => cases hGet
      | unit => cases hGet
      | adt _ _ => cases hGet
      | ref _ _ _ _ _ => cases hGet

/-- `setSpineAt` followed by `getSpineAt` at the same index returns the written
element. -/
theorem setSpineAt_getSpineAt (idx : Nat) :
    ∀ (spine v spine' : MirVal),
      setSpineAt idx v spine = some spine' →
      getSpineAt idx spine' = some v := by
  induction idx with
  | zero =>
    intro spine v spine' hSet
    cases spine with
    | mk fs ts =>
      cases ts with
      | fieldCons h t =>
        change setSpineAt 0 v (.fieldCons ⟨_, h⟩ ⟨_, t⟩) = some spine' at hSet
        rw [setSpineAt_zero_fieldCons] at hSet
        injection hSet with hEq
        subst hEq
        rfl
      | uninit => cases hSet
      | int _ => cases hSet
      | bool _ => cases hSet
      | unit => cases hSet
      | adt _ _ => cases hSet
      | ref _ _ _ _ _ => cases hSet
  | succ i ih =>
    intro spine v spine' hSet
    cases spine with
    | mk fs ts =>
      cases ts with
      | fieldCons h t =>
        change
          setSpineAt (i + 1) v (.fieldCons ⟨_, h⟩ ⟨_, t⟩) = some spine' at hSet
        rw [setSpineAt_succ_fieldCons] at hSet
        revert hSet
        cases hRec : setSpineAt i v ⟨_, t⟩ with
        | none =>
          intro hFalse
          cases hFalse
        | some t' =>
          intro hSet
          injection hSet with hEq
          subst hEq
          rw [getSpineAt_succ_fieldCons]
          exact ih ⟨_, t⟩ v t' hRec
      | uninit => cases hSet
      | int _ => cases hSet
      | bool _ => cases hSet
      | unit => cases hSet
      | adt _ _ => cases hSet
      | ref _ _ _ _ _ => cases hSet

/-- Two consecutive `setSpineAt` updates at the same index overwrite the first
update. -/
theorem setSpineAt_setSpineAt (idx : Nat) :
    ∀ (spine v1 v2 spine1 : MirVal),
      setSpineAt idx v1 spine = some spine1 →
      setSpineAt idx v2 spine1 = setSpineAt idx v2 spine := by
  induction idx with
  | zero =>
    intro spine v1 v2 spine1 hSet
    cases spine with
    | mk fs ts =>
      cases ts with
      | fieldCons h t =>
        change
          setSpineAt 0 v1 (.fieldCons ⟨_, h⟩ ⟨_, t⟩) = some spine1 at hSet
        rw [setSpineAt_zero_fieldCons] at hSet
        injection hSet with hEq
        subst hEq
        rfl
      | uninit => cases hSet
      | int _ => cases hSet
      | bool _ => cases hSet
      | unit => cases hSet
      | adt _ _ => cases hSet
      | ref _ _ _ _ _ => cases hSet
  | succ i ih =>
    intro spine v1 v2 spine1 hSet
    cases spine with
    | mk fs ts =>
      cases ts with
      | fieldCons h t =>
        change
          setSpineAt (i + 1) v1 (.fieldCons ⟨_, h⟩ ⟨_, t⟩) = some spine1 at hSet
        rw [setSpineAt_succ_fieldCons] at hSet
        revert hSet
        cases hRec : setSpineAt i v1 ⟨_, t⟩ with
        | none =>
          intro hFalse
          cases hFalse
        | some t' =>
          intro hSet
          injection hSet with hEq
          subst hEq
          change
            setSpineAt (i + 1) v2 (.fieldCons ⟨_, h⟩ t') =
            setSpineAt (i + 1) v2 (.fieldCons ⟨_, h⟩ ⟨_, t⟩)
          rw [setSpineAt_succ_fieldCons, setSpineAt_succ_fieldCons,
              ih ⟨_, t⟩ v1 v2 t' hRec]
      | uninit => cases hSet
      | int _ => cases hSet
      | bool _ => cases hSet
      | unit => cases hSet
      | adt _ _ => cases hSet
      | ref _ _ _ _ _ => cases hSet

/-- `setSpineAt` at index `i` leaves the element at every other index `j`
unchanged. -/
theorem setSpineAt_getSpineAt_other (i : Nat) :
    ∀ (j : Nat) (spine v spine' : MirVal), i ≠ j →
      setSpineAt i v spine = some spine' →
      getSpineAt j spine' = getSpineAt j spine := by
  induction i with
  | zero =>
    intro j spine v spine' hNe hSet
    cases spine with
    | mk fs ts =>
      cases ts with
      | fieldCons h t =>
        change setSpineAt 0 v (.fieldCons ⟨_, h⟩ ⟨_, t⟩) = some spine' at hSet
        rw [setSpineAt_zero_fieldCons] at hSet
        injection hSet with hEq
        subst hEq
        cases j with
        | zero => exact False.elim (hNe rfl)
        | succ j' => rfl
      | uninit => cases hSet
      | int _ => cases hSet
      | bool _ => cases hSet
      | unit => cases hSet
      | adt _ _ => cases hSet
      | ref _ _ _ _ _ => cases hSet
  | succ i ih =>
    intro j spine v spine' hNe hSet
    cases spine with
    | mk fs ts =>
      cases ts with
      | fieldCons h t =>
        change
          setSpineAt (i + 1) v (.fieldCons ⟨_, h⟩ ⟨_, t⟩) = some spine' at hSet
        rw [setSpineAt_succ_fieldCons] at hSet
        revert hSet
        cases hRec : setSpineAt i v ⟨_, t⟩ with
        | none =>
          intro hFalse
          cases hFalse
        | some t' =>
          intro hSet
          injection hSet with hEq
          subst hEq
          cases j with
          | zero => rfl
          | succ j' =>
            rw [getSpineAt_succ_fieldCons]
            exact ih j' ⟨_, t⟩ v t' (fun hEq => hNe (congrArg Nat.succ hEq))
              hRec
      | uninit => cases hSet
      | int _ => cases hSet
      | bool _ => cases hSet
      | unit => cases hSet
      | adt _ _ => cases hSet
      | ref _ _ _ _ _ => cases hSet

/-- Every element index and element size of a `.fieldCons` spine is below the
spine's size. -/
theorem getSpineAt_lt_fuel (i : Nat) :
    ∀ (spine c : MirVal),
      getSpineAt i spine = some c → i < spine.fuel ∧ c.fuel < spine.fuel := by
  induction i with
  | zero =>
    intro spine c hGet
    cases spine with
    | mk fs ts =>
      cases ts with
      | fieldCons h t =>
        change getSpineAt 0 (.fieldCons ⟨_, h⟩ ⟨_, t⟩) = some c at hGet
        rw [getSpineAt_zero_fieldCons] at hGet
        injection hGet with hEq
        subst hEq
        exact ⟨Nat.zero_lt_succ _, Nat.lt_succ_of_le (Nat.le_add_right _ _)⟩
      | uninit => cases hGet
      | int _ => cases hGet
      | bool _ => cases hGet
      | unit => cases hGet
      | adt _ _ => cases hGet
      | ref _ _ _ _ _ => cases hGet
  | succ i ih =>
    intro spine c hGet
    cases spine with
    | mk fs ts =>
      cases ts with
      | fieldCons h t =>
        change getSpineAt (i + 1) (.fieldCons ⟨_, h⟩ ⟨_, t⟩) = some c at hGet
        rw [getSpineAt_succ_fieldCons] at hGet
        have hSub := ih ⟨_, t⟩ c hGet
        exact ⟨Nat.succ_lt_succ
            (Nat.lt_of_lt_of_le hSub.1 (Nat.le_add_left _ _)),
          Nat.lt_succ_of_le
            (Nat.le_trans (Nat.le_of_lt hSub.2) (Nat.le_add_left _ _))⟩
      | uninit => cases hGet
      | int _ => cases hGet
      | bool _ => cases hGet
      | unit => cases hGet
      | adt _ _ => cases hGet
      | ref _ _ _ _ _ => cases hGet

/-- Every field index and field size of a `MirVal` aggregate is below the
value's size. -/
theorem mir_getField_lt_sizeBound (f : FieldIdx) (v c : MirVal)
    (hGet : getMirField f v = some c) : f < v.fuel ∧ c.fuel < v.fuel := by
  cases v with
  | mk fv tv =>
    cases tv with
    | adt id inner =>
      change getSpineAt f ⟨_, inner⟩ = some c at hGet
      have hSub := getSpineAt_lt_fuel f ⟨_, inner⟩ c hGet
      exact ⟨Nat.lt_succ_of_lt hSub.1, Nat.lt_succ_of_lt hSub.2⟩
    | fieldCons h t =>
      exact getSpineAt_lt_fuel f (.fieldCons ⟨_, h⟩ ⟨_, t⟩) c hGet
    | uninit => cases hGet
    | int _ => cases hGet
    | bool _ => cases hGet
    | unit => cases hGet
    | ref _ _ _ _ _ => cases hGet

/-- `setSpineAt` updates at distinct indices `i` and `j` commute: if updating
`i` and then `j` succeeds, so does updating `j` and then `i`, with the same
result. -/
theorem setSpineAt_setSpineAt_comm (i : Nat) :
    ∀ (j : Nat) (spine a b s1 s2 : MirVal), i ≠ j →
      setSpineAt i a spine = some s1 → setSpineAt j b s1 = some s2 →
      Exists fun s1' =>
        setSpineAt j b spine = some s1' ∧ setSpineAt i a s1' = some s2 := by
  induction i with
  | zero =>
    intro j spine a b s1 s2 hNe h1 h2
    cases spine with
    | mk fs ts =>
      cases ts with
      | fieldCons h t =>
        change setSpineAt 0 a (.fieldCons ⟨_, h⟩ ⟨_, t⟩) = some s1 at h1
        rw [setSpineAt_zero_fieldCons] at h1
        injection h1 with hEq1
        subst hEq1
        cases j with
        | zero => exact False.elim (hNe rfl)
        | succ j' =>
          change setSpineAt (j' + 1) b (.fieldCons a ⟨_, t⟩) = some s2 at h2
          rw [setSpineAt_succ_fieldCons] at h2
          revert h2
          cases hT : setSpineAt j' b ⟨_, t⟩ with
          | none =>
            intro hFalse
            cases hFalse
          | some t' =>
            intro h2
            injection h2 with hEq2
            subst hEq2
            refine ⟨.fieldCons ⟨_, h⟩ t', ?_, rfl⟩
            change setSpineAt (j' + 1) b (.fieldCons ⟨_, h⟩ ⟨_, t⟩) = _
            rw [setSpineAt_succ_fieldCons, hT]
      | uninit => cases h1
      | int _ => cases h1
      | bool _ => cases h1
      | unit => cases h1
      | adt _ _ => cases h1
      | ref _ _ _ _ _ => cases h1
  | succ i ih =>
    intro j spine a b s1 s2 hNe h1 h2
    cases spine with
    | mk fs ts =>
      cases ts with
      | fieldCons h t =>
        change setSpineAt (i + 1) a (.fieldCons ⟨_, h⟩ ⟨_, t⟩) = some s1 at h1
        rw [setSpineAt_succ_fieldCons] at h1
        revert h1
        cases hT1 : setSpineAt i a ⟨_, t⟩ with
        | none =>
          intro hFalse
          cases hFalse
        | some t1 =>
          intro h1
          injection h1 with hEq1
          subst hEq1
          cases j with
          | zero =>
            change setSpineAt 0 b (.fieldCons ⟨_, h⟩ t1) = some s2 at h2
            rw [setSpineAt_zero_fieldCons] at h2
            injection h2 with hEq2
            subst hEq2
            refine ⟨.fieldCons b ⟨_, t⟩, rfl, ?_⟩
            change setSpineAt (i + 1) a (.fieldCons b ⟨_, t⟩) = _
            rw [setSpineAt_succ_fieldCons, hT1]
          | succ j' =>
            change setSpineAt (j' + 1) b (.fieldCons ⟨_, h⟩ t1) = some s2 at h2
            rw [setSpineAt_succ_fieldCons] at h2
            revert h2
            cases hT2 : setSpineAt j' b t1 with
            | none =>
              intro hFalse
              cases hFalse
            | some t2 =>
              intro h2
              injection h2 with hEq2
              subst hEq2
              cases ih j' ⟨_, t⟩ a b t1 t2
                  (fun hEq => hNe (congrArg Nat.succ hEq)) hT1 hT2 with
              | intro t1' ht1' =>
                refine ⟨.fieldCons ⟨_, h⟩ t1', ?_, ?_⟩
                exact (by
                  change setSpineAt (j' + 1) b (.fieldCons ⟨_, h⟩ ⟨_, t⟩) = _
                  rw [setSpineAt_succ_fieldCons, ht1'.1])
                exact (by
                  change setSpineAt (i + 1) a (.fieldCons ⟨_, h⟩ t1') = _
                  rw [setSpineAt_succ_fieldCons, ht1'.2])
      | uninit => cases h1
      | int _ => cases h1
      | bool _ => cases h1
      | unit => cases h1
      | adt _ _ => cases h1
      | ref _ _ _ _ _ => cases h1

/-- If `setSpineAt idx v (.fieldCons h t) = some spine'`, then `spine'` is a
`.fieldCons` node so `getMirField` and `setMirField` delegate to `getSpineAt`
and `setSpineAt`. -/
theorem setSpineAt_is_fieldCons (idx : Nat) (h t v spine' : MirVal)
    (hSet : setSpineAt idx v (.fieldCons h t) = some spine') :
    getMirField idx spine' = getSpineAt idx spine' ∧
    (∀ v2, setMirField idx v2 spine' = setSpineAt idx v2 spine') := by
  cases idx with
  | zero =>
    rw [setSpineAt_zero_fieldCons] at hSet
    injection hSet with hEq
    subst hEq
    exact ⟨rfl, fun _ => rfl⟩
  | succ i =>
    rw [setSpineAt_succ_fieldCons] at hSet
    revert hSet
    cases setSpineAt i v t with
    | none =>
      intro hFalse
      cases hFalse
    | some t' =>
      intro hSet
      injection hSet with hEq
      subst hEq
      exact ⟨rfl, fun _ => rfl⟩

/-- A successful `setSpineAt` on a `.fieldCons` spine yields a `.fieldCons`
spine, on which `setMirField` at every index is `setSpineAt`. -/
theorem setSpineAt_fieldCons_setMirField (idx : Nat) (h t v spine' : MirVal)
    (hSet : setSpineAt idx v (.fieldCons h t) = some spine') :
    ∀ g w, setMirField g w spine' = setSpineAt g w spine' := by
  cases idx with
  | zero =>
    rw [setSpineAt_zero_fieldCons] at hSet
    injection hSet with hEq
    subst hEq
    exact fun _ _ => rfl
  | succ i =>
    rw [setSpineAt_succ_fieldCons] at hSet
    revert hSet
    cases setSpineAt i v t with
    | none =>
      intro hFalse
      cases hFalse
    | some t' =>
      intro hSet
      injection hSet with hEq
      subst hEq
      exact fun _ _ => rfl

/-- Updates of distinct fields of a `MirVal` aggregate commute. -/
theorem mir_setField_setField_comm (f g : FieldIdx) (s a b s1 s2 : MirVal)
    (hNe : f ≠ g) (h1 : setMirField f a s = some s1)
    (h2 : setMirField g b s1 = some s2) :
    Exists fun s1' =>
      setMirField g b s = some s1' ∧ setMirField f a s1' = some s2 := by
  cases s with
  | mk fs ts =>
    cases ts with
    | adt id inner =>
      change
        (match setSpineAt f a ⟨_, inner⟩ with
         | some inner' => some (MirVal.adt id inner')
         | none => none) = some s1 at h1
      revert h1
      cases hI1 : setSpineAt f a ⟨_, inner⟩ with
      | none =>
        intro hFalse
        cases hFalse
      | some inner1 =>
        intro h1
        injection h1 with hEq1
        subst hEq1
        change
          (match setSpineAt g b inner1 with
           | some inner' => some (MirVal.adt id inner')
           | none => none) = some s2 at h2
        revert h2
        cases hI2 : setSpineAt g b inner1 with
        | none =>
          intro hFalse
          cases hFalse
        | some inner2 =>
          intro h2
          injection h2 with hEq2
          subst hEq2
          cases setSpineAt_setSpineAt_comm f g ⟨_, inner⟩ a b inner1 inner2 hNe
              hI1 hI2 with
          | intro inner1' hI =>
            refine ⟨MirVal.adt id inner1', ?_, ?_⟩
            exact (by
              change
                (match setSpineAt g b ⟨_, inner⟩ with
                 | some inner' => some (MirVal.adt id inner')
                 | none => none) = _
              rw [hI.1])
            exact (by
              change
                (match setSpineAt f a inner1' with
                 | some inner' => some (MirVal.adt id inner')
                 | none => none) = _
              rw [hI.2])
    | fieldCons h t =>
      change setSpineAt f a (.fieldCons ⟨_, h⟩ ⟨_, t⟩) = some s1 at h1
      rw [setSpineAt_fieldCons_setMirField f ⟨_, h⟩ ⟨_, t⟩ a s1 h1 g b] at h2
      cases setSpineAt_setSpineAt_comm f g (.fieldCons ⟨_, h⟩ ⟨_, t⟩) a b s1 s2
          hNe h1 h2 with
      | intro s1' hS =>
        refine ⟨s1', hS.1, ?_⟩
        rw [setSpineAt_fieldCons_setMirField g ⟨_, h⟩ ⟨_, t⟩ b s1' hS.1 f a]
        exact hS.2
    | uninit => cases h1
    | int _ => cases h1
    | bool _ => cases h1
    | unit => cases h1
    | ref _ _ _ _ _ => cases h1

/-- Updating field `f` of a `MirVal` aggregate leaves every other field `g`
unchanged. -/
theorem mir_getField_setField_other (f g : FieldIdx) (s a s' : MirVal)
    (hNe : f ≠ g) (hPut : setMirField f a s = some s') :
    getMirField g s' = getMirField g s := by
  cases s with
  | mk fs ts =>
    cases ts with
    | adt id inner =>
      change
        (match setSpineAt f a ⟨_, inner⟩ with
         | some inner' => some (MirVal.adt id inner')
         | none => none) = some s' at hPut
      revert hPut
      cases hRec : setSpineAt f a ⟨_, inner⟩ with
      | none =>
        intro hFalse
        cases hFalse
      | some inner' =>
        intro hPut
        injection hPut with hEq
        subst hEq
        exact setSpineAt_getSpineAt_other f g ⟨_, inner⟩ a inner' hNe hRec
    | fieldCons h t =>
      change setSpineAt f a (.fieldCons ⟨_, h⟩ ⟨_, t⟩) = some s' at hPut
      -- `s'` is again a `.fieldCons` spine, on which `getMirField` is
      -- `getSpineAt`; exposing its constructor lets `hOther` close the goal.
      have hOther :=
        setSpineAt_getSpineAt_other f g (.fieldCons ⟨_, h⟩ ⟨_, t⟩) a s' hNe hPut
      cases f with
      | zero =>
        rw [setSpineAt_zero_fieldCons] at hPut
        injection hPut with hEq
        subst hEq
        exact hOther
      | succ i =>
        rw [setSpineAt_succ_fieldCons] at hPut
        revert hPut
        cases setSpineAt i a ⟨_, t⟩ with
        | none =>
          intro hFalse
          cases hFalse
        | some t' =>
          intro hPut
          injection hPut with hEq
          subst hEq
          exact hOther
    | uninit => cases hPut
    | int _ => cases hPut
    | bool _ => cases hPut
    | unit => cases hPut
    | ref _ _ _ _ _ => cases hPut

/-- Lens law `get_put` for `getMirField`/`setMirField`: writing back the field
just read leaves the aggregate unchanged. -/
theorem mir_getField_setField (f : FieldIdx) (s a : MirVal)
    (hGet : getMirField f s = some a) :
    setMirField f a s = some s := by
  cases s with
  | mk fs ts =>
    cases ts with
    | adt id inner =>
      change getSpineAt f ⟨_, inner⟩ = some a at hGet
      change
        (match setSpineAt f a ⟨_, inner⟩ with
         | some inner' => some (MirVal.adt id inner')
         | none => none) = some (MirVal.adt id ⟨_, inner⟩)
      rw [getSpineAt_setSpineAt f ⟨_, inner⟩ a hGet]
    | fieldCons h t =>
      exact getSpineAt_setSpineAt f (.fieldCons ⟨_, h⟩ ⟨_, t⟩) a hGet
    | uninit => cases hGet
    | int _ => cases hGet
    | bool _ => cases hGet
    | unit => cases hGet
    | ref _ _ _ _ _ => cases hGet

/-- Lens law `put_get` for `getMirField`/`setMirField`: reading a field just
written returns the written value. -/
theorem mir_setField_getField (f : FieldIdx) (s a s' : MirVal)
    (hPut : setMirField f a s = some s') :
    getMirField f s' = some a := by
  cases s with
  | mk fs ts =>
    cases ts with
    | adt id inner =>
      change
        (match setSpineAt f a ⟨_, inner⟩ with
         | some inner' => some (MirVal.adt id inner')
         | none => none) = some s' at hPut
      revert hPut
      cases hRec : setSpineAt f a ⟨_, inner⟩ with
      | none =>
        intro hFalse
        cases hFalse
      | some inner' =>
        intro hPut
        injection hPut with hEq
        subst hEq
        exact setSpineAt_getSpineAt f ⟨_, inner⟩ a inner' hRec
    | fieldCons h t =>
      change setSpineAt f a (.fieldCons ⟨_, h⟩ ⟨_, t⟩) = some s' at hPut
      have hFC := setSpineAt_is_fieldCons f ⟨_, h⟩ ⟨_, t⟩ a s' hPut
      rw [hFC.1]
      exact setSpineAt_getSpineAt f (.fieldCons ⟨_, h⟩ ⟨_, t⟩) a s' hPut
    | uninit => cases hPut
    | int _ => cases hPut
    | bool _ => cases hPut
    | unit => cases hPut
    | ref _ _ _ _ _ => cases hPut

/-- Lens law `put_put` for `setMirField`: two writes to one field equal the
second write alone. -/
theorem mir_setField_setField (f : FieldIdx) (s a1 a2 s1 : MirVal)
    (hPut1 : setMirField f a1 s = some s1) :
    setMirField f a2 s1 = setMirField f a2 s := by
  cases s with
  | mk fs ts =>
    cases ts with
    | adt id inner =>
      change
        (match setSpineAt f a1 ⟨_, inner⟩ with
         | some inner' => some (MirVal.adt id inner')
         | none => none) = some s1 at hPut1
      revert hPut1
      cases hRec : setSpineAt f a1 ⟨_, inner⟩ with
      | none =>
        intro hFalse
        cases hFalse
      | some inner' =>
        intro hPut1
        injection hPut1 with hEq
        subst hEq
        change
          (match setSpineAt f a2 inner' with
           | some inner2 => some (MirVal.adt id inner2)
           | none => none) =
          (match setSpineAt f a2 ⟨_, inner⟩ with
           | some inner2 => some (MirVal.adt id inner2)
           | none => none)
        rw [setSpineAt_setSpineAt f ⟨_, inner⟩ a1 a2 inner' hRec]
    | fieldCons h t =>
      change setSpineAt f a1 (.fieldCons ⟨_, h⟩ ⟨_, t⟩) = some s1 at hPut1
      have hFC := setSpineAt_is_fieldCons f ⟨_, h⟩ ⟨_, t⟩ a1 s1 hPut1
      rw [hFC.2 a2]
      exact setSpineAt_setSpineAt f (.fieldCons ⟨_, h⟩ ⟨_, t⟩) a1 a2 s1 hPut1
    | uninit => cases hPut1
    | int _ => cases hPut1
    | bool _ => cases hPut1
    | unit => cases hPut1
    | ref _ _ _ _ _ => cases hPut1

/-- Branch condition of a `MirVal` for `PureLift` (`ValAlgebra.asBool`): a
`bool` is itself, an integer is true iff it is nonzero (matching a `SwitchInt`
whose only branch is `0`), and every other value is treated as `false`.
Returning `none` would not reject such a value: `none` means a symbolic
condition, for which `PureLift` evaluates and joins both arms. The `false`
fallback gives `PureLift` a meaning for a malformed branch, but no MIR
execution inherits it: `mir_pure_lift_sound` concludes only about the MIR run
that its hypothesis `hSim` supplies, and in MIR `Trusted.stepTerminator`
faults on a non-scalar `SwitchInt` discriminant. -/
def mirAsBool (v : MirVal) : Option Bool :=
  match v with
  | ⟨_, .bool b⟩ => some b
  | ⟨_, .int n⟩ => some (n != 0)
  | _ => some false

/-- `mirValAlg.projectBranchVal` (the identity) satisfies its law for concrete
conditions. -/
theorem mir_projectBranchVal_concrete (cond : MirVal) (b _ : Bool) (v : MirVal)
    (_ : mirAsBool cond = some b) :
    v = v := rfl

/-- `mirValAlg.projectBranchVal` law for symbolic conditions, true branch;
vacuous because `mirAsBool` never returns `none`. -/
theorem mir_projectBranchVal_zip_true (cond vt vf : MirVal)
    (h : mirAsBool cond = none) :
    mirZipVal cond vt vf = vt := by
  cases cond with
  | mk fc tc => cases tc <;> cases h

/-- `mirValAlg.projectBranchVal` law for symbolic conditions, false branch;
vacuous because `mirAsBool` never returns `none`. -/
theorem mir_projectBranchVal_zip_false (cond vt vf : MirVal)
    (h : mirAsBool cond = none) :
    mirZipVal cond vt vf = vf := by
  cases cond with
  | mk fc tc => cases tc <;> cases h

/-- Handle decoding for `Trusted.MirVal`: only `.ref` leaves are handles. -/
def mirDecodeRef (v : MirVal) : Option (LoanId × SubPath) :=
  match v with
  | ⟨_, .ref _ _ ⟨lid⟩ path _⟩ => some (lid, path)
  | _ => none

/-- A value that decodes as a reference (`mirDecodeRef`) has no fields, so the
handle scan need not look inside it. -/
theorem mir_decodeRef_getField (f : FieldIdx) (v : MirVal)
    (r : LoanId × SubPath) (hDec : mirDecodeRef v = some r) :
    getMirField f v = none := by
  cases v with
  | mk fv tv =>
    cases tv with
    | ref _ _ _ _ _ => rfl
    | uninit => cases hDec
    | int _ => cases hDec
    | bool _ => cases hDec
    | unit => cases hDec
    | adt _ _ => cases hDec
    | fieldCons _ _ => cases hDec

/-- `mirAsBool` is total, so `mirZipVal` never builds a symbolic choice. -/
theorem mir_branchSplit_zipVal (cond vt vf : MirVal)
    (h : mirAsBool cond = none) :
    (none : Option (MirVal × MirVal × MirVal)) = some (cond, vt, vf) := by
  cases cond with
  | mk fc tc => cases tc <;> cases h

/-- True iff `v` is a `.fieldCons` node: the spine of an aggregate, or the rest
of one, whose head is a field (`getMirField`). -/
def mirIsSpineNode (v : MirVal) : Bool :=
  match v with
  | ⟨_, .fieldCons _ _⟩ => true
  | _ => false

/-- One step of `remapMirVal`: rename a reference to `oldLid` at the root of
`w` to `newLid`, and rename with `ih` the parts of `w` that are fields or
contain fields (the head of a `.fieldCons`, and the payload of an `.adt` or the
tail of a `.fieldCons` when it is a spine node). Other parts are kept. -/
def remapMirStep (oldLid newLid : LoanId) (ih : MirVal → MirVal)
    (w : MirVal) : MirVal :=
  match w with
  | ⟨_, .uninit⟩ => .uninit
  | ⟨_, .int n⟩ => .int n
  | ⟨_, .bool b⟩ => .bool b
  | ⟨_, .unit⟩ => .unit
  | ⟨_, .adt id inner⟩ =>
    .adt id (if mirIsSpineNode ⟨_, inner⟩ then ih ⟨_, inner⟩ else ⟨_, inner⟩)
  | ⟨_, .fieldCons h t⟩ =>
    .fieldCons (ih ⟨_, h⟩)
      (if mirIsSpineNode ⟨_, t⟩ then ih ⟨_, t⟩ else ⟨_, t⟩)
  | ⟨_, .ref isMut refGen loc path depth⟩ =>
    if loc.index == oldLid then .ref isMut refGen ⟨newLid⟩ path depth
    else .ref isMut refGen loc path depth

/-- `remapMirStep` nested `k` deep; parts of `v` deeper than `k` are left
unchanged. -/
def remapMirFuel (oldLid newLid : LoanId) (k : Nat) (v : MirVal) : MirVal :=
  @Nat.recCompiled (fun _ => MirVal → MirVal) (fun w => w)
    (fun _ ih w => remapMirStep oldLid newLid ih w) k v

/-- Rename loan `oldLid` to `newLid` in every reference inside `v` that
`PureLift` can observe (`ValAlgebra.remapRefInVal`), keeping each reference's
mutability, generation, path, and reborrow depth. `PureLift` observes a
reference leaf (`mirDecodeRef`) and the fields of aggregates (`getMirField`:
the elements of a `.fieldCons` spine, directly or under `.adt`). A component
outside a spine, such as the payload of `.adt 0 (.ref …)` or the tail of
`.fieldCons x (.ref …)`, is not a field, so `PureLift` treats it as opaque data
and it is kept unchanged, as the law `remapRefInVal_leaf` requires of a value
without fields; see `mirValAlg` for why no well-typed value has one. Leaves
have size `0`, so the fuel `v.fuel + 1` reaches every node of `v`
(`remapMirFuel_eq`). -/
def remapMirVal (oldLid newLid : LoanId) (v : MirVal) : MirVal :=
  remapMirFuel oldLid newLid (v.fuel + 1) v

theorem remapMirFuel_succ (oldLid newLid : LoanId) (k : Nat) (v : MirVal) :
    remapMirFuel oldLid newLid (k + 1) v =
      remapMirStep oldLid newLid (remapMirFuel oldLid newLid k) v :=
  rfl

/-- Any fuel above the size of a value renames it completely. -/
theorem remapMirFuel_eq (oldLid newLid : LoanId) :
    ∀ {n : Nat} (tr : MirValTree n) (k : Nat), n + 1 ≤ k →
      remapMirFuel oldLid newLid k ⟨n, tr⟩ =
        remapMirVal oldLid newLid ⟨n, tr⟩ := by
  intro n tr
  induction tr with
  | uninit =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ _ => rfl
  | int _ =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ _ => rfl
  | bool _ =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ _ => rfl
  | unit =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ _ => rfl
  | ref _ _ _ _ _ =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ _ => rfl
  | @adt f id inner ih =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ k' =>
      change MirVal.adt id
          (if mirIsSpineNode ⟨f, inner⟩ then
            remapMirFuel oldLid newLid k' ⟨f, inner⟩
          else ⟨f, inner⟩) =
        MirVal.adt id
          (if mirIsSpineNode ⟨f, inner⟩ then
            remapMirFuel oldLid newLid (f + 1) ⟨f, inner⟩
          else ⟨f, inner⟩)
      rw [ih k' (Nat.le_of_succ_le_succ hLe)]
      rfl
  | @fieldCons fh ft h t ihh iht =>
    intro k hLe
    cases k with
    | zero => nomatch hLe
    | succ k' =>
      have hSub : fh + ft + 1 ≤ k' := Nat.le_of_succ_le_succ hLe
      have hH : fh + 1 ≤ fh + ft + 1 :=
        Nat.succ_le_succ (Nat.le_add_right fh ft)
      have hT : ft + 1 ≤ fh + ft + 1 :=
        Nat.succ_le_succ (Nat.le_add_left ft fh)
      change MirVal.fieldCons (remapMirFuel oldLid newLid k' ⟨fh, h⟩)
          (if mirIsSpineNode ⟨ft, t⟩ then
            remapMirFuel oldLid newLid k' ⟨ft, t⟩
          else ⟨ft, t⟩) =
        MirVal.fieldCons (remapMirFuel oldLid newLid (fh + ft + 1) ⟨fh, h⟩)
          (if mirIsSpineNode ⟨ft, t⟩ then
            remapMirFuel oldLid newLid (fh + ft + 1) ⟨ft, t⟩
          else ⟨ft, t⟩)
      rw [ihh k' (Nat.le_trans hH hSub), iht k' (Nat.le_trans hT hSub),
        ihh _ hH, iht _ hT]

theorem remapMirVal_adt (oldLid newLid : LoanId) (id : Nat) (inner : MirVal) :
    remapMirVal oldLid newLid (.adt id inner) =
      .adt id
        (if mirIsSpineNode inner then remapMirVal oldLid newLid inner
         else inner) := by
  cases inner with
  | mk _ _ => rfl

theorem remapMirVal_fieldCons (oldLid newLid : LoanId) (h t : MirVal) :
    remapMirVal oldLid newLid (.fieldCons h t) =
      .fieldCons (remapMirVal oldLid newLid h)
        (if mirIsSpineNode t then remapMirVal oldLid newLid t else t) := by
  cases h with
  | mk fh th =>
    cases t with
    | mk ft tt =>
      change MirVal.fieldCons (remapMirFuel oldLid newLid (fh + ft + 1) ⟨fh, th⟩)
          (if mirIsSpineNode ⟨ft, tt⟩ then
            remapMirFuel oldLid newLid (fh + ft + 1) ⟨ft, tt⟩
          else ⟨ft, tt⟩) = _
      rw [remapMirFuel_eq oldLid newLid th _
          (Nat.succ_le_succ (Nat.le_add_right fh ft)),
        remapMirFuel_eq oldLid newLid tt _
          (Nat.succ_le_succ (Nat.le_add_left ft fh))]

theorem remapMirVal_ref (oldLid newLid : LoanId) (isMut : Bool) (refGen : Nat)
    (loc : Trusted.LocalId) (path : List Nat) (depth : Nat) :
    remapMirVal oldLid newLid (.ref isMut refGen loc path depth) =
      .ref isMut refGen (if loc.index == oldLid then ⟨newLid⟩ else loc) path
        depth := by
  change (if loc.index == oldLid then MirVal.ref isMut refGen ⟨newLid⟩ path depth
    else .ref isMut refGen loc path depth) = _
  cases loc.index == oldLid <;> rfl

/-- A value that is not a spine node has no spine elements. -/
theorem getSpineAt_of_not_spine (i : Nat) (s : MirVal)
    (h : mirIsSpineNode s = false) : getSpineAt i s = none := by
  cases s with
  | mk _ ts =>
    cases ts with
    | fieldCons _ _ => nomatch h
    | uninit => cases i <;> rfl
    | int _ => cases i <;> rfl
    | bool _ => cases i <;> rfl
    | unit => cases i <;> rfl
    | adt _ _ => cases i <;> rfl
    | ref _ _ _ _ _ => cases i <;> rfl

/-- Renaming commutes with taking a spine element. -/
theorem getSpineAt_remapMirVal (oldLid newLid : LoanId) (i : Nat) :
    ∀ (s : MirVal), getSpineAt i (remapMirVal oldLid newLid s) =
      (getSpineAt i s).map (remapMirVal oldLid newLid) := by
  induction i with
  | zero =>
    intro s
    cases s with
    | mk _ ts =>
      cases ts with
      | fieldCons h t =>
        change getSpineAt 0
            (remapMirVal oldLid newLid (.fieldCons ⟨_, h⟩ ⟨_, t⟩)) = _
        rw [remapMirVal_fieldCons]
        rfl
      | uninit => rfl
      | int _ => rfl
      | bool _ => rfl
      | unit => rfl
      | adt _ _ => rfl
      | ref isMut refGen loc path depth =>
        change getSpineAt 0
            (remapMirVal oldLid newLid (.ref isMut refGen loc path depth)) = _
        rw [remapMirVal_ref]
        rfl
  | succ i ih =>
    intro s
    cases s with
    | mk _ ts =>
      cases ts with
      | fieldCons h t =>
        change getSpineAt (i + 1)
            (remapMirVal oldLid newLid (.fieldCons ⟨_, h⟩ ⟨_, t⟩)) =
          (getSpineAt i ⟨_, t⟩).map (remapMirVal oldLid newLid)
        rw [remapMirVal_fieldCons, getSpineAt_succ_fieldCons]
        cases hSpine : mirIsSpineNode ⟨_, t⟩ with
        | true => exact ih ⟨_, t⟩
        | false =>
          change getSpineAt i ⟨_, t⟩ = _
          rw [getSpineAt_of_not_spine i _ hSpine]
          rfl
      | uninit => rfl
      | int _ => rfl
      | bool _ => rfl
      | unit => rfl
      | adt _ _ => rfl
      | ref isMut refGen loc path depth =>
        change getSpineAt (i + 1)
            (remapMirVal oldLid newLid (.ref isMut refGen loc path depth)) = _
        rw [remapMirVal_ref]
        rfl

theorem mir_decodeRef_remapRefInVal (oldLid newLid : LoanId) (v : MirVal) :
    mirDecodeRef (remapMirVal oldLid newLid v) =
      (mirDecodeRef v).map
        (fun r => (if r.1 == oldLid then newLid else r.1, r.2)) := by
  cases v with
  | mk _ tv =>
    cases tv with
    | uninit => rfl
    | int _ => rfl
    | bool _ => rfl
    | unit => rfl
    | adt _ _ => rfl
    | fieldCons _ _ => rfl
    | ref isMut refGen loc path depth =>
      cases loc with
      | mk idx =>
        change mirDecodeRef
            (if idx == oldLid then MirVal.ref isMut refGen ⟨newLid⟩ path depth
             else .ref isMut refGen ⟨idx⟩ path depth) =
          some (if idx == oldLid then newLid else idx, path)
        cases idx == oldLid <;> rfl

theorem mir_getField_remapRefInVal (oldLid newLid : LoanId) (f : FieldIdx)
    (v : MirVal) :
    getMirField f (remapMirVal oldLid newLid v) =
      (getMirField f v).map (remapMirVal oldLid newLid) := by
  cases v with
  | mk _ tv =>
    cases tv with
    | uninit => rfl
    | int _ => rfl
    | bool _ => rfl
    | unit => rfl
    | ref isMut refGen loc path depth =>
      change getMirField f
          (remapMirVal oldLid newLid (.ref isMut refGen loc path depth)) = _
      rw [remapMirVal_ref]
      rfl
    | adt id inner =>
      change getMirField f (remapMirVal oldLid newLid (.adt id ⟨_, inner⟩)) =
        (getSpineAt f ⟨_, inner⟩).map (remapMirVal oldLid newLid)
      rw [remapMirVal_adt]
      cases hSpine : mirIsSpineNode ⟨_, inner⟩ with
      | true =>
        change getSpineAt f (remapMirVal oldLid newLid ⟨_, inner⟩) = _
        exact getSpineAt_remapMirVal oldLid newLid f ⟨_, inner⟩
      | false =>
        change getSpineAt f ⟨_, inner⟩ = _
        rw [getSpineAt_of_not_spine f _ hSpine]
        rfl
    | fieldCons h t =>
      change getSpineAt f
          (remapMirVal oldLid newLid (.fieldCons ⟨_, h⟩ ⟨_, t⟩)) =
        (getSpineAt f (.fieldCons ⟨_, h⟩ ⟨_, t⟩)).map
          (remapMirVal oldLid newLid)
      exact getSpineAt_remapMirVal oldLid newLid f _

/-- Renaming leaves a value without a reference leaf or fields unchanged:
`remapMirVal` keeps the payload of an `.adt` that is not a spine. -/
theorem mir_remapRefInVal_leaf (oldLid newLid : LoanId) (v : MirVal)
    (hDec : mirDecodeRef v = none) (hFields : ∀ f, getMirField f v = none) :
    remapMirVal oldLid newLid v = v := by
  cases v with
  | mk _ tv =>
    cases tv with
    | uninit => rfl
    | int _ => rfl
    | bool _ => rfl
    | unit => rfl
    | ref _ _ _ _ _ => nomatch hDec
    | fieldCons _ _ => nomatch hFields 0
    | adt id inner =>
      cases inner with
      | fieldCons _ _ => nomatch hFields 0
      | uninit => rfl
      | int _ => rfl
      | bool _ => rfl
      | unit => rfl
      | adt _ _ => rfl
      | ref _ _ _ _ _ => rfl

/-- Instantiation of `PureLift.ValAlgebra` for `Trusted.MirVal`.

The fields of an aggregate are the elements of its `.unit`-terminated
`.fieldCons` spine, either directly (tuples) or under `.adt` (structs);
`getField` reaches nothing else. A value with a non-spine component, such as
`.adt 0 (.ref …)` or `.fieldCons x (.ref …)`, therefore hides that component
from `PureLift`'s handle scan (`handleFreeVal`), which walks fields only, and
handle renaming (`remapMirVal`) keeps it unchanged. Such values are not values
of any `MirTy`, so MIR entry typing rejects an argument that holds one
(`mir_non_spine_values_rejected_at_entry`), and only `.unit`-terminated spines
are meaningful here. -/
def mirValAlg : ValAlgebra MirVal where
  defaultVal := .unit
  asBool := mirAsBool
  zipVal := mirZipVal
  getField idx v := getMirField idx v
  getField_projectBranchVal _ _ _ _ _ h := h
  setField idx v child := setMirField idx child v
  getField_setField := mir_getField_setField
  setField_getField := mir_setField_getField
  setField_setField := mir_setField_setField
  getField_setField_other := mir_getField_setField_other
  setField_setField_comm f g s a b s1 s2 hNe h1 h2 :=
    mir_setField_setField_comm f g s a b s1 s2 hNe h1 h2
  encodeRef lid path := .ref true 0 ⟨lid⟩ path 0
  encodeSharedRef lid path := .ref false 0 ⟨lid⟩ path 0
  decodeRef := mirDecodeRef
  decodeRefIsShared v :=
    match v with
    | .ref false _ _ _ _ => true
    | _ => false
  decodeRef_encodeRef _ _ := rfl
  decodeRef_encodeSharedRef _ _ := rfl
  decodeRefIsShared_encodeSharedRef _ _ := rfl
  decodeRefIsShared_encodeRef _ _ := Or.inr rfl
  decodeRef_getField f v r h := mir_decodeRef_getField f v r h
  branchSplit _ := none
  decodeRef_branchSplit _ _ _ := rfl
  branchSplit_zipVal := mir_branchSplit_zipVal
  -- With no symbolic choices there are no conditions to correlate.
  sameCond _ _ := false
  sameCond_eq _ _ h := nomatch h
  remapRefInVal := remapMirVal
  decodeRef_remapRefInVal := mir_decodeRef_remapRefInVal
  getField_remapRefInVal := mir_getField_remapRefInVal
  branchSplit_remapRefInVal _ _ _ := rfl
  remapRefInVal_leaf oldLid newLid v hDec hFields _ :=
    mir_remapRefInVal_leaf oldLid newLid v hDec hFields
  projectBranchVal := fun _ _ v => v
  projectBranchVal_concrete := mir_projectBranchVal_concrete
  projectBranchVal_zip_true := mir_projectBranchVal_zip_true
  projectBranchVal_zip_false := mir_projectBranchVal_zip_false
  sizeBound v := v.fuel
  getField_lt_sizeBound := mir_getField_lt_sizeBound
  -- `.adt` tags and the tail of a `.fieldCons` spine are not fields, so no two
  -- `MirVal` aggregates are reported as field-wise mergeable; branch joins
  -- fall back to `mirZipVal` for whole aggregates.
  sameAggregateShape _ _ := false
  sameAggregateShape_ext _ _ hShape _ := nomatch hShape
  sameAggregateShape_setField _ _ _ _ _ hShape _ := nomatch hShape

/-- `fieldLens mirValAlg f` satisfies the three bidirectional lens laws
(`get_put`, `put_get`, and `put_put`) for every field index `f : FieldIdx`. -/
theorem mirFieldLens_lawful (f : FieldIdx) :
    LawfulLens MirVal MirVal (fieldLens mirValAlg f) :=
  fieldLens_lawful mirValAlg f

/-- Every nested sub-place path lens `subPathLens mirValAlg path` is lawful. -/
theorem mirSubPathLens_lawful (path : SubPath) :
    LawfulLens MirVal MirVal (subPathLens mirValAlg path) :=
  subPathLens_lawful mirValAlg path

/-! ## Operational Adapter for `Trusted.MirBody` and `Trusted.MirState` -/

/-- Structural check that `v` contains no `.uninit` leaves and every embedded
`.ref` points to a live slot whose generation matches `localGens` (matching
`Trusted.MirVal.isValidInState`, whose structural fold covers every nesting
depth). -/
def mirValValidInState (localGens : List Nat) (v : MirVal) : Bool :=
  v.isValidInState localGens

/-- Map a caller-owned referent place `(slotIdx, path)` back to its 0-based
`PureLift` root `(loanId, relPath)` in `callerPlaces`, matching the first entry
`(s, basePath)` where `s == slotIdx` and `basePath` is a prefix of `path`. -/
def findCallerPlaceLoanId (callerPlaces : List (Nat × SubPath))
    (slotIdx : Nat) (path : SubPath) : Option (LoanId × SubPath) :=
  (callerPlaces.foldr
    (fun (s, basePath) (ih : Nat → Option (LoanId × SubPath)) curIdx =>
      if s == slotIdx then
        match stripSubPathPrefix basePath path with
        | some relPath => some (curIdx, relPath)
        | none => ih (curIdx + 1)
      else
        ih (curIdx + 1))
    (fun _ => none))
    0

/-- Normalize any reference `.ref isMut refGen ⟨slotIdx⟩ path depth` inside `v`
by mapping any caller-owned referent place `(slotIdx, path)` matching an entry
in `callerPlaces` back to its `PureLift` root `(LoanId, relPath)` and
normalizing `refGen` and `reborrowDepth` to `0` so extracted references match
`mirValAlg.encodeRef` and `mirValAlg.encodeSharedRef`. -/
def normalizeReturnedPlaceRefsInVal
    (callerPlaces : List (Nat × SubPath)) (v : MirVal) : MirVal :=
  MirVal.fold
    .uninit
    (fun n => .int n)
    (fun b => .bool b)
    .unit
    (fun id _ ihInner => .adt id ihInner)
    (fun _ _ ihH ihT => .fieldCons ihH ihT)
    (fun isMut refGen loc path depth =>
      match findCallerPlaceLoanId callerPlaces loc.index path with
      | some (lid, relPath) => .ref isMut 0 ⟨lid⟩ relPath 0
      | none => .ref isMut refGen loc path depth)
    v

/-- True iff every reference inside `v` points into a caller place listed in
`callerPlaces`, so `normalizeReturnedPlaceRefsInVal` maps it to a root
`LoanId`. Extraction fails otherwise: an unresolved reference would keep its
MIR slot index, which could be mistaken for a `LoanId`. -/
def mirRefsResolve (callerPlaces : List (Nat × SubPath)) (v : MirVal) : Bool :=
  MirVal.fold
    true
    (fun _ => true)
    (fun _ => true)
    true
    (fun _ _ ihInner => ihInner)
    (fun _ _ ihH ihT => ihH && ihT)
    (fun _ _ loc path _ =>
      (findCallerPlaceLoanId callerPlaces loc.index path).isSome)
    v

/-- Extract the current values of mutable caller referent places `callerPlaces`
`(slotIdx, subPath)` in `mirSt.locals`. This place-level form is the general
extraction that the slot-level `extractCallerSlotVals` instantiates with empty
sub-paths; the soundness theorems use only whole-slot referents, because
`MirArgsMatch` requires reference parameters to borrow whole slots.
Extraction succeeds if every target place resolves to an allocated,
initialized sub-value valid in `mirSt.localGens` (no `.uninit` leaves and no
dangling or retired references), normalizing any embedded caller-place
references against `normPlaces` (which defaults to `callerPlaces` when
`refPlaces` is empty, or uses the full root-loan place table `refPlaces` when
shared reference parameters are also present).

Requiring validity keeps extraction faithful to the caller's memory:
`Trusted.MirReturn` records a reference that the callee retired as one that
names a slot that does not exist, which is never valid, so extraction fails
on it instead of reporting a target that the caller's pointer does not
have. -/
def extractCallerPlaceVals
    (callerPlaces : List (Nat × SubPath)) (mirSt : MirState)
    (refPlaces : List (Nat × SubPath) := []) :
    Option (List MirVal) :=
  let normPlaces := if refPlaces.isEmpty then callerPlaces else refPlaces
  callerPlaces.foldr
    (fun (slotIdx, subPath) acc =>
      match lookupAt mirSt.locals slotIdx, acc with
      | some (some rootVal), some vs =>
        match readFieldPath subPath rootVal with
        | some v =>
          if mirValValidInState mirSt.localGens v &&
              mirRefsResolve normPlaces v then
            some (normalizeReturnedPlaceRefsInVal normPlaces v :: vs)
          else
            none
        | none => none
      | _, _ => none)
    (some [])

/-- Extract the current values of mutable caller referent slots `callerSlots` in
`mirSt.locals` if every slot is allocated, initialized, and valid in
`mirSt.localGens` (no `.uninit` leaves and no dangling or retired references),
normalizing any embedded caller-slot references against `refSlots` (or
`callerSlots` when `refSlots` is empty). -/
def extractCallerSlotVals (callerSlots : List Nat)
    (mirSt : MirState) (refSlots : List Nat := []) : Option (List MirVal) :=
  extractCallerPlaceVals
    (callerSlots.map (fun s => (s, ([] : SubPath))))
    mirSt
    (refSlots.map (fun s => (s, ([] : SubPath))))

/-- Extract a `FuncOut MirVal` from a `Trusted.MirReturn` given the caller-owned
mutable-reference referent places `callerPlaces` `(slotIdx, subPath)` in
`ret.state.locals` (which populate `FuncOut.mutFinals`) and an optional full
root-loan referent place list `refPlaces` (including `ParamKind.sharedRef`
referent places in root `LoanId` order `0, 1, …`, defaulting to `callerPlaces`
when `refPlaces` is empty) used to normalize returned and written-back
references via `normalizeReturnedPlaceRefsInVal`. Extraction fails if a
returned or written-back reference points outside that table
(`mirRefsResolve`). -/
def extractMirPlaceFuncOut
    (callerPlaces : List (Nat × SubPath)) (ret : MirReturn)
    (refPlaces : List (Nat × SubPath) := []) :
    Option (FuncOut MirVal) :=
  let normPlaces := if refPlaces.isEmpty then callerPlaces else refPlaces
  match extractCallerPlaceVals callerPlaces ret.state refPlaces with
  | some wb =>
    if mirRefsResolve normPlaces ret.value then
      some ⟨normalizeReturnedPlaceRefsInVal normPlaces ret.value, wb⟩
    else
      none
  | none => none

/-- Extract a `FuncOut MirVal` from a `Trusted.MirReturn` given the indices of
the caller-owned mutable-reference referent slots `callerSlots` in
`ret.state.locals` (which populate `FuncOut.mutFinals`) and an optional full
root-loan referent slot list `refSlots` (including `ParamKind.sharedRef`
referent slots in root `LoanId` order `0, 1, …`, defaulting to `callerSlots`
when `refSlots` is empty) used to normalize returned and written-back
references. -/
def extractMirFuncOut (callerSlots : List Nat) (ret : MirReturn)
    (refSlots : List Nat := []) :
    Option (FuncOut MirVal) :=
  extractMirPlaceFuncOut
    (callerSlots.map (fun s => (s, ([] : SubPath))))
    ret
    (refSlots.map (fun s => (s, ([] : SubPath))))

/-- `MirRunsTo callerSlots body st fuel out refSlots` holds when running `body`
for at most `fuel` small steps from entry state `st` returns `ret`
(`runMirSteps … = .returned ret`) and `extractMirFuncOut callerSlots ret
refSlots` yields `some out`. -/
def MirRunsTo (callerSlots : List Nat) (body : MirBody)
    (st : MirState) (fuel : Nat) (out : FuncOut MirVal)
    (refSlots : List Nat := []) : Prop :=
  match runMirSteps body fuel st with
  | .returned ret => extractMirFuncOut callerSlots ret refSlots = some out
  | _ => False

/-- `MirLoopRunsTo callerSlots body st fuel out refSlots` holds when running
`stepMirLoop body fuel st` from an in-flight state `st` returns `ret`
(`.returned ret`) and `extractMirFuncOut callerSlots ret refSlots` yields
`some out`. -/
def MirLoopRunsTo (callerSlots : List Nat) (body : MirBody)
    (st : MirState) (fuel : Nat) (out : FuncOut MirVal)
    (refSlots : List Nat := []) : Prop :=
  match stepMirLoop body fuel st with
  | .returned ret => extractMirFuncOut callerSlots ret refSlots = some out
  | _ => False

/-- Initial entry-step reduction lemma for `MirRunsTo`: from an entry state
`st = ⟨locals, localGens, 0, 0⟩`, if `runMirSteps`'s admission and entry
checks followed by the first `stepMirCore` step (`if !bodyAdmissible body then
.fault else if !entryStateValid body st then .fault else stepMirCore body st`)
yield `.stepped st'` and `MirLoopRunsTo callerSlots body st' fuel out` holds,
then `MirRunsTo callerSlots body st (fuel + 1) out` holds.
`StepOutcome` has no rejection, so a failed admission or entry check, which
`runMirSteps` reports as `.rejected`, appears here as `.fault`. Only the
`.stepped` case is used, so the encoding loses nothing. -/
theorem mir_entry_stepped_runsTo (callerSlots : List Nat) (body : MirBody)
    (locals : List (Option MirVal)) (localGens : List Nat)
    (st' : MirState) (fuel : Nat) (out : FuncOut MirVal)
    (hStep :
      (if !bodyAdmissible body then
        StepOutcome.fault
      else if !entryStateValid body ⟨locals, localGens, 0, 0⟩ then
        StepOutcome.fault
      else
        stepMirCore body ⟨locals, localGens, 0, 0⟩) = .stepped st')
    (hRest : MirLoopRunsTo callerSlots body st' fuel out) :
    MirRunsTo callerSlots body ⟨locals, localGens, 0, 0⟩ (fuel + 1) out := by
  cases ha : bodyAdmissible body with
  | false =>
    rw [ha] at hStep
    exact StepOutcome.noConfusion hStep
  | true =>
    cases hv : entryStateValid body ⟨locals, localGens, 0, 0⟩ with
    | false =>
      rw [ha, hv] at hStep
      exact StepOutcome.noConfusion hStep
    | true =>
      rw [ha, hv] at hStep
      have hCore :
          stepMirCore body ⟨locals, localGens, 0, 0⟩ = .stepped st' :=
        hStep
      have hRun : runMirSteps body (fuel + 1) ⟨locals, localGens, 0, 0⟩ =
          stepMirLoop body (fuel + 1) ⟨locals, localGens, 0, 0⟩ := by
        unfold runMirSteps
        rw [ha, hv]
        rfl
      dsimp only [MirRunsTo]
      rw [hRun, stepMirLoop_succ, hCore]
      exact hRest

/-- Composable in-flight step reduction lemma for `MirLoopRunsTo`: if
`stepMirCore body st = .stepped st'` and `st'` reaches `out` in `fuel` steps,
then `st` reaches `out` in `fuel + 1` steps. -/
theorem mir_stepped_runsTo (callerSlots : List Nat) (body : MirBody)
    (st st' : MirState) (fuel : Nat) (out : FuncOut MirVal)
    (hStep : stepMirCore body st = .stepped st')
    (hRest : MirLoopRunsTo callerSlots body st' fuel out) :
    MirLoopRunsTo callerSlots body st (fuel + 1) out := by
  dsimp [MirLoopRunsTo]
  rw [stepMirLoop_succ, hStep]
  exact hRest

/-- Composable terminal-step lemma for `MirLoopRunsTo`: if `stepMirCore body st
= .returned ret` and `extractMirFuncOut callerSlots ret` yields `out`, then
`st` reaches `out` in `fuel + 1` steps. -/
theorem mir_returned_runsTo {fuel : Nat} (callerSlots : List Nat)
    (body : MirBody) (st : MirState) (ret : MirReturn) (out : FuncOut MirVal)
    (hStep : stepMirCore body st = .returned ret)
    (hExt : extractMirFuncOut callerSlots ret = some out) :
    MirLoopRunsTo callerSlots body st (fuel + 1) out := by
  dsimp [MirLoopRunsTo]
  rw [stepMirLoop_succ, hStep]
  exact hExt

/-- `MirExecutesTo callerSlots body refSlots m0 fuel mFinal` holds when the
machine state `m0` (an `M1MachState` from `Adapter.lean`: running from a MIR
state, returned with an output, or faulted) reaches `mFinal` within at most
`fuel` small steps of `Trusted.runMirSteps` (`fuel` is a bound, not an exact
count), extracting results with the root-loan referent slot table `refSlots`
(see `MirRunsTo`). A terminating run is labeled with the output that the MIR
extraction produced. -/
inductive MirExecutesTo (callerSlots : List Nat) (body : MirBody)
    (refSlots : List Nat) :
    M1MachState MirState MirVal → Nat → M1MachState MirState MirVal → Prop where
  | refl (m : M1MachState MirState MirVal) :
      MirExecutesTo callerSlots body refSlots m 0 m
  | trans {m1 m2 m3 : M1MachState MirState MirVal} {k1 k2 : Nat} :
      MirExecutesTo callerSlots body refSlots m1 k1 m2 →
      MirExecutesTo callerSlots body refSlots m2 k2 m3 →
      MirExecutesTo callerSlots body refSlots m1 (k1 + k2) m3
  | step_runs {st0 : MirState} {fuel : Nat} {out : FuncOut MirVal} :
      MirRunsTo callerSlots body st0 fuel out refSlots →
      MirExecutesTo callerSlots body refSlots (.running st0) fuel
        (.returned out)

/-- Entry relation connecting a `PureLift` `SymState MirVal` to a
`Trusted.MirState`: `mirSt` is at the entry point (`block == 0` and
`stmtIdx == 0`), every caller-owned referent slot in `callerSlots` holds a
valid, initialized `MirVal` in `mirSt`, and those referent values equal the
active root `&mut` loan values in `symSt`. It does not hold for any other
program point. References embedded in the referent values are normalized to root
`LoanId`s through the full root-loan referent slot table `refSlots` (shared
roots included; defaulting to `callerSlots` when empty). `PureLift`'s
`initFnState` rejects parameter values that carry a handle, so for a referent
that embeds a reference (as in `q: &T, p: &mut &T`) the relation cannot hold
at entry. -/
def MirStateRel (callerSlots : List Nat) (symSt : SymState MirVal)
    (mirSt : MirState) (refSlots : List Nat := []) : Prop :=
  match extractCallerSlotVals callerSlots mirSt refSlots with
  | some slotVals =>
    if mirSt.block == 0 && mirSt.stmtIdx == 0 then
      slotVals = collectRootMutVals symSt.loans
    else
      False
  | none => False

/-- The shape of a MIR argument value that `MirArgsMatch` constrains: a
top-level reference with its generation and reborrow depth erased (they
depend on the caller's history, not on the parameter), and any other value
unchanged. -/
def mirArgShape (v : MirVal) : MirVal :=
  match v with
  | ⟨_, .ref isMut _ loc path _⟩ => .ref isMut 0 loc path 0
  | _ => v

/-- The argument values `_1, _2, …` of an entry state's local list `args`
(already stripped of `_0`), shaped by `mirArgShape`; a dead slot becomes
`.uninit`. -/
def mirArgShapes (args : List (Option MirVal)) : List MirVal :=
  args.map (fun a =>
    match a with
    | some v => mirArgShape v
    | none => .uninit)

/-- The MIR argument values that `PureLift` parameters `params` denote, and the
caller slots of their `&mut` parameters in declaration order, given the root
`LoanId` referent slot table `rootSlots` (indexed from root `LoanId` `lid`).
A by-value parameter denotes its value; a reference parameter with root
`LoanId` `lid` denotes a whole-slot reference of its mutability to
`rootSlots[lid]`. The result is `none` when a reference parameter borrows a
sub-path (not modeled here), when `rootSlots` has no entry for some reference
parameter or has entries left over, or when a shared-reference parameter
occurs while `allowShared = false`. -/
def mirExpectedArgs (rootSlots : List Nat) (allowShared : Bool)
    (params : List (ParamInput MirVal)) (lid0 : Nat) :
    Option (List MirVal × List Nat) :=
  params.foldr
    (fun p (ih : Nat → Option (List MirVal × List Nat)) lid =>
      match p.mode with
      | .byVal =>
        match ih lid with
        | some (vals, mutSlots) => some (p.val :: vals, mutSlots)
        | none => none
      | .sharedRef _ path =>
        match allowShared, path, lookupAt rootSlots lid, ih (lid + 1) with
        | true, [], some s, some (vals, mutSlots) =>
          some (.ref false 0 ⟨s⟩ [] 0 :: vals, mutSlots)
        | _, _, _, _ => none
      | .mutRef _ path =>
        match path, lookupAt rootSlots lid, ih (lid + 1) with
        | [], some s, some (vals, mutSlots) =>
          some (.ref true 0 ⟨s⟩ [] 0 :: vals, s :: mutSlots)
        | _, _, _ => none)
    (fun lid => if rootSlots.length == lid then some ([], []) else none)
    lid0

/-- `MirArgsMatch body params callerSlots refSlots st0` ties the free slot
parameters of `mir_pure_lift_sound_refSlots` to the MIR entry arguments: `body`
takes one argument per parameter, each argument local `_(i+1)` of `st0` holds
the value that parameter `i` denotes (`mirExpectedArgs`, up to the generation
and reborrow depth of a reference), and `callerSlots` lists the referent slots
of the `&mut` parameters in declaration order. The root `LoanId` table is
`refSlots`, or `callerSlots` when `refSlots` is empty, in which case no
shared-reference parameter may occur (root `LoanId`s count shared parameters
too, so `callerSlots` alone cannot name them). Without this relation the slot
lists are unchecked, and a postcondition about the `PureLift` output could
transfer to the wrong MIR referent (for example, with `callerSlots` listed in
the opposite order from the arguments). -/
def MirArgsMatch (body : MirBody) (params : List (ParamInput MirVal))
    (callerSlots refSlots : List Nat) (st0 : MirState) : Prop :=
  params.length = body.argCount ∧
  mirExpectedArgs (if refSlots.isEmpty then callerSlots else refSlots)
      (!refSlots.isEmpty) params 0 =
    some (mirArgShapes ((st0.locals.drop 1).take params.length), callerSlots)

/-- `OperationalAdapter` connecting `Trusted.MirBody` and `Trusted.MirState`
to `PureLift` for parameters `params`, with root-loan referent slot table
`refSlots` (defaulting to `callerSlots` when empty).

`StateRel` is the entry relation. It holds only for the `PureLift` entry state
of `params` (`initFnState`), only when the MIR entry arguments match `params`
and `callerSlots` lists the `&mut` arguments' referents in order
(`MirArgsMatch`), and only when those `&mut` referents hold the root `&mut`
loan values (`MirStateRel`). So no instance of this adapter relates a setup
whose slot lists disagree with the arguments, and `pure_lift_sound` applied
to it reads `FuncOut.mutFinals` entry `i` from the referent of the `i`-th
`&mut` argument. Because `pure_lift_sound` requires `StateRel` for the
`PureLift` entry state of its own parameter list, that list must produce the
same entry state as `params`.

`StateRel` does not relate the referents of shared-reference parameters to
their `PureLift` values, and it does not require parameters with equal root
IDs to point to equal slots (MIR entry validation separately rejects aliasing
that involves a `&mut`). Neither is needed for the conclusion to describe the
machine: `FinalLoansRel` labels the machine with the output the MIR
extraction actually produced, and the simulation hypothesis (`hSim` of
`mir_pure_lift_sound`) requires that output to equal the `PureLift` output, so
a postcondition about `out` holds of what the machine returned. A mismatch in
these unrelated parts can only make `hSim` unprovable.

`FinalLoansRel out m` states that `m` returned `out` as extracted from the
MIR result (`extractMirFuncOut`), so a postcondition proved about `out`
transfers to the machine's result unchanged. `out` holds no references:
`evalFnValue` outputs contain no borrow handle in any field position
(`handleFreeOut`, which walks fields only; see `mirValAlg`), and MIR typing
excludes references in other positions, because the returned value must
conform to `_0`'s declared type (`Trusted.stepTerminator`, through
`checkLocalStoreTy`) and written-back caller slots are typed (entry
validation and `Trusted.assignPlace`). Functions that return references
(`evalFnReturningMut`) are not bridged. -/
def mirOperationalAdapter (callerSlots : List Nat)
    (body : MirBody) (params : List (ParamInput MirVal))
    (refSlots : List Nat := []) :
    OperationalAdapter (M1MachState MirState MirVal) MirVal where
  ExecutesTo := MirExecutesTo callerSlots body refSlots
  StateRel symSt m :=
    match m with
    | .running mirSt =>
      initFnState mirValAlg params = .ok symSt ∧
      MirArgsMatch body params callerSlots refSlots mirSt ∧
      MirStateRel callerSlots symSt mirSt refSlots
    | _ => False
  FinalLoansRel out m := m = .returned out
  exec_zero := MirExecutesTo.refl
  exec_trans := MirExecutesTo.trans

/-- Master soundness bridge specialized to `Trusted.MirBody` and
`Trusted.MirState` with an explicit root-loan referent slot table
`refSlots`. Given an entry state `st0` whose arguments match the parameters
(`hArgs`, `MirArgsMatch`) and whose referents relate to the `PureLift` entry
state (`hInit`, `MirStateRel … refSlots`), if the pure functional lifting
`evalFnValue mirValAlg params plan retExpr` satisfies `post` (`hSpec`), then
the machine returns an output `out` satisfying `post` (`FinalLoansRel`).
Reference parameters must borrow whole caller slots: `MirArgsMatch` (through
`mirExpectedArgs`) fails for a parameter whose path is not empty.

This theorem does not derive the MIR run. Hypothesis `hSim` assumes that
`Trusted.runMirSteps` terminates on `body` from `st0` and extracts the same
output as the lifting; each workload discharges it separately with its own
step-by-step `*_runsTo` lemma. The theorem packages those facts into the
`OperationalAdapter` form of `pure_lift_sound`. -/
theorem mir_pure_lift_sound_refSlots
    (callerSlots refSlots : List Nat)
    (body : MirBody)
    (params : List (ParamInput MirVal))
    (plan : FlowPlan MirVal)
    (retExpr : RvalOp MirVal)
    (post : FuncOut MirVal → Prop)
    (st0 : MirState)
    (hArgs : MirArgsMatch body params callerSlots refSlots st0)
    (hInit : Exists fun sym0 =>
      initFnState mirValAlg params = .ok sym0 ∧
      MirStateRel callerSlots sym0 st0 refSlots)
    (hSpec : HoldsFnSpec (evalFnValue mirValAlg params plan retExpr) post)
    (hSim : ∀ out, evalFnValue mirValAlg params plan retExpr = .ok out →
      Exists fun k => MirRunsTo callerSlots body st0 k out refSlots) :
    Exists fun k => Exists fun mFinal => Exists fun out =>
      (mirOperationalAdapter callerSlots body params refSlots).ExecutesTo
        (.running st0) k mFinal ∧
      (mirOperationalAdapter callerSlots body params refSlots).FinalLoansRel
        out mFinal ∧
      post out := by
  cases hInit with
  | intro sym0 hPair =>
    exact pure_lift_sound
      (mirOperationalAdapter callerSlots body params refSlots)
      mirValAlg params plan retExpr post (.running st0)
      ⟨sym0, hPair.1, And.intro hPair.1 (And.intro hArgs hPair.2)⟩ hSpec
      (by
        intro _ out _ _ hEval
        cases hSim out hEval with
        | intro k hk =>
          exact ⟨k, ⟨_, MirExecutesTo.step_runs hk, rfl⟩⟩)

/-- `mir_pure_lift_sound_refSlots` with the default root-loan referent slot
table (`callerSlots`), for functions without shared-reference parameters
(`MirArgsMatch` rejects them when `refSlots` is empty). As there, `hSim`
assumes the MIR run rather than deriving it. -/
theorem mir_pure_lift_sound
    (callerSlots : List Nat)
    (body : MirBody)
    (params : List (ParamInput MirVal))
    (plan : FlowPlan MirVal)
    (retExpr : RvalOp MirVal)
    (post : FuncOut MirVal → Prop)
    (st0 : MirState)
    (hArgs : MirArgsMatch body params callerSlots [] st0)
    (hInit : Exists fun sym0 =>
      initFnState mirValAlg params = .ok sym0 ∧
      MirStateRel callerSlots sym0 st0)
    (hSpec : HoldsFnSpec (evalFnValue mirValAlg params plan retExpr) post)
    (hSim : ∀ out, evalFnValue mirValAlg params plan retExpr = .ok out →
      Exists fun k => MirRunsTo callerSlots body st0 k out) :
    Exists fun k => Exists fun mFinal => Exists fun out =>
      (mirOperationalAdapter callerSlots body params).ExecutesTo
        (.running st0) k mFinal ∧
      (mirOperationalAdapter callerSlots body params).FinalLoansRel
        out mFinal ∧
      post out :=
  mir_pure_lift_sound_refSlots callerSlots [] body params plan retExpr post
    st0 hArgs hInit hSpec hSim

/-! ## End-to-End Verified `Trusted.MirBody` Workloads -/

/-- Modulus $2^{64}$ of 64-bit `MirTy.usize` arithmetic. -/
def mirUsizeModulus : Nat :=
  natPow2 64

/-- 64-bit `usize` wrapping addition modulo $2^{64}$. -/
def mirAddUsize (a b : Nat) : Nat :=
  Nat.mod (a + b) mirUsizeModulus

/-- $2^{64}$ is positive. -/
theorem mirUsizeModulus_pos : 0 < mirUsizeModulus := by
  decide

/-- The wrapped sum `mirAddUsize a b` always fits in 64 bits. -/
theorem decide_mirAddUsize_lt (a b : Nat) :
    decide (mirAddUsize a b < natPow2 64) = true :=
  decide_eq_true (Nat.mod_lt (a + b) mirUsizeModulus_pos)

/-- Pure 64-bit `usize` wrapping addition helper on `Trusted.MirVal`, matching
`Trusted.evalBinOp .add` on `MirTy.usize` operands. -/
def mirAddVal (v1 v2 : MirVal) : Option MirVal :=
  match v1, v2 with
  | ⟨_, .int a⟩, ⟨_, .int b⟩ => some (.int (mirAddUsize a b))
  | _, _ => none

/-- Pure 64-bit `usize` wrapping subtraction helper on `Trusted.MirVal`,
matching `Trusted.evalBinOp .sub` on `MirTy.usize` operands. -/
def mirSubUsizeVal (v1 v2 : MirVal) : Option MirVal :=
  match v1, v2 with
  | ⟨_, .int a⟩, ⟨_, .int b⟩ =>
    some (.int (Nat.mod (a + mirUsizeModulus - Nat.mod b mirUsizeModulus)
      mirUsizeModulus))
  | _, _ => none

/-- Pure integer `>` comparison helper on `Trusted.MirVal`. -/
def mirGtVal (v1 v2 : MirVal) : Option MirVal :=
  match v1, v2 with
  | ⟨_, .int a⟩, ⟨_, .int b⟩ => some (.bool (Nat.blt b a))
  | _, _ => none

/-! ### Workload M-1: Mutable Reference Borrow and Write (`add_assign`)

Rust equivalent:
```rust
fn add_assign(p: &mut usize, delta: usize) -> usize {
    let r = &mut *p;
    *r = *r + delta;
    *p
}
```
Compiled with `-C overflow-checks=off`, so `+` and `-` lower to the plain
wrapping `BinOp::Add` and `BinOp::Sub` (with overflow checks, MIR building
emits `AddWithOverflow` and an `Assert` terminator, which this subset omits).
MIR locals:
- `_0`: return `usize`
- `_1`: `p: &mut usize` (points to caller slot `4`)
- `_2`: `delta: usize`
- `_3`: `r: &mut usize`
- `_4`: caller-owned referent slot for `*p`
-/

/-- `Trusted.MirBody` for `add_assign(p: &mut usize, delta: usize) -> usize`. -/
def mirAddAssignBody : MirBody :=
  { argCount := 2
    localCount := 4
    ptrWidthBits := 64
    localTys := [.usize, .refMut .usize, .usize, .refMut .usize, .usize]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨3⟩
            , .assign ⟨⟨3⟩, []⟩ (.refMut ⟨⟨1⟩, [.deref]⟩)
            , .assign ⟨⟨3⟩, [.deref]⟩
                (.binaryOp .add (.copy ⟨⟨3⟩, [.deref]⟩) (.copy ⟨⟨2⟩, []⟩))
            , .storageDead ⟨3⟩
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, [.deref]⟩))
            ]
          terminator := .return_
        }
      ]
  }

/-- Initial `Trusted.MirState` for `mirAddAssignBody`. -/
def mirAddAssignInitState (x delta : Nat) : MirState :=
  { locals :=
      [ some .uninit
      , some (.ref true 0 ⟨4⟩ [])
      , some (.int delta)
      , none
      , some (.int x)
      ]
    localGens := [0, 0, 0, 0, 0]
    block := 0
    stmtIdx := 0
  }

/-- `PureLift` `FlowPlan` corresponding to `mirAddAssignBody`:
local `0` is `p: &mut usize`, local `1` is `delta: usize`, and local `2` is the
reborrow `r = &mut *p` (loan `1`). -/
def mirAddAssignPlan : FlowPlan MirVal :=
  .seq
    (.act (.borrow 2 .mutBorrow (.derefSub 0 [])))
    (.seq
      (.act (.assign (.derefSub 2 [])
        (.binary mirAddVal (.derefSub 2 []) (.localSub 1 []))))
      (.act (.endLoan 1)))

/-- State of `mirAddAssignBody` after its first small step (the entry step). -/
def mirAddAssignState1 (x delta : Nat) : MirState :=
  { locals :=
      [ some .uninit
      , some (.ref true 0 ⟨4⟩ [])
      , some (.int delta)
      , some .uninit
      , some (.int x)
      ]
    localGens := [0, 0, 0, 1, 0]
    block := 0
    stmtIdx := 1
  }

/-- State of `mirAddAssignBody` after its second small step. -/
def mirAddAssignState2 (x delta : Nat) : MirState :=
  { locals :=
      [ some .uninit
      , some (.ref true 0 ⟨4⟩ [])
      , some (.int delta)
      , some (.ref true 0 ⟨4⟩ [] 1)
      , some (.int x)
      ]
    localGens := [0, 0, 0, 1, 0]
    block := 0
    stmtIdx := 2
  }

/-- State of `mirAddAssignBody` after its third small step. -/
def mirAddAssignState3 (x delta : Nat) : MirState :=
  { locals :=
      [ some .uninit
      , some (.ref true 0 ⟨4⟩ [])
      , some (.int delta)
      , some (.ref true 0 ⟨4⟩ [] 1)
      , some (.int (mirAddUsize x delta))
      ]
    localGens := [0, 0, 0, 1, 0]
    block := 0
    stmtIdx := 3
  }

/-- State of `mirAddAssignBody` after its fourth small step. -/
def mirAddAssignState4 (x delta : Nat) : MirState :=
  { locals :=
      [ some .uninit
      , some (.ref true 0 ⟨4⟩ [])
      , some (.int delta)
      , none
      , some (.int (mirAddUsize x delta))
      ]
    localGens := [0, 0, 0, 2, 0]
    block := 0
    stmtIdx := 4
  }

/-- State of `mirAddAssignBody` after its fifth small step, just before
`return`. -/
def mirAddAssignState5 (x delta : Nat) : MirState :=
  { locals :=
      [ some (.int (mirAddUsize x delta))
      , some (.ref true 0 ⟨4⟩ [])
      , some (.int delta)
      , none
      , some (.int (mirAddUsize x delta))
      ]
    localGens := [0, 0, 0, 2, 0]
    block := 0
    stmtIdx := 5
  }

/-- Reduced form of the entry step of `Trusted.runMirSteps` (admission, entry
validation, then the first `stepMirCore` step) for a body with one `&mut`
argument (to caller slot `targetSlot`) and one by-value argument, with the
argument checks that depend on symbolic inputs abstracted as `b1` and `b2`. It
mirrors the trusted computation so that workload proofs can rewrite those
checks.
`StepOutcome` has no rejection, so a failed admission or entry check, which
`runMirSteps` reports as `.rejected`, appears here as `.fault`. -/
def mirEntryStep2 (targetSlot : Nat) (b1 b2 : Bool)
    (nextSt : MirState) : StepOutcome :=
  let step0 :
      Option (List EntryRef) :=
    match
      match b1 with
      | true =>
        some
          [((1, ([] : List Nat)), (true, false), ⟨targetSlot⟩,
            ([] : List Nat), 0)]
      | false => none
    with
    | some slotRefs => some ([] ++ slotRefs)
    | none => none
  let step1 :
      Option (List EntryRef) :=
    match step0 with
    | none => none
    | some prevRefs =>
      match b2 with
      | false => none
      | true => some (prevRefs ++ [])
  let excl : Bool :=
    match step1 with
    | some allRefs => entryRefListExclusive allRefs
    | none => false
  if !excl then .fault else .stepped nextSt

/-- Step-by-step execution of `mirAddAssignBody` from its entry state to its
return, for all 64-bit inputs. -/
theorem mirAddAssign_runsTo (x delta : Nat)
    (hx : x < natPow2 64) (hdelta : delta < natPow2 64) :
    MirRunsTo [4] mirAddAssignBody (mirAddAssignInitState x delta) 7
      ⟨.int (mirAddUsize x delta), [.int (mirAddUsize x delta)]⟩ := by
  have hxDec : decide (x < natPow2 64) = true := decide_eq_true hx
  have hdeltaDec : decide (delta < natPow2 64) = true := decide_eq_true hdelta
  refine mir_entry_stepped_runsTo [4] mirAddAssignBody
    (mirAddAssignInitState x delta).locals
    (mirAddAssignInitState x delta).localGens
    (mirAddAssignState1 x delta) 6
    ⟨.int (mirAddUsize x delta), [.int (mirAddUsize x delta)]⟩ ?_ ?_
  · change
      mirEntryStep2 4 (decide (x < natPow2 64)) (decide (delta < natPow2 64))
        (mirAddAssignState1 x delta) =
      StepOutcome.stepped (mirAddAssignState1 x delta)
    rw [hxDec, hdeltaDec]
    rfl
  · change MirLoopRunsTo [4] mirAddAssignBody (mirAddAssignState2 x delta)
      (4 + 1) ⟨.int (mirAddUsize x delta), [.int (mirAddUsize x delta)]⟩
    refine mir_stepped_runsTo [4] mirAddAssignBody
      (mirAddAssignState2 x delta) (mirAddAssignState3 x delta) 4
      ⟨.int (mirAddUsize x delta), [.int (mirAddUsize x delta)]⟩ ?_ ?_
    · change
        (match
          if decide (mirAddUsize x delta < natPow2 64) = true then
            some (mirAddAssignState3 x delta).locals
          else none with
         | some locals' =>
           StepOutcome.stepped ⟨locals', [0, 0, 0, 1, 0], 0, 3⟩
         | none => StepOutcome.fault) =
        StepOutcome.stepped (mirAddAssignState3 x delta)
      rw [decide_mirAddUsize_lt x delta]
      rfl
    · change MirLoopRunsTo [4] mirAddAssignBody (mirAddAssignState4 x delta)
        (2 + 1) ⟨.int (mirAddUsize x delta), [.int (mirAddUsize x delta)]⟩
      refine mir_stepped_runsTo [4] mirAddAssignBody
        (mirAddAssignState4 x delta) (mirAddAssignState5 x delta) 2
        ⟨.int (mirAddUsize x delta), [.int (mirAddUsize x delta)]⟩ ?_ ?_
      · change
          (match
            if decide (mirAddUsize x delta < natPow2 64) = true then
              some (mirAddAssignState5 x delta).locals
            else none with
           | some locals' =>
             StepOutcome.stepped ⟨locals', [0, 0, 0, 2, 0], 0, 5⟩
           | none => StepOutcome.fault) =
          StepOutcome.stepped (mirAddAssignState5 x delta)
        rw [decide_mirAddUsize_lt x delta]
        rfl
      · refine mir_returned_runsTo [4] mirAddAssignBody
          (mirAddAssignState5 x delta)
          ⟨.int (mirAddUsize x delta), mirAddAssignState5 x delta⟩
          ⟨.int (mirAddUsize x delta), [.int (mirAddUsize x delta)]⟩ ?_ rfl
        change
          (if decide (mirAddUsize x delta < natPow2 64) = true then
             StepOutcome.returned
               ⟨.int (mirAddUsize x delta), mirAddAssignState5 x delta⟩
           else StepOutcome.fault) =
          StepOutcome.returned
            ⟨.int (mirAddUsize x delta), mirAddAssignState5 x delta⟩
        rw [decide_mirAddUsize_lt x delta]
        rfl

/-- End-to-end verification of `mirAddAssignBody`: both `PureLift`
(`evalFnValue` + `mir_pure_lift_sound`) and `Trusted.runMirSteps` return
`.int (mirAddUsize x delta)` and write back `.int (mirAddUsize x delta)` to
caller slot `4` for all 64-bit `usize` inputs `x, delta < 2^64`. -/
theorem mir_add_assign_verified (x delta : Nat)
    (hx : x < natPow2 64) (hdelta : delta < natPow2 64) :
    (evalFnValue mirValAlg
        [⟨.mutRef 0 [], .int x⟩, ⟨.byVal, .int delta⟩]
        mirAddAssignPlan
        (.use (.derefSub 0 [])) =
      .ok ⟨.int (mirAddUsize x delta), [.int (mirAddUsize x delta)]⟩) ∧
    MirRunsTo [4] mirAddAssignBody (mirAddAssignInitState x delta) 7
      ⟨.int (mirAddUsize x delta), [.int (mirAddUsize x delta)]⟩ ∧
    (Exists fun k => Exists fun mFinal => Exists fun out =>
      (mirOperationalAdapter [4] mirAddAssignBody
        [⟨.mutRef 0 [], .int x⟩, ⟨.byVal, .int delta⟩]).ExecutesTo
        (.running (mirAddAssignInitState x delta)) k mFinal ∧
      (mirOperationalAdapter [4] mirAddAssignBody
        [⟨.mutRef 0 [], .int x⟩, ⟨.byVal, .int delta⟩]).FinalLoansRel
        out mFinal ∧
      out = ⟨.int (mirAddUsize x delta), [.int (mirAddUsize x delta)]⟩) := by
  refine ⟨rfl, mirAddAssign_runsTo x delta hx hdelta, ?_⟩
  exact mir_pure_lift_sound [4] mirAddAssignBody
    [⟨.mutRef 0 [], .int x⟩, ⟨.byVal, .int delta⟩]
    mirAddAssignPlan
    (.use (.derefSub 0 []))
    (fun out =>
      out = ⟨.int (mirAddUsize x delta), [.int (mirAddUsize x delta)]⟩)
    (mirAddAssignInitState x delta)
    ⟨rfl, rfl⟩
    ⟨_, ⟨rfl, rfl⟩⟩
    rfl
    (by
      intro out hEval
      change
        EvalOutcome.ok
          ⟨.int (mirAddUsize x delta), [.int (mirAddUsize x delta)]⟩ =
        EvalOutcome.ok out at hEval
      injection hEval with hOut
      subst hOut
      exact ⟨7, mirAddAssign_runsTo x delta hx hdelta⟩)

/-! ### Workload M-2: Disjoint Struct Field Borrows (`swap_fields`)

Rust equivalent:
```rust
struct Pair(usize, usize);
fn swap_fields(s: &mut Pair) -> usize {
    let p0 = &mut (*s).0;
    let p1 = &mut (*s).1;
    let tmp = *p0;
    *p0 = *p1;
    *p1 = tmp;
    (*s).0
}
```
-/

/-- Construct a 2-field `Pair(a, b)` struct `MirVal` (ADT `0`). -/
def mkMirPair (a b : Nat) : MirVal :=
  .adt 0 (.fieldCons (.int a) (.fieldCons (.int b) .unit))

/-- MIR type `Pair(usize, usize)` (ADT `0`). -/
def mirPairTy : MirTy :=
  .adt 0 [.usize, .usize]

/-- `Trusted.MirBody` for `swap_fields(s: &mut Pair) -> usize`, with the
caller-owned referent slot `5` (`*s`) typed as `Pair`. -/
def mirSwapFieldsBody : MirBody :=
  { argCount := 1
    localCount := 5
    ptrWidthBits := 64
    localTys :=
      [.usize, .refMut mirPairTy, .refMut .usize, .refMut .usize, .usize,
       mirPairTy]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨2⟩
            , .storageLive ⟨3⟩
            , .storageLive ⟨4⟩
            , .assign ⟨⟨2⟩, []⟩ (.refMut ⟨⟨1⟩, [.deref, .field 0]⟩)
            , .assign ⟨⟨3⟩, []⟩ (.refMut ⟨⟨1⟩, [.deref, .field 1]⟩)
            , .assign ⟨⟨4⟩, []⟩ (.use (.copy ⟨⟨2⟩, [.deref]⟩))
            , .assign ⟨⟨2⟩, [.deref]⟩ (.use (.copy ⟨⟨3⟩, [.deref]⟩))
            , .assign ⟨⟨3⟩, [.deref]⟩ (.use (.copy ⟨⟨4⟩, []⟩))
            , .storageDead ⟨4⟩
            , .storageDead ⟨3⟩
            , .storageDead ⟨2⟩
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, [.deref, .field 0]⟩))
            ]
          terminator := .return_
        }
      ]
  }

/-- Initial `Trusted.MirState` for `mirSwapFieldsBody` with `Pair(a, b)` in
caller slot `5`. -/
def mirSwapFieldsInitState (a b : Nat) : MirState :=
  { locals :=
      [ some .uninit
      , some (.ref true 0 ⟨5⟩ [])
      , none
      , none
      , none
      , some (mkMirPair a b)
      ]
    localGens := [0, 0, 0, 0, 0, 0]
    block := 0
    stmtIdx := 0
  }

/-- `PureLift` `FlowPlan` for `swap_fields`: local `0` is `s: &mut Pair`,
local `1` is `p0 = &mut (*s).0` (loan `1`), local `2` is `p1 = &mut (*s).1`
(loan `2`), and local `3` is `tmp = *p0`. -/
def mirSwapFieldsPlan : FlowPlan MirVal :=
  .seq
    (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.borrow 2 .mutBorrow (.derefSub 0 [1])))
      (.seq
        (.act (.assign (.localSub 3 []) (.use (.derefSub 1 []))))
        (.seq
          (.act (.assign (.derefSub 1 []) (.use (.derefSub 2 []))))
          (.seq
            (.act (.assign (.derefSub 2 []) (.use (.localSub 3 []))))
            (.seq
              (.act (.endLoan 2))
              (.act (.endLoan 1)))))))

/-- `PureLift` result of `mirSwapFieldsPlan` for any field values `a` and `b`.
-/
theorem mir_swap_fields_eval (a b : Nat) :
    evalFnValue mirValAlg
      [⟨.mutRef 0 [], mkMirPair a b⟩]
      mirSwapFieldsPlan
      (.use (.derefSub 0 [0])) =
    .ok ⟨.int b, [mkMirPair b a]⟩ := rfl

/-- `Trusted.MirState` of `mirSwapFieldsBody` before statement `idx`, with
locals `ls` and storage generations `gens`. -/
def mirSwapState (ls : List (Option MirVal)) (gens : List Nat) (idx : Nat) :
    MirState :=
  ⟨ls, gens, 0, idx⟩

/-- Locals of `mirSwapFieldsBody` while `p0`, `p1`, and `tmp` are live, with
`tmp = t` and caller slot `5` holding `pair`. -/
def mirSwapLiveLocals (t : Option MirVal) (pair : MirVal) :
    List (Option MirVal) :=
  [ some .uninit
  , some (.ref true 0 ⟨5⟩ [])
  , some (.ref true 0 ⟨5⟩ [0] 1)
  , some (.ref true 0 ⟨5⟩ [1] 1)
  , t
  , some pair
  ]

/-- Locals of `mirSwapFieldsBody` after `p0`, `p1`, and `tmp` are dead, with
return slot `ret` and caller slot `5` holding `pair`. -/
def mirSwapDoneLocals (ret : Option MirVal) (pair : MirVal) :
    List (Option MirVal) :=
  [ret, some (.ref true 0 ⟨5⟩ []), none, none, none, some pair]

/-- Entry-step outcome of `runMirSteps` on `mirSwapFieldsBody`, with the entry
pointee type check of `*s` abstracted as `tyOk`.
`StepOutcome` has no rejection, so a failed admission or entry check, which
`runMirSteps` reports as `.rejected`, appears here as `.fault`. -/
def mirSwapEntryStep (tyOk : Bool) (nextSt : MirState) : StepOutcome :=
  let step0 :
      Option (List EntryRef) :=
    match
      match tyOk with
      | true =>
        some
          [((1, ([] : List Nat)), (true, false), ⟨5⟩, ([] : List Nat), 0)]
      | false => none
    with
    | some slotRefs => some ([] ++ slotRefs)
    | none => none
  let excl : Bool :=
    match step0 with
    | some allRefs => entryRefListExclusive allRefs
    | none => false
  if !excl then .fault else .stepped nextSt

/-- `Pair(a, b)` conforms to `mirPairTy` when both fields fit in 64 bits. -/
theorem mir_pairTy_check (a b : Nat) (ha : decide (a < natPow2 64) = true)
    (hb : decide (b < natPow2 64) = true) (allowUninit : Bool)
    (tys : List MirTy) (ls : List (Option MirVal)) :
    checkValMatchesTy 64 mirPairTy (mkMirPair a b) allowUninit tys ls =
      true := by
  change (decide (a < natPow2 64) && (decide (b < natPow2 64) && true)) = true
  rw [ha, hb]
  rfl

/-- `.int a` conforms to 64-bit `usize` when `a < 2^64`. -/
theorem mir_usize_check (a : Nat) (ha : decide (a < natPow2 64) = true)
    (tys : List MirTy) (ls : List (Option MirVal)) :
    checkValMatchesTy 64 .usize (.int a) false tys ls = true := ha

/-- Step-by-step execution of `mirSwapFieldsBody` from its entry state to its
return, for all 64-bit field values. -/
theorem mir_swap_fields_runs (a b : Nat)
    (ha : a < natPow2 64) (hb : b < natPow2 64) :
    MirRunsTo [5] mirSwapFieldsBody (mirSwapFieldsInitState a b) 14
      ⟨.int b, [mkMirPair b a]⟩ := by
  have haDec : decide (a < natPow2 64) = true := decide_eq_true ha
  have hbDec : decide (b < natPow2 64) = true := decide_eq_true hb
  refine mir_entry_stepped_runsTo [5] mirSwapFieldsBody
    (mirSwapFieldsInitState a b).locals
    (mirSwapFieldsInitState a b).localGens
    (mirSwapState
      [some .uninit, some (.ref true 0 ⟨5⟩ []), some .uninit, none, none,
       some (mkMirPair a b)]
      [0, 0, 1, 0, 0, 0] 1) 13
    ⟨.int b, [mkMirPair b a]⟩ ?_ ?_
  · change mirSwapEntryStep
      (checkValMatchesTy 64 mirPairTy (mkMirPair a b) false
        mirSwapFieldsBody.localTys (mirSwapFieldsInitState a b).locals)
      (mirSwapState
        [some .uninit, some (.ref true 0 ⟨5⟩ []), some .uninit, none, none,
         some (mkMirPair a b)]
        [0, 0, 1, 0, 0, 0] 1) = _
    rw [mir_pairTy_check a b haDec hbDec]
    rfl
  -- `StorageLive` of `_3` and `_4` and both borrows are value-independent.
  change MirLoopRunsTo [5] mirSwapFieldsBody
    (mirSwapState (mirSwapLiveLocals (some .uninit) (mkMirPair a b))
      [0, 0, 1, 1, 1, 0] 5)
    (8 + 1) ⟨.int b, [mkMirPair b a]⟩
  -- `_4 = copy (*_2)` stores `a` into `_4 : usize`.
  refine mir_stepped_runsTo [5] mirSwapFieldsBody _
    (mirSwapState (mirSwapLiveLocals (some (.int a)) (mkMirPair a b))
      [0, 0, 1, 1, 1, 0] 6) 8 _ ?_ ?_
  · change
      (match
        if checkValMatchesTy 64 .usize (.int a) false _ _ = true then
          some (mirSwapLiveLocals (some (.int a)) (mkMirPair a b))
        else none with
       | some locals' =>
         StepOutcome.stepped ⟨locals', [0, 0, 1, 1, 1, 0], 0, 6⟩
       | none => StepOutcome.fault) = _
    rw [mir_usize_check a haDec]
    rfl
  -- `(*_2) = copy (*_3)` stores `b` into field `0` of `*s`.
  refine mir_stepped_runsTo [5] mirSwapFieldsBody _
    (mirSwapState (mirSwapLiveLocals (some (.int a)) (mkMirPair b b))
      [0, 0, 1, 1, 1, 0] 7) 7 _ ?_ ?_
  · change
      (match
        if (!checkValMatchesTy 64 .usize (.int b) false
              mirSwapFieldsBody.localTys
              (mirSwapLiveLocals (some (.int a)) (mkMirPair a b))) = true then
          none
        else
          some (mirSwapLiveLocals (some (.int a)) (mkMirPair b b)) with
       | some locals' =>
         StepOutcome.stepped ⟨locals', [0, 0, 1, 1, 1, 0], 0, 7⟩
       | none => StepOutcome.fault) = _
    rw [mir_usize_check b hbDec]
    rfl
  -- `(*_3) = copy _4` stores `a` into field `1` of `*s`.
  refine mir_stepped_runsTo [5] mirSwapFieldsBody _
    (mirSwapState (mirSwapLiveLocals (some (.int a)) (mkMirPair b a))
      [0, 0, 1, 1, 1, 0] 8) 6 _ ?_ ?_
  · change
      (match
        if (!checkValMatchesTy 64 .usize (.int a) false
              mirSwapFieldsBody.localTys
              (mirSwapLiveLocals (some (.int a)) (mkMirPair b b))) = true then
          none
        else
          some (mirSwapLiveLocals (some (.int a)) (mkMirPair b a)) with
       | some locals' =>
         StepOutcome.stepped ⟨locals', [0, 0, 1, 1, 1, 0], 0, 8⟩
       | none => StepOutcome.fault) = _
    rw [mir_usize_check a haDec]
    rfl
  -- The three `StorageDead`s are value-independent.
  change MirLoopRunsTo [5] mirSwapFieldsBody
    (mirSwapState (mirSwapDoneLocals (some .uninit) (mkMirPair b a))
      [0, 0, 2, 2, 2, 0] 11)
    (2 + 1) ⟨.int b, [mkMirPair b a]⟩
  -- `_0 = copy ((*_1).0)` stores `b` into `_0 : usize`.
  refine mir_stepped_runsTo [5] mirSwapFieldsBody _
    (mirSwapState (mirSwapDoneLocals (some (.int b)) (mkMirPair b a))
      [0, 0, 2, 2, 2, 0] 12) 2 _ ?_ ?_
  · change
      (match
        if checkValMatchesTy 64 .usize (.int b) false _ _ = true then
          some (mirSwapDoneLocals (some (.int b)) (mkMirPair b a))
        else none with
       | some locals' =>
         StepOutcome.stepped ⟨locals', [0, 0, 2, 2, 2, 0], 0, 12⟩
       | none => StepOutcome.fault) = _
    rw [mir_usize_check b hbDec]
    rfl
  -- `return` checks `_0 : usize`.
  refine mir_returned_runsTo [5] mirSwapFieldsBody _
    ⟨.int b,
     mirSwapState (mirSwapDoneLocals (some (.int b)) (mkMirPair b a))
       [0, 0, 2, 2, 2, 0] 12⟩
    _ ?_ rfl
  change
    (if checkValMatchesTy 64 .usize (.int b) false mirSwapFieldsBody.localTys
          (mirSwapDoneLocals (some (.int b)) (mkMirPair b a)) = true then
       StepOutcome.returned
         ⟨.int b,
          mirSwapState (mirSwapDoneLocals (some (.int b)) (mkMirPair b a))
            [0, 0, 2, 2, 2, 0] 12⟩
     else StepOutcome.fault) = _
  rw [mir_usize_check b hbDec]
  rfl

/-- End-to-end verification of `mirSwapFieldsBody`: both `PureLift` and
`Trusted.runMirSteps` swap `Pair(a, b)` into `Pair(b, a)` via simultaneous
disjoint sub-place borrows (`[0]` and `[1]`) and return `.int b` for all
64-bit `usize` fields `a, b < 2^64`. -/
theorem mir_swap_fields_verified (a b : Nat)
    (ha : a < natPow2 64) (hb : b < natPow2 64) :
    (evalFnValue mirValAlg
        [⟨.mutRef 0 [], mkMirPair a b⟩]
        mirSwapFieldsPlan
        (.use (.derefSub 0 [0])) =
      .ok ⟨.int b, [mkMirPair b a]⟩) ∧
    MirRunsTo [5] mirSwapFieldsBody (mirSwapFieldsInitState a b) 14
      ⟨.int b, [mkMirPair b a]⟩ ∧
    (Exists fun k => Exists fun mFinal => Exists fun out =>
      (mirOperationalAdapter [5] mirSwapFieldsBody
        [⟨.mutRef 0 [], mkMirPair a b⟩]).ExecutesTo
        (.running (mirSwapFieldsInitState a b)) k mFinal ∧
      (mirOperationalAdapter [5] mirSwapFieldsBody
        [⟨.mutRef 0 [], mkMirPair a b⟩]).FinalLoansRel out mFinal ∧
      out = ⟨.int b, [mkMirPair b a]⟩) := by
  refine ⟨mir_swap_fields_eval a b, mir_swap_fields_runs a b ha hb, ?_⟩
  exact mir_pure_lift_sound [5] mirSwapFieldsBody
    [⟨.mutRef 0 [], mkMirPair a b⟩]
    mirSwapFieldsPlan
    (.use (.derefSub 0 [0]))
    (fun out => out = ⟨.int b, [mkMirPair b a]⟩)
    (mirSwapFieldsInitState a b)
    ⟨rfl, rfl⟩
    ⟨_, ⟨rfl, rfl⟩⟩
    (by
      rw [mir_swap_fields_eval a b]
      rfl)
    (by
      intro out hEval
      rw [mir_swap_fields_eval a b] at hEval
      injection hEval with hOut
      subst hOut
      exact ⟨14, mir_swap_fields_runs a b ha hb⟩)

/-! ### Workload M-3: Multi-Block Conditional Diamond Reborrow (`select_add`)

Rust equivalent:
```rust
fn select_add(flag: bool, x: &mut usize, y: &mut usize, v: usize) -> usize {
    let r = if flag { &mut *x } else { &mut *y };
    *r = *r + v;
    *r
}
```
Compiled with `-C overflow-checks=off`, so `+` and `-` lower to the plain
wrapping `BinOp::Add` and `BinOp::Sub` (with overflow checks, MIR building
emits `AddWithOverflow` and an `Assert` terminator, which this subset omits).
Multi-block MIR CFG:
- `bb0`: `StorageLive(_5); SwitchInt(_1)` (`0 -> bb2`, `otherwise -> bb1`)
- `bb1`: `_5 = &mut (*_2); goto -> bb3`
- `bb2`: `_5 = &mut (*_3); goto -> bb3`
- `bb3`: `(*_5) = (*_5) + _4; _0 = (*_5); StorageDead(_5); return`
Caller-owned referent slots: `6` (`*x`) and `7` (`*y`).
-/

/-- 4-block `Trusted.MirBody` for `select_add`. -/
def mirSelectAddBody : MirBody :=
  { argCount := 4
    localCount := 6
    ptrWidthBits := 64
    localTys :=
      [ .usize
      , .bool
      , .refMut .usize
      , .refMut .usize
      , .usize
      , .refMut .usize
      , .usize
      , .usize
      ]
    blocks :=
      [ -- bb0: branch on `_1` (`flag`)
        { stmts := [.storageLive ⟨5⟩]
          terminator :=
            .switchInt (.copy ⟨⟨1⟩, []⟩)
              { branches := [⟨0, ⟨2⟩⟩], otherwise := ⟨1⟩ }
        }
      , -- bb1 (`flag = true`): `_5 = &mut (*_2); goto bb3`
        { stmts := [.assign ⟨⟨5⟩, []⟩ (.refMut ⟨⟨2⟩, [.deref]⟩)]
          terminator := .goto ⟨3⟩
        }
      , -- bb2 (`flag = false`): `_5 = &mut (*_3); goto bb3`
        { stmts := [.assign ⟨⟨5⟩, []⟩ (.refMut ⟨⟨3⟩, [.deref]⟩)]
          terminator := .goto ⟨3⟩
        }
      , -- bb3 (join): `(*_5) = (*_5) + _4; _0 = (*_5); StorageDead(_5); return`
        { stmts :=
            [ .assign ⟨⟨5⟩, [.deref]⟩
                (.binaryOp .add (.copy ⟨⟨5⟩, [.deref]⟩) (.copy ⟨⟨4⟩, []⟩))
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨5⟩, [.deref]⟩))
            , .storageDead ⟨5⟩
            ]
          terminator := .return_
        }
      ]
  }

/-- Initial `Trusted.MirState` for `mirSelectAddBody`. -/
def mirSelectAddInitState (flag : Bool) (x y v : Nat) : MirState :=
  { locals :=
      [ some .uninit
      , some (.bool flag)
      , some (.ref true 0 ⟨6⟩ [])
      , some (.ref true 0 ⟨7⟩ [])
      , some (.int v)
      , none
      , some (.int x)
      , some (.int y)
      ]
    localGens := [0, 0, 0, 0, 0, 0, 0, 0]
    block := 0
    stmtIdx := 0
  }

/-- `PureLift` `FlowPlan` for `select_add`, using `.branchExplicitJoin` with
`[(2, 2)]` for the merge at `bb3`. Every `MirVal` condition is concrete
(`mirAsBool` never returns `none`), so `PureLift` runs only the selected arm;
this workload does not exercise the symbolic join (`joinSymState`,
`BackTarget.choice`). -/
def mirSelectAddPlan : FlowPlan MirVal :=
  .seq
    (.branchExplicitJoin (.use (.localSub 0 []))
      (.act (.borrow 4 .mutBorrow (.derefSub 1 [])))
      (.act (.borrow 4 .mutBorrow (.derefSub 2 [])))
      [(2, 2)])
    (.seq
      (.act (.assign (.derefSub 4 [])
        (.binary mirAddVal (.derefSub 4 []) (.localSub 3 []))))
      (.seq
        (.act (.assign (.localSub 5 []) (.use (.derefSub 4 []))))
        (.act (.endLoan 2))))

/-- State of `mirSelectAddBody` after its entry step. -/
def mirSelectAddState1 (flag : Bool) (x y v : Nat) : MirState :=
  { locals :=
      [ some .uninit
      , some (.bool flag)
      , some (.ref true 0 ⟨6⟩ [])
      , some (.ref true 0 ⟨7⟩ [])
      , some (.int v)
      , some .uninit
      , some (.int x)
      , some (.int y)
      ]
    localGens := [0, 0, 0, 0, 0, 1, 0, 0]
    block := 0
    stmtIdx := 1
  }

/-- State of `mirSelectAddBody` with `flag = true` after its fourth small step.
-/
def mirSelectAddStateTrue4 (x y v : Nat) : MirState :=
  { locals :=
      [ some .uninit
      , some (.bool true)
      , some (.ref true 0 ⟨6⟩ [])
      , some (.ref true 0 ⟨7⟩ [])
      , some (.int v)
      , some (.ref true 0 ⟨6⟩ [] 1)
      , some (.int x)
      , some (.int y)
      ]
    localGens := [0, 0, 0, 0, 0, 1, 0, 0]
    block := 3
    stmtIdx := 0
  }

/-- State of `mirSelectAddBody` with `flag = true` after its fifth small step.
-/
def mirSelectAddStateTrue5 (x y v : Nat) : MirState :=
  { locals :=
      [ some .uninit
      , some (.bool true)
      , some (.ref true 0 ⟨6⟩ [])
      , some (.ref true 0 ⟨7⟩ [])
      , some (.int v)
      , some (.ref true 0 ⟨6⟩ [] 1)
      , some (.int (mirAddUsize x v))
      , some (.int y)
      ]
    localGens := [0, 0, 0, 0, 0, 1, 0, 0]
    block := 3
    stmtIdx := 1
  }

/-- State of `mirSelectAddBody` with `flag = true` after its sixth small step.
-/
def mirSelectAddStateTrue6 (x y v : Nat) : MirState :=
  { locals :=
      [ some (.int (mirAddUsize x v))
      , some (.bool true)
      , some (.ref true 0 ⟨6⟩ [])
      , some (.ref true 0 ⟨7⟩ [])
      , some (.int v)
      , some (.ref true 0 ⟨6⟩ [] 1)
      , some (.int (mirAddUsize x v))
      , some (.int y)
      ]
    localGens := [0, 0, 0, 0, 0, 1, 0, 0]
    block := 3
    stmtIdx := 2
  }

/-- State of `mirSelectAddBody` with `flag = false` after its fourth small step.
-/
def mirSelectAddStateFalse4 (x y v : Nat) : MirState :=
  { locals :=
      [ some .uninit
      , some (.bool false)
      , some (.ref true 0 ⟨6⟩ [])
      , some (.ref true 0 ⟨7⟩ [])
      , some (.int v)
      , some (.ref true 0 ⟨7⟩ [] 1)
      , some (.int x)
      , some (.int y)
      ]
    localGens := [0, 0, 0, 0, 0, 1, 0, 0]
    block := 3
    stmtIdx := 0
  }

/-- State of `mirSelectAddBody` with `flag = false` after its fifth small step.
-/
def mirSelectAddStateFalse5 (x y v : Nat) : MirState :=
  { locals :=
      [ some .uninit
      , some (.bool false)
      , some (.ref true 0 ⟨6⟩ [])
      , some (.ref true 0 ⟨7⟩ [])
      , some (.int v)
      , some (.ref true 0 ⟨7⟩ [] 1)
      , some (.int x)
      , some (.int (mirAddUsize y v))
      ]
    localGens := [0, 0, 0, 0, 0, 1, 0, 0]
    block := 3
    stmtIdx := 1
  }

/-- State of `mirSelectAddBody` with `flag = false` after its sixth small step.
-/
def mirSelectAddStateFalse6 (x y v : Nat) : MirState :=
  { locals :=
      [ some (.int (mirAddUsize y v))
      , some (.bool false)
      , some (.ref true 0 ⟨6⟩ [])
      , some (.ref true 0 ⟨7⟩ [])
      , some (.int v)
      , some (.ref true 0 ⟨7⟩ [] 1)
      , some (.int x)
      , some (.int (mirAddUsize y v))
      ]
    localGens := [0, 0, 0, 0, 0, 1, 0, 0]
    block := 3
    stmtIdx := 2
  }

/-- State of `mirSelectAddBody` with `flag = true` just before `return`. -/
def mirSelectAddStateTrue7 (x y v : Nat) : MirState :=
  { locals :=
      [ some (.int (mirAddUsize x v))
      , some (.bool true)
      , some (.ref true 0 ⟨6⟩ [])
      , some (.ref true 0 ⟨7⟩ [])
      , some (.int v)
      , none
      , some (.int (mirAddUsize x v))
      , some (.int y)
      ]
    localGens := [0, 0, 0, 0, 0, 2, 0, 0]
    block := 3
    stmtIdx := 3
  }

/-- State of `mirSelectAddBody` with `flag = false` just before `return`. -/
def mirSelectAddStateFalse7 (x y v : Nat) : MirState :=
  { locals :=
      [ some (.int (mirAddUsize y v))
      , some (.bool false)
      , some (.ref true 0 ⟨6⟩ [])
      , some (.ref true 0 ⟨7⟩ [])
      , some (.int v)
      , none
      , some (.int x)
      , some (.int (mirAddUsize y v))
      ]
    localGens := [0, 0, 0, 0, 0, 2, 0, 0]
    block := 3
    stmtIdx := 3
  }

/-- Reduced form of the entry step of `Trusted.runMirSteps` for
`mirSelectAddBody`, with the argument checks that depend on symbolic inputs
abstracted as `b1`, `b2`, and `b3`. It mirrors the trusted computation so that
workload proofs can rewrite those checks.
`StepOutcome` has no rejection, so a failed admission or entry check, which
`runMirSteps` reports as `.rejected`, appears here as `.fault`. -/
def mirEntryStep4 (b1 b2 b3 : Bool) (nextSt : MirState) : StepOutcome :=
  let step0 :
      Option (List EntryRef) :=
    some []
  let step1 :
      Option (List EntryRef) :=
    match step0 with
    | none => none
    | some prevRefs =>
      match
        match b1 with
        | true =>
          some
            [((2, ([] : List Nat)), (true, false), ⟨6⟩, ([] : List Nat), 0)]
        | false => none
      with
      | some slotRefs => some (prevRefs ++ slotRefs)
      | none => none
  let step2 :
      Option (List EntryRef) :=
    match step1 with
    | none => none
    | some prevRefs =>
      match
        match b2 with
        | true =>
          some
            [((3, ([] : List Nat)), (true, false), ⟨7⟩, ([] : List Nat), 0)]
        | false => none
      with
      | some slotRefs => some (prevRefs ++ slotRefs)
      | none => none
  let step3 :
      Option (List EntryRef) :=
    match step2 with
    | none => none
    | some prevRefs =>
      match b3 with
      | false => none
      | true => some (prevRefs ++ [])
  let excl : Bool :=
    match step3 with
    | some allRefs => entryRefListExclusive allRefs
    | none => false
  if !excl then .fault else .stepped nextSt

/-- Step-by-step execution of `mirSelectAddBody` from its entry state to its
return, for both values of `flag` and all 64-bit inputs. -/
theorem mirSelectAdd_runsTo (flag : Bool) (x y v : Nat)
    (hx : x < natPow2 64) (hy : y < natPow2 64) (hv : v < natPow2 64) :
    MirRunsTo [6, 7] mirSelectAddBody
      (mirSelectAddInitState flag x y v) 9
      ⟨if flag then .int (mirAddUsize x v) else .int (mirAddUsize y v),
       [if flag then .int (mirAddUsize x v) else .int x,
        if flag then .int y else .int (mirAddUsize y v)]⟩ := by
  have hxDec : decide (x < natPow2 64) = true := decide_eq_true hx
  have hyDec : decide (y < natPow2 64) = true := decide_eq_true hy
  have hvDec : decide (v < natPow2 64) = true := decide_eq_true hv
  refine mir_entry_stepped_runsTo [6, 7] mirSelectAddBody
    (mirSelectAddInitState flag x y v).locals
    (mirSelectAddInitState flag x y v).localGens
    (mirSelectAddState1 flag x y v) 8
    ⟨if flag then .int (mirAddUsize x v) else .int (mirAddUsize y v),
     [if flag then .int (mirAddUsize x v) else .int x,
      if flag then .int y else .int (mirAddUsize y v)]⟩ ?_ ?_
  · change
      mirEntryStep4
        (decide (x < natPow2 64))
        (decide (y < natPow2 64))
        (decide (v < natPow2 64))
        (mirSelectAddState1 flag x y v) =
      StepOutcome.stepped (mirSelectAddState1 flag x y v)
    rw [hxDec, hyDec, hvDec]
    rfl
  · cases flag with
    | true =>
      change MirLoopRunsTo [6, 7] mirSelectAddBody
        (mirSelectAddStateTrue4 x y v) (4 + 1)
        ⟨.int (mirAddUsize x v), [.int (mirAddUsize x v), .int y]⟩
      refine mir_stepped_runsTo [6, 7] mirSelectAddBody
        (mirSelectAddStateTrue4 x y v) (mirSelectAddStateTrue5 x y v) 4
        ⟨.int (mirAddUsize x v), [.int (mirAddUsize x v), .int y]⟩ ?_ ?_
      · change
          (match
            if decide (mirAddUsize x v < natPow2 64) = true then
              some (mirSelectAddStateTrue5 x y v).locals
            else none with
           | some locals' =>
             StepOutcome.stepped
               ⟨locals', [0, 0, 0, 0, 0, 1, 0, 0], 3, 1⟩
           | none => StepOutcome.fault) =
          StepOutcome.stepped (mirSelectAddStateTrue5 x y v)
        rw [decide_mirAddUsize_lt x v]
        rfl
      · refine mir_stepped_runsTo [6, 7] mirSelectAddBody
          (mirSelectAddStateTrue5 x y v) (mirSelectAddStateTrue6 x y v) 3
          ⟨.int (mirAddUsize x v), [.int (mirAddUsize x v), .int y]⟩ ?_ ?_
        · change
            (match
              if decide (mirAddUsize x v < natPow2 64) = true then
                some (mirSelectAddStateTrue6 x y v).locals
              else none with
             | some locals' =>
               StepOutcome.stepped
                 ⟨locals', [0, 0, 0, 0, 0, 1, 0, 0], 3, 2⟩
             | none => StepOutcome.fault) =
            StepOutcome.stepped (mirSelectAddStateTrue6 x y v)
          rw [decide_mirAddUsize_lt x v]
          rfl
        · change MirLoopRunsTo [6, 7] mirSelectAddBody
            (mirSelectAddStateTrue7 x y v) 2
            ⟨.int (mirAddUsize x v), [.int (mirAddUsize x v), .int y]⟩
          refine mir_returned_runsTo [6, 7] mirSelectAddBody
            (mirSelectAddStateTrue7 x y v)
            ⟨.int (mirAddUsize x v), mirSelectAddStateTrue7 x y v⟩
            ⟨.int (mirAddUsize x v), [.int (mirAddUsize x v), .int y]⟩ ?_ rfl
          change
            (if decide (mirAddUsize x v < natPow2 64) = true then
               StepOutcome.returned
                 ⟨.int (mirAddUsize x v), mirSelectAddStateTrue7 x y v⟩
             else StepOutcome.fault) =
            StepOutcome.returned
              ⟨.int (mirAddUsize x v), mirSelectAddStateTrue7 x y v⟩
          rw [decide_mirAddUsize_lt x v]
          rfl
    | false =>
      change MirLoopRunsTo [6, 7] mirSelectAddBody
        (mirSelectAddStateFalse4 x y v) (4 + 1)
        ⟨.int (mirAddUsize y v), [.int x, .int (mirAddUsize y v)]⟩
      refine mir_stepped_runsTo [6, 7] mirSelectAddBody
        (mirSelectAddStateFalse4 x y v) (mirSelectAddStateFalse5 x y v) 4
        ⟨.int (mirAddUsize y v), [.int x, .int (mirAddUsize y v)]⟩ ?_ ?_
      · change
          (match
            if decide (mirAddUsize y v < natPow2 64) = true then
              some (mirSelectAddStateFalse5 x y v).locals
            else none with
           | some locals' =>
             StepOutcome.stepped
               ⟨locals', [0, 0, 0, 0, 0, 1, 0, 0], 3, 1⟩
           | none => StepOutcome.fault) =
          StepOutcome.stepped (mirSelectAddStateFalse5 x y v)
        rw [decide_mirAddUsize_lt y v]
        rfl
      · refine mir_stepped_runsTo [6, 7] mirSelectAddBody
          (mirSelectAddStateFalse5 x y v) (mirSelectAddStateFalse6 x y v) 3
          ⟨.int (mirAddUsize y v), [.int x, .int (mirAddUsize y v)]⟩ ?_ ?_
        · change
            (match
              if decide (mirAddUsize y v < natPow2 64) = true then
                some (mirSelectAddStateFalse6 x y v).locals
              else none with
             | some locals' =>
               StepOutcome.stepped
                 ⟨locals', [0, 0, 0, 0, 0, 1, 0, 0], 3, 2⟩
             | none => StepOutcome.fault) =
            StepOutcome.stepped (mirSelectAddStateFalse6 x y v)
          rw [decide_mirAddUsize_lt y v]
          rfl
        · change MirLoopRunsTo [6, 7] mirSelectAddBody
            (mirSelectAddStateFalse7 x y v) 2
            ⟨.int (mirAddUsize y v), [.int x, .int (mirAddUsize y v)]⟩
          refine mir_returned_runsTo [6, 7] mirSelectAddBody
            (mirSelectAddStateFalse7 x y v)
            ⟨.int (mirAddUsize y v), mirSelectAddStateFalse7 x y v⟩
            ⟨.int (mirAddUsize y v), [.int x, .int (mirAddUsize y v)]⟩ ?_ rfl
          change
            (if decide (mirAddUsize y v < natPow2 64) = true then
               StepOutcome.returned
                 ⟨.int (mirAddUsize y v), mirSelectAddStateFalse7 x y v⟩
             else StepOutcome.fault) =
            StepOutcome.returned
              ⟨.int (mirAddUsize y v), mirSelectAddStateFalse7 x y v⟩
          rw [decide_mirAddUsize_lt y v]
          rfl

/-- End-to-end verification of the 4-block `mirSelectAddBody` for both values
of `flag` and all 64-bit `usize` inputs `x, y, v < 2^64`. Each value of
`flag` gives one concrete run per side: `PureLift` evaluates only the selected
arm, and `Trusted.runMirSteps` follows the matching `SwitchInt` edge, and the
two results agree. The symbolic diamond join is not exercised, because the
condition is always concrete. -/
theorem mir_select_add_verified (flag : Bool) (x y v : Nat)
    (hx : x < natPow2 64) (hy : y < natPow2 64) (hv : v < natPow2 64) :
    (evalFnValue mirValAlg
        [⟨.byVal, .bool flag⟩,
         ⟨.mutRef 0 [], .int x⟩,
         ⟨.mutRef 1 [], .int y⟩,
         ⟨.byVal, .int v⟩]
        mirSelectAddPlan
        (.use (.localSub 5 [])) =
      .ok ⟨if flag then .int (mirAddUsize x v) else .int (mirAddUsize y v),
           [if flag then .int (mirAddUsize x v) else .int x,
            if flag then .int y else .int (mirAddUsize y v)]⟩) ∧
    MirRunsTo [6, 7] mirSelectAddBody
      (mirSelectAddInitState flag x y v) 9
      ⟨if flag then .int (mirAddUsize x v) else .int (mirAddUsize y v),
       [if flag then .int (mirAddUsize x v) else .int x,
        if flag then .int y else .int (mirAddUsize y v)]⟩ ∧
    (Exists fun k => Exists fun mFinal => Exists fun out =>
      (mirOperationalAdapter [6, 7] mirSelectAddBody
        [⟨.byVal, .bool flag⟩, ⟨.mutRef 0 [], .int x⟩,
          ⟨.mutRef 1 [], .int y⟩, ⟨.byVal, .int v⟩]).ExecutesTo
        (.running (mirSelectAddInitState flag x y v)) k mFinal ∧
      (mirOperationalAdapter [6, 7] mirSelectAddBody
        [⟨.byVal, .bool flag⟩, ⟨.mutRef 0 [], .int x⟩,
          ⟨.mutRef 1 [], .int y⟩, ⟨.byVal, .int v⟩]).FinalLoansRel out mFinal ∧
      out = ⟨if flag then .int (mirAddUsize x v) else .int (mirAddUsize y v),
             [if flag then .int (mirAddUsize x v) else .int x,
              if flag then .int y else .int (mirAddUsize y v)]⟩) := by
  have hPure :
      evalFnValue mirValAlg
        [⟨.byVal, .bool flag⟩,
         ⟨.mutRef 0 [], .int x⟩,
         ⟨.mutRef 1 [], .int y⟩,
         ⟨.byVal, .int v⟩]
        mirSelectAddPlan
        (.use (.localSub 5 [])) =
      .ok ⟨if flag then .int (mirAddUsize x v) else .int (mirAddUsize y v),
           [if flag then .int (mirAddUsize x v) else .int x,
            if flag then .int y else .int (mirAddUsize y v)]⟩ := by
    cases flag <;> rfl
  have hMir := mirSelectAdd_runsTo flag x y v hx hy hv
  refine ⟨hPure, hMir, ?_⟩
  exact mir_pure_lift_sound [6, 7] mirSelectAddBody
    [⟨.byVal, .bool flag⟩,
     ⟨.mutRef 0 [], .int x⟩,
     ⟨.mutRef 1 [], .int y⟩,
     ⟨.byVal, .int v⟩]
    mirSelectAddPlan
    (.use (.localSub 5 []))
    (fun out =>
      out = ⟨if flag then .int (mirAddUsize x v) else .int (mirAddUsize y v),
             [if flag then .int (mirAddUsize x v) else .int x,
              if flag then .int y else .int (mirAddUsize y v)]⟩)
    (mirSelectAddInitState flag x y v)
    ⟨rfl, rfl⟩
    ⟨_, ⟨rfl, rfl⟩⟩
    (by cases flag <;> rfl)
    (by
      intro out hEval
      rw [hPure] at hEval
      injection hEval with hOut
      subst hOut
      exact ⟨9, hMir⟩)

/-! ### Workload M-4: Multi-Block Loop with Mutable Reborrow (`loop_accumulate`)

Rust equivalent:
```rust
fn loop_accumulate(acc: &mut usize, mut n: usize) -> usize {
    while n > 0 {
        let r = &mut *acc;
        *r = *r + 1;
        n = n - 1;
    }
    *acc
}
```
Compiled with `-C overflow-checks=off`, so `+` and `-` lower to the plain
wrapping `BinOp::Add` and `BinOp::Sub` (with overflow checks, MIR building
emits `AddWithOverflow` and an `Assert` terminator, which this subset omits).
-/

/-- 4-block loop `Trusted.MirBody` for `loop_accumulate`. The start block
`bb0` only jumps to the loop header `bb1`, because MIR forbids edges into the
start block. -/
def mirLoopAccumulateBody : MirBody :=
  { argCount := 2
    localCount := 5
    ptrWidthBits := 64
    localTys := [.usize, .refMut .usize, .usize, .bool, .refMut .usize, .usize]
    blocks :=
      [ -- bb0: function entry (`goto bb1`)
        { stmts := []
          terminator := .goto ⟨1⟩
        }
      , -- bb1: loop header (`_3 = _2 > 0; SwitchInt(_3)`)
        { stmts :=
            [ .assign ⟨⟨3⟩, []⟩
                (.binaryOp .gt (.copy ⟨⟨2⟩, []⟩) (.constVal (.int 0)))
            ]
          terminator :=
            .switchInt (.copy ⟨⟨3⟩, []⟩)
              { branches := [⟨0, ⟨3⟩⟩], otherwise := ⟨2⟩ }
        }
      , -- bb2: loop body (`_4 = &mut *_1; *_4 += 1; _2 -= 1; goto bb1`)
        { stmts :=
            [ .storageLive ⟨4⟩
            , .assign ⟨⟨4⟩, []⟩ (.refMut ⟨⟨1⟩, [.deref]⟩)
            , .assign ⟨⟨4⟩, [.deref]⟩
                (.binaryOp .add (.copy ⟨⟨4⟩, [.deref]⟩) (.constVal (.int 1)))
            , .storageDead ⟨4⟩
            , .assign ⟨⟨2⟩, []⟩
                (.binaryOp .sub (.copy ⟨⟨2⟩, []⟩) (.constVal (.int 1)))
            ]
          terminator := .goto ⟨1⟩
        }
      , -- bb3: loop exit (`_0 = *_1; return`)
        { stmts := [.assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, [.deref]⟩))]
          terminator := .return_
        }
      ]
  }

/-- Initial `Trusted.MirState` for `mirLoopAccumulateBody`. -/
def mirLoopAccumulateInitState (acc n : Nat) : MirState :=
  { locals :=
      [ some .uninit
      , some (.ref true 0 ⟨5⟩ [])
      , some (.int n)
      , some .uninit
      , none
      , some (.int acc)
      ]
    localGens := [0, 0, 0, 0, 0, 0]
    block := 0
    stmtIdx := 0
  }

/-- `PureLift` `.whileLoop` plan for `loop_accumulate`: local `0` is `acc: &mut
usize`, local `1` is `n: usize`, and local `2` is the per-iteration reborrow
`r = &mut *acc` retired via `.endLoanAtLocal 2`. -/
def mirLoopAccumulatePlan : FlowPlan MirVal :=
  .whileLoop 4
    (.unary (fun v => mirGtVal v (.int 0)) (.localSub 1 []))
    (.seq
      (.act (.borrow 2 .mutBorrow (.derefSub 0 [])))
      (.seq
        (.act (.assign (.derefSub 2 [])
          (.unary (fun v => mirAddVal v (.int 1)) (.derefSub 2 []))))
        (.seq
          (.act (.endLoanAtLocal 2))
          (.act (.assign (.localSub 1 [])
            (.unary (fun v => mirSubUsizeVal v (.int 1)) (.localSub 1 [])))))))

/-- Accumulator of `loop_accumulate` after one iteration. -/
def mirLoopAcc1 (acc : Nat) : Nat :=
  mirAddUsize acc 1

/-- Accumulator of `loop_accumulate` after two iterations. -/
def mirLoopAcc2 (acc : Nat) : Nat :=
  mirAddUsize (mirLoopAcc1 acc) 1

/-- Accumulator of `loop_accumulate` after three iterations. -/
def mirLoopAcc3 (acc : Nat) : Nat :=
  mirAddUsize (mirLoopAcc2 acc) 1

/-- State of `mirLoopAccumulateBody` at the loop header (`bb1`, statement `0`)
with accumulator `accVal`, counter `nVal`, comparison temporary `init3`, and
generation `gen4` of the reborrow local `_4`. -/
def mirLoopHeaderState (accVal nVal : Nat) (init3 : MirVal) (gen4 : Nat) :
    MirState :=
  { locals :=
      [ some .uninit
      , some (.ref true 0 ⟨5⟩ [])
      , some (.int nVal)
      , some init3
      , none
      , some (.int accVal)
      ]
    localGens := [0, 0, 0, 0, gen4, 0]
    block := 1
    stmtIdx := 0
  }

/-- State of `mirLoopAccumulateBody` after the header's comparison (`bb1`,
statement `1`) with comparison result `cmp`. -/
def mirLoopAfterCmpState (accVal nVal : Nat) (cmp : Bool) (gen4 : Nat) :
    MirState :=
  { locals :=
      [ some .uninit
      , some (.ref true 0 ⟨5⟩ [])
      , some (.int nVal)
      , some (.bool cmp)
      , none
      , some (.int accVal)
      ]
    localGens := [0, 0, 0, 0, gen4, 0]
    block := 1
    stmtIdx := 1
  }

/-- State of `mirLoopAccumulateBody` in the loop body just before the add
through the reborrow (`bb2`, statement `2`). -/
def mirLoopBeforeAddState (accVal nVal gen4 : Nat) : MirState :=
  { locals :=
      [ some .uninit
      , some (.ref true 0 ⟨5⟩ [])
      , some (.int nVal)
      , some (.bool true)
      , some (.ref true 0 ⟨5⟩ [] 1)
      , some (.int accVal)
      ]
    localGens := [0, 0, 0, 0, gen4, 0]
    block := 2
    stmtIdx := 2
  }

/-- State of `mirLoopAccumulateBody` in the loop body just after the add through
the reborrow (`bb2`, statement `3`). -/
def mirLoopAfterAddState (accVal nVal gen4 : Nat) : MirState :=
  { locals :=
      [ some .uninit
      , some (.ref true 0 ⟨5⟩ [])
      , some (.int nVal)
      , some (.bool true)
      , some (.ref true 0 ⟨5⟩ [] 1)
      , some (.int (mirAddUsize accVal 1))
      ]
    localGens := [0, 0, 0, 0, gen4, 0]
    block := 2
    stmtIdx := 3
  }

/-- State of `mirLoopAccumulateBody` at the exit block (`bb3`, statement `0`)
after three iterations. -/
def mirLoopAccumulateState26 (acc : Nat) : MirState :=
  { locals :=
      [ some .uninit
      , some (.ref true 0 ⟨5⟩ [])
      , some (.int 0)
      , some (.bool false)
      , none
      , some (.int (mirLoopAcc3 acc))
      ]
    localGens := [0, 0, 0, 0, 6, 0]
    block := 3
    stmtIdx := 0
  }

/-- State of `mirLoopAccumulateBody` at the exit block just before `return`
(`bb3`, statement `1`). -/
def mirLoopAccumulateState27 (acc : Nat) : MirState :=
  { locals :=
      [ some (.int (mirLoopAcc3 acc))
      , some (.ref true 0 ⟨5⟩ [])
      , some (.int 0)
      , some (.bool false)
      , none
      , some (.int (mirLoopAcc3 acc))
      ]
    localGens := [0, 0, 0, 0, 6, 0]
    block := 3
    stmtIdx := 1
  }

/-- Step-by-step execution of `mirLoopAccumulateBody` for three loop iterations,
for any 64-bit initial accumulator. -/
theorem mirLoopAccumulate_runsTo (acc : Nat) (hacc : acc < natPow2 64) :
    MirRunsTo [5] mirLoopAccumulateBody
      (mirLoopAccumulateInitState acc 3) 29
      ⟨.int (mirLoopAcc3 acc), [.int (mirLoopAcc3 acc)]⟩ := by
  have hacc0 : decide (acc < natPow2 64) = true := decide_eq_true hacc
  have hacc3 : decide (mirLoopAcc3 acc < natPow2 64) = true :=
    decide_mirAddUsize_lt (mirLoopAcc2 acc) 1
  -- Entry: `bb0` jumps to the loop header (`29 -> 28`)
  refine mir_entry_stepped_runsTo [5] mirLoopAccumulateBody
    (mirLoopAccumulateInitState acc 3).locals
    (mirLoopAccumulateInitState acc 3).localGens
    (mirLoopHeaderState acc 3 .uninit 0) 28
    ⟨.int (mirLoopAcc3 acc), [.int (mirLoopAcc3 acc)]⟩ ?_ ?_
  · change
      mirEntryStep2 5 (decide (acc < natPow2 64)) true
        (mirLoopHeaderState acc 3 .uninit 0) =
      StepOutcome.stepped (mirLoopHeaderState acc 3 .uninit 0)
    rw [hacc0]
    rfl
  · -- Iteration 1: add step (`24 -> 23`)
    change MirLoopRunsTo [5] mirLoopAccumulateBody
      (mirLoopBeforeAddState acc 3 1) (23 + 1)
      ⟨.int (mirLoopAcc3 acc), [.int (mirLoopAcc3 acc)]⟩
    refine mir_stepped_runsTo [5] mirLoopAccumulateBody
      (mirLoopBeforeAddState acc 3 1) (mirLoopAfterAddState acc 3 1) 23
      ⟨.int (mirLoopAcc3 acc), [.int (mirLoopAcc3 acc)]⟩ ?_ ?_
    · change
        (match
          if decide (mirAddUsize acc 1 < natPow2 64) = true then
            some (mirLoopAfterAddState acc 3 1).locals
          else none with
         | some locals' =>
           StepOutcome.stepped ⟨locals', [0, 0, 0, 0, 1, 0], 2, 3⟩
         | none => StepOutcome.fault) =
        StepOutcome.stepped (mirLoopAfterAddState acc 3 1)
      rw [decide_mirAddUsize_lt acc 1]
      rfl
    · -- Iteration 2: add step (`16 -> 15`)
      change MirLoopRunsTo [5] mirLoopAccumulateBody
        (mirLoopBeforeAddState (mirLoopAcc1 acc) 2 3) (15 + 1)
        ⟨.int (mirLoopAcc3 acc), [.int (mirLoopAcc3 acc)]⟩
      refine mir_stepped_runsTo [5] mirLoopAccumulateBody
        (mirLoopBeforeAddState (mirLoopAcc1 acc) 2 3)
        (mirLoopAfterAddState (mirLoopAcc1 acc) 2 3) 15
        ⟨.int (mirLoopAcc3 acc), [.int (mirLoopAcc3 acc)]⟩ ?_ ?_
      · change
          (match
            if decide (mirAddUsize (mirLoopAcc1 acc) 1 < natPow2 64) =
                true then
              some (mirLoopAfterAddState (mirLoopAcc1 acc) 2 3).locals
            else none with
           | some locals' =>
             StepOutcome.stepped ⟨locals', [0, 0, 0, 0, 3, 0], 2, 3⟩
           | none => StepOutcome.fault) =
          StepOutcome.stepped (mirLoopAfterAddState (mirLoopAcc1 acc) 2 3)
        rw [decide_mirAddUsize_lt (mirLoopAcc1 acc) 1]
        rfl
      · -- Iteration 3: add step (`8 -> 7`)
        change MirLoopRunsTo [5] mirLoopAccumulateBody
          (mirLoopBeforeAddState (mirLoopAcc2 acc) 1 5) (7 + 1)
          ⟨.int (mirLoopAcc3 acc), [.int (mirLoopAcc3 acc)]⟩
        refine mir_stepped_runsTo [5] mirLoopAccumulateBody
          (mirLoopBeforeAddState (mirLoopAcc2 acc) 1 5)
          (mirLoopAfterAddState (mirLoopAcc2 acc) 1 5) 7
          ⟨.int (mirLoopAcc3 acc), [.int (mirLoopAcc3 acc)]⟩ ?_ ?_
        · change
            (match
              if decide (mirAddUsize (mirLoopAcc2 acc) 1 < natPow2 64) =
                  true then
                some (mirLoopAfterAddState (mirLoopAcc2 acc) 1 5).locals
              else none with
             | some locals' =>
               StepOutcome.stepped ⟨locals', [0, 0, 0, 0, 5, 0], 2, 3⟩
             | none => StepOutcome.fault) =
            StepOutcome.stepped (mirLoopAfterAddState (mirLoopAcc2 acc) 1 5)
          rw [decide_mirAddUsize_lt (mirLoopAcc2 acc) 1]
          rfl
        · -- Exit block `bb3`: `_0 = *_1` (`2 -> 1`) and `return`
          change MirLoopRunsTo [5] mirLoopAccumulateBody
            (mirLoopAccumulateState26 acc) (1 + 1)
            ⟨.int (mirLoopAcc3 acc), [.int (mirLoopAcc3 acc)]⟩
          refine mir_stepped_runsTo [5] mirLoopAccumulateBody
            (mirLoopAccumulateState26 acc)
            (mirLoopAccumulateState27 acc) 1
            ⟨.int (mirLoopAcc3 acc), [.int (mirLoopAcc3 acc)]⟩ ?_ ?_
          · change
              (match
                if decide (mirLoopAcc3 acc < natPow2 64) = true then
                  some (mirLoopAccumulateState27 acc).locals
                else none with
               | some locals' =>
                 StepOutcome.stepped ⟨locals', [0, 0, 0, 0, 6, 0], 3, 1⟩
               | none => StepOutcome.fault) =
              StepOutcome.stepped (mirLoopAccumulateState27 acc)
            rw [hacc3]
            rfl
          · refine mir_returned_runsTo [5] mirLoopAccumulateBody
              (mirLoopAccumulateState27 acc)
              ⟨.int (mirLoopAcc3 acc), mirLoopAccumulateState27 acc⟩
              ⟨.int (mirLoopAcc3 acc), [.int (mirLoopAcc3 acc)]⟩ ?_ rfl
            change
              (if decide (mirLoopAcc3 acc < natPow2 64) = true then
                 StepOutcome.returned
                   ⟨.int (mirLoopAcc3 acc), mirLoopAccumulateState27 acc⟩
               else StepOutcome.fault) =
              StepOutcome.returned
                ⟨.int (mirLoopAcc3 acc), mirLoopAccumulateState27 acc⟩
            rw [hacc3]
            rfl

/-- End-to-end verification of `mirLoopAccumulateBody` for 3 loop iterations
(`n = 3`) and any 64-bit `usize` initial accumulator `acc < 2^64`. -/
theorem mir_loop_accumulate_verified (acc : Nat) (hacc : acc < natPow2 64) :
    (evalFnValue mirValAlg
        [⟨.mutRef 0 [], .int acc⟩, ⟨.byVal, .int 3⟩]
        mirLoopAccumulatePlan
        (.use (.derefSub 0 [])) =
      .ok ⟨.int (mirLoopAcc3 acc), [.int (mirLoopAcc3 acc)]⟩) ∧
    MirRunsTo [5] mirLoopAccumulateBody
      (mirLoopAccumulateInitState acc 3) 29
      ⟨.int (mirLoopAcc3 acc), [.int (mirLoopAcc3 acc)]⟩ ∧
    (Exists fun k => Exists fun mFinal => Exists fun out =>
      (mirOperationalAdapter [5] mirLoopAccumulateBody
        [⟨.mutRef 0 [], .int acc⟩, ⟨.byVal, .int 3⟩]).ExecutesTo
        (.running (mirLoopAccumulateInitState acc 3)) k mFinal ∧
      (mirOperationalAdapter [5] mirLoopAccumulateBody
        [⟨.mutRef 0 [], .int acc⟩, ⟨.byVal, .int 3⟩]).FinalLoansRel
        out mFinal ∧
      out = ⟨.int (mirLoopAcc3 acc), [.int (mirLoopAcc3 acc)]⟩) := by
  refine ⟨rfl, mirLoopAccumulate_runsTo acc hacc, ?_⟩
  exact mir_pure_lift_sound [5] mirLoopAccumulateBody
    [⟨.mutRef 0 [], .int acc⟩, ⟨.byVal, .int 3⟩]
    mirLoopAccumulatePlan
    (.use (.derefSub 0 []))
    (fun out => out = ⟨.int (mirLoopAcc3 acc), [.int (mirLoopAcc3 acc)]⟩)
    (mirLoopAccumulateInitState acc 3)
    ⟨rfl, rfl⟩
    ⟨_, ⟨rfl, rfl⟩⟩
    rfl
    (by
      intro out hEval
      change
        EvalOutcome.ok ⟨.int (mirLoopAcc3 acc), [.int (mirLoopAcc3 acc)]⟩ =
        EvalOutcome.ok out at hEval
      injection hEval with hOut
      subst hOut
      exact ⟨29, mirLoopAccumulate_runsTo acc hacc⟩)

/-! ### Workload M-5: Dangling Reference and Use-While-Borrowed Rejection

Verifies fail-closed rejection of two invalid borrow-lifecycle programs in
both `PureLift` and `Trusted.MirSemantics`:
1. **Use after loan end / `StorageDead`**: borrowing `_2 = &mut _1`, ending the
   loan / executing `StorageDead(_1)`, and then reading `*_2` fails in both
   `PureLift` (`evalFnValue = .fail`) and `Trusted.MirSemantics` (`runMirSteps =
   .fault`). The two programs differ in how the reference dies: `PureLift`
   ends the loan (`endLoan`), while MIR deallocates the referent
   (`StorageDead`). Controls that read before the loan ends, or without the
   `StorageDead`, succeed in both semantics.
2. **Owner overwrite while borrowed + child dereference**: borrowing `_2 = &mut
   (*_1)`, overwriting `*_1 = 99` while `_2` is active, and then reading `*_2`
   fails in both `PureLift` (`evalFnValue = .fail`) and `Trusted.MirSemantics`
   (`runMirSteps = .fault`), but at different steps. `PureLift` rejects the
   overwrite itself, because the owner path is mutably borrowed. MIR accepts
   the overwrite, which retires `_2` as Stacked Borrows does, and rejects only
   the later read through `_2`. The two semantics agree that the program
   fails, not on where. The `PureLift` program ends the loan properly, and a
   control without the overwrite succeeds, so its failure comes from the
   overwrite.
-/

/-- `Trusted.MirBody` that takes `&mut _1`, executes `StorageDead(_1)`, and then
attempts to read `*_2`. -/
def mirDanglingRefBody : MirBody :=
  { argCount := 0
    localCount := 3
    ptrWidthBits := 64
    localTys := [.usize, .usize, .refMut .usize]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .assign ⟨⟨1⟩, []⟩ (.use (.constVal (.int 42)))
            , .storageLive ⟨2⟩
            , .assign ⟨⟨2⟩, []⟩ (.refMut ⟨⟨1⟩, []⟩)
            , .storageDead ⟨1⟩
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨2⟩, [.deref]⟩))
            ]
          terminator := .return_
        }
      ]
  }

/-- Control for `mirDanglingRefBody`: the same body without `StorageDead(_1)`,
so the read of `*_2` is valid and the body returns `42`. -/
def mirLiveRefReadBody : MirBody :=
  { argCount := 0
    localCount := 3
    ptrWidthBits := 64
    localTys := [.usize, .usize, .refMut .usize]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .assign ⟨⟨1⟩, []⟩ (.use (.constVal (.int 42)))
            , .storageLive ⟨2⟩
            , .assign ⟨⟨2⟩, []⟩ (.refMut ⟨⟨1⟩, []⟩)
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨2⟩, [.deref]⟩))
            ]
          terminator := .return_
        }
      ]
  }

/-- Initial `Trusted.MirState` for `mirDanglingRefBody`. -/
def mirDanglingRefInitState : MirState :=
  { locals := [some .uninit, none, none]
    localGens := [0, 0, 0]
    block := 0
    stmtIdx := 0
  }

/-- `Trusted.MirBody` that borrows `_2 = &mut (*_1)`, overwrites `*_1 = 99`
while `_2` is active (retiring `_2`), and then attempts to read `*_2`. -/
def mirWriteWhileBorrowedBody : MirBody :=
  { argCount := 1
    localCount := 3
    ptrWidthBits := 64
    localTys := [.usize, .refMut .usize, .refMut .usize, .usize]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨2⟩
            , .assign ⟨⟨2⟩, []⟩ (.refMut ⟨⟨1⟩, [.deref]⟩)
            , .assign ⟨⟨1⟩, [.deref]⟩ (.use (.constVal (.int 99)))
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨2⟩, [.deref]⟩))
            ]
          terminator := .return_
        }
      ]
  }

/-- Initial `Trusted.MirState` for `mirWriteWhileBorrowedBody`. -/
def mirWriteWhileBorrowedInitState : MirState :=
  { locals := [some .uninit, some (.ref true 0 ⟨3⟩ [] 0), none, some (.int 42)]
    localGens := [0, 0, 0, 0]
    block := 0
    stmtIdx := 0
  }

/-- Both `PureLift` (`evalFnValue`) and `Trusted.runMirSteps` fail closed on
both use-after-loan-end and owner-overwrite-while-borrowed workloads (for the
second, at different steps; see the section comment). -/
theorem mir_dangling_and_conflict_rejected :
    evalFnValue mirValAlg
      []
      (.seq
        (.act (.assign (.localSub 0 []) (.constVal (.int 42))))
        (.seq
          (.act (.borrow 1 .mutBorrow (.localSub 0 [])))
          (.seq
            (.act (.endLoan 0))
            (.act (.assign (.localSub 2 []) (.use (.derefSub 1 [])))))))
      (.use (.localSub 2 [])) = .fail ∧
    -- Control: reading before the loan ends succeeds.
    evalFnValue mirValAlg
      []
      (.seq
        (.act (.assign (.localSub 0 []) (.constVal (.int 42))))
        (.seq
          (.act (.borrow 1 .mutBorrow (.localSub 0 [])))
          (.seq
            (.act (.assign (.localSub 2 []) (.use (.derefSub 1 []))))
            (.act (.endLoan 0)))))
      (.use (.localSub 2 [])) = .ok ⟨.int 42, []⟩ ∧
    runMirSteps mirDanglingRefBody 10 mirDanglingRefInitState = .fault ∧
    -- Control: without `StorageDead(_1)`, the read succeeds.
    (match runMirSteps mirLiveRefReadBody 10 mirDanglingRefInitState with
     | .returned ret => ret.value = .int 42
     | _ => False) ∧
    evalFnValue mirValAlg
      [⟨.mutRef 0 [], .int 42⟩]
      (.seq
        (.act (.borrow 1 .mutBorrow (.derefSub 0 [])))
        (.seq
          (.act (.assign (.derefSub 0 []) (.constVal (.int 99))))
          (.seq
            (.act (.assign (.localSub 2 []) (.use (.derefSub 1 []))))
            (.act (.endLoan 1)))))
      (.use (.localSub 2 [])) = .fail ∧
    -- Control: without the overwrite, the same `PureLift` program succeeds.
    evalFnValue mirValAlg
      [⟨.mutRef 0 [], .int 42⟩]
      (.seq
        (.act (.borrow 1 .mutBorrow (.derefSub 0 [])))
        (.seq
          (.act (.assign (.localSub 2 []) (.use (.derefSub 1 []))))
          (.act (.endLoan 1))))
      (.use (.localSub 2 [])) = .ok ⟨.int 42, [.int 42]⟩ ∧
    runMirSteps mirWriteWhileBorrowedBody 10
      mirWriteWhileBorrowedInitState = .fault := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Exhaustive MIR Semantics and Bridge Regression Suite -/

/-- `mirValAlg.asBool` treats an integer branch condition as true iff it is
nonzero, and the workload helper `mirSubUsizeVal` agrees with the trusted
`Trusted.evalBinOp .sub` at width 64, which wraps on underflow; without a
width the trusted operation faults. -/
theorem mir_int_branch_and_wrapping_sub_tests :
    evalFnValue mirValAlg
      [⟨.byVal, .int 5⟩]
      (.branch (.use (.localSub 0 []))
        (.act (.assign (.localSub 1 []) (.constVal (.int 10))))
        (.act (.assign (.localSub 1 []) (.constVal (.int 20)))))
      (.use (.localSub 1 [])) = .ok ⟨.int 10, []⟩ ∧
    evalFnValue mirValAlg
      [⟨.byVal, .int 0⟩]
      (.branch (.use (.localSub 0 []))
        (.act (.assign (.localSub 1 []) (.constVal (.int 10))))
        (.act (.assign (.localSub 1 []) (.constVal (.int 20)))))
      (.use (.localSub 1 [])) = .ok ⟨.int 20, []⟩ ∧
    mirSubUsizeVal (.int 5) (.int 2) =
      evalBinOp .sub (.int 5) (.int 2) (some 64) ∧
    mirSubUsizeVal (.int 2) (.int 5) =
      evalBinOp .sub (.int 2) (.int 5) (some 64) ∧
    evalBinOp .sub (.int 2) (.int 5) (some 8) = some (.int 253) ∧
    evalBinOp .sub (.int 5) (.int 2) = none := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Test body for `mir_deep_aggregate_spine_and_path_tests`. -/
def tenFieldTupleVal : MirVal :=
  packSpine
    [ .int 0, .int 1, .int 2, .int 3, .int 4
    , .int 5, .int 6, .int 7, .int 8, .int 9 ]

/-- A struct value nested ten levels deep, holding `42` at the innermost field.
-/
def depthTenNestedMirVal : MirVal :=
  .adt 0 (.fieldCons
    (.adt 0 (.fieldCons
      (.adt 0 (.fieldCons
        (.adt 0 (.fieldCons
          (.adt 0 (.fieldCons
            (.adt 0 (.fieldCons
              (.adt 0 (.fieldCons
                (.adt 0 (.fieldCons
                  (.adt 0 (.fieldCons
                    (.adt 0 (.fieldCons (.int 42) .unit))
                  .unit))
                .unit))
              .unit))
            .unit))
          .unit))
        .unit))
      .unit))
    .unit))
  .unit)

/-- `MirVal.isFullyInit`, `readFieldPath`, and `writeFieldPath` operate on
10-field and depth-10 nested aggregates: the structural folds have no depth
bound. -/
theorem mir_deep_aggregate_spine_and_path_tests :
    tenFieldTupleVal.isFullyInit = true ∧
    getMirField 9 tenFieldTupleVal = some (.int 9) ∧
    depthTenNestedMirVal.isFullyInit = true ∧
    readFieldPath [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] depthTenNestedMirVal =
      some (.int 42) ∧
    (match writeFieldPath [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (.int 99)
        depthTenNestedMirVal with
     | some updated =>
       updated.isFullyInit = true ∧
       readFieldPath [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] updated = some (.int 99)
     | none => False) := by
  refine ⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩⟩

/-- Integer bitwise binary operations (`.bitAnd`, `.bitOr`, `.bitXor`) evaluate
properly on `MirVal.int`, including on values above $2^{16}$. -/
theorem mir_integer_bitwise_ops_tests :
    evalBinOp .bitAnd (.int 6) (.int 3) = some (.int 2) ∧
    evalBinOp .bitOr (.int 6) (.int 3) = some (.int 7) ∧
    evalBinOp .bitXor (.int 6) (.int 3) = some (.int 5) ∧
    evalBinOp .bitXor (.int 0) (.int 0) = some (.int 0) ∧
    evalBinOp .bitAnd (.int 65536) (.int 65536) = some (.int 65536) ∧
    evalBinOp .bitOr (.int 65536) (.int 1) = some (.int 65537) ∧
    evalBinOp .bitXor (.int 65537) (.int 65536) = some (.int 1) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Test body for `mir_unop_not_uint8_and_bool_tests`. -/
def mirUint8BitNotBody (input : Nat) : MirBody :=
  { argCount := 0
    localCount := 2
    ptrWidthBits := 64
    localTys := [.uint 8, .uint 8]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .assign ⟨⟨1⟩, []⟩ (.use (.constVal (.int input)))
            , .assign ⟨⟨0⟩, []⟩ (.unaryOp .not (.copy ⟨⟨1⟩, []⟩))
            ]
          terminator := .return_
        }
      ]
  }

/-- `UnOp.not` computes bitwise complement $(2^w - 1) - n$ on `MirTy.uint w`
integer operands as well as logical negation on `.bool` operands. -/
theorem mir_unop_not_uint8_and_bool_tests :
    (match runMirSteps (mirUint8BitNotBody 0) 5
        ⟨[some .uninit, none], [0, 0], 0, 0⟩ with
     | .returned ret => ret.value = .int 255
     | _ => False) ∧
    (match runMirSteps (mirUint8BitNotBody 170) 5
        ⟨[some .uninit, none], [0, 0], 0, 0⟩ with
     | .returned ret => ret.value = .int 85
     | _ => False) ∧
    evalUnOp .not none (.bool true) = some (.bool false) := by
  refine ⟨rfl, rfl, rfl⟩

/-- Test body for `mir_assign_to_dead_local_rejected`. -/
def mirAssignDeadLocalBody : MirBody :=
  { argCount := 0
    localCount := 2
    ptrWidthBits := 64
    localTys := [.usize, .usize]
    blocks :=
      [ { stmts :=
            [ .storageDead ⟨1⟩
            , .assign ⟨⟨1⟩, []⟩ (.use (.constVal (.int 42)))
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, []⟩))
            ]
          terminator := .return_
        }
      ]
  }

/-- `assignPlace` rejects direct root assignment to an unallocated (`none`)
local slot before `StorageLive` has allocated it. -/
theorem mir_assign_to_dead_local_rejected :
    runMirSteps mirAssignDeadLocalBody 4
      ⟨[some .uninit, none], [0, 0], 0, 0⟩ = .fault := rfl

/-- Test body for `mir_move_deinitializes_place_and_subfield_tests`. -/
def mirUseAfterMoveLocalBody : MirBody :=
  { argCount := 0
    localCount := 2
    ptrWidthBits := 64
    localTys := [.usize, .usize]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .assign ⟨⟨1⟩, []⟩ (.use (.constVal (.int 11)))
            , .assign ⟨⟨0⟩, []⟩ (.use (.move ⟨⟨1⟩, []⟩))
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, []⟩))
            ]
          terminator := .return_
        }
      ]
  }

/-- Moves field `0` out of a tuple local and then reads its sibling field `1`.
-/
def mirPartialFieldMoveSiblingReadBody : MirBody :=
  { argCount := 0
    localCount := 3
    ptrWidthBits := 64
    localTys := [.usize, .adt 0 [.usize, .usize], .usize]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .storageLive ⟨2⟩
            , .assign ⟨⟨1⟩, []⟩
                (.use (.constVal
                  (.adt 0 (.fieldCons (.int 10) (.fieldCons (.int 20) .unit)))))
            , .assign ⟨⟨2⟩, []⟩ (.use (.move ⟨⟨1⟩, [.field 0]⟩))
            , .assign ⟨⟨0⟩, []⟩
                (.binaryOp .add
                  (.copy ⟨⟨2⟩, []⟩)
                  (.copy ⟨⟨1⟩, [.field 1]⟩))
            ]
          terminator := .return_
        }
      ]
  }

/-- Moves field `0` out of a tuple local and then reads the same field again. -/
def mirPartialFieldMoveSameFieldReadBody : MirBody :=
  { argCount := 0
    localCount := 3
    ptrWidthBits := 64
    localTys := [.usize, .adt 0 [.usize, .usize], .usize]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .storageLive ⟨2⟩
            , .assign ⟨⟨1⟩, []⟩
                (.use (.constVal
                  (.adt 0 (.fieldCons (.int 10) (.fieldCons (.int 20) .unit)))))
            , .assign ⟨⟨2⟩, []⟩ (.use (.move ⟨⟨1⟩, [.field 0]⟩))
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, [.field 0]⟩))
            ]
          terminator := .return_
        }
      ]
  }

/-- `Operand.move` deinitializes the moved place (or sub-field) to `.uninit`,
causing subsequent reads of the moved place to fault while leaving sibling
fields readable. -/
theorem mir_move_deinitializes_place_and_subfield_tests :
    runMirSteps mirUseAfterMoveLocalBody 6
      ⟨[some .uninit, none], [0, 0], 0, 0⟩ = .fault ∧
    (match runMirSteps mirPartialFieldMoveSiblingReadBody 7
        ⟨[some .uninit, none, none], [0, 0, 0], 0, 0⟩ with
     | .returned ret => ret.value = .int 30
     | _ => False) ∧
    runMirSteps mirPartialFieldMoveSameFieldReadBody 7
      ⟨[some .uninit, none, none], [0, 0, 0], 0, 0⟩ = .fault := by
  refine ⟨rfl, rfl, rfl⟩

/-- Test body for `mir_reference_exclusivity_enforced`. -/
def mirReadOwnerWhileMutBorrowedBody : MirBody :=
  { argCount := 0
    localCount := 3
    ptrWidthBits := 64
    localTys := [.usize, .usize, .refMut .usize]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .assign ⟨⟨1⟩, []⟩ (.use (.constVal (.int 7)))
            , .storageLive ⟨2⟩
            , .assign ⟨⟨2⟩, []⟩ (.refMut ⟨⟨1⟩, []⟩)
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, []⟩))
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨2⟩, [.deref]⟩))
            ]
          terminator := .return_
        }
      ]
  }

/-- Borrows a local mutably, stops using the borrow, and overwrites the owner
(allowed under non-lexical lifetimes). -/
def mirNllOverwriteOwnerAfterBorrowBody : MirBody :=
  { argCount := 0
    localCount := 3
    ptrWidthBits := 64
    localTys := [.usize, .usize, .refMut .usize]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .assign ⟨⟨1⟩, []⟩ (.use (.constVal (.int 7)))
            , .storageLive ⟨2⟩
            , .assign ⟨⟨2⟩, []⟩ (.refMut ⟨⟨1⟩, []⟩)
            , .assign ⟨⟨2⟩, [.deref]⟩ (.use (.constVal (.int 8)))
            , .assign ⟨⟨1⟩, []⟩ (.use (.constVal (.int 9)))
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, []⟩))
            ]
          terminator := .return_
        }
      ]
  }

/-- Uses a parent `&mut` while a child reborrow of it is live, then uses the
child. -/
def mirUseParentWhileReborrowedBody : MirBody :=
  { argCount := 0
    localCount := 4
    ptrWidthBits := 64
    localTys := [.usize, .usize, .refMut .usize, .refMut .usize]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .assign ⟨⟨1⟩, []⟩ (.use (.constVal (.int 7)))
            , .storageLive ⟨2⟩
            , .assign ⟨⟨2⟩, []⟩ (.refMut ⟨⟨1⟩, []⟩)
            , .storageLive ⟨3⟩
            , .assign ⟨⟨3⟩, []⟩ (.refMut ⟨⟨2⟩, [.deref]⟩)
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨2⟩, [.deref]⟩))
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨3⟩, [.deref]⟩))
            ]
          terminator := .return_
        }
      ]
  }

/-- Takes two `&mut` arguments; used with entry states in which they alias. -/
def mirAliasedMutEntryArgsBody : MirBody :=
  { argCount := 2
    localCount := 3
    ptrWidthBits := 64
    localTys := [.usize, .refMut .usize, .refMut .usize, .usize]
    blocks :=
      [ { stmts :=
            [ .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, [.deref]⟩)) ]
          terminator := .return_
        }
      ]
  }

/-- `Trusted.MirSemantics` enforces Stacked-Borrows reference exclusivity while
supporting non-lexical borrow lifetimes (NLL):
1. Reading or writing an owner local `_1` directly while `_2 = &mut _1` is in
   scope retires `_2`, so a subsequent dereference `*_2` faults
   (`mirReadOwnerWhileMutBorrowedBody`), whereas NLL code that never uses `_2`
   again after overwriting `_1` succeeds
   (`mirNllOverwriteOwnerAfterBorrowBody`).
2. Using a parent mutable reference `*_2` while a child reborrow `_3 = &mut *_2`
   is in scope retires `_3`, so a subsequent use of `*_3` faults
   (`mirUseParentWhileReborrowedBody`).
3. Entry states with aliasing mutable reference arguments (`_1` and `_2`
   pointing to overlapping paths of the same caller slot) are rejected before
   the first step (`runMirSteps … = .rejected`). -/
theorem mir_reference_exclusivity_enforced :
    runMirSteps mirReadOwnerWhileMutBorrowedBody 8
      ⟨[some .uninit, none, none], [0, 0, 0], 0, 0⟩ = .fault ∧
    (match runMirSteps mirNllOverwriteOwnerAfterBorrowBody 9
        ⟨[some .uninit, none, none], [0, 0, 0], 0, 0⟩ with
     | .returned ret => ret.value = .int 9
     | _ => False) ∧
    runMirSteps mirUseParentWhileReborrowedBody 10
      ⟨[some .uninit, none, none, none], [0, 0, 0, 0], 0, 0⟩ = .fault ∧
    runMirSteps mirAliasedMutEntryArgsBody 3
      ⟨[some .uninit,
        some (.ref true 0 ⟨3⟩ []),
        some (.ref true 0 ⟨3⟩ []),
        some (.int 99)],
       [0, 0, 0, 0], 0, 0⟩ = .rejected := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- Test body for `mir_place_mention_uninit_vs_dead_tests`. -/
def mirPlaceMentionUninitBody : MirBody :=
  { argCount := 0
    localCount := 2
    ptrWidthBits := 64
    localTys := [.usize, .usize]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .placeMention ⟨⟨1⟩, []⟩
            , .assign ⟨⟨0⟩, []⟩ (.use (.constVal (.int 7)))
            ]
          terminator := .return_
        }
      ]
  }

/-- Mentions a local (`PlaceMention`) after its storage is dead. -/
def mirPlaceMentionDeadBody : MirBody :=
  { argCount := 0
    localCount := 2
    ptrWidthBits := 64
    localTys := [.usize, .usize]
    blocks :=
      [ { stmts :=
            [ .storageDead ⟨1⟩
            , .placeMention ⟨⟨1⟩, []⟩
            , .assign ⟨⟨0⟩, []⟩ (.use (.constVal (.int 7)))
            ]
          terminator := .return_
        }
      ]
  }

/-- `Stmt.placeMention` succeeds on a live `.uninit` local without loading it,
and faults on a dead (`none`) local. -/
theorem mir_place_mention_uninit_vs_dead_tests :
    (match runMirSteps mirPlaceMentionUninitBody 5
        ⟨[some .uninit, none], [0, 0], 0, 0⟩ with
     | .returned ret => ret.value = .int 7
     | _ => False) ∧
    runMirSteps mirPlaceMentionDeadBody 5
      ⟨[some .uninit, none], [0, 0], 0, 0⟩ = .fault := by
  exact ⟨rfl, rfl⟩

/-- `_2 = &_1` followed, if `kill`, by `StorageDead(_1); StorageLive(_1); _1 =
11`, which reallocates `_1` and leaves `_2` stale. The body then returns `*_2`,
either directly or (if `viaCopy`) through a copy `_3 = copy _2`. -/
def mirStaleRefBody (kill viaCopy : Bool) : MirBody :=
  { argCount := 0
    localCount := 4
    ptrWidthBits := 64
    localTys := [.usize, .usize, .ref .usize, .ref .usize]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .storageLive ⟨2⟩
            , .storageLive ⟨3⟩
            , .assign ⟨⟨1⟩, []⟩ (.use (.constVal (.int 10)))
            , .assign ⟨⟨2⟩, []⟩ (.ref ⟨⟨1⟩, []⟩)
            ] ++
            (if kill then
              [ .storageDead ⟨1⟩
              , .storageLive ⟨1⟩
              , .assign ⟨⟨1⟩, []⟩ (.use (.constVal (.int 11)))
              ]
            else []) ++
            (if viaCopy then
              [ .assign ⟨⟨3⟩, []⟩ (.use (.copy ⟨⟨2⟩, []⟩))
              , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨3⟩, [.deref]⟩))
              ]
            else
              [ .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨2⟩, [.deref]⟩)) ])
          terminator := .return_
        }
      ]
  }

/-- A stale reference faults when it is dereferenced or copied, even though
its referent local is allocated and initialized again: the reallocation bumps
the local's generation, so `_2`'s recorded generation no longer matches
(`resolvePlace`, `MirVal.isValidInState`). Without the reallocation, the same
bodies return `10`, so the faults come from staleness alone. -/
theorem mir_stale_ref_copy_and_deref_rejected :
    (match runMirSteps (mirStaleRefBody false false) 16
        ⟨[some .uninit, none, none, none], [0, 0, 0, 0], 0, 0⟩ with
     | .returned ret => ret.value = .int 10
     | _ => False) ∧
    runMirSteps (mirStaleRefBody true false) 16
      ⟨[some .uninit, none, none, none], [0, 0, 0, 0], 0, 0⟩ = .fault ∧
    (match runMirSteps (mirStaleRefBody false true) 16
        ⟨[some .uninit, none, none, none], [0, 0, 0, 0], 0, 0⟩ with
     | .returned ret => ret.value = .int 10
     | _ => False) ∧
    runMirSteps (mirStaleRefBody true true) 16
      ⟨[some .uninit, none, none, none], [0, 0, 0, 0], 0, 0⟩ = .fault := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Test body for `mir_direct_access_beyond_localCount_rejected`. -/
def mirOutOfBoundsDirectPlaceBody : MirBody :=
  { argCount := 1
    localCount := 2
    ptrWidthBits := 64
    localTys := [.usize, .refMut .usize, .usize]
    blocks :=
      [ { stmts :=
            [ .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨2⟩, []⟩)) ]
          terminator := .return_
        }
      ]
  }

/-- Direct place access to a slot index $\ge$ `body.localCount` is rejected even
when `st.locals` contains caller-owned referent slots at those indices. -/
theorem mir_direct_access_beyond_localCount_rejected :
    runMirSteps mirOutOfBoundsDirectPlaceBody 3
      ⟨[some .uninit, some (.ref true 0 ⟨2⟩ []), some (.int 55)],
       [0, 0, 0], 0, 0⟩ = .fault := rfl

/-- Test body for `mir_localTys_uint8_bounds_enforced`. -/
def mirTypedUint8Body (valToStore : Nat) : MirBody :=
  { argCount := 0
    localCount := 1
    ptrWidthBits := 64
    localTys := [.uint 8]
    blocks :=
      [ { stmts :=
            [ .assign ⟨⟨0⟩, []⟩ (.use (.constVal (.int valToStore))) ]
          terminator := .return_
        }
      ]
  }

/-- `MirBody.localTys` enforces declared local types and `uint` bit-width bounds
in `assignPlace`. -/
theorem mir_localTys_uint8_bounds_enforced :
    (match runMirSteps (mirTypedUint8Body 255) 3
        ⟨[some .uninit], [0], 0, 0⟩ with
     | .returned ret => ret.value = .int 255
     | _ => False) ∧
    runMirSteps (mirTypedUint8Body 256) 3
      ⟨[some .uninit], [0], 0, 0⟩ = .fault := by
  exact ⟨rfl, rfl⟩

/-- Test body for `mir_copy_switch_unreachable_and_binops_tests`. -/
def mirCopyAndSwitchBody (sel : Nat) : MirBody :=
  { argCount := 0
    localCount := 4
    ptrWidthBits := 64
    localTys := [.usize, .usize, .ref .usize, .usize]
    blocks :=
      [ { stmts :=
            [ .nop
            , .storageLive ⟨1⟩
            , .assign ⟨⟨1⟩, []⟩ (.use (.constVal (.int 15)))
            , .storageLive ⟨2⟩
            , .assign ⟨⟨2⟩, []⟩ (.ref ⟨⟨1⟩, []⟩)
            , .storageLive ⟨3⟩
            , .assign ⟨⟨3⟩, []⟩ (.use (.constVal (.int sel)))
            ]
          terminator :=
            .switchInt (.copy ⟨⟨3⟩, []⟩)
              { branches := [⟨1, ⟨1⟩⟩], otherwise := ⟨2⟩ }
        }
      , { stmts :=
            [ .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨2⟩, [.deref]⟩))
            , .storageDead ⟨2⟩
            , .storageDead ⟨1⟩
            ]
          terminator := .return_
        }
      , { stmts := []
          terminator := .unreachable
        }
      ]
  }

/-- Exhaustive unit tests for `Rvalue.use`, `Stmt.nop`,
`Terminator.switchInt` (matched branch vs. `otherwise`),
`Terminator.unreachable`, and remaining `BinOp` operators (`.mul`, `.eq`, `.ne`,
`.lt`, `.le`, `.gt`, `.ge`, and boolean `.bitAnd` / `.bitOr` / `.bitXor`). -/
theorem mir_copy_switch_unreachable_and_binops_tests :
    (match runMirSteps (mirCopyAndSwitchBody 1) 12
        ⟨[some .uninit, none, none, none], [0, 0, 0, 0], 0, 0⟩ with
     | .returned ret => ret.value = .int 15
     | _ => False) ∧
    runMirSteps (mirCopyAndSwitchBody 99) 12
      ⟨[some .uninit, none, none, none], [0, 0, 0, 0], 0, 0⟩ = .fault ∧
    evalBinOp .mul (.int 6) (.int 7) (some 8) = some (.int 42) ∧
    evalBinOp .eq (.int 5) (.int 5) = some (.bool true) ∧
    evalBinOp .ne (.int 5) (.int 6) = some (.bool true) ∧
    evalBinOp .lt (.int 3) (.int 5) = some (.bool true) ∧
    evalBinOp .le (.int 5) (.int 5) = some (.bool true) ∧
    evalBinOp .gt (.int 7) (.int 2) = some (.bool true) ∧
    evalBinOp .ge (.int 7) (.int 7) = some (.bool true) ∧
    evalBinOp .bitAnd (.bool true) (.bool false) = some (.bool false) ∧
    evalBinOp .bitOr (.bool true) (.bool false) = some (.bool true) ∧
    evalBinOp .bitXor (.bool true) (.bool true) = some (.bool false) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Test body for `mir_ref_encoding_widths_wrapping_and_reborrow_tests`. -/
def mirTypedUint8WrapBody : MirBody :=
  { argCount := 0
    localCount := 3
    ptrWidthBits := 64
    localTys := [.uint 8, .uint 8, .uint 8]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .storageLive ⟨2⟩
            , .assign ⟨⟨1⟩, []⟩ (.use (.constVal (.int 0)))
            , .assign ⟨⟨2⟩, []⟩
                (.binaryOp .sub (.copy ⟨⟨1⟩, []⟩) (.constVal (.int 1)))
            , .assign ⟨⟨0⟩, []⟩
                (.binaryOp .add (.copy ⟨⟨2⟩, []⟩) (.constVal (.int 2)))
            ]
          terminator := .return_
        }
      ]
  }

/-- Reborrows `*_2` into the argument local `_1`, writes through it, and returns
the written value. -/
def mirReborrowIntoArgSlotBody : MirBody :=
  { argCount := 2
    localCount := 3
    ptrWidthBits := 64
    localTys := [.usize, .refMut .usize, .refMut .usize, .usize, .usize]
    blocks :=
      [ { stmts :=
            [ .assign ⟨⟨1⟩, []⟩ (.refMut ⟨⟨2⟩, [.deref]⟩)
            , .assign ⟨⟨1⟩, [.deref]⟩ (.use (.constVal (.int 88)))
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, [.deref]⟩))
            ]
          terminator := .return_
        }
      ]
  }

/-- Regression tests for:
1. `mirValAlg.encodeSharedRef` (`isMut = false`) and `remapRefInVal` preserving
   `isMut`, `refGen`, and `reborrowDepth` inside nested `.adt` / `.fieldCons`
   aggregates,
2. `extractMirFuncOut` rejecting `.uninit` or stale/retired references in
   caller-owned referent slots,
3. the pointer width (e.g. a `16`-bit target) fixing the `.usize` bit width,
   value bounds, and bitwise complement,
4. wrapping unsigned arithmetic at width 8: `0 - 1 + 2 = 1` through typed
   `.uint 8` locals, and `255 + 1 = 0` and `16 * 16 = 0` in `evalBinOp`, and
5. Intra-function reborrowing into an argument local (`_1 = &mut *_2`,
   `reborrowDepth = 1`) succeeding without faulting in `entryArgsExclusive`. -/
theorem mir_ref_encoding_widths_wrapping_and_reborrow_tests :
    -- 1. `encodeSharedRef` vs `encodeRef` and `remapRefInVal` on nested `.adt`:
    mirValAlg.encodeSharedRef 3 [0] = .ref false 0 ⟨3⟩ [0] 0 ∧
    mirValAlg.remapRefInVal 3 9
      (.adt 0 (.fieldCons (.ref false 2 ⟨3⟩ [1] 4) .unit)) =
      .adt 0 (.fieldCons (.ref false 2 ⟨9⟩ [1] 4) .unit) ∧
    -- 2. `extractMirFuncOut` rejects `.uninit` and dangling references in
    -- caller slots:
    extractMirFuncOut [1]
      ⟨.unit, ⟨[some .unit, some .uninit], [0, 0], 0, 0⟩⟩ = none ∧
    extractMirFuncOut [1]
      ⟨.unit,
       ⟨[some .unit, some (.ref true 1 ⟨0⟩ [] 0)], [0, 0], 0, 0⟩⟩ =
      none ∧
    -- A retired reference (target `localGens.length`) is rejected too:
    extractMirFuncOut [1]
      ⟨.unit,
       ⟨[some .unit, some (.ref true 0 ⟨2⟩ [] 0)], [0, 0], 0, 0⟩⟩ =
      none ∧
    -- 3. `ptrWidthBits` parameterizes `tyBitWidth` and `checkValMatchesTy`:
    tyBitWidth 32 .usize = some 32 ∧
    checkValMatchesTy 16 .usize (.int 65535) false [] [] = true ∧
    checkValMatchesTy 16 .usize (.int 65536) false [] [] = false ∧
    tyBitWidth 16 .usize = some 16 ∧
    evalUnOp .not (some 16) (.int 0) = some (.int 65535) ∧
    -- 4. Wrapping `.sub` and `.add` on typed `.uint 8` locals
    -- (`0 - 1 + 2 = 1`):
    (match runMirSteps mirTypedUint8WrapBody 7
        ⟨[some .uninit, none, none], [0, 0, 0], 0, 0⟩ with
     | .returned ret => ret.value = .int 1
     | _ => False) ∧
    evalBinOp .add (.int 255) (.int 1) (some 8) = some (.int 0) ∧
    evalBinOp .mul (.int 16) (.int 16) (some 8) = some (.int 0) ∧
    -- 5. Reborrowing `_1 = &mut *_2` into an argument local succeeds:
    (match runMirSteps mirReborrowIntoArgSlotBody 5
        ⟨[some .uninit,
          some (.ref true 0 ⟨3⟩ [] 0),
          some (.ref true 0 ⟨4⟩ [] 0),
          some (.int 10),
          some (.int 20)],
         [0, 0, 0, 0, 0], 0, 0⟩ with
     | .returned ret =>
       extractMirFuncOut [3, 4] ret = some ⟨.int 88, [.int 10, .int 88]⟩
     | _ => False) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Test body for `mir_tuple_typing_entry_validity_and_return_tests`. -/
def mirProjectedTupleFieldBody : MirBody :=
  { argCount := 0
    localCount := 2
    ptrWidthBits := 64
    localTys := [.uint 8, .tuple [.uint 8, .uint 16]]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .assign ⟨⟨1⟩, []⟩
                (.use (.constVal
                  (.fieldCons (.int 255) (.fieldCons (.int 1000) .unit))))
            , .assign ⟨⟨1⟩, [.field 0]⟩
                (.binaryOp .add
                  (.copy ⟨⟨1⟩, [.field 0]⟩)
                  (.constVal (.int 1)))
            , .assign ⟨⟨0⟩, []⟩ (.unaryOp .not (.copy ⟨⟨1⟩, [.field 0]⟩))
            ]
          terminator := .return_
        }
      ]
  }

/-- Returns a reference to one of its own locals. -/
def mirReturnFrameRefBody : MirBody :=
  { argCount := 0
    localCount := 2
    ptrWidthBits := 64
    localTys := [.ref .usize, .usize]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .assign ⟨⟨1⟩, []⟩ (.use (.constVal (.int 7)))
            , .assign ⟨⟨0⟩, []⟩ (.ref ⟨⟨1⟩, []⟩)
            ]
          terminator := .return_
        }
      ]
  }

/-- Regression tests for MIR and bridge invariants:
1. Projected tuple field width inference (`_1.0` where `_1 : (u8, u16)` wraps
   `255 + 1` to `0` and computes `8`-bit `!0 = 255`),
2. Recursive tuple type checking in `checkValMatchesTy` (accepting matching
   element types/arity and rejecting mismatched element types or wrong arity),
3. Entry argument exclusivity and validity (`entryArgsExclusive`) rejecting
   aliased mutable references nested inside a tuple argument and a dangling
   (stale-generation) reference argument, while accepting the same arguments
   with distinct targets and the current generation,
4. `stepTerminator` at `Terminator.return_` rejecting return values that
   contain a reference into the returning frame (`targetLoc.index <
   body.localCount`); returning a caller-owned reference is accepted in
   `mir_adt_typing_field_init_and_ref_return_tests` (item 6), and
5. Boolean relational comparisons (`.lt`, `.le`, `.gt`, `.ge`) in `evalBinOp`.
-/
theorem mir_tuple_typing_entry_validity_and_return_tests :
    -- 1. Projected tuple field `u8` wrapping `.add` and `.not`:
    (match runMirSteps mirProjectedTupleFieldBody 6
        ⟨[some .uninit, none], [0, 0], 0, 0⟩ with
     | .returned ret => ret.value = .int 255
     | _ => False) ∧
    -- 2. Recursive tuple validation in `checkValMatchesTy`:
    checkValMatchesTy 64 (.tuple [.uint 8, .bool])
      (.fieldCons (.int 200) (.fieldCons (.bool true) .unit))
        false [] [] = true ∧
    checkValMatchesTy 64 (.tuple [.uint 8])
      (.fieldCons (.bool true) (.fieldCons (.int 1) .unit))
        false [] [] = false ∧
    checkValMatchesTy 64 (.tuple [.uint 8, .bool])
      (.fieldCons (.int 300) (.fieldCons (.bool true) .unit))
        false [] [] = false ∧
    -- 3. `entryArgsExclusive` rejects nested aliased `&mut` inside a tuple arg
    -- and rejects a dangling reference argument at entry:
    entryArgsExclusive
      { argCount := 1, localCount := 2, ptrWidthBits := 64,
        localTys :=
          [.usize, .tuple [.refMut .usize, .refMut .usize], .usize, .usize],
        blocks := [] }
      ⟨[some .uninit,
        some (.fieldCons (.ref true 0 ⟨2⟩ [] 0)
          (.fieldCons (.ref true 0 ⟨2⟩ [] 0) .unit)),
        some (.int 1), some (.int 2)],
       [0, 0, 0, 0], 0, 0⟩ = false ∧
    entryArgsExclusive
      { argCount := 1, localCount := 2, ptrWidthBits := 64,
        localTys :=
          [.usize, .tuple [.refMut .usize, .refMut .usize], .usize, .usize],
        blocks := [] }
      ⟨[some .uninit,
        some (.fieldCons (.ref true 0 ⟨2⟩ [] 0)
          (.fieldCons (.ref true 0 ⟨3⟩ [] 0) .unit)),
        some (.int 1), some (.int 2)],
       [0, 0, 0, 0], 0, 0⟩ = true ∧
    entryArgsExclusive
      { argCount := 1, localCount := 2, ptrWidthBits := 64,
        localTys := [.usize, .ref .usize, .usize], blocks := [] }
      ⟨[some .uninit, some (.ref false 1 ⟨2⟩ [] 0), some (.int 1)],
       [0, 0, 0], 0, 0⟩ = false ∧
    entryArgsExclusive
      { argCount := 1, localCount := 2, ptrWidthBits := 64,
        localTys := [.usize, .ref .usize, .usize], blocks := [] }
      ⟨[some .uninit, some (.ref false 0 ⟨2⟩ [] 0), some (.int 1)],
       [0, 0, 0], 0, 0⟩ = true ∧
    -- 4. Returning a reference to an in-frame local (`_1 < localCount`) faults:
    runMirSteps mirReturnFrameRefBody 6
      ⟨[some .uninit, none], [0, 0], 0, 0⟩ = .fault ∧
    -- 5. Boolean relational comparisons (`false < true`):
    evalBinOp .lt (.bool false) (.bool true) = some (.bool true) ∧
    evalBinOp .lt (.bool true) (.bool false) = some (.bool false) ∧
    evalBinOp .le (.bool true) (.bool true) = some (.bool true) ∧
    evalBinOp .gt (.bool true) (.bool false) = some (.bool true) ∧
    evalBinOp .ge (.bool false) (.bool true) = some (.bool false) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl⟩

/-- `MirBody` with an `.adt 0 [.uint 8, .uint 16]` local whose `.field 0` wraps
at 8 bits (`255 + 1 = 0`). -/
def mirProjectedAdtFieldBody : MirBody :=
  { argCount := 0
    localCount := 2
    ptrWidthBits := 64
    localTys := [.uint 8, .adt 0 [.uint 8, .uint 16]]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .assign ⟨⟨1⟩, []⟩
                (.use (.constVal
                  (.adt 0 (.fieldCons (.int 255)
                    (.fieldCons (.int 1000) .unit)))))
            , .assign ⟨⟨1⟩, [.field 0]⟩
                (.binaryOp .add
                  (.copy ⟨⟨1⟩, [.field 0]⟩)
                  (.constVal (.int 1)))
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, [.field 0]⟩))
            ]
          terminator := .return_
        }
      ]
  }

/-- `MirBody` that initializes a 2-field tuple `_1 : (u8, u8)` field-by-field
starting from `.uninit` after `StorageLive(_1)`, then returns `_1`. -/
def mirPartialTupleInitBody : MirBody :=
  { argCount := 0
    localCount := 2
    ptrWidthBits := 64
    localTys := [.tuple [.uint 8, .uint 8], .tuple [.uint 8, .uint 8]]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .assign ⟨⟨1⟩, [.field 0]⟩ (.use (.constVal (.int 10)))
            , .assign ⟨⟨1⟩, [.field 1]⟩ (.use (.constVal (.int 20)))
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, []⟩))
            ]
          terminator := .return_
        }
      ]
  }

/-- `MirBody` that initializes only `_1.0` of `_1 : (u8, u8)` and attempts to
copy the whole partially initialized tuple `_1` into `_0` (must fault). -/
def mirPartialTupleReadUninitBody : MirBody :=
  { argCount := 0
    localCount := 2
    ptrWidthBits := 64
    localTys := [.tuple [.uint 8, .uint 8], .tuple [.uint 8, .uint 8]]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .assign ⟨⟨1⟩, [.field 0]⟩ (.use (.constVal (.int 10)))
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, []⟩))
            ]
          terminator := .return_
        }
      ]
  }

/-- Reference-returning `MirBody` for `select_mut_ref(flag, x, y) -> &mut usize`
that reborrows either `*_2` (`x` in caller slot `4`) or `*_3` (`y` in caller
slot `5`) into `_0` and returns `_0`. -/
def mirSelectMutRefBody : MirBody :=
  { argCount := 3
    localCount := 4
    ptrWidthBits := 64
    localTys :=
      [ .refMut .usize
      , .bool
      , .refMut .usize
      , .refMut .usize
      , .usize
      , .usize
      ]
    blocks :=
      [ { stmts := []
          terminator :=
            .switchInt (.copy ⟨⟨1⟩, []⟩)
              { branches := [⟨0, ⟨2⟩⟩], otherwise := ⟨1⟩ }
        }
      , { stmts := [.assign ⟨⟨0⟩, []⟩ (.refMut ⟨⟨2⟩, [.deref]⟩)]
          terminator := .return_
        }
      , { stmts := [.assign ⟨⟨0⟩, []⟩ (.refMut ⟨⟨3⟩, [.deref]⟩)]
          terminator := .return_
        }
      ]
  }

/-- Regression tests for MIR and bridge invariants:
1. `MirTy.adt` field-type projection and recursive validation in
   `projectFieldPathTy` and `checkValMatchesTy` (plus 8-bit wrapping arithmetic
   on an `.adt 0 [.uint 8, .uint 16]` field),
2. `entryArgsExclusive` pointee and nested-ADT reference validation (rejecting
   out-of-range pointee values and nested aliased `&mut` inside `.adt`),
3. `entryArgsExclusive` scalar argument validation (rejecting ill-typed scalar
   arguments before the first step),
4. Field-by-field initialization of an `.uninit` tuple/ADT local (accepting
   complete field initialization and rejecting reads of partially initialized
   aggregates),
5. `PlaceMention` projected path validation (accepting allocated `.uninit` root
   locals while rejecting invalid or out-of-bounds field projections), and
6. `extractMirFuncOut` normalizes a returned reference to the root `LoanId`
   of its caller slot (`loanId = 0` for caller slot `4`, `loanId = 1` for
   caller slot `5`, `reborrowDepth = 0`). -/
theorem mir_adt_typing_field_init_and_ref_return_tests :
    -- 1. `MirTy.adt` field projection and `checkValMatchesTy`:
    projectFieldPathTy [0] (.adt 0 [.uint 8, .bool]) = some (.uint 8) ∧
    projectFieldPathTy [1] (.adt 0 [.uint 8, .bool]) = some .bool ∧
    projectFieldPathTy [2] (.adt 0 [.uint 8, .bool]) = none ∧
    checkValMatchesTy 64 (.adt 0 [.uint 8, .bool])
      (.adt 0 (.fieldCons (.int 200) (.fieldCons (.bool true) .unit)))
        false [] [] = true ∧
    checkValMatchesTy 64 (.adt 0 [.uint 8, .bool])
      (.adt 0 (.fieldCons (.int 300) (.fieldCons (.bool true) .unit)))
        false [] [] = false ∧
    checkValMatchesTy 64 (.adt 0 [.uint 8, .bool])
      (.adt 0 (.fieldCons (.int 200) .unit)) false [] [] = false ∧
    (match runMirSteps mirProjectedAdtFieldBody 6
        ⟨[some .uninit, none], [0, 0], 0, 0⟩ with
     | .returned ret => ret.value = .int 0
     | _ => False) ∧
    -- 2. `entryArgsExclusive` checks pointee types and nested `.adt` refs:
    entryArgsExclusive
      { argCount := 1, localCount := 2, ptrWidthBits := 64,
        localTys := [.usize, .refMut (.uint 8), .uint 8], blocks := [] }
      ⟨[some .uninit, some (.ref true 0 ⟨2⟩ [] 0), some (.int 200)],
       [0, 0, 0], 0, 0⟩ = true ∧
    entryArgsExclusive
      { argCount := 1, localCount := 2, ptrWidthBits := 64,
        localTys := [.usize, .refMut (.uint 8), .uint 8], blocks := [] }
      ⟨[some .uninit, some (.ref true 0 ⟨2⟩ [] 0), some (.int 300)],
       [0, 0, 0], 0, 0⟩ = false ∧
    entryArgsExclusive
      { argCount := 1, localCount := 2, ptrWidthBits := 64,
        localTys := [.usize, .adt 0 [.refMut .usize, .refMut .usize], .usize],
        blocks := [] }
      ⟨[some .uninit,
        some (.adt 0 (.fieldCons (.ref true 0 ⟨2⟩ [] 0)
          (.fieldCons (.ref true 0 ⟨2⟩ [] 0) .unit))),
        some (.int 1)],
       [0, 0, 0], 0, 0⟩ = false ∧
    -- 3. `entryArgsExclusive` rejects ill-typed scalar arguments at entry:
    entryArgsExclusive
      { argCount := 1, localCount := 2, ptrWidthBits := 64,
        localTys := [.uint 8, .uint 8], blocks := [] }
      ⟨[some .uninit, some (.int 300)], [0, 0], 0, 0⟩ = false ∧
    -- 4. Partial aggregate field initialization on `.uninit` local:
    (match runMirSteps mirPartialTupleInitBody 6
        ⟨[some .uninit, none], [0, 0], 0, 0⟩ with
     | .returned ret =>
       ret.value = .fieldCons (.int 10) (.fieldCons (.int 20) .unit)
     | _ => False) ∧
    runMirSteps mirPartialTupleReadUninitBody 6
      ⟨[some .uninit, none], [0, 0], 0, 0⟩ = .fault ∧
    -- 5. `PlaceMention` accepts allocated `.uninit` root local and rejects
    -- invalid field projections:
    stepStmt
      { argCount := 0, localCount := 2, ptrWidthBits := 64,
        localTys := [.usize, .tuple [.uint 8, .uint 8]], blocks := [] }
      ⟨[some .uninit, some .uninit], [0, 0], 0, 0⟩
      (.placeMention ⟨⟨1⟩, []⟩) =
      .stepped ⟨[some .uninit, some .uninit], [0, 0], 0, 1⟩ ∧
    stepStmt
      { argCount := 0, localCount := 2, ptrWidthBits := 64,
        localTys := [.usize, .tuple [.uint 8, .uint 8]], blocks := [] }
      ⟨[some .uninit, some .uninit], [0, 0], 0, 0⟩
      (.placeMention ⟨⟨1⟩, [.field 3]⟩) = .fault ∧
    stepStmt
      { argCount := 0, localCount := 2, ptrWidthBits := 64,
        localTys := [.usize, .usize], blocks := [] }
      ⟨[some .uninit, some (.int 5)], [0, 0], 0, 0⟩
      (.placeMention ⟨⟨1⟩, [.field 0]⟩) = .fault ∧
    -- 6. Reference-returning `MirBody` normalized by `extractMirFuncOut`:
    (match runMirSteps mirSelectMutRefBody 4
        ⟨[some .uninit, some (.bool true),
          some (.ref true 0 ⟨4⟩ [] 0), some (.ref true 0 ⟨5⟩ [] 0),
          some (.int 11), some (.int 22)],
         [0, 0, 0, 0, 0, 0], 0, 0⟩ with
     | .returned ret =>
       extractMirFuncOut [4, 5] ret =
         some ⟨.ref true 0 ⟨0⟩ [] 0, [.int 11, .int 22]⟩
     | _ => False) ∧
    (match runMirSteps mirSelectMutRefBody 4
        ⟨[some .uninit, some (.bool false),
          some (.ref true 0 ⟨4⟩ [] 0), some (.ref true 0 ⟨5⟩ [] 0),
          some (.int 11), some (.int 22)],
         [0, 0, 0, 0, 0, 0], 0, 0⟩ with
     | .returned ret =>
       extractMirFuncOut [4, 5] ret =
         some ⟨.ref true 0 ⟨1⟩ [] 0, [.int 11, .int 22]⟩
     | _ => False) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Regression tests for MIR and bridge invariants:
1. Zero-field `MirTy.adt id []` requires a `.unit` spine in
   `checkValMatchesTy`,
2. `entryArgsExclusive` rejects entry references pointing to in-frame locals
   (`targetLoc.index < body.localCount`) and recursively validates references
   nested inside dereferenced pointee values (`&(&mut x, &mut x)`),
3. `assignPlace` enforces declared reference pointee types (`_1 : &mut u8`) on
   dereferenced writes to caller-owned slots even when `localTys` omits caller
   slot entries,
4. `stepTerminator` at `Terminator.return_` enforces `localTys` on `_0`, and
5. `extractCallerSlotVals` normalizes references stored inside caller `&mut`
   slots and `extractMirPlaceFuncOut` extracts disjoint sub-place borrows
   `[(slotIdx, [0]), (slotIdx, [1])]` of a single caller aggregate slot. -/
theorem mir_zero_field_adt_entry_refs_and_extraction_tests :
    -- 1. Zero-field `.adt 0 []` requires `.unit` spine:
    checkValMatchesTy 64 (.adt 0 []) (.adt 0 .unit) false [] [] = true ∧
    checkValMatchesTy 64 (.adt 0 []) (.adt 0 (.int 42)) false [] [] = false ∧
    -- 2. `entryArgsExclusive` rejects in-frame targetLoc (`0 < localCount`) and
    -- recursively detects aliased `&mut` references behind a shared reference:
    entryArgsExclusive
      { argCount := 1, localCount := 2, ptrWidthBits := 64,
        localTys := [.usize, .ref .usize], blocks := [] }
      ⟨[some (.int 1), some (.ref false 0 ⟨0⟩ [] 0)], [0, 0], 0, 0⟩ =
      false ∧
    entryArgsExclusive
      { argCount := 1, localCount := 2, ptrWidthBits := 64,
        localTys :=
          [.usize, .ref (.tuple [.refMut .usize, .refMut .usize]),
           .tuple [.refMut .usize, .refMut .usize], .usize],
        blocks := [] }
      ⟨[some .uninit,
        some (.ref false 0 ⟨2⟩ [] 0),
        some (.fieldCons (.ref true 0 ⟨3⟩ [] 0)
          (.fieldCons (.ref true 0 ⟨3⟩ [] 0) .unit)),
        some (.int 5)],
       [0, 0, 0, 0], 0, 0⟩ = false ∧
    -- 3. `assignPlace` enforces `.refMut (.uint 8)` on deref write to caller
    -- slot `2` even when `localTys` only lists in-frame locals `0` and `1`:
    assignPlace
      { argCount := 1, localCount := 2, ptrWidthBits := 64,
        localTys := [.usize, .refMut (.uint 8)], blocks := [] }
      ⟨[some .uninit, some (.ref true 0 ⟨2⟩ [] 0), some (.int 10)],
       [0, 0, 0], 0, 0⟩
      ⟨⟨1⟩, [.deref]⟩
      (.int 300) = none ∧
    -- 4. `stepTerminator` at `.return_` rejects ill-typed pre-populated `_0`:
    stepTerminator
      { argCount := 0, localCount := 1, ptrWidthBits := 64,
        localTys := [.uint 8], blocks := [] }
      ⟨[some (.int 300)], [0], 0, 0⟩
      .return_ = .fault ∧
    -- 5. `extractMirFuncOut` normalizes references stored in caller `&mut`
    -- slots, and `extractMirPlaceFuncOut` extracts disjoint sub-place borrows
    -- `[(2, [0]), (2, [1])]` of a single caller aggregate slot:
    extractMirFuncOut [2, 3]
      ⟨.unit,
       ⟨[some .unit, none,
         some (.ref false 5 ⟨3⟩ [0] 2),
         some (.fieldCons (.int 77) .unit)],
        [0, 0, 0, 5], 0, 0⟩⟩ =
      some ⟨.unit, [.ref false 0 ⟨1⟩ [0] 0, .fieldCons (.int 77) .unit]⟩ ∧
    extractMirPlaceFuncOut [(2, [0]), (2, [1])]
      ⟨.ref true 0 ⟨2⟩ [1] 1,
       ⟨[some .unit, none,
         some (.fieldCons (.int 11) (.fieldCons (.int 22) .unit))],
        [0, 0, 0], 0, 0⟩⟩ =
      some ⟨.ref true 0 ⟨1⟩ [] 0, [.int 11, .int 22]⟩ := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Regression tests for MIR and bridge invariants:
1. `stepTerminator` at `.return_` does not inspect caller-owned slots
   (`idx ≥ body.localCount`), even one holding a frame-local reference, which
   `assignPlace` never stores there,
2. `checkValMatchesTy` and `assignPlace` reject storing a reference to a `.bool`
   local into a slot declared as `.ref .usize`,
3. `runMirSteps` runs entry validation before the first step and refuses to
   start from a non-entry PC (`block != 0 || stmtIdx != 0`), so no caller can
   skip entry validation,
4. `Rvalue.use (.copy p) .no` copies a stored reference unchanged, while
   `Rvalue.use (.copy p) .yes` retags it (`reborrowDepth` increases by one;
   `mir_entry_frame_widths_and_retag_tests` covers the retag's access), and
5. Repeated `Stmt.storageDead` on an already-dead local (`some none`) is a
   no-op that does not increment `localGens`. -/
theorem mir_store_typing_entry_pc_retag_and_storage_tests :
    -- 1. `.return_` does not inspect caller slot `2`, even when it holds a
    -- frame-local reference (`assignPlace` keeps such references out):
    stepTerminator
      { argCount := 1, localCount := 2, ptrWidthBits := 64,
        localTys := [.unit, .usize], blocks := [] }
      ⟨[some .unit, some (.int 1), some (.ref false 0 ⟨1⟩ [] 0)],
       [0, 0, 0], 0, 0⟩
      .return_ =
      .returned
        ⟨.unit,
         ⟨[some .unit, some (.int 1), some (.ref false 0 ⟨1⟩ [] 0)],
          [0, 0, 0], 0, 0⟩⟩ ∧
    -- 2. `checkValMatchesTy` rejects reference to `.bool` local for `&usize`:
    checkValMatchesTy 64 (.ref .usize) (.ref false 0 ⟨1⟩ [] 0) false
      [.ref .usize, .bool] [] = false ∧
    -- 3. `runMirSteps` validates the entry state, and rejects a non-entry
    -- starting PC even from a state that is valid at entry (which, started
    -- at the entry PC, runs and faults at the uninitialized `u8` return):
    runMirSteps
      { argCount := 1, localCount := 2, ptrWidthBits := 64,
        localTys := [.uint 8, .uint 8],
        blocks := [{ stmts := [.nop, .nop], terminator := .return_ }] } 5
      ⟨[some .uninit, some (.int 300)], [0, 0], 0, 0⟩ = .rejected ∧
    runMirSteps
      { argCount := 1, localCount := 2, ptrWidthBits := 64,
        localTys := [.uint 8, .uint 8],
        blocks := [{ stmts := [.nop, .nop], terminator := .return_ }] } 5
      ⟨[some .uninit, some (.int 3)], [0, 0], 0, 1⟩ = .rejected ∧
    runMirSteps
      { argCount := 1, localCount := 2, ptrWidthBits := 64,
        localTys := [.uint 8, .uint 8],
        blocks := [{ stmts := [.nop, .nop], terminator := .return_ }] } 5
      ⟨[some .uninit, some (.int 3)], [0, 0], 0, 0⟩ = .fault ∧
    -- 4. `Rvalue.use (.copy _) .no` copies a reference unchanged, while
    -- `.yes` retags it one reborrow level deeper:
    evalRvalue
      { argCount := 0, localCount := 3, ptrWidthBits := 64,
        localTys := [.unit, .usize, .refMut .usize], blocks := [] }
      ⟨⟨2⟩, []⟩
      ⟨[some .uninit, some (.int 42), some (.ref true 0 ⟨1⟩ [] 0)],
       [0, 0, 0], 0, 0⟩
      (.use (.copy ⟨⟨2⟩, []⟩) .no) =
      some (.ref true 0 ⟨1⟩ [] 0,
            ⟨[some .uninit, some (.int 42), some (.ref true 0 ⟨1⟩ [] 0)],
             [0, 0, 0], 0, 0⟩) ∧
    evalRvalue
      { argCount := 0, localCount := 3, ptrWidthBits := 64,
        localTys := [.unit, .usize, .refMut .usize], blocks := [] }
      ⟨⟨2⟩, []⟩
      ⟨[some .uninit, some (.int 42), some (.ref true 0 ⟨1⟩ [] 0)],
       [0, 0, 0], 0, 0⟩
      (.use (.copy ⟨⟨2⟩, []⟩) .yes) =
      some (.ref true 0 ⟨1⟩ [] 1,
            ⟨[some .uninit, some (.int 42), some (.ref true 0 ⟨1⟩ [] 0)],
             [0, 0, 0], 0, 0⟩) ∧
    -- 5. Repeated `StorageDead` on a dead local is a no-op:
    stepStmt
      { argCount := 0, localCount := 2, ptrWidthBits := 64, blocks := [] }
      ⟨[some .uninit, none], [0, 3], 0, 0⟩
      (.storageDead ⟨1⟩) =
      .stepped ⟨[some .uninit, none], [0, 3], 0, 1⟩ := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Extraction normalizes a returned reference to a caller slot to the first
root loan that names that slot: with two shared roots naming caller slot `2`
(`refSlots = [2, 2]`), the returned reference becomes loan `0`. -/
theorem mir_extract_normalizes_aliased_shared_roots :
    extractMirFuncOut []
      ⟨.ref false 0 ⟨2⟩ [] 0,
       ⟨[some (.ref false 0 ⟨2⟩ [] 0), some (.ref false 0 ⟨2⟩ [] 0),
         some (.ref false 0 ⟨2⟩ [] 0), some (.int 9)],
        [0, 0, 0, 0], 0, 0⟩⟩ [2, 2] =
      some ⟨.ref false 0 ⟨0⟩ [] 0, []⟩ :=
  rfl

/-- `fn f(s: &mut (&mut u8,)) -> u8 { *s.0 }` as emitted in
`Runtime(PostCleanup)`: a compiler temporary `_2 = copy ((*_1).0)` followed by
a read through `*_2`. -/
def mirCompilerCopyDerefBody : MirBody :=
  { argCount := 1
    localCount := 3
    ptrWidthBits := 64
    localTys :=
      [.uint 8, .refMut (.tuple [.refMut (.uint 8)]), .refMut (.uint 8),
       .tuple [.refMut (.uint 8)], .uint 8]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨2⟩
            , .assign ⟨⟨2⟩, []⟩
                (.use (.copy ⟨⟨1⟩, [.deref, .field 0]⟩) .no)
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨2⟩, [.deref]⟩) .yes)
            , .storageDead ⟨2⟩
            ]
          terminator := .return_
        }
      ]
  }

/-- Entry state for `mirCompilerCopyDerefBody`: `_1` points to caller slot `3`
holding `(&mut x,)`, and caller slot `4` holds `x = 7`. -/
def mirCompilerCopyDerefInitState : MirState :=
  ⟨[some .uninit, some (.ref true 0 ⟨3⟩ [] 0), none,
    some (.fieldCons (.ref true 0 ⟨4⟩ [] 0) .unit), some (.int 7)],
   [0, 0, 0, 0, 0], 0, 0⟩

/-- Shared-reference argument signature `f(a: &&mut u8, b: &&mut u8)`, with
caller-owned slot types `callerTys`. -/
def mirSharedOfMutArgsBody (callerTys : List MirTy) : MirBody :=
  { argCount := 2
    localCount := 3
    ptrWidthBits := 64
    localTys :=
      [.unit, .ref (.refMut (.uint 8)), .ref (.refMut (.uint 8))] ++ callerTys
    blocks := []
  }

/-- Loop whose back edge re-enters the loop header `bb1` after moving out of
argument `_1`: `bb0` jumps to `bb1`; `bb1` switches on argument `_2`; `bb2`
sets `_2 = 1`, moves `_1` into `_0`, and jumps back to `bb1`; `bb3` returns.
Re-running entry validation at the back edge would reject the
now-uninitialized `_1`. -/
def mirBackEdgeAfterMoveBody : MirBody :=
  { argCount := 2
    localCount := 3
    ptrWidthBits := 64
    localTys := [.uint 8, .uint 8, .uint 8]
    blocks :=
      [ { stmts := [], terminator := .goto ⟨1⟩ }
      , { stmts := []
          terminator :=
            .switchInt (.copy ⟨⟨2⟩, []⟩)
              { branches := [⟨0, ⟨2⟩⟩], otherwise := ⟨3⟩ }
        }
      , { stmts :=
            [ .assign ⟨⟨2⟩, []⟩ (.use (.constVal (.int 1)))
            , .assign ⟨⟨0⟩, []⟩ (.use (.move ⟨⟨1⟩, []⟩))
            ]
          terminator := .goto ⟨1⟩
        }
      , { stmts := [], terminator := .return_ }
      ]
  }

/-- Regression tests for MIR and bridge invariants:
1. A compiler copy of a mutable reference used only for a dereference
   (`_2 = copy ((*_1).0)`; `_0 = copy (*_2)`) does not retire the original
   reference stored in the caller's aggregate,
2. `stepTerminator` at `.return_` does not inspect caller-owned slots: it
   returns with an uninitialized caller slot, a dead reference (here one to an
   absent slot), or a live reference to an uninitialized pointee,
3. `entryArgsExclusive` accepts `f(&r, &r)` where `r : &mut u8` lives in one
   caller slot, but rejects `f(&a, &b)` where distinct `a, b : &mut u8` alias,
4. `runMirSteps` refuses non-entry starting PCs, while a loop back edge (to
   the header `bb1`) does not re-run entry validation after the body has moved
   out of an argument, and
5. `extractMirFuncOut` with `refSlots` normalizes a returned shared reference
   to its root `LoanId` without adding the shared referent to `mutFinals` (and
   fails without the table), and preserves loan numbering when a shared loan
   precedes a mutable one. -/
theorem mir_compiler_copy_return_and_back_edge_tests :
    -- 1. Compiler copy through `(*_1).0` preserves `s.0`:
    (match runMirSteps mirCompilerCopyDerefBody 10
        mirCompilerCopyDerefInitState with
     | .returned ret => extractMirFuncOut [3] ret [3, 4]
     | _ => none) =
      some ⟨.int 7, [.fieldCons (.ref true 0 ⟨1⟩ [] 0) .unit]⟩ ∧
    -- 2. `.return_` does not inspect caller-owned slots:
    stepTerminator
      { argCount := 0, localCount := 2, ptrWidthBits := 64,
        localTys := [.usize, .usize], blocks := [] }
      ⟨[some (.int 1), some (.int 0), some .uninit], [0, 0, 0], 0, 0⟩
      .return_ =
      .returned
        ⟨.int 1,
         ⟨[some (.int 1), some (.int 0), some .uninit], [0, 0, 0], 0, 0⟩⟩ ∧
    stepTerminator
      { argCount := 0, localCount := 2, ptrWidthBits := 64,
        localTys := [.usize, .usize], blocks := [] }
      ⟨[some (.int 1), some (.int 0), some (.ref true 0 ⟨3⟩ [] 0)],
       [0, 0, 0], 0, 0⟩
      .return_ =
      .returned
        ⟨.int 1,
         ⟨[some (.int 1), some (.int 0), some (.ref true 0 ⟨3⟩ [] 0)],
          [0, 0, 0], 0, 0⟩⟩ ∧
    stepTerminator
      { argCount := 0, localCount := 2, ptrWidthBits := 64,
        localTys := [.usize, .usize], blocks := [] }
      ⟨[some (.int 1), some (.int 0), some (.ref true 0 ⟨3⟩ [] 0),
        some .uninit],
       [0, 0, 0, 0], 0, 0⟩
      .return_ =
      .returned
        ⟨.int 1,
         ⟨[some (.int 1), some (.int 0), some (.ref true 0 ⟨3⟩ [] 0),
           some .uninit],
          [0, 0, 0, 0], 0, 0⟩⟩ ∧
    stepTerminator
      { argCount := 0, localCount := 2, ptrWidthBits := 64,
        localTys := [.usize, .usize], blocks := [] }
      ⟨[some (.int 1), some (.int 0), some (.ref true 0 ⟨3⟩ [] 0),
        some (.int 4)],
       [0, 0, 0, 0], 0, 0⟩
      .return_ =
      .returned
        ⟨.int 1,
         ⟨[some (.int 1), some (.int 0), some (.ref true 0 ⟨3⟩ [] 0),
           some (.int 4)],
          [0, 0, 0, 0], 0, 0⟩⟩ ∧
    -- 3. One stored `&mut` reached through two shared references is a single
    -- reference; two distinct aliasing `&mut` references still conflict:
    entryArgsExclusive (mirSharedOfMutArgsBody [.refMut (.uint 8), .uint 8])
      ⟨[some .uninit, some (.ref false 0 ⟨3⟩ [] 0),
        some (.ref false 0 ⟨3⟩ [] 0), some (.ref true 0 ⟨4⟩ [] 0),
        some (.int 5)],
       [0, 0, 0, 0, 0], 0, 0⟩ = true ∧
    entryArgsExclusive
      (mirSharedOfMutArgsBody [.refMut (.uint 8), .refMut (.uint 8), .uint 8])
      ⟨[some .uninit, some (.ref false 0 ⟨3⟩ [] 0),
        some (.ref false 0 ⟨4⟩ [] 0), some (.ref true 0 ⟨5⟩ [] 0),
        some (.ref true 0 ⟨5⟩ [] 0), some (.int 5)],
       [0, 0, 0, 0, 0, 0], 0, 0⟩ = false ∧
    -- 4. Back-edges skip entry validation; non-entry starts are rejected:
    (match runMirSteps mirBackEdgeAfterMoveBody 10
        ⟨[some .uninit, some (.int 7), some (.int 0)], [0, 0, 0], 0, 0⟩ with
     | .returned ret => extractMirFuncOut [] ret
     | _ => none) = some ⟨.int 7, []⟩ ∧
    runMirSteps mirBackEdgeAfterMoveBody 10
      ⟨[some (.int 7), some .uninit, some (.int 1)], [0, 0, 0], 0, 0⟩
        = .rejected ∧
    runMirSteps mirBackEdgeAfterMoveBody 10
      ⟨[some .uninit, some (.int 7), some (.int 0)], [0, 0, 0], 1, 0⟩
        = .rejected ∧
    -- 5. Shared-reference normalization is separate from writebacks:
    extractMirFuncOut []
      ⟨.ref false 0 ⟨2⟩ [] 0,
       ⟨[some (.ref false 0 ⟨2⟩ [] 0), some (.ref false 0 ⟨2⟩ [] 0),
         some (.int 9)],
        [0, 0, 0], 0, 0⟩⟩ [2] =
      some ⟨.ref false 0 ⟨0⟩ [] 0, []⟩ ∧
    -- Without the table, the reference has no root `LoanId`, and extraction
    -- fails rather than leaving the slot index in place:
    extractMirFuncOut []
      ⟨.ref false 0 ⟨2⟩ [] 0,
       ⟨[some (.ref false 0 ⟨2⟩ [] 0), some (.ref false 0 ⟨2⟩ [] 0),
         some (.int 9)],
        [0, 0, 0], 0, 0⟩⟩ =
      none ∧
    extractMirFuncOut [4]
      ⟨.ref true 0 ⟨4⟩ [] 0,
       ⟨[some .unit, some (.ref false 0 ⟨3⟩ [] 0), some (.ref true 0 ⟨4⟩ [] 0),
         some (.int 1), some (.int 2)],
        [0, 0, 0, 0, 0], 0, 0⟩⟩ [3, 4] =
      some ⟨.ref true 0 ⟨1⟩ [] 0, [.int 2]⟩ := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `fn f(x: &mut u8)` whose body returns `()` immediately, used to check the
canonical entry state of the temporary `_2 : &mut u8`. -/
def mirEntryTempBody : MirBody :=
  { argCount := 1
    localCount := 3
    ptrWidthBits := 64
    localTys := [.unit, .refMut (.uint 8), .refMut (.uint 8), .uint 8]
    blocks :=
      [ { stmts := [.assign ⟨⟨0⟩, []⟩ (.use (.constVal .unit))]
          terminator := .return_ } ]
  }

/-- Entry state for `mirEntryTempBody` with return slot `ret`, temporary slot
`tmp`, argument `_1` pointing to caller slot `3`, and `x = 5`. -/
def mirEntryTempState (ret tmp : Option MirVal) : MirState :=
  ⟨[ret, some (.ref true 0 ⟨3⟩ [] 0), tmp, some (.int 5)], [0, 0, 0, 0], 0, 0⟩

/-- `fn f()` declaring a local of type `ty` and returning `()` immediately. -/
def mirDeclaresTyBody (ty : MirTy) : MirBody :=
  { argCount := 0
    localCount := 2
    ptrWidthBits := 64
    localTys := [.unit, ty]
    blocks :=
      [ { stmts := [.assign ⟨⟨0⟩, []⟩ (.use (.constVal .unit))]
          terminator := .return_ } ]
  }

/-- `fn f(x: &mut u8)` that copies `_1` into `_2` with retag flag `retag` and
then writes through both: `*_1 = 1; *_2 = 2` when `parentFirst`, and
`*_2 = 2; *_1 = 1` otherwise. -/
def mirRetagCopyBody (retag : WithRetag) (parentFirst : Bool) : MirBody :=
  let writeParent : Stmt := .assign ⟨⟨1⟩, [.deref]⟩ (.use (.constVal (.int 1)))
  let writeChild : Stmt := .assign ⟨⟨2⟩, [.deref]⟩ (.use (.constVal (.int 2)))
  { argCount := 1
    localCount := 3
    ptrWidthBits := 64
    localTys := [.unit, .refMut (.uint 8), .refMut (.uint 8), .uint 8]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨2⟩
            , .assign ⟨⟨2⟩, []⟩ (.use (.copy ⟨⟨1⟩, []⟩) retag)
            ] ++
            (if parentFirst then [writeParent, writeChild]
             else [writeChild, writeParent]) ++
            [ .assign ⟨⟨0⟩, []⟩ (.use (.constVal .unit)) ]
          terminator := .return_ } ]
  }

/-- Entry state for `mirRetagCopyBody`: `_1` points to caller slot `3`, which
holds `x = 0`. -/
def mirRetagCopyInitState : MirState :=
  ⟨[some .uninit, some (.ref true 0 ⟨3⟩ [] 0), none, some (.int 0)],
   [0, 0, 0, 0], 0, 0⟩

/-- Regression tests for `Trusted.MirSemantics`:
1. `entryFrameSlotsCanonical` (checked by `runMirSteps` at entry through
   `entryStateValid`) rejects a temporary that already holds a second `&mut`
   aliasing an argument and a return slot that is already initialized, accepts
   an uninitialized temporary, rejects `argCount ≥ localCount`, and rejects a
   dead temporary that has no `Storage*` statements,
2. `.uint bits` has no bit-width and no inhabitants unless `bits` is a Rust
   integer width, `usize` requires a supported pointer width, and
   `bodyTysSupported` rejects bodies that declare any other width (including
   inside aggregates and pointees) before execution starts,
3. `Rvalue.use _ .yes` retags every copied reference one level deeper and
   performs its access: a write through the parent retires the retagged copy,
   writes through the copy keep the parent, a mutable retag retires a sibling
   reborrow, a shared retag keeps shared siblings, and references in
   aggregate fields are retagged too, while `Rvalue.use _ .no` keeps the
   copy's identity so interleaved writes through both copies succeed. -/
theorem mir_entry_frame_widths_and_retag_tests :
    -- 1. Canonical entry states for non-argument frame slots:
    runMirSteps mirEntryTempBody 5
      (mirEntryTempState (some .uninit) (some (.ref true 0 ⟨3⟩ [] 0)))
        = .rejected ∧
    runMirSteps mirEntryTempBody 5
      (mirEntryTempState (some .unit) (some .uninit)) = .rejected ∧
    runMirSteps mirEntryTempBody 5
      (mirEntryTempState (some .uninit) none) = .rejected ∧
    (runMirSteps mirEntryTempBody 5
      (mirEntryTempState (some .uninit) (some .uninit))).isReturned = true ∧
    entryFrameSlotsCanonical
      { argCount := 1, localCount := 1, ptrWidthBits := 64, blocks := [] }
      ⟨[some .uninit, some (.int 0)], [0, 0], 0, 0⟩ = false ∧
    -- 2. Only Rust integer and pointer widths have semantics:
    tyBitWidth 64 (.uint 1) = none ∧
    tyBitWidth 64 (.uint 128) = some 128 ∧
    tyBitWidth 8 .usize = none ∧
    checkValMatchesTy 64 (.uint 1) (.int 0) false [] [] = false ∧
    checkValMatchesTy 8 .usize (.int 0) false [] [] = false ∧
    bodyTysSupported
      (mirDeclaresTyBody (.tuple [.uint 8, .refMut (.uint 7)])) = false ∧
    bodyTysSupported
      (mirDeclaresTyBody (.adt 0 [.uint 16, .ref .usize])) = true ∧
    bodyTysSupported
      { argCount := 0, localCount := 1, ptrWidthBits := 8, localTys := [.unit],
        blocks := [] } =
      false ∧
    runMirSteps (mirDeclaresTyBody (.uint 1)) 5
      ⟨[some .uninit, some .uninit], [0, 0], 0, 0⟩ = .rejected ∧
    (runMirSteps (mirDeclaresTyBody (.uint 8)) 5
      ⟨[some .uninit, some .uninit], [0, 0], 0, 0⟩).isReturned = true ∧
    -- 3. Retagging copies:
    runMirSteps (mirRetagCopyBody .yes true) 10 mirRetagCopyInitState = .fault ∧
    (match runMirSteps (mirRetagCopyBody .yes false) 10
        mirRetagCopyInitState with
     | .returned ret => extractMirFuncOut [3] ret
     | _ => none) = some ⟨.unit, [.int 1]⟩ ∧
    (match runMirSteps (mirRetagCopyBody .no true) 10
        mirRetagCopyInitState with
     | .returned ret => extractMirFuncOut [3] ret
     | _ => none) = some ⟨.unit, [.int 2]⟩ ∧
    evalRvalue
      { argCount := 0, localCount := 4, ptrWidthBits := 64,
        localTys := [.unit, .refMut .usize, .refMut .usize, .refMut .usize],
        blocks := [] } ⟨⟨3⟩, []⟩
      ⟨[some .uninit, some (.ref true 0 ⟨4⟩ [] 0),
        some (.ref true 0 ⟨4⟩ [] 1), none, some (.int 0)],
       [0, 0, 0, 0, 0], 0, 0⟩
      (.use (.copy ⟨⟨1⟩, []⟩) .yes) =
      some (.ref true 0 ⟨4⟩ [] 1,
            ⟨[some .uninit, some (.ref true 0 ⟨4⟩ [] 0),
              some (.ref true 0 ⟨5⟩ [] 1), none, some (.int 0)],
             [0, 0, 0, 0, 0], 0, 0⟩) ∧
    evalRvalue
      { argCount := 0, localCount := 4, ptrWidthBits := 64,
        localTys := [.unit, .ref .usize, .ref .usize, .ref .usize],
        blocks := [] } ⟨⟨3⟩, []⟩
      ⟨[some .uninit, some (.ref false 0 ⟨4⟩ [] 0),
        some (.ref false 0 ⟨4⟩ [] 1), none, some (.int 0)],
       [0, 0, 0, 0, 0], 0, 0⟩
      (.use (.copy ⟨⟨1⟩, []⟩) .yes) =
      some (.ref false 0 ⟨4⟩ [] 1,
            ⟨[some .uninit, some (.ref false 0 ⟨4⟩ [] 0),
              some (.ref false 0 ⟨4⟩ [] 1), none, some (.int 0)],
             [0, 0, 0, 0, 0], 0, 0⟩) ∧
    evalRvalue
      { argCount := 0, localCount := 3, ptrWidthBits := 64,
        localTys := [.unit, .tuple [.refMut .usize], .tuple [.refMut .usize]],
        blocks := [] } ⟨⟨2⟩, []⟩
      ⟨[some .uninit, some (.fieldCons (.ref true 0 ⟨3⟩ [] 0) .unit), none,
        some (.int 0)],
       [0, 0, 0, 0], 0, 0⟩
      (.use (.move ⟨⟨1⟩, []⟩) .yes) =
      some (.fieldCons (.ref true 0 ⟨3⟩ [] 1) .unit,
            ⟨[some .uninit, some .uninit, none, some (.int 0)],
             [0, 0, 0, 0], 0, 0⟩) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `fn f()` whose body stores the constant `v` into `_0` and returns, with
declared local types `tys`. -/
def mirStoreConstBody (tys : List MirTy) (v : MirVal) : MirBody :=
  { argCount := 0
    localCount := 1
    ptrWidthBits := 64
    localTys := tys
    blocks :=
      [ { stmts := [.assign ⟨⟨0⟩, []⟩ (.use (.constVal v))]
          terminator := .return_ } ]
  }

/-- `fn f(x: T1, y: T2) -> R` whose body evaluates `rv` into `_0` and returns,
with declared local types `tys`. -/
def mirRvalueBody (tys : List MirTy) (rv : Rvalue) : MirBody :=
  { argCount := 2
    localCount := 3
    ptrWidthBits := 64
    localTys := tys
    blocks :=
      [ { stmts := [.assign ⟨⟨0⟩, []⟩ rv]
          terminator := .return_ } ]
  }

/-- `fn f(p: &mut usize)` called with `p = &mut s.1` after the caller moved out
of `s.0`, so caller slot `2` holds `Pair(<uninit>, 5)`. The body runs `stmts`
and returns `()`. -/
def mirPartialCallerBody (stmts : List Stmt) : MirBody :=
  { argCount := 1
    localCount := 2
    ptrWidthBits := 64
    localTys := [.unit, .refMut .usize, mirPairTy]
    blocks :=
      [ { stmts := stmts ++ [.assign ⟨⟨0⟩, []⟩ (.use (.constVal .unit))]
          terminator := .return_ } ]
  }

/-- Entry state for `mirPartialCallerBody`. -/
def mirPartialCallerState : MirState :=
  ⟨[some .uninit, some (.ref true 0 ⟨2⟩ [1] 0),
    some (.adt 0 (.fieldCons .uninit (.fieldCons (.int 5) .unit)))],
   [0, 0, 0], 0, 0⟩

/-- Regression tests for `Trusted.MirSemantics`:
1. `bodyTysSupported` rejects a body that leaves a local without a declared
   type, so an untyped `_0` cannot return an arbitrary integer,
2. constant operands that contain references are rejected
   (`evalOperand`), so a constant cannot forge a reference to a live but
   uninitialized local,
3. `Rvalue.use` requires the operand's declared type to equal the
   destination's (`rvalueTysOk`),
4. binary operations require operands of one declared type, a `bool`
   destination for comparisons and the operand type otherwise, and constants
   that fit the operand type,
5. a call that borrows `&mut s.1` after the caller moved out of `s.0` returns
   normally (also after writing through the borrow), while moving out of a
   place behind a reference faults, and
6. `stepMirCore` does not depend on the PC or re-run entry validation, so the
   loop header `bb1` steps normally after the body has moved out of an
   argument, while `runMirSteps` rejects that state as an entry state. -/
theorem mir_declared_types_partial_moves_and_pc_tests :
    -- 1.
    bodyTysSupported (mirStoreConstBody [] (.int 300)) = false ∧
    runMirSteps (mirStoreConstBody [] (.int 300)) 3
      ⟨[some .uninit], [0], 0, 0⟩ = .rejected ∧
    runMirSteps (mirStoreConstBody [.uint 8] (.int 300)) 3
      ⟨[some .uninit], [0], 0, 0⟩ = .fault ∧
    (runMirSteps (mirStoreConstBody [.uint 8] (.int 7)) 3
      ⟨[some .uninit], [0], 0, 0⟩).isReturned = true ∧
    -- 2.
    evalOperand
      { argCount := 0, localCount := 3, ptrWidthBits := 64, blocks := [] }
      ⟨[some .uninit, none, some .uninit], [0, 0, 1], 0, 0⟩
      (.constVal (.ref false 1 ⟨2⟩ [] 0)) = none ∧
    evalOperand
      { argCount := 0, localCount := 3, ptrWidthBits := 64, blocks := [] }
      ⟨[some .uninit, none, some .uninit], [0, 0, 1], 0, 0⟩
      (.constVal (.int 5)) =
      some (.int 5, ⟨[some .uninit, none, some .uninit], [0, 0, 1], 0, 0⟩) ∧
    runMirSteps
      { argCount := 0, localCount := 3, ptrWidthBits := 64,
        localTys := [.ref (.uint 8), .uint 8, .uint 8],
        blocks :=
          [ { stmts :=
                [ .storageLive ⟨2⟩
                , .assign ⟨⟨0⟩, []⟩ (.use (.constVal (.ref false 1 ⟨2⟩ [] 0)))
                ]
              terminator := .return_ } ] } 4
      ⟨[some .uninit, some .uninit, none], [0, 0, 0], 0, 0⟩ = .fault ∧
    -- 3.
    runMirSteps (mirRvalueBody [.uint 16, .uint 8, .uint 8]
        (.use (.copy ⟨⟨1⟩, []⟩))) 3
      ⟨[some .uninit, some (.int 5), some (.int 6)], [0, 0, 0], 0, 0⟩ = .fault ∧
    (runMirSteps (mirRvalueBody [.uint 8, .uint 8, .uint 8]
        (.use (.copy ⟨⟨1⟩, []⟩))) 3
      ⟨[some .uninit, some (.int 5), some (.int 6)], [0, 0, 0], 0, 0⟩
      ).isReturned = true ∧
    -- 4.
    runMirSteps (mirRvalueBody [.bool, .uint 8, .uint 16]
        (.binaryOp .eq (.copy ⟨⟨1⟩, []⟩) (.copy ⟨⟨2⟩, []⟩))) 3
      ⟨[some .uninit, some (.int 5), some (.int 5)], [0, 0, 0], 0, 0⟩ = .fault ∧
    (match runMirSteps (mirRvalueBody [.bool, .uint 8, .uint 8]
        (.binaryOp .eq (.copy ⟨⟨1⟩, []⟩) (.copy ⟨⟨2⟩, []⟩))) 3
      ⟨[some .uninit, some (.int 5), some (.int 5)], [0, 0, 0], 0, 0⟩ with
     | .returned ret => ret.value = .bool true
     | _ => False) ∧
    runMirSteps (mirRvalueBody [.uint 8, .uint 8, .uint 16]
        (.binaryOp .add (.copy ⟨⟨1⟩, []⟩) (.copy ⟨⟨2⟩, []⟩))) 3
      ⟨[some .uninit, some (.int 5), some (.int 6)], [0, 0, 0], 0, 0⟩ = .fault ∧
    runMirSteps (mirRvalueBody [.bool, .uint 8, .uint 8]
        (.binaryOp .add (.copy ⟨⟨1⟩, []⟩) (.copy ⟨⟨2⟩, []⟩))) 3
      ⟨[some .uninit, some (.int 5), some (.int 6)], [0, 0, 0], 0, 0⟩ = .fault ∧
    rvalueTysOk
      (mirRvalueBody [.bool, .uint 8, .uint 8] (.use (.copy ⟨⟨1⟩, []⟩)))
      ⟨⟨0⟩, []⟩ (.binaryOp .eq (.constVal (.int 1)) (.constVal (.int 1))) =
      false ∧
    rvalueTysOk
      (mirRvalueBody [.uint 8, .uint 8, .uint 8] (.use (.copy ⟨⟨1⟩, []⟩)))
      ⟨⟨0⟩, []⟩ (.binaryOp .add (.copy ⟨⟨1⟩, []⟩) (.constVal (.int 300))) =
      false ∧
    -- 5.
    (runMirSteps (mirPartialCallerBody []) 3 mirPartialCallerState).isReturned =
      true ∧
    (match runMirSteps
        (mirPartialCallerBody
          [.assign ⟨⟨1⟩, [.deref]⟩ (.use (.constVal (.int 9)))]) 4
        mirPartialCallerState with
     | .returned ret => lookupAt ret.state.locals 2 =
         some (some (.adt 0 (.fieldCons .uninit (.fieldCons (.int 9) .unit))))
     | _ => False) ∧
    runMirSteps
      { argCount := 1, localCount := 3, ptrWidthBits := 64,
        localTys := [.unit, .refMut .usize, .usize, mirPairTy],
        blocks :=
          [ { stmts :=
                [ .storageLive ⟨2⟩
                , .assign ⟨⟨2⟩, []⟩ (.use (.move ⟨⟨1⟩, [.deref]⟩))
                , .assign ⟨⟨0⟩, []⟩ (.use (.constVal .unit)) ]
              terminator := .return_ } ] } 5
      ⟨[some .uninit, some (.ref true 0 ⟨3⟩ [1] 0), none,
        some (.adt 0 (.fieldCons .uninit (.fieldCons (.int 5) .unit)))],
       [0, 0, 0, 0], 0, 0⟩ = .fault ∧
    -- 6.
    stepMirCore mirBackEdgeAfterMoveBody
      ⟨[some (.int 7), some .uninit, some (.int 1)], [0, 0, 0], 1, 0⟩ =
      .stepped ⟨[some (.int 7), some .uninit, some (.int 1)], [0, 0, 0], 3, 0⟩ ∧
    runMirSteps mirBackEdgeAfterMoveBody 10
      ⟨[some (.int 7), some .uninit, some (.int 1)], [0, 0, 0], 0, 0⟩
        = .rejected :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl⟩

/-- `fn f(x: u8) -> u8` whose start block ends in `term` and whose `bb1`
returns `_0 = 1` and `bb2` returns `_0 = 2`. -/
def mirCfgBody (term : Terminator) : MirBody :=
  { argCount := 1
    localCount := 2
    ptrWidthBits := 64
    localTys := [.uint 8, .uint 8]
    blocks :=
      [ { stmts := [], terminator := term }
      , { stmts := [.assign ⟨⟨0⟩, []⟩ (.use (.constVal (.int 1)))]
          terminator := .return_ }
      , { stmts := [.assign ⟨⟨0⟩, []⟩ (.use (.constVal (.int 2)))]
          terminator := .goto ⟨0⟩ }
      ]
  }

/-- `mirCfgBody` with `bb2` returning instead of jumping back to `bb0`. -/
def mirCfgBodyNoBack (term : Terminator) : MirBody :=
  { argCount := 1
    localCount := 2
    ptrWidthBits := 64
    localTys := [.uint 8, .uint 8]
    blocks :=
      [ { stmts := [], terminator := term }
      , { stmts := [.assign ⟨⟨0⟩, []⟩ (.use (.constVal (.int 1)))]
          terminator := .return_ }
      , { stmts := [.assign ⟨⟨0⟩, []⟩ (.use (.constVal (.int 2)))]
          terminator := .return_ }
      ]
  }

/-- Entry state for `mirCfgBody` with argument `x`. -/
def mirCfgState (x : Nat) : MirState :=
  ⟨[some .uninit, some (.int x)], [0, 0], 0, 0⟩

/-- `fn f(a: &u8, b: &u16)` with caller slot types `callerTys`, where both
arguments point to caller slot `3`. -/
def mirTwoSharedArgsBody (callerTys : List MirTy) : MirBody :=
  { argCount := 2
    localCount := 3
    ptrWidthBits := 64
    localTys := [.unit, .ref (.uint 8), .ref (.uint 16)] ++ callerTys
    blocks :=
      [ { stmts := [.assign ⟨⟨0⟩, []⟩ (.use (.constVal .unit))]
          terminator := .return_ } ]
  }

/-- Entry state for `mirTwoSharedArgsBody`: both arguments point to caller
slot `3`, which holds `1`. -/
def mirTwoSharedArgsState : MirState :=
  ⟨[some .uninit, some (.ref false 0 ⟨3⟩ [] 0), some (.ref false 0 ⟨3⟩ [] 0),
    some (.int 1)],
   [0, 0, 0, 0], 0, 0⟩

/-- Entry state for `q: &u8, p: &mut &u8` with `q` pointing to caller slot `3`
(holding `1`) and `p` pointing to caller slot `4`, which holds a copy of `q`. -/
def mirSharedInMutRootState : MirState :=
  ⟨[some .uninit, some (.ref false 0 ⟨3⟩ [] 0), some (.ref true 0 ⟨4⟩ [] 0),
    some (.int 1), some (.ref false 0 ⟨3⟩ [] 0)],
   [0, 0, 0, 0, 0], 0, 0⟩

/-- `PureLift` entry parameters for `q: &u8, p: &mut &u8`; `p`'s value names
`q` by its root `LoanId` `0`. -/
def mirSharedInMutRootParams : List (ParamInput MirVal) :=
  [⟨.sharedRef 0 [], .int 1⟩, ⟨.mutRef 1 [], .ref false 0 ⟨0⟩ [] 0⟩]

/-- `fn f() -> R` with return type `retTy` whose body is a bare `return`. -/
def mirBareReturnBody (retTy : MirTy) : MirBody :=
  { argCount := 0
    localCount := 1
    ptrWidthBits := 64
    localTys := [retTy]
    blocks := [{ stmts := [], terminator := .return_ }]
  }

/-- `let _ = x.0.0` after moving out of `x.0`, with `x : ((u8,), u8)`. -/
def mirPlaceMentionNestedMovedBody : MirBody :=
  { argCount := 0
    localCount := 3
    ptrWidthBits := 64
    localTys := [.unit, .tuple [.tuple [.uint 8], .uint 8], .tuple [.uint 8]]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨1⟩
            , .storageLive ⟨2⟩
            , .assign ⟨⟨1⟩, []⟩
                (.use (.constVal
                  (.fieldCons (.fieldCons (.int 5) .unit)
                    (.fieldCons (.int 6) .unit))))
            , .assign ⟨⟨2⟩, []⟩ (.use (.move ⟨⟨1⟩, [.field 0]⟩))
            , .placeMention ⟨⟨1⟩, [.field 0, .field 0]⟩
            , .assign ⟨⟨0⟩, []⟩ (.use (.constVal .unit))
            ]
          terminator := .return_ } ]
  }

/-- `fn f(x: X) -> T` (`x : outerTy`, a reference to `&mut u8`) with temporary
`_2 : &mut u8`, caller slots `3` (`*x : &mut u8`) and `4` (`**x : u8`), and
body statements `stmts`. -/
def mirDerefTempBody (retTy outerTy : MirTy) (stmts : List Stmt) : MirBody :=
  { argCount := 1
    localCount := 3
    ptrWidthBits := 64
    localTys := [retTy, outerTy, .refMut (.uint 8), .refMut (.uint 8), .uint 8]
    blocks := [{ stmts := stmts, terminator := .return_ }]
  }

/-- Entry state for `mirDerefTempBody`: `x` (a mutable reference iff `xMut`)
points to caller slot `3`, which holds a `&mut` to caller slot `4` holding
`5`. -/
def mirDerefTempState (xMut : Bool) : MirState :=
  ⟨[some .uninit, some (.ref xMut 0 ⟨3⟩ [] 0), none,
    some (.ref true 0 ⟨4⟩ [] 0), some (.int 5)],
   [0, 0, 0, 0, 0], 0, 0⟩

/-- Regression tests for `Trusted.MirSemantics` and the bridge:
1. entry validation (`bodyCfgValid`) rejects a `SwitchInt` with duplicate
   values, a value that does not fit the discriminant type, or a constant
   discriminant, and accepts a well-formed table,
2. entry validation rejects any edge into the start block `bb0` (by `goto` or
   by a `SwitchInt` target), and accepts the same body without it,
3. distinct fields of a struct or tuple are disjoint places (`pathsOverlap`),
4. the declared type of a caller-owned slot is authoritative: `&u8` and `&u16`
   arguments that target one slot are rejected whatever its type (or if it has
   none), while two `&u8` arguments to a `u8` slot are accepted, and
5. for `q: &u8, p: &mut &u8`, extraction with the full root-loan slot table
   normalizes `p`'s referent to name `q` by its root `LoanId` (without the
   table it fails rather than leave `q`'s slot index in place), while
   `PureLift`'s `initFnState` rejects the parameter value that carries `q`'s
   handle,
6. entry validation rejects a state without a generation counter per slot,
7. `PlaceMention` of `x.0.0` succeeds after moving out of `x.0`, because it
   checks the declared projection instead of reading the value,
8. a bare `return` from `fn f()` (or a function returning a fieldless struct)
   returns the type's unique value, while an uninitialized `u8` return place
   still faults, and
9. `bodyTysSupported` rejects a bare field-list spine as a local type, and
   `MirTy.wellFormed` rejects malformed `.adt` and reference children, and
10. non-retagging copies must define dereference temporaries
   (`bodyDerefTempsValid`): `**x` for `x : &&mut u8` reads through one, while
   returning the inner `&mut u8` (with either retag flag), writing through a
   temporary copied from behind `&`, and using a temporary other than as a
   dereference base are rejected; writing through a temporary copied from
   `&mut &mut u8` is accepted. -/
theorem mir_cfg_validation_slot_types_and_unit_return_tests :
    -- 1. SwitchInt tables.
    (match runMirSteps (mirCfgBodyNoBack
        (.switchInt (.copy ⟨⟨1⟩, []⟩)
          { branches := [⟨7, ⟨1⟩⟩], otherwise := ⟨2⟩ })) 4 (mirCfgState 7) with
     | .returned ret => ret.value = .int 1
     | _ => False) ∧
    runMirSteps (mirCfgBodyNoBack
        (.switchInt (.copy ⟨⟨1⟩, []⟩)
          { branches := [⟨7, ⟨1⟩⟩, ⟨7, ⟨2⟩⟩], otherwise := ⟨2⟩ })) 4
      (mirCfgState 7) = .rejected ∧
    runMirSteps (mirCfgBodyNoBack
        (.switchInt (.copy ⟨⟨1⟩, []⟩)
          { branches := [⟨256, ⟨1⟩⟩], otherwise := ⟨2⟩ })) 4
      (mirCfgState 7) = .rejected ∧
    runMirSteps (mirCfgBodyNoBack
        (.switchInt (.constVal (.int 7))
          { branches := [⟨7, ⟨1⟩⟩], otherwise := ⟨2⟩ })) 4
      (mirCfgState 7) = .rejected ∧
    terminatorCfgValid (mirCfgBodyNoBack .return_)
      (.switchInt (.copy ⟨⟨0⟩, []⟩)
        { branches := [⟨1, ⟨1⟩⟩], otherwise := ⟨2⟩ }) = true ∧
    -- 2. No edge into `bb0`.
    runMirSteps (mirCfgBody (.goto ⟨2⟩)) 6 (mirCfgState 7) = .rejected ∧
    runMirSteps (mirCfgBodyNoBack
        (.switchInt (.copy ⟨⟨1⟩, []⟩)
          { branches := [⟨7, ⟨0⟩⟩], otherwise := ⟨2⟩ })) 4
      (mirCfgState 7) = .rejected ∧
    (match runMirSteps (mirCfgBodyNoBack (.goto ⟨2⟩)) 4 (mirCfgState 7) with
     | .returned ret => ret.value = .int 2
     | _ => False) ∧
    -- 3. Distinct struct fields are disjoint.
    pathsOverlap [0] [1] = false ∧
    pathsOverlap [0] [0, 1] = true ∧
    -- 4. Caller-slot types are authoritative.
    runMirSteps (mirTwoSharedArgsBody [.uint 8]) 3 mirTwoSharedArgsState
      = .rejected ∧
    runMirSteps (mirTwoSharedArgsBody [.uint 16]) 3 mirTwoSharedArgsState
      = .rejected ∧
    runMirSteps (mirTwoSharedArgsBody []) 3 mirTwoSharedArgsState = .rejected ∧
    (runMirSteps
      { argCount := 2, localCount := 3, ptrWidthBits := 64,
        localTys := [.unit, .ref (.uint 8), .ref (.uint 8), .uint 8],
        blocks :=
          [ { stmts := [.assign ⟨⟨0⟩, []⟩ (.use (.constVal .unit))]
              terminator := .return_ } ] } 3
      mirTwoSharedArgsState).isReturned = true ∧
    -- 5. Shared roots normalize writebacks in the MIR extraction, while
    -- `PureLift` rejects a parameter value that carries a handle:
    extractCallerSlotVals [4] mirSharedInMutRootState [3, 4] =
      some [.ref false 0 ⟨0⟩ [] 0] ∧
    initFnState mirValAlg mirSharedInMutRootParams = .fail ∧
    extractCallerSlotVals [4] mirSharedInMutRootState = none ∧
    -- 6.-9.
    runMirSteps (mirStoreConstBody [.unit] .unit) 3
      ⟨[some .uninit], [], 0, 0⟩ = .rejected ∧
    (runMirSteps (mirStoreConstBody [.unit] .unit) 3
      ⟨[some .uninit], [0], 0, 0⟩).isReturned = true ∧
    (runMirSteps mirPlaceMentionNestedMovedBody 8
      ⟨[some .uninit, none, none], [0, 0, 0], 0, 0⟩).isReturned = true ∧
    (match runMirSteps (mirBareReturnBody .unit) 2
        ⟨[some .uninit], [0], 0, 0⟩ with
     | .returned ret => ret.value = .unit
     | _ => False) ∧
    (match runMirSteps (mirBareReturnBody (.adt 0 [.tuple []])) 2
        ⟨[some .uninit], [0], 0, 0⟩ with
     | .returned ret => ret.value = .adt 0 (.fieldCons .unit .unit)
     | _ => False) ∧
    runMirSteps (mirBareReturnBody (.uint 8)) 2
      ⟨[some .uninit], [0], 0, 0⟩ = .fault ∧
    bodyTysSupported (mirDeclaresTyBody (MirTy.packList [.uint 8])) = false ∧
    (MirTy.tuple [.uint 8, .ref (.adt 0 [])]).wellFormed = true ∧
    MirTy.wellFormed ⟨1, .adt 0 .usize⟩ = false ∧
    MirTy.wellFormed ⟨1, .ref .nil⟩ = false ∧
    -- 10.
    -- `fn f(x: &&mut u8) -> u8 { **x }` reads through a deref temporary.
    (match runMirSteps
        (mirDerefTempBody (.uint 8) (.ref (.refMut (.uint 8)))
          [ .storageLive ⟨2⟩
          , .assign ⟨⟨2⟩, []⟩ (.use (.copy ⟨⟨1⟩, [.deref]⟩) .no)
          , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨2⟩, [.deref]⟩))
          , .storageDead ⟨2⟩ ]) 6
        (mirDerefTempState false) with
     | .returned ret => ret.value = .int 5
     | _ => False) ∧
    -- Returning the `&mut u8` inside a `&&mut u8` is rejected with either flag.
    runMirSteps
        (mirDerefTempBody (.refMut (.uint 8)) (.ref (.refMut (.uint 8)))
          [ .storageLive ⟨2⟩
          , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, [.deref]⟩) .no) ]) 4
        (mirDerefTempState false) = .rejected ∧
    runMirSteps
        (mirDerefTempBody (.refMut (.uint 8)) (.ref (.refMut (.uint 8)))
          [ .storageLive ⟨2⟩
          , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, [.deref]⟩)) ]) 4
        (mirDerefTempState false) = .rejected ∧
    -- Writing through a temporary copied from behind `&` is rejected.
    runMirSteps
        (mirDerefTempBody .unit (.ref (.refMut (.uint 8)))
          [ .storageLive ⟨2⟩
          , .assign ⟨⟨2⟩, []⟩ (.use (.copy ⟨⟨1⟩, [.deref]⟩) .no)
          , .assign ⟨⟨2⟩, [.deref]⟩ (.use (.constVal (.int 9)))
          , .assign ⟨⟨0⟩, []⟩ (.use (.constVal .unit)) ]) 6
        (mirDerefTempState false) = .rejected ∧
    -- Through `&mut &mut u8`, writing via the temporary is accepted.
    (match runMirSteps
        (mirDerefTempBody .unit (.refMut (.refMut (.uint 8)))
          [ .storageLive ⟨2⟩
          , .assign ⟨⟨2⟩, []⟩ (.use (.copy ⟨⟨1⟩, [.deref]⟩) .no)
          , .assign ⟨⟨2⟩, [.deref]⟩ (.use (.constVal (.int 9)))
          , .assign ⟨⟨0⟩, []⟩ (.use (.constVal .unit)) ]) 6
        (mirDerefTempState true) with
     | .returned ret => lookupAt ret.state.locals 4 = some (some (.int 9))
     | _ => False) ∧
    -- A temporary used other than as a dereference base is rejected.
    runMirSteps
        (mirDerefTempBody (.refMut (.uint 8)) (.refMut (.refMut (.uint 8)))
          [ .storageLive ⟨2⟩
          , .assign ⟨⟨2⟩, []⟩ (.use (.copy ⟨⟨1⟩, [.deref]⟩) .no)
          , .assign ⟨⟨0⟩, []⟩ (.use (.move ⟨⟨2⟩, []⟩)) ]) 6
        (mirDerefTempState true) = .rejected ∧
    bodyDerefTempsValid
      (mirDerefTempBody .unit (.ref (.refMut (.uint 8)))
        [ .storageLive ⟨2⟩
        , .assign ⟨⟨2⟩, []⟩ (.use (.copy ⟨⟨1⟩, [.deref]⟩) .no)
        , .assign ⟨⟨2⟩, [.deref]⟩ (.use (.constVal (.int 9)))
        , .assign ⟨⟨0⟩, []⟩ (.use (.constVal .unit)) ]) = false ∧
    bodyDerefTempsValid
      (mirDerefTempBody .unit (.refMut (.refMut (.uint 8)))
        [ .storageLive ⟨2⟩
        , .assign ⟨⟨2⟩, []⟩ (.use (.copy ⟨⟨1⟩, [.deref]⟩) .no)
        , .assign ⟨⟨2⟩, [.deref]⟩ (.use (.constVal (.int 9)))
        , .assign ⟨⟨0⟩, []⟩ (.use (.constVal .unit)) ]) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `fn f(x: &mut u8) { *x = 1 }` with caller slot `2` (`*x : u8`) and an
unreachable caller slot `3 : &u8`. -/
def mirMutWriteOneBody : MirBody :=
  { argCount := 1
    localCount := 2
    ptrWidthBits := 64
    localTys := [.unit, .refMut (.uint 8), .uint 8, .ref (.uint 8)]
    blocks :=
      [ { stmts := [.assign ⟨⟨1⟩, [.deref]⟩ (.use (.constVal (.int 1)))]
          terminator := .return_ } ]
  }

/-- Entry state for `mirMutWriteOneBody`: `x` points to caller slot `2`. If
`withStale`, caller slot `3` holds a shared reference to slot `2`, as when the
caller ran `let r = &x; f(&mut x);` and never used `r` again. -/
def mirMutWriteOneState (withStale : Bool) : MirState :=
  if withStale then
    ⟨[some .uninit, some (.ref true 0 ⟨2⟩ [] 1), some (.int 0),
      some (.ref false 0 ⟨2⟩ [] 1)], [0, 0, 0, 0], 0, 0⟩
  else
    ⟨[some .uninit, some (.ref true 0 ⟨2⟩ [] 1), some (.int 0)],
     [0, 0, 0], 0, 0⟩

/-- `fn f(a: &&mut u8, b: &u8) -> u8 { *b; **a }`, reading `**a` through the
dereference temporary `_3`. Caller slot `4` holds `r: &mut u8` and caller slot
`5` holds `x: u8`. -/
def mirSharedReborrowArgsBody : MirBody :=
  { argCount := 2
    localCount := 4
    ptrWidthBits := 64
    localTys :=
      [.uint 8, .ref (.refMut (.uint 8)), .ref (.uint 8), .refMut (.uint 8),
       .refMut (.uint 8), .uint 8]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨3⟩
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨2⟩, [.deref]⟩))
            , .assign ⟨⟨3⟩, []⟩ (.use (.copy ⟨⟨1⟩, [.deref]⟩) .no)
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨3⟩, [.deref]⟩))
            , .storageDead ⟨3⟩ ]
          terminator := .return_ } ]
  }

/-- Entry state for the call `let r = &mut x; f(&r, &*r)` of
`mirSharedReborrowArgsBody`: `a = &r`, `b = &*r` (a reborrow of `r`, one level
deeper), and `r = &mut x` with `x = 5`. -/
def mirSharedReborrowArgsState : MirState :=
  ⟨[some .uninit, some (.ref false 0 ⟨4⟩ [] 1), some (.ref false 0 ⟨5⟩ [] 2),
    none, some (.ref true 0 ⟨5⟩ [] 1), some (.int 5)],
   [0, 0, 0, 0, 0, 0], 0, 0⟩

/-- `fn f() -> bool { lhs == rhs }` with two constant operands. -/
def mirConstCmpBody (lhs rhs : MirVal) : MirBody :=
  { argCount := 0
    localCount := 1
    ptrWidthBits := 64
    localTys := [.bool]
    blocks :=
      [ { stmts :=
            [.assign ⟨⟨0⟩, []⟩
              (.binaryOp .eq (.constVal lhs) (.constVal rhs))]
          terminator := .return_ } ]
  }

/-- `fn f(a: &mut usize, b: &mut usize) -> usize { *a = 1; *b = 2; 0 }`. -/
def mirTwoMutArgsBody : MirBody :=
  { argCount := 2
    localCount := 3
    ptrWidthBits := 64
    localTys := [.usize, .refMut .usize, .refMut .usize, .usize, .usize]
    blocks :=
      [ { stmts :=
            [ .assign ⟨⟨1⟩, [.deref]⟩ (.use (.constVal (.int 1)))
            , .assign ⟨⟨2⟩, [.deref]⟩ (.use (.constVal (.int 2)))
            , .assign ⟨⟨0⟩, []⟩ (.use (.constVal (.int 0))) ]
          terminator := .return_ } ]
  }

/-- Entry state for `mirTwoMutArgsBody` with `a` pointing to caller slot `4`
and `b` pointing to caller slot `3`, both holding `0`. -/
def mirTwoMutArgsState : MirState :=
  ⟨[some .uninit, some (.ref true 0 ⟨4⟩ [] 0), some (.ref true 0 ⟨3⟩ [] 0),
    some (.int 0), some (.int 0)], [0, 0, 0, 0, 0], 0, 0⟩

/-- `PureLift` parameters `a: &mut usize, b: &mut usize`, both `0`. -/
def mirTwoMutArgsParams : List (ParamInput MirVal) :=
  [⟨.mutRef 0 [], .int 0⟩, ⟨.mutRef 1 [], .int 0⟩]

/-- `MirArgsMatch` rejects caller-slot lists that do not follow the arguments:
for `mirTwoMutArgsState`, where `a` points to slot `4` and `b` to slot `3`,
`callerSlots = [3, 4]` would read `a`'s final value from `b`'s referent. -/
theorem mir_args_match_rejects_swapped_slots :
    ¬ MirArgsMatch mirTwoMutArgsBody mirTwoMutArgsParams [3, 4] []
      mirTwoMutArgsState := by
  intro h
  cases h.2

/-- Regression tests for `Trusted.MirSemantics` and the bridge:
1. at return, a caller slot that no argument reaches may hold a reference that
   the callee's write retired (`let r = &x; f(&mut x)`), and the run succeeds
   with the retired reference left in place,
2. entry validation accepts `f(&r, &*r)` for `a: &&mut u8, b: &u8`, because a
   `&mut` reached through `&` does not conflict with a deeper shared reference
   (`mir_entry_depth_consistency_tests` covers the other depths), and the
   callee reads both,
3. two `bool` constants have operand type `bool` (`true == false` evaluates to
   `false`), while two integer constants have no known type and are rejected,
4. `assignPlace` fails closed when neither the place nor the target slot has
   a declared type, for whole-place and field writes,
5. `MirArgsMatch` accepts the caller-slot list that follows the arguments,
   `mirExpectedArgs` computes the arguments that parameters denote, and it
   rejects a shared-reference parameter without a full root-loan table and a
   root-loan table with left-over entries, and
6. a reference made stale by reallocating its referent faults when it is
   dereferenced or copied, while the same bodies without the reallocation
   return `10` (`mir_stale_ref_copy_and_deref_rejected`). -/
theorem mir_entry_aliasing_const_cmp_and_args_match_tests :
    -- 1. Retired references in unreachable caller slots.
    (runMirSteps mirMutWriteOneBody 3 (mirMutWriteOneState false)).isReturned =
      true ∧
    (match runMirSteps mirMutWriteOneBody 3 (mirMutWriteOneState true) with
     | .returned ret => lookupAt ret.state.locals 3
     | _ => none) = some (some (.ref false 0 ⟨4⟩ [] 1)) ∧
    -- 2. A `&mut` behind `&` next to a shared reborrow of it.
    entryStateValid mirSharedReborrowArgsBody mirSharedReborrowArgsState =
      true ∧
    (match runMirSteps mirSharedReborrowArgsBody 8
        mirSharedReborrowArgsState with
     | .returned ret => ret.value = .int 5
     | _ => False) ∧
    -- 3. Comparisons of two constants.
    (match runMirSteps (mirConstCmpBody (.bool true) (.bool false)) 3
        ⟨[some .uninit], [0], 0, 0⟩ with
     | .returned ret => ret.value = .bool false
     | _ => False) ∧
    runMirSteps (mirConstCmpBody (.int 1) (.int 2)) 3
      ⟨[some .uninit], [0], 0, 0⟩ = .fault ∧
    -- 4. Untyped stores fail.
    assignPlace
      { argCount := 0, localCount := 1, ptrWidthBits := 64, blocks := [] }
      ⟨[some .uninit], [0], 0, 0⟩ ⟨⟨0⟩, []⟩ (.int 5) = none ∧
    assignPlace
      { argCount := 0, localCount := 1, ptrWidthBits := 64, blocks := [] }
      ⟨[some (.fieldCons (.int 1) .unit)], [0], 0, 0⟩ ⟨⟨0⟩, [.field 0]⟩
      (.int 5) = none ∧
    -- 5. Arguments match parameters.
    MirArgsMatch mirTwoMutArgsBody mirTwoMutArgsParams [4, 3] []
      mirTwoMutArgsState ∧
    mirExpectedArgs [3, 4] false mirTwoMutArgsParams 0 =
      some ([.ref true 0 ⟨3⟩ [] 0, .ref true 0 ⟨4⟩ [] 0], [3, 4]) ∧
    mirArgShapes ((mirTwoMutArgsState.locals.drop 1).take 2) =
      [.ref true 0 ⟨4⟩ [] 0, .ref true 0 ⟨3⟩ [] 0] ∧
    mirExpectedArgs [3] true [⟨.sharedRef 0 [], .int 1⟩] 0 =
      some ([.ref false 0 ⟨3⟩ [] 0], []) ∧
    mirExpectedArgs [3] false [⟨.sharedRef 0 [], .int 1⟩] 0 = none ∧
    mirExpectedArgs [3, 4] false [⟨.mutRef 0 [], .int 1⟩] 0 = none ∧
    -- 6. Stale references.
    runMirSteps (mirStaleRefBody true false) 16
      ⟨[some .uninit, none, none, none], [0, 0, 0, 0], 0, 0⟩ = .fault := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl,
    rfl, rfl, rfl⟩

/-- `fn f(a: &mut &mut u8) { let mut l = 1; *a = &mut l; [l = 7;] }`, where
`_1 = a` points to caller slot `3 : &mut u8` and `_2 = l`. The write `l = 7`
(present if `retire`) would retire the stored `&mut l`. -/
def mirFrameEscapeBody (retire : Bool) : MirBody :=
  { argCount := 1
    localCount := 3
    ptrWidthBits := 64
    localTys :=
      [.unit, .refMut (.refMut (.uint 8)), .uint 8, .refMut (.uint 8), .uint 8]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨2⟩
            , .assign ⟨⟨2⟩, []⟩ (.use (.constVal (.int 1)))
            , .assign ⟨⟨1⟩, [.deref]⟩ (.refMut ⟨⟨2⟩, []⟩) ] ++
            (if retire then [.assign ⟨⟨2⟩, []⟩ (.use (.constVal (.int 7)))]
             else []) ++
            [ .storageDead ⟨2⟩
            , .assign ⟨⟨0⟩, []⟩ (.use (.constVal .unit)) ]
          terminator := .return_ } ]
  }

/-- Entry state for `mirFrameEscapeBody`: `a` points to caller slot `3`, which
holds a `&mut` to caller slot `4` holding `5`. -/
def mirFrameEscapeState : MirState :=
  ⟨[some .uninit, some (.ref true 0 ⟨3⟩ [] 1), none,
    some (.ref true 0 ⟨4⟩ [] 1), some (.int 5)],
   [0, 0, 0, 0, 0], 0, 0⟩

/-- `fn f<'a>(a: &mut &'a u8, b: &'a mut u8) { *a = &*b; *b = 5; }`: the callee
stores a live shared reborrow of `*b` into caller slot `4` (`*a`) and then
retires it by writing through `b`. -/
def mirStoreThenRetireBody : MirBody :=
  { argCount := 2
    localCount := 4
    ptrWidthBits := 64
    localTys :=
      [.unit, .refMut (.ref (.uint 8)), .refMut (.uint 8), .ref (.uint 8),
       .ref (.uint 8), .uint 8, .uint 8]
    blocks :=
      [ { stmts :=
            [ .storageLive ⟨3⟩
            , .assign ⟨⟨3⟩, []⟩ (.ref ⟨⟨2⟩, [.deref]⟩)
            , .assign ⟨⟨1⟩, [.deref]⟩ (.use (.copy ⟨⟨3⟩, []⟩))
            , .storageDead ⟨3⟩
            , .assign ⟨⟨2⟩, [.deref]⟩ (.use (.constVal (.int 5)))
            , .assign ⟨⟨0⟩, []⟩ (.use (.constVal .unit)) ]
          terminator := .return_ } ]
  }

/-- Entry state for `mirStoreThenRetireBody`: `a` points to caller slot `4`
(holding a shared reference to slot `5`) and `b` points to caller slot `6`. -/
def mirStoreThenRetireState : MirState :=
  ⟨[some .uninit, some (.ref true 0 ⟨4⟩ [] 1), some (.ref true 0 ⟨6⟩ [] 1),
    none, some (.ref false 0 ⟨5⟩ [] 1), some (.int 1), some (.int 2)],
   [0, 0, 0, 0, 0, 0, 0], 0, 0⟩

/-- The adapter itself enforces `MirArgsMatch`: for `mirTwoMutArgsState`, where
`a` points to slot `4` and `b` to slot `3`, no `PureLift` state relates to the
machine under `callerSlots = [3, 4]`, so the generic `pure_lift_sound` cannot
be instantiated with that adapter (its `hInit` is unprovable). -/
theorem mir_adapter_rejects_swapped_slots (sym : SymState MirVal) :
    ¬ (mirOperationalAdapter [3, 4] mirTwoMutArgsBody
      mirTwoMutArgsParams).StateRel sym (.running mirTwoMutArgsState) := by
  intro h
  cases h.2.1.2

/-- Regression tests for `Trusted.MirSemantics` and the bridge:
1. `assignPlace` rejects storing a frame-local reference into a caller slot,
   so `*a = &mut l` faults whether or not a later write to `l` retires the
   stored reference,
2. a reference the callee stores into a caller slot and then retires (`*a =
   &*b; *b = 5`) stays there as a retired reference, and the call returns, and
3. with `callerSlots = [4, 3]`, which follows the arguments, the adapter
   relates the `PureLift` entry state to the machine (compare
   `mir_adapter_rejects_swapped_slots`). -/
theorem mir_frame_escape_and_adapter_relation_tests :
    -- 1. Frame-local references never reach caller slots.
    entryStateValid (mirFrameEscapeBody true) mirFrameEscapeState = true ∧
    runMirSteps (mirFrameEscapeBody true) 20 mirFrameEscapeState = .fault ∧
    runMirSteps (mirFrameEscapeBody false) 20 mirFrameEscapeState = .fault ∧
    -- 2. A stored reference retired later.
    (match runMirSteps mirStoreThenRetireBody 20 mirStoreThenRetireState with
     | .returned ret => lookupAt ret.state.locals 4
     | _ => none) = some (some (.ref false 0 ⟨7⟩ [] 3)) ∧
    -- 3. The adapter relates a matching setup.
    (Exists fun sym =>
      initFnState mirValAlg mirTwoMutArgsParams = .ok sym ∧
      (mirOperationalAdapter [4, 3] mirTwoMutArgsBody
        mirTwoMutArgsParams).StateRel sym (.running mirTwoMutArgsState)) :=
  ⟨rfl, rfl, rfl, rfl, ⟨_, rfl, And.intro rfl (And.intro ⟨rfl, rfl⟩ rfl)⟩⟩

/-- `fn f() {}`. -/
def mirNoopBody : MirBody :=
  { argCount := 0
    localCount := 1
    ptrWidthBits := 64
    localTys := [.unit]
    blocks := [{ stmts := [], terminator := .return_ }]
  }

/-- `fn f(a: &mut u32) { *a = 5; }`, with caller slot `2 : u32` (`*a`) and
caller slots `3 : &u32` and `4 : &&u32` that no argument reaches. -/
def mirWriteOneU32Body : MirBody :=
  { argCount := 1
    localCount := 2
    ptrWidthBits := 64
    localTys :=
      [.unit, .refMut (.uint 32), .uint 32, .ref (.uint 32),
       .ref (.ref (.uint 32))]
    blocks :=
      [ { stmts := [.assign ⟨⟨1⟩, [.deref]⟩ (.use (.constVal (.int 5)))]
          terminator := .return_ } ]
  }

/-- Return does not inspect caller-owned slots, so calls are accepted when a
caller slot that no argument reaches holds what a valid caller can leave there:
1. a live reference `q = &s` to a value `s` whose field `s.0` was moved out
   (`let q = &s; let a = s.0; f();`),
2. a stale reference whose target index happens to name a frame local, and
3. a reference `rr = &r` to a reference `r = &x` that the callee's write
   through `a = &mut x` retires (`let r = &x; let rr = &r; f(&mut x);`). -/
theorem mir_return_ignores_caller_slots_tests :
    (runMirSteps mirNoopBody 2
      ⟨[some .uninit, some (.fieldCons .uninit (.fieldCons (.int 2) .unit)),
        some (.ref false 0 ⟨1⟩ [] 0)], [0, 0, 0], 0, 0⟩).isReturned = true ∧
    (runMirSteps mirNoopBody 2
      ⟨[some .uninit, some (.ref false 7 ⟨0⟩ [] 0)], [0, 0], 0, 0⟩).isReturned =
      true ∧
    (runMirSteps mirWriteOneU32Body 3
      ⟨[some .uninit, some (.ref true 0 ⟨2⟩ [] 0), some (.int 1),
        some (.ref false 0 ⟨2⟩ [] 1), some (.ref false 0 ⟨3⟩ [] 1)],
       [0, 0, 0, 0, 0], 0, 0⟩).isReturned = true :=
  ⟨rfl, rfl, rfl⟩

/-- Statements of `mirDerefBaseReadBody`: `_2 = &mut _1`, then (if
`readBase`) `_3 = copy (*_1)`, then `_4 = copy (*_2)` without a retag and
`_0 = copy (*_4)`. -/
def mirDerefBaseReadStmts (readBase : Bool) : List Stmt :=
  [ .assign ⟨⟨2⟩, []⟩ (.refMut ⟨⟨1⟩, []⟩) ] ++
  (if readBase then [.assign ⟨⟨3⟩, []⟩ (.use (.copy ⟨⟨1⟩, [.deref]⟩))]
   else []) ++
  [ .assign ⟨⟨4⟩, []⟩ (.use (.copy ⟨⟨2⟩, [.deref]⟩) .no)
  , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨4⟩, [.deref]⟩)) ]

/-- `fn f(x: &mut u32) -> u32` running `mirDerefBaseReadStmts readBase`, with
caller slot `5 : u32` (`*x`). -/
def mirDerefBaseReadBody (readBase : Bool) : MirBody :=
  { argCount := 1
    localCount := 5
    ptrWidthBits := 64
    localTys :=
      [.uint 32, .refMut (.uint 32), .refMut (.refMut (.uint 32)), .uint 32,
       .refMut (.uint 32), .uint 32]
    blocks :=
      [{ stmts := mirDerefBaseReadStmts readBase, terminator := .return_ }]
  }

/-- Entry state for `mirDerefBaseReadBody`: `x` points to caller slot `5`,
which holds `7`. -/
def mirDerefBaseReadState : MirState :=
  ⟨[some .uninit, some (.ref true 0 ⟨5⟩ [] 0), some .uninit, some .uninit,
    some .uninit, some (.int 7)],
   [0, 0, 0, 0, 0, 0], 0, 0⟩

/-- Evaluating `*_1` reads the pointer out of `_1` (`readDerefBase`), which
retires the mutable borrow `_2 = &mut _1`; a later use of `_2` faults, as in
Stacked Borrows. Without the read of `*_1`, the body returns `7`. -/
theorem mir_deref_reads_base_local_tests :
    runMirSteps (mirDerefBaseReadBody true) 10 mirDerefBaseReadState = .fault ∧
    (match
        runMirSteps (mirDerefBaseReadBody false) 10 mirDerefBaseReadState with
     | .returned ret => ret.value = .int 7
     | _ => False) :=
  ⟨rfl, rfl⟩

/-- `fn f(x: (u32,)) -> u32 { x.idx }`. -/
def mirFieldPastEndBody (idx : Nat) : MirBody :=
  { argCount := 1
    localCount := 2
    ptrWidthBits := 64
    localTys := [.uint 32, .tuple [.uint 32]]
    blocks :=
      [ { stmts := [.assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, [.field idx]⟩))]
          terminator := .return_ } ]
  }

/-- A place operand without a declared type is ill typed
(`rvalueOperandsTyped`): copying `x.7` out of `x : (u32,)` faults, while `x.0`
returns `3`. A constant that contains a reference never fits a type
(`constOperandFits`). -/
theorem mir_untyped_place_operand_tests :
    runMirSteps (mirFieldPastEndBody 7) 3
      ⟨[some .uninit, some (.fieldCons (.int 3) .unit)], [0, 0], 0, 0⟩ =
      .fault ∧
    (match runMirSteps (mirFieldPastEndBody 0) 3
        ⟨[some .uninit, some (.fieldCons (.int 3) .unit)], [0, 0], 0, 0⟩ with
     | .returned ret => ret.value = .int 3
     | _ => False) ∧
    constOperandFits 64 (.ref .usize) (.constVal (.ref false 0 ⟨99⟩ [] 0)) =
      false :=
  ⟨rfl, rfl, rfl⟩

/-- `fn f(x: S) -> u32 { x.0 }` for a struct `S` (`.adt 0`) with one `u32`
field, and caller slot `2 : u32`. -/
def mirAdtArgBody : MirBody :=
  { argCount := 1
    localCount := 2
    ptrWidthBits := 64
    localTys := [.uint 32, .adt 0 [.uint 32], .uint 32]
    blocks :=
      [ { stmts := [.assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, [.field 0]⟩))]
          terminator := .return_ } ]
  }

/-- Values with a component outside a `.unit`-terminated field spine are not
values of their declared type, so `runMirSteps` rejects arguments holding
them: a struct whose payload is a reference instead of a field spine, and a
tuple whose spine ends in a reference instead of `.unit`. The well-formed
counterparts run normally. -/
theorem mir_non_spine_values_rejected_at_entry :
    runMirSteps mirAdtArgBody 3
      ⟨[some .uninit, some (.adt 0 (.ref false 0 ⟨2⟩ [] 0)), some (.int 3)],
       [0, 0, 0], 0, 0⟩ = .rejected ∧
    (runMirSteps mirAdtArgBody 3
      ⟨[some .uninit, some (.adt 0 (.fieldCons (.int 3) .unit)), some (.int 3)],
       [0, 0, 0], 0, 0⟩).isReturned = true ∧
    runMirSteps (mirFieldPastEndBody 0) 3
      ⟨[some .uninit, some (.fieldCons (.int 3) (.ref false 0 ⟨2⟩ [] 0)),
        some (.int 3)], [0, 0, 0], 0, 0⟩ = .rejected :=
  ⟨rfl, rfl, rfl⟩

/-- `_1 : (u8, u8, u8)` is filled field by field, copied into `_dst`, and
`_0 = copy _dst.2` is returned. With `dst = 1` the copy is `_1 = copy _1`. -/
def mirTupleCopyBody (dst : Nat) : MirBody :=
  { argCount := 0
    localCount := 3
    ptrWidthBits := 64
    localTys :=
      [.uint 8, .tuple [.uint 8, .uint 8, .uint 8],
       .tuple [.uint 8, .uint 8, .uint 8]]
    blocks :=
      [ { stmts :=
            [ .assign ⟨⟨1⟩, [.field 0]⟩ (.use (.constVal (.int 1)))
            , .assign ⟨⟨1⟩, [.field 1]⟩ (.use (.constVal (.int 2)))
            , .assign ⟨⟨1⟩, [.field 2]⟩ (.use (.constVal (.int 3)))
            , .assign ⟨⟨dst⟩, []⟩ (.use (.copy ⟨⟨1⟩, []⟩))
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨dst⟩, [.field 2]⟩)) ]
          terminator := .return_ } ]
  }

/-- `_1 : (u8, u8, u8)` is filled and copied into `_4`; then `_2 = &mut _1`,
`_3 = &shared`, and `(*_2) = copy (*_3)`. With `shared = *_2` the two sides of
the last assignment are the same memory. -/
def mirDerefCopyBody (shared : Place) : MirBody :=
  { argCount := 0
    localCount := 5
    ptrWidthBits := 64
    localTys :=
      [.unit, .tuple [.uint 8, .uint 8, .uint 8],
       .refMut (.tuple [.uint 8, .uint 8, .uint 8]),
       .ref (.tuple [.uint 8, .uint 8, .uint 8]),
       .tuple [.uint 8, .uint 8, .uint 8]]
    blocks :=
      [ { stmts :=
            [ .assign ⟨⟨1⟩, [.field 0]⟩ (.use (.constVal (.int 1)))
            , .assign ⟨⟨1⟩, [.field 1]⟩ (.use (.constVal (.int 2)))
            , .assign ⟨⟨1⟩, [.field 2]⟩ (.use (.constVal (.int 3)))
            , .assign ⟨⟨4⟩, []⟩ (.use (.copy ⟨⟨1⟩, []⟩))
            , .assign ⟨⟨2⟩, []⟩ (.refMut ⟨⟨1⟩, []⟩)
            , .assign ⟨⟨3⟩, []⟩ (.ref shared)
            , .assign ⟨⟨2⟩, [.deref]⟩ (.use (.copy ⟨⟨3⟩, [.deref]⟩))
            , .assign ⟨⟨0⟩, []⟩ (.use (.constVal .unit)) ]
          terminator := .return_ } ]
  }

/-- `_1, _3 : (u8, &u8)`: `_2 = &target`, `_3.1 = copy _2`, `_1 = copy _3`,
and `_0 = copy _1.0` is returned. With `target = _1.0`, the write to `_1`
removes the item of the reference that the stored value carries. -/
def mirStoreRetiresCarriedRefBody (target : Place) : MirBody :=
  { argCount := 0
    localCount := 5
    ptrWidthBits := 64
    localTys :=
      [.uint 8, .tuple [.uint 8, .ref (.uint 8)], .ref (.uint 8),
       .tuple [.uint 8, .ref (.uint 8)], .uint 8]
    blocks :=
      [ { stmts :=
            [ .assign ⟨⟨1⟩, [.field 0]⟩ (.use (.constVal (.int 7)))
            , .assign ⟨⟨3⟩, [.field 0]⟩ (.use (.constVal (.int 9)))
            , .assign ⟨⟨4⟩, []⟩ (.use (.constVal (.int 4)))
            , .assign ⟨⟨2⟩, []⟩ (.ref target)
            , .assign ⟨⟨3⟩, [.field 1]⟩ (.use (.copy ⟨⟨2⟩, []⟩))
            , .assign ⟨⟨1⟩, []⟩ (.use (.copy ⟨⟨3⟩, []⟩))
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, [.field 0]⟩)) ]
          terminator := .return_ } ]
  }

/-- A pair holding a reference `_2 = &mut _1` (or `&_1` if `!parentMut`) and a
shared reborrow of it is moved into `_5` (a retagging copy), and `_0 = copy
_1` is returned. -/
def mirRetagPairBody (parentMut : Bool) : MirBody :=
  let parentTy : MirTy :=
    if parentMut then .refMut (.uint 8) else .ref (.uint 8)
  let pairTy : MirTy := .tuple [parentTy, .ref (.uint 8)]
  { argCount := 0
    localCount := 6
    ptrWidthBits := 64
    localTys := [.uint 8, .uint 8, parentTy, pairTy, parentTy, pairTy]
    blocks :=
      [ { stmts :=
            [ .assign ⟨⟨1⟩, []⟩ (.use (.constVal (.int 5)))
            , .assign ⟨⟨2⟩, []⟩
                (if parentMut then .refMut ⟨⟨1⟩, []⟩ else .ref ⟨⟨1⟩, []⟩)
            , .assign ⟨⟨3⟩, [.field 0]⟩ (.use (.move ⟨⟨2⟩, []⟩))
            , .assign ⟨⟨4⟩, []⟩ (.use (.copy ⟨⟨3⟩, [.field 0]⟩) .no)
            , .assign ⟨⟨3⟩, [.field 1]⟩ (.ref ⟨⟨4⟩, [.deref]⟩)
            , .assign ⟨⟨5⟩, []⟩ (.use (.move ⟨⟨3⟩, []⟩))
            , .assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, []⟩)) ]
          terminator := .return_ } ]
  }

/-- An all-uninitialized entry state with `n` slots (for `n ≤ 6`) and no
arguments, written out so that evaluation does not unfold `List.replicate`. -/
def mirUninitState : Nat → MirState
  | 3 => ⟨[some .uninit, some .uninit, some .uninit], [0, 0, 0], 0, 0⟩
  | 5 =>
    ⟨[some .uninit, some .uninit, some .uninit, some .uninit, some .uninit],
     [0, 0, 0, 0, 0], 0, 0⟩
  | 6 =>
    ⟨[some .uninit, some .uninit, some .uninit, some .uninit, some .uninit,
      some .uninit],
     [0, 0, 0, 0, 0, 0], 0, 0⟩
  | _ => ⟨[], [], 0, 0⟩

/-- The two sides of a `Use` assignment must not overlap statically: `_1 = copy
_1` is rejected before the first step (`bodyUseAssignsDisjoint`), while
copying into another local returns `3`. -/
theorem mir_static_assignment_overlap_tests :
    runMirSteps (mirTupleCopyBody 1) 20 (mirUninitState 3) = .rejected ∧
    (match runMirSteps (mirTupleCopyBody 2) 20 (mirUninitState 3) with
     | .returned ret => ret.value = .int 3
     | _ => False) :=
  ⟨rfl, rfl⟩

/-- The two sides of a `Use` assignment must not overlap through references:
`(*_2) = copy (*_3)` with `_3 = &*_2` faults (`useAssignOverlaps`), while
copying from a separate local returns. -/
theorem mir_dynamic_assignment_overlap_tests :
    runMirSteps (mirDerefCopyBody ⟨⟨2⟩, [.deref]⟩) 30 (mirUninitState 5) =
      .fault ∧
    (runMirSteps (mirDerefCopyBody ⟨⟨4⟩, []⟩) 30 (mirUninitState 5)
      ).isReturned = true :=
  ⟨rfl, rfl⟩

/-- Storing a value that carries a reference to the overwritten place faults
(`assignPlace`), because the store removes that reference's item before its
retag. -/
theorem mir_store_retires_carried_ref_faults :
    runMirSteps (mirStoreRetiresCarriedRefBody ⟨⟨1⟩, [.field 0]⟩) 30
      (mirUninitState 5) = .fault :=
  rfl

/-- The fault in `mir_store_retires_carried_ref_faults` happens at the sixth
step, the store `_1 = copy _3`: five steps run out of fuel without a fault. -/
theorem mir_store_retires_carried_ref_fault_step :
    runMirSteps (mirStoreRetiresCarriedRefBody ⟨⟨1⟩, [.field 0]⟩) 5
      (mirUninitState 5) = .outOfFuel ∧
    runMirSteps (mirStoreRetiresCarriedRefBody ⟨⟨1⟩, [.field 0]⟩) 6
      (mirUninitState 5) = .fault :=
  ⟨rfl, rfl⟩

/-- Control for `mir_store_retires_carried_ref_faults`: in the same body, the
store `_1 = copy _3` succeeds when the carried reference points to `_4`. The
check runs that single step from the state the body reaches just before it;
running the whole body through `runMirSteps` exceeds the elaborator's default
evaluation budget, which this repository does not let proofs raise. -/
theorem mir_store_carried_ref_elsewhere_steps :
    (match stepMirCore (mirStoreRetiresCarriedRefBody ⟨⟨4⟩, []⟩)
        ⟨[some .uninit,
          some (.fieldCons (.int 7) (.fieldCons .uninit .unit)),
          some (.ref false 0 ⟨4⟩ [] 1),
          some (.fieldCons (.int 9) (.fieldCons (.ref false 0 ⟨4⟩ [] 2) .unit)),
          some (.int 4)],
         [0, 0, 0, 0, 0], 0, 5⟩ with
     | .stepped _ => true
     | _ => false) = true :=
  rfl

/-- Retagging a pair of a `&mut` and its shared reborrow faults
(`retagRefsConsistent`), because the mutable retag retires the reborrow. -/
theorem mir_retag_mut_and_reborrow_pair_faults :
    runMirSteps (mirRetagPairBody true) 30 (mirUninitState 6) = .fault :=
  rfl

/-- Control for `mir_retag_mut_and_reborrow_pair_faults`: a pair of two
shared references returns `5`. -/
theorem mir_retag_shared_pair_returns :
    match runMirSteps (mirRetagPairBody false) 30 (mirUninitState 6) with
    | .returned ret => ret.value = .int 5
    | _ => False :=
  rfl

/-- Admission rejects an edge to a block that does not exist, even on a branch
that the run would not take (`terminatorCfgValid`), and a body without blocks
(`bodyCfgValid`); the same body with in-range targets returns. -/
theorem mir_cfg_rejects_invalid_block_targets :
    runMirSteps (mirCfgBodyNoBack
        (.switchInt (.copy ⟨⟨1⟩, []⟩)
          { branches := [⟨0, ⟨7⟩⟩], otherwise := ⟨1⟩ })) 4 (mirCfgState 5) =
      .rejected ∧
    runMirSteps (mirCfgBodyNoBack (.goto ⟨3⟩)) 4 (mirCfgState 5) = .rejected ∧
    runMirSteps
      { argCount := 0, localCount := 1, ptrWidthBits := 64,
        localTys := [.unit], blocks := [] } 4
      ⟨[some .uninit], [0], 0, 0⟩ = .rejected ∧
    (match runMirSteps (mirCfgBodyNoBack
        (.switchInt (.copy ⟨⟨1⟩, []⟩)
          { branches := [⟨0, ⟨2⟩⟩], otherwise := ⟨1⟩ })) 4 (mirCfgState 5) with
     | .returned ret => ret.value = .int 1
     | _ => False) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Entry state for `mirMutWriteOneBody` (`fn f(a: &mut u8) { *a = 1 }`) in the
valid call `let s = &x; f(&mut x);`, where the caller never uses `s` again:
`a` points to caller slot `2` (`x = 0`), and caller slot `3` holds `s = &x`
with reborrow depth `5`. No argument reaches slot `3`. -/
def mirUnreachableSharedState : MirState :=
  ⟨[some .uninit, some (.ref true 0 ⟨2⟩ [] 1), some (.int 0),
    some (.ref false 0 ⟨2⟩ [] 5)],
   [0, 0, 0, 0], 0, 0⟩

/-- The run of `mirMutWriteOneBody` from `mirUnreachableSharedState`. -/
def mirUnreachableSharedRun : MirRunOutcome :=
  runMirSteps mirMutWriteOneBody 3 mirUnreachableSharedState

/-- A reference that the callee retires in a caller slot comes back rewritten,
and extraction fails closed on it (`Trusted.MirReturn`): in the valid call
`let s = &x; f(&mut x);`, the run returns with `*a = 1`, and the write
through `a` retires `s` in the unreachable caller slot `3`, whose target
becomes the dead slot index `4` (`localGens.length`) instead of `x`'s slot
`2`, where Rust's memory still points. Extraction reads `x = 1`, but fails on
slot `3` even with a root-loan table that names slot `2`, while the same
extraction from the entry state succeeds. -/
theorem mir_retired_caller_ref_tests :
    (match mirUnreachableSharedRun with
     | .returned ret => lookupAt ret.state.locals 2
     | _ => none) = some (some (.int 1)) ∧
    (match mirUnreachableSharedRun with
     | .returned ret => lookupAt ret.state.locals 3
     | _ => none) = some (some (.ref false 0 ⟨4⟩ [] 5)) ∧
    (match mirUnreachableSharedRun with
     | .returned ret => extractCallerPlaceVals [(2, [])] ret.state
     | _ => none) = some [.int 1] ∧
    (match mirUnreachableSharedRun with
     | .returned ret =>
       extractCallerPlaceVals [(3, [])] ret.state [(2, []), (3, [])]
     | _ => some []) = none ∧
    extractCallerPlaceVals [(3, [])] mirUnreachableSharedState
      [(2, []), (3, [])] = some [.ref false 0 ⟨0⟩ [] 0] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `fn f(a: &&mut u8, b: &u8) -> u8 { *b }`, with caller slot `3` holding
`x: u8` and caller slot `4` holding `r: &mut u8`. -/
def mirReadSharedArgBody : MirBody :=
  { argCount := 2
    localCount := 3
    ptrWidthBits := 64
    localTys :=
      [.uint 8, .ref (.refMut (.uint 8)), .ref (.uint 8), .uint 8,
       .refMut (.uint 8)]
    blocks :=
      [ { stmts := [.assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨2⟩, [.deref]⟩))]
          terminator := .return_ } ]
  }

/-- Entry state for the call `let r = &mut x; f(&r, &*r)` of
`mirReadSharedArgBody` with `x = 7`: `a = &r`, `b = &*r` with reborrow depth
`bDepth`, and `r = &mut x` with reborrow depth `rDepth`. A reborrow of `r` is
one level deeper than `r`, so only `bDepth > rDepth` describes this call. -/
def mirReadSharedArgState (rDepth bDepth : Nat) : MirState :=
  ⟨[some .uninit, some (.ref false 0 ⟨4⟩ [] 1),
    some (.ref false 0 ⟨3⟩ [] bDepth), some (.int 7),
    some (.ref true 0 ⟨3⟩ [] rDepth)],
   [0, 0, 0, 0, 0], 0, 0⟩

/-- Entry validation requires a shared reference that overlaps a `&mut` behind
a shared reference to be deeper than the `&mut`
(`Trusted.conflictsWithAnyEntryRef`):
1. for `fn f(a: &&mut u8, b: &u8) -> u8 { *b }`, an entry state that gives
   `b` a reborrow depth not greater than `r`'s (`b` at `1` or `5` with `r` at
   `5`, and both at `1`) is rejected,
2. `stepMirLoop`, which skips entry validation, shows what the check
   prevents: from the state with `b` shallower than `r`, reading `*b` retires
   `r` and rewrites it in caller slot `4` to name the dead slot index `5`,
   although Stacked Borrows keeps a `&mut` when a reborrow of it is read, and
3. with consistent depths (`r` at `1` and `b` at `2`), the run returns `7`
   and leaves `r` unchanged in caller slot `4`. -/
theorem mir_entry_depth_consistency_tests :
    -- 1. Inconsistent depths are rejected.
    entryArgsExclusive mirReadSharedArgBody (mirReadSharedArgState 5 1) =
      false ∧
    runMirSteps mirReadSharedArgBody 3 (mirReadSharedArgState 5 1) =
      .rejected ∧
    runMirSteps mirReadSharedArgBody 3 (mirReadSharedArgState 5 5) =
      .rejected ∧
    runMirSteps mirReadSharedArgBody 3 (mirReadSharedArgState 1 1) =
      .rejected ∧
    -- 2. Without the check, the read would retire `r` in caller memory.
    (match stepMirLoop mirReadSharedArgBody 3 (mirReadSharedArgState 5 1) with
     | .returned ret => lookupAt ret.state.locals 4
     | _ => none) = some (some (.ref true 0 ⟨5⟩ [] 5)) ∧
    -- 3. Consistent depths run and keep `r`.
    entryArgsExclusive mirReadSharedArgBody (mirReadSharedArgState 1 2) =
      true ∧
    (match runMirSteps mirReadSharedArgBody 3 (mirReadSharedArgState 1 2) with
     | .returned ret => ret.value
     | _ => .uninit) = .int 7 ∧
    (match runMirSteps mirReadSharedArgBody 3 (mirReadSharedArgState 1 2) with
     | .returned ret => lookupAt ret.state.locals 4
     | _ => none) = some (some (.ref true 0 ⟨3⟩ [] 1)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `fn f(a: &mut u8) { *a = 5; }` where `a` points to field `0` of caller slot
`2 : (u8, &u8)`. -/
def mirWriteCallerField0Body : MirBody :=
  { argCount := 1
    localCount := 2
    ptrWidthBits := 64
    localTys :=
      [.unit, .refMut (.uint 8), .tuple [.uint 8, .ref (.uint 8)]]
    blocks :=
      [ { stmts :=
            [ .assign ⟨⟨1⟩, [.deref]⟩ (.use (.constVal (.int 5)))
            , .assign ⟨⟨0⟩, []⟩ (.use (.constVal .unit)) ]
          terminator := .return_ } ]
  }

/-- Entry state for `mirWriteCallerField0Body` with untouched sibling field
`S.1 = sibVal`. -/
def mirWriteCallerField0State (sibVal : MirVal) : MirState :=
  ⟨[some .uninit, some (.ref true 0 ⟨2⟩ [0] 0),
    some (.fieldCons (.int 1) (.fieldCons sibVal .unit))],
   [0, 0, 0], 0, 0⟩

/-- Writing to a sub-place `S.0` of a caller-owned aggregate slot checks the
aggregate spine along `resolved.fieldPath` and the written leaf without
re-checking untouched sibling fields (`Trusted.assignPlace`,
`Trusted.writeFieldPathWithTy`), while still rejecting ill-formed root
containers (such as a wrong spine length). -/
theorem mir_assignPlace_subfield_ignores_untouched_siblings_tests :
    -- 1. Entry validation and `*a = 5` succeed when `S.1` holds a retired ref
    -- or an unvalidated scalar value.
    entryStateValid mirWriteCallerField0Body
      (mirWriteCallerField0State (.ref false 0 ⟨3⟩ [] 0)) = true ∧
    (runMirSteps mirWriteCallerField0Body 3
      (mirWriteCallerField0State (.ref false 0 ⟨3⟩ [] 0))).isReturned = true ∧
    (runMirSteps mirWriteCallerField0Body 3
      (mirWriteCallerField0State (.int 300))).isReturned = true ∧
    -- 2. A root container with the wrong tuple spine length still fails.
    assignPlace mirWriteCallerField0Body
      ⟨[some .uninit, some (.ref true 0 ⟨2⟩ [0] 0),
        some (.fieldCons (.int 1) .unit)],
       [0, 0, 0], 0, 0⟩
      ⟨⟨1⟩, [.deref]⟩ (.int 5) = none :=
  ⟨rfl, rfl, rfl, rfl⟩

end Anneal.PureLift
