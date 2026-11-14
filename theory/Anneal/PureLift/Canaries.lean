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
import Anneal.PureLift.Lens
import Anneal.PureLift.PermTree
import Anneal.PureLift.LoanGraph
import Anneal.PureLift.SpatialPin
import Anneal.PureLift.Plan
import Anneal.PureLift.BlockCfg
import Anneal.PureLift.Adapter

namespace Anneal.PureLift

/-!
# Verification Suite and Negative Falsification Canaries (`Canaries`)

End-to-end kernel-verified test suite exercising `PureLift` across:
- **Part I (`S1`–`S7`)**: single mutable borrow (`max_assign`), two-reference
  disjoint vs. aliased entry validation (`update_min`), shared vs. mutable
  aliasing (`shared_max`), two-phase diamond conditional reborrows
  (`two_phase_reborrow`), borrow-returning functions and lawful backward lenses
  (`choose_mut`), constructive loops (`count_up`), and modular call composition
  (`double_bounded`).
- **Part II (`H1`–`H5`)**: split sibling sub-place borrows and commutative loan
  release (`H1`), multi-region-group staggered termination with outlives order
  and 3-level reborrow chains (`H2`), hybrid functional-spatial pinning and
  reabsorption (`H3`), operational bridges to machine styles `M1`, `M2`, and
  `M3` (`H4`), and nested early return plus Goodhart vacuity rejection canaries
  (`H5`).
-/

/-- Reference value carrier for the `PureLift` verification suite. -/
inductive StdVal where
  | unit : StdVal
  | nat (n : Nat) : StdVal
  | bool (b : Bool) : StdVal
  | symBool (b : Bool) : StdVal
  | pair (fst snd : StdVal) : StdVal
  | refVal (lid : LoanId) (path : SubPath) : StdVal

def zipStdVal (cond vt vf : StdVal) : StdVal :=
  match cond with
  | .bool b => if b then vt else vf
  | .symBool b => if b then vt else vf
  | _ => vt

noncomputable def remapStdVal (oldLid newLid : LoanId) (v : StdVal) : StdVal :=
  @StdVal.rec (fun _ => StdVal)
    .unit
    (fun n => .nat n)
    (fun b => .bool b)
    (fun b => .symBool b)
    (fun _ _ ihA ihB => .pair ihA ihB)
    (fun lid path =>
      if lid == oldLid then .refVal newLid path else .refVal lid path)
    v

noncomputable def stdValAlg : ValAlgebra StdVal where
  defaultVal := .unit
  asBool v :=
    match v with
    | .bool b => some b
    | _ => none
  zipVal := zipStdVal
  getField idx v :=
    match idx, v with
    | 0, .pair a _ => some a
    | 1, .pair _ b => some b
    | _, _ => none
  setField idx v child :=
    match idx, v with
    | 0, .pair _ b => some (.pair child b)
    | 1, .pair a _ => some (.pair a child)
    | _, _ => none
  encodeRef lid path := .refVal lid path
  decodeRef v :=
    match v with
    | .refVal lid path => some (lid, path)
    | _ => none
  remapRefInVal := remapStdVal

def stdAdd (v1 v2 : StdVal) : Option StdVal :=
  match v1, v2 with
  | .nat n1, .nat n2 => some (.nat (n1 + n2))
  | _, _ => none

def stdAddNat (k : Nat) (v : StdVal) : Option StdVal :=
  stdAdd v (.nat k)

def stdInc (v : StdVal) : Option StdVal :=
  stdAddNat 1 v

def stdLtSym (v1 v2 : StdVal) : Option StdVal :=
  match v1, v2 with
  | .nat n1, .nat n2 => some (.symBool (Nat.blt n1 n2))
  | _, _ => none

def stdLtBool (v1 v2 : StdVal) : Option StdVal :=
  match v1, v2 with
  | .nat n1, .nat n2 => some (.bool (Nat.blt n1 n2))
  | _, _ => none

/-!
## Part I: Core Borrow and Control-Flow Scenarios (`S1`–`S7`)
-/

/-- **S1 (`max_assign`)**: `if *x < y { *x = y }`. -/
def s1MaxAssignPlan : FlowPlan StdVal :=
  .seq
    (.act (.assign (.localSub 2 [])
      (.binary stdLtSym (.derefSub 0 []) (.localSub 1 []))))
    (.branch (.use (.localSub 2 []))
      (.act (.assign (.derefSub 0 []) (.use (.localSub 1 []))))
      .skip)

theorem s1_max_assign_spec (vx vy : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .nat vx⟩, ⟨.byVal, .nat vy⟩]
      s1MaxAssignPlan
      (.constVal .unit) =
    .ok ⟨.unit, [if Nat.blt vx vy then .nat vy else .nat vx]⟩ := rfl

/-- **S2 (`update_min`)**: Two `&mut` parameters with entry aliasing checks. -/
def s2UpdateMinPlan : FlowPlan StdVal :=
  .seq
    (.act (.assign (.localSub 2 [])
      (.binary stdLtSym (.derefSub 0 []) (.derefSub 1 []))))
    (.branch (.use (.localSub 2 []))
      (.act (.assign (.derefSub 1 []) (.use (.derefSub 0 []))))
      (.act (.assign (.derefSub 0 []) (.use (.derefSub 1 [])))))

theorem s2_update_min_distinct_spec (vx vy : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .nat vx⟩, ⟨.mutRef 1 [], .nat vy⟩]
      s2UpdateMinPlan
      (.constVal .unit) =
    .ok ⟨.unit,
      [if Nat.blt vx vy then .nat vx else .nat vy,
       if Nat.blt vx vy then .nat vx else .nat vy]⟩ := rfl

theorem s2_update_min_aliased_fails (vx : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .nat vx⟩, ⟨.mutRef 0 [], .nat vx⟩]
      s2UpdateMinPlan
      (.constVal .unit) = .fail := rfl

/-- **S3 (`shared_max` vs. `max_assign_shared`)**: Shared borrows permit
aliasing, whereas `&mut` + `&` on the same root is rejected. -/
def s3SharedMaxPlan : FlowPlan StdVal :=
  .seq
    (.act (.assign (.localSub 2 [])
      (.binary stdLtSym (.derefSub 0 []) (.derefSub 1 []))))
    (.branch (.use (.localSub 2 []))
      (.act (.assign (.localSub 3 []) (.use (.derefSub 1 []))))
      (.act (.assign (.localSub 3 []) (.use (.derefSub 0 [])))))

theorem s3_shared_max_aliased_ok (va : Nat) :
    evalFnValue stdValAlg
      [⟨.sharedRef 0 [], .nat va⟩, ⟨.sharedRef 0 [], .nat va⟩]
      s3SharedMaxPlan
      (.use (.localSub 3 [])) =
    .ok ⟨if Nat.blt va va then .nat va else .nat va, []⟩ := rfl

theorem s3_max_assign_shared_aliased_fails (va : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .nat va⟩, ⟨.sharedRef 0 [], .nat va⟩]
      s1MaxAssignPlan
      (.constVal .unit) = .fail := rfl

/-- **S4 (`two_phase_reborrow`)**: Diamond conditional reborrow
`let r = if cond { &mut *x } else { &mut *y }; *r += a; endLoan(r); *x += b`. -/
def s4DiamondReborrowPlan : FlowPlan StdVal :=
  .seq
    (.branch (.use (.localSub 0 []))
      (.act (.borrow 5 .mutBorrow (.derefSub 1 [])))
      (.act (.borrow 5 .mutBorrow (.derefSub 2 []))))
    (.seq
      (.act (.assign (.derefSub 5 [])
        (.binary stdAdd (.derefSub 5 []) (.localSub 3 []))))
      (.seq
        (.act (.endLoan 2))
        (.act (.assign (.derefSub 1 [])
          (.binary stdAdd (.derefSub 1 []) (.localSub 4 []))))))

theorem s4_two_phase_reborrow_symbolic (cond : Bool) (vx vy a b : Nat) :
    evalFnValue stdValAlg
      [⟨.byVal, .symBool cond⟩,
       ⟨.mutRef 0 [], .nat vx⟩,
       ⟨.mutRef 1 [], .nat vy⟩,
       ⟨.byVal, .nat a⟩,
       ⟨.byVal, .nat b⟩]
      s4DiamondReborrowPlan
      (.constVal .unit) =
    .ok ⟨.unit,
      [if cond then .nat (vx + a + b) else .nat (vx + b),
       if cond then .nat vy else .nat (vy + a)]⟩ := by
  cases cond <;> rfl

/-- **S5 (`choose_mut` & `choose_test`)**: Function returning `&'a mut T` with
a lawful forward/backward lens and modular caller composition. -/
def s5ChoosePlan : FlowPlan StdVal :=
  .branch (.use (.localSub 0 []))
    (.act (.borrow 3 .mutBorrow (.derefSub 1 [])))
    (.act (.borrow 3 .mutBorrow (.derefSub 2 [])))

theorem s5_choose_mut_spec (cond : Bool) (vx vy vNew : Nat) :
    match evalFnReturningMut stdValAlg
      [⟨.byVal, .symBool cond⟩,
       ⟨.mutRef 0 [], .nat vx⟩,
       ⟨.mutRef 1 [], .nat vy⟩]
      s5ChoosePlan 3 with
    | .ok (fwdVal, backFn) =>
      fwdVal = (if cond then .nat vx else .nat vy) ∧
      backFn (.nat vNew) =
        some [if cond then .nat vNew else .nat vx,
              if cond then .nat vy else .nat vNew]
    | .fail => False := by
  cases cond <;> exact ⟨rfl, rfl⟩

def chooseCallSummary : CallSummary StdVal where
  returnsMutBorrow := true
  fwd pureVals mutVals :=
    match pureVals, mutVals with
    | [cond], [vx, vy] => some (zipStdVal cond vx vy)
    | _, _ => none
  back pureVals mutVals vFinal :=
    match pureVals, mutVals with
    | [cond], [vx, vy] =>
      some [zipStdVal cond vFinal vx, zipStdVal cond vy vFinal]
    | _, _ => none

def choosePairLens (cond : Bool) : Lens (StdVal × StdVal) StdVal where
  get xy := chooseCallSummary.fwd [.symBool cond] [xy.1, xy.2]
  put xy vNew :=
    match chooseCallSummary.back [.symBool cond] [xy.1, xy.2] vNew with
    | some [x', y'] => some (x', y')
    | _ => none

theorem s5_choosePairLens_lawful (cond : Bool) :
    LawfulLens (StdVal × StdVal) StdVal (choosePairLens cond) where
  get_put := by
    intro s a hGet
    cases s with
    | mk x y =>
      cases cond <;> (
        dsimp [choosePairLens, chooseCallSummary, zipStdVal] at hGet
        injection hGet with hEq
        subst hEq
        rfl)
  put_get := by
    intro s a s' hPut
    cases s with
    | mk x y =>
      cases cond <;> (
        dsimp [choosePairLens, chooseCallSummary, zipStdVal] at hPut
        injection hPut with hEq
        subst hEq
        rfl)
  put_put := by
    intro s a1 a2 s1 hPut1
    cases s with
    | mk x y =>
      cases cond <;> (
        dsimp [choosePairLens, chooseCallSummary, zipStdVal] at hPut1
        injection hPut1 with hEq
        subst hEq
        rfl)

def s5ChooseCallerPlan : FlowPlan StdVal :=
  .seq
    (.act (.call 4 chooseCallSummary
      [.use (.localSub 0 [])]
      [.derefSub 1 [], .derefSub 2 []]))
    (.seq
      (.act (.assign (.derefSub 4 [])
        (.binary stdAdd (.derefSub 4 []) (.localSub 3 []))))
      (.seq
        (.act (.endLoan 2))
        (.act (.assign (.derefSub 1 []) (.unary stdInc (.derefSub 1 []))))))

theorem s5_choose_caller_symbolic (cond : Bool) (vx vy delta : Nat) :
    evalFnValue stdValAlg
      [⟨.byVal, .symBool cond⟩,
       ⟨.mutRef 0 [], .nat vx⟩,
       ⟨.mutRef 1 [], .nat vy⟩,
       ⟨.byVal, .nat delta⟩]
      s5ChooseCallerPlan
      (.constVal .unit) =
    .ok ⟨.unit,
      [if cond then .nat (vx + delta + 1) else .nat (vx + 1),
       if cond then .nat vy else .nat (vy + delta)]⟩ := by
  cases cond <;> rfl

/-- **S6 (`count_up`)**: Constructive `while` loop and non-vacuity on
insufficient fuel. -/
def s6CountUpPlan (fuel : Nat) : FlowPlan StdVal :=
  .whileLoop fuel
    (.binary stdLtBool (.derefSub 0 []) (.localSub 1 []))
    (.act (.assign (.derefSub 0 []) (.unary stdInc (.derefSub 0 []))))

theorem s6_count_up_concrete :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .nat 2⟩, ⟨.byVal, .nat 5⟩]
      (s6CountUpPlan 3)
      (.constVal .unit) =
    .ok ⟨.unit, [.nat 5]⟩ := rfl

theorem s6_count_up_insufficient_fuel_fails :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .nat 2⟩, ⟨.byVal, .nat 5⟩]
      (s6CountUpPlan 1)
      (.constVal .unit) = .fail := rfl

/-- **S7 (`double_bounded`)**: Modular interprocedural call composition. -/
def addInPlaceSummary : CallSummary StdVal where
  returnsMutBorrow := false
  fwd pureVals mutVals :=
    match pureVals, mutVals with
    | [.nat _], [.nat _] => some .unit
    | _, _ => none
  back pureVals mutVals _ :=
    match pureVals, mutVals with
    | [.nat d], [.nat x] => some [.nat (x + d)]
    | _, _ => none

def s7DoubleCallPlan : FlowPlan StdVal :=
  .seq
    (.act (.call 2 addInPlaceSummary [.use (.localSub 1 [])] [.derefSub 0 []]))
    (.act (.call 2 addInPlaceSummary [.use (.localSub 1 [])] [.derefSub 0 []]))

theorem s7_double_bounded_spec (vx d : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .nat vx⟩, ⟨.byVal, .nat d⟩]
      s7DoubleCallPlan
      (.constVal .unit) =
    .ok ⟨.unit, [.nat (vx + d + d)]⟩ := rfl

/-!
## Part II: Held-Out Stress Scenarios (`H1`–`H5`) and Negative Canaries
-/

/-- **H1 Plan A**: Borrow `r0 = &mut (*p).0` (loan 1) and `r1 = &mut (*p).1`
(loan 2), swap them, end loan 1 then loan 2, and read root `*p` at `[]`. -/
def h1SplitSwapEnd12Plan : FlowPlan StdVal :=
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
              (.act (.endLoan 1))
              (.seq
                (.act (.endLoan 2))
                (.act (.assign (.localSub 4 []) (.use (.derefSub 0 []))))))))))

/-- **H1 Plan B**: Identical to Plan A except loan 2 (`&mut p.1`) ends before
loan 1 (`&mut p.0`). -/
def h1SplitSwapEnd21Plan : FlowPlan StdVal :=
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
              (.seq
                (.act (.endLoan 1))
                (.act (.assign (.localSub 4 []) (.use (.derefSub 0 []))))))))))

theorem h1_sibling_split_borrow_swap_spec (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h1SplitSwapEnd12Plan
      (.use (.localSub 4 [])) =
    .ok ⟨.pair (.nat v1) (.nat v0), [.pair (.nat v1) (.nat v0)]⟩ := rfl

theorem h1_sibling_end_commutes_spec (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h1SplitSwapEnd12Plan
      (.use (.localSub 4 [])) =
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h1SplitSwapEnd21Plan
      (.use (.localSub 4 [])) := rfl

def h1SharedAndMutSiblingsPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .shared (.derefSub 0 [0])))
    (.seq
      (.act (.borrow 2 .mutBorrow (.derefSub 0 [1])))
      (.seq
        (.act (.assign (.derefSub 2 [])
          (.binary stdAdd (.derefSub 1 []) (.derefSub 2 []))))
        (.seq
          (.act (.endLoan 2))
          (.act (.endLoan 1)))))

theorem h1_shared_and_mut_disjoint_siblings_ok (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h1SharedAndMutSiblingsPlan
      (.constVal .unit) =
    .ok ⟨.unit, [.pair (.nat v0) (.nat (v0 + v1))]⟩ := rfl

def h1MultiSharedLoanIdTrackingPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .shared (.derefSub 0 [0])))
    (.seq
      (.act (.borrow 2 .shared (.derefSub 0 [0])))
      (.seq
        (.act (.borrow 3 .mutBorrow (.derefSub 0 [1])))
        (.seq
          (.act (.endLoan 1))
          (.seq
            (.act (.assign (.derefSub 3 [])
              (.binary stdAdd (.derefSub 2 []) (.derefSub 3 []))))
            (.seq
              (.act (.endLoan 2))
              (.seq
                (.act (.endLoan 3))
                (.seq
                  (.act (.borrow 4 .mutBorrow (.derefSub 0 [0])))
                  (.seq
                    (.act (.assign (.derefSub 4 [])
                      (.unary stdInc (.derefSub 4 []))))
                    (.act (.endLoan 4))))))))))

theorem h1_multi_shared_loan_id_tracking_spec (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h1MultiSharedLoanIdTrackingPlan
      (.constVal .unit) =
    .ok ⟨.unit, [.pair (.nat (v0 + 1)) (.nat (v0 + v1))]⟩ := rfl

def h1BadMutWhileSecondSharedActivePlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .shared (.derefSub 0 [0])))
    (.seq
      (.act (.borrow 2 .shared (.derefSub 0 [0])))
      (.seq
        (.act (.endLoan 1))
        (.seq
          (.act (.borrow 3 .mutBorrow (.derefSub 0 [0])))
          (.seq (.act (.endLoan 3)) (.act (.endLoan 2))))))

theorem h1_reject_mut_while_second_shared_active (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h1BadMutWhileSecondSharedActivePlan
      (.constVal .unit) = .fail := rfl

def h1BadBorrowRootWhileFieldActivePlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.borrow 2 .mutBorrow (.derefSub 0 [])))
      (.seq (.act (.endLoan 2)) (.act (.endLoan 1))))

theorem h1_reject_root_borrow_while_field_active (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h1BadBorrowRootWhileFieldActivePlan
      (.constVal .unit) = .fail := rfl

def h1BadBorrowSubpathWhilePrefixActivePlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.borrow 2 .mutBorrow (.derefSub 0 [0, 1])))
      (.seq (.act (.endLoan 2)) (.act (.endLoan 1))))

theorem h1_reject_subpath_borrow_while_prefix_active (v0 v1 v2 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.pair (.nat v0) (.nat v1)) (.nat v2)⟩]
      h1BadBorrowSubpathWhilePrefixActivePlan
      (.constVal .unit) = .fail := rfl

/-- **H2**: Multi-region-group staggered termination with `requiredChildren`. -/
def h2DependentRegionSpecs : List (RegionGroupSpec StdVal) :=
  [ { groupId := 0
      requiredChildren := [1]
      inputPlaces := [.derefSub 1 []]
      outDsts := [2]
      fwdOuts := fun _ muts =>
        match muts with
        | [vx] => some [vx]
        | _ => none
      backFn := fun _ _ outVals deps =>
        match outVals, deps with
        | [.nat v0], [.nat vDep] =>
          match stdAdd (.nat v0) (.nat vDep) with
          | some vSum => some ([vSum], [])
          | none => none
        | _, _ => none },
    { groupId := 1
      requiredChildren := []
      inputPlaces := []
      outDsts := [3]
      fwdOuts := fun pureVals _ =>
        match pureVals with
        | [vy] => some [vy]
        | _ => none
      backFn := fun _ _ outVals _ =>
        match outVals with
        | [v1] => some ([], [v1])
        | _ => none } ]

def h2ValidMultiRegionPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.callMultiRegion [.constVal (.nat 10)] h2DependentRegionSpecs))
      (.seq
        (.act (.assign (.derefSub 3 [])
          (.unary (stdAddNat 5) (.derefSub 3 []))))
        (.seq
          (.act (.endRegionGroup 1))
          (.seq
            (.act (.assign (.derefSub 2 [])
              (.unary stdInc (.derefSub 2 []))))
            (.seq
              (.act (.endRegionGroup 0))
              (.act (.endLoan 1)))))))

theorem h2_multi_region_valid_order_and_reborrow_propagation_spec
    (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h2ValidMultiRegionPlan
      (.constVal .unit) =
    .ok ⟨.unit, [.pair (.nat (v0 + 1 + (10 + 5))) (.nat v1)]⟩ := rfl

def h2BadOutOfOrderRegionPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.callMultiRegion [.constVal (.nat 10)] h2DependentRegionSpecs))
      (.seq
        (.act (.endRegionGroup 0))
        (.seq
          (.act (.endRegionGroup 1))
          (.act (.endLoan 1)))))

theorem h2_multi_region_out_of_order_rejected (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h2BadOutOfOrderRegionPlan
      (.constVal .unit) = .fail := rfl

def h2BadEndRegionWhileOutputReborrowedPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.callMultiRegion [.constVal (.nat 10)] h2DependentRegionSpecs))
      (.seq
        (.act (.borrow 4 .mutBorrow (.derefSub 3 [])))
        (.act (.endRegionGroup 1))))

theorem h2_reject_end_region_while_output_reborrowed (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h2BadEndRegionWhileOutputReborrowedPlan
      (.constVal .unit) = .fail := rfl

def h2ThreeLevelReborrowPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 2 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.borrow 3 .mutBorrow (.derefSub 2 [])))
      (.seq
        (.act (.borrow 4 .mutBorrow (.derefSub 3 [])))
        (.seq
          (.act (.assign (.derefSub 4 [])
            (.binary stdAdd (.derefSub 4 []) (.localSub 1 []))))
          (.seq
            (.act (.endLoan 3))
            (.seq
              (.act (.assign (.derefSub 3 [])
                (.unary stdInc (.derefSub 3 []))))
              (.seq
                (.act (.endLoan 2))
                (.seq
                  (.act (.assign (.derefSub 2 [])
                    (.unary stdInc (.derefSub 2 []))))
                  (.act (.endLoan 1)))))))))

theorem h2_three_level_reborrow_chain_spec (v0 v1 delta : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩, ⟨.byVal, .nat delta⟩]
      h2ThreeLevelReborrowPlan
      (.constVal .unit) =
    .ok ⟨.unit, [.pair (.nat (v0 + delta + 1 + 1)) (.nat v1)]⟩ := rfl

/-- **H3**: Hybrid functional-spatial pinning and unpinned sibling isolation. -/
def h3HybridSpatialSiblingPlan (vSpatialNew : Nat) : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.borrow 2 .mutBorrow (.derefSub 0 [1])))
      (.seq
        (.act (.freezeSpatial 1 valueCellCodec))
        (.seq
          (.act (.assign (.derefSub 2 []) (.unary stdInc (.derefSub 2 []))))
          (.seq
            (.act (.mutateSpatial 0 0 [.init (.nat vSpatialNew)]))
            (.seq
              (.act (.reabsorbSpatial 1 valueCellCodec))
              (.seq
                (.act (.endLoan 1))
                (.act (.endLoan 2))))))))

theorem h3_hybrid_spatial_preserves_unpinned_sibling_spec
    (v0 v1 vSpatialNew : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      (h3HybridSpatialSiblingPlan vSpatialNew)
      (.constVal .unit) =
    .ok ⟨.unit, [.pair (.nat vSpatialNew) (.nat (v1 + 1))]⟩ := rfl

def h3BadPureWriteWhileSpatialPinnedPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.freezeSpatial 1 valueCellCodec))
      (.act (.assign (.derefSub 1 []) (.constVal (.nat 99)))))

def h3BadEndLoanWhileSpatialPinnedPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.freezeSpatial 1 valueCellCodec))
      (.act (.endLoan 1)))

theorem h3_reject_pure_write_and_end_while_spatial_pinned (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h3BadPureWriteWhileSpatialPinnedPlan
      (.constVal .unit) = .fail ∧
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h3BadEndLoanWhileSpatialPinnedPlan
      (.constVal .unit) = .fail :=
  ⟨rfl, rfl⟩

def h3BadUninitReabsorbPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.freezeSpatial 1 valueCellCodec))
      (.seq
        (.act (.mutateSpatial 0 0 [.uninit]))
        (.seq
          (.act (.reabsorbSpatial 1 valueCellCodec))
          (.act (.endLoan 1)))))

theorem h3_reject_uninit_reabsorb (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h3BadUninitReabsorbPlan
      (.constVal .unit) = .fail := rfl

/-- **H4**: End-to-end operational bridges for machine styles `M1`, `M2`, and
`M3`. -/
def m1MaxAssignStep (vx vy : Nat) : Nat → M1StepResult Nat StdVal
  | 0 => .next 1
  | _ => .ret ⟨.unit, [if Nat.blt vx vy then .nat vy else .nat vx]⟩

theorem h4_m1_bridge_sound (vx vy : Nat) :
    let ad := m1OperationalAdapter (m1MaxAssignStep vx vy) (fun _ s => s = 0)
    Exists fun k => Exists fun mFinal => Exists fun out =>
      ad.ExecutesTo (.running 0) k mFinal ∧
      ad.FinalLoansRel out mFinal ∧
      out = ⟨.unit, [if Nat.blt vx vy then .nat vy else .nat vx]⟩ := by
  refine pure_lift_sound
    (m1OperationalAdapter (m1MaxAssignStep vx vy) (fun _ s => s = 0))
    stdValAlg
    [⟨.mutRef 0 [], .nat vx⟩, ⟨.byVal, .nat vy⟩]
    s1MaxAssignPlan
    (.constVal .unit)
    (fun out => out = ⟨.unit, [if Nat.blt vx vy then .nat vy else .nat vx]⟩)
    (.running 0)
    ⟨_, ⟨rfl, rfl⟩⟩
    rfl
    ?_
  intro _ out _ _ hEval
  injection hEval with hOut
  subst hOut
  refine ⟨2,
    ⟨.returned ⟨.unit, [if Nat.blt vx vy then .nat vy else .nat vx]⟩,
     rfl, rfl⟩⟩

def m2MaxAssignStep (vx vy : Nat) : Nat → M2StepResult Nat Nat StdVal
  | 0 => .step [vx, vy] 1
  | _ => .terminated ⟨.unit, [if Nat.blt vx vy then .nat vy else .nat vx]⟩

theorem h4_m2_bridge_sound (vx vy : Nat) :
    let ad := m2OperationalAdapter (m2MaxAssignStep vx vy) (fun _ s => s = 0)
    Exists fun k => Exists fun mFinal => Exists fun out =>
      ad.ExecutesTo ⟨0, [], none⟩ k mFinal ∧
      ad.FinalLoansRel out mFinal ∧
      out = ⟨.unit, [if Nat.blt vx vy then .nat vy else .nat vx]⟩ := by
  refine pure_lift_sound
    (m2OperationalAdapter (m2MaxAssignStep vx vy) (fun _ s => s = 0))
    stdValAlg
    [⟨.mutRef 0 [], .nat vx⟩, ⟨.byVal, .nat vy⟩]
    s1MaxAssignPlan
    (.constVal .unit)
    (fun out => out = ⟨.unit, [if Nat.blt vx vy then .nat vy else .nat vx]⟩)
    ⟨0, [], none⟩
    ⟨_, ⟨rfl, ⟨rfl, rfl, trivial⟩⟩⟩
    rfl
    ?_
  intro _ out _ _ hEval
  injection hEval with hOut
  subst hOut
  refine ⟨1 + 1,
    ⟨⟨1, [] ++ [vx, vy],
      some ⟨.unit, [if Nat.blt vx vy then .nat vy else .nat vx]⟩⟩,
    M2ExecutesTo.trans
      (M2ExecutesTo.step_emit rfl)
      (M2ExecutesTo.step_term rfl),
    rfl⟩⟩

def m3SwapHeapStep (v0 v1 : Nat) :
    List (M3Cell StdVal) → M1StepResult (List (M3Cell StdVal)) StdVal
  | _ => .ret ⟨.pair (.nat v1) (.nat v0), [.pair (.nat v1) (.nat v0)]⟩

theorem h4_m3_tree_borrows_bridge_sound (v0 v1 : Nat) :
    let sp := m3SpatialModel StdVal
    let initHeap : List (M3Cell StdVal) :=
      [ ⟨0, 0, [0], 1, .activeUnique, .init (.nat v0)⟩,
        ⟨0, 1, [1], 2, .activeUnique, .init (.nat v1)⟩ ]
    let splitPerm : PermTree :=
      .split [([0], .mutLocked 1), ([1], .mutLocked 2)]
    let ad := m3OperationalAdapter (m3SwapHeapStep v0 v1) (fun _ _ => True)
    sp.ownSubPlace initHeap (0, 0) [0] splitPerm (.nat v0) ∧
    sp.ownSubPlace initHeap (0, 1) [1] splitPerm (.nat v1) ∧
    (Exists fun k => Exists fun mFinal => Exists fun out =>
      ad.ExecutesTo ⟨initHeap, none⟩ k mFinal ∧
      ad.FinalLoansRel out mFinal ∧
      out = ⟨.pair (.nat v1) (.nat v0), [.pair (.nat v1) (.nat v0)]⟩) := by
  refine ⟨⟨rfl, ⟨rfl, Or.inl rfl⟩⟩, ⟨rfl, ⟨rfl, Or.inl rfl⟩⟩, ?_⟩
  refine pure_lift_sound
    (m3OperationalAdapter (m3SwapHeapStep v0 v1) (fun _ _ => True))
    stdValAlg
    [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
    h1SplitSwapEnd12Plan
    (.use (.localSub 4 []))
    (fun out => out = ⟨.pair (.nat v1) (.nat v0), [.pair (.nat v1) (.nat v0)]⟩)
    ⟨[ ⟨0, 0, [0], 1, .activeUnique, .init (.nat v0)⟩,
       ⟨0, 1, [1], 2, .activeUnique, .init (.nat v1)⟩ ], none⟩
    ⟨_, ⟨rfl, ⟨rfl, trivial⟩⟩⟩
    rfl
    ?_
  intro _ out _ _ hEval
  injection hEval with hOut
  subst hOut
  refine ⟨1,
    ⟨⟨[ ⟨0, 0, [0], 1, .activeUnique, .init (.nat v0)⟩,
        ⟨0, 1, [1], 2, .activeUnique, .init (.nat v1)⟩ ],
      some ⟨.pair (.nat v1) (.nat v0), [.pair (.nat v1) (.nat v0)]⟩⟩,
    M3ExecutesTo.step_ret rfl,
    rfl⟩⟩

/-- **H5**: Nested early return inside sub-borrows and Goodhart rejection
canaries. -/
def h5EarlyReturnNestedSubBorrowsPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 2 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.borrow 3 .mutBorrow (.derefSub 2 [])))
      (.seq
        (.branch (.use (.localSub 1 []))
          (.seq
            (.act (.assign (.derefSub 3 [])
              (.unary (stdAddNat 10) (.derefSub 3 []))))
            (.earlyReturn [2, 1] [] (.constVal (.nat 1))))
          (.act (.endLoan 2)))
        (.seq
          (.act (.assign (.derefSub 2 [])
            (.unary (stdAddNat 100) (.derefSub 2 []))))
          (.act (.endLoan 1)))))

theorem h5_early_return_branch_taken_spec (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩, ⟨.byVal, .bool true⟩]
      h5EarlyReturnNestedSubBorrowsPlan
      (.constVal (.nat 0)) =
    .ok ⟨.nat 1, [.pair (.nat (v0 + 10)) (.nat v1)]⟩ := rfl

theorem h5_early_return_branch_not_taken_spec (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩, ⟨.byVal, .bool false⟩]
      h5EarlyReturnNestedSubBorrowsPlan
      (.constVal (.nat 0)) =
    .ok ⟨.nat 0, [.pair (.nat (v0 + 100)) (.nat v1)]⟩ := rfl

def h5GoodhartEarlyReturnUnendedLoanPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 2 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.borrow 3 .mutBorrow (.derefSub 2 [])))
      (.earlyReturn [2] [] (.constVal (.nat 1))))

theorem h5_goodhart_early_return_unended_loan_fails (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h5GoodhartEarlyReturnUnendedLoanPlan
      (.constVal (.nat 0)) = .fail := rfl

def h5GoodhartOutOfOrderEndLoanPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 2 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.borrow 3 .mutBorrow (.derefSub 2 [])))
      (.seq
        (.act (.endLoan 1))
        (.act (.endLoan 2))))

theorem h5_goodhart_out_of_order_end_loan_fails (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h5GoodhartOutOfOrderEndLoanPlan
      (.constVal .unit) = .fail := rfl

def h5GoodhartDoubleEndLoanPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.endLoan 1))
      (.act (.endLoan 1)))

theorem h5_goodhart_double_end_loan_fails (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h5GoodhartDoubleEndLoanPlan
      (.constVal .unit) = .fail := rfl

def h5GoodhartUnendedLoanAtReturnPlan : FlowPlan StdVal :=
  .act (.borrow 1 .mutBorrow (.derefSub 0 [0]))

theorem h5_goodhart_unended_loan_at_normal_return_fails (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      h5GoodhartUnendedLoanAtReturnPlan
      (.constVal .unit) = .fail := rfl

def h5GoodhartReadLocalWhileMutBorrowedPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 1 .mutBorrow (.localSub 0 [])))
    (.seq
      (.act (.assign (.derefSub 1 []) (.constVal (.nat 99))))
      (.seq
        (.act (.assign (.localSub 2 []) (.use (.localSub 0 []))))
        (.act (.endLoan 0))))

theorem h5_goodhart_read_local_while_mut_borrowed_fails (v0 : Nat) :
    evalFnValue stdValAlg
      [⟨.byVal, .nat v0⟩]
      h5GoodhartReadLocalWhileMutBorrowedPlan
      (.use (.localSub 2 [])) = .fail := rfl

def h5GoodhartAliasedBranchJoinPlan : FlowPlan StdVal :=
  .branchExplicitJoin (.use (.localSub 0 []))
    .skip
    .skip
    [(1, 2), (1, 3)]

theorem h5_goodhart_aliased_branch_join_fails (cond : Bool) :
    evalFnValue stdValAlg
      [⟨.byVal, .symBool cond⟩]
      h5GoodhartAliasedBranchJoinPlan
      (.constVal .unit) = .fail := rfl

/-! ## Part III: Exhaustive Plan, BlockCfg, and Adapter Regression Suite -/

/-- Symbolic branch merge preserves locals at index $\ge 8$ and across unequal
local list lengths. -/
def highLocalBranchPlan : FlowPlan StdVal :=
  .seq
    (.branch (.use (.localSub 0 []))
      (.act (.assign (.localSub 10 []) (.constVal (.nat 77))))
      (.act (.assign (.localSub 2 []) (.constVal (.nat 33)))))
    (.act (.assign (.localSub 11 []) (.use (.localSub 10 []))))

theorem high_local_branch_join_preserves_above_eight (cond : Bool) :
    evalFnValue stdValAlg
      [⟨.byVal, .symBool cond⟩]
      highLocalBranchPlan
      (.use (.localSub 11 [])) =
    .ok ⟨if cond then .nat 77 else .unit, []⟩ := by
  cases cond <;> rfl

/-- `.branchExplicitJoin` remaps distinct branch-local loan IDs (`2` in the
true arm vs. `3` in the false arm after a scratch loan `2` ends) into canonical
loan `2` at the join point. -/
def explicitJoinRemapLoanIdsPlan : FlowPlan StdVal :=
  .seq
    (.branchExplicitJoin (.use (.localSub 0 []))
      (.seq
        (.act (.borrow 3 .mutBorrow (.derefSub 1 [])))
        (.seq
          (.act (.borrow 4 .shared (.localSub 0 [])))
          (.act (.endLoan 3))))
      (.seq
        (.act (.borrow 4 .shared (.localSub 0 [])))
        (.seq
          (.act (.endLoan 2))
          (.act (.borrow 3 .mutBorrow (.derefSub 2 [])))))
      [(2, 3)])
    (.seq
      (.act (.assign (.derefSub 3 []) (.constVal (.nat 50))))
      (.act (.endLoan 2)))

theorem explicit_join_remaps_distinct_branch_loan_ids
    (cond : Bool) (vx vy : Nat) :
    evalFnValue stdValAlg
      [⟨.byVal, .symBool cond⟩,
       ⟨.mutRef 0 [], .nat vx⟩,
       ⟨.mutRef 1 [], .nat vy⟩]
      explicitJoinRemapLoanIdsPlan
      (.constVal .unit) =
    .ok ⟨.unit,
      [if cond then .nat 50 else .nat vx,
       if cond then .nat vy else .nat 50]⟩ := by
  cases cond <;> rfl

/-- `.branchExplicitJoin` fails closed when a join pair names a nonexistent loan
ID. -/
theorem explicit_join_rejects_nonexistent_loan_id (cond : Bool) :
    evalFnValue stdValAlg
      [⟨.byVal, .symBool cond⟩]
      (.branchExplicitJoin (.use (.localSub 0 [])) .skip .skip [(99, 99)])
      (.constVal .unit) = .fail := rfl

/-- Symbolic branch joining two `.call`s that return mutable borrows (`lensCall`
targets) preserves both backward lenses under `.choice` and writes back to the
selected caller-owned referent when the joined loan ends. -/
def singleMutIdSummary (offset : Nat) : CallSummary StdVal where
  returnsMutBorrow := true
  fwd _ mutVals :=
    match mutVals with
    | [.nat v] => some (.nat (v + offset))
    | _ => none
  back _ _ vFinal :=
    match vFinal with
    | .nat vf => some [.nat (vf + offset)]
    | _ => none

def branchJoinLensCallsPlan : FlowPlan StdVal :=
  .seq
    (.branch (.use (.localSub 0 []))
      (.act (.call 3 (singleMutIdSummary 10) [] [.derefSub 1 []]))
      (.act (.call 3 (singleMutIdSummary 20) [] [.derefSub 2 []])))
    (.seq
      (.act (.assign (.derefSub 3 []) (.constVal (.nat 100))))
      (.act (.endLoan 2)))

theorem branch_join_lens_calls_writeback_verified
    (cond : Bool) (vx vy : Nat) :
    evalFnValue stdValAlg
      [⟨.byVal, .symBool cond⟩,
       ⟨.mutRef 0 [], .nat vx⟩,
       ⟨.mutRef 1 [], .nat vy⟩]
      branchJoinLensCallsPlan
      (.constVal .unit) =
    .ok ⟨.unit,
      [if cond then .nat 110 else .nat vx,
       if cond then .nat vy else .nat 120]⟩ := by
  cases cond <;> rfl

/-- Symbolic branch joining two active region groups with matching metadata
merges their `backFn`s under `cond`, while mismatched region-group metadata
fails closed. -/
def regionSpecWithAdd (k : Nat) : RegionGroupSpec StdVal where
  groupId := 0
  requiredChildren := []
  inputPlaces := [.derefSub 1 []]
  outDsts := [2]
  fwdOuts := fun _ muts =>
    match muts with
    | [vx] => some [vx]
    | _ => none
  backFn := fun _ _ outVals _ =>
    match outVals with
    | [.nat vOut] => some ([.nat (vOut + k)], [])
    | _ => none

def branchJoinRegionGroupsPlan : FlowPlan StdVal :=
  .seq
    (.branch (.use (.localSub 0 []))
      (.act (.callMultiRegion [] [regionSpecWithAdd 5]))
      (.act (.callMultiRegion [] [regionSpecWithAdd 50])))
    (.seq
      (.act (.assign (.derefSub 2 []) (.constVal (.nat 300))))
      (.act (.endRegionGroup 0)))

theorem branch_join_region_groups_merges_backFn (cond : Bool) (vx : Nat) :
    evalFnValue stdValAlg
      [⟨.byVal, .symBool cond⟩, ⟨.mutRef 0 [], .nat vx⟩]
      branchJoinRegionGroupsPlan
      (.constVal .unit) =
    .ok ⟨.unit, [if cond then .nat 305 else .nat 350]⟩ := by
  cases cond <;> rfl

theorem branch_join_mismatched_region_groups_rejected
    (cond : Bool) (vx : Nat) :
    evalFnValue stdValAlg
      [⟨.byVal, .symBool cond⟩, ⟨.mutRef 0 [], .nat vx⟩]
      (.branch (.use (.localSub 0 []))
        (.act (.callMultiRegion [] [regionSpecWithAdd 5]))
        (.act (.callMultiRegion []
          [{ regionSpecWithAdd 50 with groupId := 9 }])))
      (.constVal .unit) = .fail := rfl

/-- Spatial provenance counter takes `max st1.nextSpatialTag st2.nextSpatialTag`
across symbolic branch joins so post-join `freezeSpatial` never reuses an
in-branch tag. -/
def branchSpatialTagFreshnessPlan : FlowPlan StdVal :=
  .seq
    (.act (.borrow 2 .mutBorrow (.derefSub 1 [])))
    (.seq
      (.branch (.use (.localSub 0 []))
        (.seq
          (.act (.freezeSpatial 1 valueCellCodec))
          (.act (.reabsorbSpatial 1 valueCellCodec)))
        .skip)
      (.seq
        (.act (.freezeSpatial 1 valueCellCodec))
        (.seq
          (.act (.mutateSpatial 1 1 [.init (.nat 88)]))
          (.seq
            (.act (.reabsorbSpatial 1 valueCellCodec))
            (.act (.endLoan 1))))))

theorem branch_spatial_tag_freshness_verified (cond : Bool) (vx : Nat) :
    evalFnValue stdValAlg
      [⟨.byVal, .symBool cond⟩, ⟨.mutRef 0 [], .nat vx⟩]
      branchSpatialTagFreshnessPlan
      (.constVal .unit) =
    .ok ⟨.unit, [.nat 88]⟩ := rfl

/-- Output-free region group (`outDsts = []`) reserves its `lockLid` in
`st.loans` so a subsequent sibling borrow gets a distinct `LoanId` and does not
collide when ending. -/
def outputFreeRegionSpec : RegionGroupSpec StdVal where
  groupId := 0
  requiredChildren := []
  inputPlaces := [.derefSub 0 [0]]
  outDsts := []
  fwdOuts := fun _ _ => some []
  backFn := fun _ muts _ _ =>
    match muts with
    | [.nat v0] => some ([.nat (v0 + 7)], [])
    | _ => none

def outputFreeRegionThenSiblingBorrowPlan : FlowPlan StdVal :=
  .seq
    (.act (.callMultiRegion [] [outputFreeRegionSpec]))
    (.seq
      (.act (.borrow 1 .mutBorrow (.derefSub 0 [1])))
      (.seq
        (.act (.assign (.derefSub 1 []) (.constVal (.nat 42))))
        (.seq
          (.act (.endLoan 2))
          (.act (.endRegionGroup 0)))))

theorem output_free_region_no_lockLid_collision (v0 v1 : Nat) :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      outputFreeRegionThenSiblingBorrowPlan
      (.constVal .unit) =
    .ok ⟨.unit, [.pair (.nat (v0 + 7)) (.nat 42)]⟩ := rfl

/-- `PrimAction.endLoanAtLocal` retires a freshly allocated reborrow on every
iteration of a `.whileLoop`. -/
def loopReborrowWithEndLoanAtLocalPlan (fuel : Nat) : FlowPlan StdVal :=
  .whileLoop fuel
    (.binary stdLtBool (.derefSub 0 []) (.localSub 1 []))
    (.seq
      (.act (.borrow 2 .mutBorrow (.derefSub 0 [])))
      (.seq
        (.act (.assign (.derefSub 2 []) (.unary stdInc (.derefSub 2 []))))
        (.act (.endLoanAtLocal 2))))

theorem loop_reborrow_with_endLoanAtLocal_verified :
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .nat 1⟩, ⟨.byVal, .nat 4⟩]
      (loopReborrowWithEndLoanAtLocalPlan 4)
      (.constVal .unit) =
    .ok ⟨.unit, [.nat 4]⟩ := rfl

/-- Concrete `BasicBlock` multi-block execution and `CfgCertificate` soundness
equivalence with `evalPlan`. -/
def sampleTwoBlockCfg : List (BasicBlock StdVal) :=
  [ ⟨.act (.assign (.localSub 1 []) (.constVal (.nat 20))), .goto 1⟩
  , ⟨.act (.assign (.localSub 1 []) (.unary stdInc (.localSub 1 []))),
     .ret (.use (.localSub 1 []))⟩
  ]

theorem blockCfg_two_block_exec_and_equiv_test :
    (match initFnState stdValAlg [⟨.byVal, .nat 0⟩] with
     | .ok st0 =>
       runBlockCfg (stepBasicBlock stdValAlg sampleTwoBlockCfg) 0 st0 3 =
         .ret ⟨.nat 21, []⟩ ∧
       evalFnValue stdValAlg [⟨.byVal, .nat 0⟩]
         (.seq
           (.act (.assign (.localSub 1 []) (.constVal (.nat 20))))
           (.act (.assign (.localSub 1 []) (.unary stdInc (.localSub 1 [])))))
         (.use (.localSub 1 [])) =
         .ok ⟨.nat 21, []⟩
     | .fail => False) :=
  ⟨rfl, rfl⟩

/-- `M2ExecutesTo.step_choice` and `m3SpatialModel.disjointSubPlaces`
exhaustive tests. -/
def m2ChoiceStep : Nat → M2StepResult Nat Nat StdVal
  | 0 => .choice (fun s' => s' = 1 ∨ s' = 2)
  | _ => .terminated ⟨.nat 99, []⟩

theorem m2_choice_and_m3_subPathDisjoint_tests :
    M2ExecutesTo m2ChoiceStep ⟨0, [], none⟩ (1 + 1)
      ⟨1, [], some ⟨.nat 99, []⟩⟩ ∧
    subPathDisjoint [0] [0, 1] = false ∧
    subPathDisjoint [0, 1] [0] = false ∧
    subPathDisjoint [0, 1] [0, 2] = true ∧
    subPathDisjoint [0] [1] = true := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  exact M2ExecutesTo.trans
    (M2ExecutesTo.step_choice rfl (Or.inl rfl))
    (M2ExecutesTo.step_term rfl)

/-- `m3SpatialModel.ownSubPlace` projects `getPathPerm path perm` through split
permission trees and rejects mismatched loan tags (`c.tag ≠ lid`). -/
theorem m3_ownSubPlace_projects_split_and_checks_loan_tag :
    let sp := m3SpatialModel StdVal
    let heap : List (M3Cell StdVal) :=
      [ ⟨0, 0, [0], 1, .activeUnique, .init (.nat 10)⟩,
        ⟨0, 0, [1], 2, .frozen, .init (.nat 20)⟩ ]
    let splitPerm : PermTree :=
      .split [([0], .mutLocked 1), ([1], .shared [2])]
    sp.ownSubPlace heap (0, 0) [0] splitPerm (.nat 10) ∧
    sp.ownSubPlace heap (0, 0) [1] splitPerm (.nat 20) ∧
    ¬ sp.ownSubPlace heap (0, 0) [0] (.mutLocked 99) (.nat 10) := by
  refine ⟨⟨rfl, ⟨rfl, Or.inl rfl⟩⟩, ⟨rfl, ⟨rfl, rfl⟩⟩, ?_⟩
  intro hBad
  cases hBad with
  | intro _ hTag =>
    cases hTag with
    | intro hEq _ => nomatch hEq

/-- `FlowPlan.branchExplicitJoin` short-circuits on concrete boolean conditions
(`.bool true` / `.bool false`), executing only the taken arm. -/
theorem branchExplicitJoin_concrete_bool_short_circuits :
    let plan : FlowPlan StdVal :=
      .branchExplicitJoin (.use (.localSub 0 []))
        (.act (.assign (.localSub 1 []) (.constVal (.nat 42))))
        (.act (.endLoan 99))
        []
    evalFnValue stdValAlg [⟨.byVal, .bool true⟩] plan (.use (.localSub 1 [])) =
      .ok ⟨.nat 42, []⟩ := rfl

/-- `joinSymState` rejects branch merges when `st1.regionDeposits` and
`st2.regionDeposits` have different lengths. -/
theorem joinSymState_rejects_unequal_regionDeposits :
    let st1 : SymState StdVal := ⟨[], [], [], [.nat 1], [], 0⟩
    let st2 : SymState StdVal := ⟨[], [], [], [.nat 1, .nat 2], [], 0⟩
    joinSymState stdValAlg (.symBool true) st1 st2 = none := rfl

/-- `FlowPlan.earlyReturn` evaluates `retExpr` before running `cleanupLoans` and
`cleanupGroups`, allowing `return *r` where `r`'s loan is retired by the return
cleanup. -/
theorem earlyReturn_evaluates_retExpr_before_cleanup (v0 v1 : Nat) :
    let plan : FlowPlan StdVal :=
      .seq
        (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
        (.seq
          (.act (.assign (.derefSub 1 [])
            (.unary (stdAddNat 7) (.derefSub 1 []))))
          (.earlyReturn [1] [] (.use (.derefSub 1 []))))
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      plan
      (.constVal (.nat 0)) =
    .ok ⟨.nat (v0 + 7), [.pair (.nat (v0 + 7)) (.nat v1)]⟩ := rfl

/-- `applyOneJoinPair` remaps encoded references stored inside loan cell values
(`e2.cell.val` and `e.cell.val`) in addition to `st2.locals`. -/
theorem applyOneJoinPair_remaps_loan_cell_ref_values :
    let e0 : LoanEntry StdVal :=
      ⟨0, .activeMut, ⟨.refVal 1 [], .unborrowed⟩, .rootParam 0⟩
    let e1Active : LoanEntry StdVal :=
      ⟨1, .activeMut, ⟨.nat 55, .unborrowed⟩, .direct (.localReg 0) []⟩
    let e2Ended : LoanEntry StdVal :=
      ⟨2, .ended, ⟨.nat 0, .unborrowed⟩, .direct (.localReg 0) []⟩
    let st1 : SymState StdVal :=
      ⟨[⟨.nat 55, .mutLocked 1⟩], [e0, e1Active, e2Ended], [], [], [], 0⟩
    let e0In2 : LoanEntry StdVal :=
      ⟨0, .activeMut, ⟨.refVal 2 [], .unborrowed⟩, .rootParam 0⟩
    let e1Ended : LoanEntry StdVal :=
      ⟨1, .ended, ⟨.nat 0, .unborrowed⟩, .direct (.localReg 0) []⟩
    let e2Active : LoanEntry StdVal :=
      ⟨2, .activeMut, ⟨.refVal 2 [0], .unborrowed⟩, .direct (.localReg 0) []⟩
    let st2 : SymState StdVal :=
      ⟨[⟨.nat 55, .mutLocked 2⟩], [e0In2, e1Ended, e2Active], [], [], [], 0⟩
    match applyOneJoinPair stdValAlg 1 2 st1 st2 with
    | some st2' =>
      match findLoan 0 st2'.loans, findLoan 1 st2'.loans with
      | some e0', some e1' =>
        e0'.cell.val = .refVal 1 [] ∧ e1'.cell.val = .refVal 1 [0]
      | _, _ => False
    | none => False :=
  ⟨rfl, rfl⟩

/-- Exhaustive unit tests for `FlowPlan.whileLoop` (early return propagation,
fuel exhaustion failure, and non-boolean condition failure), `initFnState`
(duplicate/overlapping parameter `rootId` rejection and disjoint sibling
sub-path acceptance), and `evalFnReturningMut` negative guards. -/
theorem plan_whileLoop_initFnState_and_returningMut_exhaustive_tests :
    -- 1. `.whileLoop` propagates `.earlyReturn` immediately on iteration 1:
    evalFnValue stdValAlg [⟨.byVal, .bool true⟩]
      (.whileLoop 5 (.use (.localSub 0 []))
        (.earlyReturn [] [] (.constVal (.nat 77))))
      (.constVal (.nat 0)) = .ok ⟨.nat 77, []⟩ ∧
    -- 2. `.whileLoop` fails closed when fuel is exhausted while condition is
    -- true, or when condition is non-boolean:
    evalFnValue stdValAlg [⟨.byVal, .bool true⟩]
      (.whileLoop 2 (.use (.localSub 0 [])) .skip)
      (.constVal (.nat 0)) = .fail ∧
    evalFnValue stdValAlg [⟨.byVal, .nat 5⟩]
      (.whileLoop 2 (.use (.localSub 0 [])) .skip)
      (.constVal (.nat 0)) = .fail ∧
    -- 3. `initFnState` rejects overlapping parameter borrows on the same
    -- `rootId`, while allowing disjoint sibling sub-paths `[0]` and `[1]` or
    -- multiple `.sharedRef` parameters on the same `rootId`:
    initFnState stdValAlg
      [⟨.mutRef 0 [], .nat 1⟩, ⟨.mutRef 0 [], .nat 2⟩] = .fail ∧
    initFnState stdValAlg
      [⟨.sharedRef 0 [], .nat 1⟩, ⟨.mutRef 0 [], .nat 2⟩] = .fail ∧
    initFnState stdValAlg
      [⟨.mutRef 0 [0], .nat 1⟩, ⟨.mutRef 0 [0, 1], .nat 2⟩] = .fail ∧
    (match initFnState stdValAlg
        [⟨.mutRef 0 [0], .nat 1⟩, ⟨.mutRef 0 [1], .nat 2⟩] with
     | .ok _ => True
     | .fail => False) ∧
    (match initFnState stdValAlg
        [⟨.sharedRef 0 [], .nat 1⟩, ⟨.sharedRef 0 [], .nat 1⟩] with
     | .ok _ => True
     | .fail => False) ∧
    -- 4. `evalFnReturningMut` rejects returning a non-reference local or
    -- returning a shared reference as mutable:
    (match evalFnReturningMut stdValAlg [⟨.byVal, .nat 10⟩] .skip 0 with
     | .fail => True
     | .ok _ => False) ∧
    (match evalFnReturningMut stdValAlg [⟨.sharedRef 0 [], .nat 10⟩]
        .skip 0 with
     | .fail => True
     | .ok _ => False) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, trivial, trivial, trivial, trivial⟩

/-- Exhaustive unit tests for `BlockCfg` terminators (`BlockTerm.branch`,
`BlockTerm.goto`, `BlockTerm.ret`), out-of-bounds block IDs (`.fault`), zero
fuel (`.diverged`), and `cfg_certificate_step_sound`. -/
def sampleBranchBlockCfg : List (BasicBlock StdVal) :=
  [ ⟨.skip, .branch (.use (.localSub 0 [])) 1 2⟩
  , ⟨.act (.assign (.localSub 1 []) (.constVal (.nat 10))),
     .goto 3⟩
  , ⟨.act (.assign (.localSub 1 []) (.constVal (.nat 20))),
     .goto 3⟩
  , ⟨.skip, .ret (.use (.localSub 1 []))⟩
  ]

theorem blockCfg_terminators_and_certificate_exhaustive_tests :
    (match initFnState stdValAlg [⟨.byVal, .bool true⟩] with
     | .ok stT =>
       runBlockCfg (stepBasicBlock stdValAlg sampleBranchBlockCfg) 0 stT 4 =
         .ret ⟨.nat 10, []⟩ ∧
       runBlockCfg (stepBasicBlock stdValAlg sampleBranchBlockCfg) 99 stT 2 =
         .fault ∧
       runBlockCfg (stepBasicBlock stdValAlg sampleBranchBlockCfg) 0 stT 0 =
         .diverged
     | .fail => False) ∧
    (match initFnState stdValAlg [⟨.byVal, .bool false⟩] with
     | .ok stF =>
       runBlockCfg (stepBasicBlock stdValAlg sampleBranchBlockCfg) 0 stF 4 =
         .ret ⟨.nat 20, []⟩
     | .fail => False) ∧
    runBlockCfg
      (stepBasicBlock stdValAlg
        [⟨.act (.assign (.localSub 1 []) (.constVal (.nat 42))),
          .ret (.use (.localSub 1 []))⟩])
      0 ⟨[⟨.nat 0, .unborrowed⟩], [], [], [], [], 0⟩ 1 =
      .ret ⟨.nat 42, []⟩ := by
  refine ⟨⟨rfl, rfl, rfl⟩, rfl, ?_⟩
  exact cfg_certificate_step_sound stdValAlg
    [⟨.byVal, .nat 0⟩]
    (.act (.assign (.localSub 1 []) (.constVal (.nat 42))))
    (.use (.localSub 1 []))
    ⟨[⟨.nat 0, .unborrowed⟩], [], [], [], [], 0⟩
    ⟨.nat 42, []⟩
    rfl
    rfl

/-- Exhaustive regression tests for:
1. `callMultiRegion` inside a `.whileLoop` (replacing inactive
   `RegionGroupEntry` entries across iterations so later iterations are not
   shadowed by iteration `0`, and rejecting duplicate active `groupId`),
2. `applyOneJoinPair` remapping loan IDs inside nested `StdVal.pair` values,
   `regionGroups`, and `regionDeposits`,
3. Multi-argument `.call` returning a mutable borrow over two disjoint sub-paths
   (`[0]` and `[1]`) of the same owner (`releaseLoanPermAtPath`), and
4. Symbolic branches where one arm takes `.earlyReturn` and the other arm
   continues into subsequent statements (`ExecFlow.guardedContinuing`). -/
def loopRegionGroupPlan (fuel : Nat) : FlowPlan StdVal :=
  .whileLoop fuel
    (.binary stdLtBool (.derefSub 0 []) (.localSub 1 []))
    (.seq
      (.act (.callMultiRegion []
        [{ regionSpecWithAdd 1 with inputPlaces := [.derefSub 0 []] }]))
      (.act (.endRegionGroup 0)))

def pairSwapMutBorrowSummary : CallSummary StdVal where
  returnsMutBorrow := true
  fwd _ mutVals :=
    match mutVals with
    | [v0, _] => some v0
    | _ => none
  back _ mutVals vFinal :=
    match mutVals with
    | [_, v1] => some [vFinal, v1]
    | _ => none

def sameOwnerTwoSubpathMutCallPlan : FlowPlan StdVal :=
  .seq
    (.act (.call 1 pairSwapMutBorrowSummary []
      [.derefSub 0 [0], .derefSub 0 [1]]))
    (.seq
      (.act (.assign (.derefSub 1 []) (.constVal (.nat 88))))
      (.act (.endLoan 1)))

def symbolicMixedEarlyReturnPlan : FlowPlan StdVal :=
  .seq
    (.branch (.use (.localSub 0 []))
      (.seq
        (.act (.assign (.derefSub 1 []) (.constVal (.nat 10))))
        (.earlyReturn [] [] (.constVal (.nat 1))))
      (.act (.assign (.derefSub 1 []) (.constVal (.nat 20)))))
    (.act (.assign (.derefSub 1 [])
      (.unary (stdAddNat 5) (.derefSub 1 []))))

theorem round4_plan_and_loan_regressions_exhaustive_tests
    (cond : Bool) (v0 v1 : Nat) :
    -- 1. `callMultiRegion` in a loop updates across multiple iterations:
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .nat 1⟩, ⟨.byVal, .nat 4⟩]
      (loopRegionGroupPlan 4)
      (.constVal .unit) = .ok ⟨.unit, [.nat 4]⟩ ∧
    -- Duplicate active `groupId` in the same `callMultiRegion` fails:
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      (.act (.callMultiRegion []
        [ { regionSpecWithAdd 1 with inputPlaces := [.derefSub 0 [0]] }
        , { regionSpecWithAdd 2 with inputPlaces := [.derefSub 0 [1]] } ]))
      (.constVal .unit) = .fail ∧
    -- 2. `applyOneJoinPair` remaps references nested inside `.pair`,
    -- `regionGroups`, and `regionDeposits`:
    (let e0 : LoanEntry StdVal :=
       ⟨0, .activeMut, ⟨.pair (.refVal 1 []) (.nat 0), .unborrowed⟩,
        .rootParam 0⟩
     let e1Act : LoanEntry StdVal :=
       ⟨1, .activeMut, ⟨.nat 5, .unborrowed⟩, .regionOut 0 0⟩
     let e2End : LoanEntry StdVal :=
       ⟨2, .ended, ⟨.nat 0, .unborrowed⟩, .regionOut 0 0⟩
     let rg1 : RegionGroupEntry StdVal :=
       ⟨0, true, 1, [(.parentLoan 1, [])], [1], [],
        fun outs deps => some (outs, deps)⟩
     let st1 : SymState StdVal :=
       ⟨[], [e0, e1Act, e2End], [rg1], [.refVal 1 []], [], 0⟩
     let e0In2 : LoanEntry StdVal :=
       ⟨0, .activeMut, ⟨.pair (.refVal 2 []) (.nat 0), .unborrowed⟩,
        .rootParam 0⟩
     let e1End : LoanEntry StdVal :=
       ⟨1, .ended, ⟨.nat 0, .unborrowed⟩, .regionOut 0 0⟩
     let e2Act : LoanEntry StdVal :=
       ⟨2, .activeMut, ⟨.nat 5, .unborrowed⟩, .regionOut 0 0⟩
     let rg2 : RegionGroupEntry StdVal :=
       ⟨0, true, 2, [(.parentLoan 2, [])], [2], [],
        fun outs deps => some (outs, deps)⟩
     let st2 : SymState StdVal :=
       ⟨[], [e0In2, e1End, e2Act], [rg2], [.refVal 2 []], [], 0⟩
     match applyOneJoinPair stdValAlg 1 2 st1 st2 with
     | some st2' =>
       st2'.regionDeposits = [.refVal 1 []] ∧
       (match findLoan 0 st2'.loans, findRegionGroup 0 st2'.regionGroups with
        | some e0', some rg' =>
          e0'.cell.val = .pair (.refVal 1 []) (.nat 0) ∧
          rg'.lockLid = 1 ∧
          rg'.outputLoans = [1] ∧
          rg'.inputTargets = [(.parentLoan 1, [])]
        | _, _ => False)
     | none => False) ∧
    -- 3. Multi-leaf `.lensCall` on disjoint sub-paths of the same owner:
    evalFnValue stdValAlg
      [⟨.mutRef 0 [], .pair (.nat v0) (.nat v1)⟩]
      sameOwnerTwoSubpathMutCallPlan
      (.constVal .unit) =
      .ok ⟨.unit, [.pair (.nat 88) (.nat v1)]⟩ ∧
    -- 4. Symbolic mixed early-return branch (`ExecFlow.guardedContinuing`):
    evalFnValue stdValAlg
      [⟨.byVal, .symBool cond⟩, ⟨.mutRef 0 [], .nat v0⟩]
      symbolicMixedEarlyReturnPlan
      (.constVal (.nat 0)) =
      .ok ⟨if cond then .nat 1 else .nat 0,
           [if cond then .nat 10 else .nat 25]⟩ := by
  cases cond <;>
    exact ⟨rfl, rfl, ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩⟩, rfl, rfl⟩

end Anneal.PureLift
