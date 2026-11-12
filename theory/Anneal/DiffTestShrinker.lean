-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

namespace Anneal.DiffTestShrinker

/-!
# Verified Mutator-Chain Delta-Debugging Shrinker and Wide `BitVec` Shift Guards

The differential-testing harnesses in `crates/anneal-difftest` (`miri-difftest`
and `itree-difftest`) minimize the mutator chain of every finding with
`shrink_mutation_chain_detailed` (`crates/anneal-difftest/src/shrink.rs`). This
module states and proves what that minimization guarantees:

1. Deterministic single-step (`dropOneCandidates`), chunk-deletion
   (`dropChunkCandidates`), and fuel-bounded (`shrinkMutatorChain`) mutator-chain
   shrinking with machine-checked discrepancy preservation, length monotonicity,
   `List.Sublist` preservation, and 1-minimality (`IsOneMinimal`).
2. A step-for-step reference model of the Rust `ddmin` loop (`ddminReference`),
   proved 1-minimal (`ddminReference_one_minimal`) and total for enough fuel
   (`ddminReference_total`). A unit test in `shrink.rs` checks that the Rust
   implementation makes exactly the same predicate calls as this model.
3. Guarded wide `BitVec` shift operations (`bvShlSafe`, `bvLshrSafe`,
   `bvAshrSafe`) and MIR-style overflowing shift companions
   (`bvShlOverflowing`, `bvLshrOverflowing`, `bvAshrOverflowing`) that bound
   shift exponents before invoking Lean's `BitVec` shift primitives. They
   prevent `lean_nat_shiftl` (`SIGABRT: Nat.shiftl exponent is too big`) panics
   on 64-bit and 128-bit operands when `rhs ≥ 2^32`.

Like `Anneal.MirLift`, this module is built as its own target
(`lake build Anneal.DiffTestShrinker`) rather than through the `Anneal` umbrella,
whose imports the trusted-boundary audit pins (`DOWNSTREAM_TARGETS` in
`trusted/audit/check_trusted.py`). It re-exports its core declarations under
`Anneal` at the end of the file.
-/

/-! ## Part 1: Mutator-Chain Delta-Debugging & 1-Minimality -/

/-- Packaging of a mutator chain `steps`, an observed oracle discrepancy `tag`,
and a proof that evaluating `steps` under `eval` produces `some tag`. -/
structure DiscrepancyWitness (α τ : Type) where
  steps : List α
  tag : τ
  eval : List α → Option τ
  h_eval : eval steps = some tag

/-- Deterministic single-element deletions of `xs` in index order `0 .. xs.length - 1`. -/
def dropOneCandidates : List α → List (List α)
  | [] => []
  | x :: xs => xs :: (dropOneCandidates xs).map (fun ys => x :: ys)

/-- Deterministic contiguous `k`-element chunk deletions of `xs` for `k ≥ 1`. -/
def dropChunkCandidates (k : Nat) : List α → List (List α)
  | [] => []
  | x :: xs =>
    if k = 0 then
      []
    else if (x :: xs).length < k then
      []
    else
      (x :: xs).drop k :: (dropChunkCandidates k xs).map (fun ys => x :: ys)

/-- A mutator chain `xs` is 1-minimal with respect to `pred` iff `pred xs = true`
and deleting any single element falsifies `pred`. -/
def IsOneMinimal (pred : List α → Bool) (xs : List α) : Prop :=
  pred xs = true ∧ ∀ ys ∈ dropOneCandidates xs, pred ys = false

/-- Candidate deletions attempted in a single reduction step: tries half-length chunk
deletions (`ddmin`) first when `xs.length / 2 ≥ 2`, followed by single-element
deletions (`dropOneCandidates xs`). Every candidate strictly reduces `xs.length`. -/
def shrinkStepCandidates (xs : List α) : List (List α) :=
  if xs.length / 2 ≥ 2 then
    dropChunkCandidates (xs.length / 2) xs ++ dropOneCandidates xs
  else
    dropOneCandidates xs

/-- Single-step reduction using `dropOneCandidates`. -/
def dropOneStep (pred : List α → Bool) (xs : List α) : List α :=
  match (dropOneCandidates xs).find? pred with
  | some ys => ys
  | none => xs

/-- Fuel-bounded deterministic mutator-chain shrinker. Each recursive step that
consumes one unit of `fuel` strictly decreases `xs.length` by at least `1`; when
no candidate deletion satisfies `pred`, shrinking terminates immediately at the
1-minimal fixed point `xs`. -/
def shrinkMutatorChain : Nat → (List α → Bool) → List α → List α
  | 0, _, xs => xs
  | fuel + 1, pred, xs =>
    match (shrinkStepCandidates xs).find? pred with
    | some ys => shrinkMutatorChain fuel pred ys
    | none => xs

/-- Alias for `shrinkMutatorChain`. -/
abbrev shrinkChain (fuel : Nat) (pred : List α → Bool) (xs : List α) : List α :=
  shrinkMutatorChain fuel pred xs

@[simp]
theorem dropOneCandidates_nil : dropOneCandidates ([] : List α) = [] := rfl

@[simp]
theorem dropOneCandidates_cons (x : α) (xs : List α) :
    dropOneCandidates (x :: xs) = xs :: (dropOneCandidates xs).map (fun ys => x :: ys) := rfl

theorem dropOneCandidates_length (xs : List α) :
    (dropOneCandidates xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp [dropOneCandidates, ih]

theorem mem_dropOneCandidates_sublist {xs ys : List α}
    (h : ys ∈ dropOneCandidates xs) : List.Sublist ys xs := by
  induction xs generalizing ys with
  | nil =>
    simp [dropOneCandidates] at h
  | cons x rest ih =>
    simp only [dropOneCandidates, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨zs, hzs, rfl⟩
    · exact List.Sublist.cons x (List.Sublist.refl ys)
    · exact List.Sublist.cons_cons x (ih hzs)

theorem mem_dropOneCandidates_length {xs ys : List α}
    (h : ys ∈ dropOneCandidates xs) : ys.length + 1 = xs.length := by
  induction xs generalizing ys with
  | nil =>
    simp [dropOneCandidates] at h
  | cons x rest ih =>
    simp only [dropOneCandidates, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨zs, hzs, rfl⟩
    · simp
    · have hlen := ih hzs
      simp [hlen]

theorem mem_dropOneCandidates_sublist_and_length {xs ys : List α}
    (h : ys ∈ dropOneCandidates xs) :
    List.Sublist ys xs ∧ ys.length + 1 = xs.length :=
  ⟨mem_dropOneCandidates_sublist h, mem_dropOneCandidates_length h⟩

theorem dropChunkCandidates_one_eq_dropOneCandidates (xs : List α) :
    dropChunkCandidates 1 xs = dropOneCandidates xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp [dropChunkCandidates, dropOneCandidates, ih]

private theorem drop_sublist (k : Nat) (xs : List α) :
    List.Sublist (xs.drop k) xs := by
  induction xs generalizing k with
  | nil => simp
  | cons x rest ih =>
    cases k with
    | zero => exact List.Sublist.refl (x :: rest)
    | succ k' =>
      simp only [List.drop_succ_cons]
      exact List.Sublist.cons x (ih k')

theorem mem_dropChunkCandidates_sublist {k : Nat} {xs ys : List α}
    (h : ys ∈ dropChunkCandidates k xs) : List.Sublist ys xs := by
  induction xs generalizing ys with
  | nil =>
    simp [dropChunkCandidates] at h
  | cons x rest ih =>
    unfold dropChunkCandidates at h
    split at h
    · contradiction
    · split at h
      · contradiction
      · simp only [List.mem_cons, List.mem_map] at h
        rcases h with rfl | ⟨zs, hzs, rfl⟩
        · exact drop_sublist k (x :: rest)
        · exact List.Sublist.cons_cons x (ih hzs)

theorem mem_dropChunkCandidates_length_add {k : Nat} {xs ys : List α}
    (h : ys ∈ dropChunkCandidates k xs) :
    k ≥ 1 ∧ ys.length + k = xs.length := by
  induction xs generalizing ys with
  | nil =>
    simp [dropChunkCandidates] at h
  | cons x rest ih =>
    unfold dropChunkCandidates at h
    split at h
    · contradiction
    · rename_i hk0
      split at h
      · contradiction
      · rename_i hlen_ge
        simp only [List.mem_cons, List.mem_map] at h
        rcases h with rfl | ⟨zs, hzs, rfl⟩
        · constructor
          · omega
          · simp only [List.length_cons] at hlen_ge
            simp only [List.length_drop, List.length_cons]
            omega
        · obtain ⟨hk1, hlen_zs⟩ := ih hzs
          refine ⟨hk1, ?_⟩
          simp only [List.length_cons]
          omega

theorem mem_dropChunkCandidates_length_lt {k : Nat} {xs ys : List α}
    (h : ys ∈ dropChunkCandidates k xs) : ys.length < xs.length := by
  obtain ⟨hk1, hsum⟩ := mem_dropChunkCandidates_length_add h
  omega

theorem mem_shrinkStepCandidates_sublist {xs ys : List α}
    (h : ys ∈ shrinkStepCandidates xs) : List.Sublist ys xs := by
  unfold shrinkStepCandidates at h
  split at h
  · simp only [List.mem_append] at h
    rcases h with hchunk | hdrop1
    · exact mem_dropChunkCandidates_sublist hchunk
    · exact mem_dropOneCandidates_sublist hdrop1
  · exact mem_dropOneCandidates_sublist h

theorem mem_shrinkStepCandidates_length_lt {xs ys : List α}
    (h : ys ∈ shrinkStepCandidates xs) : ys.length < xs.length := by
  unfold shrinkStepCandidates at h
  split at h
  · simp only [List.mem_append] at h
    rcases h with hchunk | hdrop1
    · exact mem_dropChunkCandidates_length_lt hchunk
    · have h1 := mem_dropOneCandidates_length hdrop1
      omega
  · have h1 := mem_dropOneCandidates_length h
    omega

theorem mem_shrinkStepCandidates_of_mem_dropOneCandidates {xs ys : List α}
    (h : ys ∈ dropOneCandidates xs) : ys ∈ shrinkStepCandidates xs := by
  unfold shrinkStepCandidates
  split
  · exact List.mem_append_right _ h
  · exact h

theorem dropOne_preserves_discrepancy (pred : List α → Bool) (xs : List α)
    (h_pred : pred xs = true) :
    pred (dropOneStep pred xs) = true := by
  unfold dropOneStep
  cases h_find : (dropOneCandidates xs).find? pred with
  | none => exact h_pred
  | some ys => exact List.find?_some h_find

theorem dropOneStep_sublist (pred : List α → Bool) (xs : List α) :
    List.Sublist (dropOneStep pred xs) xs := by
  unfold dropOneStep
  cases h_find : (dropOneCandidates xs).find? pred with
  | none => exact List.Sublist.refl xs
  | some ys => exact mem_dropOneCandidates_sublist (List.mem_of_find?_eq_some h_find)

theorem dropOneStep_len_le (pred : List α → Bool) (xs : List α) :
    (dropOneStep pred xs).length ≤ xs.length :=
  (dropOneStep_sublist pred xs).length_le

theorem shrinkMutatorChain_preserves_discrepancy (fuel : Nat) (pred : List α → Bool)
    (xs : List α) (h_pred : pred xs = true) :
    pred (shrinkMutatorChain fuel pred xs) = true := by
  induction fuel generalizing xs with
  | zero => exact h_pred
  | succ n ih =>
    unfold shrinkMutatorChain
    cases h_find : (shrinkStepCandidates xs).find? pred with
    | none => exact h_pred
    | some ys =>
      exact ih ys (List.find?_some h_find)

theorem shrinkChain_preserves_discrepancy (fuel : Nat) (pred : List α → Bool)
    (xs : List α) (h_pred : pred xs = true) :
    pred (shrinkChain fuel pred xs) = true :=
  shrinkMutatorChain_preserves_discrepancy fuel pred xs h_pred

theorem shrinkMutatorChain_sublist (fuel : Nat) (pred : List α → Bool) (xs : List α) :
    List.Sublist (shrinkMutatorChain fuel pred xs) xs := by
  induction fuel generalizing xs with
  | zero => exact List.Sublist.refl xs
  | succ n ih =>
    unfold shrinkMutatorChain
    cases h_find : (shrinkStepCandidates xs).find? pred with
    | none => exact List.Sublist.refl xs
    | some ys =>
      have h_sub_ys : List.Sublist ys xs :=
        mem_shrinkStepCandidates_sublist (List.mem_of_find?_eq_some h_find)
      exact List.Sublist.trans (ih ys) h_sub_ys

theorem shrinkChain_sublist (fuel : Nat) (pred : List α → Bool) (xs : List α) :
    List.Sublist (shrinkChain fuel pred xs) xs :=
  shrinkMutatorChain_sublist fuel pred xs

theorem shrinkMutatorChain_len_le (fuel : Nat) (pred : List α → Bool) (xs : List α) :
    (shrinkMutatorChain fuel pred xs).length ≤ xs.length :=
  (shrinkMutatorChain_sublist fuel pred xs).length_le

theorem shrinkChain_length_le (fuel : Nat) (pred : List α → Bool) (xs : List α) :
    (shrinkChain fuel pred xs).length ≤ xs.length :=
  shrinkMutatorChain_len_le fuel pred xs

theorem shrinkMutatorChain_one_minimal (fuel : Nat) (pred : List α → Bool) (xs : List α)
    (h_pred : pred xs = true) (h_fuel : xs.length ≤ fuel) :
    IsOneMinimal pred (shrinkMutatorChain fuel pred xs) := by
  induction fuel generalizing xs with
  | zero =>
    have h_nil : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst h_nil
    refine ⟨h_pred, ?_⟩
    intro ys h_mem
    simp [shrinkMutatorChain] at h_mem
  | succ n ih =>
    unfold shrinkMutatorChain
    cases h_find : (shrinkStepCandidates xs).find? pred with
    | none =>
      refine ⟨h_pred, ?_⟩
      intro ys h_mem_drop1
      have h_mem_step : ys ∈ shrinkStepCandidates xs :=
        mem_shrinkStepCandidates_of_mem_dropOneCandidates h_mem_drop1
      have h_not_true := List.find?_eq_none.mp h_find ys h_mem_step
      cases h_bool : pred ys with
      | false => rfl
      | true => exact False.elim (h_not_true h_bool)
    | some ys =>
      have h_pred_ys : pred ys = true := List.find?_some h_find
      have h_mem_ys : ys ∈ shrinkStepCandidates xs := List.mem_of_find?_eq_some h_find
      have h_len_lt : ys.length < xs.length := mem_shrinkStepCandidates_length_lt h_mem_ys
      exact ih ys h_pred_ys (by omega)

theorem shrinkChain_one_minimal (fuel : Nat) (pred : List α → Bool) (xs : List α)
    (h_pred : pred xs = true) (h_fuel : xs.length ≤ fuel) :
    IsOneMinimal pred (shrinkChain fuel pred xs) :=
  shrinkMutatorChain_one_minimal fuel pred xs h_pred h_fuel

/-- `dropOneStep pred xs` leaves `xs` unchanged iff every single-deletion candidate
falsifies `pred`. -/
theorem dropOneStep_eq_self_iff (pred : List α → Bool) (xs : List α) :
    dropOneStep pred xs = xs ↔ ∀ ys ∈ dropOneCandidates xs, pred ys = false := by
  unfold dropOneStep
  cases h_find : (dropOneCandidates xs).find? pred with
  | none =>
    simp only [true_iff]
    intro ys h_mem
    have h_not := List.find?_eq_none.mp h_find ys h_mem
    cases h_b : pred ys with
    | false => rfl
    | true => exact False.elim (h_not h_b)
  | some ys =>
    have h_mem : ys ∈ dropOneCandidates xs := List.mem_of_find?_eq_some h_find
    have h_pred : pred ys = true := List.find?_some h_find
    have h_len : ys.length + 1 = xs.length := mem_dropOneCandidates_length h_mem
    constructor
    · intro h_eq
      have h_eq' : ys = xs := h_eq
      rw [h_eq'] at h_len
      omega
    · intro h_all
      have h_false := h_all ys h_mem
      rw [h_pred] at h_false
      contradiction

/-- Fixed-point characterization of 1-minimality: `xs` is 1-minimal under `pred`
iff `pred xs = true` and `dropOneStep pred xs = xs`. -/
theorem isOneMinimal_iff_dropOneStep_fixed (pred : List α → Bool) (xs : List α) :
    IsOneMinimal pred xs ↔ pred xs = true ∧ dropOneStep pred xs = xs := by
  unfold IsOneMinimal
  rw [dropOneStep_eq_self_iff]

/-- With `xs.length ≤ fuel`, `shrinkMutatorChain` only terminates at a chain where
`shrinkStepCandidates` contains no candidate satisfying `pred` (both half-chunk and
single-deletion candidates are exhausted). -/
theorem shrinkMutatorChain_find?_eq_none (fuel : Nat) (pred : List α → Bool) (xs : List α)
    (h_fuel : xs.length ≤ fuel) :
    (shrinkStepCandidates (shrinkMutatorChain fuel pred xs)).find? pred = none := by
  induction fuel generalizing xs with
  | zero =>
    have h_nil : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst h_nil
    simp [shrinkMutatorChain, shrinkStepCandidates]
  | succ n ih =>
    unfold shrinkMutatorChain
    cases h_find : (shrinkStepCandidates xs).find? pred with
    | none => exact h_find
    | some ys =>
      have h_mem : ys ∈ shrinkStepCandidates xs := List.mem_of_find?_eq_some h_find
      have h_lt : ys.length < xs.length := mem_shrinkStepCandidates_length_lt h_mem
      exact ih ys (by omega)

/-- Any chain where `shrinkStepCandidates` has no match is a fixed point of
`shrinkMutatorChain` for every `fuel`. -/
theorem shrinkMutatorChain_eq_self_of_find?_eq_none (fuel : Nat) (pred : List α → Bool)
    (xs : List α) (h_none : (shrinkStepCandidates xs).find? pred = none) :
    shrinkMutatorChain fuel pred xs = xs := by
  cases fuel with
  | zero => rfl
  | succ n =>
    unfold shrinkMutatorChain
    rw [h_none]

/-- Idempotence of `shrinkMutatorChain`: re-running `shrinkMutatorChain` with any fuel
`fuel₂` on an already-minimized chain returns that chain unchanged. -/
theorem shrinkMutatorChain_idempotent (fuel₁ fuel₂ : Nat) (pred : List α → Bool) (xs : List α)
    (h_fuel : xs.length ≤ fuel₁) :
    shrinkMutatorChain fuel₂ pred (shrinkMutatorChain fuel₁ pred xs) =
      shrinkMutatorChain fuel₁ pred xs :=
  shrinkMutatorChain_eq_self_of_find?_eq_none fuel₂ pred
    (shrinkMutatorChain fuel₁ pred xs)
    (shrinkMutatorChain_find?_eq_none fuel₁ pred xs h_fuel)

/-- Tag-specialized predicate checking whether `eval ys` reproduces `some tag`. -/
def evalMatchesTag [DecidableEq τ] (eval : List α → Option τ) (tag : τ) (ys : List α) : Bool :=
  decide (eval ys = some tag)

/-- Shrinks a `DiscrepancyWitness` to a 1-minimal `DiscrepancyWitness` with the
exact same oracle discrepancy `tag`. -/
def shrinkDiscrepancyWitness [DecidableEq τ] (w : DiscrepancyWitness α τ) :
    DiscrepancyWitness α τ :=
  let pred := evalMatchesTag w.eval w.tag
  let minimized := shrinkMutatorChain w.steps.length pred w.steps
  have h_init : pred w.steps = true := decide_eq_true w.h_eval
  have h_pres : pred minimized = true :=
    shrinkMutatorChain_preserves_discrepancy w.steps.length pred w.steps h_init
  { steps := minimized
    tag := w.tag
    eval := w.eval
    h_eval := of_decide_eq_true h_pres }

theorem shrinkDiscrepancyWitness_one_minimal [DecidableEq τ] (w : DiscrepancyWitness α τ) :
    IsOneMinimal (evalMatchesTag w.eval w.tag) (shrinkDiscrepancyWitness w).steps ∧
      List.Sublist (shrinkDiscrepancyWitness w).steps w.steps ∧
      (shrinkDiscrepancyWitness w).steps.length ≤ w.steps.length ∧
      w.eval (shrinkDiscrepancyWitness w).steps = some w.tag := by
  have h_init : evalMatchesTag w.eval w.tag w.steps = true := decide_eq_true w.h_eval
  refine ⟨?_, ?_, ?_, (shrinkDiscrepancyWitness w).h_eval⟩
  · exact shrinkMutatorChain_one_minimal w.steps.length (evalMatchesTag w.eval w.tag)
      w.steps h_init (Nat.le_refl _)
  · exact shrinkMutatorChain_sublist w.steps.length (evalMatchesTag w.eval w.tag) w.steps
  · exact shrinkMutatorChain_len_le w.steps.length (evalMatchesTag w.eval w.tag) w.steps

theorem shrinkMutatorChain_eval_tag_sound [DecidableEq τ]
    (eval : List α → Option τ) (xs : List α) (tag : τ) (fuel : Nat)
    (h_eval : eval xs = some tag) (h_fuel : xs.length ≤ fuel) :
    let pred := evalMatchesTag eval tag
    let res := shrinkMutatorChain fuel pred xs
    eval res = some tag ∧ IsOneMinimal pred res ∧ List.Sublist res xs ∧ res.length ≤ xs.length := by
  intro pred res
  have h_init : pred xs = true := decide_eq_true h_eval
  have h_pres : pred res = true := shrinkMutatorChain_preserves_discrepancy fuel pred xs h_init
  exact ⟨of_decide_eq_true h_pres,
    shrinkMutatorChain_one_minimal fuel pred xs h_init h_fuel,
    shrinkMutatorChain_sublist fuel pred xs,
    shrinkMutatorChain_len_le fuel pred xs⟩

/-! ## Part 1b: Faithful Reference Model of the Rust `ddmin` Loop

`shrinkMutatorChain` above is a clean specification-level shrinker. The definitions
below instead transliterate the control flow of the Rust
`shrink_mutation_chain_detailed` (in `crates/anneal-difftest/src/shrink.rs`) step for
step: the initial `predicate(initial)` / `is_empty` / `predicate(&[])` checks, the
sliding-window sweep `while pos < best.len()` with the `end - pos == best.len()` break,
the candidate `best[..pos] ++ best[end..]`, and the granularity update
(`div_ceil(2)` halving, reset to `best.len().div_ceil(2)` after a successful
`chunk_size == 1` sweep). Fuel only bounds the recursion; the Rust loops are
unbounded. `ddminReference_one_minimal` proves that every result the model returns is
1-minimal and a sublist of the input, which is exactly the `is_one_minimal` claim
the Rust shrinker reports; a Rust unit test checks that the implementation makes
the same predicate calls in the same order as this model. -/

/-- The candidate `best[..pos] ++ best[end..]` with `end = min (pos + chunk) best.len()`. -/
def windowDelete (xs : List α) (pos chunk : Nat) : List α :=
  xs.take pos ++ xs.drop (min (pos + chunk) xs.length)

/-- One sliding-window sweep (`while pos < best.len()`) at granularity `chunk`. -/
def ddminSweep (pred : List α → Bool) (chunk : Nat) :
    Nat → List α → Nat → Bool → Option (List α × Bool)
  | 0, _, _, _ => none
  | fuel + 1, best, pos, improved =>
    if pos < best.length then
      if min (pos + chunk) best.length - pos = best.length then
        some (best, improved)
      else if pred (windowDelete best pos chunk) then
        ddminSweep pred chunk fuel (windowDelete best pos chunk) pos true
      else
        ddminSweep pred chunk fuel best (pos + 1) improved
    else
      some (best, improved)

/-- Granularity update after a sweep that did not terminate the loop. -/
def ddminNextChunk (chunk : Nat) (best : List α) : Nat :=
  if chunk = 1 then
    (if 2 ≤ best.length then (best.length + 1) / 2 else 1)
  else
    max 1 (min ((chunk + 1) / 2) ((best.length + 1) / 2))

/-- Outer `loop`: stop after a `chunk = 1` sweep that accepted nothing. -/
def ddminLoop (pred : List α → Bool) : Nat → List α → Nat → Option (List α)
  | 0, _, _ => none
  | fuel + 1, best, chunk =>
    match ddminSweep pred chunk (2 * best.length + 1) best 0 false with
    | none => none
    | some (best', improved) =>
      if chunk = 1 ∧ improved = false then some best'
      else ddminLoop pred fuel best' (ddminNextChunk chunk best')

/-- Reference model of `shrink_mutation_chain_detailed`: `none` when the initial
predicate check fails (`succeeded = false`) or `fuel` runs out. -/
def ddminReference (pred : List α → Bool) (fuel : Nat) (xs : List α) : Option (List α) :=
  if pred xs then
    if xs.isEmpty then some []
    else if pred [] then some []
    else ddminLoop pred fuel xs ((xs.length + 1) / 2)
  else none

private theorem take_append_drop_sublist (xs : List α) {p q : Nat} (h : p ≤ q) :
    (xs.take p ++ xs.drop q).Sublist xs := by
  have h1 : (xs.take p ++ xs.drop q).Sublist (xs.take p ++ xs.drop p) :=
    (List.drop_sublist_drop_left xs h).append_left _
  rwa [List.take_append_drop] at h1

theorem windowDelete_sublist (xs : List α) (pos chunk : Nat) :
    (windowDelete xs pos chunk).Sublist xs := by
  unfold windowDelete
  by_cases h : pos ≤ min (pos + chunk) xs.length
  · exact take_append_drop_sublist xs h
  · have hlen : xs.length < pos := by omega
    rw [List.take_of_length_le (Nat.le_of_lt hlen),
      List.drop_eq_nil_of_le (by omega), List.append_nil]
    exact List.Sublist.refl _

theorem mem_dropOneCandidates_exists_take_drop {xs ys : List α} (h : ys ∈ dropOneCandidates xs) :
    ∃ i, i < xs.length ∧ ys = xs.take i ++ xs.drop (i + 1) := by
  induction xs generalizing ys with
  | nil => simp [dropOneCandidates] at h
  | cons x rest ih =>
    simp only [dropOneCandidates, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨zs, hzs, rfl⟩
    · exact ⟨0, by simp, by simp⟩
    · obtain ⟨i, hi, rfl⟩ := ih hzs
      exact ⟨i + 1, by simp; omega, by simp⟩

theorem ddminSweep_spec (pred : List α → Bool) (chunk : Nat) :
    ∀ (fuel : Nat) (best : List α) (pos : Nat) (imp : Bool) (r : List α) (imp' : Bool),
      ddminSweep pred chunk fuel best pos imp = some (r, imp') →
      pred best = true → pred r = true ∧ r.Sublist best := by
  intro fuel
  induction fuel with
  | zero => intro best pos imp r imp' h; simp [ddminSweep] at h
  | succ n ih =>
    intro best pos imp r imp' h hbest
    unfold ddminSweep at h
    split at h
    · split at h
      · cases h; exact ⟨hbest, List.Sublist.refl _⟩
      · split at h
        · rename_i hcand
          obtain ⟨hr, hsub⟩ := ih _ _ _ _ _ h hcand
          exact ⟨hr, hsub.trans (windowDelete_sublist best pos chunk)⟩
        · exact ih _ _ _ _ _ h hbest
    · cases h; exact ⟨hbest, List.Sublist.refl _⟩

theorem ddminSweep_true_flag (pred : List α → Bool) (chunk : Nat) :
    ∀ (fuel : Nat) (best : List α) (pos : Nat) (r : List α) (f : Bool),
      ddminSweep pred chunk fuel best pos true = some (r, f) → f = true := by
  intro fuel
  induction fuel with
  | zero => intro best pos r f h; simp [ddminSweep] at h
  | succ n ih =>
    intro best pos r f h
    unfold ddminSweep at h
    split at h
    · split at h
      · cases h; rfl
      · split at h
        · exact ih _ _ _ _ h
        · exact ih _ _ _ _ h
    · cases h; rfl

theorem ddminSweep_one_complete (pred : List α → Bool) :
    ∀ (fuel : Nat) (best : List α) (pos : Nat) (r : List α),
      ddminSweep pred 1 fuel best pos false = some (r, false) →
      r = best ∧ ∀ i, pos ≤ i → i < best.length →
        pred (windowDelete best i 1) = false ∨ windowDelete best i 1 = [] := by
  intro fuel
  induction fuel with
  | zero => intro best pos r h; simp [ddminSweep] at h
  | succ n ih =>
    intro best pos r h
    unfold ddminSweep at h
    split at h
    · rename_i hpos
      split at h
      · rename_i hbreak
        cases h
        refine ⟨rfl, fun i hi hlt => Or.inr ?_⟩
        have hlen : best.length = 1 := by omega
        have hi0 : i = 0 := by omega
        subst hi0
        simp [windowDelete, hlen, List.drop_eq_nil_of_le]
      · split at h
        · exact absurd (ddminSweep_true_flag pred 1 n _ _ _ _ h) (by simp)
        · rename_i hbreak hfalse
          obtain ⟨hr, hall⟩ := ih _ _ _ h
          refine ⟨hr, fun i hi hlt => ?_⟩
          by_cases hip : i = pos
          · subst hip
            exact Or.inl (by simpa using hfalse)
          · exact hall i (by omega) hlt
    · rename_i hpos
      cases h
      exact ⟨rfl, fun i hi hlt => absurd (Nat.lt_of_le_of_lt hi hlt) hpos⟩

theorem windowDelete_one_eq (xs : List α) {i : Nat} (hi : i < xs.length) :
    windowDelete xs i 1 = xs.take i ++ xs.drop (i + 1) := by
  unfold windowDelete
  rw [Nat.min_eq_left (by omega)]

theorem take_append_drop_succ_mem_dropOneCandidates (xs : List α) {i : Nat} (hi : i < xs.length) :
    xs.take i ++ xs.drop (i + 1) ∈ dropOneCandidates xs := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x rest ih =>
    cases i with
    | zero => simp [dropOneCandidates]
    | succ j =>
      simp only [List.length_cons] at hi
      have hj : j < rest.length := by omega
      simp only [dropOneCandidates, List.take_succ_cons, List.drop_succ_cons, List.cons_append,
        List.mem_cons, List.mem_map]
      exact Or.inr ⟨rest.take j ++ rest.drop (j + 1), ih hj, rfl⟩

/-- On any 1-minimal chain `best`, a `chunk = 1` sweep rejects every single-element
deletion and returns `some (best, false)`. -/
theorem ddminSweep_one_of_isOneMinimal (pred : List α → Bool) (best : List α)
    (h_min : IsOneMinimal pred best) :
    ∀ (fuel : Nat) (pos : Nat),
      best.length - pos < fuel →
      ddminSweep pred 1 fuel best pos false = some (best, false) := by
  intro fuel
  induction fuel with
  | zero => intro pos hfuel; omega
  | succ n ih =>
    intro pos hfuel
    unfold ddminSweep
    split
    · rename_i hpos
      split
      · rfl
      · have h_mem : windowDelete best pos 1 ∈ dropOneCandidates best := by
          rw [windowDelete_one_eq best hpos]
          exact take_append_drop_succ_mem_dropOneCandidates best hpos
        have h_false : pred (windowDelete best pos 1) = false := h_min.2 _ h_mem
        rw [h_false]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ih (pos + 1) (by omega)
    · rfl

/-- When `ddminLoop` reaches `chunk = 1` on a 1-minimal chain `best`, it terminates in
one sweep and returns `some best` unchanged. -/
theorem ddminLoop_one_eq_some_of_isOneMinimal (pred : List α → Bool) (fuel : Nat)
    (best : List α) (h_min : IsOneMinimal pred best) :
    ddminLoop pred (fuel + 1) best 1 = some best := by
  unfold ddminLoop
  have hsweep : ddminSweep pred 1 (2 * best.length + 1) best 0 false = some (best, false) :=
    ddminSweep_one_of_isOneMinimal pred best h_min (2 * best.length + 1) 0 (by omega)
  rw [hsweep]
  simp

/-- Any 1-minimal chain `best` of length `1` or `2` (where the initial chunk size
`(best.length + 1) / 2` is `1`) is a fixed point of `ddminReference` whenever
`pred [] = false`. -/
theorem ddminReference_eq_some_self_of_isOneMinimal_le_two (pred : List α → Bool)
    (fuel : Nat) (best : List α) (h_min : IsOneMinimal pred best)
    (h_nil : pred [] = false) (h_len : best.length ≤ 2) :
    ddminReference pred (fuel + 1) best = some best := by
  have h_pred : pred best = true := h_min.1
  have h_ne_nil : best ≠ [] := by
    intro h_eq
    subst h_eq
    rw [h_pred] at h_nil
    contradiction
  have h_not_empty : best.isEmpty = false := by
    cases best with
    | nil => contradiction
    | cons _ _ => rfl
  have h_pos_len : 1 ≤ best.length := by
    cases best with
    | nil => contradiction
    | cons _ _ => simp
  have h_chunk : (best.length + 1) / 2 = 1 := by omega
  unfold ddminReference
  rw [h_pred, h_not_empty, h_nil]
  simp only [Bool.false_eq_true, ↓reduceIte, h_chunk]
  exact ddminLoop_one_eq_some_of_isOneMinimal pred fuel best h_min

theorem ddminLoop_spec (pred : List α → Bool) (h_nil : pred [] = false) :
    ∀ (fuel : Nat) (best : List α) (chunk : Nat) (r : List α),
      ddminLoop pred fuel best chunk = some r → pred best = true →
      IsOneMinimal pred r ∧ r.Sublist best := by
  intro fuel
  induction fuel with
  | zero => intro best chunk r h; simp [ddminLoop] at h
  | succ n ih =>
    intro best chunk r h hbest
    unfold ddminLoop at h
    split at h
    · simp at h
    · rename_i best' improved hsweep
      obtain ⟨hpred', hsub'⟩ := ddminSweep_spec pred chunk _ _ _ _ _ _ hsweep hbest
      split at h
      · rename_i hstop
        obtain ⟨hchunk, himp⟩ := hstop
        cases h
        subst hchunk
        subst himp
        obtain ⟨hr, hall⟩ := ddminSweep_one_complete pred _ _ _ _ hsweep
        subst hr
        refine ⟨⟨hpred', fun ys hys => ?_⟩, hsub'⟩
        obtain ⟨i, hi, rfl⟩ := mem_dropOneCandidates_exists_take_drop hys
        rcases hall i (Nat.zero_le _) hi with hf | hnil
        · rwa [windowDelete_one_eq _ hi] at hf
        · rw [windowDelete_one_eq _ hi] at hnil
          rw [hnil]; exact h_nil
      · obtain ⟨hmin, hsub⟩ := ih _ _ _ h hpred'
        exact ⟨hmin, hsub.trans hsub'⟩

/-- Every result of the reference `ddmin` model is 1-minimal and a sublist of the
input, and the input satisfied the predicate. -/
theorem ddminReference_one_minimal (pred : List α → Bool) (fuel : Nat) (xs r : List α)
    (h : ddminReference pred fuel xs = some r) :
    pred xs = true ∧ IsOneMinimal pred r ∧ r.Sublist xs := by
  unfold ddminReference at h
  split at h
  · rename_i hxs
    refine ⟨hxs, ?_⟩
    split at h
    · rename_i hempty
      cases h
      have hx : xs = [] := List.isEmpty_iff.mp hempty
      subst hx
      exact ⟨⟨hxs, by simp [dropOneCandidates]⟩, List.Sublist.refl _⟩
    · split at h
      · rename_i _ hnil
        cases h
        exact ⟨⟨hnil, by simp [dropOneCandidates]⟩, List.nil_sublist _⟩
      · rename_i _ hnil
        exact ddminLoop_spec pred (by simpa using hnil) _ _ _ _ h hxs
  · simp at h

/-! ### Kernel witnesses equal to the Rust `shrink_mutation_chain_detailed` test outcomes -/

theorem ddminReference_coupled_pair_witness :
    ddminReference (fun xs : List Nat => (xs.contains 1 == xs.contains 2) && xs.contains 4)
      16 [1, 2, 3, 4] = some [4] := by rfl

theorem ddminReference_tag_pair_witness :
    ddminReference
        (evalMatchesTag
          (fun xs : List Nat =>
            if xs.contains 1 && xs.contains 4 then some 0
            else if xs.contains 1 then some 1 else none)
          0)
        16 [0, 1, 2, 3, 4, 5] = some [1, 4] := by rfl

theorem ddminReference_trigger_pair_witness :
    ddminReference (fun xs : List Nat => xs.contains 2 && xs.contains 5) 16
      [0, 1, 2, 3, 4, 5, 6] = some [2, 5] := by rfl

theorem ddminReference_root_fault_witness :
    ddminReference (fun _ : List Nat => true) 4 [1, 2, 3] = some [] := by rfl

theorem ddminReference_single_step_witness :
    ddminReference (fun xs : List Nat => xs == [7]) 4 [7] = some [7] := by rfl

theorem ddminReference_initial_false_witness :
    ddminReference (fun _ : List Nat => false) 4 [1, 2] = none := by rfl

/-! ### Termination: with enough fuel the reference model always answers -/

theorem windowDelete_length_lt (xs : List α) {pos chunk : Nat} (hpos : pos < xs.length)
    (hchunk : 1 ≤ chunk) : (windowDelete xs pos chunk).length < xs.length := by
  unfold windowDelete
  simp only [List.length_append, List.length_take, List.length_drop]
  omega

theorem windowDelete_length_ge_pos (xs : List α) {pos chunk : Nat} (hpos : pos < xs.length) :
    pos ≤ (windowDelete xs pos chunk).length := by
  unfold windowDelete
  simp only [List.length_append, List.length_take, List.length_drop]
  omega

theorem ddminSweep_sublist (pred : List α → Bool) (chunk : Nat) :
    ∀ (fuel : Nat) (best : List α) (pos : Nat) (imp : Bool) (r : List α) (imp' : Bool),
      ddminSweep pred chunk fuel best pos imp = some (r, imp') → r.Sublist best := by
  intro fuel
  induction fuel with
  | zero => intro best pos imp r imp' h; simp [ddminSweep] at h
  | succ n ih =>
    intro best pos imp r imp' h
    unfold ddminSweep at h
    split at h
    · split at h
      · cases h; exact List.Sublist.refl _
      · split at h
        · exact (ih _ _ _ _ _ h).trans (windowDelete_sublist best pos chunk)
        · exact ih _ _ _ _ _ h
    · cases h; exact List.Sublist.refl _

/-- A sweep that starts with `improved = false` and reports `improved = true` accepted at
least one deletion, so the chain got strictly shorter. -/
theorem ddminSweep_improved_shorter (pred : List α → Bool) {chunk : Nat} (hchunk : 1 ≤ chunk) :
    ∀ (fuel : Nat) (best : List α) (pos : Nat) (r : List α),
      ddminSweep pred chunk fuel best pos false = some (r, true) → r.length < best.length := by
  intro fuel
  induction fuel with
  | zero => intro best pos r h; simp [ddminSweep] at h
  | succ n ih =>
    intro best pos r h
    unfold ddminSweep at h
    split at h
    · rename_i hpos
      split at h
      · cases h
      · split at h
        · exact Nat.lt_of_le_of_lt (ddminSweep_sublist pred chunk _ _ _ _ _ _ h).length_le
            (windowDelete_length_lt best hpos hchunk)
        · exact ih _ _ _ h
    · cases h

theorem ddminSweep_terminates (pred : List α → Bool) {chunk : Nat} (hchunk : 1 ≤ chunk) :
    ∀ (fuel : Nat) (best : List α) (pos : Nat) (imp : Bool),
      pos ≤ best.length → 2 * best.length - pos + 1 ≤ fuel →
      ∃ r f, ddminSweep pred chunk fuel best pos imp = some (r, f) := by
  intro fuel
  induction fuel with
  | zero => intro best pos imp _ hfuel; omega
  | succ n ih =>
    intro best pos imp hpos hfuel
    unfold ddminSweep
    split
    · rename_i hlt
      split
      · exact ⟨_, _, rfl⟩
      · split
        · have hshort := windowDelete_length_lt best hlt hchunk
          have hge := windowDelete_length_ge_pos best (chunk := chunk) hlt
          exact ih _ _ _ hge (by omega)
        · exact ih _ _ _ (by omega) (by omega)
    · exact ⟨_, _, rfl⟩

theorem ddminNextChunk_pos (chunk : Nat) (best : List α) : 1 ≤ ddminNextChunk chunk best := by
  unfold ddminNextChunk
  split
  · split <;> omega
  · omega

private theorem sq_succ_le {a b : Nat} (h : a + 1 ≤ b) : (a + 1) * (a + 1) ≤ b * b :=
  Nat.mul_le_mul h h

private theorem mul_succ_mono {a b : Nat} (h : a ≤ b) : a * (a + 1) ≤ b * (b + 1) :=
  Nat.mul_le_mul h (Nat.succ_le_succ h)

theorem ddminLoop_terminates (pred : List α → Bool) :
    ∀ (fuel : Nat) (best : List α) (chunk : Nat),
      1 ≤ chunk → best.length * (best.length + 1) + chunk < fuel →
      ∃ r, ddminLoop pred fuel best chunk = some r := by
  intro fuel
  induction fuel with
  | zero => intro best chunk _ hfuel; omega
  | succ n ih =>
    intro best chunk hchunk hfuel
    obtain ⟨best', improved, hsweep⟩ :=
      ddminSweep_terminates pred hchunk (2 * best.length + 1) best 0 false
        (Nat.zero_le _) (by omega)
    unfold ddminLoop
    rw [hsweep]
    simp only
    split
    · exact ⟨_, rfl⟩
    · rename_i hcont
      have hle : best'.length ≤ best.length :=
        (ddminSweep_sublist pred chunk _ _ _ _ _ _ hsweep).length_le
      apply ih _ _ (ddminNextChunk_pos chunk best')
      by_cases h1 : chunk = 1
      · subst h1
        have himp : improved = true := by
          cases improved
          · exact absurd ⟨rfl, rfl⟩ hcont
          · rfl
        subst himp
        have hlt := ddminSweep_improved_shorter pred (Nat.le_refl 1) _ _ _ _ hsweep
        have hnext : ddminNextChunk 1 best' ≤ best'.length + 1 := by
          unfold ddminNextChunk; split <;> (try split) <;> omega
        have hsq := sq_succ_le hlt
        have hexp : best'.length * (best'.length + 1) + (best'.length + 1) =
            (best'.length + 1) * (best'.length + 1) := by
          rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]
        have hexp2 : best.length * (best.length + 1) = best.length * best.length + best.length := by
          rw [Nat.mul_add, Nat.mul_one]
        omega
      · have hnext : ddminNextChunk chunk best' < chunk := by
          unfold ddminNextChunk; split <;> (try split) <;> omega
        have hmono := mul_succ_mono hle
        omega

/-- With fuel above `n * (n + 1) + ⌈n / 2⌉` (`n = xs.length`), the reference model
returns a 1-minimal sublist whenever the initial predicate holds. -/
theorem ddminReference_total (pred : List α → Bool) (xs : List α) (fuel : Nat)
    (h_pred : pred xs = true)
    (h_fuel : xs.length * (xs.length + 1) + (xs.length + 1) / 2 < fuel) :
    ∃ r, ddminReference pred fuel xs = some r ∧ IsOneMinimal pred r ∧ r.Sublist xs := by
  have h_some : ∃ r, ddminReference pred fuel xs = some r := by
    unfold ddminReference
    split
    · split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · rename_i hne _
          have hlen : 1 ≤ xs.length := by
            cases xs with
            | nil => simp at hne
            | cons _ _ => simp
          exact ddminLoop_terminates pred _ _ _ (by omega) h_fuel
    · rename_i hneg
      exact absurd h_pred hneg
  obtain ⟨r, hr⟩ := h_some
  exact ⟨r, hr, (ddminReference_one_minimal pred fuel xs r hr).2⟩


/-! ## Part 1c: When Is a 1-Minimal Witness Globally Minimal?

1-minimality only rules out single-step deletions. For *monotone* predicates (adding
mutation steps never destroys a reproduction, e.g. "every trigger step is present"),
it already implies that **no proper subsequence** reproduces the discrepancy, so both
shrinkers return globally minimal witnesses. Without monotonicity (coupled AST
dependencies, tag-sensitive steps) the guarantee is genuinely local, and the chunk
phase of the reference `ddmin` can reach strictly smaller witnesses than single-step
deletion. -/

/-- Every proper sublist of `xs` is a sublist of some single-step deletion of `xs`. -/
theorem exists_mem_dropOneCandidates_of_sublist {ys xs : List α} (h : ys.Sublist xs)
    (hlt : ys.length < xs.length) : ∃ zs ∈ dropOneCandidates xs, ys.Sublist zs := by
  revert hlt
  induction h with
  | slnil => intro hlt; simp at hlt
  | cons a h _ =>
    intro _
    exact ⟨_, by simp [dropOneCandidates], h⟩
  | cons_cons a _ ih =>
    intro hlt
    simp only [List.length_cons] at hlt
    obtain ⟨zs, hzs, hsub⟩ := ih (by omega)
    refine ⟨a :: zs, ?_, hsub.cons_cons a⟩
    simp only [dropOneCandidates, List.mem_cons, List.mem_map]
    exact Or.inr ⟨zs, hzs, rfl⟩

/-- For predicates that are monotone under adding steps, a 1-minimal witness is globally
minimal: no proper subsequence satisfies `pred`. -/
theorem isOneMinimal_globally_minimal_of_monotone (pred : List α → Bool)
    (h_mono : ∀ ys xs : List α, ys.Sublist xs → pred ys = true → pred xs = true)
    {r : List α} (h_min : IsOneMinimal pred r) :
    ∀ ys, ys.Sublist r → ys.length < r.length → pred ys = false := by
  intro ys hsub hlt
  obtain ⟨zs, hzs, hys⟩ := exists_mem_dropOneCandidates_of_sublist hsub hlt
  cases h : pred ys with
  | false => rfl
  | true =>
    have h_zs := h_mono ys zs hys h
    rw [h_min.2 zs hzs] at h_zs
    exact absurd h_zs (by simp)

/-- The specification shrinker returns a globally minimal witness for monotone
predicates. -/
theorem shrinkMutatorChain_globally_minimal_of_monotone (fuel : Nat) (pred : List α → Bool)
    (xs : List α)
    (h_mono : ∀ ys xs : List α, ys.Sublist xs → pred ys = true → pred xs = true)
    (h_pred : pred xs = true) (h_fuel : xs.length ≤ fuel) :
    ∀ ys, ys.Sublist (shrinkMutatorChain fuel pred xs) →
      ys.length < (shrinkMutatorChain fuel pred xs).length → pred ys = false :=
  isOneMinimal_globally_minimal_of_monotone pred h_mono
    (shrinkMutatorChain_one_minimal fuel pred xs h_pred h_fuel)

/-- The reference model of the Rust `ddmin` returns a globally minimal witness for
monotone predicates. -/
theorem ddminReference_globally_minimal_of_monotone (pred : List α → Bool) (fuel : Nat)
    (xs r : List α)
    (h_mono : ∀ ys xs : List α, ys.Sublist xs → pred ys = true → pred xs = true)
    (h : ddminReference pred fuel xs = some r) :
    ∀ ys, ys.Sublist r → ys.length < r.length → pred ys = false :=
  isOneMinimal_globally_minimal_of_monotone pred h_mono
    (ddminReference_one_minimal pred fuel xs r h).2.1

/-- "Every trigger step in `req` is present" predicates are monotone. -/
theorem containsAll_monotone [DecidableEq α] (req : List α) :
    ∀ ys xs : List α, ys.Sublist xs →
      req.all (fun a => decide (a ∈ ys)) = true → req.all (fun a => decide (a ∈ xs)) = true := by
  intro ys xs hsub h
  simp only [List.all_eq_true, decide_eq_true_eq] at h ⊢
  exact fun a ha => hsub.subset (h a ha)

/-- A sublist whose length is at least the ambient list's length is equal to it. -/
theorem sublist_eq_of_length_le {ys xs : List α} (hsub : ys.Sublist xs)
    (hlen : xs.length ≤ ys.length) : ys = xs := by
  induction hsub with
  | slnil => rfl
  | cons a h _ =>
    have hle := h.length_le
    simp only [List.length_cons] at hlen
    omega
  | cons_cons a h ih =>
    simp only [List.length_cons] at hlen
    rw [ih (by omega)]

/-- Antisymmetry of 1-minimal witnesses under a monotone predicate: if `r₁` and `r₂` are
both 1-minimal and `r₁` is a sublist of `r₂`, then `r₁ = r₂`. -/
theorem isOneMinimal_eq_of_sublist_of_monotone (pred : List α → Bool)
    (h_mono : ∀ ys xs : List α, ys.Sublist xs → pred ys = true → pred xs = true)
    {r₁ r₂ : List α} (h₁ : IsOneMinimal pred r₁) (h₂ : IsOneMinimal pred r₂)
    (hsub : r₁.Sublist r₂) : r₁ = r₂ := by
  by_cases hlt : r₁.length < r₂.length
  · have hfalse := isOneMinimal_globally_minimal_of_monotone pred h_mono h₂ r₁ hsub hlt
    rw [h₁.1] at hfalse
    contradiction
  · exact sublist_eq_of_length_le hsub (by omega)

/-- Uniqueness of 1-minimal witnesses when `pred` is monotone and closed under common
sublist lower bounds on sublists of `xs`. -/
theorem isOneMinimal_unique_of_monotone_inf (pred : List α → Bool) (xs : List α)
    (h_mono : ∀ ys zs : List α, ys.Sublist zs → pred ys = true → pred zs = true)
    (h_inf : ∀ y₁ y₂ : List α, y₁.Sublist xs → y₂.Sublist xs →
      pred y₁ = true → pred y₂ = true →
      ∃ w, w.Sublist y₁ ∧ w.Sublist y₂ ∧ pred w = true)
    {r₁ r₂ : List α} (hsub₁ : r₁.Sublist xs) (hsub₂ : r₂.Sublist xs)
    (hmin₁ : IsOneMinimal pred r₁) (hmin₂ : IsOneMinimal pred r₂) : r₁ = r₂ := by
  obtain ⟨w, hw₁, hw₂, hpw⟩ := h_inf r₁ r₂ hsub₁ hsub₂ hmin₁.1 hmin₂.1
  have heq₁ : w = r₁ := by
    by_cases hlt : w.length < r₁.length
    · have hf := isOneMinimal_globally_minimal_of_monotone pred h_mono hmin₁ w hw₁ hlt
      rw [hpw] at hf
      contradiction
    · exact sublist_eq_of_length_le hw₁ (by omega)
  have heq₂ : w = r₂ := by
    by_cases hlt : w.length < r₂.length
    · have hf := isOneMinimal_globally_minimal_of_monotone pred h_mono hmin₂ w hw₂ hlt
      rw [hpw] at hf
      contradiction
    · exact sublist_eq_of_length_le hw₂ (by omega)
  exact heq₁.symm.trans heq₂

/-- Under monotonicity and sublist lower-bound closure, the specification shrinker
`shrinkMutatorChain` and the Rust reference model `ddminReference` return the exact same
1-minimal witness `r`. -/
theorem shrinkMutatorChain_eq_ddminReference_of_monotone_inf (pred : List α → Bool)
    (xs r : List α) (fuel_s fuel_d : Nat)
    (h_mono : ∀ ys zs : List α, ys.Sublist zs → pred ys = true → pred zs = true)
    (h_inf : ∀ y₁ y₂ : List α, y₁.Sublist xs → y₂.Sublist xs →
      pred y₁ = true → pred y₂ = true →
      ∃ w, w.Sublist y₁ ∧ w.Sublist y₂ ∧ pred w = true)
    (h_ddmin : ddminReference pred fuel_d xs = some r)
    (h_fuel : xs.length ≤ fuel_s) :
    shrinkMutatorChain fuel_s pred xs = r := by
  obtain ⟨h_pred, hmin_r, hsub_r⟩ := ddminReference_one_minimal pred fuel_d xs r h_ddmin
  have hmin_s := shrinkMutatorChain_one_minimal fuel_s pred xs h_pred h_fuel
  have hsub_s := shrinkMutatorChain_sublist fuel_s pred xs
  exact isOneMinimal_unique_of_monotone_inf pred xs h_mono h_inf hsub_s hsub_r hmin_s hmin_r

/-- On a chain of distinct steps, a sublist that keeps every trigger step of `req` that
occurs in the chain keeps exactly the chain's trigger steps, in chain order. -/
theorem filter_mem_eq_of_sublist_of_nodup [DecidableEq α] (req : List α) {ys xs : List α}
    (hsub : ys.Sublist xs) (hnd : xs.Nodup) (hkeep : ∀ a ∈ xs, a ∈ req → a ∈ ys) :
    ys.filter (fun a => decide (a ∈ req)) = xs.filter (fun a => decide (a ∈ req)) := by
  revert hnd hkeep
  induction hsub with
  | slnil => intro _ _; rfl
  | cons a h ih =>
    intro hnd hkeep
    have hnd' := List.nodup_cons.mp hnd
    have ha : a ∉ req := fun ha => hnd'.1 (h.subset (hkeep a (by simp) ha))
    have heq := ih hnd'.2 (fun b hb hbr => hkeep b (by simp [hb]) hbr)
    simp [ha, heq]
  | cons_cons a h ih =>
    intro hnd hkeep
    have hnd' := List.nodup_cons.mp hnd
    have heq := ih hnd'.2 (fun b hb hbr => by
      rcases List.mem_cons.mp (hkeep b (by simp [hb]) hbr) with rfl | h'
      · exact absurd hb hnd'.1
      · exact h')
    simp only [List.filter_cons, heq]

/-- Concrete instance of the lower-bound closure hypothesis `h_inf` above: on a chain of
distinct steps (the Rust shrinker identifies steps by their distinct `pass_index`),
"every trigger step in `req` is present" predicates have the common lower bound
`xs.filter (· ∈ req)`. -/
theorem containsAll_inf_closed [DecidableEq α] (req xs : List α) (hnd : xs.Nodup) :
    ∀ y₁ y₂ : List α, y₁.Sublist xs → y₂.Sublist xs →
      req.all (fun a => decide (a ∈ y₁)) = true → req.all (fun a => decide (a ∈ y₂)) = true →
      ∃ w : List α, w.Sublist y₁ ∧ w.Sublist y₂ ∧ req.all (fun a => decide (a ∈ w)) = true := by
  intro y₁ y₂ h₁ h₂ hp₁ hp₂
  simp only [List.all_eq_true, decide_eq_true_eq] at hp₁ hp₂
  have he₁ := filter_mem_eq_of_sublist_of_nodup req h₁ hnd (fun a _ ha => hp₁ a ha)
  have he₂ := filter_mem_eq_of_sublist_of_nodup req h₂ hnd (fun a _ ha => hp₂ a ha)
  refine ⟨y₁.filter (fun a => decide (a ∈ req)), List.filter_sublist .., ?_, ?_⟩
  · rw [he₁, ← he₂]
    exact List.filter_sublist ..
  · simp only [List.all_eq_true, decide_eq_true_eq, List.mem_filter]
    exact fun a ha => ⟨hp₁ a ha, by simpa using ha⟩

/-- Non-vacuous instance of `shrinkMutatorChain_eq_ddminReference_of_monotone_inf`: on a
chain of distinct steps, both shrinkers return the same witness for every "every trigger
step is present" predicate. -/
theorem containsAll_shrinkMutatorChain_eq_ddminReference [DecidableEq α] (req xs r : List α)
    (fuel_s fuel_d : Nat) (hnd : xs.Nodup)
    (h_ddmin : ddminReference (fun ys => req.all (fun a => decide (a ∈ ys))) fuel_d xs = some r)
    (h_fuel : xs.length ≤ fuel_s) :
    shrinkMutatorChain fuel_s (fun ys => req.all (fun a => decide (a ∈ ys))) xs = r :=
  shrinkMutatorChain_eq_ddminReference_of_monotone_inf _ xs r fuel_s fuel_d
    (containsAll_monotone req) (containsAll_inf_closed req xs hnd) h_ddmin h_fuel

/-- Closed-form characterization of 1-minimal trigger-set witnesses on a duplicate-free
chain `xs`: any 1-minimal sublist `r` of `xs` for "every step in `req` is present"
equals `xs.filter (fun a => decide (a ∈ req))`. -/
theorem isOneMinimal_containsAll_eq_filter [DecidableEq α] (req xs r : List α)
    (hsub : r.Sublist xs) (hnd : xs.Nodup)
    (hmin : IsOneMinimal (fun ys => req.all (fun a => decide (a ∈ ys))) r) :
    r = xs.filter (fun a => decide (a ∈ req)) := by
  let pred := fun ys : List α => req.all (fun a => decide (a ∈ ys))
  have hp_r : ∀ a ∈ req, a ∈ r := by
    have h1 := hmin.1
    simp only [List.all_eq_true, decide_eq_true_eq] at h1
    exact h1
  let w := r.filter (fun a => decide (a ∈ req))
  have hw_sub : w.Sublist r := List.filter_sublist
  have hp_w : pred w = true := by
    simp only [pred, w, List.all_eq_true, decide_eq_true_eq, List.mem_filter]
    exact fun a ha => ⟨hp_r a ha, by simpa using ha⟩
  have hw_eq_r : w = r := by
    by_cases hlt : w.length < r.length
    · have hf :=
        isOneMinimal_globally_minimal_of_monotone pred (containsAll_monotone req) hmin w hw_sub hlt
      rw [hp_w] at hf
      contradiction
    · exact sublist_eq_of_length_le hw_sub (by omega)
  have hw_eq_xs : w = xs.filter (fun a => decide (a ∈ req)) :=
    filter_mem_eq_of_sublist_of_nodup req hsub hnd (fun a _ ha => hp_r a ha)
  exact hw_eq_r.symm.trans hw_eq_xs

/-- Closed-form theorem for `shrinkMutatorChain` on trigger-set predicates: on a
duplicate-free chain `xs` with `xs.length ≤ fuel`, `shrinkMutatorChain` returns
`xs.filter (fun a => decide (a ∈ req))`. -/
theorem shrinkMutatorChain_containsAll_eq_filter [DecidableEq α] (req xs : List α) (fuel : Nat)
    (hnd : xs.Nodup)
    (h_pred : req.all (fun a => decide (a ∈ xs)) = true)
    (h_fuel : xs.length ≤ fuel) :
    shrinkMutatorChain fuel (fun ys => req.all (fun a => decide (a ∈ ys))) xs =
      xs.filter (fun a => decide (a ∈ req)) :=
  isOneMinimal_containsAll_eq_filter req xs _
    (shrinkMutatorChain_sublist fuel _ xs) hnd
    (shrinkMutatorChain_one_minimal fuel _ xs h_pred h_fuel)

/-- Closed-form theorem for `ddminReference` on trigger-set predicates (proving the exact
property tested over 600 random trials by `shrink_mutation_chain_detailed_is_globally_minimal_for_monotone_predicates`
in `shrink.rs`): on a duplicate-free chain `xs` with sufficient fuel, `ddminReference`
returns `some (xs.filter (fun a => decide (a ∈ req)))`. -/
theorem ddminReference_containsAll_eq_some_filter [DecidableEq α] (req xs : List α) (fuel : Nat)
    (hnd : xs.Nodup)
    (h_pred : req.all (fun a => decide (a ∈ xs)) = true)
    (h_fuel : xs.length * (xs.length + 1) + (xs.length + 1) / 2 < fuel) :
    ddminReference (fun ys => req.all (fun a => decide (a ∈ ys))) fuel xs =
      some (xs.filter (fun a => decide (a ∈ req))) := by
  obtain ⟨r, hr, hmin, hsub⟩ :=
    ddminReference_total (fun ys => req.all (fun a => decide (a ∈ ys))) xs fuel h_pred h_fuel
  rw [hr, isOneMinimal_containsAll_eq_filter req xs r hsub hnd hmin]

/-- Kernel witness of the instance: both shrinkers isolate exactly the trigger steps
`[1, 4]` of a 6-step chain. -/
theorem containsAll_shrinkers_agree_witness :
    shrinkMutatorChain 6 (fun ys : List Nat => [1, 4].all (fun a => decide (a ∈ ys)))
        [0, 1, 2, 3, 4, 5] = [1, 4] ∧
      ddminReference (fun ys : List Nat => [1, 4].all (fun a => decide (a ∈ ys))) 16
        [0, 1, 2, 3, 4, 5] = some [1, 4] := ⟨by rfl, by rfl⟩

/-- The distinct-steps hypothesis of the instance cannot be dropped: on the chain
`[1, 2, 1]` with a repeated step, the two shrinkers return different 1-minimal witnesses
for "steps `1` and `2` are present" (`h_inf` fails: `[2, 1]` and `[1, 2]` have no common
sublist containing both steps). -/
theorem containsAll_shrinkers_disagree_on_repeated_step :
    shrinkMutatorChain 3 (fun ys : List Nat => [1, 2].all (fun a => decide (a ∈ ys)))
        [1, 2, 1] = [2, 1] ∧
      ddminReference (fun ys : List Nat => [1, 2].all (fun a => decide (a ∈ ys))) 16
        [1, 2, 1] = some [1, 2] := ⟨by rfl, by rfl⟩

/-- Non-monotone (coupled) predicate: `[1, 2, 3]` is 1-minimal although the smaller
`[3]` also satisfies it, so 1-minimality is not global minimality in general. -/
theorem coupled_window_one_minimal_not_globally_minimal :
    IsOneMinimal (fun xs : List Nat => xs == [1, 2, 3] || xs == [3]) [1, 2, 3] ∧
      (fun xs : List Nat => xs == [1, 2, 3] || xs == [3]) [3] = true := by
  refine ⟨⟨rfl, ?_⟩, rfl⟩
  intro ys hys
  simp only [dropOneCandidates, List.map, List.mem_cons, List.not_mem_nil, or_false] at hys
  rcases hys with rfl | rfl | rfl <;> rfl

/-- On that predicate the specification shrinker (single-step deletions only, since
`3 / 2 < 2`) stops at the local minimum `[1, 2, 3]`. -/
theorem coupled_window_spec_shrinker_stops_at_local_minimum :
    shrinkMutatorChain 3 (fun xs : List Nat => xs == [1, 2, 3] || xs == [3]) [1, 2, 3] =
      [1, 2, 3] := by rfl

/-- The reference `ddmin` deletes the coupled window `[1, 2]` at chunk size `2` and
reaches the smaller witness `[3]`. -/
theorem coupled_window_ddmin_reaches_smaller_witness :
    ddminReference (fun xs : List Nat => xs == [1, 2, 3] || xs == [3]) 16 [1, 2, 3] =
      some [3] := by rfl

/-- The fuel hypothesis `xs.length ≤ fuel` of `shrinkMutatorChain_one_minimal` is tight:
with `fuel = xs.length - 1` the result need not be 1-minimal. -/
theorem shrinkMutatorChain_fuel_bound_tight :
    shrinkMutatorChain 2 (fun _ : List Nat => true) [1, 2, 3] = [3] ∧
      ¬ IsOneMinimal (fun _ : List Nat => true)
        (shrinkMutatorChain 2 (fun _ : List Nat => true) [1, 2, 3]) := by
  have hval : shrinkMutatorChain 2 (fun _ : List Nat => true) [1, 2, 3] = [3] := by rfl
  refine ⟨hval, ?_⟩
  rw [hval]
  intro h
  have h_nil := h.2 [] (by simp [dropOneCandidates])
  exact absurd h_nil (by simp)

/-! ### Partial / Fallible Oracle Shrinking (`MutatorChainShrinkStatus::Inconclusive`)

Both `miri-difftest` (`minimize_miri_candidate_mutations_with_compile_check`) and
`itree-difftest` (`minimize_itree_recorded_mutations_with_compile_check`) query a
fallible oracle `pred? : List α → Option Bool`, where `some true` means the
replayed subsequence compiled and reproduced the discrepancy signature,
`some false` means it was judged and rejected, and `none` means the oracle
pipeline failed to produce a judgment (`oracle_failures += 1`).

The Rust shrinker passes `partialOraclePred pred?` (`pred? ys == some true`) to
`shrink_mutation_chain_detailed` and classifies the completed run via
`MutatorChainShrinkStatus::of_completed_shrink`:
- Any accepted reduction `r` is sound (`pred? r = some true` and `r <+ xs`) even
  when some intermediate queries returned `none` (`ddminReference_partialOracle_sound`).
- When every single-step deletion of `r` produced a judgment (`some b`), 1-minimality
  under `partialOraclePred pred?` guarantees that every single-step deletion was
  genuinely judged and rejected with `some false`
  (`isOneMinimal_partialOracle_iff_all_some_false`,
  `ddminReference_partialOracle_confirmed_one_minimal`).
- Conversely, a single `none` failure on a 1-step deletion can mask a strictly
  smaller satisfying subsequence (`partialOracle_failure_masks_smaller_witness`),
  which is why `oracle_failures > 0` reports `Inconclusive` instead of claiming
  1-minimality. -/

/-- Boolean predicate passed to `ddmin` when wrapping a partial/fallible oracle
`pred? : List α → Option Bool`: only confirmed `some true` answers are accepted,
while both `some false` and oracle failures (`none`) return `false`. -/
def partialOraclePred (pred? : List α → Option Bool) (ys : List α) : Bool :=
  pred? ys == some true

@[simp]
theorem partialOraclePred_eq_true_iff (pred? : List α → Option Bool) (ys : List α) :
    partialOraclePred pred? ys = true ↔ pred? ys = some true := by
  simp [partialOraclePred]

theorem partialOraclePred_eq_false_iff (pred? : List α → Option Bool) (ys : List α) :
    partialOraclePred pred? ys = false ↔ pred? ys = some false ∨ pred? ys = none := by
  unfold partialOraclePred
  cases h : pred? ys with
  | none => simp
  | some b => cases b <;> simp

/-- Soundness of `ddminReference` under a partial oracle: even when some oracle
queries fail (`pred? ys = none`), any returned chain `r` is a sublist of `xs`
with `r.length ≤ xs.length` that the oracle positively confirmed
(`pred? r = some true`). -/
theorem ddminReference_partialOracle_sound (pred? : List α → Option Bool) (fuel : Nat)
    (xs r : List α) (h : ddminReference (partialOraclePred pred?) fuel xs = some r) :
    pred? xs = some true ∧ pred? r = some true ∧ r.Sublist xs ∧ r.length ≤ xs.length := by
  obtain ⟨hxs, hmin, hsub⟩ := ddminReference_one_minimal (partialOraclePred pred?) fuel xs r h
  exact ⟨(partialOraclePred_eq_true_iff pred? xs).mp hxs,
    (partialOraclePred_eq_true_iff pred? r).mp hmin.1,
    hsub, hsub.length_le⟩

/-- When no single-step deletion of `r` failed the oracle (`∀ ys ∈ dropOneCandidates r,
∃ b, pred? ys = some b`), 1-minimality under `partialOraclePred pred?` is equivalent
to `pred? r = some true` together with confirmed `some false` rejection of every
single-step deletion of `r`. -/
theorem isOneMinimal_partialOracle_iff_all_some_false (pred? : List α → Option Bool)
    (r : List α) (h_no_fail : ∀ ys ∈ dropOneCandidates r, ∃ b, pred? ys = some b) :
    IsOneMinimal (partialOraclePred pred?) r ↔
      pred? r = some true ∧ ∀ ys ∈ dropOneCandidates r, pred? ys = some false := by
  unfold IsOneMinimal
  rw [partialOraclePred_eq_true_iff]
  refine and_congr_right fun _ => ⟨fun h ys hys => ?_, fun h ys hys => ?_⟩
  · obtain ⟨b, hb⟩ := h_no_fail ys hys
    have hf := (partialOraclePred_eq_false_iff pred? ys).mp (h ys hys)
    rcases hf with hf | hf
    · exact hf
    · rw [hb] at hf
      contradiction
  · exact (partialOraclePred_eq_false_iff pred? ys).mpr (Or.inl (h ys hys))

/-- When `ddminReference (partialOraclePred pred?)` succeeds and every single-step
deletion of `r` was answered by the oracle without failure (in particular, when
`oracle_failures == 0`), `r` is confirmed (`pred? r = some true`) and every
single-step deletion of `r` was confirmed to be rejected (`some false`). -/
theorem ddminReference_partialOracle_confirmed_one_minimal
    (pred? : List α → Option Bool) (fuel : Nat) (xs r : List α)
    (h : ddminReference (partialOraclePred pred?) fuel xs = some r)
    (h_no_fail : ∀ ys ∈ dropOneCandidates r, ∃ b, pred? ys = some b) :
    pred? xs = some true ∧ pred? r = some true ∧
      (∀ ys ∈ dropOneCandidates r, pred? ys = some false) ∧ r.Sublist xs := by
  obtain ⟨hxs, hmin, hsub⟩ := ddminReference_one_minimal (partialOraclePred pred?) fuel xs r h
  obtain ⟨hr, h_all_false⟩ :=
    (isOneMinimal_partialOracle_iff_all_some_false pred? r h_no_fail).mp hmin
  exact ⟨(partialOraclePred_eq_true_iff pred? xs).mp hxs, hr, h_all_false, hsub⟩

/-- Concrete witness justifying `MutatorChainShrinkStatus::Inconclusive`: the true
discrepancy predicate holds on `[1, 2]` and on `[2]`, so `[1, 2]` is not 1-minimal
for the true predicate, but if the oracle fails (`none`) when querying `[2]`,
`ddminReference (partialOraclePred ...)` stops at `[1, 2]`. -/
theorem partialOracle_failure_masks_smaller_witness :
    let truePred := fun xs : List Nat => xs == [1, 2] || xs == [2]
    let fallibleOracle := fun xs : List Nat =>
      if xs == [2] then none else some (truePred xs)
    ddminReference (partialOraclePred fallibleOracle) 10 [1, 2] = some [1, 2] ∧
      truePred [2] = true ∧
      ¬ IsOneMinimal truePred [1, 2] := by
  refine ⟨by rfl, by rfl, fun h => ?_⟩
  have h2 := h.2 [2] (by simp [dropOneCandidates])
  exact absurd h2 (by decide)

/-! ## Part 2: Wide `BitVec` Shift-Exponent Bounds Guard -/

/-- Guarded left shift that checks `rhs.toNat < w` before invoking `lhs <<< rhs.toNat`,
preventing GMP `lean_nat_shiftl` (`SIGABRT: Nat.shiftl exponent is too big`) when
`w ≥ 33` and `rhs.toNat ≥ 2^32`. -/
def bvShlSafe {w : Nat} (lhs rhs : BitVec w) : Option (BitVec w) :=
  if rhs.toNat < w then some (lhs <<< rhs.toNat) else none

/-- Guarded logical right shift that checks `rhs.toNat < w` before invoking `lhs >>> rhs.toNat`. -/
def bvLshrSafe {w : Nat} (lhs rhs : BitVec w) : Option (BitVec w) :=
  if rhs.toNat < w then some (lhs >>> rhs.toNat) else none

/-- Guarded arithmetic right shift that checks `rhs.toNat < w` before invoking
`BitVec.sshiftRight lhs rhs.toNat`. -/
def bvAshrSafe {w : Nat} (lhs rhs : BitVec w) : Option (BitVec w) :=
  if rhs.toNat < w then some (BitVec.sshiftRight lhs rhs.toNat) else none

/-- MIR-style overflowing left shift (`CheckedOp.Shl`) that masks the shift amount by
`rhs.toNat % w` when `w > 0` so `<<<` is only ever called with a shift exponent `< w`,
paired with the overflow flag `decide (rhs.toNat ≥ w)`. -/
def bvShlOverflowing {w : Nat} (lhs rhs : BitVec w) : BitVec w × Bool :=
  if w > 0 then
    (lhs <<< (rhs.toNat % w), decide (w ≤ rhs.toNat))
  else
    (lhs, true)

/-- MIR-style overflowing logical right shift (`CheckedOp.Shr` unsigned). -/
def bvLshrOverflowing {w : Nat} (lhs rhs : BitVec w) : BitVec w × Bool :=
  if w > 0 then
    (lhs >>> (rhs.toNat % w), decide (w ≤ rhs.toNat))
  else
    (lhs, true)

/-- MIR-style overflowing arithmetic right shift (`CheckedOp.Shr` signed). -/
def bvAshrOverflowing {w : Nat} (lhs rhs : BitVec w) : BitVec w × Bool :=
  if w > 0 then
    (BitVec.sshiftRight lhs (rhs.toNat % w), decide (w ≤ rhs.toNat))
  else
    (lhs, true)

@[simp]
theorem bvShlSafe_eq {w : Nat} (lhs rhs : BitVec w) :
    bvShlSafe lhs rhs = (if rhs.toNat < w then some (lhs <<< rhs.toNat) else none) := rfl

@[simp]
theorem bvLshrSafe_eq {w : Nat} (lhs rhs : BitVec w) :
    bvLshrSafe lhs rhs = (if rhs.toNat < w then some (lhs >>> rhs.toNat) else none) := rfl

@[simp]
theorem bvAshrSafe_eq {w : Nat} (lhs rhs : BitVec w) :
    bvAshrSafe lhs rhs =
      (if rhs.toNat < w then some (BitVec.sshiftRight lhs rhs.toNat) else none) := rfl

@[simp]
theorem bvShlSafe_eq_of_lt {w : Nat} (lhs rhs : BitVec w) (h : rhs.toNat < w) :
    bvShlSafe lhs rhs = some (lhs <<< rhs.toNat) := by
  simp [bvShlSafe, h]

@[simp]
theorem bvShlSafe_eq_none_of_ge {w : Nat} (lhs rhs : BitVec w) (h : w ≤ rhs.toNat) :
    bvShlSafe lhs rhs = none := by
  have h_not_lt : ¬ (rhs.toNat < w) := Nat.not_lt.mpr h
  simp [bvShlSafe, h_not_lt]

@[simp]
theorem bvLshrSafe_eq_of_lt {w : Nat} (lhs rhs : BitVec w) (h : rhs.toNat < w) :
    bvLshrSafe lhs rhs = some (lhs >>> rhs.toNat) := by
  simp [bvLshrSafe, h]

@[simp]
theorem bvLshrSafe_eq_none_of_ge {w : Nat} (lhs rhs : BitVec w) (h : w ≤ rhs.toNat) :
    bvLshrSafe lhs rhs = none := by
  have h_not_lt : ¬ (rhs.toNat < w) := Nat.not_lt.mpr h
  simp [bvLshrSafe, h_not_lt]

@[simp]
theorem bvAshrSafe_eq_of_lt {w : Nat} (lhs rhs : BitVec w) (h : rhs.toNat < w) :
    bvAshrSafe lhs rhs = some (BitVec.sshiftRight lhs rhs.toNat) := by
  simp [bvAshrSafe, h]

@[simp]
theorem bvAshrSafe_eq_none_of_ge {w : Nat} (lhs rhs : BitVec w) (h : w ≤ rhs.toNat) :
    bvAshrSafe lhs rhs = none := by
  have h_not_lt : ¬ (rhs.toNat < w) := Nat.not_lt.mpr h
  simp [bvAshrSafe, h_not_lt]

/-- Raw arithmetic fact behind the overflowing companions: the masked exponent
`rhs.toNat % w` is strictly below a positive width `w`. -/
theorem bvShlOverflowing_shift_amount_lt {w : Nat} (rhs : BitVec w) (hw : w > 0) :
    rhs.toNat % w < w :=
  Nat.mod_lt rhs.toNat hw

theorem bvShlOverflowing_eq_of_pos {w : Nat} (lhs rhs : BitVec w) (hw : w > 0) :
    bvShlOverflowing lhs rhs = (lhs <<< (rhs.toNat % w), decide (w ≤ rhs.toNat)) := by
  simp [bvShlOverflowing, hw]

theorem bvLshrOverflowing_eq_of_pos {w : Nat} (lhs rhs : BitVec w) (hw : w > 0) :
    bvLshrOverflowing lhs rhs = (lhs >>> (rhs.toNat % w), decide (w ≤ rhs.toNat)) := by
  simp [bvLshrOverflowing, hw]

theorem bvAshrOverflowing_eq_of_pos {w : Nat} (lhs rhs : BitVec w) (hw : w > 0) :
    bvAshrOverflowing lhs rhs =
      (BitVec.sshiftRight lhs (rhs.toNat % w), decide (w ≤ rhs.toNat)) := by
  simp [bvAshrOverflowing, hw]

/-! ### Exponent bounds stated about the definitions themselves

The statements below quantify over the exponent that each definition actually
passes to a `BitVec` shift primitive, instead of restating `Nat.mod_lt` in
isolation: every shift primitive reached by the overflowing companions receives an
exponent `s < w`, and every `some` result of a guarded operation was produced by
a shift whose exponent is `< w`. For all MIR integer widths (`w ≤ 128`) the
exponent is therefore `< 2^32`, the threshold above which `lean_nat_shiftl`
aborts. -/

private theorem lt_two_pow_32_of_lt_of_le_128 {s w : Nat} (hs : s < w) (hw : w ≤ 128) :
    s < 2 ^ 32 :=
  Nat.lt_of_lt_of_le hs (Nat.le_trans hw (by decide))

/-- `bvShlOverflowing` only ever evaluates `lhs <<< s` with `s < w`. -/
theorem bvShlOverflowing_shift_bound {w : Nat} (lhs rhs : BitVec w) (hw : w > 0) :
    ∃ s, s < w ∧ bvShlOverflowing lhs rhs = (lhs <<< s, decide (w ≤ rhs.toNat)) :=
  ⟨rhs.toNat % w, Nat.mod_lt _ hw, bvShlOverflowing_eq_of_pos lhs rhs hw⟩

/-- `bvLshrOverflowing` only ever evaluates `lhs >>> s` with `s < w`. -/
theorem bvLshrOverflowing_shift_bound {w : Nat} (lhs rhs : BitVec w) (hw : w > 0) :
    ∃ s, s < w ∧ bvLshrOverflowing lhs rhs = (lhs >>> s, decide (w ≤ rhs.toNat)) :=
  ⟨rhs.toNat % w, Nat.mod_lt _ hw, bvLshrOverflowing_eq_of_pos lhs rhs hw⟩

/-- `bvAshrOverflowing` only ever evaluates `BitVec.sshiftRight lhs s` with `s < w`. -/
theorem bvAshrOverflowing_shift_bound {w : Nat} (lhs rhs : BitVec w) (hw : w > 0) :
    ∃ s, s < w ∧
      bvAshrOverflowing lhs rhs = (BitVec.sshiftRight lhs s, decide (w ≤ rhs.toNat)) :=
  ⟨rhs.toNat % w, Nat.mod_lt _ hw, bvAshrOverflowing_eq_of_pos lhs rhs hw⟩

/-- For every MIR integer width (`0 < w ≤ 128`, covering `u64`/`u128`), the exponent
fed to `<<<` by `bvShlOverflowing` is `< 2^32`. -/
theorem bvShlOverflowing_shift_lt_two_pow_32 {w : Nat} (lhs rhs : BitVec w)
    (hw : w > 0) (hw128 : w ≤ 128) :
    ∃ s, s < 2 ^ 32 ∧ bvShlOverflowing lhs rhs = (lhs <<< s, decide (w ≤ rhs.toNat)) := by
  obtain ⟨s, hs, h⟩ := bvShlOverflowing_shift_bound lhs rhs hw
  exact ⟨s, lt_two_pow_32_of_lt_of_le_128 hs hw128, h⟩

/-- Same bound for `bvLshrOverflowing`. -/
theorem bvLshrOverflowing_shift_lt_two_pow_32 {w : Nat} (lhs rhs : BitVec w)
    (hw : w > 0) (hw128 : w ≤ 128) :
    ∃ s, s < 2 ^ 32 ∧ bvLshrOverflowing lhs rhs = (lhs >>> s, decide (w ≤ rhs.toNat)) := by
  obtain ⟨s, hs, h⟩ := bvLshrOverflowing_shift_bound lhs rhs hw
  exact ⟨s, lt_two_pow_32_of_lt_of_le_128 hs hw128, h⟩

/-- Same bound for `bvAshrOverflowing`. -/
theorem bvAshrOverflowing_shift_lt_two_pow_32 {w : Nat} (lhs rhs : BitVec w)
    (hw : w > 0) (hw128 : w ≤ 128) :
    ∃ s, s < 2 ^ 32 ∧
      bvAshrOverflowing lhs rhs = (BitVec.sshiftRight lhs s, decide (w ≤ rhs.toNat)) := by
  obtain ⟨s, hs, h⟩ := bvAshrOverflowing_shift_bound lhs rhs hw
  exact ⟨s, lt_two_pow_32_of_lt_of_le_128 hs hw128, h⟩

/-- Every `some` result of `bvShlSafe` came from an in-bounds shift. -/
theorem bvShlSafe_eq_some_iff {w : Nat} (lhs rhs r : BitVec w) :
    bvShlSafe lhs rhs = some r ↔ rhs.toNat < w ∧ r = lhs <<< rhs.toNat := by
  by_cases h : rhs.toNat < w
  · rw [bvShlSafe_eq_of_lt lhs rhs h]
    exact ⟨fun hs => ⟨h, (Option.some.inj hs).symm⟩, fun ⟨_, hr⟩ => hr ▸ rfl⟩
  · rw [bvShlSafe_eq_none_of_ge lhs rhs (Nat.not_lt.mp h)]
    exact ⟨fun hs => (nomatch hs), fun ⟨hlt, _⟩ => absurd hlt h⟩

/-- Every `some` result of `bvLshrSafe` came from an in-bounds shift. -/
theorem bvLshrSafe_eq_some_iff {w : Nat} (lhs rhs r : BitVec w) :
    bvLshrSafe lhs rhs = some r ↔ rhs.toNat < w ∧ r = lhs >>> rhs.toNat := by
  by_cases h : rhs.toNat < w
  · rw [bvLshrSafe_eq_of_lt lhs rhs h]
    exact ⟨fun hs => ⟨h, (Option.some.inj hs).symm⟩, fun ⟨_, hr⟩ => hr ▸ rfl⟩
  · rw [bvLshrSafe_eq_none_of_ge lhs rhs (Nat.not_lt.mp h)]
    exact ⟨fun hs => (nomatch hs), fun ⟨hlt, _⟩ => absurd hlt h⟩

/-- Every `some` result of `bvAshrSafe` came from an in-bounds shift. -/
theorem bvAshrSafe_eq_some_iff {w : Nat} (lhs rhs r : BitVec w) :
    bvAshrSafe lhs rhs = some r ↔ rhs.toNat < w ∧ r = BitVec.sshiftRight lhs rhs.toNat := by
  by_cases h : rhs.toNat < w
  · rw [bvAshrSafe_eq_of_lt lhs rhs h]
    exact ⟨fun hs => ⟨h, (Option.some.inj hs).symm⟩, fun ⟨_, hr⟩ => hr ▸ rfl⟩
  · rw [bvAshrSafe_eq_none_of_ge lhs rhs (Nat.not_lt.mp h)]
    exact ⟨fun hs => (nomatch hs), fun ⟨hlt, _⟩ => absurd hlt h⟩

/-- A successful guarded shift at any MIR width (`w ≤ 128`) used an exponent `< 2^32`. -/
theorem bvShlSafe_some_shift_lt_two_pow_32 {w : Nat} {lhs rhs r : BitVec w}
    (hw128 : w ≤ 128) (h : bvShlSafe lhs rhs = some r) : rhs.toNat < 2 ^ 32 :=
  lt_two_pow_32_of_lt_of_le_128 ((bvShlSafe_eq_some_iff lhs rhs r).mp h).1 hw128

theorem bvLshrSafe_some_shift_lt_two_pow_32 {w : Nat} {lhs rhs r : BitVec w}
    (hw128 : w ≤ 128) (h : bvLshrSafe lhs rhs = some r) : rhs.toNat < 2 ^ 32 :=
  lt_two_pow_32_of_lt_of_le_128 ((bvLshrSafe_eq_some_iff lhs rhs r).mp h).1 hw128

theorem bvAshrSafe_some_shift_lt_two_pow_32 {w : Nat} {lhs rhs r : BitVec w}
    (hw128 : w ≤ 128) (h : bvAshrSafe lhs rhs = some r) : rhs.toNat < 2 ^ 32 :=
  lt_two_pow_32_of_lt_of_le_128 ((bvAshrSafe_eq_some_iff lhs rhs r).mp h).1 hw128

/-! ### Guarded vs. MIR overflowing shifts agree

In range, the overflowing companion returns exactly the guarded result with a clear
overflow flag; the overflow flag is raised exactly when the guarded operation
refuses (including the degenerate width `w = 0`). -/

theorem bvShlOverflowing_eq_of_lt {w : Nat} (lhs rhs : BitVec w) (h : rhs.toNat < w) :
    bvShlOverflowing lhs rhs = (lhs <<< rhs.toNat, false) := by
  have hw : w > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) h
  rw [bvShlOverflowing_eq_of_pos lhs rhs hw, Nat.mod_eq_of_lt h]
  simp [Nat.not_le.mpr h]

theorem bvLshrOverflowing_eq_of_lt {w : Nat} (lhs rhs : BitVec w) (h : rhs.toNat < w) :
    bvLshrOverflowing lhs rhs = (lhs >>> rhs.toNat, false) := by
  have hw : w > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) h
  rw [bvLshrOverflowing_eq_of_pos lhs rhs hw, Nat.mod_eq_of_lt h]
  simp [Nat.not_le.mpr h]

theorem bvAshrOverflowing_eq_of_lt {w : Nat} (lhs rhs : BitVec w) (h : rhs.toNat < w) :
    bvAshrOverflowing lhs rhs = (BitVec.sshiftRight lhs rhs.toNat, false) := by
  have hw : w > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) h
  rw [bvAshrOverflowing_eq_of_pos lhs rhs hw, Nat.mod_eq_of_lt h]
  simp [Nat.not_le.mpr h]

theorem bvShlSafe_eq_some_overflowing_fst {w : Nat} (lhs rhs : BitVec w)
    (h : rhs.toNat < w) : bvShlSafe lhs rhs = some (bvShlOverflowing lhs rhs).1 := by
  rw [bvShlSafe_eq_of_lt lhs rhs h, bvShlOverflowing_eq_of_lt lhs rhs h]

theorem bvLshrSafe_eq_some_overflowing_fst {w : Nat} (lhs rhs : BitVec w)
    (h : rhs.toNat < w) : bvLshrSafe lhs rhs = some (bvLshrOverflowing lhs rhs).1 := by
  rw [bvLshrSafe_eq_of_lt lhs rhs h, bvLshrOverflowing_eq_of_lt lhs rhs h]

theorem bvAshrSafe_eq_some_overflowing_fst {w : Nat} (lhs rhs : BitVec w)
    (h : rhs.toNat < w) : bvAshrSafe lhs rhs = some (bvAshrOverflowing lhs rhs).1 := by
  rw [bvAshrSafe_eq_of_lt lhs rhs h, bvAshrOverflowing_eq_of_lt lhs rhs h]

theorem bvShlOverflowing_snd_eq_true_iff {w : Nat} (lhs rhs : BitVec w) :
    (bvShlOverflowing lhs rhs).2 = true ↔ bvShlSafe lhs rhs = none := by
  by_cases h : rhs.toNat < w
  · rw [bvShlOverflowing_eq_of_lt lhs rhs h, bvShlSafe_eq_of_lt lhs rhs h]
    simp
  · rw [bvShlSafe_eq_none_of_ge lhs rhs (Nat.not_lt.mp h)]
    unfold bvShlOverflowing
    split <;> simp [Nat.not_lt.mp h]

theorem bvLshrOverflowing_snd_eq_true_iff {w : Nat} (lhs rhs : BitVec w) :
    (bvLshrOverflowing lhs rhs).2 = true ↔ bvLshrSafe lhs rhs = none := by
  by_cases h : rhs.toNat < w
  · rw [bvLshrOverflowing_eq_of_lt lhs rhs h, bvLshrSafe_eq_of_lt lhs rhs h]
    simp
  · rw [bvLshrSafe_eq_none_of_ge lhs rhs (Nat.not_lt.mp h)]
    unfold bvLshrOverflowing
    split <;> simp [Nat.not_lt.mp h]

theorem bvAshrOverflowing_snd_eq_true_iff {w : Nat} (lhs rhs : BitVec w) :
    (bvAshrOverflowing lhs rhs).2 = true ↔ bvAshrSafe lhs rhs = none := by
  by_cases h : rhs.toNat < w
  · rw [bvAshrOverflowing_eq_of_lt lhs rhs h, bvAshrSafe_eq_of_lt lhs rhs h]
    simp
  · rw [bvAshrSafe_eq_none_of_ge lhs rhs (Nat.not_lt.mp h)]
    unfold bvAshrOverflowing
    split <;> simp [Nat.not_lt.mp h]

/-! ### Agreement with Rust's `overflowing_shl` / `overflowing_shr`

Every MIR integer type has a power-of-two width `w = 2^k`. Rust's
`overflowing_shl` / `overflowing_shr` (and MIR's wrapping `Shl` / `Shr`) shift by
`rhs & (BITS - 1)` and report overflow iff `rhs >= BITS`; for such widths the
overflowing companions compute exactly that. -/

theorem bvShlOverflowing_eq_rust_mask {k : Nat} (lhs rhs : BitVec (2 ^ k)) :
    bvShlOverflowing lhs rhs =
      (lhs <<< (rhs.toNat &&& (2 ^ k - 1)), decide (2 ^ k ≤ rhs.toNat)) := by
  rw [bvShlOverflowing_eq_of_pos lhs rhs (Nat.two_pow_pos k), Nat.and_two_pow_sub_one_eq_mod]

theorem bvLshrOverflowing_eq_rust_mask {k : Nat} (lhs rhs : BitVec (2 ^ k)) :
    bvLshrOverflowing lhs rhs =
      (lhs >>> (rhs.toNat &&& (2 ^ k - 1)), decide (2 ^ k ≤ rhs.toNat)) := by
  rw [bvLshrOverflowing_eq_of_pos lhs rhs (Nat.two_pow_pos k), Nat.and_two_pow_sub_one_eq_mod]

theorem bvAshrOverflowing_eq_rust_mask {k : Nat} (lhs rhs : BitVec (2 ^ k)) :
    bvAshrOverflowing lhs rhs =
      (BitVec.sshiftRight lhs (rhs.toNat &&& (2 ^ k - 1)), decide (2 ^ k ≤ rhs.toNat)) := by
  rw [bvAshrOverflowing_eq_of_pos lhs rhs (Nat.two_pow_pos k), Nat.and_two_pow_sub_one_eq_mod]

/-- `u64::overflowing_shl`: shift by `rhs & 63`, overflow iff `rhs ≥ 64`. -/
theorem bvShlOverflowing_u64_eq_rust_mask (lhs rhs : BitVec 64) :
    bvShlOverflowing lhs rhs = (lhs <<< (rhs.toNat &&& 63), decide (64 ≤ rhs.toNat)) :=
  bvShlOverflowing_eq_rust_mask (k := 6) lhs rhs

/-- `u128::overflowing_shl`: shift by `rhs & 127`, overflow iff `rhs ≥ 128`. -/
theorem bvShlOverflowing_u128_eq_rust_mask (lhs rhs : BitVec 128) :
    bvShlOverflowing lhs rhs = (lhs <<< (rhs.toNat &&& 127), decide (128 ≤ rhs.toNat)) :=
  bvShlOverflowing_eq_rust_mask (k := 7) lhs rhs

/-- `i64::overflowing_shr` (arithmetic): shift by `rhs & 63`, overflow iff `rhs ≥ 64`. -/
theorem bvAshrOverflowing_u64_eq_rust_mask (lhs rhs : BitVec 64) :
    bvAshrOverflowing lhs rhs =
      (BitVec.sshiftRight lhs (rhs.toNat &&& 63), decide (64 ≤ rhs.toNat)) :=
  bvAshrOverflowing_eq_rust_mask (k := 6) lhs rhs

/-- `u64::overflowing_shr` (logical): shift by `rhs & 63`, overflow iff `rhs ≥ 64`. -/
theorem bvLshrOverflowing_u64_eq_rust_mask (lhs rhs : BitVec 64) :
    bvLshrOverflowing lhs rhs = (lhs >>> (rhs.toNat &&& 63), decide (64 ≤ rhs.toNat)) :=
  bvLshrOverflowing_eq_rust_mask (k := 6) lhs rhs

/-- `u128::overflowing_shr` (logical): shift by `rhs & 127`, overflow iff `rhs ≥ 128`. -/
theorem bvLshrOverflowing_u128_eq_rust_mask (lhs rhs : BitVec 128) :
    bvLshrOverflowing lhs rhs = (lhs >>> (rhs.toNat &&& 127), decide (128 ≤ rhs.toNat)) :=
  bvLshrOverflowing_eq_rust_mask (k := 7) lhs rhs

/-- `i128::overflowing_shr` (arithmetic): shift by `rhs & 127`, overflow iff `rhs ≥ 128`. -/
theorem bvAshrOverflowing_u128_eq_rust_mask (lhs rhs : BitVec 128) :
    bvAshrOverflowing lhs rhs =
      (BitVec.sshiftRight lhs (rhs.toNat &&& 127), decide (128 ≤ rhs.toNat)) :=
  bvAshrOverflowing_eq_rust_mask (k := 7) lhs rhs

/-- Sign-bit (`msb`) preservation for `bvAshrSafe`: arithmetic right shift preserves
the sign bit of `lhs` on every in-bounds shift. -/
theorem bvAshrSafe_msb_eq {w : Nat} {lhs rhs r : BitVec w}
    (h : bvAshrSafe lhs rhs = some r) : r.msb = lhs.msb := by
  obtain ⟨_, rfl⟩ := (bvAshrSafe_eq_some_iff lhs rhs r).mp h
  exact BitVec.msb_sshiftRight

/-- Sign-bit (`msb`) preservation for `bvAshrOverflowing` at every width `w`
(including `w = 0`). -/
theorem bvAshrOverflowing_fst_msb_eq {w : Nat} (lhs rhs : BitVec w) :
    (bvAshrOverflowing lhs rhs).1.msb = lhs.msb := by
  unfold bvAshrOverflowing
  split
  · exact BitVec.msb_sshiftRight
  · rfl

/-- Zero-shift right-identity for `bvShlSafe` at any positive width `w > 0`. -/
@[simp]
theorem bvShlSafe_zero_right {w : Nat} (lhs : BitVec w) (hw : w > 0) :
    bvShlSafe lhs (0 : BitVec w) = some lhs := by
  rw [bvShlSafe_eq_of_lt lhs 0 (by simpa using hw)]
  simp

/-- Zero-shift right-identity for `bvLshrSafe` at any positive width `w > 0`. -/
@[simp]
theorem bvLshrSafe_zero_right {w : Nat} (lhs : BitVec w) (hw : w > 0) :
    bvLshrSafe lhs (0 : BitVec w) = some lhs := by
  rw [bvLshrSafe_eq_of_lt lhs 0 (by simpa using hw)]
  simp

/-- Zero-shift right-identity for `bvAshrSafe` at any positive width `w > 0`. -/
@[simp]
theorem bvAshrSafe_zero_right {w : Nat} (lhs : BitVec w) (hw : w > 0) :
    bvAshrSafe lhs (0 : BitVec w) = some lhs := by
  rw [bvAshrSafe_eq_of_lt lhs 0 (by simpa using hw)]
  simp

/-- Zero-shift right-identity for `bvShlOverflowing` at any positive width `w > 0`. -/
@[simp]
theorem bvShlOverflowing_zero_right {w : Nat} (lhs : BitVec w) (hw : w > 0) :
    bvShlOverflowing lhs (0 : BitVec w) = (lhs, false) := by
  rw [bvShlOverflowing_eq_of_lt lhs 0 (by simpa using hw)]
  simp

/-- Zero-shift right-identity for `bvLshrOverflowing` at any positive width `w > 0`. -/
@[simp]
theorem bvLshrOverflowing_zero_right {w : Nat} (lhs : BitVec w) (hw : w > 0) :
    bvLshrOverflowing lhs (0 : BitVec w) = (lhs, false) := by
  rw [bvLshrOverflowing_eq_of_lt lhs 0 (by simpa using hw)]
  simp

/-- Zero-shift right-identity for `bvAshrOverflowing` at any positive width `w > 0`. -/
@[simp]
theorem bvAshrOverflowing_zero_right {w : Nat} (lhs : BitVec w) (hw : w > 0) :
    bvAshrOverflowing lhs (0 : BitVec w) = (lhs, false) := by
  rw [bvAshrOverflowing_eq_of_lt lhs 0 (by simpa using hw)]
  simp

/-! ## Part 3: Concrete Kernel Regression Witnesses (Zero `native_decide`) -/

/-- On non-negative operands (`msb = false`) the guarded arithmetic and logical right
shifts coincide. -/
theorem bvAshrSafe_eq_bvLshrSafe_of_msb_false {w : Nat} (lhs rhs : BitVec w)
    (h : lhs.msb = false) : bvAshrSafe lhs rhs = bvLshrSafe lhs rhs := by
  unfold bvAshrSafe bvLshrSafe
  split <;> simp [BitVec.sshiftRight_eq_of_msb_false h]

/-- On non-negative operands the overflowing arithmetic and logical right shifts
coincide (shifted value and overflow flag). -/
theorem bvAshrOverflowing_eq_bvLshrOverflowing_of_msb_false {w : Nat} (lhs rhs : BitVec w)
    (h : lhs.msb = false) : bvAshrOverflowing lhs rhs = bvLshrOverflowing lhs rhs := by
  unfold bvAshrOverflowing bvLshrOverflowing
  split <;> simp [BitVec.sshiftRight_eq_of_msb_false h]

/-- On negative operands they differ: `i8::MIN >> 1` is `0xC0` arithmetically but `0x40`
logically. -/
theorem bvAshrSafe_ne_bvLshrSafe_i8_min :
    bvAshrSafe (BitVec.ofInt 8 (-128)) (BitVec.ofNat 8 1) = some (BitVec.ofNat 8 0xC0) ∧
      bvLshrSafe (BitVec.ofInt 8 (-128)) (BitVec.ofNat 8 1) = some (BitVec.ofNat 8 0x40) := by
  constructor <;> rfl

/-- Wide `BitVec 64` shifts with exponent `2^32` (`4294967296`) evaluate cleanly
in the Lean 4 kernel without triggering `lean_nat_shiftl` `SIGABRT`. -/
theorem bvShlSafe_u64_exp_2pow32 :
    bvShlSafe (BitVec.ofNat 64 1) (BitVec.ofNat 64 (2 ^ 32)) = none := by rfl

theorem bvLshrSafe_u64_exp_2pow32 :
    bvLshrSafe (BitVec.ofNat 64 0xFFFF_FFFF_FFFF_FFFF) (BitVec.ofNat 64 (2 ^ 32)) = none := by rfl

theorem bvAshrSafe_u64_exp_2pow40 :
    bvAshrSafe (BitVec.ofNat 64 0x8000_0000_0000_0000) (BitVec.ofNat 64 (2 ^ 40)) = none := by rfl

/-- Wide `BitVec 128` shifts with exponents `2^32`, `2^40`, and `2^64 + 13` evaluate
cleanly in the Lean 4 kernel via `by rfl`. -/
theorem bvShlSafe_u128_exp_2pow32 :
    bvShlSafe (BitVec.ofNat 128 1) (BitVec.ofNat 128 (2 ^ 32)) = none := by rfl

theorem bvShlSafe_u128_exp_2pow64_plus_13 :
    bvShlSafe (BitVec.ofNat 128 7) (BitVec.ofNat 128 (2 ^ 64 + 13)) = none := by rfl

theorem bvLshrSafe_u128_exp_2pow64_plus_13 :
    bvLshrSafe (BitVec.ofNat 128 7) (BitVec.ofNat 128 (2 ^ 64 + 13)) = none := by rfl

theorem bvAshrSafe_u128_exp_2pow64_plus_13 :
    bvAshrSafe (BitVec.ofNat 128 7) (BitVec.ofNat 128 (2 ^ 64 + 13)) = none := by rfl

theorem bvShlOverflowing_u64_exp_2pow32 :
    bvShlOverflowing (BitVec.ofNat 64 1) (BitVec.ofNat 64 (2 ^ 32)) =
      (BitVec.ofNat 64 1, true) := by rfl

theorem bvShlOverflowing_u128_exp_2pow64_plus_13 :
    bvShlOverflowing (BitVec.ofNat 128 1) (BitVec.ofNat 128 (2 ^ 64 + 13)) =
      (BitVec.ofNat 128 (1 <<< 13), true) := by rfl

theorem bvShlSafe_u64_in_bounds_63 :
    bvShlSafe (BitVec.ofNat 64 1) (BitVec.ofNat 64 63) =
      some (BitVec.ofNat 64 (1 <<< 63)) := by rfl

/-! ### Complete wide-shift regression matrix

Every guarded operation and every overflowing companion is evaluated in the
kernel on `BitVec 64` and `BitVec 128` with exponents `2^32`, `2^40`, and
`2^64 + 13`. The left operands set both the sign bit and bit `0`, so arithmetic
vs. logical right shifts and truncating left shifts are distinguishable.
Note that `BitVec.ofNat 64 (2^64 + 13)` truncates to `13` at construction, so on
`BitVec 64` the `2^64 + 13` row exercises the in-range path. -/

/-- `0x8000_0000_0000_0001`: sign bit and bit `0` set. -/
abbrev wideLhs64 : BitVec 64 := BitVec.ofNat 64 0x8000_0000_0000_0001

/-- `2^127 + 1`: sign bit and bit `0` set. -/
abbrev wideLhs128 : BitVec 128 := BitVec.ofNat 128 (2 ^ 127 + 1)

theorem bvShlSafe_u64_exp_2pow40 :
    bvShlSafe wideLhs64 (BitVec.ofNat 64 (2 ^ 40)) = none := by rfl

theorem bvShlSafe_u64_exp_2pow64_plus_13_truncates :
    bvShlSafe wideLhs64 (BitVec.ofNat 64 (2 ^ 64 + 13)) = some (BitVec.ofNat 64 0x2000) := by
  rfl

theorem bvLshrSafe_u64_exp_2pow40 :
    bvLshrSafe wideLhs64 (BitVec.ofNat 64 (2 ^ 40)) = none := by rfl

theorem bvLshrSafe_u64_exp_2pow64_plus_13_truncates :
    bvLshrSafe wideLhs64 (BitVec.ofNat 64 (2 ^ 64 + 13)) =
      some (BitVec.ofNat 64 (2 ^ 50)) := by rfl

theorem bvAshrSafe_u64_exp_2pow32 :
    bvAshrSafe wideLhs64 (BitVec.ofNat 64 (2 ^ 32)) = none := by rfl

theorem bvAshrSafe_u64_exp_2pow64_plus_13_truncates :
    bvAshrSafe wideLhs64 (BitVec.ofNat 64 (2 ^ 64 + 13)) =
      some (BitVec.ofNat 64 0xFFFC_0000_0000_0000) := by rfl

theorem bvShlSafe_u128_exp_2pow40 :
    bvShlSafe wideLhs128 (BitVec.ofNat 128 (2 ^ 40)) = none := by rfl

theorem bvLshrSafe_u128_exp_2pow32 :
    bvLshrSafe wideLhs128 (BitVec.ofNat 128 (2 ^ 32)) = none := by rfl

theorem bvLshrSafe_u128_exp_2pow40 :
    bvLshrSafe wideLhs128 (BitVec.ofNat 128 (2 ^ 40)) = none := by rfl

theorem bvAshrSafe_u128_exp_2pow32 :
    bvAshrSafe wideLhs128 (BitVec.ofNat 128 (2 ^ 32)) = none := by rfl

theorem bvAshrSafe_u128_exp_2pow40 :
    bvAshrSafe wideLhs128 (BitVec.ofNat 128 (2 ^ 40)) = none := by rfl

theorem bvShlOverflowing_u64_exp_2pow40 :
    bvShlOverflowing wideLhs64 (BitVec.ofNat 64 (2 ^ 40)) = (wideLhs64, true) := by rfl

theorem bvShlOverflowing_u64_exp_2pow64_plus_13_truncates :
    bvShlOverflowing wideLhs64 (BitVec.ofNat 64 (2 ^ 64 + 13)) =
      (BitVec.ofNat 64 0x2000, false) := by rfl

theorem bvLshrOverflowing_u64_exp_2pow32 :
    bvLshrOverflowing wideLhs64 (BitVec.ofNat 64 (2 ^ 32)) = (wideLhs64, true) := by rfl

theorem bvLshrOverflowing_u64_exp_2pow40 :
    bvLshrOverflowing wideLhs64 (BitVec.ofNat 64 (2 ^ 40)) = (wideLhs64, true) := by rfl

theorem bvLshrOverflowing_u64_exp_2pow64_plus_13_truncates :
    bvLshrOverflowing wideLhs64 (BitVec.ofNat 64 (2 ^ 64 + 13)) =
      (BitVec.ofNat 64 (2 ^ 50), false) := by rfl

theorem bvAshrOverflowing_u64_exp_2pow32 :
    bvAshrOverflowing wideLhs64 (BitVec.ofNat 64 (2 ^ 32)) = (wideLhs64, true) := by rfl

theorem bvAshrOverflowing_u64_exp_2pow40 :
    bvAshrOverflowing wideLhs64 (BitVec.ofNat 64 (2 ^ 40)) = (wideLhs64, true) := by rfl

theorem bvAshrOverflowing_u64_exp_2pow64_plus_13_truncates :
    bvAshrOverflowing wideLhs64 (BitVec.ofNat 64 (2 ^ 64 + 13)) =
      (BitVec.ofNat 64 0xFFFC_0000_0000_0000, false) := by rfl

theorem bvShlOverflowing_u128_exp_2pow32 :
    bvShlOverflowing wideLhs128 (BitVec.ofNat 128 (2 ^ 32)) = (wideLhs128, true) := by rfl

theorem bvShlOverflowing_u128_exp_2pow40 :
    bvShlOverflowing wideLhs128 (BitVec.ofNat 128 (2 ^ 40)) = (wideLhs128, true) := by rfl

theorem bvShlOverflowing_u128_exp_2pow64_plus_13_masks_to_13 :
    bvShlOverflowing wideLhs128 (BitVec.ofNat 128 (2 ^ 64 + 13)) =
      (BitVec.ofNat 128 0x2000, true) := by rfl

theorem bvLshrOverflowing_u128_exp_2pow32 :
    bvLshrOverflowing wideLhs128 (BitVec.ofNat 128 (2 ^ 32)) = (wideLhs128, true) := by rfl

theorem bvLshrOverflowing_u128_exp_2pow40 :
    bvLshrOverflowing wideLhs128 (BitVec.ofNat 128 (2 ^ 40)) = (wideLhs128, true) := by rfl

theorem bvLshrOverflowing_u128_exp_2pow64_plus_13_masks_to_13 :
    bvLshrOverflowing wideLhs128 (BitVec.ofNat 128 (2 ^ 64 + 13)) =
      (BitVec.ofNat 128 (2 ^ 114), true) := by rfl

theorem bvAshrOverflowing_u128_exp_2pow32 :
    bvAshrOverflowing wideLhs128 (BitVec.ofNat 128 (2 ^ 32)) = (wideLhs128, true) := by rfl

theorem bvAshrOverflowing_u128_exp_2pow40 :
    bvAshrOverflowing wideLhs128 (BitVec.ofNat 128 (2 ^ 40)) = (wideLhs128, true) := by rfl

theorem bvAshrOverflowing_u128_exp_2pow64_plus_13_masks_to_13 :
    bvAshrOverflowing wideLhs128 (BitVec.ofNat 128 (2 ^ 64 + 13)) =
      (BitVec.ofNat 128 (2 ^ 128 - 2 ^ 114), true) := by rfl

/-! ### Signed, boundary, odd-width, and zero-width corner cases -/

/-- A negative signed shift amount (`-1`, i.e. all ones in two's complement) is out
of range, and the overflowing companion masks it to `63` with the flag raised. -/
theorem bvShlSafe_u64_neg_one_amount :
    bvShlSafe (BitVec.ofNat 64 1) (BitVec.ofInt 64 (-1)) = none := by rfl

theorem bvShlOverflowing_u64_neg_one_amount :
    bvShlOverflowing (BitVec.ofNat 64 1) (BitVec.ofInt 64 (-1)) =
      (BitVec.ofNat 64 (2 ^ 63), true) := by rfl

/-- Shift amount exactly equal to the width is rejected; `w - 1` is accepted. -/
theorem bvLshrSafe_u8_amount_eq_width :
    bvLshrSafe (BitVec.ofNat 8 0xFF) (BitVec.ofNat 8 8) = none := by rfl

theorem bvLshrSafe_u8_amount_width_sub_one :
    bvLshrSafe (BitVec.ofNat 8 0xFF) (BitVec.ofNat 8 7) = some (BitVec.ofNat 8 1) := by rfl

/-- `i8::MIN >> 7` (arithmetic) is `-1`; `i8::MIN >> 8` overflows and masks to `>> 0`. -/
theorem bvAshrSafe_i8_min_by_7 :
    bvAshrSafe (BitVec.ofInt 8 (-128)) (BitVec.ofNat 8 7) = some (BitVec.ofInt 8 (-1)) := by rfl

theorem bvAshrOverflowing_i8_min_by_8 :
    bvAshrOverflowing (BitVec.ofInt 8 (-128)) (BitVec.ofNat 8 8) =
      (BitVec.ofInt 8 (-128), true) := by rfl

/-- Width `33` is the smallest width admitting an exponent `2^32`: the guarded shift
refuses it, and the overflowing companion uses `2^32 % 33 = 4`. -/
theorem bvShlSafe_u33_exp_2pow32 :
    bvShlSafe (BitVec.ofNat 33 1) (BitVec.ofNat 33 (2 ^ 32)) = none := by rfl

theorem bvShlOverflowing_u33_exp_2pow32 :
    bvShlOverflowing (BitVec.ofNat 33 1) (BitVec.ofNat 33 (2 ^ 32)) =
      (BitVec.ofNat 33 16, true) := by rfl

/-- Degenerate width `0`: every shift is refused / flagged and the operand is kept. -/
theorem bvShlSafe_width_zero : bvShlSafe (0 : BitVec 0) 0 = none := by rfl

theorem bvShlOverflowing_width_zero : bvShlOverflowing (0 : BitVec 0) 0 = (0, true) := by rfl

/-! ## Part 3b: Compiled-Code Regression Guards

The `by rfl` witnesses above are checked by the kernel. The abort this module guards
against happens in the *runtime*: in this toolchain, `#eval` of the unguarded
`(BitVec.ofNat 64 1) <<< (2 ^ 32 : Nat)` terminates the Lean process with
`INTERNAL PANIC: Nat.shiftl exponent is too big`, because `BitVec.shiftLeft x s`
computes `x.toNat <<< s` before truncating. Each `#guard` below evaluates a guarded
operation in the interpreter, so removing or weakening a guard makes elaboration of
this very file abort instead of silently passing. -/

#guard bvShlSafe wideLhs64 (BitVec.ofNat 64 (2 ^ 32)) == none
#guard bvShlSafe wideLhs64 (BitVec.ofNat 64 (2 ^ 40)) == none
#guard bvShlSafe wideLhs64 (BitVec.ofNat 64 (2 ^ 64 + 13)) == some (BitVec.ofNat 64 0x2000)
#guard bvLshrSafe wideLhs64 (BitVec.ofNat 64 (2 ^ 32)) == none
#guard bvLshrSafe wideLhs64 (BitVec.ofNat 64 (2 ^ 40)) == none
#guard bvLshrSafe wideLhs64 (BitVec.ofNat 64 (2 ^ 64 + 13)) == some (BitVec.ofNat 64 (2 ^ 50))
#guard bvAshrSafe wideLhs64 (BitVec.ofNat 64 (2 ^ 32)) == none
#guard bvAshrSafe wideLhs64 (BitVec.ofNat 64 (2 ^ 40)) == none
#guard bvAshrSafe wideLhs64 (BitVec.ofNat 64 (2 ^ 64 + 13)) ==
  some (BitVec.ofNat 64 0xFFFC_0000_0000_0000)
#guard bvShlOverflowing wideLhs64 (BitVec.ofNat 64 (2 ^ 32)) == (wideLhs64, true)
#guard bvShlOverflowing wideLhs64 (BitVec.ofNat 64 (2 ^ 40)) == (wideLhs64, true)
#guard bvShlOverflowing wideLhs64 (BitVec.ofNat 64 (2 ^ 64 + 13)) ==
  (BitVec.ofNat 64 0x2000, false)
#guard bvLshrOverflowing wideLhs64 (BitVec.ofNat 64 (2 ^ 32)) == (wideLhs64, true)
#guard bvLshrOverflowing wideLhs64 (BitVec.ofNat 64 (2 ^ 40)) == (wideLhs64, true)
#guard bvLshrOverflowing wideLhs64 (BitVec.ofNat 64 (2 ^ 64 + 13)) ==
  (BitVec.ofNat 64 (2 ^ 50), false)
#guard bvAshrOverflowing wideLhs64 (BitVec.ofNat 64 (2 ^ 32)) == (wideLhs64, true)
#guard bvAshrOverflowing wideLhs64 (BitVec.ofNat 64 (2 ^ 40)) == (wideLhs64, true)
#guard bvAshrOverflowing wideLhs64 (BitVec.ofNat 64 (2 ^ 64 + 13)) ==
  (BitVec.ofNat 64 0xFFFC_0000_0000_0000, false)
#guard bvShlSafe wideLhs128 (BitVec.ofNat 128 (2 ^ 32)) == none
#guard bvShlSafe wideLhs128 (BitVec.ofNat 128 (2 ^ 40)) == none
#guard bvShlSafe wideLhs128 (BitVec.ofNat 128 (2 ^ 64 + 13)) == none
#guard bvLshrSafe wideLhs128 (BitVec.ofNat 128 (2 ^ 32)) == none
#guard bvLshrSafe wideLhs128 (BitVec.ofNat 128 (2 ^ 40)) == none
#guard bvLshrSafe wideLhs128 (BitVec.ofNat 128 (2 ^ 64 + 13)) == none
#guard bvAshrSafe wideLhs128 (BitVec.ofNat 128 (2 ^ 32)) == none
#guard bvAshrSafe wideLhs128 (BitVec.ofNat 128 (2 ^ 40)) == none
#guard bvAshrSafe wideLhs128 (BitVec.ofNat 128 (2 ^ 64 + 13)) == none
#guard bvShlOverflowing wideLhs128 (BitVec.ofNat 128 (2 ^ 32)) == (wideLhs128, true)
#guard bvShlOverflowing wideLhs128 (BitVec.ofNat 128 (2 ^ 40)) == (wideLhs128, true)
#guard bvShlOverflowing wideLhs128 (BitVec.ofNat 128 (2 ^ 64 + 13)) ==
  (BitVec.ofNat 128 0x2000, true)
#guard bvLshrOverflowing wideLhs128 (BitVec.ofNat 128 (2 ^ 32)) == (wideLhs128, true)
#guard bvLshrOverflowing wideLhs128 (BitVec.ofNat 128 (2 ^ 40)) == (wideLhs128, true)
#guard bvLshrOverflowing wideLhs128 (BitVec.ofNat 128 (2 ^ 64 + 13)) ==
  (BitVec.ofNat 128 (2 ^ 114), true)
#guard bvAshrOverflowing wideLhs128 (BitVec.ofNat 128 (2 ^ 32)) == (wideLhs128, true)
#guard bvAshrOverflowing wideLhs128 (BitVec.ofNat 128 (2 ^ 40)) == (wideLhs128, true)
#guard bvAshrOverflowing wideLhs128 (BitVec.ofNat 128 (2 ^ 64 + 13)) ==
  (BitVec.ofNat 128 (2 ^ 128 - 2 ^ 114), true)
#guard bvShlSafe (BitVec.ofNat 64 1) (BitVec.ofInt 64 (-1)) == none
#guard bvShlOverflowing (BitVec.ofNat 64 1) (BitVec.ofInt 64 (-1)) ==
  (BitVec.ofNat 64 (2 ^ 63), true)
#guard bvShlSafe (BitVec.ofNat 33 1) (BitVec.ofNat 33 (2 ^ 32)) == none
#guard bvShlOverflowing (BitVec.ofNat 33 1) (BitVec.ofNat 33 (2 ^ 32)) ==
  (BitVec.ofNat 33 16, true)

/-- Concrete kernel execution of `shrinkMutatorChain` reducing a 5-step mutator chain
down to its 2-step 1-minimal subsequence `[2, 4]`. -/
theorem shrinkMutatorChain_concrete_pair_witness :
    shrinkMutatorChain 5 (fun xs => xs.contains 2 && xs.contains 4) [1, 2, 3, 4, 5] =
      [2, 4] := by rfl

/-! ### Kernel witnesses mirroring the Rust `shrink_mutation_chain_detailed` edge cases -/

/-- Coupled AST dependency: step `2` only compiles together with step `1`, and step `4`
is the divergence trigger. The half-length chunk deletion removes the coupled pair
`[1, 2]` in one step before single-step deletions isolate `[4]`. -/
theorem shrinkMutatorChain_coupled_pair_witness :
    shrinkMutatorChain 4 (fun xs => (xs.contains 1 == xs.contains 2) && xs.contains 4)
      [1, 2, 3, 4] = [4] := by rfl

/-- Tag-sensitive pair: `[1, 4]` reproduces tag `0` (for example `missed_ub`) while `[1]`
alone produces a different tag `1` (for example `panic`), so shrinking under
`evalMatchesTag eval 0` must keep both steps. -/
theorem shrinkMutatorChain_tag_pair_witness :
    shrinkMutatorChain 6
        (evalMatchesTag
          (fun xs : List Nat =>
            if xs.contains 1 && xs.contains 4 then some 0
            else if xs.contains 1 then some 1 else none)
          0)
        [0, 1, 2, 3, 4, 5] = [1, 4] := by rfl

/-- Root fault: when the unmutated seed `[]` already satisfies the predicate, the
1-minimal witness is `[]`. -/
theorem shrinkMutatorChain_root_fault_witness :
    shrinkMutatorChain 3 (fun _ => true) [1, 2, 3] = [] := by rfl

/-- Single-step chain whose deletion falsifies the predicate is already 1-minimal. -/
theorem shrinkMutatorChain_single_step_witness :
    shrinkMutatorChain 1 (fun xs => xs == [7]) [7] = [7] := by rfl

#print axioms shrinkMutatorChain_preserves_discrepancy
#print axioms shrinkMutatorChain_sublist
#print axioms shrinkMutatorChain_len_le
#print axioms shrinkMutatorChain_one_minimal
#print axioms isOneMinimal_iff_dropOneStep_fixed
#print axioms shrinkMutatorChain_idempotent
#print axioms shrinkDiscrepancyWitness_one_minimal
#print axioms shrinkMutatorChain_eval_tag_sound
#print axioms ddminReference_one_minimal
#print axioms ddminReference_total
#print axioms ddminLoop_one_eq_some_of_isOneMinimal
#print axioms ddminReference_eq_some_self_of_isOneMinimal_le_two
#print axioms isOneMinimal_globally_minimal_of_monotone
#print axioms ddminReference_globally_minimal_of_monotone
#print axioms isOneMinimal_unique_of_monotone_inf
#print axioms shrinkMutatorChain_eq_ddminReference_of_monotone_inf
#print axioms containsAll_inf_closed
#print axioms containsAll_shrinkMutatorChain_eq_ddminReference
#print axioms isOneMinimal_containsAll_eq_filter
#print axioms shrinkMutatorChain_containsAll_eq_filter
#print axioms ddminReference_containsAll_eq_some_filter
#print axioms containsAll_shrinkers_disagree_on_repeated_step
#print axioms coupled_window_one_minimal_not_globally_minimal
#print axioms shrinkMutatorChain_fuel_bound_tight
#print axioms ddminReference_partialOracle_sound
#print axioms isOneMinimal_partialOracle_iff_all_some_false
#print axioms ddminReference_partialOracle_confirmed_one_minimal
#print axioms partialOracle_failure_masks_smaller_witness
#print axioms bvAshrOverflowing_eq_bvLshrOverflowing_of_msb_false
#print axioms ddminReference_coupled_pair_witness
#print axioms bvShlOverflowing_shift_bound
#print axioms bvShlOverflowing_shift_lt_two_pow_32
#print axioms bvAshrOverflowing_shift_lt_two_pow_32
#print axioms bvShlSafe_eq_some_iff
#print axioms bvShlSafe_some_shift_lt_two_pow_32
#print axioms bvShlOverflowing_snd_eq_true_iff
#print axioms bvAshrOverflowing_snd_eq_true_iff
#print axioms bvAshrSafe_msb_eq
#print axioms bvAshrOverflowing_fst_msb_eq
#print axioms bvShlSafe_zero_right
#print axioms bvAshrOverflowing_zero_right
#print axioms bvShlSafe_u128_exp_2pow64_plus_13
#print axioms bvShlOverflowing_u128_exp_2pow64_plus_13
#print axioms bvAshrOverflowing_u128_exp_2pow64_plus_13_masks_to_13
#print axioms shrinkMutatorChain_tag_pair_witness

end Anneal.DiffTestShrinker

namespace Anneal

/-! Re-exports of the core shrinker and wide-shift declarations under `Anneal`
for every importer of this module. -/

export Anneal.DiffTestShrinker (
  DiscrepancyWitness dropOneCandidates dropChunkCandidates IsOneMinimal
  shrinkMutatorChain evalMatchesTag shrinkDiscrepancyWitness
  shrinkMutatorChain_preserves_discrepancy shrinkMutatorChain_sublist
  shrinkMutatorChain_len_le shrinkMutatorChain_one_minimal
  shrinkMutatorChain_idempotent shrinkDiscrepancyWitness_one_minimal
  windowDelete ddminSweep ddminNextChunk ddminLoop ddminReference
  ddminReference_one_minimal ddminReference_total
  ddminLoop_one_eq_some_of_isOneMinimal
  isOneMinimal_globally_minimal_of_monotone
  ddminReference_globally_minimal_of_monotone
  ddminReference_containsAll_eq_some_filter
  containsAll_shrinkMutatorChain_eq_ddminReference
  partialOraclePred ddminReference_partialOracle_sound
  isOneMinimal_partialOracle_iff_all_some_false
  ddminReference_partialOracle_confirmed_one_minimal
  bvShlSafe bvLshrSafe bvAshrSafe
  bvShlOverflowing bvLshrOverflowing bvAshrOverflowing
  bvShlSafe_some_shift_lt_two_pow_32 bvLshrSafe_some_shift_lt_two_pow_32
  bvAshrSafe_some_shift_lt_two_pow_32
  bvShlOverflowing_shift_lt_two_pow_32 bvLshrOverflowing_shift_lt_two_pow_32
  bvAshrOverflowing_shift_lt_two_pow_32
  bvShlOverflowing_eq_rust_mask bvLshrOverflowing_eq_rust_mask
  bvAshrOverflowing_eq_rust_mask
  bvShlOverflowing_snd_eq_true_iff bvLshrOverflowing_snd_eq_true_iff
  bvAshrOverflowing_snd_eq_true_iff
  bvAshrSafe_msb_eq bvAshrOverflowing_fst_msb_eq
)

end Anneal
