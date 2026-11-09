namespace Anneal.DiffTestShrinkerPrototype

/-!
# Verified Mutator-Chain Delta-Debugging Shrinker & Wide `BitVec` Shift Guard Prototype

Track P prototype (`ws-proto-difftest-shrinker-mutant-gate`) formalizing:
1. Deterministic single-step (`dropOneCandidates`), chunk-deletion (`dropChunkCandidates`),
   and fuel-bounded (`shrinkMutatorChain`) mutator-chain shrinking with machine-checked
   discrepancy preservation, length monotonicity, `List.Sublist` preservation, and
   1-minimality (`IsOneMinimal`).
2. Guarded wide `BitVec` shift operations (`bvShlSafe`, `bvLshrSafe`, `bvAshrSafe`)
   and MIR-style overflowing shift companions (`bvShlOverflowing`, `bvLshrOverflowing`,
   `bvAshrOverflowing`) that bound shift exponents before invoking Lean's `BitVec`
   shift primitives, preventing `lean_nat_shiftl` (`SIGABRT: Nat.shiftl exponent is too big`)
   panics on 64-bit and 128-bit operands when `rhs ≥ 2^32`.
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

theorem bvShlOverflowing_shift_bound {w : Nat} (rhs : BitVec w) (hw : w > 0) :
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

/-! ## Part 3: Concrete Kernel Regression Witnesses (Zero `native_decide`) -/

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

/-- Concrete kernel execution of `shrinkMutatorChain` reducing a 5-step mutator chain
down to its 2-step 1-minimal subsequence `[2, 4]`. -/
theorem shrinkMutatorChain_concrete_pair_witness :
    shrinkMutatorChain 5 (fun xs => xs.contains 2 && xs.contains 4) [1, 2, 3, 4, 5] =
      [2, 4] := by rfl

#print axioms shrinkMutatorChain_preserves_discrepancy
#print axioms shrinkMutatorChain_sublist
#print axioms shrinkMutatorChain_len_le
#print axioms shrinkMutatorChain_one_minimal
#print axioms shrinkDiscrepancyWitness_one_minimal
#print axioms bvShlSafe_u128_exp_2pow64_plus_13
#print axioms bvShlOverflowing_u128_exp_2pow64_plus_13

end Anneal.DiffTestShrinkerPrototype
