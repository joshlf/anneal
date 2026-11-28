-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.NotationExtra
import Init.Data.Nat.Basic
import Init.Data.List.Basic
import Init.Data.Option.Basic
import Anneal.InitLemmas
import Anneal.Hybrid

/-!
# Canaries for `Anneal.Hybrid`

Concrete instances of every combinator in `Anneal.Hybrid`, together with
the counterexamples that motivate its design:

1. **Portfolios and `toOption`:** choosing the first producer that returns
   any candidate and only then checking it loses a valid backup
   (`naive_precheck_orelse_drops_valid_backup`); `firstAccepted` skips an
   oversized witness and a wrong candidate (`canary_portfolio`); `toOption`
   projects accepted and rejected gate results (`canary_toOption_projection`).
2. **Fallbacks:** re-checking the fallback's result with an incomplete
   checker aborts on an input where the fallback is correct
   (`runtime_checked_fallback_aborts`), while `withFallback` stays sound.
3. **Hint steps and streams:** a rejected hint falls back to the current
   state (`canary_hint_steps`), and a stream stops at the first rejected
   chunk without emitting it while every emitted chunk stays valid
   (`canary_stream_prefix`, `canary_stream_prefix_valid`).
4. **Certificate cuts:** `Anneal.LinearArith` natural-number and integer
   cut certificates and an `Anneal.BitTrieLrat` refutation discharge their
   goals by `rfl` through `certGateCut_sound`; oversized and forged
   certificates are rejected across all three gates (`canary_natCut_bounds`,
   `canary_rup_bounds`, `canary_intCut_bounds`).
5. **`zerocopy` slice-DST casts (`sliceDstCastGate`):** a witness-free
   relational gate for the result of zerocopy's
   `DstLayout::validate_cast_and_convert_metadata`
   (`zerocopy/src/layout.rs`): the element count and split point must fit,
   be aligned, and be maximal. The object's pointer alignment and its
   size-rounding alignment are separate, as in zerocopy, where a
   `repr(packed)` wrapper lowers the first but not the second. The gate is
   proved sound, accepts the maximal candidate, and rejects a sub-maximal
   one and a misaligned suffix cast. The model works over unbounded `Nat`
   with a `usize` bound on `addr + bytes_len`; it is not a proof about the
   Rust function.
6. **In-process producers:** a producer free of undefined behavior that
   overwrites caller memory before returning a wrong candidate breaks the
   composed contract even with a sound checker and a correct fallback
   (`rung15_without_callerMemPreserved_unsound`); a memory-preserving
   producer with the same wrong candidate does not
   (`canary_rung15_preserving`), including under `isUnsafe = true`, unwinding,
   and strict effect-mask weakening (`canary_rung15_unsafe_and_effects`).
7. **Anti-vacuity:** an always-`none` body has no accepted witness, and an
   accepting body does (`canary_hasAcceptedWitness`); the slice-DST gate's
   specification kills a mutant inside the accepted fibre
   (`canary_dst_accepted_dichotomy`); an impossible specification still
   passes ordinary `PostconditionDichotomy` under `optionLift` while failing
   accepted-fibre dichotomy (`canary_optionLift_vacuity_trap`).
8. **Ratchets:** a two-producer portfolio with stronger effect guarantees
   may replace a single producer and returns the same output
   (`canary_ratchet`), ratchets compose transitively (`canary_ratchet_trans`),
   and a caller's proof carries over (`canary_ratchet_outer`).
9. **Effect-mask order laws:** `maskLe` is definitionally the body of
   upstream `Anneal.Framework.effectMaskLe` (`maskLe_eq_effectMaskLe_body`);
   it is reflexive, transitive, and antisymmetric (`canary_maskLe_refl`,
   `canary_maskLe_trans`, `canary_maskLe_antisymm`), rejects weakening any
   single bit (`canary_maskLe_strict_separation`), and is a partial, not
   total, order (`canary_maskLe_incomparable`).
10. **Compatibility envelope:** the local `OracleGrade.licenses` table matches
   the upper-triangular `Trusted.Framework` table cell by cell for arbitrary
   identifiers (`canary_licenses_table`), unspecified `FnContract` fields
   default to `True` (`canary_fnContract_defaults`), safe functions ignore
   `safetyPre` while both safe and unsafe enforce `behaviorPre`
   (`canary_effectiveSafetyPre`), all nine `DisclosedGap` constructors match
   in order with no extras (`canary_disclosedGap_constructors`), as do the
   `TerminalOutcome`, `ClaimShape`, and `OracleGrade` constructors
   (`canary_closed_constructors`), the `EffectMask`, `FnContract`, and
   `ExecutionModel` field layouts match (`canary_effectMask_fnContract_layout`,
   `canary_executionModel_layout`), type-parameter, constructor-argument,
   and binder names match (`canary_binder_names`), and the four pure-`Prop`
   realizability predicates match their upstream bodies by `rfl`
   (`canary_specRealizability_compat_bodies`).
11. **Outcome gating:** `OutcomeAllowed` forbids undefined behavior under
   every mask (`canary_outcomeAllowed_effects`), each effect bit gates
   exactly its own outcome arm (`canary_outcomeAllowed_bit_arms`), and each
   terminal arm consults strictly its own postcondition with exact `(q, r, m)`
   argument plumbing (`canary_outcomeAllowed_posts`,
   `canary_outcomeAllowed_post_args`).
-/

namespace Anneal.Hybrid.Canaries

open Anneal.Hybrid

/-! ## Portfolios -/

/-- Accepts exactly `y = x`. -/
def eqGate : CertifiedGate Nat Nat Unit (fun _ => True)
    (fun x y => y = x) :=
  { maxWitness := fun _ => 0
    wSize := fun _ => 0
    check := fun x y _ => Nat.beq y x
    sound := fun _ _ _ _ _ h => Nat.eq_of_beq_eq_true h }

/-- Take the first producer that returns any candidate, before checking. -/
def naivePreGateChoice {E Y W : Type} (rs : List (RawOutcome E Y W)) :
    RawOutcome E Y W :=
  List.foldr
    (fun r acc =>
      match r with
      | .candidate y w => .candidate y w
      | _ => acc)
    .trapped rs

/-- A wrong candidate followed by the right one. -/
def twoCandidates : List (RawOutcome Unit Nat Unit) :=
  [.candidate 999 (), .candidate 7 ()]

/-- Choosing before checking loses the valid second candidate, while
`firstAccepted` finds it. -/
theorem naive_precheck_orelse_drops_valid_backup :
    evalGate eqGate 7 (naivePreGateChoice twoCandidates) =
      .error .rejectedByChecker ∧
    firstAccepted eqGate 7 twoCandidates = .ok 7 :=
  ⟨rfl, rfl⟩

/-- Accepts `y = x + 1` with a witness of at most four elements. -/
def succGate : CertifiedGate Nat Nat (List Nat) (fun _ => True)
    (fun x y => y = x + 1) :=
  { maxWitness := fun _ => 4
    wSize := List.length
    check := fun x y _ => Nat.beq y (x + 1)
    sound := fun _ _ _ _ _ h => Nat.eq_of_beq_eq_true h }

/-- An oversized witness, a wrong candidate, and a trap are skipped. -/
theorem canary_portfolio :
    firstAccepted succGate 10
        ([.candidate 11 [0, 0, 0, 0, 0], .candidate 999 [], .trapped,
          .candidate 11 [1, 2]] : List (RawOutcome Unit Nat (List Nat)))
      = .ok 11 ∧
    evalGate (E := Unit) succGate 10 (.candidate 11 [0, 0, 0, 0, 0]) =
      .error (.witnessOversized 5 4) ∧
    firstAccepted succGate 10
        ([.candidate 999 [], .prodErr ()] :
          List (RawOutcome Unit Nat (List Nat))) =
      .error (.producerFailed ()) :=
  ⟨rfl, rfl, rfl⟩

/-- `toOption` preserves accepted outputs and maps rejections to `none`,
lifting gate soundness to the `Option` carrier. -/
theorem canary_toOption_projection :
    toOption (evalGate (E := Unit) eqGate 7 (.candidate 7 ())) = some 7 ∧
    toOption (evalGate (E := Unit) eqGate 7 (.candidate 9 ())) = none ∧
    (∀ raw : RawOutcome Unit Nat Unit, ∀ y,
      toOption (evalGate eqGate 7 raw) = some y → y = 7) :=
  ⟨rfl, rfl, fun raw y h => toOption_evalGate_sound eqGate 7 raw y True.intro h⟩

/-! ## Fallbacks -/

/-- Sound for `x ≤ y` but accepts only `y = x + 1`. -/
def strictSuccGate : CertifiedGate Nat Nat Unit (fun _ => True)
    (fun x y => x ≤ y) :=
  { maxWitness := fun _ => 0
    wSize := fun _ => 0
    check := fun x y _ => Nat.beq y (x + 1)
    sound := fun x _ _ _ _ h => by
      rw [Nat.eq_of_beq_eq_true h]
      exact Nat.le_succ x }

/-- Use the fallback only if the checker accepts it, aborting (`none`)
otherwise. -/
def assertCheckedFallback {X Y W E : Type} {Pre : X → Prop}
    {Spec : X → Y → Prop} (g : CertifiedGate X Y W Pre Spec) (x : X)
    (res : Except (HybridErr E) Y) (fb : X → Y × W) : Option Y :=
  match res with
  | .ok y => some y
  | .error _ =>
    match g.check x (fb x).1 (fb x).2 with
    | true => some (fb x).1
    | false => none

/-- The identity fallback is correct for `x ≤ y`, but the checker does not
accept it, so re-checking aborts. `withFallback` returns it and is sound
for every producer outcome. -/
theorem runtime_checked_fallback_aborts :
    (∀ x : Nat, x ≤ x) ∧
    assertCheckedFallback strictSuccGate 5
        (.error (HybridErr.producerTrapped : HybridErr Unit))
        (fun x => (x, ())) = none ∧
    (∀ raw : RawOutcome Unit Nat Unit,
      5 ≤ withFallback 5 (evalGate strictSuccGate 5 raw) (fun x => x)) :=
  ⟨Nat.le_refl, rfl, fun raw =>
    withFallback_total_sound strictSuccGate 5 raw (fun x => x) True.intro
      (fun x _ => Nat.le_refl x)⟩

/-! ## Hint steps and streams -/

/-- Accepts a next state that is at most `100` and does not decrease. -/
def boundedStepGate : CertifiedGate (Nat × Nat) Nat Unit
    (fun su => su.1 ≤ 100) (fun su s' => s' ≤ 100 ∧ su.1 ≤ s') :=
  { maxWitness := fun _ => 0
    wSize := fun _ => 0
    check := fun su s' _ => Nat.ble s' 100 && Nat.ble su.1 s'
    sound := fun _ _ _ _ _ h =>
      ⟨Nat.le_of_ble_eq_true (Anneal.InitLemmas.bool_and_left h),
        Nat.le_of_ble_eq_true (Anneal.InitLemmas.bool_and_right h)⟩ }

/-- The hint `70` would overshoot, so the state stays at `60`. -/
theorem canary_hint_steps :
    foldHintSteps (Inv := fun s => s ≤ 100) (StepRel := fun s _ s' => s ≤ s')
        boundedStepGate
        (fun s u => (.candidate (s + u) () : RawOutcome Unit Nat Unit))
        (fun su => su.1) 0 [10, 50, 70, 5] = 65 ∧
    ∀ us : List Nat,
      foldHintSteps (Inv := fun s => s ≤ 100)
        (StepRel := fun s _ s' => s ≤ s') boundedStepGate
        (fun s u => (.candidate (s + u) () : RawOutcome Unit Nat Unit))
        (fun su => su.1) 0 us ≤ 100 :=
  ⟨rfl, fun us =>
    foldHintSteps_preserves_inv (Inv := fun s => s ≤ 100)
      (StepRel := fun s _ s' => s ≤ s') boundedStepGate _ (fun su => su.1)
      (fun _ h => ⟨h, Nat.le_refl _⟩) us 0 (Nat.zero_le _)⟩

/-- Accepts a chunk below `100` that does not decrease, and makes it the
new state. -/
def monotoneChunkGate : CertifiedGate (Nat × Nat) (Nat × Nat) Unit
    (fun su => su.1 < 100) (fun _ sc => sc.1 < 100 ∧ sc.2 < 100) :=
  { maxWitness := fun _ => 0
    wSize := fun _ => 0
    check := fun su sc _ =>
      Nat.ble su.1 sc.2 && Nat.ble (sc.2 + 1) 100 && Nat.beq sc.1 sc.2
    sound := fun _ sc _ _ _ h => by
      have hEq := Nat.eq_of_beq_eq_true (Anneal.InitLemmas.bool_and_right h)
      have hLt : sc.2 < 100 := Nat.le_of_ble_eq_true
        (Anneal.InitLemmas.bool_and_right (Anneal.InitLemmas.bool_and_left h))
      refine ⟨?_, hLt⟩
      rw [hEq]
      exact hLt }

/-- `500` is rejected, so `30` is never considered. -/
theorem canary_stream_prefix :
    foldStreamPrefix (AccInv := fun s => s < 100)
        (ValidChunk := fun c => c < 100)
        monotoneChunkGate
        (fun _ u => (.candidate (u, u) () : RawOutcome Unit (Nat × Nat) Unit))
        0 [10, 25, 500, 30] =
      ([10, 25], some .rejectedByChecker) :=
  rfl

/-- Every emitted chunk is valid across arbitrary input streams, and a
rejected head chunk halts immediately without emitting anything. -/
theorem canary_stream_prefix_valid :
    (∀ us : List Nat, ∀ c,
      c ∈ (foldStreamPrefix (AccInv := fun s => s < 100)
        (ValidChunk := fun c => c < 100)
        monotoneChunkGate
        (fun _ u => (.candidate (u, u) () : RawOutcome Unit (Nat × Nat) Unit))
        0 us).1 → c < 100) ∧
    (∀ us : List Nat,
      foldStreamPrefix (AccInv := fun s => s < 100)
        (ValidChunk := fun c => c < 100)
        monotoneChunkGate
        (fun _ u => (.candidate (u, u) () : RawOutcome Unit (Nat × Nat) Unit))
        0 (500 :: us) = ([], some .rejectedByChecker)) :=
  ⟨fun us c h =>
    foldStreamPrefix_all_emitted_valid (AccInv := fun s => s < 100)
      (ValidChunk := fun c => c < 100) monotoneChunkGate _ us 0
      (Nat.zero_lt_succ 99) c h,
    fun us =>
      foldStreamPrefix_halts (AccInv := fun s => s < 100)
        (ValidChunk := fun c => c < 100) monotoneChunkGate _ 0 500 us
        .rejectedByChecker rfl⟩

/-! ## Certificate cuts -/

/-- `2 * i + 1 ≤ 2 * n → i < n` from the existing Farkas certificate,
through the gate. -/
theorem canary_natCut_parity (i n : Nat) (h : 2 * i + 1 ≤ 2 * n) : i < n :=
  certGateCut_sound (natCutGate 8) (x := Anneal.LinearArith.parityStrideGoal)
    (y := ()) (w := Anneal.LinearArith.parityStrideFarkasCert) True.intro
    (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl) [i, n] h

/-- The four-step certificate is rejected under a two-step bound and
accepted under an eight-step bound; a truncated certificate is rejected by
the checker. -/
theorem canary_natCut_bounds :
    evalGate (E := Unit) (natCutGate 2) Anneal.LinearArith.parityStrideGoal
        (.candidate () Anneal.LinearArith.parityStrideCert) =
      .error (.witnessOversized 4 2) ∧
    evalGate (E := Unit) (natCutGate 8) Anneal.LinearArith.parityStrideGoal
        (.candidate () Anneal.LinearArith.parityStrideCert) = .ok () ∧
    evalGate (E := Unit) (natCutGate 8) Anneal.LinearArith.parityStrideGoal
        (.candidate () [.hyp 0]) = .error .rejectedByChecker :=
  ⟨rfl, rfl, rfl⟩

/-- An LRAT refutation checked through the gate. -/
theorem canary_rup_unsat :
    Anneal.BitTrieLrat.UnsatCnf Anneal.BitTrieLrat.sampleUnsatCnf :=
  certGateCut_sound (rupGate 6 8) (y := ())
    (w := Anneal.BitTrieLrat.sampleUnsatSteps) True.intro
    (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl)

/-- A hint chain that ends without a conflict is rejected. -/
theorem canary_rup_forged_rejected :
    evalGate (E := Unit) (rupGate 6 8) Anneal.BitTrieLrat.sampleUnsatCnf
        (.candidate ()
          [.addRup 5 [Anneal.BitTrieLrat.mkLit 3 true] [0]]) =
      .error .rejectedByChecker :=
  rfl

/-- The three-step RUP refutation is rejected under a two-step bound and
accepted under an eight-step bound; a forged step list is rejected. -/
theorem canary_rup_bounds :
    evalGate (E := Unit) (rupGate 6 2) Anneal.BitTrieLrat.sampleUnsatCnf
        (.candidate () Anneal.BitTrieLrat.sampleUnsatSteps) =
      .error (.witnessOversized 3 2) ∧
    evalGate (E := Unit) (rupGate 6 8) Anneal.BitTrieLrat.sampleUnsatCnf
        (.candidate () Anneal.BitTrieLrat.sampleUnsatSteps) = .ok () ∧
    evalGate (E := Unit) (rupGate 6 8) Anneal.BitTrieLrat.sampleUnsatCnf
        (.candidate ()
          [.addRup 5 [Anneal.BitTrieLrat.mkLit 3 true] [0]]) =
      .error .rejectedByChecker :=
  ⟨rfl, rfl, rfl⟩

/-! ## `zerocopy` slice-DST casts -/

/-- The inputs of `DstLayout::validate_cast_and_convert_metadata` for a
slice DST: the address and length of the source bytes, the object's pointer
alignment (`DstLayout::align`), the trailing-slice layout (`sizeBase`,
`phase`, `elemSize`, and the size-rounding alignment `sizeAlign`), and the
cast direction. -/
structure DstCastInput where
  addr : Nat
  bytesLen : Nat
  align : Nat
  sizeBase : Nat
  phase : Nat
  elemSize : Nat
  sizeAlign : Nat
  isPrefix : Bool

/-- `v` rounded up to a multiple of `a` (for `0 < a`). -/
def roundUpNat (v a : Nat) : Nat :=
  match Nat.beq (Nat.mod v a) 0 with
  | true => v
  | false => v + (a - Nat.mod v a)

/-- Size of the slice DST with `elems` trailing elements. -/
def dstObjectSize (x : DstCastInput) (elems : Nat) : Nat :=
  x.sizeBase + roundUpNat (x.phase + elems * x.elemSize) x.sizeAlign

/-- `usize::MAX` on 64-bit targets. -/
def usizeMax : Nat := 18446744073709551615

/-- Where the source bytes are split for an object of `selfBytes` bytes. -/
def dstSplitAt (x : DstCastInput) (selfBytes : Nat) : Nat :=
  match x.isPrefix with
  | true => selfBytes
  | false => x.bytesLen - selfBytes

/-- Address of the cast object. -/
def dstTargetAddr (x : DstCastInput) (splitAt : Nat) : Nat :=
  match x.isPrefix with
  | true => x.addr
  | false => x.addr + splitAt

/-- `(elems, splitAt)` is a valid result: the object fits, the split point
matches it, the object is aligned, and one more element would not fit. -/
def ValidDstCast (x : DstCastInput) (out : Nat × Nat) : Prop :=
  0 < x.align ∧ 0 < x.sizeAlign ∧ 0 < x.elemSize ∧
  x.addr + x.bytesLen ≤ usizeMax ∧
  dstObjectSize x out.1 ≤ x.bytesLen ∧
  out.2 = dstSplitAt x (dstObjectSize x out.1) ∧
  Nat.mod (dstTargetAddr x out.2) x.align = 0 ∧
  x.bytesLen < dstObjectSize x (out.1 + 1)

/-- Boolean check of `ValidDstCast`, recomputing every size from the
layout rather than trusting the candidate. -/
def checkDstCast (x : DstCastInput) (out : Nat × Nat) : Bool :=
  Nat.ble 1 x.align && Nat.ble 1 x.sizeAlign && Nat.ble 1 x.elemSize &&
    Nat.ble (x.addr + x.bytesLen) usizeMax &&
    Nat.ble (dstObjectSize x out.1) x.bytesLen &&
    Nat.beq out.2 (dstSplitAt x (dstObjectSize x out.1)) &&
    Nat.beq (Nat.mod (dstTargetAddr x out.2) x.align) 0 &&
    Nat.ble (x.bytesLen + 1) (dstObjectSize x (out.1 + 1))

theorem checkDstCast_sound (x : DstCastInput) (out : Nat × Nat)
    (h : checkDstCast x out = true) : ValidDstCast x out := by
  have h6 := Anneal.InitLemmas.bool_and_right h
  have r5 := Anneal.InitLemmas.bool_and_left h
  have h5 := Anneal.InitLemmas.bool_and_right r5
  have r4 := Anneal.InitLemmas.bool_and_left r5
  have h4 := Anneal.InitLemmas.bool_and_right r4
  have r3 := Anneal.InitLemmas.bool_and_left r4
  have h3 := Anneal.InitLemmas.bool_and_right r3
  have r2 := Anneal.InitLemmas.bool_and_left r3
  have h2 := Anneal.InitLemmas.bool_and_right r2
  have r1 := Anneal.InitLemmas.bool_and_left r2
  have h1 := Anneal.InitLemmas.bool_and_right r1
  have r0 := Anneal.InitLemmas.bool_and_left r1
  have hS := Anneal.InitLemmas.bool_and_right r0
  have h0 := Anneal.InitLemmas.bool_and_left r0
  exact ⟨Nat.le_of_ble_eq_true h0, Nat.le_of_ble_eq_true hS,
    Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2,
    Nat.le_of_ble_eq_true h3, Nat.eq_of_beq_eq_true h4,
    Nat.eq_of_beq_eq_true h5, Nat.le_of_ble_eq_true h6⟩

/-- Witness-free relational gate for slice-DST cast metadata. -/
def sliceDstCastGate :
    CertifiedGate DstCastInput (Nat × Nat) Unit (fun _ => True)
      ValidDstCast :=
  { maxWitness := fun _ => 0
    wSize := fun _ => 0
    check := fun x out _ => checkDstCast x out
    sound := fun x out _ _ _ h => checkDstCast_sound x out h }

/-- 26 bytes at a 4-aligned address, a 4-byte header, 6-byte elements,
alignment 4, prefix cast. Three elements need 24 bytes and four need 28. -/
def castIn : DstCastInput :=
  { addr := 4096, bytesLen := 26, align := 4, sizeBase := 4, phase := 0,
    elemSize := 6, sizeAlign := 4, isPrefix := true }

/-- The same input as a suffix cast, which starts at `4098`. -/
def castInSuffix : DstCastInput :=
  { castIn with isPrefix := false }

/-- The maximal candidate is accepted after a trap and a sub-maximal
candidate, and it is valid. -/
theorem canary_dst_portfolio :
    firstAccepted sliceDstCastGate castIn
        ([.trapped, .candidate (2, 16) (), .candidate (3, 24) ()] :
          List (RawOutcome Unit (Nat × Nat) Unit)) = .ok (3, 24) ∧
    ValidDstCast castIn (3, 24) :=
  ⟨rfl, evalGate_sound (E := Unit) sliceDstCastGate castIn
    (.candidate (3, 24) ()) (3, 24) True.intro rfl⟩

/-- Two elements fit, but so do three, so `(2, 16)` is not maximal. -/
theorem canary_dst_submaximal_invalid : ¬ ValidDstCast castIn (2, 16) :=
  fun h => absurd h.2.2.2.2.2.2.2 (by decide)

/-- The sub-maximal candidate and the misaligned suffix cast are rejected.
-/
theorem canary_dst_rejections :
    evalGate (E := Unit) sliceDstCastGate castIn (.candidate (2, 16) ()) =
      .error .rejectedByChecker ∧
    evalGate (E := Unit) sliceDstCastGate castInSuffix
        (.candidate (3, 2) ()) = .error .rejectedByChecker :=
  ⟨rfl, rfl⟩

/-- A `repr(packed(2))` wrapper: pointer alignment 2, size alignment 4. At
address 2, two 2-byte elements round up to 4 bytes and fit in 6; three
round up to 8 and do not. With a single alignment of 4 the address would be
rejected. -/
def castInPacked : DstCastInput :=
  { addr := 2, bytesLen := 6, align := 2, sizeBase := 0, phase := 0,
    elemSize := 2, sizeAlign := 4, isPrefix := true }

theorem canary_dst_packed :
    evalGate (E := Unit) sliceDstCastGate castInPacked
        (.candidate (2, 4) ()) = .ok (2, 4) ∧
    evalGate (E := Unit) sliceDstCastGate castInPacked
        (.candidate (3, 6) ()) = .error .rejectedByChecker ∧
    evalGate (E := Unit) sliceDstCastGate
        { castInPacked with align := 4 } (.candidate (2, 4) ()) =
      .error .rejectedByChecker :=
  ⟨rfl, rfl, rfl⟩

/-- `ValidDstCast` distinguishes two accepted (`some`) outputs. -/
theorem canary_dst_accepted_dichotomy :
    DichotomyModuloObservation (fun _ o => Option.isSome o)
      (fun _ => True) (optionLift ValidDstCast) :=
  optionLift_acceptedDichotomy castIn True.intro (3, 24) (2, 16)
    canary_dst_portfolio.2 canary_dst_submaximal_invalid

/-! ## In-process producers -/

/-- Only freedom from undefined behavior; nothing about memory. -/
def wfOnlyProducerContract {Mem X Ret : Type}
    (sPre bPre : Mem × X → Prop) (eff : EffectMask) :
    FnContract (Mem × X) Ret Mem :=
  { safetyPre := sPre, behaviorPre := bPre, effects := eff }

/-- All three effect guarantees. -/
def totalMask : EffectMask :=
  { terminates := true, noUnwind := true, noAbort := true }

/-- Returns a wrong candidate after zeroing caller memory. -/
def clobberProducer (q : Nat × Nat)
    (o : RunOutcome (Nat × Unit) Nat) : Prop :=
  o = .terminal (.returned (q.2 + 999, ()) 0)

/-- Returns the same wrong candidate with caller memory unchanged. -/
def keepProducer (q : Nat × Nat)
    (o : RunOutcome (Nat × Unit) Nat) : Prop :=
  o = .terminal (.returned (q.2 + 999, ()) q.1)

/-- Output must be `x + mem`, with memory unchanged. -/
def sumPost (q : Nat × Nat) (y : Nat) (m' : Nat) : Prop :=
  y = q.2 + q.1 ∧ m' = q.1

def sumCheck (q : Nat × Nat) (y : Nat) (_ : Unit) : Bool :=
  Nat.beq y (q.2 + q.1)

def keepMem (q : Nat × Nat) (_ : Nat) : Nat := q.1

def sumFb (q : Nat × Nat) : Nat × Nat := (q.2 + q.1, q.1)

theorem sumCheck_sound (q : Nat × Nat) (y : Nat) (w : Unit)
    (h : sumCheck q y w = true) : sumPost q y (keepMem q y) :=
  ⟨Nat.eq_of_beq_eq_true h, rfl⟩

theorem sumFb_sound (q : Nat × Nat) : sumPost q (sumFb q).1 (sumFb q).2 :=
  ⟨rfl, rfl⟩

/-- A producer free of undefined behavior that zeroes caller memory makes
the checker and fallback read the wrong memory: on `(mem, x) = (10, 5)`
the composition returns `5` with memory `0`. -/
theorem rung15_without_callerMemPreserved_unsound :
    ContractHolds
        (wfOnlyProducerContract (fun _ => True) (fun q => q.1 = 10) totalMask)
        false clobberProducer ∧
    ¬ ContractHolds
        (rung15OuterContract (fun _ => True) (fun q => q.1 = 10) sumPost
          totalMask)
        false (rung15Run clobberProducer sumCheck keepMem sumFb) := by
  refine ⟨⟨fun _ _ h => (by cases h), fun _ _ o h => ?_⟩, fun hC => ?_⟩
  · have h' : o = .terminal (.returned (_ + 999, ()) 0) := h
    rw [h']
    exact True.intro
  · have hBad : (5 = 5 + 10 ∧ (0 : Nat) = 10) :=
      hC.2 (10, 5) ⟨fun _ => True.intro, rfl⟩ (.terminal (.returned 5 0))
        ⟨_, rfl, rfl⟩
    exact absurd hBad.2 (by decide)

/-- The same wrong candidate from a memory-preserving producer is
harmless. -/
theorem canary_rung15_preserving :
    ContractHolds
      (rung15OuterContract (fun _ => True) (fun q => q.1 = 10) sumPost
        totalMask)
      false (rung15Run keepProducer sumCheck keepMem sumFb) := by
  refine rung15_with_callerMemPreserved_sound _ _ sumPost totalMask totalMask
    false keepProducer sumCheck keepMem sumFb (maskLe_refl _)
    ⟨fun _ _ h => (by cases h), fun q _ o h => ?_⟩
    (fun q y w _ h => sumCheck_sound q y w h) (fun q _ => sumFb_sound q)
  have h' : o = .terminal (.returned (q.2 + 999, ()) q.1) := h
  rw [h']
  exact rfl

/-- An unsafe producer that preserves memory on return or unwind when
`q.1 = 10`, and faults with `.faultUB` outside its safety precondition. -/
def unsafeUnwindProducer (q : Nat × Nat)
    (o : RunOutcome (Nat × Unit) Nat) : Prop :=
  (q.1 = 10 ∧
    (o = .terminal (.returned (q.2 + 999, ()) q.1) ∨
      o = .terminal (.unwound q.1))) ∨
  (q.1 ≠ 10 ∧ o = .faultUB)

/-- Exercises `rung15_with_callerMemPreserved_sound` under `isUnsafe = true`,
a nontrivial `safetyPre`, and an unwinding producer. The statement itself
pins the strict effect weakening (`fEff` guarantees `noAbort`, `outerEff`
does not, and `maskLe` holds in one direction only) and the producer's own
`fEff` contract, so the weakening cannot silently collapse to equal masks.
Both composed paths are inhabited on `(mem, x) = (10, 5)`: the
wrong candidate falls back to `15` with memory `10`, and the unwind
propagates. The same `.faultUB`-capable producer fails a safe
(`isUnsafe = false`) contract even when `safetyPre := False`. -/
theorem canary_rung15_unsafe_and_effects :
    let fEff : EffectMask :=
      { terminates := true, noUnwind := false, noAbort := true }
    let outerEff : EffectMask :=
      { terminates := true, noUnwind := false, noAbort := false }
    let run := rung15Run unsafeUnwindProducer sumCheck keepMem sumFb
    maskLe outerEff fEff ∧ ¬ maskLe fEff outerEff ∧
    ContractHolds
        (rung15ProducerContract (Ret := Nat × Unit) (fun q => q.1 = 10)
          (fun _ => True) fEff)
        true unsafeUnwindProducer ∧
    ContractHolds
        (rung15OuterContract (fun q => q.1 = 10) (fun _ => True) sumPost
          outerEff)
        true run ∧
    run (10, 5) (.terminal (.returned 15 10)) ∧
    run (10, 5) (.terminal (.unwound 10)) ∧
    ¬ ContractHolds
        (rung15OuterContract (fun _ => False) (fun _ => True) sumPost
          outerEff)
        false run := by
  intro fEff outerEff run
  have hMask : maskLe outerEff fEff :=
    ⟨fun _ => rfl, fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩
  have hF : ContractHolds
      (rung15ProducerContract (Ret := Nat × Unit) (fun q => q.1 = 10)
        (fun _ => True) fEff)
      true unsafeUnwindProducer := by
    refine ⟨?_, ?_⟩
    · intro q hS hUb
      have h10 : q.1 = 10 := hS rfl
      cases hUb with
      | inl hOk =>
        cases hOk.2 with
        | inl hR => cases hR
        | inr hU => cases hU
      | inr hBad => exact hBad.1 h10
    · intro q hB o ho
      have h10 : q.1 = 10 := hB.1 rfl
      cases ho with
      | inr hBad => exact absurd h10 hBad.1
      | inl hOk =>
        cases hOk.2 with
        | inl hR =>
          rw [hR]
          exact rfl
        | inr hU =>
          rw [hU]
          exact ⟨rfl, rfl⟩
  refine ⟨hMask, fun h => Bool.noConfusion (h.2.2 rfl), hF,
    rung15_with_callerMemPreserved_sound (fun q => q.1 = 10) (fun _ => True)
      sumPost fEff outerEff true unsafeUnwindProducer sumCheck keepMem sumFb
      hMask hF (fun q y w _ h => sumCheck_sound q y w h)
      (fun q _ => sumFb_sound q),
    ⟨.terminal (.returned (5 + 999, ()) 10), Or.inl ⟨rfl, Or.inl rfl⟩, rfl⟩,
    ⟨.terminal (.unwound 10), Or.inl ⟨rfl, Or.inr rfl⟩, rfl⟩, ?_⟩
  intro hSafe
  exact hSafe.1 (0, 0) (fun h => Bool.noConfusion h)
    ⟨.faultUB, Or.inr ⟨by decide, rfl⟩, rfl⟩

/-! ## Anti-vacuity -/

/-- A single-body model whose body returns `impl q`. -/
def toyModel (impl : Nat → Option Nat) :
    ExecutionModel Unit Unit Unit Nat (Option Nat) Unit :=
  { profileId := "toy"
    oracleGrade := .unbridged "toy"
    programAdmitted := fun _ => true
    bodyAdmitted := fun _ _ => true
    isPartialScope := fun _ => false
    bodyAt := fun _ _ => some ()
    uniqueIdentities := fun _ => true
    bodyIdentity := fun _ => "toy"
    bodyIsUnsafe := fun _ => false
    bodyIsExternal := fun _ => false
    bodyMatchesSig := fun _ _ => true
    modelGaps := []
    requiredGaps := fun _ => []
    claimShapeGaps := fun _ => []
    entryDom := fun _ _ => True
    returnValid := fun _ _ _ => True
    memValid := fun _ => True
    execForBody := fun p _ => p
    wellFormed := fun _ _ => True
    produces := fun _ q o => o = .returned (impl q) ()
    diverges := fun _ _ => False
    faultsUB := fun _ _ => False }

def toyContract : FnContract Nat (Option Nat) Unit :=
  { effects := totalMask }

/-- An accepting body has an accepted witness; an always-`none` body, which
meets every `optionLift` specification, has none. -/
theorem canary_hasAcceptedWitness :
    HasAcceptedWitness (toyModel some) () 0 () toyContract Option.isSome ∧
    ¬ HasAcceptedWitness (toyModel (fun _ => none)) () 0 () toyContract
      Option.isSome := by
  refine ⟨⟨rfl, 0, some 0, (), True.intro,
    ⟨fun h => (by cases h), True.intro⟩, rfl, rfl⟩, ?_⟩
  refine not_hasAcceptedWitness_of_alwaysRejects _ _ _ _ _ _ ?_
  intro q r m h
  have h' : TerminalOutcome.returned r m = .returned none () := h
  injection h' with hr
  rw [hr]
  rfl

/-- The witness is tied to the body stored at `defId`: a model with no body
there has no accepted witness, even though its execution accepts. -/
theorem canary_hasAcceptedWitness_requires_bodyAt :
    ¬ HasAcceptedWitness { toyModel some with bodyAt := fun _ _ => none } ()
      0 () toyContract Option.isSome :=
  fun h => by
    have hNone : (none : Option Unit) = some () := h.bodyAt_eq
    cases hNone

/-- Anti-vacuity trap for `optionLift`: an impossible specification
(`fun _ _ => False`) still satisfies ordinary `PostconditionDichotomy` under
`optionLift` and admits the always-`none` implementation, yet fails
accepted-fibre dichotomy (`DichotomyModuloObservation` on `Option.isSome`). -/
theorem canary_optionLift_vacuity_trap :
    PostconditionDichotomy (fun (_ : Nat) => True)
        (optionLift (fun (_ : Nat) (_ : Nat) => False)) ∧
    (∀ x : Nat, optionLift (fun (_ : Nat) (_ : Nat) => False) x none) ∧
    ¬ DichotomyModuloObservation (fun _ o => Option.isSome o)
        (fun (_ : Nat) => True)
        (optionLift (fun (_ : Nat) (_ : Nat) => False)) :=
  let hPass :=
    optionLift_dichotomy_while_none_passes
      (Pre := fun (_ : Nat) => True)
      (Spec := fun (_ : Nat) (_ : Nat) => False)
      0 True.intro 0 (fun h => h)
  ⟨hPass.1, hPass.2, fun hDich =>
    let ⟨_, _, ⟨_, hOk⟩, _⟩ := optionLift_acceptedDichotomy_iff.1 hDich
    hOk⟩

/-! ## Ratchets -/

/-- No effect guarantees. -/
def anyExitMask : EffectMask :=
  { terminates := false, noUnwind := false, noAbort := false }

/-- One producer that proposes `x`. -/
def singleProducer : HybridComponent Nat Unit Nat :=
  { mask := anyExitMask
    run := fun x => evalGate eqGate x (.candidate x ()) }

/-- A portfolio whose first producer is wrong and whose second proposes `x`,
with stronger effect guarantees. -/
def portfolio : HybridComponent Nat Unit Nat :=
  { mask := totalMask
    run := fun x =>
      firstAccepted eqGate x [.candidate (x + 1) (), .candidate x ()] }

theorem portfolio_sound :
    ResultSound (fun _ => True) (fun x y => y = x) portfolio.run :=
  fun x _ y h =>
    firstAccepted_sound eqGate x [.candidate (x + 1) (), .candidate x ()] y
      True.intro h

theorem singleProducer_sound :
    ResultSound (fun _ => True) (fun x y => y = x) singleProducer.run :=
  fun x _ y h => evalGate_sound eqGate x (.candidate x ()) y True.intro h

theorem evalGate_eqGate_self (x : Nat) :
    evalGate (E := Unit) eqGate x (.candidate x ()) = .ok x :=
  (evalGate_candidate_ok_iff eqGate x x () x).2
    ⟨rfl, Nat.le_refl 0, Nat.beq_refl x⟩

/-- The portfolio may replace the single producer, and because the
specification determines the output, it returns the same output. -/
theorem canary_ratchet :
    HybridRefines (fun _ => True) (fun x y => y = x) singleProducer
        portfolio ∧
    ∀ x, portfolio.run x = .ok x := by
  have hRef : HybridRefines (fun _ => True) (fun x y => y = x)
      singleProducer portfolio :=
    ⟨⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion h,
        fun h => Bool.noConfusion h⟩,
      portfolio_sound,
      fun x _ _ _ => (firstAccepted_ok_iff_exists eqGate x _).2
        ⟨.candidate x (), List.Mem.tail _ (List.Mem.head _), x,
          evalGate_eqGate_self x⟩⟩
  exact ⟨hRef, fun x =>
    hybridRefines_pointwise_of_deterministic
      (fun _ _ _ _ h1 h2 => h1.trans h2.symm) singleProducer_sound hRef x
      True.intro x (evalGate_eqGate_self x)⟩

/-- A caller that doubles the component's output. -/
def doubleOuter (f : Nat → Except (HybridErr Unit) Nat) (x : Nat) :
    Except Unit Nat :=
  match f x with
  | .ok y => .ok (y + y)
  | .error _ => .error ()

/-- The caller's proof for every sound component carries over to the
portfolio. -/
theorem canary_ratchet_outer (x z : Nat)
    (h : doubleOuter portfolio.run x = .ok z) : z = x + x := by
  have hOuter : ∀ f, ResultSound (fun _ => True) (fun x y => y = x) f →
      ∀ x, True → ∀ z, doubleOuter f x = .ok z → z = x + x := by
    intro f hf x hx z h
    revert h
    dsimp only [doubleOuter]
    cases hfx : f x with
    | error _ => intro h; cases h
    | ok y =>
      intro h
      injection h with h
      rw [← h, hf x hx y hfx]
  exact (ratchet_result_preserves_outer_safety_and_availability doubleOuter
    (fun x z => z = x + x) hOuter canary_ratchet.1).1 x True.intro z h

/-- Intermediate portfolio guaranteeing termination and no-unwind, used to
exercise transitive multi-step ratchets. -/
def midPortfolio : HybridComponent Nat Unit Nat :=
  { mask := { terminates := true, noUnwind := true, noAbort := false }
    run := fun x => firstAccepted eqGate x [.trapped, .candidate x ()] }

theorem midPortfolio_sound :
    ResultSound (fun _ => True) (fun x y => y = x) midPortfolio.run :=
  fun x _ y h =>
    firstAccepted_sound eqGate x [.trapped, .candidate x ()] y True.intro h

/-- Two-step transitive ratchet (`singleProducer -> midPortfolio -> portfolio`)
composed via `hybridRefines_trans`. -/
theorem canary_ratchet_trans :
    HybridRefines (fun _ => True) (fun x y => y = x) singleProducer
        midPortfolio ∧
    HybridRefines (fun _ => True) (fun x y => y = x) midPortfolio portfolio ∧
    HybridRefines (fun _ => True) (fun x y => y = x) singleProducer
        portfolio := by
  have h12 : HybridRefines (fun _ => True) (fun x y => y = x)
      singleProducer midPortfolio :=
    ⟨⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion h,
        fun h => Bool.noConfusion h⟩,
      midPortfolio_sound,
      fun x _ _ _ =>
        (firstAccepted_ok_iff_exists eqGate x [.trapped, .candidate x ()]).2
          ⟨.candidate x (), List.Mem.tail _ (List.Mem.head _), x,
            evalGate_eqGate_self x⟩⟩
  have h23 : HybridRefines (fun _ => True) (fun x y => y = x)
      midPortfolio portfolio :=
    ⟨⟨fun _ => rfl, fun _ => rfl, fun h => Bool.noConfusion h⟩,
      portfolio_sound,
      fun x _ _ _ =>
        (firstAccepted_ok_iff_exists eqGate x
          [.candidate (x + 1) (), .candidate x ()]).2
          ⟨.candidate x (), List.Mem.tail _ (List.Mem.head _), x,
            evalGate_eqGate_self x⟩⟩
  exact ⟨h12, h23, hybridRefines_trans h12 h23⟩

/-! ## Integer cuts -/

/-- `(-2) * x - y ≤ 5 → -3 ≤ -y → -4 ≤ x` through the integer-cut gate. -/
theorem canary_intCut (x y : Int)
    (h1 : Int.sub (Int.mul (Int.negOfNat 2) x) y ≤ Int.ofNat 5)
    (h2 : Int.negOfNat 3 ≤ Int.neg y) : Int.negOfNat 4 ≤ x :=
  certGateCut_sound (intCutGate 8) (x := Anneal.LinearArith.intSubNegMulGoal)
    (y := ()) (w := Anneal.LinearArith.intSubNegMulCert) True.intro
    (Anneal.Framework.StepWp.BoolCertCut.seal _ _ rfl) [x, y] h1 h2

/-- The five-step integer-cut certificate is rejected under a two-step bound
and accepted under an eight-step bound; a truncated certificate is rejected
by the checker. -/
theorem canary_intCut_bounds :
    evalGate (E := Unit) (intCutGate 2) Anneal.LinearArith.intSubNegMulGoal
        (.candidate () Anneal.LinearArith.intSubNegMulCert) =
      .error (.witnessOversized 5 2) ∧
    evalGate (E := Unit) (intCutGate 8) Anneal.LinearArith.intSubNegMulGoal
        (.candidate () Anneal.LinearArith.intSubNegMulCert) = .ok () ∧
    evalGate (E := Unit) (intCutGate 8) Anneal.LinearArith.intSubNegMulGoal
        (.candidate () [.hyp 0]) = .error .rejectedByChecker :=
  ⟨rfl, rfl, rfl⟩

/-! ## Effect-mask order laws -/

/-- Effect mask guaranteeing only termination. -/
def termOnlyMask : EffectMask :=
  { terminates := true, noUnwind := false, noAbort := false }

/-- Intermediate effect mask guaranteeing termination and no-unwind, while
still permitting aborts. -/
def termNoUnwindMask : EffectMask :=
  { terminates := true, noUnwind := true, noAbort := false }

/-- Reflexivity of `maskLe` across arbitrary masks. -/
theorem canary_maskLe_refl (m : EffectMask) : maskLe m m :=
  maskLe_refl m

/-- Non-vacuous transitivity of `maskLe` along the strict three-step chain
`termOnlyMask < termNoUnwindMask < totalMask` (carrying `terminates = true`
across both steps), plus general transitivity. -/
theorem canary_maskLe_trans :
    maskLe termOnlyMask termNoUnwindMask ∧
    maskLe termNoUnwindMask totalMask ∧
    maskLe termOnlyMask totalMask ∧
    ¬ maskLe termNoUnwindMask termOnlyMask ∧
    ¬ maskLe totalMask termNoUnwindMask ∧
    (∀ m1 m2 m3 : EffectMask, maskLe m1 m2 → maskLe m2 m3 → maskLe m1 m3) := by
  have h1 : maskLe termOnlyMask termNoUnwindMask :=
    ⟨fun _ => rfl, fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩
  have h2 : maskLe termNoUnwindMask totalMask :=
    ⟨fun _ => rfl, fun _ => rfl, fun h => Bool.noConfusion h⟩
  exact ⟨h1, h2, maskLe_trans h1 h2,
    fun h => Bool.noConfusion (h.2.1 rfl),
    fun h => Bool.noConfusion (h.2.2 rfl),
    fun _ _ _ => maskLe_trans⟩

/-- Strict separation of `maskLe`: weakening any single guaranteed effect bit
(`terminates`, `noUnwind`, or `noAbort`) is rejected. -/
theorem canary_maskLe_strict_separation :
    ¬ maskLe totalMask anyExitMask ∧
    ¬ maskLe totalMask { totalMask with terminates := false } ∧
    ¬ maskLe totalMask { totalMask with noUnwind := false } ∧
    ¬ maskLe totalMask { totalMask with noAbort := false } :=
  ⟨fun h => Bool.noConfusion (h.1 rfl),
    fun h => Bool.noConfusion (h.1 rfl),
    fun h => Bool.noConfusion (h.2.1 rfl),
    fun h => Bool.noConfusion (h.2.2 rfl)⟩

/-- `maskLe` is, by `rfl`, the body of upstream `Anneal.Framework.effectMaskLe`
(which is absent here), so a later import swap cannot change its meaning. -/
theorem maskLe_eq_effectMaskLe_body :
    maskLe = fun m1 m2 =>
      (m1.terminates = true → m2.terminates = true) ∧
      (m1.noUnwind = true → m2.noUnwind = true) ∧
      (m1.noAbort = true → m2.noAbort = true) :=
  rfl

/-- Two Booleans that imply each other's truth are equal. -/
private theorem bool_eq_of_imp_true :
    ∀ {a b : Bool}, (a = true → b = true) → (b = true → a = true) → a = b
  | false, false, _, _ => rfl
  | false, true, _, h => Bool.noConfusion (h rfl)
  | true, false, h, _ => Bool.noConfusion (h rfl)
  | true, true, _, _ => rfl

/-- Antisymmetry of `maskLe`: mutually bounded masks are equal. -/
theorem canary_maskLe_antisymm :
    ∀ m1 m2 : EffectMask, maskLe m1 m2 → maskLe m2 m1 → m1 = m2
  | ⟨_, _, _⟩, ⟨_, _, _⟩, h12, h21 =>
    congr
      (congr
        (congrArg EffectMask.mk (bool_eq_of_imp_true h12.1 h21.1))
        (bool_eq_of_imp_true h12.2.1 h21.2.1))
      (bool_eq_of_imp_true h12.2.2 h21.2.2)

/-- A mask guaranteeing only `noAbort`. -/
def noAbortOnlyMask : EffectMask :=
  { terminates := false, noUnwind := false, noAbort := true }

/-- `maskLe` is not total: guaranteeing termination and no unwinding is
incomparable with guaranteeing only no abort. -/
theorem canary_maskLe_incomparable :
    ¬ maskLe termNoUnwindMask noAbortOnlyMask ∧
    ¬ maskLe noAbortOnlyMask termNoUnwindMask :=
  ⟨fun h => Bool.noConfusion (h.1 rfl), fun h => Bool.noConfusion (h.2.2 rfl)⟩

/-! ## Compatibility envelope -/

/-- Every cell of the local `OracleGrade.licenses` table for arbitrary
profile/oracle identifiers, matching `Trusted.Framework.OracleGrade.licenses`:
`forwardSim` never licenses `termination` or `existsWitness`, and no grade
licenses `generalHyper`. -/
theorem canary_licenses_table (pid oid : String) :
    (OracleGrade.unbridged pid).licenses .existsWitness = false ∧
    (OracleGrade.unbridged pid).licenses .forallSafety = true ∧
    (OracleGrade.unbridged pid).licenses .generalHyper = false ∧
    (OracleGrade.unbridged pid).licenses .subsetHyper = false ∧
    (OracleGrade.unbridged pid).licenses .termination = true ∧
    (OracleGrade.forwardSim oid).licenses .existsWitness = false ∧
    (OracleGrade.forwardSim oid).licenses .forallSafety = true ∧
    (OracleGrade.forwardSim oid).licenses .generalHyper = false ∧
    (OracleGrade.forwardSim oid).licenses .subsetHyper = true ∧
    (OracleGrade.forwardSim oid).licenses .termination = false ∧
    (OracleGrade.biFaultEquiv oid).licenses .existsWitness = true ∧
    (OracleGrade.biFaultEquiv oid).licenses .forallSafety = true ∧
    (OracleGrade.biFaultEquiv oid).licenses .generalHyper = false ∧
    (OracleGrade.biFaultEquiv oid).licenses .subsetHyper = true ∧
    (OracleGrade.biFaultEquiv oid).licenses .termination = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl⟩

/-- Unspecified `FnContract` fields default to `True`, while `effects` has no
default and must be stated. -/
theorem canary_fnContract_defaults :
    let c : FnContract Unit Unit Unit := { effects := anyExitMask }
    c.safetyPre = (fun _ => True) ∧ c.behaviorPre = (fun _ => True) ∧
    c.postReturn = (fun _ _ _ => True) ∧ c.postUnwind = (fun _ _ => True) ∧
    c.postAbort = (fun _ _ => True) ∧ c.effects = anyExitMask :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Safe functions ignore `safetyPre` (even `False`), unsafe functions require
it, and `effectiveBehaviorPre` genuinely conjoins `behaviorPre` for both safe
and unsafe functions. -/
theorem canary_effectiveSafetyPre :
    let cSafe : FnContract Unit Unit Unit :=
      { safetyPre := fun _ => False, effects := anyExitMask }
    let cBeh : FnContract Unit Unit Unit :=
      { behaviorPre := fun _ => False, effects := anyExitMask }
    cSafe.effectiveSafetyPre false () ∧ ¬ cSafe.effectiveSafetyPre true () ∧
    cSafe.effectiveBehaviorPre false () ∧ ¬ cSafe.effectiveBehaviorPre true () ∧
    cBeh.effectiveSafetyPre false () ∧ cBeh.effectiveSafetyPre true () ∧
    ¬ cBeh.effectiveBehaviorPre false () ∧
    ¬ cBeh.effectiveBehaviorPre true () :=
  ⟨fun h => Bool.noConfusion h, fun h => h rfl,
    ⟨fun h => Bool.noConfusion h, True.intro⟩, fun h => h.1 rfl,
    fun _ => True.intro, fun _ => True.intro,
    fun h => h.2, fun h => h.2⟩

/-- Positive-polarity effect gating in `OutcomeAllowed`: `totalMask` forbids
unwinding, aborting, divergence, and UB while permitting normal returns;
`anyExitMask` permits unwinding, aborting, and divergence yet still forbids
undefined behavior. -/
theorem canary_outcomeAllowed_effects :
    let cTot : FnContract Unit Unit Unit := { effects := totalMask }
    let cAny : FnContract Unit Unit Unit := { effects := anyExitMask }
    OutcomeAllowed cTot () (.terminal (.returned () ())) ∧
    ¬ OutcomeAllowed cTot () (.terminal (.unwound ())) ∧
    ¬ OutcomeAllowed cTot () (.terminal (.aborted ())) ∧
    ¬ OutcomeAllowed cTot () .diverged ∧
    ¬ OutcomeAllowed cTot () .faultUB ∧
    OutcomeAllowed cAny () (.terminal (.unwound ())) ∧
    OutcomeAllowed cAny () (.terminal (.aborted ())) ∧
    OutcomeAllowed cAny () .diverged ∧
    ¬ OutcomeAllowed cAny () .faultUB :=
  ⟨True.intro, fun h => Bool.noConfusion h.1, fun h => Bool.noConfusion h.1,
    fun h => Bool.noConfusion h, fun h => h,
    ⟨rfl, True.intro⟩, ⟨rfl, True.intro⟩, rfl, fun h => h⟩

/-- Each effect bit gates exactly its own `RunOutcome` arm (`noUnwind` the
`unwound` arm, `noAbort` the `aborted` arm, `terminates` the `diverged`
arm). Comparing only `totalMask` with `anyExitMask` cannot detect two bits
swapped inside `OutcomeAllowed`; this canary can. -/
theorem canary_outcomeAllowed_bit_arms :
    let cU : FnContract Unit Unit Unit :=
      { effects := { terminates := false, noUnwind := true, noAbort := false } }
    let cA : FnContract Unit Unit Unit := { effects := noAbortOnlyMask }
    let cT : FnContract Unit Unit Unit := { effects := termOnlyMask }
    ¬ OutcomeAllowed cU () (.terminal (.unwound ())) ∧
    OutcomeAllowed cU () (.terminal (.aborted ())) ∧
    OutcomeAllowed cU () .diverged ∧
    OutcomeAllowed cA () (.terminal (.unwound ())) ∧
    ¬ OutcomeAllowed cA () (.terminal (.aborted ())) ∧
    OutcomeAllowed cA () .diverged ∧
    OutcomeAllowed cT () (.terminal (.unwound ())) ∧
    OutcomeAllowed cT () (.terminal (.aborted ())) ∧
    ¬ OutcomeAllowed cT () .diverged :=
  ⟨fun h => Bool.noConfusion h.1, ⟨rfl, True.intro⟩, rfl,
    ⟨rfl, True.intro⟩, fun h => Bool.noConfusion h.1, rfl,
    ⟨rfl, True.intro⟩, ⟨rfl, True.intro⟩, fun h => Bool.noConfusion h⟩

/-- Each terminal arm of `OutcomeAllowed` consults strictly its own
postcondition: setting one postcondition to `False` while leaving the other
two `True` rejects only the matching outcome arm (detecting swapped
`postUnwind`/`postAbort` fields), while divergence depends only on
`terminates`. -/
theorem canary_outcomeAllowed_posts :
    let cR : FnContract Unit Unit Unit :=
      { postReturn := fun _ _ _ => False, effects := anyExitMask }
    let cU : FnContract Unit Unit Unit :=
      { postUnwind := fun _ _ => False, effects := anyExitMask }
    let cA : FnContract Unit Unit Unit :=
      { postAbort := fun _ _ => False, effects := anyExitMask }
    ¬ OutcomeAllowed cR () (.terminal (.returned () ())) ∧
    OutcomeAllowed cR () (.terminal (.unwound ())) ∧
    OutcomeAllowed cR () (.terminal (.aborted ())) ∧
    OutcomeAllowed cU () (.terminal (.returned () ())) ∧
    ¬ OutcomeAllowed cU () (.terminal (.unwound ())) ∧
    OutcomeAllowed cU () (.terminal (.aborted ())) ∧
    OutcomeAllowed cA () (.terminal (.returned () ())) ∧
    OutcomeAllowed cA () (.terminal (.unwound ())) ∧
    ¬ OutcomeAllowed cA () (.terminal (.aborted ())) ∧
    OutcomeAllowed cR () .diverged :=
  ⟨fun h => h, ⟨rfl, True.intro⟩, ⟨rfl, True.intro⟩,
    True.intro, fun h => h.2, ⟨rfl, True.intro⟩,
    True.intro, ⟨rfl, True.intro⟩, fun h => h.2, rfl⟩

/-- `OutcomeAllowed` threads exact `(q, r, m)` arguments into `postReturn`,
`postUnwind`, and `postAbort`: distinct non-`Unit` values catch swapped or
dropped arguments. -/
theorem canary_outcomeAllowed_post_args :
    let c : FnContract Nat Nat Nat :=
      { postReturn := fun q r m => q = 1 ∧ r = 2 ∧ m = 3
        postUnwind := fun q m => q = 1 ∧ m = 3
        postAbort := fun q m => q = 1 ∧ m = 3
        effects := anyExitMask }
    OutcomeAllowed c 1 (.terminal (.returned 2 3)) ∧
    ¬ OutcomeAllowed c 1 (.terminal (.returned 3 2)) ∧
    OutcomeAllowed c 1 (.terminal (.unwound 3)) ∧
    ¬ OutcomeAllowed c 3 (.terminal (.unwound 1)) ∧
    OutcomeAllowed c 1 (.terminal (.aborted 3)) ∧
    ¬ OutcomeAllowed c 3 (.terminal (.aborted 1)) :=
  ⟨⟨rfl, rfl, rfl⟩, fun h => absurd h.2.1 (by decide),
    ⟨rfl, rfl, rfl⟩, fun h => absurd h.2.1 (by decide),
    ⟨rfl, rfl, rfl⟩, fun h => absurd h.2.1 (by decide)⟩

/-- Pins the nine `DisclosedGap` constructors of
`Trusted.Framework.DisclosedGap`: their payload types, their declaration
order (`ctorIdx` is `0` through `8`), and that no other constructor exists
(every `ctorIdx` is below `9`). A list-length check would pass even with an
extra, reordered, or duplicated constructor. -/
theorem canary_disclosedGap_constructors (s : String) :
    [(DisclosedGap.unbridgedSemantics s).ctorIdx,
      (DisclosedGap.callerRawPtrAliasing s).ctorIdx,
      (DisclosedGap.callerMemoryThreadIsolation s).ctorIdx,
      (DisclosedGap.configuredReferenceScope s).ctorIdx,
      (DisclosedGap.assumedExternalCallee s).ctorIdx,
      (DisclosedGap.waivedInhabitation s).ctorIdx,
      DisclosedGap.selectedUnitScope.ctorIdx,
      DisclosedGap.rawLegacySpec.ctorIdx,
      (DisclosedGap.unverifiedDownstream s).ctorIdx] =
      [0, 1, 2, 3, 4, 5, 6, 7, 8] ∧
    ∀ g : DisclosedGap, g.ctorIdx < 9 :=
  ⟨rfl, fun
    | .unbridgedSemantics _ => Nat.le_of_ble_eq_true rfl
    | .callerRawPtrAliasing _ => Nat.le_of_ble_eq_true rfl
    | .callerMemoryThreadIsolation _ => Nat.le_of_ble_eq_true rfl
    | .configuredReferenceScope _ => Nat.le_of_ble_eq_true rfl
    | .assumedExternalCallee _ => Nat.le_of_ble_eq_true rfl
    | .waivedInhabitation _ => Nat.le_of_ble_eq_true rfl
    | .selectedUnitScope => Nat.le_of_ble_eq_true rfl
    | .rawLegacySpec => Nat.le_of_ble_eq_true rfl
    | .unverifiedDownstream _ => Nat.le_of_ble_eq_true rfl⟩

/-- Pins the closed constructor sets, declaration order, and payload types of
`TerminalOutcome`, `ClaimShape` (canonical lexicographic order), and
`OracleGrade` against `Trusted.Framework`. -/
theorem canary_closed_constructors {Ret Mem : Type} (r : Ret) (m : Mem)
    (s : String) :
    [(TerminalOutcome.returned r m).ctorIdx,
      (TerminalOutcome.unwound (Ret := Ret) m).ctorIdx,
      (TerminalOutcome.aborted (Ret := Ret) m).ctorIdx] = [0, 1, 2] ∧
    (∀ o : TerminalOutcome Ret Mem, o.ctorIdx < 3) ∧
    [ClaimShape.existsWitness.ctorIdx, ClaimShape.forallSafety.ctorIdx,
      ClaimShape.generalHyper.ctorIdx, ClaimShape.subsetHyper.ctorIdx,
      ClaimShape.termination.ctorIdx] = [0, 1, 2, 3, 4] ∧
    (∀ c : ClaimShape, c.ctorIdx < 5) ∧
    [(OracleGrade.unbridged s).ctorIdx, (OracleGrade.forwardSim s).ctorIdx,
      (OracleGrade.biFaultEquiv s).ctorIdx] = [0, 1, 2] ∧
    (∀ g : OracleGrade, g.ctorIdx < 3) :=
  ⟨rfl,
    fun
      | .returned _ _ => Nat.le_of_ble_eq_true rfl
      | .unwound _ => Nat.le_of_ble_eq_true rfl
      | .aborted _ => Nat.le_of_ble_eq_true rfl,
    rfl,
    fun
      | .existsWitness => Nat.le_of_ble_eq_true rfl
      | .forallSafety => Nat.le_of_ble_eq_true rfl
      | .generalHyper => Nat.le_of_ble_eq_true rfl
      | .subsetHyper => Nat.le_of_ble_eq_true rfl
      | .termination => Nat.le_of_ble_eq_true rfl,
    rfl,
    fun
      | .unbridged _ => Nat.le_of_ble_eq_true rfl
      | .forwardSim _ => Nat.le_of_ble_eq_true rfl
      | .biFaultEquiv _ => Nat.le_of_ble_eq_true rfl⟩

/-- Pins the field order of `EffectMask` and `FnContract`: positional
construction agrees with named construction, so swapping two same-typed
fields (such as `postUnwind` and `postAbort`) breaks this canary. -/
theorem canary_effectMask_fnContract_layout {Q R M : Type} (a b c : Bool)
    (sp bp : Q → Prop) (pr : Q → R → M → Prop) (pu pa : Q → M → Prop)
    (e : EffectMask) :
    EffectMask.mk a b c = { terminates := a, noUnwind := b, noAbort := c } ∧
    FnContract.mk sp bp pr pu pa e =
      { safetyPre := sp, behaviorPre := bp, postReturn := pr,
        postUnwind := pu, postAbort := pa, effects := e } :=
  ⟨rfl, rfl⟩

/-- Pins the names, types, and order of all 22 `ExecutionModel` fields of
`Trusted.Framework.ExecutionModel`. -/
theorem canary_executionModel_layout {Prog Body Sig Query Ret Mem : Type}
    (pid : String) (og : OracleGrade) (progAdm : Prog → Bool)
    (bodyAdm : Prog → Body → Bool) (partialScope : Prog → Bool)
    (bodyAt : Prog → Nat → Option Body) (uniq : Prog → Bool)
    (ident : Body → String) (isUnsafe isExt : Body → Bool)
    (matchesSig : Body → Sig → Bool) (mGaps : List DisclosedGap)
    (rGaps : Body → List DisclosedGap)
    (csGaps : ClaimShape → List DisclosedGap)
    (entryDom : Body → Query → Prop) (retValid : Body → Ret → Mem → Prop)
    (memValid : Mem → Prop) (execFor : Prog → Nat → Prog)
    (wf : Prog → Query → Prop)
    (produces : Prog → Query → TerminalOutcome Ret Mem → Prop)
    (diverges faultsUB : Prog → Query → Prop) :
    (ExecutionModel.mk pid og progAdm bodyAdm partialScope bodyAt uniq ident
        isUnsafe isExt matchesSig mGaps rGaps csGaps entryDom retValid
        memValid execFor wf produces diverges faultsUB :
      ExecutionModel Prog Body Sig Query Ret Mem) =
      { profileId := pid, oracleGrade := og, programAdmitted := progAdm,
        bodyAdmitted := bodyAdm, isPartialScope := partialScope,
        bodyAt := bodyAt, uniqueIdentities := uniq, bodyIdentity := ident,
        bodyIsUnsafe := isUnsafe, bodyIsExternal := isExt,
        bodyMatchesSig := matchesSig, modelGaps := mGaps,
        requiredGaps := rGaps, claimShapeGaps := csGaps,
        entryDom := entryDom, returnValid := retValid, memValid := memValid,
        execForBody := execFor, wellFormed := wf, produces := produces,
        diverges := diverges, faultsUB := faultsUB } :=
  rfl

/-- Pins the four local pure-`Prop` realizability compatibility predicates to
their verbatim upstream `Anneal.SpecRealizability` bodies by `rfl`. -/
theorem canary_specRealizability_compat_bodies.{u, v, w} :
    (@PostconditionDichotomy.{u, v} =
      fun {X : Type u} {Y : Type v} (pre : X → Prop) (post : X → Y → Prop) =>
        ∃ x, pre x ∧ (∃ y_ok, post x y_ok) ∧ (∃ y_bad, ¬ post x y_bad)) ∧
    (@ContractDeterministicOn.{u, v, w} =
      fun {X : Type u} {Y : Type v} {Z : Type w} (obs : Y → Z)
          (pre : X → Prop) (post : X → Y → Prop) =>
        ∀ x y₁ y₂, pre x → post x y₁ → post x y₂ → obs y₁ = obs y₂) ∧
    (@ContractDeterministic.{u, v} =
      fun {X : Type u} {Y : Type v} (pre : X → Prop) (post : X → Y → Prop) =>
        ContractDeterministicOn id pre post) ∧
    (@DichotomyModuloObservation.{u, v, w} =
      fun {X : Type u} {Y : Type v} {Z : Type w} (obs : X → Y → Z)
          (pre : X → Prop) (post : X → Y → Prop) =>
        ∃ x, pre x ∧ ∃ y_ok y_bad,
          obs x y_ok = obs x y_bad ∧ post x y_ok ∧ ¬ post x y_bad) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Pins the type-parameter, constructor-argument, and binder names of
`Trusted.Framework` (`Ret`/`Mem`, `ret`/`mem`, `profileId`, `oracleId`,
`identity`, `stage`, `Prog`/`Body`/`Sig`/`Query`, `Q`/`R`/`M`/`c`/`isUnsafe`/
`q`) and `Anneal.SpecRealizability` (`X`/`Y`/`Z`/`obs`/`pre`/`post`), so named
arguments keep elaborating after a future import swap. Distinct type arguments
also pin parameter order. -/
theorem canary_binder_names (r : Nat) (m : Bool) (s : String)
    (c : FnContract Unit Nat Bool)
    (pre : Nat → Prop) (post : Nat → Bool → Prop)
    (obs1 : Bool → String) (obs2 : Nat → Bool → String) :
    TerminalOutcome (Ret := Nat) (Mem := Bool) = TerminalOutcome Nat Bool ∧
    FnContract (Query := String) (Ret := Nat) (Mem := Bool) =
      FnContract String Nat Bool ∧
    ExecutionModel (Prog := Unit) (Body := Bool) (Sig := Nat)
        (Query := String) (Ret := Int) (Mem := Char) =
      ExecutionModel Unit Bool Nat String Int Char ∧
    TerminalOutcome.returned (ret := r) (mem := m) = .returned r m ∧
    TerminalOutcome.unwound (Ret := Nat) (mem := m) = .unwound m ∧
    TerminalOutcome.aborted (Ret := Nat) (mem := m) = .aborted m ∧
    OracleGrade.unbridged (profileId := s) = .unbridged s ∧
    OracleGrade.forwardSim (oracleId := s) = .forwardSim s ∧
    OracleGrade.biFaultEquiv (oracleId := s) = .biFaultEquiv s ∧
    DisclosedGap.unbridgedSemantics (profileId := s) =
      .unbridgedSemantics s ∧
    DisclosedGap.callerRawPtrAliasing (profileId := s) =
      .callerRawPtrAliasing s ∧
    DisclosedGap.callerMemoryThreadIsolation (profileId := s) =
      .callerMemoryThreadIsolation s ∧
    DisclosedGap.configuredReferenceScope (oracleId := s) =
      .configuredReferenceScope s ∧
    DisclosedGap.assumedExternalCallee (identity := s) =
      .assumedExternalCallee s ∧
    DisclosedGap.waivedInhabitation (identity := s) =
      .waivedInhabitation s ∧
    DisclosedGap.unverifiedDownstream (stage := s) =
      .unverifiedDownstream s ∧
    FnContract.effectiveSafetyPre (Q := Unit) (R := Nat) (M := Bool)
        (c := c) (isUnsafe := true) (q := ()) =
      c.effectiveSafetyPre true () ∧
    FnContract.effectiveBehaviorPre (Q := Unit) (R := Nat) (M := Bool)
        (c := c) (isUnsafe := false) (q := ()) =
      c.effectiveBehaviorPre false () ∧
    PostconditionDichotomy (X := Nat) (Y := Bool) (pre := pre)
        (post := post) = PostconditionDichotomy pre post ∧
    ContractDeterministicOn (X := Nat) (Y := Bool) (Z := String)
        (obs := obs1) (pre := pre) (post := post) =
      ContractDeterministicOn obs1 pre post ∧
    ContractDeterministic (X := Nat) (Y := Bool) (pre := pre)
        (post := post) = ContractDeterministic pre post ∧
    DichotomyModuloObservation (X := Nat) (Y := Bool) (Z := String)
        (obs := obs2) (pre := pre) (post := post) =
      DichotomyModuloObservation obs2 pre post :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.Hybrid.Canaries
