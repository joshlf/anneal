import Trusted
import Anneal
import Mir.FxfsPlatformPager.layer_pager_read_unfixed
import Obligations.FxfsPlatformPager.layer_pager_read_unfixed
import Specs.FxfsPlatformPager.layer_pager_read_unfixed
import Proof.FxfsPlatformPager.mapped_vmo_as_slice_unfixed

namespace Proof.FxfsPlatformPager.layer_pager_read_unfixed

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

private theorem ble_eq_false_of_lt {a b : Nat} (h : b < a) : Nat.ble a b = false := by
  cases h_b : Nat.ble a b
  · rfl
  · have := Nat.le_of_ble_eq_true h_b
    omega

set_option maxHeartbeats 2000000 in
theorem verified : ModularVerificationResult Obligations.FxfsPlatformPager.layer_pager_read_unfixed.modularClaim := by
  refine verifyModularContractMirSym
    Obligations.FxfsPlatformPager.mapped_vmo_as_slice_unfixed.ubExceptionClaim.callContract
    Mir.FxfsPlatformPager.layer_pager_read_unfixed.body
    Specs.FxfsPlatformPager.layer_pager_read_unfixed.pre
    Specs.FxfsPlatformPager.layer_pager_read_unfixed.post
    30 ?_
  intro args mem h_pre
  rcases h_pre with ⟨mapped_len, pnn, pb, read_offset, read_len, h_ml, h_ro, h_rl, h_pnn, h_pb, rfl, rfl⟩
  rcases h_pnn with rfl | rfl
  · conv => whnf
    intro retVal mem' h_out
    injection h_out with h_pair
    injection h_pair with h_ret h_mem
    subst h_ret h_mem
    refine ⟨rfl, ?_⟩
    intro ml' pnn' pb' ro' rl' h_args
    injection h_args with h1 ht1
    injection ht1 with h2 ht2
    injection h2 with hs2
    cases hs2
    simp
  · conv => whnf
    refine ⟨⟨rfl, mapped_len, pb, h_ml, h_pb, rfl, rfl⟩, ?_⟩
    rintro _ ⟨retVal, mem', rfl, h_mem', h_ret_fn⟩
    have h_rv := h_ret_fn mapped_len pb rfl
    have h_mem_empty : mem' = emptyMemory := h_mem'
    clear h_ret_fn h_mem'
    subst h_rv h_mem_empty
    change wpMirExecModularSym
      Obligations.FxfsPlatformPager.mapped_vmo_as_slice_unfixed.ubExceptionClaim.callContract
      21
      Mir.FxfsPlatformPager.layer_pager_read_unfixed.body
      (.running {
        frame := {
          blockIdx := 3,
          stmtIdx := 0,
          locals := [
            .uninit,
            .init (.scalar { bits := mapped_len, sizeBytes := 8 }),
            .init (.scalar { bits := 1, sizeBytes := 1 }),
            .init (.scalar { bits := pb, sizeBytes := 1 }),
            .init (.scalar { bits := read_offset, sizeBytes := 8 }),
            .init (.scalar { bits := read_len, sizeBytes := 8 }),
            .init (.scalar { bits := mapped_len, sizeBytes := 8 }),
            .uninit, .uninit, .uninit, .uninit, .uninit, .uninit
          ]
        },
        memory := emptyMemory
      })
      _
    conv => whnf
    split
    · next h_ble1 =>
      have h_le1 : read_offset ≤ mapped_len := Nat.le_of_ble_eq_true h_ble1
      conv => whnf
      split
      · next h_ble2 =>
        conv => whnf
        split
        · next h_ble3 =>
          have h_sub_lt : mapped_len - read_offset < 18446744073709551616 := by omega
          have h_ble3' : Nat.ble read_len (mapped_len - read_offset) = true := by
            dsimp [wrapScalarBits, scalarModulus, Nat.sub] at h_ble3
            rw [ble_eq_false_of_lt h_sub_lt] at h_ble3
            exact h_ble3
          have h_le2 : read_len ≤ mapped_len - read_offset := Nat.le_of_ble_eq_true h_ble3'
          conv => whnf
          split
          · next h_ble4 =>
            have h_sum_lt : read_offset + read_len < 18446744073709551616 := by omega
            have h_nble4 : Nat.ble 18446744073709551616 (read_offset + read_len) = false :=
              ble_eq_false_of_lt h_sum_lt
            dsimp [scalarModulus, Nat.add] at h_ble4
            rw [h_nble4] at h_ble4
            contradiction
          · next h_nble4 =>
            conv => whnf
            intro retVal' mem'' h_out
            injection h_out with h_pair
            injection h_pair with h_ret h_mem
            subst h_ret h_mem
            refine ⟨rfl, ?_⟩
            intro ml' pnn' pb' ro' rl' h_args
            injection h_args with h1 ht1
            injection ht1 with h2 ht2
            injection ht2 with h3 ht3
            injection ht3 with h4 ht4
            injection ht4 with h5 _
            injection h1 with hs1
            injection h2 with hs2
            injection h4 with hs4
            injection h5 with hs5
            cases hs1; cases hs2; cases hs4; cases hs5
            have h_ok : read_offset ≤ mapped_len ∧ read_len ≤ mapped_len - read_offset := ⟨h_le1, h_le2⟩
            simp [h_ok]
            omega
        · next h_nble3 =>
          have h_sub_lt : mapped_len - read_offset < 18446744073709551616 := by omega
          have h_nble3' : Nat.ble read_len (mapped_len - read_offset) = false := by
            dsimp [wrapScalarBits, scalarModulus, Nat.sub] at h_nble3
            rw [ble_eq_false_of_lt h_sub_lt] at h_nble3
            exact h_nble3
          have h_gt2 : ¬ read_len ≤ mapped_len - read_offset :=
            fun h_le => by rw [Nat.ble_eq_true_of_le h_le] at h_nble3'; contradiction
          conv => whnf
          intro retVal' mem'' h_out
          injection h_out with h_pair
          injection h_pair with h_ret h_mem
          subst h_ret h_mem
          refine ⟨rfl, ?_⟩
          intro ml' pnn' pb' ro' rl' h_args
          injection h_args with h1 ht1
          injection ht1 with h2 ht2
          injection ht2 with h3 ht3
          injection ht3 with h4 ht4
          injection ht4 with h5 _
          injection h1 with hs1
          injection h2 with hs2
          injection h4 with hs4
          injection h5 with hs5
          cases hs1; cases hs2; cases hs4; cases hs5
          have h_not : ¬ (read_offset ≤ mapped_len ∧ read_len ≤ mapped_len - read_offset) := by omega
          simp [h_not]
      · intro _ _ h; nomatch h
    · next h_nble1 =>
      have h_gt1 : ¬ read_offset ≤ mapped_len :=
        fun h_le => by
          have h_tr : Nat.ble read_offset mapped_len = true := Nat.ble_eq_true_of_le h_le
          rw [h_tr] at h_nble1; contradiction
      conv => whnf
      intro retVal' mem'' h_out
      injection h_out with h_pair
      injection h_pair with h_ret h_mem
      subst h_ret h_mem
      refine ⟨rfl, ?_⟩
      intro ml' pnn' pb' ro' rl' h_args
      injection h_args with h1 ht1
      injection ht1 with h2 ht2
      injection ht2 with h3 ht3
      injection ht3 with h4 ht4
      injection ht4 with h5 _
      injection h1 with hs1
      injection h2 with hs2
      injection h4 with hs4
      injection h5 with hs5
      cases hs1; cases hs2; cases hs4; cases hs5
      have h_not : ¬ (read_offset ≤ mapped_len ∧ read_len ≤ mapped_len - read_offset) := by omega
      simp [h_not]

/-- Model witness for `mapped_vmo_as_slice_unfixed` returning `mapped_len`. -/
def mappedVmoLenModel (args : List Value) (mem : Memory) : Value × Memory :=
  match args with
  | .scalar { bits := mapped_len, .. } :: _ =>
    (.scalar { bits := mapped_len, sizeBytes := 8 }, mem)
  | _ => (.scalar { bits := 0, sizeBytes := 8 }, mem)

/-- End-to-end horizontal linking theorem combining the modular proof of
    `layer_pager_read_unfixed` with the scoped UB-exception proof of
    `mapped_vmo_as_slice_unfixed`. -/
theorem linked_with_ub_exception (fallback : ExternalCallHandler) :
    ((fun args mem =>
      (mirHandledTree
        Mir.FxfsPlatformPager.layer_pager_read_unfixed.body
        args mem
        (ubExceptionModelHandler
          Obligations.FxfsPlatformPager.mapped_vmo_as_slice_unfixed.ubExceptionClaim
          mappedVmoLenModel
          fallback)).toPartial) ≤
      MirClosedStatefulContractSpec
        Specs.FxfsPlatformPager.layer_pager_read_unfixed.pre
        Specs.FxfsPlatformPager.layer_pager_read_unfixed.pre
        Specs.FxfsPlatformPager.layer_pager_read_unfixed.post) ∧
    MirStatefulContractHoldsWithSafety
      Mir.FxfsPlatformPager.mapped_vmo_as_slice_unfixed.body
      (fun args mem =>
        Specs.FxfsPlatformPager.mapped_vmo_as_slice_unfixed.pre args mem ∧
        Specs.FxfsPlatformPager.mapped_vmo_as_slice_unfixed.strictSafetyPre args mem)
      Specs.FxfsPlatformPager.mapped_vmo_as_slice_unfixed.pre
      Specs.FxfsPlatformPager.mapped_vmo_as_slice_unfixed.post := by
  refine linkUbExceptionCallee
    verified
    Proof.FxfsPlatformPager.mapped_vmo_as_slice_unfixed.verified
    mappedVmoLenModel
    fallback
    ?_
  intro args mem h_pre _
  rcases h_pre with ⟨mapped_len, pb, _, _, rfl, rfl⟩
  refine ⟨rfl, ?_⟩
  intro ml' pb' h_args
  injection h_args with h1 _

end Proof.FxfsPlatformPager.layer_pager_read_unfixed
