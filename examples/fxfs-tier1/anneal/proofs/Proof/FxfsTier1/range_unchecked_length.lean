import Trusted
import Anneal.Rustc.V2026_06_01.Lower
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Mir.FxfsTier1.range_unchecked_length
import Specs.FxfsTier1.range_unchecked_length
import Obligations.FxfsTier1.range_unchecked_length

namespace Proof.FxfsTier1.range_unchecked_length

set_option linter.unusedSimpArgs false

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Specs.FxfsTier1.range_unchecked_length

/-- Universal proof that `range_unchecked_length` (`u64::unchecked_sub` extracted from
    `fxfs/src/range.rs`) is free of Undefined Behavior (`BinOp.subUnchecked`) for all
    64-bit ranges satisfying `start <= end`. -/
theorem verified : VerificationResult Obligations.FxfsTier1.range_unchecked_length.claim := by
  refine verifyMirNoPanicSym Obligations.FxfsTier1.range_unchecked_length.claim 8 ?_
  intro args h_pre
  rcases h_pre with ⟨s, e, h_le, h_e_max, rfl⟩
  have h_sub_lt : e - s < 18446744073709551616 := by omega
  have h_wrap_sub : wrapScalarBits (e - s) 18446744073709551616 = e - s :=
    wrapScalarBits_of_lt h_sub_lt
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
  all_goals (try (simp_all [h_wrap_sub]; omega))
  all_goals (
    intro s' e' h_eq
    injection h_eq with h_f0 h_f1
    injection h_f1 with h_f1_hd _
    injection h_f0 with h_s0
    injection h_s0 with h_s _
    injection h_f1_hd with h_s1
    injection h_s1 with h_e _
    subst h_s h_e
    simp [h_wrap_sub]
  )

end Proof.FxfsTier1.range_unchecked_length
