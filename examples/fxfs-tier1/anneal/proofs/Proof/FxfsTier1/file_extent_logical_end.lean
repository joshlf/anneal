import Trusted
import Anneal.Rustc.V2026_06_01.Lower
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Mir.FxfsTier1.file_extent_logical_end
import Specs.FxfsTier1.file_extent_logical_end
import Obligations.FxfsTier1.file_extent_logical_end

namespace Proof.FxfsTier1.file_extent_logical_end

set_option linter.unusedSimpArgs false

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Specs.FxfsTier1.file_extent_logical_end

/-- Universal proof that `file_extent_logical_end` (`u64::unchecked_sub` + `u64::unchecked_add`
    extracted from `fxfs/src/object_store/data_object_handle.rs`) is free of Undefined Behavior
    (`BinOp.subUnchecked` and `BinOp.addUnchecked`) for all valid 64-bit `FileExtent` values. -/
theorem verified : VerificationResult Obligations.FxfsTier1.file_extent_logical_end.claim := by
  refine verifyMirNoPanicSym Obligations.FxfsTier1.file_extent_logical_end.claim 8 ?_
  intro args h_pre
  rcases h_pre with ⟨ds, de, lo, h_lt, h_de_max, h_sum_max, rfl⟩
  have h_sub_lt : de - ds < 18446744073709551616 := by omega
  have h_wrap_sub : wrapScalarBits (de - ds) 18446744073709551616 = de - ds :=
    wrapScalarBits_of_lt h_sub_lt
  have h_wrap_add : wrapScalarBits (lo + (de - ds)) 18446744073709551616 = lo + (de - ds) :=
    wrapScalarBits_of_lt h_sum_max
  (repeat' ((conv => whnf); split)); all_goals (conv => whnf)
  all_goals (try (simp_all [h_wrap_sub, h_wrap_add]; omega))
  all_goals (
    intro ds' de' lo' h_eq
    injection h_eq with h_f0 h_f1
    injection h_f1 with h_f1_hd h_f2
    injection h_f2 with h_f2_hd _
    injection h_f0 with h_s0
    injection h_s0 with h_ds _
    injection h_f1_hd with h_s1
    injection h_s1 with h_de _
    injection h_f2_hd with h_s2
    injection h_s2 with h_lo _
    subst h_ds h_de h_lo
    simp [h_wrap_sub, h_wrap_add]
  )

end Proof.FxfsTier1.file_extent_logical_end
