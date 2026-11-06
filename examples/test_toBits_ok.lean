import LeanMiriSpec.Correspondence.Translate
import LeanMiriSpec.Correspondence.Relation

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

private theorem toBits_ok (msc : Miri.Memory.ScalarInt) (sz : Miri.ABI.Size) (hsz : sz == msc.size) :
  ∃ v, msc.toBits sz = .ok v := by
  unfold Miri.Memory.ScalarInt.toBits
  have h_eq : sz = msc.size := beq_iff_eq.mp hsz
  subst h_eq
  unfold Miri.Memory.ScalarInt.size
  simp [bne_self_eq_false, bind, Except.bind, pure, Except.pure]

