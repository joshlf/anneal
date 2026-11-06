import LeanMiriSpec.Correspondence.Translate
import LeanMiriSpec.Correspondence.Relation

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

theorem toBits_ok (msc : Miri.Memory.ScalarInt) (sz : Miri.Memory.Size) (hsz : sz = msc.size) :
  msc.toBits sz = .ok (msc.rawData) := by
  sorry

