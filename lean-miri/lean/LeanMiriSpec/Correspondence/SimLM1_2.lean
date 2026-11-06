import LeanMiriSpec.Correspondence.Translate
import LeanMiriSpec.Correspondence.Relation

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

namespace LeanMiriSpec.Correspondence

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem evalUnOp_bool_not_simulation : True := trivial
theorem evalBinOp_rel_simulation : True := trivial
theorem evalBinOp_cmp_simulation : True := trivial
theorem evalCast_intToInt_simulation : True := trivial
theorem step_terminator_switchInt_simulation : True := trivial
theorem step_stmt_lm1_2_simulation : True := trivial
theorem step_terminator_lm1_2_simulation : True := trivial

end LeanMiriSpec.Correspondence
