/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import MiniRustSpec.Anchors
import MiniRustSpec.Correspondence.Witness

/-!
# Axiom audit

`#assert_standard_axioms` fails the build unless each listed declaration
depends only on Lean's standard axioms (`propext`, `Quot.sound`,
`Classical.choice`); in particular on no `sorryAx` and no
`Lean.ofReduceBool` (which `native_decide` would introduce). It also logs the
axioms of each declaration, so `lake build MiniRustSpec.Audit` doubles as the
`#print axioms` receipt.
-/

namespace MiniRustSpec.Audit

open Lean Elab Command

/-- Fail unless every listed declaration depends only on the standard axioms. -/
elab "#assert_standard_axioms " ids:ident* : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axs ← liftCoreM <| Lean.collectAxioms n
    for a in axs do
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{n} depends on the non-standard axiom {a}"
    logInfo m!"{n} depends on axioms: {axs.toList}"

open MiniRustSpec.LibSpecr in
#assert_standard_axioms
  Nondet
  NdResult

#assert_standard_axioms MiniRustSpec.Gen.NdResult

open MiniRustSpec.Correspondence in
#assert_standard_axioms
  step_correspondence
  step_initBlock
  step_start
  initMachineState_startRel
  reaches_rel
  run_ret
  run_ret_from_start
  run_ub
  run_ub_from_start
  steps_error
  steps_error_from_start
  steps_outcome
  mirNoUB_safe
  mirNoUB_safe_from_start
  mirNoUB_progress
  mirNoUB_progress_from_start
  mirNoUB_diverges_steps_ok
  mirNoUB_diverges_from_start
  mirCall_ret
  mirCall_ub
  mirCall_noUB
  mirCall_progress
  mirCall_diverges_steps_ok
  runA_sound
  runA_noUB
  faultsA_sound
  treeSafe_of_tau_inv
  noRet_of_tau_inv
  evalReturn_callee
  evalStatement_assign
  evalStatement_placeMention
  evalValue_operand
  evalValue_rvalue
  evalStmt_assign
  evalStmt_placeMention
  evalOperand_frag
  evalRvalue_frag
  castBits_eq_toNat
  switch_lookup
  translateFn_spec
  translateFn_start

open MiniRustSpec.Correspondence.Witness in
#assert_standard_axioms
  sumTo_inFragment
  sumTo_translate
  sumTo_init_step
  sumTo_rel
  sumTo_anneal_ret
  sumTo_noUB
  sumTo_minirust_ret
  sumTo_minirust_direct
  sumTo_minirust_ret_from_start
  sumTo_minirust_direct_from_start
  retUninit_inFragment
  retUninit_translate
  retUninit_rel
  retUninit_anneal_ub
  retUninit_minirust_ub
  retUninit_minirust_direct
  retUninit_minirust_ub_from_start
  negMention_inFragment
  negMention_translate
  negMention5_startRel
  negMention5_anneal_ret
  negMention5_minirust_ret_from_start
  negMention5_minirust_direct
  negMention0_startRel
  negMention0_anneal_ub
  negMention0_minirust_ub_from_start
  negMention0_minirust_direct
  signedEdge_inFragment
  signedEdge_translate
  signedEdgeMin_anneal_ret
  signedEdgeMin_noUB
  signedEdgeMin_minirust_ret_from_start
  signedEdgeMin_minirust_noUB
  signedEdgeMin_minirust_direct
  signedEdgeOne_anneal_ret
  signedEdgeOne_minirust_ret_from_start
  signedEdgeOne_minirust_direct
  castBitNot_inFragment
  castBitNot_translate
  castBitNot4_anneal_ret
  castBitNot4_noUB
  castBitNot4_minirust_ret_from_start
  castBitNot4_minirust_direct
  spinLoop_inFragment
  spinLoop_translate
  spinLoop_noUB
  spinLoop_diverges
  spinLoop_minirust_steps_ok

#assert_standard_axioms MiniRustSpec.Anchors.anchors_ok

end MiniRustSpec.Audit
