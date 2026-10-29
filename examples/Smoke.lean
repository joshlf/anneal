-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Anneal

/-!
# Worked Example: Minimal Small-Step Machine and Structural Non-Vacuity

This module exercises `Trusted.SmallStepMachine` and
`Anneal.non_vacuity_at_every_depth` on a minimal one-state machine.
-/

namespace AnnealExamples

open Trusted
open Anneal

/-- Trivial one-state small-step machine that terminates immediately with
    `()`. -/
def unitMachine : SmallStepMachine Unit Unit Unit Unit where
  initState _ _ := True
  step _ _ r := r = .terminated (.normal ())

theorem unitMachine_total : TotalStep unitMachine :=
  fun _ _ => ⟨.terminated (.normal ()), rfl⟩

theorem unitMachine_inhabited : InhabitedDemonic unitMachine := by
  intro _ _ _ _ h
  cases h

theorem unitMachine_non_vacuous (n : Nat) :
    ∃ out : ExecOut Unit Unit,
      ReachesPrefix unitMachine () () n () out.trace out.outcome ∧
      out.outcome ≠ .stuck := by
  cases non_vacuity_at_every_depth unitMachine_total unitMachine_inhabited () () True.intro n with
  | intro out hout =>
    exact ⟨out, hout.2.1, hout.2.2⟩

end AnnealExamples
