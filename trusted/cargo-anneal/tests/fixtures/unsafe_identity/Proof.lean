-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Expected
import Anneal.Mvp.Execution

namespace Proof

open Trusted.Mvp Anneal.Mvp

-- Inventory positions retrieve the operational bodies for this fixture. The
-- canonical safety duty still selects the reviewed predicate by body identity.
def faulting : Body := Captured.program.bodies[0]
def returning : Body := Captured.program.bodies[1]

theorem returning_runs (args : List Word) :
    run returning 2 (initial returning args) = some 0 := rfl

theorem faulting_really_faults :
    step faulting (initial faulting []) = .fault .unreachable := rfl

theorem faulting_not_safe : ¬Safe faulting [] := by
  intro safe
  exact safe (initial faulting []) .refl .unreachable faulting_really_faults

theorem verify : Expected.claim := by
  constructor
  · rfl
  · constructor
    · intro id selected found
      cases id with
      | zero =>
          have same : faulting = selected := Option.some.inj found
          subst selected
          constructor
          · rfl
          · intro args valid required
            -- This elimination is valid only for the uncallable locked item.
            -- Moving the same faulting body to open changes its authenticated
            -- key, so its caller requirement no longer supplies False here.
            exact False.elim (required rfl)
      | succ id =>
          cases id with
          | zero =>
              have same : returning = selected := Option.some.inj found
              subst selected
              exact ⟨rfl, fun args _ _ =>
                (run_initial_success (returning_runs args)).1⟩
          | succ id => simp [Captured.program] at found
    · exact True.intro

end Proof
