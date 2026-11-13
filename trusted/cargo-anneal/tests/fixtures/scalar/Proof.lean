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

def body : Body := Captured.program.bodies[0]

-- The execution certificate uses the captured body. Changing the Rust result
-- invalidates this equation and the stated property.
theorem runs (args : List Word) :
    run body 2 (initial body args) = some 0 := rfl

theorem verify : Expected.claim := by
  constructor
  · rfl
  · constructor
    · intro id selected found
      cases id with
      | zero =>
          have same : body = selected := Option.some.inj found
          subst selected
          exact ⟨rfl, fun args _ _ => (run_initial_success (runs args)).1⟩
      | succ id => simp [Captured.program] at found
    · intro selected found value returned
      have same : body = selected := Option.some.inj found
      subst selected
      exact (run_result_unique (runs []) returned).symm

end Proof
