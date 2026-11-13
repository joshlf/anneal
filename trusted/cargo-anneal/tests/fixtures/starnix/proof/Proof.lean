-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Expected
import ProductionClaims

namespace Proof

open Trusted.Mvp Endianness ProductionReduction ProductionClaims

theorem verify : Expected.claim := by
  constructor
  · rfl
  · constructor
    · intro id body found
      change ([sourceBody] : List Body)[id]? = some body at found
      cases id with
      | zero =>
        have same : sourceBody = body := Option.some.inj found
        subst body
        exact baseline _
      | succ id => simp at found
    · exact ⟨sourceBody, rfl, bigEndian_exact, littleEndian_exact,
        bigEndian_involutive⟩

end Proof
