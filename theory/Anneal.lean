-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted

/-!
# Anneal Theory Umbrella (`Anneal.lean`)

Root umbrella module for Anneal's verified meta-theory (`theory/`).
-/

namespace Anneal

/-- Placeholder crate checker pending `theory/Anneal/MirLemmas.lean`. -/
def checkCrate (_ : Trusted.Crate) : List String :=
  ["MIR lowering not yet implemented", "crate"]

/-- Placeholder crate verification entrypoint pending
`theory/Anneal/MirLemmas.lean`. -/
theorem proveCrate (c : Trusted.Crate) (h : checkCrate c = []) :
    Trusted.CrateTheorem c := by
  nomatch h

end Anneal
