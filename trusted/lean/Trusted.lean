-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Trusted.Attributes
import Trusted.Refinement
import Trusted.CoInd
import Trusted.Effect
import Trusted.Specs
import Trusted.Verify
import Trusted.Machine
import Trusted.Values
import Trusted.Memory
import Trusted.CFG
import Trusted.Statements
import Trusted.Function
import Trusted.Semantics
import Trusted.Rustc
import Trusted.Mir
import Trusted.Obligation

/-!
# Trusted (TCB) Index (`Trusted.lean`)

This module re-exports the foundational trust boundary for Anneal. All
symbolic execution routines (`wpMirSym`, `holdBoolMirSym`), verification
conditions, and kernel semantic interpretations of Rust/MIR AST nodes must
reside in `Trusted.*`.

Secondary proof automation tactics, heuristics, verification-condition
bisimulations, simulations, predicate transformers, and domain lemmas live in
`theory/Anneal/`.
-/

end Trusted
