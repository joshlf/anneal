/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.Translate
import LeanMiriSpec.Correspondence.Relation
import LeanMiriSpec.Correspondence.Simulation
import LeanMiriSpec.Audit

/-!
# `lean-miri` Correspondence with Anneal's MIR Semantics (`LeanMiriSpec`)

* `LeanMiriSpec.Correspondence.Translate`: bidirectional translation between
  Anneal's `Trusted.Rustc.V2026_06_01.MirAst` and `Miri.MIR`, together with
  single-threaded `AnnealStepHooks` (`RvalueHooks`, `ScalarOpsHooks`,
  `ControlHooks`, `TerminatorHooks`, `StepHooks`).
* `LeanMiriSpec.Correspondence.Relation`: dual immediate/indirect simulation
  relations (`ScalarRel`, `ImmediateRel`, `MemPlaceRel`, `LocalRel`, `FrameRel`,
  `StateRel`, `RvalueResultRel`, `StepRel`).
* `LeanMiriSpec.Correspondence.Simulation`: lockstep simulation theorems for
  arithmetic, bitwise, shift, unary, statement (`assign` / `nop`), and
  terminator (`goto` / `return_`) execution.
* `LeanMiriSpec.Audit`: axiom audit (`#assert_standard_axioms` and exhaustive
  module-wide axiom verification across `LeanMiriSpec.*` and `Miri.*`).
-/
