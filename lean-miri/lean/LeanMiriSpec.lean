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
import LeanMiriSpec.Correspondence.SimLM1_2
import LeanMiriSpec.Correspondence.Witness
import LeanMiriSpec.Correspondence.WitLM1_2
import LeanMiriSpec.Correspondence.SimLM1_3
import LeanMiriSpec.Correspondence.WitLM1_3
import LeanMiriSpec.Audit

/-!
# `lean-miri` Correspondence with Anneal's MIR Semantics (`LeanMiriSpec`)

* `LeanMiriSpec.Correspondence.Translate`: syntax, type, and layout translation
  from Anneal's `Trusted.Rustc.V2026_06_01.MirAst` to `Miri.MIR`, together with
  single-threaded `AnnealMachine` and `annealStepHooks` (`RvalueHooks`,
  `ScalarOpsHooks`, `CastHooks`, `ControlHooks`, `TerminatorHooks`,
  `LocalStorageHooks`, `StepHooks`).
* `LeanMiriSpec.Correspondence.Relation`: dual immediate/indirect simulation
  relations (`ScalarRel`, `ImmediateRel`, `MemPlaceRel`, `LocalRel`, `FrameRel`,
  `StateRel`, `RvalueResultRel`, `StepRel`, `StepObsRel`).
* `LeanMiriSpec.Correspondence.Simulation`: single-step and fuel-bounded
  multi-step lockstep simulation and bisimulation theorems for scalar constants,
  copies, arithmetic (wrapping, checked `WithOverflow`, and `Unchecked`),
  division/remainder, bitwise, shift (`Shl`/`Shr`/`ShlUnchecked`/`ShrUnchecked`),
  unary (`Neg`/`Not`), statement (`assign`, `storageLive`, `storageDead`, `nop`),
  and terminator (`goto`, `return_`, `unreachable`) execution.
* `LeanMiriSpec.Correspondence.Witness`: kernel-checked non-vacuity and
  behavioral fidelity witnesses across normal returns, UB traps (`Div` by zero,
  signed `INT_MIN / -1`, OOB and negative signed shifts, `AddUnchecked`
  overflow, `Unreachable`), `(u16, bool)` scalar pairs, Unicode `char`, indirect
  `MemPlaceRel` allocations, `IntToInt` casts, and `SwitchInt` hooks.
* `LeanMiriSpec.Correspondence.SimLM1_2`: `LM-1.2` value- and step-level
  correspondence for boolean `Not`, `Eq`..`Ge` on `bool`/signed/unsigned
  operands, three-way `Cmp`, `IntToInt` casts, and `SwitchInt`
  (`step_stmt_lm1_2_simulation`, `step_terminator_lm1_2_simulation`).
* `LeanMiriSpec.Correspondence.WitLM1_2`: `LM-1.2` non-vacuity witnesses and
  concrete runs on which both machines agree.
* `LeanMiriSpec.Audit`: statement pins and axiom audit (`#assert_standard_axioms`
  plus exhaustive environment-wide verification across `LeanMiriSpec.*` and
  `Miri.*`).
-/
