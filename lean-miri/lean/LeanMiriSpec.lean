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
import LeanMiriSpec.Correspondence.AllocLM1_4
import LeanMiriSpec.Correspondence.SimLM1_4
import LeanMiriSpec.Correspondence.WitLM1_4
import LeanMiriSpec.Correspondence.PtrLM3_1
import LeanMiriSpec.Correspondence.SimLM3_1
import LeanMiriSpec.Correspondence.WitLM3_1
import LeanMiriSpec.Audit

/-!
# `lean-miri` Correspondence with Anneal's MIR Semantics (`LeanMiriSpec`)

* `LeanMiriSpec.Correspondence.Translate`: syntax, type, and layout translation
  from Anneal's `Trusted.Rustc.V2026_06_01.MirAst` to `Miri.MIR`, together with
  single-threaded `AnnealMachine` and `annealStepHooks` (`RvalueHooks`,
  `ScalarOpsHooks`, `CastHooks`, `ControlHooks`, `TerminatorHooks`,
  `LocalStorageHooks`, `PlaceHooks`, `StepHooks`).
* `LeanMiriSpec.Correspondence.Relation`: dual immediate/indirect simulation
  relations (`ScalarRel`, `ImmediateRel`, `MemPlaceRel`, `LocalRel`, `FrameRel`,
  `MemoryAllocDisjoint`, `StateRel`, `RvalueResultRel`, `StepRel`,
  `StepObsRel`).
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
* `LeanMiriSpec.Correspondence.SimLM1_3`: `LM-1.3` correspondence for `Assert`
  terminators (`step_terminator_assert_simulation`), `Field` projections of
  scalar pairs, and checked `Add`/`Sub`/`Mul` followed by their overflow
  `Assert` (`checked_binop_then_assert_simulation`).
* `LeanMiriSpec.Correspondence.WitLM1_3`: `LM-1.3` witnesses that run a checked
  `(u16, bool)` `AddWithOverflow` body to the same result in both machines,
  with and without overflow.
* `LeanMiriSpec.Correspondence.AllocLM1_4`: fresh stack allocations of
  `forceAllocation` (shape, and the scalar write/read round trip).
* `LeanMiriSpec.Correspondence.SimLM1_4`: `StorageLive`/`StorageDead` of any
  local, `PlaceMention`, destructive moves, and the representation coalescing
  theorem `forceAllocation_preserves_StateRel` (`LM-1.4`).
* `LeanMiriSpec.Correspondence.WitLM1_4`: non-vacuity witnesses for `LM-1.4`.
* `LeanMiriSpec.Correspondence.PtrLM3_1`: raw pointer and allocation-map invariants
  (`AllocMapRel`, `PtrRel`), pointer resolution (`annealResolvePtr`), bounds/alignment
  validation (`checkAndDerefPtr`), and `Miri.Interpreter.ptrOffsetInbounds` (`LM-3.1`).
* `LeanMiriSpec.Correspondence.SimLM3_1`: `LM-3.1` correspondence for `Rvalue.RawPtr`
  (`&raw const`/`&raw mut`) with `forceAllocation`, `PlaceElem.Deref` (`*ptr`) reads,
  writes, and UB, `BinOp.Offset` (`inbounds` vs. `wrapping`), `CastKind.PtrToPtr`,
  and pointer/integer exposure casts (`step_stmt_lm3_1_simulation`).
* `LeanMiriSpec.Correspondence.WitLM3_1`: non-vacuity witnesses for `LM-3.1`.
* `LeanMiriSpec.Audit`: statement pins and axiom audit (`#assert_standard_axioms`
  plus exhaustive environment-wide verification across `LeanMiriSpec.*` and
  `Miri.*`).
-/
