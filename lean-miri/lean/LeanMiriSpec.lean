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
import LeanMiriSpec.Correspondence.AllocLM2_1
import LeanMiriSpec.Correspondence.SimLM2_1
import LeanMiriSpec.Correspondence.WitLM2_1
import LeanMiriSpec.Correspondence.LayoutLM2_2
import LeanMiriSpec.Correspondence.ProjLM2_2
import LeanMiriSpec.Correspondence.SimLM2_2
import LeanMiriSpec.Correspondence.WitLM2_2
import LeanMiriSpec.Correspondence.EnumLM2_3
import LeanMiriSpec.Correspondence.SimLM2_3
import LeanMiriSpec.Correspondence.WitLM2_3
import LeanMiriSpec.Correspondence.UnionLM2_4
import LeanMiriSpec.Correspondence.SimLM2_4
import LeanMiriSpec.Correspondence.WitLM2_4
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
* `LeanMiriSpec.Correspondence.AllocLM2_1`: contiguous scalar byte-slice round
  trips and `ArraySliceRel` preservation (`nil`, `readScalar_get`,
  `writeScalar_snoc`, `writeScalar_set`, `writeScalarRepeatedly_spec`) for
  `LM-2.1`.
* `LeanMiriSpec.Correspondence.SimLM2_1`: `LM-2.1` correspondence for homogeneous
  arrays `[T; N]`, `Aggregate (.array _)`, `Rvalue.Repeat`, `Rvalue.Len`, and
  `Index`/`ConstantIndex` projections (`fromEnd = false` and `fromEnd = true`),
  including out-of-bounds and uninitialized/dead index UB equivalence
  (`step_stmt_lm2_1_simulation`), with `step_stmt_lm2_1_array_simulation`
  re-establishing `LiveAllocsNodup` and local immediacy so that array statements
  chain.
* `LeanMiriSpec.Correspondence.WitLM2_1`: non-vacuity witnesses for `LM-2.1`.
* `LeanMiriSpec.Correspondence.LayoutLM2_2`: byte-level `InitMaskWordRel`,
  arbitrary-offset `Allocation.readScalar`/`writeScalar` round-trip,
  `ValidStructLayout`, field-write preservation across disjoint scalar fields
  and uninitialized padding bytes, and unpadded vs. padded byte-counting
  dichotomy (`LM-2.2`).
* `LeanMiriSpec.Correspondence.ProjLM2_2`: nested `Field` projection chains,
  `StructMemPlaceRel` / `ImmediateStructRel`, `StateRelLM2_2`, base `StateRel`
  bridge theorems (`StateRel.toLM2_2`, `StateRelLM2_2.toStateRel_of_flat_imm`),
  and nested `Field` read simulation (`LM-2.2`).
* `LeanMiriSpec.Correspondence.SimLM2_2`: state-independent `LM-2.2` typing
  judgments and lockstep simulation for `Rvalue.Aggregate` (`Tuple` / single-variant
  `Adt`), nested `Field` scalar and immediate sub-struct reads/writes (`.Scalar`
  wrappers and `.ScalarPair` sub-structs), whole-value `Use` copies/moves across
  both immediate-ABI and `.Memory`-ABI aggregates (`annealStructMemCopyOp`,
  including self-move `_idx = move _idx` lockstep simulation and self-copy
  `_idx = copy _idx` `copyRangesOverlap` UB characterization),
  `StorageLive`/`StorageDead`, block-level composition (`step_stmts_lm2_2_simulation`),
  and `Goto`/`Unreachable`/`Return` terminators (including tuple- and
  struct-returning root functions via `step_terminator_return_struct_lm2_2_simulation`)
  under `StateRelLM2_2`.
* `LeanMiriSpec.Correspondence.WitLM2_2`: seventeen kernel-checked `LM-2.2`
  execution witnesses covering `AbiRepr.ScalarPair` (`forceAllocation` +
  `StorageDead` + memory-backed reassignment), unpadded and padded
  `AbiRepr.Memory`, nested `AbiRepr.Scalar` wrapper (`_3 = copy _1.1`,
  `_1.1 = move _2`, plus immediate `ScalarPair` + `Scalar` wrapper
  `_4 = copy _3.1`) and `ScalarPair` (`_3 = copy _2.1`, `_2.1 = move _4`)
  sub-struct reads/writes, whole-value `.Memory` struct move/copy
  (`_3 = move _2`, `_4 = copy _3`), self-move (`_1 = move _1`) vs. self-copy
  (`_1 = copy _1` `copyRangesOverlap` UB), dangling/read-only/move-then-use UB,
  2-level 3-field `.Memory` sub-struct construction/mutation/read,
  tuple/struct-returning root functions (`fn() -> PaddedOuter`), root `return`
  with live padded memory, and `> 64`-byte multi-block `InitMask` `#[repr(C)]`
  structs (`80` bytes across two 64-bit `InitMask` words).
* `LeanMiriSpec.Correspondence.EnumLM2_3`: `LM-2.3` multi-variant direct-tagged
  enum overlay (`annealStepHooksLM2_3`, proved conservatively extending
  `annealStepHooks` via `step_LM2_3_eq_of_bodyFree`), `ValidEnumLayout`
  (`Variants.Multiple` + `TagEncoding.Direct`), `EnumMemRel`,
  `UninitEnumMemRel`, `EnumLocalByteUninit`, `StateRelLM2_3`, `StepRelLM2_3`,
  and entry bridges (`StateRel.toLM2_3_empty`, `StateRel.toLM2_3`).
* `LeanMiriSpec.Correspondence.SimLM2_3`: `LM-2.3` correspondence for
  multi-variant enum `Rvalue.Aggregate`
  (`evalRvalue_aggregate_enum_simulation`), `StatementKind.SetDiscriminant`
  (`step_setDiscriminant_simulation` and `.uninit` divergence),
  `Rvalue.Discriminant` (`evalRvalue_discriminant_simulation`), `Downcast` +
  `Field` reads and writes (`evalProjection_downcast_field_simulation`,
  `step_downcast_field_write_simulation`, plus inactive-initialized and
  inactive/`.uninit` write boundaries), `Terminator.SwitchInt`
  (`enum_match_switchInt_simulation`), `StorageLive`/`StorageDead`, whole-enum
  `Copy`/`Move` (`step_enum_copy_move_simulation`,
  `step_enum_self_move_simulation`,
  `step_enum_self_copy_dead_or_uninit_simulation`, plus unconditional self-copy
  `copyRangesOverlap` and `enumUninitInd` copy/move boundaries), and
  `Goto`/`Return` helpers.
* `LeanMiriSpec.Correspondence.WitLM2_3`: 18 kernel-checked `LM-2.3`
  multi-variant `Lm23Enum` execution, lockstep-UB, divergence, and
  `BodyFreeOfLM2_3` witnesses exercising every `SimLM2_3` theorem and boundary.
* `LeanMiriSpec.Correspondence.UnionLM2_4`: the `LM-2.4` union and `Subslice`
  hooks (`annealStepHooksLM2_4`, a conservative extension of `annealStepHooks`),
  the union initialization masks of `I-11` (`unionPrefixMask`, certified against
  the vendored chunk copy by `unionPrefixMask_vendoredCopy`), and the union state
  relation `StateRelLM2_4`.
* `LeanMiriSpec.Correspondence.SimLM2_4`: `LM-2.4` correspondence for union
  aggregates, union field reads (including reads of uninitialized bytes),
  whole-union copies that preserve the initialization mask, and `Subslice`
  projections, with the boundaries of the agreeing fragment.
* `LeanMiriSpec.Correspondence.WitLM2_4`: non-vacuity witnesses for `LM-2.4`.
* `LeanMiriSpec.Audit`: statement pins and axiom audit (`#assert_standard_axioms`
  plus exhaustive environment-wide verification across `LeanMiriSpec.*` and
  `Miri.*`).
-/
