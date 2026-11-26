-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Anneal.OpaqueCalleeTable.TableAndPruning
import Anneal.OpaqueCalleeTable.FramesAndConeBridge

/-!
# `Anneal.OpaqueCalleeTable`

Umbrella module re-exporting every `Anneal.OpaqueCalleeTable.*` submodule; all declarations live
in namespace `Anneal.OpaqueCalleeTable`. The submodule split keeps each file within `3,500` lines
so it elaborates and kernel-replays under `-j1 -M2048`.

- `OpaqueCalleeTable.TableAndPruning`: `DecidableEq` without `BEq` on the trusted types, the
  `@[irreducible]` sealed table and its `O(1)` certificates, exact literal `switchInt` pruning
  (`tailCallWith` / `stepTerminatorWith`, verbatim copies of the trusted tail-call / call arms),
  fuel-bounded evaluation, demanded-key call-cone narrowing, and canary run summaries.
- `OpaqueCalleeTable.FramesAndConeBridge`: unconditional trusted frame lemmas, the
  unconditional opaque-evaluator identification, and the bridge to `Anneal.MirLiftCore`
  call-cone narrowing.

Concrete canaries, the heartbeat regression gate, and the module-wide axiom / namespace audit
live in `tests/mir/CompilerQueryAndOpaqueCalleeTests.lean`.
-/
