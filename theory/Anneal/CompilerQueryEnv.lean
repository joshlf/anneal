-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Anneal.CompilerQueryEnv.EnvAndLayoutBridges
import Anneal.CompilerQueryEnv.DynDispatch

/-!
# `Anneal.CompilerQueryEnv`

Umbrella module re-exporting every `Anneal.CompilerQueryEnv.*` submodule; all declarations live
in namespace `Anneal.CompilerQueryEnv`. The submodule split keeps each file within `3,500` lines
so it elaborates and kernel-replays under `-j1 -M2048`.

- `CompilerQueryEnv.EnvAndLayoutBridges`: `DecidableEq` without `BEq` on the V2026_08_01
  types, schemas and evidence, the V2026_06_01 / V2026_08_01 layout and `RigidTy` bridges
  (exact up to the V2026_06_01-only explicit variant discriminants), the finite-material
  environment, its five query families, and environment extension.
- `CompilerQueryEnv.DynDispatch`: end-to-end receiver-driven dynamic dispatch, demand-gated
  dynamic call steps, the multi-site `DynCallRegistry`, and certificate-driven
  dynamic-dispatch cone narrowing.

Concrete canaries, axiom pins, and the module-wide axiom / namespace audit live in
`tests/mir/CompilerQueryAndOpaqueCalleeTests.lean`.
-/
