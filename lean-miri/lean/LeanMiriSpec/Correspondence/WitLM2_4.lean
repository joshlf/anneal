/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.WitLM2_4Core
import LeanMiriSpec.Correspondence.WitLM2_4PaddedZst
import LeanMiriSpec.Correspondence.WitLM2_4TwoSided

/-!
# `LM-2.4` Union & Subslice Witnesses (Umbrella Re-Export)

Re-exports the split `< 3,500`-LOC `LM-2.4` witness modules:
* `LeanMiriSpec.Correspondence.WitLM2_4Core`: Sections 1-11 (scalar unions,
  whole-union copies/moves, `D13a` overlay, subslices, nested subslices).
* `LeanMiriSpec.Correspondence.WitLM2_4PaddedZst`: Section 12 concrete padded
  `[(); N]` ZST union witnesses and `lean-miri` step lemmas using vendored
  `projectField`/`projectConstantIndex` and vendored
  `Miri.Interpreter.ValidityVisitor.validatePlace`.
* `LeanMiriSpec.Correspondence.WitLM2_4TwoSided`: Section 12 two-sided general
  step simulation theorems (`R-a`) and the documented never-written union ZST
  read model boundary (`lm24_never_written_union_zst_read_boundary`, `R-b`).
-/
