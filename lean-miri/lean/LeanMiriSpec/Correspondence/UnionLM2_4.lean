/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.UnionLM2_4Core
import LeanMiriSpec.Correspondence.UnionLM2_4Step
import LeanMiriSpec.Correspondence.UnionPaddedZstLM2_4

/-!
# Union and `Subslice` Hooks (`LM-2.4`, Umbrella Re-Export)

Re-exports the split `< 3,500`-LOC `LM-2.4` modules:
* `LeanMiriSpec.Correspondence.UnionLM2_4Core`: union layouts, projection
  contexts, operands/places, whole-value memory copies, `annealStepHooksLM2_4`,
  conservative extension, init-mask lemmas, and core allocation specs.
* `LeanMiriSpec.Correspondence.UnionLM2_4Step`: allocation overwrite/copy
  lemmas and the `LM-2.4` state/step relations (`UnionMemRel`, `UnionLocalRel`,
  `FrameRelLM2_4`, `StateRelLM2_4`, `StepRelLM2_4`).
* `LeanMiriSpec.Correspondence.UnionPaddedZstLM2_4`: padded `[(); N]` union ZST
  array arm relations, vendored `projectField`/`projectConstantIndex`
  projections, and vendored `Miri.Interpreter.ValidityVisitor.validatePlace`
  copy validation (`annealStepHooksLM2_4PaddedZst`).
-/
