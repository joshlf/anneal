-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted

namespace Anneal

/-- Placeholder proof helper in the untrusted `Anneal` library. Theorems in
`tests/` or crate `Proof/` modules may reference `Anneal` declarations inside
their proof terms (`ci.value?`), never in their theorem statements (`ci.type`). -/
theorem trivial_witness : True := True.intro

end Anneal
