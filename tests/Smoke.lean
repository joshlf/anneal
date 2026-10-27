-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Anneal

namespace AnnealTests

/-- A claim theorem whose statement (`ci.type`) references only `Init.NotationExtra` /
`Trusted` constants (`True`), while its proof term (`ci.value?`) uses the
untrusted `Anneal.trivial_witness` lemma from `theory/`. -/
theorem smoke_claim : True := Anneal.trivial_witness

end AnnealTests
