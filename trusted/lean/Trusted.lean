-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: vetted
prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Trusted.MirModel
import Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst
import Trusted.Rustc.V2026_05_31_R14210df0e.MirAst
import Trusted.Rustc.V2026_05_30_Rf8a08b688.MirAst
import Trusted.MirSemantics
