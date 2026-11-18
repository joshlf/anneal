-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Captured
import SourceInputs

namespace ProductionReduction

open Trusted.MirModel Trusted.MirSemantics Anneal.MirWp Endianness

noncomputable abbrev sourceProgram : Program :=
  interpretV2026_10_22_R7189d39d9 Captured.program

noncomputable abbrev sourceBody : Body := sourceProgram.bodies[0]'(by decide)

noncomputable abbrev dataWidthVal (width : Nat) : Val :=
  bodyDataWidthVal sourceBody width

noncomputable abbrev endianArgs (toBe : Bool) (width : Nat) (value : Word) : List Val :=
  bodyEndianArgs sourceBody toBe width value

end ProductionReduction
