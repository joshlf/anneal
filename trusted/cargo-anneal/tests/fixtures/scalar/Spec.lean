-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted.Mvp

namespace Spec

open Trusted.Mvp

def returnsZero (program : Program) : Prop :=
  ∀ body, program.bodies[0]? = some body →
    ∀ value, Returns body [] value → value = 0

def specs : Specs := ⟨fun _ _ => False, returnsZero⟩

end Spec
