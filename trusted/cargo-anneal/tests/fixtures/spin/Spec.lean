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

def specs : Trusted.Mvp.Specs := ⟨fun _ _ => False, fun program =>
  ∀ body, program.bodies[0]? = some body →
    ∀ args value, ¬Trusted.Mvp.Returns body args value⟩

end Spec
