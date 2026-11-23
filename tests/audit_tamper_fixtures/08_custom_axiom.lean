-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- @fixture_id: 08_custom_axiom
-- @module_name: Specs.Tamper08
-- @expected_ok: false
-- @expected_category: forbiddenAxiom
-- @tamper_mode: compile

namespace Specs.Tamper08

-- V04: Unreferenced custom axiom in a Specs module (must still be rejected module-wide).
axiom unreferencedSpecAxiom : False

theorem cleanLookingSpecThm : True := True.intro

end Specs.Tamper08
