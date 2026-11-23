-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- @fixture_id: 18_mutual_all_hidden_axiom
-- @module_name: Proof.Tamper18
-- @expected_ok: false
-- @expected_category: forbiddenAxiom
-- @tamper_mode: compile

namespace Proof.Tamper18

mutual
theorem cleanFront : True := True.intro
theorem hiddenSorrySibling : False := sorryAx False false
end

end Proof.Tamper18
