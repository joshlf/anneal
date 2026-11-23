-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- @fixture_id: 17_reducibility_instance_override
-- @module_name: Proof.Tamper17
-- @expected_ok: false
-- @expected_category: forbiddenReducibilityOverride
-- @tamper_mode: compile

namespace Proof.Tamper17

set_option allowUnsafeReducibility true in
attribute [reducible] Nat.add

theorem trivialAfterOverride : True := True.intro

end Proof.Tamper17
