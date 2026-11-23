-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- @fixture_id: 02_duplicate_const_names
-- @module_name: Proof.Tamper02
-- @expected_ok: false
-- @expected_category: duplicateConstName
-- @tamper_mode: forge_module_data:duplicate_const_names

namespace Proof.Tamper02

theorem sharedThm : True := True.intro

end Proof.Tamper02
