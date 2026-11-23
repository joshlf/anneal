-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- @fixture_id: 03_const_names_size_mismatch
-- @module_name: Proof.Tamper03
-- @expected_ok: false
-- @expected_category: constNamesSizeMismatch
-- @tamper_mode: forge_module_data:const_names_size_mismatch

namespace Proof.Tamper03

theorem keptThm : True := True.intro
theorem truncatedThm : True := True.intro

end Proof.Tamper03
