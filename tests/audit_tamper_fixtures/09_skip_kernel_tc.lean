-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- @fixture_id: 09_skip_kernel_tc
-- @module_name: Proof.Tamper09
-- @expected_ok: false
-- @expected_category: forbiddenSourceOption
-- @tamper_mode: forge_module_data:skip_kernel_tc_and_ill_typed

namespace Proof.Tamper09

set_option debug.skipKernelTC true in
theorem skippedKernelCheck : True := True.intro

end Proof.Tamper09
