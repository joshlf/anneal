-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- @fixture_id: 11_extern_override
-- @module_name: Proof.Tamper11
-- @expected_ok: false
-- @expected_category: forbiddenInitOrCodegenHook
-- @tamper_mode: compile

namespace Proof.Tamper11

@[extern "c_evil_extern_override"]
opaque externEscape : Unit → Nat

end Proof.Tamper11
