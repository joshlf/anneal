-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- @fixture_id: 10_implemented_by
-- @module_name: Proof.Tamper10
-- @expected_ok: false
-- @expected_category: forbiddenInitOrCodegenHook
-- @tamper_mode: compile

namespace Proof.Tamper10

def replacementZero : Nat := 0

@[implemented_by replacementZero]
def specOne : Nat := 1

end Proof.Tamper10
