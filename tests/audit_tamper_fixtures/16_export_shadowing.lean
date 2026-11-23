-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- @fixture_id: 16_export_shadowing
-- @module_name: Proof.Tamper16
-- @expected_ok: false
-- @expected_category: forbiddenShadowingOrExport
-- @tamper_mode: compile

namespace Proof.Tamper16

namespace Hidden
def sneakyVal : Nat := 99
end Hidden

export Hidden (sneakyVal)

def Nat.add (a _b : _root_.Nat) : _root_.Nat := a

end Proof.Tamper16
