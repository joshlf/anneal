-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- @fixture_id: 12_unsafe_escape
-- @module_name: Proof.Tamper12
-- @expected_ok: false
-- @expected_category: unsafeOrPartialDecl
-- @tamper_mode: compile

namespace Proof.Tamper12

unsafe def unsafeEscapeFn : Nat := 0

def sneakyUnsafeTerm : Nat := unsafe (0 : Nat)

end Proof.Tamper12
