-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- @fixture_id: 14_macro_elaborator_hijack
-- @module_name: Proof.Tamper14
-- @expected_ok: false
-- @expected_category: forbiddenMacroOrElab
-- @tamper_mode: compile

namespace Proof.Tamper14

macro "audit_hijack_token" : term => `(True.intro)

theorem looksClean : True := audit_hijack_token

end Proof.Tamper14
