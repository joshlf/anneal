-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- @fixture_id: 07_sorry_ax
-- @module_name: Proof.Tamper07
-- @expected_ok: false
-- @expected_category: forbiddenAxiom
-- @tamper_mode: compile

namespace Proof.Tamper07

-- V05: sorryAx hidden inside an opaque helper definition.
opaque hiddenWitness : False := sorryAx False false

theorem falseViaOpaqueHelper : False := hiddenWitness

end Proof.Tamper07
