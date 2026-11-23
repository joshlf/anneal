-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- @fixture_id: 05_of_reduce_bool_native_decide
-- @module_name: Proof.Tamper05
-- @expected_ok: false
-- @expected_category: forbiddenNativeReductionAxiom
-- @tamper_mode: compile

namespace Proof.Tamper05

theorem usesNativeDecide : 1 + 1 = 2 := by native_decide

end Proof.Tamper05
