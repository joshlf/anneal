-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- @fixture_id: 04_of_reduce_nat_axiom
-- @module_name: Proof.Tamper04
-- @expected_ok: false
-- @expected_category: forbiddenNativeReductionAxiom
-- @tamper_mode: compile

namespace Proof.Tamper04

set_option linter.deprecated false in
theorem usesOfReduceNat (h : Lean.reduceNat 2 = 2) : 2 = 2 :=
  Lean.ofReduceNat 2 2 h

end Proof.Tamper04
