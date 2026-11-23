-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- @fixture_id: 06_custom_decide_config
-- @module_name: Proof.Tamper06
-- @expected_ok: false
-- @expected_category: forbiddenNativeReductionAxiom
-- @tamper_mode: compile_with_source

namespace Proof.Tamper06

-- Positional DecideConfig.mk (kernel := false, native := true, zetaReduce := true, revert := false)
-- emits `._native.decide.ax_1_1` without ever spelling the identifier `native`.
theorem positionalDecideEscape : 1 + 1 = 2 := by
  decide (config := ⟨false, true, true, false⟩)

end Proof.Tamper06
