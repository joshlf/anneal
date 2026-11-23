-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- @fixture_id: 01_lean4_16677_key_mismatch_recursor
-- @module_name: Proof.Tamper01
-- @expected_ok: false
-- @expected_category: keyNameMismatch
-- @tamper_mode: forge_module_data:recursor_key_mismatch

namespace Proof.Tamper01

inductive T where
  | mk

theorem validWitness : True := True.intro

end Proof.Tamper01
