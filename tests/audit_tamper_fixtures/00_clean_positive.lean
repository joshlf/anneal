-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- @fixture_id: 00_clean_positive
-- @module_name: Proof.CleanPositive
-- @expected_ok: true
-- @expected_category: none
-- @tamper_mode: compile

namespace Proof.CleanPositive

-- Comments mentioning set_option debug.skipKernelTC true or native_decide must not false-positive.
/- Nested block comment /- unsafe partial bv_decide run_cmd -/ still safe. -/

def safeMessage : String := "escaped \" quote mentioning unsafe and skipKernelTC"
def safeQuoteChar : Char := '"'
def rawSafe : String := r#"set_option debug.skipKernelTC true"#
def x' : Nat := 1

def countdown : Nat → Nat
  | 0 => 0
  | n + 1 => countdown n

theorem kernelDecideOk : x' + 1 = 2 := by decide +kernel

mutual
theorem mutualCleanA : True := True.intro
theorem mutualCleanB : countdown 3 = 0 := rfl
end

mutual
opaque mutualOpaqueA : Nat := 1
opaque mutualOpaqueB : Nat := mutualOpaqueA
end

end Proof.CleanPositive
