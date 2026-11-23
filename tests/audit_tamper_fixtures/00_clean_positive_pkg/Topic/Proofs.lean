-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Topic.Defs
import Anneal.TheoryHelper

namespace Topic.Proofs

-- Comments mentioning native_decide or set_option debug.skipKernelTC true are safe.
def quoteCh : Char := '"'
def strWithEscape : String := "safe \"escaped\" text"

theorem cleanClaimProof : Topic.Defs.claimTargetProp := by
  have _ : True := Anneal.TheoryHelper.helperLemma
  rfl

mutual
theorem mutThmA : True := True.intro
theorem mutThmB : Topic.Defs.claimTargetProp := cleanClaimProof
end

end Topic.Proofs
