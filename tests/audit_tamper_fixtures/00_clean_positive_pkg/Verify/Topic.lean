-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Trusted.VerificationResult
import Topic.Defs
import Topic.Proofs

namespace Verify.Topic

def itemIdentity : Trusted.VerificationResult.ArtifactIdentity :=
  { defPath := "topic::clean_item"
    mirDialect := "V2026_06_01"
    mirModuleSha256 := "0000000000000000000000000000000000000000000000000000000000000000" }

theorem verified :
    Trusted.VerificationResult.CrateVerificationResult
      { crateName := itemIdentity.defPath
        mirDialect := itemIdentity.mirDialect
        items := [{ identity := itemIdentity, certificate := Topic.Defs.claimTargetProp }] } :=
  Trusted.VerificationResult.mkPolyVerificationResult itemIdentity Topic.Proofs.cleanClaimProof

end Verify.Topic
