/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/
import Trusted.Correspondence
import Anneal.Mir.Correspondence.Codec
import Anneal.Mir.Correspondence.LayoutQuery
import Anneal.Mir.Correspondence.MoveDeinit
import Anneal.Mir.Correspondence.Canaries

/-!
# Correspondence claims (`claim` module)

Each theorem below states *exactly* one top-level claim proposition defined in
the human-audited TCB module `Trusted.Correspondence`; every statement
references only `Trusted.Correspondence.*` constants, so
`TrustedBoundary.checkStatementOrigins` admits it, while the proofs live in the
untrusted `Anneal.Mir.Correspondence.*` modules.
-/

namespace Anneal.Mir.Correspondence.Claims

/-- The type-interning codec round-trips every program. -/
theorem codec_roundtrip_claim_holds : Trusted.Correspondence.CodecRoundtripClaim :=
  Anneal.Mir.Correspondence.codecRoundtripClaim_proof

/-- Demand-time layout queries correspond to deep resolution and fail closed. -/
theorem layout_query_correspondence_claim_holds :
    Trusted.Correspondence.LayoutQueryCorrespondenceClaim :=
  Anneal.Mir.Correspondence.layoutQueryCorrespondenceClaim_proof

/-- `M_ref` on `encodeProg p` steps and observes exactly like `M_anneal` on `p`. -/
theorem correspondence_claim_holds : Trusted.Correspondence.CorrespondenceClaim :=
  Anneal.Mir.Correspondence.correspondenceClaim_proof

/-- Every observation pole is reached by `M_anneal` iff by `M_ref`. -/
theorem fault_equivalence_claim_holds : Trusted.Correspondence.FaultEquivalenceClaim :=
  Anneal.Mir.Correspondence.faultEquivalenceClaim_proof

/-- The `deinitMovedPlace` latch wiring and its Tree Borrows silence. -/
theorem miri_move_deinit_wiring_claim_holds :
    Trusted.Correspondence.MiriMoveDeinitWiringClaim :=
  Anneal.Mir.Correspondence.miriMoveDeinitWiringClaim_proof

/-- The live Trusted `evalOperand` deinitializes projected and dereferenced
moves when `deinitProjectedMoves := true`. -/
theorem trusted_projected_move_deinit_claim_holds :
    Trusted.Correspondence.TrustedProjectedMoveDeinitClaim :=
  Anneal.Mir.Correspondence.trustedProjectedMoveDeinitClaim_proof

end Anneal.Mir.Correspondence.Claims
