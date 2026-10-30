-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Anneal

namespace AnnealTests

/-- Trivial language over `Unit` used by the Layer 1 smoke claim. -/
def smokeLang : Trusted.Language where
  Prog := Unit
  Query := Unit
  Out := Unit
  sem _ _ := Trusted.Partial.pure (fun _ => True)

/-- Identity compiler on `smokeLang`. -/
def smokeCompiler : Trusted.Compiler smokeLang smokeLang where
  compile p := p
  π b := b

/-- Trivial trusted-assumption type for `smoke_claim`. -/
inductive SmokeAssumption where
  | compilerOk

instance instTrustedAssumptionSmoke : Trusted.TrustedAssumption SmokeAssumption where
  meaning
    | .compilerOk => smokeCompiler.SoundOn ()

/-- Trust policy permitting `SmokeAssumption.compilerOk`. -/
def smokePolicy : Trusted.TrustPolicy SmokeAssumption where
  isAllowed
    | .compilerOk => True

/-- A claim theorem whose statement (`ci.type`) references only `Trusted`,
    file-local definitions, and `Init.NotationExtra` constants, while its proof
    term (`ci.value?`) discharges the obligation through
    `Anneal.verify_through_passes` in `theory/`. -/
theorem smoke_claim :
    Trusted.VerificationResult
      smokeCompiler
      smokePolicy
      [.compilerOk]
      ()
      [] := by
  refine ⟨⟨True.intro, True.intro⟩, ?_⟩
  intro hAssumptions
  exact ⟨Anneal.verify_through_passes
    (L_v := smokeLang)
    (C := smokeCompiler)
    (π_v := fun b => b)
    (Trusted.Preorder.le_refl _)
    (Trusted.Preorder.le_refl _)
    Anneal.monotone_id
    hAssumptions.1, True.intro⟩

end AnnealTests
