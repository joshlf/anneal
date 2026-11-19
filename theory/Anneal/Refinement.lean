import Trusted

namespace Anneal.Refinement

open Trusted.Refinement

export Trusted.Refinement (
  instTransLE
  instLEProp
  instIsPartialOrderProp
  instLEFun
  instIsPreorderFun
  instIsPartialOrderFun
  Semantics
  Spec
  Monotone
  GuardedRefines
  BehaviorSet
  Partial
  instLEPartial
  instIsPreorderPartial
  instIsPartialOrderPartial
  Language
  Compiles
  Abstracts
  Compiler
  TrustedAssumption
  TrustPolicy
  AllHold
  VerificationResultOn
)

/-!
Derived refinement algebra, pass specializations (`VerifierPass`,
`CompilerPass`, `BugFinderPass`, `SanitizerPass`, `ExactPass`), `Partial` and
`Language` laws, and the Y-diagram soundness theorems (`y_diagram_sound`,
`anneal_is_correct`, `verify_on_through_passes`, `verify_through_passes`) built
on Lean's standard order classes (`LE`, `Std.IsPreorder`, `Std.IsPartialOrder`)
and `Trusted.Refinement` (`#100` §3–§4, `#103` §1).

The final section adds gap-preserving outcome and program equivalence
(`OutcomeWithGap`, `GapEqErr`, `GapForbidEq`, `OutcomeSetEquiv`, `ContextEquiv`,
`ProgramEquiv`, `ContextEquiv.toProgramEquiv`) together with its bridges to
`Partial`, `Language`, and the pass specializations.
-/

theorem monotone_id {Behavior : Type u} [LE Behavior] :
    Monotone (fun b : Behavior => b) :=
  fun _ _ h => h

theorem Monotone.comp {BehA : Type u} {BehB : Type v} {BehC : Type w}
    [LE BehA] [LE BehB] [LE BehC]
    {π₁ : BehB → BehC} {π₂ : BehA → BehB}
    (h₁ : Monotone π₁) (h₂ : Monotone π₂) :
    Monotone (fun b => π₁ (π₂ b)) :=
  fun _ _ h => h₁ (h₂ h)

/-- Trivial specification holding for all behaviors. -/
def Spec.top {Behavior : Type u} [LE Behavior] : Spec Behavior where
  holds _ := True
  downward_closed _ _ _ _ := trivial

/-- Conjunction of downward-closed specifications. -/
def Spec.and {Behavior : Type u} [LE Behavior]
    (P Q : Spec Behavior) : Spec Behavior where
  holds b := P.holds b ∧ Q.holds b
  downward_closed _ _ h_ref h :=
    ⟨P.downward_closed h_ref h.1, Q.downward_closed h_ref h.2⟩

/-- Re-export pullback of specifications along monotone observation maps. -/
abbrev Spec.pullback {BehHigh : Type u} {BehLow : Type v}
    [LE BehHigh] [LE BehLow]
    {π : BehHigh → BehLow} (h_mono : Monotone π)
    (S : Spec BehLow) : Spec BehHigh :=
  Trusted.Refinement.Spec.pullback h_mono S

/-- Negations of downward-closed specifications lift counterexamples upward. -/
theorem Spec.counterexample_upward {Behavior : Type u} [LE Behavior]
    (S : Spec Behavior) {b_low b_high : Behavior}
    (h_ref : b_low ≤ b_high) (h_cex : ¬ S.holds b_low) :
    ¬ S.holds b_high :=
  fun h_high => h_cex (S.downward_closed h_ref h_high)

theorem GuardedRefines.refl {Behavior : Type u}
    [LE Behavior] [Std.IsPreorder Behavior]
    (G : Spec Behavior) (b : Behavior) :
    GuardedRefines G id b b :=
  fun _ => Std.le_refl b

/-- Compose two guarded refinements across an intermediate behavior `b_mid`. -/
theorem GuardedRefines.trans
    {BehLow : Type u} {BehMid : Type v} {BehHigh : Type w}
    [LE BehLow] [Std.IsPreorder BehLow] [LE BehMid] [LE BehHigh]
    {G₁ : Spec BehMid} {G₂ : Spec BehHigh}
    {π₁ : BehMid → BehLow} {π₂ : BehHigh → BehMid}
    {b_low : BehLow} {b_mid : BehMid} {b_high : BehHigh}
    (h_low : GuardedRefines G₁ π₁ b_low b_mid)
    (h_high : GuardedRefines G₂ π₂ b_mid b_high)
    (h_mono : Monotone π₁)
    (h_guard : ∀ ⦃b_m b_h⦄, G₂.holds b_h → b_m ≤ π₂ b_h → G₁.holds b_m) :
    GuardedRefines G₂ (fun b => π₁ (π₂ b)) b_low b_high :=
  fun hg₂ =>
    calc b_low
      _ ≤ π₁ b_mid        := h_low (h_guard hg₂ (h_high hg₂))
      _ ≤ π₁ (π₂ b_high)  := h_mono (h_high hg₂)

/-- Transfer any downward-closed specification once the guard is discharged. -/
theorem GuardedRefines.transfer
    {BehLow : Type u} {BehHigh : Type v}
    [LE BehLow] [LE BehHigh]
    {G : Spec BehHigh} {π : BehHigh → BehLow}
    {b_low : BehLow} {b_high : BehHigh}
    (h_ref : GuardedRefines G π b_low b_high)
    (h_guard : G.holds b_high)
    (spec : Spec BehLow)
    (h_spec : spec.holds (π b_high)) :
    spec.holds b_low :=
  spec.downward_closed (h_ref h_guard) h_spec

/-! ## Five Specializations of `GuardedRefines` -/

/-- Verifier pass `p₁ ↦ p₂`: `S₁ p₁ ≤ π_v (S₂ p₂)` under guard `G₂` on `S₂ p₂`. -/
def VerifierPass {Prog₁ : Type u₁} {Prog₂ : Type u₂}
    {Beh₁ : Type v₁} {Beh₂ : Type v₂} [LE Beh₁] [LE Beh₂]
    (S₁ : Semantics Prog₁ Beh₁) (S₂ : Semantics Prog₂ Beh₂)
    (G₂ : Spec Beh₂) (π_v : Beh₂ → Beh₁)
    (p₁ : Prog₁) (p₂ : Prog₂) : Prop :=
  GuardedRefines G₂ π_v (S₁ p₁) (S₂ p₂)

theorem VerifierPass.transfer
    {Prog₁ : Type u₁} {Prog₂ : Type u₂}
    {Beh₁ : Type v₁} {Beh₂ : Type v₂} [LE Beh₁] [LE Beh₂]
    {S₁ : Semantics Prog₁ Beh₁} {S₂ : Semantics Prog₂ Beh₂}
    {G₂ : Spec Beh₂} {π_v : Beh₂ → Beh₁} {p₁ : Prog₁} {p₂ : Prog₂}
    (h_pass : VerifierPass S₁ S₂ G₂ π_v p₁ p₂)
    (h_guard : G₂.holds (S₂ p₂))
    (spec : Spec Beh₁)
    (h_spec : spec.holds (π_v (S₂ p₂))) :
    spec.holds (S₁ p₁) :=
  GuardedRefines.transfer h_pass h_guard spec h_spec

theorem VerifierPass.reflect_guard
    {Prog₁ : Type u₁} {Prog₂ : Type u₂}
    {Beh₁ : Type v₁} {Beh₂ : Type v₂} [LE Beh₁] [LE Beh₂]
    {S₁ : Semantics Prog₁ Beh₁} {S₂ : Semantics Prog₂ Beh₂}
    {G₁ : Spec Beh₁} {G₂ : Spec Beh₂} {π_v : Beh₂ → Beh₁}
    {p₁ : Prog₁} {p₂ : Prog₂}
    (h_pass : VerifierPass S₁ S₂ G₂ π_v p₁ p₂)
    (h_preserve : G₂.holds (S₂ p₂) → G₁.holds (π_v (S₂ p₂)))
    (h_g₂ : G₂.holds (S₂ p₂)) :
    G₁.holds (S₁ p₁) :=
  G₁.downward_closed (h_pass h_g₂) (h_preserve h_g₂)

theorem VerifierPass.comp
    {Prog₁ : Type u₁} {Prog₂ : Type u₂} {Prog₃ : Type u₃}
    {Beh₁ : Type v₁} {Beh₂ : Type v₂} {Beh₃ : Type v₃}
    [LE Beh₁] [Std.IsPreorder Beh₁] [LE Beh₂] [LE Beh₃]
    {S₁ : Semantics Prog₁ Beh₁} {S₂ : Semantics Prog₂ Beh₂}
    {S₃ : Semantics Prog₃ Beh₃}
    {G₂ : Spec Beh₂} {G₃ : Spec Beh₃}
    {π₁ : Beh₂ → Beh₁} {π₂ : Beh₃ → Beh₂}
    {p₁ : Prog₁} {p₂ : Prog₂} {p₃ : Prog₃}
    (h₁ : VerifierPass S₁ S₂ G₂ π₁ p₁ p₂)
    (h₂ : VerifierPass S₂ S₃ G₃ π₂ p₂ p₃)
    (h_mono : Monotone π₁)
    (h_guard : ∀ ⦃b_m b_h⦄, G₃.holds b_h → b_m ≤ π₂ b_h → G₂.holds b_m) :
    VerifierPass S₁ S₃ G₃ (fun b => π₁ (π₂ b)) p₁ p₃ :=
  GuardedRefines.trans h₁ h₂ h_mono h_guard

/-- Compiler pass `p₁ ↦ p₂`: `S₂ p₂ ≤ π_c (S₁ p₁)` under guard `G₁` on `S₁ p₁`. -/
def CompilerPass {Prog₁ : Type u₁} {Prog₂ : Type u₂}
    {Beh₁ : Type v₁} {Beh₂ : Type v₂} [LE Beh₁] [LE Beh₂]
    (S₁ : Semantics Prog₁ Beh₁) (S₂ : Semantics Prog₂ Beh₂)
    (G₁ : Spec Beh₁) (π_c : Beh₁ → Beh₂)
    (p₁ : Prog₁) (p₂ : Prog₂) : Prop :=
  GuardedRefines G₁ π_c (S₂ p₂) (S₁ p₁)

theorem CompilerPass.comp
    {Prog₁ : Type u₁} {Prog₂ : Type u₂} {Prog₃ : Type u₃}
    {Beh₁ : Type v₁} {Beh₂ : Type v₂} {Beh₃ : Type v₃}
    [LE Beh₁] [LE Beh₂] [LE Beh₃] [Std.IsPreorder Beh₃]
    {S₁ : Semantics Prog₁ Beh₁} {S₂ : Semantics Prog₂ Beh₂}
    {S₃ : Semantics Prog₃ Beh₃}
    {G₁ : Spec Beh₁} {G₂ : Spec Beh₂}
    {π₁ : Beh₁ → Beh₂} {π₂ : Beh₂ → Beh₃}
    {p₁ : Prog₁} {p₂ : Prog₂} {p₃ : Prog₃}
    (h₁ : CompilerPass S₁ S₂ G₁ π₁ p₁ p₂)
    (h₂ : CompilerPass S₂ S₃ G₂ π₂ p₂ p₃)
    (h_mono : Monotone π₂)
    (h_guard : ∀ ⦃b_m b_h⦄, G₁.holds b_h → b_m ≤ π₁ b_h → G₂.holds b_m) :
    CompilerPass S₁ S₃ G₁ (fun b => π₂ (π₁ b)) p₁ p₃ :=
  GuardedRefines.trans h₂ h₁ h_mono h_guard

/-- Bug-finder pass `p₁ ↦ p₂`: unconditional under-approximation `S₂ p₂ ≤ π_b (S₁ p₁)`. -/
def BugFinderPass {Prog₁ : Type u₁} {Prog₂ : Type u₂}
    {Beh₁ : Type v₁} {Beh₂ : Type v₂} [LE Beh₁] [LE Beh₂]
    (S₁ : Semantics Prog₁ Beh₁) (S₂ : Semantics Prog₂ Beh₂)
    (π_b : Beh₁ → Beh₂) (p₁ : Prog₁) (p₂ : Prog₂) : Prop :=
  GuardedRefines Spec.top π_b (S₂ p₂) (S₁ p₁)

theorem BugFinderPass.lift_counterexample
    {Prog₁ : Type u₁} {Prog₂ : Type u₂}
    {Beh₁ : Type v₁} {Beh₂ : Type v₂} [LE Beh₁] [LE Beh₂]
    {S₁ : Semantics Prog₁ Beh₁} {S₂ : Semantics Prog₂ Beh₂}
    {π_b : Beh₁ → Beh₂} {p₁ : Prog₁} {p₂ : Prog₂}
    (h_bug : BugFinderPass S₁ S₂ π_b p₁ p₂)
    (spec : Spec Beh₂)
    (h_found : ¬ spec.holds (S₂ p₂)) :
    ¬ spec.holds (π_b (S₁ p₁)) :=
  Spec.counterexample_upward spec (h_bug trivial) h_found

/-- Sanitizer pass `p₁ ↦ p₂`: maps UB in `Beh₁` to defined abort in `Beh₂`. -/
def SanitizerPass {Prog₁ : Type u₁} {Prog₂ : Type u₂}
    {Beh₁ : Type v₁} {Beh₂ : Type v₂} [LE Beh₁] [LE Beh₂]
    (S₁ : Semantics Prog₁ Beh₁) (S₂ : Semantics Prog₂ Beh₂)
    (ubToAbort : Beh₁ → Beh₂) (p₁ : Prog₁) (p₂ : Prog₂) : Prop :=
  GuardedRefines Spec.top ubToAbort (S₂ p₂) (S₁ p₁)

theorem SanitizerPass.unconditional_safety
    {Prog₁ : Type u₁} {Prog₂ : Type u₂}
    {Beh₁ : Type v₁} {Beh₂ : Type v₂} [LE Beh₁] [LE Beh₂]
    {S₁ : Semantics Prog₁ Beh₁} {S₂ : Semantics Prog₂ Beh₂}
    {ubToAbort : Beh₁ → Beh₂} {p₁ : Prog₁} {p₂ : Prog₂}
    (h_san : SanitizerPass S₁ S₂ ubToAbort p₁ p₂)
    (NoUB₂ : Spec Beh₂)
    (h_abort_safe : NoUB₂.holds (ubToAbort (S₁ p₁))) :
    NoUB₂.holds (S₂ p₂) :=
  NoUB₂.downward_closed (h_san trivial) h_abort_safe

/-- Exact pass `p₁ ↦ p₂`: unconditional mutual refinement. -/
structure ExactPass {Prog₁ : Type u₁} {Prog₂ : Type u₂}
    {Beh₁ : Type v₁} {Beh₂ : Type v₂} [LE Beh₁] [LE Beh₂]
    (S₁ : Semantics Prog₁ Beh₁) (S₂ : Semantics Prog₂ Beh₂)
    (π_fwd : Beh₁ → Beh₂) (π_bwd : Beh₂ → Beh₁)
    (p₁ : Prog₁) (p₂ : Prog₂) : Prop where
  up_refines : GuardedRefines Spec.top π_bwd (S₁ p₁) (S₂ p₂)
  down_refines : GuardedRefines Spec.top π_fwd (S₂ p₂) (S₁ p₁)

theorem ExactPass.toVerifierPass
    {Prog₁ : Type u₁} {Prog₂ : Type u₂}
    {Beh₁ : Type v₁} {Beh₂ : Type v₂} [LE Beh₁] [LE Beh₂]
    {S₁ : Semantics Prog₁ Beh₁} {S₂ : Semantics Prog₂ Beh₂}
    {π_fwd : Beh₁ → Beh₂} {π_bwd : Beh₂ → Beh₁} {p₁ : Prog₁} {p₂ : Prog₂}
    (h_exact : ExactPass S₁ S₂ π_fwd π_bwd p₁ p₂) (G₂ : Spec Beh₂) :
    VerifierPass S₁ S₂ G₂ π_bwd p₁ p₂ :=
  fun _ => h_exact.up_refines trivial

theorem ExactPass.toCompilerPass
    {Prog₁ : Type u₁} {Prog₂ : Type u₂}
    {Beh₁ : Type v₁} {Beh₂ : Type v₂} [LE Beh₁] [LE Beh₂]
    {S₁ : Semantics Prog₁ Beh₁} {S₂ : Semantics Prog₂ Beh₂}
    {π_fwd : Beh₁ → Beh₂} {π_bwd : Beh₂ → Beh₁} {p₁ : Prog₁} {p₂ : Prog₂}
    (h_exact : ExactPass S₁ S₂ π_fwd π_bwd p₁ p₂) (G₁ : Spec Beh₁) :
    CompilerPass S₁ S₂ G₁ π_fwd p₁ p₂ :=
  fun _ => h_exact.down_refines trivial

theorem ExactPass.toBugFinderPass
    {Prog₁ : Type u₁} {Prog₂ : Type u₂}
    {Beh₁ : Type v₁} {Beh₂ : Type v₂} [LE Beh₁] [LE Beh₂]
    {S₁ : Semantics Prog₁ Beh₁} {S₂ : Semantics Prog₂ Beh₂}
    {π_fwd : Beh₁ → Beh₂} {π_bwd : Beh₂ → Beh₁} {p₁ : Prog₁} {p₂ : Prog₂}
    (h_exact : ExactPass S₁ S₂ π_fwd π_bwd p₁ p₂) :
    BugFinderPass S₁ S₂ π_fwd p₁ p₂ :=
  h_exact.down_refines

/-! ## Abstract Y-Diagram Soundness Theorems -/

/-- Join compiler branch (`p_mid ↦ p_tgt`) and verifier branch (`p_mid ↦ p_verif`). -/
theorem y_diagram_sound
    {MidProg : Type u₁} {VerifProg : Type u₂} {TgtProg : Type u₃}
    {MidBeh : Type v₁} {VerifBeh : Type v₂} {TgtBeh : Type v₃}
    [LE MidBeh] [LE VerifBeh] [LE TgtBeh] [Std.IsPreorder TgtBeh]
    (MidSem : Semantics MidProg MidBeh)
    (VerifSem : Semantics VerifProg VerifBeh)
    (TgtSem : Semantics TgtProg TgtBeh)
    (G_mid : Spec MidBeh) (G_verif : Spec VerifBeh)
    (π_c : MidBeh → TgtBeh) (π_v : VerifBeh → MidBeh)
    (h_mono_c : Monotone π_c)
    {p_mid : MidProg} {p_verif : VerifProg} {p_tgt : TgtProg}
    (h_compile : CompilerPass MidSem TgtSem G_mid π_c p_mid p_tgt)
    (h_verif : VerifierPass MidSem VerifSem G_verif π_v p_mid p_verif)
    (h_reflect : ∀ ⦃b_v⦄, G_verif.holds b_v → G_mid.holds (π_v b_v))
    (h_safe_verif : G_verif.holds (VerifSem p_verif))
    (spec : Spec TgtBeh)
    (h_spec_verif : spec.holds (π_c (π_v (VerifSem p_verif)))) :
    spec.holds (TgtSem p_tgt) ∧ G_mid.holds (MidSem p_mid) := by
  have h_mid_safe : G_mid.holds (MidSem p_mid) :=
    VerifierPass.reflect_guard h_verif (@h_reflect (VerifSem p_verif)) h_safe_verif
  have h_joined :=
    GuardedRefines.trans h_compile h_verif h_mono_c
      (fun _ _ h_gv h_ref => G_mid.downward_closed h_ref (h_reflect h_gv))
  exact ⟨GuardedRefines.transfer h_joined h_safe_verif spec h_spec_verif, h_mid_safe⟩

/-- End-to-end Y-diagram theorem from capture artifact to target machine. -/
theorem anneal_is_correct
    {Artifact : Type u₀} {MirProgram : Type u₁}
    {VerifProgram : Type u₂} {TgtProgram : Type u₃}
    {MirBeh : Type v₁} {VerifBeh : Type v₂} {TgtBeh : Type v₃}
    [LE MirBeh] [LE VerifBeh] [LE TgtBeh] [Std.IsPreorder TgtBeh]
    (MirSem : Semantics MirProgram MirBeh)
    (VerifSem : Semantics VerifProgram VerifBeh)
    (T : Semantics TgtProgram TgtBeh)
    (MirNoUB : Spec MirBeh) (VerifNoUB : Spec VerifBeh)
    (parseCapture : Artifact → Option MirProgram)
    (compile : MirProgram → TgtProgram)
    (π_c : MirBeh → TgtBeh)
    (h_mono_c : Monotone π_c)
    (h_rustc : ∀ p, CompilerPass MirSem T MirNoUB π_c p (compile p))
    (artifact : Artifact) (p : MirProgram) (p_verif : VerifProgram)
    (π_v : VerifBeh → MirBeh)
    (_h_capture : parseCapture artifact = some p)
    (h_passes : VerifierPass MirSem VerifSem VerifNoUB π_v p p_verif)
    (h_reflect_noUB : ∀ ⦃b_v⦄, VerifNoUB.holds b_v → MirNoUB.holds (π_v b_v))
    (h_noUB_v : VerifNoUB.holds (VerifSem p_verif))
    (spec : Spec TgtBeh)
    (h_spec_v : spec.holds (π_c (π_v (VerifSem p_verif)))) :
    spec.holds (T (compile p)) :=
  (y_diagram_sound MirSem VerifSem T MirNoUB VerifNoUB π_c π_v h_mono_c
    (h_rustc p) h_passes h_reflect_noUB h_noUB_v spec h_spec_v).1

/-! ## `BehaviorSet`, `Partial`, and `Language` Refinement Laws -/

theorem BehaviorSet.map_monotone {α : Type u} {β : Type v} (f : α → β) :
    Monotone (BehaviorSet.map f) :=
  fun _ _ h_ref _ ⟨x, hx, hfy⟩ => ⟨x, h_ref x hx, hfy⟩

theorem Partial.map_monotone {B₁ : Type u} {B₂ : Type v}
    [LE B₁] [LE B₂] {f : B₁ → B₂} (hf : Monotone f) :
    Monotone (Partial.map f) :=
  fun _ _ h_ref h₂ =>
    let ⟨h₁, hle⟩ := h_ref h₂
    ⟨h₁, hf hle⟩

/-- `Partial.ub` is the top element `⊤` of `Partial B`. -/
@[simp]
theorem Partial.ub_top {B : Type u} [LE B] (p : Partial B) :
    p ≤ Partial.ub :=
  fun h => False.elim h

/-- On `Partial.pure` values, `Partial` refinement reduces to `B`. -/
@[simp]
theorem Partial.pure_le_pure_iff {B : Type u} [LE B] (b₁ b₂ : B) :
    Partial.pure b₁ ≤ Partial.pure b₂ ↔ b₁ ≤ b₂ :=
  ⟨fun h => (h trivial).2, fun h _ => ⟨trivial, h⟩⟩

theorem Partial.pure_refines_pure_iff {B : Type u} [LE B] (b₁ b₂ : B) :
    Partial.pure b₁ ≤ Partial.pure b₂ ↔ b₁ ≤ b₂ :=
  Partial.pure_le_pure_iff b₁ b₂

/-- `Partial.ub` never refines `Partial.pure b`. -/
theorem Partial.not_ub_refines_pure {B : Type u} [LE B] (b : B) :
    ¬ ((@Partial.ub B) ≤ Partial.pure b) :=
  fun h => (h trivial).1

theorem Language.refines_wellFormedOn_iff {L : Language}
    (b : L.Behavior) (safetyPre : L.Query → Prop) :
    b ≤ L.WellFormedOn safetyPre ↔ ∀ q, safetyPre q → (b q).defined :=
  ⟨fun h q h_pre => (h q h_pre).1,
   fun h q h_pre => ⟨h q h_pre, fun _ _ => trivial⟩⟩

theorem Language.refines_wellFormed_iff {L : Language} (b : L.Behavior) :
    b ≤ L.WellFormed ↔ ∀ q, (b q).defined :=
  ⟨fun h q => (h q trivial).1, fun h q _ => ⟨h q, fun _ _ => trivial⟩⟩

theorem Language.wellFormed_refines_wellFormedOn {L : Language}
    (safetyPre : L.Query → Prop) :
    L.WellFormed ≤ L.WellFormedOn safetyPre :=
  fun _ _ => ⟨trivial, fun _ _ => trivial⟩

theorem Language.contractSpec_refines_wellFormedOn {L : Language}
    (safetyPre funcPre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    L.ContractSpec safetyPre funcPre post ≤ L.WellFormedOn safetyPre :=
  fun _ h_pre => ⟨h_pre, fun _ _ => trivial⟩

theorem Language.contractSpec_safe_refines_wellFormed {L : Language}
    (funcPre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    L.ContractSpec (fun _ => True) funcPre post ≤ L.WellFormed :=
  Language.contractSpec_refines_wellFormedOn (fun _ => True) funcPre post

/-- Unguarded composition across monotone observation map `π₁`. -/
theorem pass_trans
    {BehLow : Type u} {BehMid : Type v} {BehHigh : Type w}
    [LE BehLow] [Std.IsPreorder BehLow] [LE BehMid] [LE BehHigh]
    {π₁ : BehMid → BehLow} {π₂ : BehHigh → BehMid}
    {b_low : BehLow} {b_mid : BehMid} {b_high : BehHigh}
    (h_low : b_low ≤ π₁ b_mid)
    (h_high : b_mid ≤ π₂ b_high)
    (h_mono : Monotone π₁) :
    b_low ≤ π₁ (π₂ b_high) :=
  calc b_low
    _ ≤ π₁ b_mid       := h_low
    _ ≤ π₁ (π₂ b_high) := h_mono h_high

theorem Compiles.comp
    {L₁ L₂ L₃ : Language}
    {π₁ : L₁.Behavior → L₂.Behavior} {π₂ : L₂.Behavior → L₃.Behavior}
    {p₁ : L₁.Prog} {p₂ : L₂.Prog} {p₃ : L₃.Prog}
    (h₁ : Compiles L₁ L₂ π₁ p₁ p₂)
    (h₂ : Compiles L₂ L₃ π₂ p₂ p₃)
    (h_mono : Monotone π₂) :
    Compiles L₁ L₃ (fun b => π₂ (π₁ b)) p₁ p₃ :=
  pass_trans h₂ h₁ h_mono

theorem Abstracts.comp
    {L₁ L₂ L₃ : Language}
    {π₁ : L₂.Behavior → L₁.Behavior} {π₂ : L₃.Behavior → L₂.Behavior}
    {p₁ : L₁.Prog} {p₂ : L₂.Prog} {p₃ : L₃.Prog}
    (h₁ : Abstracts L₂ L₁ π₁ p₂ p₁)
    (h₂ : Abstracts L₃ L₂ π₂ p₃ p₂)
    (h_mono : Monotone π₁) :
    Abstracts L₃ L₁ (fun b => π₁ (π₂ b)) p₃ p₁ :=
  pass_trans h₁ h₂ h_mono

/-- End-to-end Y-diagram theorem on `Language` under `safetyPre`. -/
theorem verify_on_through_passes
    {L_src L_v L_tgt : Language}
    {π_c : L_src.Behavior → L_tgt.Behavior}
    {π_v : L_v.Behavior → L_src.Behavior}
    (h_mono_c : Monotone π_c)
    (h_mono_v : Monotone π_v)
    {s : L_src.Prog} {v : L_v.Prog} {t : L_tgt.Prog}
    (h_compile : Compiles L_src L_tgt π_c s t)
    (h_abstract : Abstracts L_v L_src π_v v s)
    {spec : L_v.Behavior}
    (h_spec : L_v.sem v ≤ spec)
    {safetyPre : L_src.Query → Prop}
    (h_wf_spec : π_v spec ≤ L_src.WellFormedOn safetyPre) :
    L_src.sem s ≤ L_src.WellFormedOn safetyPre ∧
      L_tgt.sem t ≤ π_c (π_v spec) :=
  have h_src_spec : L_src.sem s ≤ π_v spec :=
    pass_trans (π₂ := id) h_abstract h_spec h_mono_v
  ⟨Std.le_trans h_src_spec h_wf_spec, pass_trans h_compile h_src_spec h_mono_c⟩

/-- End-to-end Y-diagram theorem on `Language` for unconditionally safe specs. -/
theorem verify_through_passes
    {L_src L_v L_tgt : Language}
    {π_c : L_src.Behavior → L_tgt.Behavior}
    {π_v : L_v.Behavior → L_src.Behavior}
    (h_mono_c : Monotone π_c)
    (h_mono_v : Monotone π_v)
    {s : L_src.Prog} {v : L_v.Prog} {t : L_tgt.Prog}
    (h_compile : Compiles L_src L_tgt π_c s t)
    (h_abstract : Abstracts L_v L_src π_v v s)
    {spec : L_v.Behavior}
    (h_spec : L_v.sem v ≤ spec)
    (h_wf_spec : π_v spec ≤ L_src.WellFormed) :
    L_src.sem s ≤ L_src.WellFormed ∧ L_tgt.sem t ≤ π_c (π_v spec) :=
  verify_on_through_passes h_mono_c h_mono_v h_compile h_abstract h_spec h_wf_spec

theorem Compiler.SoundOn.verify
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt} {s : L_src.Prog} {spec : L_src.Behavior}
    (h_sound : C.SoundOn s) (h_src : L_src.sem s ≤ spec) :
    C.Verified s spec :=
  ⟨h_src, h_sound.2, pass_trans (π₂ := id) h_sound.2 h_src h_sound.1⟩

theorem verifyResultOn_single
    {L_src L_tgt : Language}
    {A : Type u} [TrustedAssumption A]
    {C : Compiler L_src L_tgt}
    {policy : TrustPolicy A}
    {assumptions : List A}
    {prog : L_src.Prog}
    {pre : L_src.Query → Prop}
    {spec : L_src.Behavior}
    (h_allowed : AllHold (assumptions.map policy.isAllowed))
    (h_sound : AllHold (assumptions.map TrustedAssumption.meaning) → C.SoundOn prog)
    (h_spec : AllHold (assumptions.map TrustedAssumption.meaning) → L_src.sem prog ≤ spec)
    (h_wf : spec ≤ L_src.WellFormedOn pre) :
    VerificationResultOn C policy assumptions prog pre [spec] := by
  refine ⟨h_allowed, fun h_assump => ?_⟩
  have hs := h_sound h_assump
  have hsp := h_spec h_assump
  exact ⟨Compiler.SoundOn.verify hs (Std.le_trans hsp h_wf),
         Compiler.SoundOn.verify hs hsp,
         trivial⟩

/-! ## Gap-Preserving Outcome and Program Equivalence

Whole-program equivalence (`ExactPass`, gap-free `ProgramEquiv`) requires every
execution of both programs to stay inside the modeled fragment of the
interpreter, including executions that run through shared, unchanged helper
callees. `OutcomeWithGap` separates the two ways an execution can fail to
produce a value:

- a **fault** (`.fault`) is a behavior of the *program* (undefined behavior, a
  panic, an abort, ...), compared across programs by a chosen fault relation;
- a **gap** (`.gap`) is a limitation of the *interpreter* (an unmodeled
  construct, an unresolved callee, an exhausted step budget, ...), which says
  nothing about the program and therefore only ever matches the identical gap.

`GapEqErr` relates outcomes up to identical gaps, so `ContextEquiv` holds
reflexively on unchanged code without any gap-freedom proof and composes through
monadic `bind`. `GapForbidEq` additionally forbids gaps, giving the gap-free
`ProgramEquiv`, and `ContextEquiv.toProgramEquiv` upgrades the former to the
latter on every query where one side is known to be gap-free.
-/

section GapPreservingEquivalence

universe uF uG uV uF' uG' uV' uF'' uG'' uV'' uQ uP uP'

/--
Terminal outcome of an execution, separating runtime faults of the program
(`.fault`) from modeling gaps of the interpreter (`.gap`).
-/
inductive OutcomeWithGap (Fault : Type uF) (Gap : Type uG) (Val : Type uV) :
    Type (max uF uG uV) where
  /-- Normal completion with value `val`. -/
  | ok (val : Val)
  /-- Runtime fault `err` of the program (undefined behavior, panic, abort). -/
  | fault (err : Fault)
  /-- Modeling gap `gap` of the interpreter (unmodeled construct, budget). -/
  | gap (gap : Gap)
  deriving DecidableEq, Repr

namespace OutcomeWithGap

variable {Fault : Type uF} {Gap : Type uG} {Val : Type uV}

/-- Map `f` over the `.ok` payload, preserving faults and gaps. -/
def map {Val' : Type uV'} (f : Val → Val') :
    OutcomeWithGap Fault Gap Val → OutcomeWithGap Fault Gap Val'
  | .ok v => .ok (f v)
  | .fault e => .fault e
  | .gap g => .gap g

/-- Map `f` over the `.fault` payload, preserving values and gaps. -/
def mapFault {Fault' : Type uF'} (f : Fault → Fault') :
    OutcomeWithGap Fault Gap Val → OutcomeWithGap Fault' Gap Val
  | .ok v => .ok v
  | .fault e => .fault (f e)
  | .gap g => .gap g

/-- Map `f` over the `.gap` payload, preserving values and faults. -/
def mapGap {Gap' : Type uG'} (f : Gap → Gap') :
    OutcomeWithGap Fault Gap Val → OutcomeWithGap Fault Gap' Val
  | .ok v => .ok v
  | .fault e => .fault e
  | .gap g => .gap (f g)

/-- Sequence `k` after `m`: faults and gaps of `m` are absorbing. -/
def bind {Val' : Type uV'} (m : OutcomeWithGap Fault Gap Val)
    (k : Val → OutcomeWithGap Fault Gap Val') : OutcomeWithGap Fault Gap Val' :=
  match m with
  | .ok v => k v
  | .fault e => .fault e
  | .gap g => .gap g

/-- `.ok _` and `.fault _` are gap-free; `.gap _` is not. -/
def isGapFree : OutcomeWithGap Fault Gap Val → Prop
  | .ok _ => True
  | .fault _ => True
  | .gap _ => False

instance instDecidableIsGapFree :
    (o : OutcomeWithGap Fault Gap Val) → Decidable o.isGapFree
  | .ok _ => isTrue trivial
  | .fault _ => isTrue trivial
  | .gap _ => isFalse (fun h => h)

instance : Monad (OutcomeWithGap Fault Gap) where
  pure := .ok
  bind := bind
  map := map

@[simp]
theorem bind_ok {Val' : Type uV'} (v : Val)
    (k : Val → OutcomeWithGap Fault Gap Val') :
    (OutcomeWithGap.ok v).bind k = k v := rfl

@[simp]
theorem bind_fault {Val' : Type uV'} (e : Fault)
    (k : Val → OutcomeWithGap Fault Gap Val') :
    (OutcomeWithGap.fault e).bind k = .fault e := rfl

/-- A gap is absorbing: no continuation runs after it. -/
@[simp]
theorem bind_gap {Val' : Type uV'} (g : Gap)
    (k : Val → OutcomeWithGap Fault Gap Val') :
    (OutcomeWithGap.gap g).bind k = .gap g := rfl

@[simp]
theorem bind_ok_right (m : OutcomeWithGap Fault Gap Val) :
    m.bind .ok = m := by
  cases m <;> rfl

theorem bind_assoc {Val' : Type uV'} {Val'' : Type uV''}
    (m : OutcomeWithGap Fault Gap Val)
    (k₁ : Val → OutcomeWithGap Fault Gap Val')
    (k₂ : Val' → OutcomeWithGap Fault Gap Val'') :
    (m.bind k₁).bind k₂ = m.bind (fun v => (k₁ v).bind k₂) := by
  cases m <;> rfl

theorem map_eq_bind {Val' : Type uV'} (f : Val → Val')
    (m : OutcomeWithGap Fault Gap Val) :
    m.map f = m.bind (fun v => .ok (f v)) := by
  cases m <;> rfl

theorem bind_map {Val' : Type uV'} {Val'' : Type uV''} (f : Val → Val')
    (m : OutcomeWithGap Fault Gap Val)
    (k : Val' → OutcomeWithGap Fault Gap Val'') :
    (m.map f).bind k = m.bind (fun v => k (f v)) := by
  cases m <;> rfl

theorem map_bind {Val' : Type uV'} {Val'' : Type uV''}
    (m : OutcomeWithGap Fault Gap Val)
    (k : Val → OutcomeWithGap Fault Gap Val') (f : Val' → Val'') :
    (m.bind k).map f = m.bind (fun v => (k v).map f) := by
  cases m <;> rfl

theorem map_map {Val' : Type uV'} {Val'' : Type uV''} (f : Val → Val')
    (g : Val' → Val'') (m : OutcomeWithGap Fault Gap Val) :
    (m.map f).map g = m.map (fun v => g (f v)) := by
  cases m <;> rfl

instance : LawfulMonad (OutcomeWithGap Fault Gap) := LawfulMonad.mk'
  (id_map := fun x => by cases x <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x _ _ => by cases x <;> rfl)

@[simp]
theorem isGapFree_ok (v : Val) :
    (OutcomeWithGap.ok v : OutcomeWithGap Fault Gap Val).isGapFree := trivial

@[simp]
theorem isGapFree_fault (e : Fault) :
    (OutcomeWithGap.fault e : OutcomeWithGap Fault Gap Val).isGapFree := trivial

@[simp]
theorem not_isGapFree_gap (g : Gap) :
    ¬ (OutcomeWithGap.gap g : OutcomeWithGap Fault Gap Val).isGapFree :=
  fun h => h

/-- An outcome is gap-free exactly when it is not a gap. -/
theorem isGapFree_iff_ne_gap (o : OutcomeWithGap Fault Gap Val) :
    o.isGapFree ↔ ∀ g, o ≠ .gap g := by
  cases o with
  | ok v => exact ⟨fun _ g h => (by cases h), fun _ => trivial⟩
  | fault e => exact ⟨fun _ g h => (by cases h), fun _ => trivial⟩
  | gap g => exact ⟨fun h => False.elim h, fun h => h g rfl⟩

theorem not_isGapFree_iff (o : OutcomeWithGap Fault Gap Val) :
    ¬ o.isGapFree ↔ ∃ g, o = .gap g := by
  cases o with
  | ok v => exact ⟨fun h => False.elim (h trivial), fun h => by obtain ⟨_, h⟩ := h; cases h⟩
  | fault e => exact ⟨fun h => False.elim (h trivial), fun h => by obtain ⟨_, h⟩ := h; cases h⟩
  | gap g => exact ⟨fun _ => ⟨g, rfl⟩, fun _ h => h⟩

/--
`m.bind k` is gap-free exactly when `m` is gap-free and `k` is gap-free on the
value `m` returns (if any).
-/
theorem isGapFree_bind_iff {Val' : Type uV'}
    (m : OutcomeWithGap Fault Gap Val)
    (k : Val → OutcomeWithGap Fault Gap Val') :
    (m.bind k).isGapFree ↔
      m.isGapFree ∧ ∀ v, m = .ok v → (k v).isGapFree := by
  cases m with
  | ok v =>
    exact ⟨fun h => ⟨trivial, fun v' hv => by cases hv; exact h⟩,
      fun h => h.2 v rfl⟩
  | fault e => exact ⟨fun _ => ⟨trivial, fun v hv => by cases hv⟩, fun _ => trivial⟩
  | gap g => exact ⟨fun h => False.elim h, fun h => h.1⟩

@[simp]
theorem isGapFree_map_iff {Val' : Type uV'} (f : Val → Val')
    (m : OutcomeWithGap Fault Gap Val) :
    (m.map f).isGapFree ↔ m.isGapFree := by
  cases m <;> exact Iff.rfl

@[simp]
theorem isGapFree_mapFault_iff {Fault' : Type uF'} (f : Fault → Fault')
    (m : OutcomeWithGap Fault Gap Val) :
    (m.mapFault f).isGapFree ↔ m.isGapFree := by
  cases m <;> exact Iff.rfl

@[simp]
theorem isGapFree_mapGap_iff {Gap' : Type uG'} (f : Gap → Gap')
    (m : OutcomeWithGap Fault Gap Val) :
    (m.mapGap f).isGapFree ↔ m.isGapFree := by
  cases m <;> exact Iff.rfl

theorem mapFault_mapFault {Fault' : Type uF'} {Fault'' : Type uF''}
    (f : Fault → Fault') (g : Fault' → Fault'')
    (m : OutcomeWithGap Fault Gap Val) :
    (m.mapFault f).mapFault g = m.mapFault (fun e => g (f e)) := by
  cases m <;> rfl

theorem mapGap_mapGap {Gap' : Type uG'} {Gap'' : Type uG''}
    (f : Gap → Gap') (g : Gap' → Gap'')
    (m : OutcomeWithGap Fault Gap Val) :
    (m.mapGap f).mapGap g = m.mapGap (fun x => g (f x)) := by
  cases m <;> rfl

theorem mapFault_bind {Fault' : Type uF'} {Val' : Type uV'} (f : Fault → Fault')
    (m : OutcomeWithGap Fault Gap Val)
    (k : Val → OutcomeWithGap Fault Gap Val') :
    (m.bind k).mapFault f = (m.mapFault f).bind (fun v => (k v).mapFault f) := by
  cases m <;> rfl

theorem mapGap_bind {Gap' : Type uG'} {Val' : Type uV'} (f : Gap → Gap')
    (m : OutcomeWithGap Fault Gap Val)
    (k : Val → OutcomeWithGap Fault Gap Val') :
    (m.bind k).mapGap f = (m.mapGap f).bind (fun v => (k v).mapGap f) := by
  cases m <;> rfl

/--
Definedness of a single outcome relative to `isUB`: values and defined runtime
faults (panics, aborts) are defined; UB faults and gaps are not.
-/
def isDefined (isUB : Fault → Prop) : OutcomeWithGap Fault Gap Val → Prop
  | .ok _ => True
  | .fault e => ¬ isUB e
  | .gap _ => False

@[simp]
theorem isDefined_ok {isUB : Fault → Prop} (v : Val) :
    (OutcomeWithGap.ok v : OutcomeWithGap Fault Gap Val).isDefined isUB := trivial

@[simp]
theorem isDefined_fault_iff {isUB : Fault → Prop} (e : Fault) :
    (OutcomeWithGap.fault e : OutcomeWithGap Fault Gap Val).isDefined isUB ↔
      ¬ isUB e := Iff.rfl

@[simp]
theorem not_isDefined_gap {isUB : Fault → Prop} (g : Gap) :
    ¬ (OutcomeWithGap.gap g : OutcomeWithGap Fault Gap Val).isDefined isUB :=
  fun h => h

theorem isDefined.isGapFree {isUB : Fault → Prop}
    {o : OutcomeWithGap Fault Gap Val} (h : o.isDefined isUB) : o.isGapFree := by
  cases o with
  | ok v => trivial
  | fault e => trivial
  | gap g => exact h

@[simp]
theorem map_id (m : OutcomeWithGap Fault Gap Val) :
    m.map id = m := by
  cases m <;> rfl

@[simp]
theorem mapFault_id (m : OutcomeWithGap Fault Gap Val) :
    m.mapFault id = m := by
  cases m <;> rfl

@[simp]
theorem mapGap_id (m : OutcomeWithGap Fault Gap Val) :
    m.mapGap id = m := by
  cases m <;> rfl

@[simp]
theorem isDefined_map_iff {Val' : Type uV'} {isUB : Fault → Prop}
    (f : Val → Val') (m : OutcomeWithGap Fault Gap Val) :
    (m.map f).isDefined isUB ↔ m.isDefined isUB := by
  cases m <;> exact Iff.rfl

@[simp]
theorem isDefined_mapGap_iff {Gap' : Type uG'} {isUB : Fault → Prop}
    (f : Gap → Gap') (m : OutcomeWithGap Fault Gap Val) :
    (m.mapGap f).isDefined isUB ↔ m.isDefined isUB := by
  cases m <;> exact Iff.rfl

theorem isDefined_mapFault_iff {Fault' : Type uF'}
    {isUB : Fault → Prop} {isUB' : Fault' → Prop} {f : Fault → Fault'}
    (hf : ∀ e, isUB' (f e) ↔ isUB e) (m : OutcomeWithGap Fault Gap Val) :
    (m.mapFault f).isDefined isUB' ↔ m.isDefined isUB := by
  cases m with
  | ok _ => exact Iff.rfl
  | fault e =>
    exact ⟨fun h he => h ((hf e).mpr he), fun h he' => h ((hf e).mp he')⟩
  | gap _ => exact Iff.rfl

theorem isDefined_bind_iff {Val' : Type uV'} {isUB : Fault → Prop}
    (m : OutcomeWithGap Fault Gap Val)
    (k : Val → OutcomeWithGap Fault Gap Val') :
    (m.bind k).isDefined isUB ↔
      m.isDefined isUB ∧ ∀ v, m = .ok v → (k v).isDefined isUB := by
  cases m with
  | ok v =>
    exact ⟨fun h => ⟨trivial, fun v' hv => by cases hv; exact h⟩,
      fun h => h.2 v rfl⟩
  | fault e =>
    exact ⟨fun h => ⟨h, fun _ hv => by cases hv⟩, fun h => h.1⟩
  | gap g => exact ⟨fun h => False.elim h, fun h => h.1⟩

end OutcomeWithGap

/-! ### Outcome Relations `GapEqErr` and `GapForbidEq` -/

/--
Gap-preserving outcome relation: values are related by `rVal`, faults by
`rFault`, gaps only when identical, and no outcome is related to an outcome of a
different kind. In particular a gap never matches a value or a fault.
-/
def GapEqErr {Fault₁ : Type uF} {Fault₂ : Type uF'} {Gap : Type uG}
    {Val₁ : Type uV} {Val₂ : Type uV'}
    (rVal : Val₁ → Val₂ → Prop) (rFault : Fault₁ → Fault₂ → Prop) :
    OutcomeWithGap Fault₁ Gap Val₁ → OutcomeWithGap Fault₂ Gap Val₂ → Prop
  | .ok v₁, .ok v₂ => rVal v₁ v₂
  | .ok _, .fault _ => False
  | .ok _, .gap _ => False
  | .fault _, .ok _ => False
  | .fault e₁, .fault e₂ => rFault e₁ e₂
  | .fault _, .gap _ => False
  | .gap _, .ok _ => False
  | .gap _, .fault _ => False
  | .gap g₁, .gap g₂ => g₁ = g₂

namespace GapEqErr

variable {Fault₁ : Type uF} {Fault₂ : Type uF'} {Gap : Type uG}
  {Val₁ : Type uV} {Val₂ : Type uV'}
  {rVal : Val₁ → Val₂ → Prop} {rFault : Fault₁ → Fault₂ → Prop}

instance instDecidable [DecidableEq Gap]
    [∀ v₁ v₂, Decidable (rVal v₁ v₂)] [∀ e₁ e₂, Decidable (rFault e₁ e₂)] :
    (o₁ : OutcomeWithGap Fault₁ Gap Val₁) → (o₂ : OutcomeWithGap Fault₂ Gap Val₂) →
      Decidable (GapEqErr rVal rFault o₁ o₂)
  | .ok v₁, .ok v₂ => inferInstanceAs (Decidable (rVal v₁ v₂))
  | .fault e₁, .fault e₂ => inferInstanceAs (Decidable (rFault e₁ e₂))
  | .gap g₁, .gap g₂ => inferInstanceAs (Decidable (g₁ = g₂))
  | .ok _, .fault _ => isFalse (fun h => h)
  | .ok _, .gap _ => isFalse (fun h => h)
  | .fault _, .ok _ => isFalse (fun h => h)
  | .fault _, .gap _ => isFalse (fun h => h)
  | .gap _, .ok _ => isFalse (fun h => h)
  | .gap _, .fault _ => isFalse (fun h => h)

@[simp]
theorem ok_ok_iff {v₁ : Val₁} {v₂ : Val₂} :
    GapEqErr (Gap := Gap) rVal rFault (.ok v₁) (.ok v₂) ↔ rVal v₁ v₂ := Iff.rfl

@[simp]
theorem fault_fault_iff {e₁ : Fault₁} {e₂ : Fault₂} :
    GapEqErr (Gap := Gap) rVal rFault (.fault e₁) (.fault e₂) ↔ rFault e₁ e₂ :=
  Iff.rfl

/-- Two gaps are related exactly when they are the same gap. -/
@[simp]
theorem gap_gap_iff {g₁ g₂ : Gap} :
    GapEqErr rVal rFault (.gap g₁) (.gap g₂) ↔ g₁ = g₂ := Iff.rfl

@[simp]
theorem not_ok_fault {v₁ : Val₁} {e₂ : Fault₂} :
    ¬ GapEqErr (Gap := Gap) rVal rFault (.ok v₁) (.fault e₂) := fun h => h

@[simp]
theorem not_ok_gap {v₁ : Val₁} {g₂ : Gap} :
    ¬ GapEqErr rVal rFault (.ok v₁) (.gap g₂) := fun h => h

@[simp]
theorem not_fault_ok {e₁ : Fault₁} {v₂ : Val₂} :
    ¬ GapEqErr (Gap := Gap) rVal rFault (.fault e₁) (.ok v₂) := fun h => h

@[simp]
theorem not_fault_gap {e₁ : Fault₁} {g₂ : Gap} :
    ¬ GapEqErr rVal rFault (.fault e₁) (.gap g₂) := fun h => h

@[simp]
theorem not_gap_ok {g₁ : Gap} {v₂ : Val₂} :
    ¬ GapEqErr rVal rFault (.gap g₁) (.ok v₂) := fun h => h

@[simp]
theorem not_gap_fault {g₁ : Gap} {e₂ : Fault₂} :
    ¬ GapEqErr rVal rFault (.gap g₁) (.fault e₂) := fun h => h

/-- A gap on the left is matched only by the identical gap on the right. -/
theorem gap_iff {g : Gap} {o₂ : OutcomeWithGap Fault₂ Gap Val₂} :
    GapEqErr rVal rFault (.gap g) o₂ ↔ o₂ = .gap g := by
  cases o₂ with
  | ok v => exact ⟨False.elim, fun h => by cases h⟩
  | fault e => exact ⟨False.elim, fun h => by cases h⟩
  | gap g' =>
    exact ⟨fun (h : g = g') => congrArg _ h.symm,
      fun h => by cases h; exact (rfl : g = g)⟩

/-- A gap on the right is matched only by the identical gap on the left. -/
theorem gap_iff_right {g : Gap} {o₁ : OutcomeWithGap Fault₁ Gap Val₁} :
    GapEqErr rVal rFault o₁ (.gap g) ↔ o₁ = .gap g := by
  cases o₁ with
  | ok v => exact ⟨False.elim, fun h => by cases h⟩
  | fault e => exact ⟨False.elim, fun h => by cases h⟩
  | gap g' =>
    exact ⟨fun (h : g' = g) => congrArg _ h,
      fun h => by cases h; exact (rfl : g = g)⟩

theorem ok_iff {v₁ : Val₁} {o₂ : OutcomeWithGap Fault₂ Gap Val₂} :
    GapEqErr rVal rFault (.ok v₁) o₂ ↔ ∃ v₂, o₂ = .ok v₂ ∧ rVal v₁ v₂ := by
  cases o₂ with
  | ok v => exact ⟨fun h => ⟨v, rfl, h⟩, fun h => by obtain ⟨_, h, hr⟩ := h; cases h; exact hr⟩
  | fault e => exact ⟨False.elim, fun h => by obtain ⟨_, h, _⟩ := h; cases h⟩
  | gap g => exact ⟨False.elim, fun h => by obtain ⟨_, h, _⟩ := h; cases h⟩

theorem ok_iff_right {v₂ : Val₂} {o₁ : OutcomeWithGap Fault₁ Gap Val₁} :
    GapEqErr rVal rFault o₁ (.ok v₂) ↔ ∃ v₁, o₁ = .ok v₁ ∧ rVal v₁ v₂ := by
  cases o₁ with
  | ok v => exact ⟨fun h => ⟨v, rfl, h⟩, fun h => by obtain ⟨_, h, hr⟩ := h; cases h; exact hr⟩
  | fault e => exact ⟨False.elim, fun h => by obtain ⟨_, h, _⟩ := h; cases h⟩
  | gap g => exact ⟨False.elim, fun h => by obtain ⟨_, h, _⟩ := h; cases h⟩

theorem fault_iff {e₁ : Fault₁} {o₂ : OutcomeWithGap Fault₂ Gap Val₂} :
    GapEqErr rVal rFault (.fault e₁) o₂ ↔ ∃ e₂, o₂ = .fault e₂ ∧ rFault e₁ e₂ := by
  cases o₂ with
  | ok v => exact ⟨False.elim, fun h => by obtain ⟨_, h, _⟩ := h; cases h⟩
  | fault e => exact ⟨fun h => ⟨e, rfl, h⟩, fun h => by obtain ⟨_, h, hr⟩ := h; cases h; exact hr⟩
  | gap g => exact ⟨False.elim, fun h => by obtain ⟨_, h, _⟩ := h; cases h⟩

theorem fault_iff_right {e₂ : Fault₂} {o₁ : OutcomeWithGap Fault₁ Gap Val₁} :
    GapEqErr rVal rFault o₁ (.fault e₂) ↔ ∃ e₁, o₁ = .fault e₁ ∧ rFault e₁ e₂ := by
  cases o₁ with
  | ok v => exact ⟨False.elim, fun h => by obtain ⟨_, h, _⟩ := h; cases h⟩
  | fault e => exact ⟨fun h => ⟨e, rfl, h⟩, fun h => by obtain ⟨_, h, hr⟩ := h; cases h; exact hr⟩
  | gap g => exact ⟨False.elim, fun h => by obtain ⟨_, h, _⟩ := h; cases h⟩

/-- Related outcomes are gap-free together: neither side can introduce a gap. -/
theorem isGapFree_iff {o₁ : OutcomeWithGap Fault₁ Gap Val₁}
    {o₂ : OutcomeWithGap Fault₂ Gap Val₂} (h : GapEqErr rVal rFault o₁ o₂) :
    o₁.isGapFree ↔ o₂.isGapFree := by
  cases o₁ <;> cases o₂ <;> first | exact Iff.rfl | exact False.elim h

/-- Reflexivity needs no side condition on gaps: `.gap g` relates to itself. -/
theorem refl {Fault : Type uF} {Val : Type uV}
    {rVal : Val → Val → Prop} {rFault : Fault → Fault → Prop}
    (hVal : ∀ v, rVal v v) (hFault : ∀ e, rFault e e)
    (o : OutcomeWithGap Fault Gap Val) : GapEqErr rVal rFault o o := by
  cases o with
  | ok v => exact hVal v
  | fault e => exact hFault e
  | gap g => exact (rfl : g = g)

/-- Swap the two sides, flipping both payload relations. -/
theorem flip {o₁ : OutcomeWithGap Fault₁ Gap Val₁}
    {o₂ : OutcomeWithGap Fault₂ Gap Val₂} (h : GapEqErr rVal rFault o₁ o₂) :
    GapEqErr (fun v₂ v₁ => rVal v₁ v₂) (fun e₂ e₁ => rFault e₁ e₂) o₂ o₁ := by
  cases o₁ <;> cases o₂ <;> first | exact Eq.symm h | exact h

theorem flip_iff {o₁ : OutcomeWithGap Fault₁ Gap Val₁}
    {o₂ : OutcomeWithGap Fault₂ Gap Val₂} :
    GapEqErr (fun v₂ v₁ => rVal v₁ v₂) (fun e₂ e₁ => rFault e₁ e₂) o₂ o₁ ↔
      GapEqErr rVal rFault o₁ o₂ :=
  ⟨fun h => h.flip, fun h => h.flip⟩

theorem symm {Fault : Type uF} {Val : Type uV}
    {rVal : Val → Val → Prop} {rFault : Fault → Fault → Prop}
    (hVal : ∀ a b, rVal a b → rVal b a) (hFault : ∀ a b, rFault a b → rFault b a)
    {o₁ o₂ : OutcomeWithGap Fault Gap Val} (h : GapEqErr rVal rFault o₁ o₂) :
    GapEqErr rVal rFault o₂ o₁ := by
  cases o₁ <;> cases o₂ <;>
    first
    | exact hVal _ _ h
    | exact hFault _ _ h
    | exact Eq.symm h
    | exact h

/-- Compose two relations through a middle outcome (relational composition). -/
theorem comp {Fault₃ : Type uF''} {Val₃ : Type uV''}
    {rVal' : Val₂ → Val₃ → Prop} {rFault' : Fault₂ → Fault₃ → Prop}
    {o₁ : OutcomeWithGap Fault₁ Gap Val₁} {o₂ : OutcomeWithGap Fault₂ Gap Val₂}
    {o₃ : OutcomeWithGap Fault₃ Gap Val₃}
    (h₁₂ : GapEqErr rVal rFault o₁ o₂) (h₂₃ : GapEqErr rVal' rFault' o₂ o₃) :
    GapEqErr (fun v₁ v₃ => ∃ v₂, rVal v₁ v₂ ∧ rVal' v₂ v₃)
      (fun e₁ e₃ => ∃ e₂, rFault e₁ e₂ ∧ rFault' e₂ e₃) o₁ o₃ := by
  cases o₁ <;> cases o₂ <;> cases o₃ <;>
    first
    | exact ⟨_, h₁₂, h₂₃⟩
    | exact Eq.trans h₁₂ h₂₃
    | exact False.elim h₁₂
    | exact False.elim h₂₃

theorem trans {Fault : Type uF} {Val : Type uV}
    {rVal : Val → Val → Prop} {rFault : Fault → Fault → Prop}
    (hVal : ∀ a b c, rVal a b → rVal b c → rVal a c)
    (hFault : ∀ a b c, rFault a b → rFault b c → rFault a c)
    {o₁ o₂ o₃ : OutcomeWithGap Fault Gap Val}
    (h₁₂ : GapEqErr rVal rFault o₁ o₂) (h₂₃ : GapEqErr rVal rFault o₂ o₃) :
    GapEqErr rVal rFault o₁ o₃ := by
  cases o₁ <;> cases o₂ <;> cases o₃ <;>
    first
    | exact hVal _ _ _ h₁₂ h₂₃
    | exact hFault _ _ _ h₁₂ h₂₃
    | exact Eq.trans h₁₂ h₂₃
    | exact False.elim h₁₂
    | exact False.elim h₂₃

/-- Monotonicity in the value and fault relations. -/
theorem mono {rVal' : Val₁ → Val₂ → Prop} {rFault' : Fault₁ → Fault₂ → Prop}
    (hVal : ∀ v₁ v₂, rVal v₁ v₂ → rVal' v₁ v₂)
    (hFault : ∀ e₁ e₂, rFault e₁ e₂ → rFault' e₁ e₂)
    {o₁ : OutcomeWithGap Fault₁ Gap Val₁} {o₂ : OutcomeWithGap Fault₂ Gap Val₂}
    (h : GapEqErr rVal rFault o₁ o₂) : GapEqErr rVal' rFault' o₁ o₂ := by
  cases o₁ <;> cases o₂ <;>
    first
    | exact hVal _ _ h
    | exact hFault _ _ h
    | exact h

/-- Exact matching on both payloads is equality of outcomes. -/
theorem eq_iff {Fault : Type uF} {Val : Type uV}
    {o₁ o₂ : OutcomeWithGap Fault Gap Val} :
    GapEqErr (· = ·) (· = ·) o₁ o₂ ↔ o₁ = o₂ := by
  constructor
  · intro h
    cases o₁ <;> cases o₂ <;> first | exact congrArg _ h | exact False.elim h
  · intro h
    cases h
    exact refl (fun _ => rfl) (fun _ => rfl) o₁

/--
Monadic `bind` congruence. When `m₁` and `m₂` are the same gap (for example the
result of a shared unchanged callee), both binds are that gap and the
continuations `k₁` and `k₂` are never compared.
-/
theorem bind_congr {ValB₁ : Type uV''} {ValB₂ : Type uP}
    {rValB : ValB₁ → ValB₂ → Prop}
    {m₁ : OutcomeWithGap Fault₁ Gap Val₁} {m₂ : OutcomeWithGap Fault₂ Gap Val₂}
    {k₁ : Val₁ → OutcomeWithGap Fault₁ Gap ValB₁}
    {k₂ : Val₂ → OutcomeWithGap Fault₂ Gap ValB₂}
    (hm : GapEqErr rVal rFault m₁ m₂)
    (hk : ∀ a₁ a₂, rVal a₁ a₂ → GapEqErr rValB rFault (k₁ a₁) (k₂ a₂)) :
    GapEqErr rValB rFault (m₁.bind k₁) (m₂.bind k₂) := by
  cases m₁ <;> cases m₂ <;>
    first
    | exact hk _ _ hm
    | exact hm
    | exact False.elim hm

/-- A gap on either side of a `bind` propagates regardless of the continuations. -/
theorem bind_gap_congr {ValB₁ : Type uV''} {ValB₂ : Type uP}
    {rValB : ValB₁ → ValB₂ → Prop} (g : Gap)
    (k₁ : Val₁ → OutcomeWithGap Fault₁ Gap ValB₁)
    (k₂ : Val₂ → OutcomeWithGap Fault₂ Gap ValB₂) :
    GapEqErr rValB rFault ((OutcomeWithGap.gap g).bind k₁)
      ((OutcomeWithGap.gap g).bind k₂) :=
  (rfl : g = g)

theorem map_congr {ValB₁ : Type uV''} {ValB₂ : Type uP}
    {rValB : ValB₁ → ValB₂ → Prop} {f₁ : Val₁ → ValB₁} {f₂ : Val₂ → ValB₂}
    {m₁ : OutcomeWithGap Fault₁ Gap Val₁} {m₂ : OutcomeWithGap Fault₂ Gap Val₂}
    (hm : GapEqErr rVal rFault m₁ m₂)
    (hf : ∀ a₁ a₂, rVal a₁ a₂ → rValB (f₁ a₁) (f₂ a₂)) :
    GapEqErr rValB rFault (m₁.map f₁) (m₂.map f₂) := by
  cases m₁ <;> cases m₂ <;>
    first
    | exact hf _ _ hm
    | exact hm
    | exact False.elim hm

theorem mapFault_congr {FaultB₁ : Type uF''} {FaultB₂ : Type uP}
    {rFaultB : FaultB₁ → FaultB₂ → Prop}
    {f₁ : Fault₁ → FaultB₁} {f₂ : Fault₂ → FaultB₂}
    {m₁ : OutcomeWithGap Fault₁ Gap Val₁} {m₂ : OutcomeWithGap Fault₂ Gap Val₂}
    (hm : GapEqErr rVal rFault m₁ m₂)
    (hf : ∀ e₁ e₂, rFault e₁ e₂ → rFaultB (f₁ e₁) (f₂ e₂)) :
    GapEqErr rVal rFaultB (m₁.mapFault f₁) (m₂.mapFault f₂) := by
  cases m₁ <;> cases m₂ <;>
    first
    | exact hf _ _ hm
    | exact hm
    | exact False.elim hm

theorem mapGap_congr {Gap' : Type uG'} (f : Gap → Gap')
    {m₁ : OutcomeWithGap Fault₁ Gap Val₁} {m₂ : OutcomeWithGap Fault₂ Gap Val₂}
    (hm : GapEqErr rVal rFault m₁ m₂) :
    GapEqErr rVal rFault (m₁.mapGap f) (m₂.mapGap f) := by
  cases m₁ <;> cases m₂ <;>
    first
    | exact congrArg f hm
    | exact hm
    | exact False.elim hm

theorem mapGap_iff_of_injective {Gap' : Type uG'} {f : Gap → Gap'}
    (hinj : ∀ g₁ g₂, f g₁ = f g₂ → g₁ = g₂)
    {m₁ : OutcomeWithGap Fault₁ Gap Val₁} {m₂ : OutcomeWithGap Fault₂ Gap Val₂} :
    GapEqErr rVal rFault (m₁.mapGap f) (m₂.mapGap f) ↔
      GapEqErr rVal rFault m₁ m₂ := by
  cases m₁ <;> cases m₂ <;>
    first
    | exact Iff.rfl
    | exact ⟨fun h => hinj _ _ h, fun h => congrArg f h⟩

/-- Related outcomes agree on definedness when `rFault` preserves UB-ness. -/
theorem isDefined_iff {isUB₁ : Fault₁ → Prop} {isUB₂ : Fault₂ → Prop}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → (isUB₁ e₁ ↔ isUB₂ e₂))
    {o₁ : OutcomeWithGap Fault₁ Gap Val₁} {o₂ : OutcomeWithGap Fault₂ Gap Val₂}
    (h : GapEqErr rVal rFault o₁ o₂) :
    o₁.isDefined isUB₁ ↔ o₂.isDefined isUB₂ := by
  cases o₁ with
  | ok v₁ =>
    cases o₂ with
    | ok v₂ => exact Iff.rfl
    | fault e₂ => exact False.elim h
    | gap g₂ => exact False.elim h
  | fault e₁ =>
    cases o₂ with
    | ok v₂ => exact False.elim h
    | fault e₂ =>
      exact ⟨fun h₁ h₂ => h₁ ((hUB e₁ e₂ h).mpr h₂),
        fun h₂ h₁ => h₂ ((hUB e₁ e₂ h).mp h₁)⟩
    | gap g₂ => exact False.elim h
  | gap g₁ =>
    cases o₂ with
    | ok v₂ => exact False.elim h
    | fault e₂ => exact False.elim h
    | gap g₂ => exact Iff.rfl

end GapEqErr

/--
Gap-forbidding outcome relation used by gap-free `ProgramEquiv`: values are
related by `rVal`, faults by `rFault`, and a gap on either side is never
related to anything (not even to the identical gap). The two sides may
therefore use different gap alphabets.
-/
def GapForbidEq {Fault₁ : Type uF} {Fault₂ : Type uF'} {Gap₁ : Type uG}
    {Gap₂ : Type uG'} {Val₁ : Type uV} {Val₂ : Type uV'}
    (rVal : Val₁ → Val₂ → Prop) (rFault : Fault₁ → Fault₂ → Prop) :
    OutcomeWithGap Fault₁ Gap₁ Val₁ → OutcomeWithGap Fault₂ Gap₂ Val₂ → Prop
  | .ok v₁, .ok v₂ => rVal v₁ v₂
  | .ok _, .fault _ => False
  | .ok _, .gap _ => False
  | .fault _, .ok _ => False
  | .fault e₁, .fault e₂ => rFault e₁ e₂
  | .fault _, .gap _ => False
  | .gap _, .ok _ => False
  | .gap _, .fault _ => False
  | .gap _, .gap _ => False

namespace GapForbidEq

variable {Fault₁ : Type uF} {Fault₂ : Type uF'} {Gap₁ : Type uG} {Gap₂ : Type uG'}
  {Val₁ : Type uV} {Val₂ : Type uV'}
  {rVal : Val₁ → Val₂ → Prop} {rFault : Fault₁ → Fault₂ → Prop}

instance instDecidable
    [∀ v₁ v₂, Decidable (rVal v₁ v₂)] [∀ e₁ e₂, Decidable (rFault e₁ e₂)] :
    (o₁ : OutcomeWithGap Fault₁ Gap₁ Val₁) → (o₂ : OutcomeWithGap Fault₂ Gap₂ Val₂) →
      Decidable (GapForbidEq rVal rFault o₁ o₂)
  | .ok v₁, .ok v₂ => inferInstanceAs (Decidable (rVal v₁ v₂))
  | .fault e₁, .fault e₂ => inferInstanceAs (Decidable (rFault e₁ e₂))
  | .ok _, .fault _ => isFalse (fun h => h)
  | .ok _, .gap _ => isFalse (fun h => h)
  | .fault _, .ok _ => isFalse (fun h => h)
  | .fault _, .gap _ => isFalse (fun h => h)
  | .gap _, .ok _ => isFalse (fun h => h)
  | .gap _, .fault _ => isFalse (fun h => h)
  | .gap _, .gap _ => isFalse (fun h => h)

@[simp]
theorem ok_ok_iff {v₁ : Val₁} {v₂ : Val₂} :
    GapForbidEq (Gap₁ := Gap₁) (Gap₂ := Gap₂) rVal rFault (.ok v₁) (.ok v₂) ↔
      rVal v₁ v₂ := Iff.rfl

@[simp]
theorem fault_fault_iff {e₁ : Fault₁} {e₂ : Fault₂} :
    GapForbidEq (Gap₁ := Gap₁) (Gap₂ := Gap₂) rVal rFault (.fault e₁) (.fault e₂) ↔
      rFault e₁ e₂ := Iff.rfl

theorem refl {Fault : Type uF} {Gap : Type uG} {Val : Type uV}
    {rVal : Val → Val → Prop} {rFault : Fault → Fault → Prop}
    (hVal : ∀ v, rVal v v) (hFault : ∀ e, rFault e e)
    {o : OutcomeWithGap Fault Gap Val} (hgf : o.isGapFree) :
    GapForbidEq rVal rFault o o := by
  cases o with
  | ok v => exact hVal v
  | fault e => exact hFault e
  | gap g => exact False.elim hgf

theorem symm {Fault : Type uF} {Gap : Type uG} {Val : Type uV}
    {rVal : Val → Val → Prop} {rFault : Fault → Fault → Prop}
    (hVal : ∀ a b, rVal a b → rVal b a) (hFault : ∀ a b, rFault a b → rFault b a)
    {o₁ o₂ : OutcomeWithGap Fault Gap Val} (h : GapForbidEq rVal rFault o₁ o₂) :
    GapForbidEq rVal rFault o₂ o₁ := by
  cases o₁ <;> cases o₂ <;>
    first
    | exact hVal _ _ h
    | exact hFault _ _ h
    | exact h

theorem trans {Fault : Type uF} {Gap : Type uG} {Val : Type uV}
    {rVal : Val → Val → Prop} {rFault : Fault → Fault → Prop}
    (hVal : ∀ a b c, rVal a b → rVal b c → rVal a c)
    (hFault : ∀ a b c, rFault a b → rFault b c → rFault a c)
    {o₁ o₂ o₃ : OutcomeWithGap Fault Gap Val}
    (h₁₂ : GapForbidEq rVal rFault o₁ o₂) (h₂₃ : GapForbidEq rVal rFault o₂ o₃) :
    GapForbidEq rVal rFault o₁ o₃ := by
  cases o₁ <;> cases o₂ <;> cases o₃ <;>
    first
    | exact hVal _ _ _ h₁₂ h₂₃
    | exact hFault _ _ _ h₁₂ h₂₃
    | exact False.elim h₁₂
    | exact False.elim h₂₃

theorem bind_congr {ValB₁ : Type uV''} {ValB₂ : Type uP}
    {rValB : ValB₁ → ValB₂ → Prop}
    {m₁ : OutcomeWithGap Fault₁ Gap₁ Val₁} {m₂ : OutcomeWithGap Fault₂ Gap₂ Val₂}
    {k₁ : Val₁ → OutcomeWithGap Fault₁ Gap₁ ValB₁}
    {k₂ : Val₂ → OutcomeWithGap Fault₂ Gap₂ ValB₂}
    (hm : GapForbidEq rVal rFault m₁ m₂)
    (hk : ∀ a₁ a₂, rVal a₁ a₂ → GapForbidEq rValB rFault (k₁ a₁) (k₂ a₂)) :
    GapForbidEq rValB rFault (m₁.bind k₁) (m₂.bind k₂) := by
  cases m₁ <;> cases m₂ <;>
    first
    | exact hk _ _ hm
    | exact hm
    | exact False.elim hm

theorem map_congr {ValB₁ : Type uV''} {ValB₂ : Type uP}
    {rValB : ValB₁ → ValB₂ → Prop} {f₁ : Val₁ → ValB₁} {f₂ : Val₂ → ValB₂}
    {m₁ : OutcomeWithGap Fault₁ Gap₁ Val₁} {m₂ : OutcomeWithGap Fault₂ Gap₂ Val₂}
    (hm : GapForbidEq rVal rFault m₁ m₂)
    (hf : ∀ a₁ a₂, rVal a₁ a₂ → rValB (f₁ a₁) (f₂ a₂)) :
    GapForbidEq rValB rFault (m₁.map f₁) (m₂.map f₂) := by
  cases m₁ <;> cases m₂ <;>
    first
    | exact hf _ _ hm
    | exact hm
    | exact False.elim hm

theorem mapFault_congr {FaultB₁ : Type uF''} {FaultB₂ : Type uP}
    {rFaultB : FaultB₁ → FaultB₂ → Prop}
    {f₁ : Fault₁ → FaultB₁} {f₂ : Fault₂ → FaultB₂}
    {m₁ : OutcomeWithGap Fault₁ Gap₁ Val₁} {m₂ : OutcomeWithGap Fault₂ Gap₂ Val₂}
    (hm : GapForbidEq rVal rFault m₁ m₂)
    (hf : ∀ e₁ e₂, rFault e₁ e₂ → rFaultB (f₁ e₁) (f₂ e₂)) :
    GapForbidEq rVal rFaultB (m₁.mapFault f₁) (m₂.mapFault f₂) := by
  cases m₁ <;> cases m₂ <;>
    first
    | exact hf _ _ hm
    | exact hm
    | exact False.elim hm

/--
Because `GapForbidEq` forbids gaps altogether, remapping gap tags with arbitrary
functions `f₁` and `f₂` (even non-injective ones) preserves `GapForbidEq` iff.
-/
@[simp]
theorem mapGap_iff {GapB₁ : Type uG''} {GapB₂ : Type uP}
    (f₁ : Gap₁ → GapB₁) (f₂ : Gap₂ → GapB₂)
    {m₁ : OutcomeWithGap Fault₁ Gap₁ Val₁} {m₂ : OutcomeWithGap Fault₂ Gap₂ Val₂} :
    GapForbidEq rVal rFault (m₁.mapGap f₁) (m₂.mapGap f₂) ↔
      GapForbidEq rVal rFault m₁ m₂ := by
  cases m₁ <;> cases m₂ <;> exact Iff.rfl

theorem ok_iff {v₁ : Val₁} {o₂ : OutcomeWithGap Fault₂ Gap₂ Val₂} :
    GapForbidEq (Gap₁ := Gap₁) rVal rFault (.ok v₁) o₂ ↔
      ∃ v₂, o₂ = .ok v₂ ∧ rVal v₁ v₂ := by
  cases o₂ with
  | ok v => exact ⟨fun h => ⟨v, rfl, h⟩, fun h => by obtain ⟨_, h, hr⟩ := h; cases h; exact hr⟩
  | fault _ => exact ⟨False.elim, fun h => by obtain ⟨_, h, _⟩ := h; cases h⟩
  | gap _ => exact ⟨False.elim, fun h => by obtain ⟨_, h, _⟩ := h; cases h⟩

theorem ok_iff_right {v₂ : Val₂} {o₁ : OutcomeWithGap Fault₁ Gap₁ Val₁} :
    GapForbidEq (Gap₂ := Gap₂) rVal rFault o₁ (.ok v₂) ↔
      ∃ v₁, o₁ = .ok v₁ ∧ rVal v₁ v₂ := by
  cases o₁ with
  | ok v => exact ⟨fun h => ⟨v, rfl, h⟩, fun h => by obtain ⟨_, h, hr⟩ := h; cases h; exact hr⟩
  | fault _ => exact ⟨False.elim, fun h => by obtain ⟨_, h, _⟩ := h; cases h⟩
  | gap _ => exact ⟨False.elim, fun h => by obtain ⟨_, h, _⟩ := h; cases h⟩

theorem fault_iff {e₁ : Fault₁} {o₂ : OutcomeWithGap Fault₂ Gap₂ Val₂} :
    GapForbidEq (Gap₁ := Gap₁) rVal rFault (.fault e₁) o₂ ↔
      ∃ e₂, o₂ = .fault e₂ ∧ rFault e₁ e₂ := by
  cases o₂ with
  | ok _ => exact ⟨False.elim, fun h => by obtain ⟨_, h, _⟩ := h; cases h⟩
  | fault e => exact ⟨fun h => ⟨e, rfl, h⟩, fun h => by obtain ⟨_, h, hr⟩ := h; cases h; exact hr⟩
  | gap _ => exact ⟨False.elim, fun h => by obtain ⟨_, h, _⟩ := h; cases h⟩

theorem fault_iff_right {e₂ : Fault₂} {o₁ : OutcomeWithGap Fault₁ Gap₁ Val₁} :
    GapForbidEq (Gap₂ := Gap₂) rVal rFault o₁ (.fault e₂) ↔
      ∃ e₁, o₁ = .fault e₁ ∧ rFault e₁ e₂ := by
  cases o₁ with
  | ok _ => exact ⟨False.elim, fun h => by obtain ⟨_, h, _⟩ := h; cases h⟩
  | fault e => exact ⟨fun h => ⟨e, rfl, h⟩, fun h => by obtain ⟨_, h, hr⟩ := h; cases h; exact hr⟩
  | gap _ => exact ⟨False.elim, fun h => by obtain ⟨_, h, _⟩ := h; cases h⟩

theorem eq_iff {Fault : Type uF} {Gap : Type uG} {Val : Type uV}
    {o₁ o₂ : OutcomeWithGap Fault Gap Val} :
    GapForbidEq (· = ·) (· = ·) o₁ o₂ ↔ o₁ = o₂ ∧ o₁.isGapFree := by
  constructor
  · intro h
    cases o₁ <;> cases o₂ <;> first | exact ⟨congrArg _ h, trivial⟩ | exact False.elim h
  · rintro ⟨rfl, hgf⟩
    cases o₁ with
    | ok _ => rfl
    | fault _ => rfl
    | gap _ => exact False.elim hgf

theorem isDefined_iff {isUB₁ : Fault₁ → Prop} {isUB₂ : Fault₂ → Prop}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → (isUB₁ e₁ ↔ isUB₂ e₂))
    {o₁ : OutcomeWithGap Fault₁ Gap₁ Val₁} {o₂ : OutcomeWithGap Fault₂ Gap₂ Val₂}
    (h : GapForbidEq rVal rFault o₁ o₂) :
    o₁.isDefined isUB₁ ↔ o₂.isDefined isUB₂ := by
  cases o₁ with
  | ok v₁ =>
    cases o₂ with
    | ok v₂ => exact Iff.rfl
    | fault e₂ => exact False.elim h
    | gap g₂ => exact False.elim h
  | fault e₁ =>
    cases o₂ with
    | ok v₂ => exact False.elim h
    | fault e₂ =>
      exact ⟨fun h₁ h₂ => h₁ ((hUB e₁ e₂ h).mpr h₂),
        fun h₂ h₁ => h₂ ((hUB e₁ e₂ h).mp h₁)⟩
    | gap g₂ => exact False.elim h
  | gap g₁ => cases o₂ <;> exact False.elim h

theorem isGapFree_left {o₁ : OutcomeWithGap Fault₁ Gap₁ Val₁}
    {o₂ : OutcomeWithGap Fault₂ Gap₂ Val₂} (h : GapForbidEq rVal rFault o₁ o₂) :
    o₁.isGapFree := by
  cases o₁ <;> cases o₂ <;> first | exact trivial | exact False.elim h

theorem isGapFree_right {o₁ : OutcomeWithGap Fault₁ Gap₁ Val₁}
    {o₂ : OutcomeWithGap Fault₂ Gap₂ Val₂} (h : GapForbidEq rVal rFault o₁ o₂) :
    o₂.isGapFree := by
  cases o₁ <;> cases o₂ <;> first | exact trivial | exact False.elim h

/-- A gap is never `GapForbidEq`-related to anything, including itself. -/
theorem not_gap_left {g : Gap₁} {o₂ : OutcomeWithGap Fault₂ Gap₂ Val₂} :
    ¬ GapForbidEq rVal rFault (.gap g : OutcomeWithGap Fault₁ Gap₁ Val₁) o₂ :=
  fun h => h.isGapFree_left

theorem not_gap_right {g : Gap₂} {o₁ : OutcomeWithGap Fault₁ Gap₁ Val₁} :
    ¬ GapForbidEq rVal rFault o₁ (.gap g : OutcomeWithGap Fault₂ Gap₂ Val₂) :=
  fun h => h.isGapFree_right

theorem flip {o₁ : OutcomeWithGap Fault₁ Gap₁ Val₁}
    {o₂ : OutcomeWithGap Fault₂ Gap₂ Val₂} (h : GapForbidEq rVal rFault o₁ o₂) :
    GapForbidEq (fun v₂ v₁ => rVal v₁ v₂) (fun e₂ e₁ => rFault e₁ e₂) o₂ o₁ := by
  cases o₁ <;> cases o₂ <;> exact h

theorem comp {Fault₃ : Type uF''} {Gap₃ : Type uG''} {Val₃ : Type uV''}
    {rVal' : Val₂ → Val₃ → Prop} {rFault' : Fault₂ → Fault₃ → Prop}
    {o₁ : OutcomeWithGap Fault₁ Gap₁ Val₁} {o₂ : OutcomeWithGap Fault₂ Gap₂ Val₂}
    {o₃ : OutcomeWithGap Fault₃ Gap₃ Val₃}
    (h₁₂ : GapForbidEq rVal rFault o₁ o₂) (h₂₃ : GapForbidEq rVal' rFault' o₂ o₃) :
    GapForbidEq (fun v₁ v₃ => ∃ v₂, rVal v₁ v₂ ∧ rVal' v₂ v₃)
      (fun e₁ e₃ => ∃ e₂, rFault e₁ e₂ ∧ rFault' e₂ e₃) o₁ o₃ := by
  cases o₁ <;> cases o₂ <;> cases o₃ <;>
    first
    | exact ⟨_, h₁₂, h₂₃⟩
    | exact False.elim h₁₂
    | exact False.elim h₂₃

theorem mono {rVal' : Val₁ → Val₂ → Prop} {rFault' : Fault₁ → Fault₂ → Prop}
    (hVal : ∀ v₁ v₂, rVal v₁ v₂ → rVal' v₁ v₂)
    (hFault : ∀ e₁ e₂, rFault e₁ e₂ → rFault' e₁ e₂)
    {o₁ : OutcomeWithGap Fault₁ Gap₁ Val₁} {o₂ : OutcomeWithGap Fault₂ Gap₂ Val₂}
    (h : GapForbidEq rVal rFault o₁ o₂) : GapForbidEq rVal' rFault' o₁ o₂ := by
  cases o₁ <;> cases o₂ <;>
    first
    | exact hVal _ _ h
    | exact hFault _ _ h
    | exact h

/-- On a shared gap alphabet, `GapForbidEq` is `GapEqErr` minus the gaps. -/
theorem iff_gapEqErr_and_left {Gap : Type uG}
    {o₁ : OutcomeWithGap Fault₁ Gap Val₁} {o₂ : OutcomeWithGap Fault₂ Gap Val₂} :
    GapForbidEq rVal rFault o₁ o₂ ↔ GapEqErr rVal rFault o₁ o₂ ∧ o₁.isGapFree := by
  cases o₁ <;> cases o₂ <;>
    first
    | exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
    | exact ⟨False.elim, fun h => h.1⟩
    | exact ⟨False.elim, fun h => h.2⟩

theorem iff_gapEqErr_and_right {Gap : Type uG}
    {o₁ : OutcomeWithGap Fault₁ Gap Val₁} {o₂ : OutcomeWithGap Fault₂ Gap Val₂} :
    GapForbidEq rVal rFault o₁ o₂ ↔ GapEqErr rVal rFault o₁ o₂ ∧ o₂.isGapFree := by
  cases o₁ <;> cases o₂ <;>
    first
    | exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
    | exact ⟨False.elim, fun h => h.1⟩
    | exact ⟨False.elim, fun h => h.2⟩

theorem toGapEqErr {Gap : Type uG}
    {o₁ : OutcomeWithGap Fault₁ Gap Val₁} {o₂ : OutcomeWithGap Fault₂ Gap Val₂}
    (h : GapForbidEq rVal rFault o₁ o₂) : GapEqErr rVal rFault o₁ o₂ :=
  (iff_gapEqErr_and_left.mp h).1

theorem of_gapEqErr_left {Gap : Type uG}
    {o₁ : OutcomeWithGap Fault₁ Gap Val₁} {o₂ : OutcomeWithGap Fault₂ Gap Val₂}
    (h : GapEqErr rVal rFault o₁ o₂) (hgf : o₁.isGapFree) :
    GapForbidEq rVal rFault o₁ o₂ :=
  iff_gapEqErr_and_left.mpr ⟨h, hgf⟩

theorem of_gapEqErr_right {Gap : Type uG}
    {o₁ : OutcomeWithGap Fault₁ Gap Val₁} {o₂ : OutcomeWithGap Fault₂ Gap Val₂}
    (h : GapEqErr rVal rFault o₁ o₂) (hgf : o₂.isGapFree) :
    GapForbidEq rVal rFault o₁ o₂ :=
  iff_gapEqErr_and_right.mpr ⟨h, hgf⟩

end GapForbidEq

/-! ### Bidirectional Simulation on Behavior Sets (`OutcomeSetEquiv`) -/

/-- The behavior set containing exactly `a` (a deterministic behavior). -/
def BehaviorSet.singleton {α : Type uV} (a : α) : BehaviorSet α :=
  fun x => x = a

/-- Relational image of a behavior set under `R`. -/
def BehaviorSet.relImage {α : Type uV} {β : Type uV'} (R : α → β → Prop)
    (S : BehaviorSet α) : BehaviorSet β :=
  fun b => ∃ a, S a ∧ R a b

theorem BehaviorSet.relImage_monotone {α : Type uV} {β : Type uV'}
    (R : α → β → Prop) : Monotone (BehaviorSet.relImage R) :=
  fun _ _ h_ref _ ⟨a, ha, hr⟩ => ⟨a, h_ref a ha, hr⟩

/--
Forward-and-backward relational simulation between two behavior sets: every
behavior of either set is matched by an `R`-related behavior of the other.

Instantiated on `BehaviorSet (OutcomeWithGap Fault Gap Val)` with `GapEqErr`
(`ContextEquiv`) and `GapForbidEq` (`ProgramEquiv`), it covers deterministic
evaluators (`BehaviorSet.singleton`) and nondeterministic or relational
semantics uniformly.
-/
structure OutcomeSetEquiv {α : Type uV} {β : Type uV'} (R : α → β → Prop)
    (S₁ : BehaviorSet α) (S₂ : BehaviorSet β) : Prop where
  /-- Every behavior of `S₁` is matched by a related behavior of `S₂`. -/
  forward : ∀ ⦃a⦄, S₁ a → ∃ b, S₂ b ∧ R a b
  /-- Every behavior of `S₂` is matched by a related behavior of `S₁`. -/
  backward : ∀ ⦃b⦄, S₂ b → ∃ a, S₁ a ∧ R a b

namespace OutcomeSetEquiv

variable {α : Type uV} {β : Type uV'} {γ : Type uV''}

theorem refl {R : α → α → Prop} (hR : ∀ a, R a a) (S : BehaviorSet α) :
    OutcomeSetEquiv R S S :=
  ⟨fun a ha => ⟨a, ha, hR a⟩, fun a ha => ⟨a, ha, hR a⟩⟩

theorem flip {R : α → β → Prop} {S₁ : BehaviorSet α} {S₂ : BehaviorSet β}
    (h : OutcomeSetEquiv R S₁ S₂) : OutcomeSetEquiv (fun b a => R a b) S₂ S₁ :=
  ⟨fun _ hb => h.backward hb, fun _ ha => h.forward ha⟩

theorem mono {R R' : α → β → Prop} {S₁ : BehaviorSet α} {S₂ : BehaviorSet β}
    (hR : ∀ a b, R a b → R' a b) (h : OutcomeSetEquiv R S₁ S₂) :
    OutcomeSetEquiv R' S₁ S₂ := by
  refine ⟨fun _ ha => ?_, fun _ hb => ?_⟩
  · obtain ⟨b, hb, hab⟩ := h.forward ha; exact ⟨b, hb, hR _ _ hab⟩
  · obtain ⟨a, ha, hab⟩ := h.backward hb; exact ⟨a, ha, hR _ _ hab⟩

theorem comp {R : α → β → Prop} {R' : β → γ → Prop}
    {S₁ : BehaviorSet α} {S₂ : BehaviorSet β} {S₃ : BehaviorSet γ}
    (h₁₂ : OutcomeSetEquiv R S₁ S₂) (h₂₃ : OutcomeSetEquiv R' S₂ S₃) :
    OutcomeSetEquiv (fun a c => ∃ b, R a b ∧ R' b c) S₁ S₃ := by
  refine ⟨fun _ ha => ?_, fun _ hc => ?_⟩
  · obtain ⟨b, hb, hab⟩ := h₁₂.forward ha
    obtain ⟨c, hc, hbc⟩ := h₂₃.forward hb
    exact ⟨c, hc, b, hab, hbc⟩
  · obtain ⟨b, hb, hbc⟩ := h₂₃.backward hc
    obtain ⟨a, ha, hab⟩ := h₁₂.backward hb
    exact ⟨a, ha, b, hab, hbc⟩

theorem symm {R : α → α → Prop} {S₁ S₂ : BehaviorSet α}
    (hR : ∀ a b, R a b → R b a) (h : OutcomeSetEquiv R S₁ S₂) :
    OutcomeSetEquiv R S₂ S₁ :=
  h.flip.mono (fun b a => hR a b)

theorem trans {R : α → α → Prop} {S₁ S₂ S₃ : BehaviorSet α}
    (hR : ∀ a b c, R a b → R b c → R a c)
    (h₁₂ : OutcomeSetEquiv R S₁ S₂) (h₂₃ : OutcomeSetEquiv R S₂ S₃) :
    OutcomeSetEquiv R S₁ S₃ :=
  (h₁₂.comp h₂₃).mono (fun a c h => by obtain ⟨b, hab, hbc⟩ := h; exact hR a b c hab hbc)

/-- On deterministic behaviors the simulation is the underlying relation. -/
theorem singleton_iff {R : α → β → Prop} {a : α} {b : β} :
    OutcomeSetEquiv R (BehaviorSet.singleton a) (BehaviorSet.singleton b) ↔
      R a b := by
  constructor
  · intro h
    obtain ⟨b', hb', hab⟩ := h.forward (a := a) rfl
    cases hb'
    exact hab
  · intro h
    refine ⟨fun a' ha' => ⟨b, rfl, ?_⟩, fun b' hb' => ⟨a, rfl, ?_⟩⟩
    · cases ha'; exact h
    · cases hb'; exact h

end OutcomeSetEquiv

/-! ### Gap-Aware Semantics, `ContextEquiv`, and `ProgramEquiv` -/

/-- Nondeterministic gap-aware behavior: a set of `OutcomeWithGap` outcomes. -/
abbrev OutcomeSet (Fault : Type uF) (Gap : Type uG) (Val : Type uV) :
    Type (max uF uG uV) :=
  BehaviorSet (OutcomeWithGap Fault Gap Val)

/-- Query-indexed gap-aware semantics (`Query → OutcomeSet Fault Gap Val`). -/
abbrev GapSem (Query : Type uQ) (Fault : Type uF) (Gap : Type uG) (Val : Type uV) :
    Type (max uQ uF uG uV) :=
  Query → OutcomeSet Fault Gap Val

/-- Embed a deterministic query-indexed evaluator as a `GapSem`. -/
def GapSem.det {Query : Type uQ} {Fault : Type uF} {Gap : Type uG} {Val : Type uV}
    (f : Query → OutcomeWithGap Fault Gap Val) : GapSem Query Fault Gap Val :=
  fun q => BehaviorSet.singleton (f q)

/-- Restrict a semantics to the queries satisfying `pre`. -/
def GapSem.restrict {Query : Type uQ} {Fault : Type uF} {Gap : Type uG}
    {Val : Type uV} (pre : Query → Prop) (sem : GapSem Query Fault Gap Val) :
    GapSem { q : Query // pre q } Fault Gap Val :=
  fun q => sem q.1

/-- No behavior in `S` is a modeling gap. -/
def NeverGap {Fault : Type uF} {Gap : Type uG} {Val : Type uV}
    (S : OutcomeSet Fault Gap Val) : Prop :=
  ∀ ⦃o⦄, S o → o.isGapFree

/-- `sem` is gap-free on every query satisfying `pre`. -/
def GapFreeOn {Query : Type uQ} {Fault : Type uF} {Gap : Type uG} {Val : Type uV}
    (pre : Query → Prop) (sem : GapSem Query Fault Gap Val) : Prop :=
  ∀ q, pre q → NeverGap (sem q)

/-- `sem` is gap-free on every query. -/
def AllGapFree {Query : Type uQ} {Fault : Type uF} {Gap : Type uG} {Val : Type uV}
    (sem : GapSem Query Fault Gap Val) : Prop :=
  ∀ q, NeverGap (sem q)

/--
Gap-preserving (context) equivalence on the queries satisfying `pre`: on each
such query the two behavior sets simulate each other up to `GapEqErr`, so both
programs return related values, raise related faults, or hit the identical gap.
-/
def ContextEquivOn {Query : Type uQ} {Fault₁ : Type uF} {Fault₂ : Type uF'}
    {Gap : Type uG} {Val₁ : Type uV} {Val₂ : Type uV'}
    (pre : Query → Prop)
    (rVal : Val₁ → Val₂ → Prop) (rFault : Fault₁ → Fault₂ → Prop)
    (sem₁ : GapSem Query Fault₁ Gap Val₁) (sem₂ : GapSem Query Fault₂ Gap Val₂) :
    Prop :=
  ∀ q, pre q → OutcomeSetEquiv (GapEqErr rVal rFault) (sem₁ q) (sem₂ q)

/-- Gap-preserving (context) equivalence on every query. -/
def ContextEquiv {Query : Type uQ} {Fault₁ : Type uF} {Fault₂ : Type uF'}
    {Gap : Type uG} {Val₁ : Type uV} {Val₂ : Type uV'}
    (rVal : Val₁ → Val₂ → Prop) (rFault : Fault₁ → Fault₂ → Prop)
    (sem₁ : GapSem Query Fault₁ Gap Val₁) (sem₂ : GapSem Query Fault₂ Gap Val₂) :
    Prop :=
  ∀ q, OutcomeSetEquiv (GapEqErr rVal rFault) (sem₁ q) (sem₂ q)

/--
Gap-free program equivalence on the queries satisfying `pre`: on each such
query the two behavior sets simulate each other up to `GapForbidEq`, so both
programs are gap-free there and return related values or raise related faults
(`programEquivOn_iff`).
-/
def ProgramEquivOn {Query : Type uQ} {Fault₁ : Type uF} {Fault₂ : Type uF'}
    {Gap₁ : Type uG} {Gap₂ : Type uG'} {Val₁ : Type uV} {Val₂ : Type uV'}
    (pre : Query → Prop)
    (rVal : Val₁ → Val₂ → Prop) (rFault : Fault₁ → Fault₂ → Prop)
    (sem₁ : GapSem Query Fault₁ Gap₁ Val₁) (sem₂ : GapSem Query Fault₂ Gap₂ Val₂) :
    Prop :=
  ∀ q, pre q → OutcomeSetEquiv (GapForbidEq rVal rFault) (sem₁ q) (sem₂ q)

/-- Gap-free program equivalence on every query. -/
def ProgramEquiv {Query : Type uQ} {Fault₁ : Type uF} {Fault₂ : Type uF'}
    {Gap₁ : Type uG} {Gap₂ : Type uG'} {Val₁ : Type uV} {Val₂ : Type uV'}
    (rVal : Val₁ → Val₂ → Prop) (rFault : Fault₁ → Fault₂ → Prop)
    (sem₁ : GapSem Query Fault₁ Gap₁ Val₁) (sem₂ : GapSem Query Fault₂ Gap₂ Val₂) :
    Prop :=
  ∀ q, OutcomeSetEquiv (GapForbidEq rVal rFault) (sem₁ q) (sem₂ q)

section SetLevel

variable {Fault₁ : Type uF} {Fault₂ : Type uF'} {Gap : Type uG}
  {Val₁ : Type uV} {Val₂ : Type uV'}
  {rVal : Val₁ → Val₂ → Prop} {rFault : Fault₁ → Fault₂ → Prop}
  {S₁ : OutcomeSet Fault₁ Gap Val₁} {S₂ : OutcomeSet Fault₂ Gap Val₂}

theorem neverGap_singleton_iff {o : OutcomeWithGap Fault₁ Gap Val₁} :
    NeverGap (BehaviorSet.singleton o) ↔ o.isGapFree :=
  ⟨fun h => h (o := o) rfl, fun h o' ho' => by cases ho'; exact h⟩

/-- Lift a gap-tag transformation pointwise to an `OutcomeSet`. -/
def OutcomeSet.mapGap {Gap' : Type uG'} (f : Gap₁ → Gap')
    (S : OutcomeSet Fault₁ Gap₁ Val₁) : OutcomeSet Fault₁ Gap' Val₁ :=
  fun o' => ∃ o, S o ∧ o.mapGap f = o'

theorem OutcomeSetEquiv.mapGap_congr {Gap : Type uG} {Gap' : Type uG'}
    (f : Gap → Gap')
    {S₁ : OutcomeSet Fault₁ Gap Val₁} {S₂ : OutcomeSet Fault₂ Gap Val₂}
    (h : OutcomeSetEquiv (GapEqErr rVal rFault) S₁ S₂) :
    OutcomeSetEquiv (GapEqErr rVal rFault)
      (OutcomeSet.mapGap f S₁) (OutcomeSet.mapGap f S₂) where
  forward := by
    intro _ ho₁'
    obtain ⟨o₁, ho₁, rfl⟩ := ho₁'
    obtain ⟨o₂, ho₂, hr⟩ := h.forward ho₁
    exact ⟨o₂.mapGap f, ⟨o₂, ho₂, rfl⟩, hr.mapGap_congr f⟩
  backward := by
    intro _ ho₂'
    obtain ⟨o₂, ho₂, rfl⟩ := ho₂'
    obtain ⟨o₁, ho₁, hr⟩ := h.backward ho₂
    exact ⟨o₁.mapGap f, ⟨o₁, ho₁, rfl⟩, hr.mapGap_congr f⟩

theorem OutcomeSetEquiv.mapGap_iff_of_injective {Gap : Type uG} {Gap' : Type uG'}
    {f : Gap → Gap'} (hinj : ∀ g₁ g₂, f g₁ = f g₂ → g₁ = g₂)
    {S₁ : OutcomeSet Fault₁ Gap Val₁} {S₂ : OutcomeSet Fault₂ Gap Val₂} :
    OutcomeSetEquiv (GapEqErr rVal rFault)
        (OutcomeSet.mapGap f S₁) (OutcomeSet.mapGap f S₂) ↔
      OutcomeSetEquiv (GapEqErr rVal rFault) S₁ S₂ := by
  refine ⟨fun h => ?_, OutcomeSetEquiv.mapGap_congr f⟩
  refine ⟨fun o₁ ho₁ => ?_, fun o₂ ho₂ => ?_⟩
  · obtain ⟨_, ⟨o₂, ho₂, rfl⟩, hr⟩ := h.forward ⟨o₁, ho₁, rfl⟩
    exact ⟨o₂, ho₂, (GapEqErr.mapGap_iff_of_injective hinj).mp hr⟩
  · obtain ⟨_, ⟨o₁, ho₁, rfl⟩, hr⟩ := h.backward ⟨o₂, ho₂, rfl⟩
    exact ⟨o₁, ho₁, (GapEqErr.mapGap_iff_of_injective hinj).mp hr⟩

/-- `GapEqErr`-equivalent behavior sets are gap-free together. -/
theorem OutcomeSetEquiv.neverGap_iff
    (h : OutcomeSetEquiv (GapEqErr rVal rFault) S₁ S₂) :
    NeverGap S₁ ↔ NeverGap S₂ := by
  refine ⟨fun h₁ _ ho₂ => ?_, fun h₂ _ ho₁ => ?_⟩
  · obtain ⟨_, ho₁, hr⟩ := h.backward ho₂; exact hr.isGapFree_iff.mp (h₁ ho₁)
  · obtain ⟨_, ho₂, hr⟩ := h.forward ho₁; exact hr.isGapFree_iff.mpr (h₂ ho₂)

/--
`GapForbidEq`-equivalence is `GapEqErr`-equivalence between two gap-free
behavior sets.
-/
theorem OutcomeSetEquiv.forbid_iff :
    OutcomeSetEquiv (GapForbidEq rVal rFault) S₁ S₂ ↔
      NeverGap S₁ ∧ NeverGap S₂ ∧ OutcomeSetEquiv (GapEqErr rVal rFault) S₁ S₂ := by
  constructor
  · intro h
    refine ⟨fun o₁ ho₁ => ?_, fun o₂ ho₂ => ?_, h.mono (fun _ _ hr => hr.toGapEqErr)⟩
    · obtain ⟨_, _, hr⟩ := h.forward ho₁
      exact hr.isGapFree_left
    · obtain ⟨_, _, hr⟩ := h.backward ho₂
      exact hr.isGapFree_right
  · rintro ⟨h₁, h₂, h⟩
    refine ⟨fun o₁ ho₁ => ?_, fun o₂ ho₂ => ?_⟩
    · obtain ⟨o₂, ho₂, hr⟩ := h.forward ho₁
      exact ⟨o₂, ho₂, GapForbidEq.of_gapEqErr_left hr (h₁ ho₁)⟩
    · obtain ⟨o₁, ho₁, hr⟩ := h.backward ho₂
      exact ⟨o₁, ho₁, GapForbidEq.of_gapEqErr_right hr (h₂ ho₂)⟩

/--
Per-behavior-set upgrade: a `GapEqErr`-equivalence whose left side is gap-free
is a `GapForbidEq`-equivalence (the right side is then gap-free as well).
-/
theorem OutcomeSetEquiv.forbid_of_neverGap_left
    (h : OutcomeSetEquiv (GapEqErr rVal rFault) S₁ S₂) (h₁ : NeverGap S₁) :
    OutcomeSetEquiv (GapForbidEq rVal rFault) S₁ S₂ :=
  OutcomeSetEquiv.forbid_iff.mpr ⟨h₁, h.neverGap_iff.mp h₁, h⟩

theorem OutcomeSetEquiv.forbid_of_neverGap_right
    (h : OutcomeSetEquiv (GapEqErr rVal rFault) S₁ S₂) (h₂ : NeverGap S₂) :
    OutcomeSetEquiv (GapForbidEq rVal rFault) S₁ S₂ :=
  OutcomeSetEquiv.forbid_iff.mpr ⟨h.neverGap_iff.mpr h₂, h₂, h⟩

end SetLevel

/-! #### Sequential composition of behavior sets -/

/--
Sequence `k` after every behavior of `S`: values continue with `k`, while faults
and gaps of `S` are absorbing.
-/
def OutcomeSet.bind {Fault : Type uF} {Gap : Type uG} {Val : Type uV}
    {Val' : Type uV'} (S : OutcomeSet Fault Gap Val)
    (k : Val → OutcomeSet Fault Gap Val') : OutcomeSet Fault Gap Val' :=
  fun o => ∃ m, S m ∧
    match m with
    | .ok v => k v o
    | .fault e => o = .fault e
    | .gap g => o = .gap g

/-- Sequence a query-indexed continuation after a query-indexed semantics. -/
def GapSem.bind {Query : Type uQ} {Fault : Type uF} {Gap : Type uG}
    {Val : Type uV} {Val' : Type uV'} (sem : GapSem Query Fault Gap Val)
    (k : Query → Val → OutcomeSet Fault Gap Val') : GapSem Query Fault Gap Val' :=
  fun q => OutcomeSet.bind (sem q) (k q)

/-- `OutcomeSet.bind` on deterministic behaviors is `OutcomeWithGap.bind`. -/
theorem OutcomeSet.bind_singleton_iff {Fault : Type uF} {Gap : Type uG}
    {Val : Type uV} {Val' : Type uV'} (m : OutcomeWithGap Fault Gap Val)
    (k : Val → OutcomeWithGap Fault Gap Val') (o : OutcomeWithGap Fault Gap Val') :
    OutcomeSet.bind (BehaviorSet.singleton m)
        (fun v => BehaviorSet.singleton (k v)) o ↔
      BehaviorSet.singleton (m.bind k) o := by
  constructor
  · rintro ⟨m', hm', ho⟩
    cases hm'
    cases m <;> exact ho
  · intro ho
    refine ⟨m, rfl, ?_⟩
    cases m <;> exact ho

theorem OutcomeSet.bind_ok_left {Fault : Type uF} {Gap : Type uG}
    {Val : Type uV} {Val' : Type uV'} (v : Val)
    (k : Val → OutcomeSet Fault Gap Val') :
    OutcomeSet.bind (BehaviorSet.singleton (.ok v)) k = k v := by
  funext o; apply propext
  constructor
  · rintro ⟨m, hm, ho⟩; cases hm; exact ho
  · intro ho; exact ⟨.ok v, rfl, ho⟩

theorem OutcomeSet.bind_ok_right {Fault : Type uF} {Gap : Type uG}
    {Val : Type uV} (S : OutcomeSet Fault Gap Val) :
    OutcomeSet.bind S (fun v => BehaviorSet.singleton (.ok v)) = S := by
  funext o; apply propext
  constructor
  · rintro ⟨m, hm, ho⟩
    cases m with
    | ok v => cases ho; exact hm
    | fault e => cases ho; exact hm
    | gap g => cases ho; exact hm
  · intro ho
    refine ⟨o, ho, ?_⟩
    cases o <;> rfl

theorem OutcomeSet.bind_assoc {Fault : Type uF} {Gap : Type uG}
    {Val : Type uV} {Val' : Type uV'} {Val'' : Type uV''}
    (S : OutcomeSet Fault Gap Val)
    (k₁ : Val → OutcomeSet Fault Gap Val')
    (k₂ : Val' → OutcomeSet Fault Gap Val'') :
    OutcomeSet.bind (OutcomeSet.bind S k₁) k₂ =
      OutcomeSet.bind S (fun v => OutcomeSet.bind (k₁ v) k₂) := by
  funext o; apply propext
  constructor
  · rintro ⟨m', ⟨m, hm, hm'⟩, ho⟩
    cases m with
    | ok v => exact ⟨.ok v, hm, m', hm', ho⟩
    | fault e =>
      cases hm'
      cases ho
      exact ⟨.fault e, hm, rfl⟩
    | gap g =>
      cases hm'
      cases ho
      exact ⟨.gap g, hm, rfl⟩
  · rintro ⟨m, hm, ho⟩
    cases m with
    | ok v =>
      obtain ⟨m', hm', ho'⟩ := ho
      exact ⟨m', ⟨.ok v, hm, hm'⟩, ho'⟩
    | fault e =>
      cases ho
      exact ⟨.fault e, ⟨.fault e, hm, rfl⟩, rfl⟩
    | gap g =>
      cases ho
      exact ⟨.gap g, ⟨.gap g, hm, rfl⟩, rfl⟩

/--
`OutcomeSet.bind S k` is gap-free exactly when `S` is gap-free and every
value `v` admitted by `S` has a gap-free continuation `k v`.
-/
theorem OutcomeSet.neverGap_bind_iff {Fault : Type uF} {Gap : Type uG}
    {Val : Type uV} {Val' : Type uV'}
    (S : OutcomeSet Fault Gap Val) (k : Val → OutcomeSet Fault Gap Val') :
    NeverGap (OutcomeSet.bind S k) ↔
      NeverGap S ∧ ∀ v, S (.ok v) → NeverGap (k v) := by
  constructor
  · intro h
    refine ⟨fun m hm => ?_, fun v hv o ho => h ⟨.ok v, hv, ho⟩⟩
    cases m with
    | ok v => trivial
    | fault e => trivial
    | gap g => exact h ⟨.gap g, hm, rfl⟩
  · rintro ⟨hS, hk⟩ o ⟨m, hm, ho⟩
    cases m with
    | ok v => exact hk v hm ho
    | fault e => cases ho; trivial
    | gap g => exact False.elim (hS hm)

private theorem OutcomeSetEquiv.forbid_bind_forward {Fault₁ : Type uF} {Fault₂ : Type uF'}
    {Gap₁ : Type uG} {Gap₂ : Type uG'} {ValA₁ : Type uV} {ValA₂ : Type uV'}
    {ValB₁ : Type uV''} {ValB₂ : Type uP}
    {rValA : ValA₁ → ValA₂ → Prop} {rValB : ValB₁ → ValB₂ → Prop}
    {rFault : Fault₁ → Fault₂ → Prop}
    {S₁ : OutcomeSet Fault₁ Gap₁ ValA₁} {S₂ : OutcomeSet Fault₂ Gap₂ ValA₂}
    {k₁ : ValA₁ → OutcomeSet Fault₁ Gap₁ ValB₁}
    {k₂ : ValA₂ → OutcomeSet Fault₂ Gap₂ ValB₂}
    (hS : OutcomeSetEquiv (GapForbidEq rValA rFault) S₁ S₂)
    (hk : ∀ a₁ a₂, rValA a₁ a₂ →
      OutcomeSetEquiv (GapForbidEq rValB rFault) (k₁ a₁) (k₂ a₂)) :
    ∀ ⦃o₁⦄, OutcomeSet.bind S₁ k₁ o₁ →
      ∃ o₂, OutcomeSet.bind S₂ k₂ o₂ ∧ GapForbidEq rValB rFault o₁ o₂ := by
  rintro o₁ ⟨m₁, hm₁, ho₁⟩
  obtain ⟨m₂, hm₂, hr⟩ := hS.forward hm₁
  cases m₁ with
  | ok a₁ =>
    cases m₂ with
    | ok a₂ =>
      obtain ⟨o₂, ho₂, hro⟩ := (hk a₁ a₂ hr).forward ho₁
      exact ⟨o₂, ⟨.ok a₂, hm₂, ho₂⟩, hro⟩
    | fault _ => exact False.elim hr
    | gap _ => exact False.elim hr
  | fault e₁ =>
    cases m₂ with
    | ok _ => exact False.elim hr
    | fault e₂ =>
      cases ho₁
      exact ⟨.fault e₂, ⟨.fault e₂, hm₂, rfl⟩, hr⟩
    | gap _ => exact False.elim hr
  | gap _ => exact False.elim hr.isGapFree_left

/--
Set-level `bind` congruence for gap-forbidding `GapForbidEq` across possibly
distinct gap alphabets.
-/
theorem OutcomeSetEquiv.forbid_bind_congr {Fault₁ : Type uF} {Fault₂ : Type uF'}
    {Gap₁ : Type uG} {Gap₂ : Type uG'} {ValA₁ : Type uV} {ValA₂ : Type uV'}
    {ValB₁ : Type uV''} {ValB₂ : Type uP}
    {rValA : ValA₁ → ValA₂ → Prop} {rValB : ValB₁ → ValB₂ → Prop}
    {rFault : Fault₁ → Fault₂ → Prop}
    {S₁ : OutcomeSet Fault₁ Gap₁ ValA₁} {S₂ : OutcomeSet Fault₂ Gap₂ ValA₂}
    {k₁ : ValA₁ → OutcomeSet Fault₁ Gap₁ ValB₁}
    {k₂ : ValA₂ → OutcomeSet Fault₂ Gap₂ ValB₂}
    (hS : OutcomeSetEquiv (GapForbidEq rValA rFault) S₁ S₂)
    (hk : ∀ a₁ a₂, rValA a₁ a₂ →
      OutcomeSetEquiv (GapForbidEq rValB rFault) (k₁ a₁) (k₂ a₂)) :
    OutcomeSetEquiv (GapForbidEq rValB rFault)
      (OutcomeSet.bind S₁ k₁) (OutcomeSet.bind S₂ k₂) where
  forward := forbid_bind_forward hS hk
  backward := by
    intro o₂ ho₂
    obtain ⟨o₁, ho₁, hr⟩ :=
      forbid_bind_forward (hS.flip.mono (fun _ _ h => h.flip))
        (fun a₂ a₁ ha => (hk a₁ a₂ ha).flip.mono (fun _ _ h => h.flip)) ho₂
    exact ⟨o₁, ho₁, hr.flip⟩

private theorem OutcomeSetEquiv.bind_forward {Fault₁ : Type uF} {Fault₂ : Type uF'}
    {Gap : Type uG} {ValA₁ : Type uV} {ValA₂ : Type uV'}
    {ValB₁ : Type uV''} {ValB₂ : Type uP}
    {rValA : ValA₁ → ValA₂ → Prop} {rValB : ValB₁ → ValB₂ → Prop}
    {rFault : Fault₁ → Fault₂ → Prop}
    {S₁ : OutcomeSet Fault₁ Gap ValA₁} {S₂ : OutcomeSet Fault₂ Gap ValA₂}
    {k₁ : ValA₁ → OutcomeSet Fault₁ Gap ValB₁}
    {k₂ : ValA₂ → OutcomeSet Fault₂ Gap ValB₂}
    (hS : OutcomeSetEquiv (GapEqErr rValA rFault) S₁ S₂)
    (hk : ∀ a₁ a₂, rValA a₁ a₂ →
      OutcomeSetEquiv (GapEqErr rValB rFault) (k₁ a₁) (k₂ a₂)) :
    ∀ ⦃o₁⦄, OutcomeSet.bind S₁ k₁ o₁ →
      ∃ o₂, OutcomeSet.bind S₂ k₂ o₂ ∧ GapEqErr rValB rFault o₁ o₂ := by
  rintro o₁ ⟨m₁, hm₁, ho₁⟩
  obtain ⟨m₂, hm₂, hr⟩ := hS.forward hm₁
  cases m₁ with
  | ok a₁ =>
    cases m₂ with
    | ok a₂ =>
      obtain ⟨o₂, ho₂, hro⟩ := (hk a₁ a₂ hr).forward ho₁
      exact ⟨o₂, ⟨.ok a₂, hm₂, ho₂⟩, hro⟩
    | fault _ => exact False.elim hr
    | gap _ => exact False.elim hr
  | fault e₁ =>
    cases m₂ with
    | ok _ => exact False.elim hr
    | fault e₂ =>
      cases ho₁
      exact ⟨.fault e₂, ⟨.fault e₂, hm₂, rfl⟩, hr⟩
    | gap _ => exact False.elim hr
  | gap g₁ =>
    cases m₂ with
    | ok _ => exact False.elim hr
    | fault _ => exact False.elim hr
    | gap g₂ =>
      cases ho₁
      exact ⟨.gap g₂, ⟨.gap g₂, hm₂, rfl⟩, hr⟩

/--
Set-level `bind` congruence: related prefixes followed by continuations that
are related on related values give related composites. Behaviors on which both
prefixes hit the identical gap are matched without consulting the
continuations.
-/
theorem OutcomeSetEquiv.bind_congr {Fault₁ : Type uF} {Fault₂ : Type uF'}
    {Gap : Type uG} {ValA₁ : Type uV} {ValA₂ : Type uV'}
    {ValB₁ : Type uV''} {ValB₂ : Type uP}
    {rValA : ValA₁ → ValA₂ → Prop} {rValB : ValB₁ → ValB₂ → Prop}
    {rFault : Fault₁ → Fault₂ → Prop}
    {S₁ : OutcomeSet Fault₁ Gap ValA₁} {S₂ : OutcomeSet Fault₂ Gap ValA₂}
    {k₁ : ValA₁ → OutcomeSet Fault₁ Gap ValB₁}
    {k₂ : ValA₂ → OutcomeSet Fault₂ Gap ValB₂}
    (hS : OutcomeSetEquiv (GapEqErr rValA rFault) S₁ S₂)
    (hk : ∀ a₁ a₂, rValA a₁ a₂ →
      OutcomeSetEquiv (GapEqErr rValB rFault) (k₁ a₁) (k₂ a₂)) :
    OutcomeSetEquiv (GapEqErr rValB rFault)
      (OutcomeSet.bind S₁ k₁) (OutcomeSet.bind S₂ k₂) where
  forward := bind_forward hS hk
  backward := by
    intro o₂ ho₂
    obtain ⟨o₁, ho₁, hr⟩ :=
      bind_forward (hS.flip.mono (fun _ _ h => h.flip))
        (fun a₂ a₁ ha => (hk a₁ a₂ ha).flip.mono (fun _ _ h => h.flip)) ho₂
    exact ⟨o₁, ho₁, hr.flip⟩

/-! #### Equivalence laws -/

section EquivLaws

variable {Query : Type uQ} {Fault₁ : Type uF} {Fault₂ : Type uF'}
  {Fault₃ : Type uF''} {Gap : Type uG} {Val₁ : Type uV} {Val₂ : Type uV'}
  {Val₃ : Type uV''}
  {pre : Query → Prop}
  {rVal : Val₁ → Val₂ → Prop} {rFault : Fault₁ → Fault₂ → Prop}
  {sem₁ : GapSem Query Fault₁ Gap Val₁} {sem₂ : GapSem Query Fault₂ Gap Val₂}

theorem contextEquiv_iff_on_true :
    ContextEquiv rVal rFault sem₁ sem₂ ↔
      ContextEquivOn (fun _ => True) rVal rFault sem₁ sem₂ :=
  ⟨fun h q _ => h q, fun h q => h q trivial⟩

theorem programEquiv_iff_on_true {Gap₁ : Type uG} {Gap₂ : Type uG'}
    {sem₁ : GapSem Query Fault₁ Gap₁ Val₁} {sem₂ : GapSem Query Fault₂ Gap₂ Val₂} :
    ProgramEquiv rVal rFault sem₁ sem₂ ↔
      ProgramEquivOn (fun _ => True) rVal rFault sem₁ sem₂ :=
  ⟨fun h q _ => h q, fun h q => h q trivial⟩

/-- `ContextEquivOn pre` is `ContextEquiv` over the query subtype `{q // pre q}`. -/
theorem contextEquivOn_iff_restrict :
    ContextEquivOn pre rVal rFault sem₁ sem₂ ↔
      ContextEquiv rVal rFault (sem₁.restrict pre) (sem₂.restrict pre) :=
  ⟨fun h q => h q.1 q.2, fun h q hq => h ⟨q, hq⟩⟩

theorem ContextEquiv.on (h : ContextEquiv rVal rFault sem₁ sem₂)
    (pre : Query → Prop) : ContextEquivOn pre rVal rFault sem₁ sem₂ :=
  fun q _ => h q

theorem ContextEquivOn.mono_pre {pre' : Query → Prop}
    (h : ContextEquivOn pre rVal rFault sem₁ sem₂) (hpre : ∀ q, pre' q → pre q) :
    ContextEquivOn pre' rVal rFault sem₁ sem₂ :=
  fun q hq => h q (hpre q hq)

theorem ContextEquivOn.mono {rVal' : Val₁ → Val₂ → Prop}
    {rFault' : Fault₁ → Fault₂ → Prop}
    (hVal : ∀ v₁ v₂, rVal v₁ v₂ → rVal' v₁ v₂)
    (hFault : ∀ e₁ e₂, rFault e₁ e₂ → rFault' e₁ e₂)
    (h : ContextEquivOn pre rVal rFault sem₁ sem₂) :
    ContextEquivOn pre rVal' rFault' sem₁ sem₂ :=
  fun q hq => (h q hq).mono (fun _ _ hr => hr.mono hVal hFault)

/--
`ContextEquivOn` is reflexive on *every* semantics, gap-free or not: an
unchanged program (or shared helper) is equivalent to itself with no
gap-freedom obligation.
-/
theorem ContextEquivOn.refl {Fault : Type uF} {Val : Type uV}
    {rVal : Val → Val → Prop} {rFault : Fault → Fault → Prop}
    (hVal : ∀ v, rVal v v) (hFault : ∀ e, rFault e e)
    (pre : Query → Prop) (sem : GapSem Query Fault Gap Val) :
    ContextEquivOn pre rVal rFault sem sem :=
  fun q _ => OutcomeSetEquiv.refl (GapEqErr.refl hVal hFault) (sem q)

theorem ContextEquivOn.flip (h : ContextEquivOn pre rVal rFault sem₁ sem₂) :
    ContextEquivOn pre (fun v₂ v₁ => rVal v₁ v₂) (fun e₂ e₁ => rFault e₁ e₂)
      sem₂ sem₁ :=
  fun q hq => (h q hq).flip.mono (fun _ _ hr => hr.flip)

theorem ContextEquivOn.symm {Fault : Type uF} {Val : Type uV}
    {rVal : Val → Val → Prop} {rFault : Fault → Fault → Prop}
    {sem₁ sem₂ : GapSem Query Fault Gap Val}
    (hVal : ∀ a b, rVal a b → rVal b a) (hFault : ∀ a b, rFault a b → rFault b a)
    (h : ContextEquivOn pre rVal rFault sem₁ sem₂) :
    ContextEquivOn pre rVal rFault sem₂ sem₁ :=
  fun q hq => (h q hq).symm (fun _ _ hr => hr.symm hVal hFault)

theorem ContextEquivOn.comp {rVal' : Val₂ → Val₃ → Prop}
    {rFault' : Fault₂ → Fault₃ → Prop} {sem₃ : GapSem Query Fault₃ Gap Val₃}
    (h₁₂ : ContextEquivOn pre rVal rFault sem₁ sem₂)
    (h₂₃ : ContextEquivOn pre rVal' rFault' sem₂ sem₃) :
    ContextEquivOn pre (fun v₁ v₃ => ∃ v₂, rVal v₁ v₂ ∧ rVal' v₂ v₃)
      (fun e₁ e₃ => ∃ e₂, rFault e₁ e₂ ∧ rFault' e₂ e₃) sem₁ sem₃ :=
  fun q hq => ((h₁₂ q hq).comp (h₂₃ q hq)).mono
    (fun _ _ h => by obtain ⟨_, hab, hbc⟩ := h; exact hab.comp hbc)

theorem ContextEquivOn.trans {Fault : Type uF} {Val : Type uV}
    {rVal : Val → Val → Prop} {rFault : Fault → Fault → Prop}
    {sem₁ sem₂ sem₃ : GapSem Query Fault Gap Val}
    (hVal : ∀ a b c, rVal a b → rVal b c → rVal a c)
    (hFault : ∀ a b c, rFault a b → rFault b c → rFault a c)
    (h₁₂ : ContextEquivOn pre rVal rFault sem₁ sem₂)
    (h₂₃ : ContextEquivOn pre rVal rFault sem₂ sem₃) :
    ContextEquivOn pre rVal rFault sem₁ sem₃ :=
  fun q hq => (h₁₂ q hq).trans (fun _ _ _ hab hbc => hab.trans hVal hFault hbc)
    (h₂₃ q hq)

/-- Equivalent programs are gap-free on exactly the same queries. -/
theorem ContextEquivOn.neverGap_iff
    (h : ContextEquivOn pre rVal rFault sem₁ sem₂) {q : Query} (hq : pre q) :
    NeverGap (sem₁ q) ↔ NeverGap (sem₂ q) :=
  (h q hq).neverGap_iff

/--
Per-query gap-freedom transfer: if the baseline is gap-free on `q`, so is the
refactored program, since any gap of the latter would have to match the
identical gap of the former.
-/
theorem ContextEquivOn.gapFree_right_of_gapFree_left
    (h : ContextEquivOn pre rVal rFault sem₁ sem₂) {q : Query} (hq : pre q)
    (h₁ : NeverGap (sem₁ q)) : NeverGap (sem₂ q) :=
  (h.neverGap_iff hq).mp h₁

theorem ContextEquivOn.gapFree_left_of_gapFree_right
    (h : ContextEquivOn pre rVal rFault sem₁ sem₂) {q : Query} (hq : pre q)
    (h₂ : NeverGap (sem₂ q)) : NeverGap (sem₁ q) :=
  (h.neverGap_iff hq).mpr h₂

theorem ContextEquivOn.gapFreeOn_right
    (h : ContextEquivOn pre rVal rFault sem₁ sem₂) (h₁ : GapFreeOn pre sem₁) :
    GapFreeOn pre sem₂ :=
  fun q hq => h.gapFree_right_of_gapFree_left hq (h₁ q hq)

/--
Upgrade `ContextEquivOn pre` to gap-free `ProgramEquivOn pre` from gap-freedom
of the baseline alone; gap-freedom of the refactored program is a consequence.
-/
theorem ContextEquivOn.toProgramEquivOn
    (h : ContextEquivOn pre rVal rFault sem₁ sem₂) (h₁ : GapFreeOn pre sem₁) :
    ProgramEquivOn pre rVal rFault sem₁ sem₂ :=
  fun q hq => (h q hq).forbid_of_neverGap_left (h₁ q hq)

theorem ContextEquivOn.toProgramEquivOn_of_right
    (h : ContextEquivOn pre rVal rFault sem₁ sem₂) (h₂ : GapFreeOn pre sem₂) :
    ProgramEquivOn pre rVal rFault sem₁ sem₂ :=
  fun q hq => (h q hq).forbid_of_neverGap_right (h₂ q hq)

/--
`ContextEquivOn` is `ProgramEquivOn` on the gap-free queries of the baseline,
the largest query set on which the upgrade can hold.
-/
theorem ContextEquivOn.toProgramEquivOn_gapFree
    (h : ContextEquivOn pre rVal rFault sem₁ sem₂) :
    ProgramEquivOn (fun q => pre q ∧ NeverGap (sem₁ q)) rVal rFault sem₁ sem₂ :=
  fun q hq => (h q hq.1).forbid_of_neverGap_left hq.2

/-- Characterization of gap-free `ProgramEquivOn` on a shared gap alphabet. -/
theorem programEquivOn_iff :
    ProgramEquivOn pre rVal rFault sem₁ sem₂ ↔
      GapFreeOn pre sem₁ ∧ GapFreeOn pre sem₂ ∧
        ContextEquivOn pre rVal rFault sem₁ sem₂ :=
  ⟨fun h =>
      ⟨fun q hq => (OutcomeSetEquiv.forbid_iff.mp (h q hq)).1,
       fun q hq => (OutcomeSetEquiv.forbid_iff.mp (h q hq)).2.1,
       fun q hq => (OutcomeSetEquiv.forbid_iff.mp (h q hq)).2.2⟩,
   fun h => h.2.2.toProgramEquivOn h.1⟩

/-- Every gap-free `ProgramEquivOn` is immediately a `ContextEquivOn`. -/
theorem ProgramEquivOn.toContextEquivOn
    (h : ProgramEquivOn pre rVal rFault sem₁ sem₂) :
    ContextEquivOn pre rVal rFault sem₁ sem₂ :=
  (programEquivOn_iff.mp h).2.2

theorem ContextEquiv.refl {Fault : Type uF} {Val : Type uV}
    {rVal : Val → Val → Prop} {rFault : Fault → Fault → Prop}
    (hVal : ∀ v, rVal v v) (hFault : ∀ e, rFault e e)
    (sem : GapSem Query Fault Gap Val) : ContextEquiv rVal rFault sem sem :=
  fun q => OutcomeSetEquiv.refl (GapEqErr.refl hVal hFault) (sem q)

theorem ContextEquiv.flip (h : ContextEquiv rVal rFault sem₁ sem₂) :
    ContextEquiv (fun v₂ v₁ => rVal v₁ v₂) (fun e₂ e₁ => rFault e₁ e₂) sem₂ sem₁ :=
  fun q => (h q).flip.mono (fun _ _ hr => hr.flip)

theorem ContextEquiv.symm {Fault : Type uF} {Val : Type uV}
    {rVal : Val → Val → Prop} {rFault : Fault → Fault → Prop}
    {sem₁ sem₂ : GapSem Query Fault Gap Val}
    (hVal : ∀ a b, rVal a b → rVal b a) (hFault : ∀ a b, rFault a b → rFault b a)
    (h : ContextEquiv rVal rFault sem₁ sem₂) : ContextEquiv rVal rFault sem₂ sem₁ :=
  fun q => (h q).symm (fun _ _ hr => hr.symm hVal hFault)

theorem ContextEquiv.comp {rVal' : Val₂ → Val₃ → Prop}
    {rFault' : Fault₂ → Fault₃ → Prop} {sem₃ : GapSem Query Fault₃ Gap Val₃}
    (h₁₂ : ContextEquiv rVal rFault sem₁ sem₂)
    (h₂₃ : ContextEquiv rVal' rFault' sem₂ sem₃) :
    ContextEquiv (fun v₁ v₃ => ∃ v₂, rVal v₁ v₂ ∧ rVal' v₂ v₃)
      (fun e₁ e₃ => ∃ e₂, rFault e₁ e₂ ∧ rFault' e₂ e₃) sem₁ sem₃ :=
  fun q => ((h₁₂ q).comp (h₂₃ q)).mono
    (fun _ _ h => by obtain ⟨_, hab, hbc⟩ := h; exact hab.comp hbc)

theorem ContextEquiv.trans {Fault : Type uF} {Val : Type uV}
    {rVal : Val → Val → Prop} {rFault : Fault → Fault → Prop}
    {sem₁ sem₂ sem₃ : GapSem Query Fault Gap Val}
    (hVal : ∀ a b c, rVal a b → rVal b c → rVal a c)
    (hFault : ∀ a b c, rFault a b → rFault b c → rFault a c)
    (h₁₂ : ContextEquiv rVal rFault sem₁ sem₂)
    (h₂₃ : ContextEquiv rVal rFault sem₂ sem₃) :
    ContextEquiv rVal rFault sem₁ sem₃ :=
  fun q => (h₁₂ q).trans (fun _ _ _ hab hbc => hab.trans hVal hFault hbc) (h₂₃ q)

theorem ContextEquiv.mono {rVal' : Val₁ → Val₂ → Prop}
    {rFault' : Fault₁ → Fault₂ → Prop}
    (hVal : ∀ v₁ v₂, rVal v₁ v₂ → rVal' v₁ v₂)
    (hFault : ∀ e₁ e₂, rFault e₁ e₂ → rFault' e₁ e₂)
    (h : ContextEquiv rVal rFault sem₁ sem₂) :
    ContextEquiv rVal' rFault' sem₁ sem₂ :=
  fun q => (h q).mono (fun _ _ hr => hr.mono hVal hFault)

theorem ContextEquiv.neverGap_iff (h : ContextEquiv rVal rFault sem₁ sem₂)
    (q : Query) : NeverGap (sem₁ q) ↔ NeverGap (sem₂ q) :=
  (h q).neverGap_iff

theorem ContextEquiv.mapGap_iff_of_injective {Gap' : Type uG'} {f : Gap → Gap'}
    (hinj : ∀ g₁ g₂, f g₁ = f g₂ → g₁ = g₂) :
    ContextEquiv rVal rFault
        (fun q => OutcomeSet.mapGap f (sem₁ q))
        (fun q => OutcomeSet.mapGap f (sem₂ q)) ↔
      ContextEquiv rVal rFault sem₁ sem₂ :=
  ⟨fun h q => (OutcomeSetEquiv.mapGap_iff_of_injective hinj).mp (h q),
   fun h q => (OutcomeSetEquiv.mapGap_iff_of_injective hinj).mpr (h q)⟩

/--
Constructive boolean partition patching for `ContextEquivOn`: combine two
`ContextEquivOn` proofs across complementary branches `p q = true` and
`p q = false` without `Classical.choice`.
-/
theorem ContextEquivOn.piecewise_bool (p : Query → Bool)
    (hTrue : ContextEquivOn (fun q => pre q ∧ p q = true) rVal rFault sem₁ sem₂)
    (hFalse : ContextEquivOn (fun q => pre q ∧ p q = false) rVal rFault sem₁ sem₂) :
    ContextEquivOn pre rVal rFault sem₁ sem₂ := by
  intro q hpre
  cases hp : p q with
  | true => exact hTrue q ⟨hpre, hp⟩
  | false => exact hFalse q ⟨hpre, hp⟩

/--
Constructive fast-path + fallback patching: combine gap-free `ProgramEquivOn`
on a verified fast-path (`p q = true`) with gap-preserving `ContextEquivOn` on
an unmodeled fallback branch (`p q = false`) into a full-domain `ContextEquiv`,
using zero `Classical.choice`.
-/
theorem ContextEquiv.of_boolPartition (p : Query → Bool)
    (hFast : ProgramEquivOn (fun q => p q = true) rVal rFault sem₁ sem₂)
    (hFallback : ContextEquivOn (fun q => p q = false) rVal rFault sem₁ sem₂) :
    ContextEquiv rVal rFault sem₁ sem₂ := by
  intro q
  cases hp : p q with
  | true => exact hFast.toContextEquivOn q hp
  | false => exact hFallback q hp

/--
Per-query gap-freedom transfer for `ContextEquiv`: gap-freedom of the baseline
on `q` yields gap-freedom of the refactored program on `q`.
-/
theorem ContextEquiv.gapFree_right_of_gapFree_left
    (h : ContextEquiv rVal rFault sem₁ sem₂) {q : Query}
    (h₁ : NeverGap (sem₁ q)) : NeverGap (sem₂ q) :=
  (h.neverGap_iff q).mp h₁

theorem ContextEquiv.gapFree_left_of_gapFree_right
    (h : ContextEquiv rVal rFault sem₁ sem₂) {q : Query}
    (h₂ : NeverGap (sem₂ q)) : NeverGap (sem₁ q) :=
  (h.neverGap_iff q).mpr h₂

/--
Upgrade `ContextEquiv` to full gap-free `ProgramEquiv` from gap-freedom of the
baseline alone.
-/
theorem ContextEquiv.toProgramEquiv (h : ContextEquiv rVal rFault sem₁ sem₂)
    (h₁ : AllGapFree sem₁) : ProgramEquiv rVal rFault sem₁ sem₂ :=
  fun q => (h q).forbid_of_neverGap_left (h₁ q)

theorem ContextEquiv.toProgramEquiv_of_right
    (h : ContextEquiv rVal rFault sem₁ sem₂) (h₂ : AllGapFree sem₂) :
    ProgramEquiv rVal rFault sem₁ sem₂ :=
  fun q => (h q).forbid_of_neverGap_right (h₂ q)

/--
Query-scoped upgrade of `ContextEquiv`: gap-free `ProgramEquivOn pre` from
gap-freedom of the baseline on the queries satisfying `pre`.
-/
theorem ContextEquiv.toProgramEquivOn (h : ContextEquiv rVal rFault sem₁ sem₂)
    (h₁ : GapFreeOn pre sem₁) : ProgramEquivOn pre rVal rFault sem₁ sem₂ :=
  (h.on pre).toProgramEquivOn h₁

/-- Characterization of gap-free `ProgramEquiv` on a shared gap alphabet. -/
theorem programEquiv_iff :
    ProgramEquiv rVal rFault sem₁ sem₂ ↔
      AllGapFree sem₁ ∧ AllGapFree sem₂ ∧ ContextEquiv rVal rFault sem₁ sem₂ :=
  ⟨fun h =>
      ⟨fun q => (OutcomeSetEquiv.forbid_iff.mp (h q)).1,
       fun q => (OutcomeSetEquiv.forbid_iff.mp (h q)).2.1,
       fun q => (OutcomeSetEquiv.forbid_iff.mp (h q)).2.2⟩,
   fun h => h.2.2.toProgramEquiv h.1⟩

/-- Every gap-free `ProgramEquiv` is immediately a `ContextEquiv`. -/
theorem ProgramEquiv.toContextEquiv (h : ProgramEquiv rVal rFault sem₁ sem₂) :
    ContextEquiv rVal rFault sem₁ sem₂ :=
  (programEquiv_iff.mp h).2.2

/-- Sequential-composition congruence for query-indexed semantics. -/
theorem ContextEquivOn.bind_congr {ValB₁ : Type uV''} {ValB₂ : Type uP}
    {rValB : ValB₁ → ValB₂ → Prop}
    {k₁ : Query → Val₁ → OutcomeSet Fault₁ Gap ValB₁}
    {k₂ : Query → Val₂ → OutcomeSet Fault₂ Gap ValB₂}
    (h : ContextEquivOn pre rVal rFault sem₁ sem₂)
    (hk : ∀ q, pre q → ∀ a₁ a₂, rVal a₁ a₂ →
      OutcomeSetEquiv (GapEqErr rValB rFault) (k₁ q a₁) (k₂ q a₂)) :
    ContextEquivOn pre rValB rFault (sem₁.bind k₁) (sem₂.bind k₂) :=
  fun q hq => (h q hq).bind_congr (hk q hq)

theorem ContextEquiv.bind_congr {ValB₁ : Type uV''} {ValB₂ : Type uP}
    {rValB : ValB₁ → ValB₂ → Prop}
    {k₁ : Query → Val₁ → OutcomeSet Fault₁ Gap ValB₁}
    {k₂ : Query → Val₂ → OutcomeSet Fault₂ Gap ValB₂}
    (h : ContextEquiv rVal rFault sem₁ sem₂)
    (hk : ∀ q a₁ a₂, rVal a₁ a₂ →
      OutcomeSetEquiv (GapEqErr rValB rFault) (k₁ q a₁) (k₂ q a₂)) :
    ContextEquiv rValB rFault (sem₁.bind k₁) (sem₂.bind k₂) :=
  fun q => (h q).bind_congr (hk q)

/-- On deterministic evaluators `ContextEquivOn` is pointwise `GapEqErr`. -/
theorem contextEquivOn_det_iff
    {f₁ : Query → OutcomeWithGap Fault₁ Gap Val₁}
    {f₂ : Query → OutcomeWithGap Fault₂ Gap Val₂} :
    ContextEquivOn pre rVal rFault (GapSem.det f₁) (GapSem.det f₂) ↔
      ∀ q, pre q → GapEqErr rVal rFault (f₁ q) (f₂ q) :=
  ⟨fun h q hq => OutcomeSetEquiv.singleton_iff.mp (h q hq),
   fun h q hq => OutcomeSetEquiv.singleton_iff.mpr (h q hq)⟩

theorem contextEquiv_det_iff
    {f₁ : Query → OutcomeWithGap Fault₁ Gap Val₁}
    {f₂ : Query → OutcomeWithGap Fault₂ Gap Val₂} :
    ContextEquiv rVal rFault (GapSem.det f₁) (GapSem.det f₂) ↔
      ∀ q, GapEqErr rVal rFault (f₁ q) (f₂ q) :=
  ⟨fun h q => OutcomeSetEquiv.singleton_iff.mp (h q),
   fun h q => OutcomeSetEquiv.singleton_iff.mpr (h q)⟩

theorem gapFreeOn_det_iff {f : Query → OutcomeWithGap Fault₁ Gap Val₁} :
    GapFreeOn pre (GapSem.det f) ↔ ∀ q, pre q → (f q).isGapFree :=
  ⟨fun h q hq => neverGap_singleton_iff.mp (h q hq),
   fun h q hq => neverGap_singleton_iff.mpr (h q hq)⟩

/-- Binary union of query-scoped `ContextEquivOn` certificates (`0` `Classical.choice`). -/
theorem ContextEquivOn.sup {pre₁ pre₂ : Query → Prop}
    (h₁ : ContextEquivOn pre₁ rVal rFault sem₁ sem₂)
    (h₂ : ContextEquivOn pre₂ rVal rFault sem₁ sem₂) :
    ContextEquivOn (fun q => pre₁ q ∨ pre₂ q) rVal rFault sem₁ sem₂
  | q, .inl hp₁ => h₁ q hp₁
  | q, .inr hp₂ => h₂ q hp₂

/-- Indexed family union of `ContextEquivOn` certificates (e.g., `switchInt` or enum arms). -/
theorem ContextEquivOn.iSup {ι : Sort uP} {P : ι → Query → Prop}
    (h : ∀ i, ContextEquivOn (P i) rVal rFault sem₁ sem₂) :
    ContextEquivOn (fun q => ∃ i, P i q) rVal rFault sem₁ sem₂
  | q, ⟨i, hi⟩ => h i q hi

/-- Constructive binary-cover patching into full `ContextEquiv`. -/
theorem ContextEquiv.of_cover {pre₁ pre₂ : Query → Prop}
    (hCover : ∀ q, pre₁ q ∨ pre₂ q)
    (h₁ : ContextEquivOn pre₁ rVal rFault sem₁ sem₂)
    (h₂ : ContextEquivOn pre₂ rVal rFault sem₁ sem₂) :
    ContextEquiv rVal rFault sem₁ sem₂ :=
  fun q => (h₁.sup h₂) q (hCover q)

/-- Constructive indexed-cover patching into full `ContextEquiv`. -/
theorem ContextEquiv.of_iSup_cover {ι : Sort uP} {P : ι → Query → Prop}
    (hCover : ∀ q, ∃ i, P i q)
    (h : ∀ i, ContextEquivOn (P i) rVal rFault sem₁ sem₂) :
    ContextEquiv rVal rFault sem₁ sem₂ :=
  fun q => (ContextEquivOn.iSup h) q (hCover q)

end EquivLaws

section ProgramEquivLaws

variable {Query : Type uQ} {Fault₁ : Type uF} {Fault₂ : Type uF'}
  {Fault₃ : Type uF''} {Gap₁ : Type uG} {Gap₂ : Type uG'} {Gap₃ : Type uG''}
  {Val₁ : Type uV} {Val₂ : Type uV'} {Val₃ : Type uV''}
  {pre : Query → Prop}
  {rVal : Val₁ → Val₂ → Prop} {rFault : Fault₁ → Fault₂ → Prop}
  {sem₁ : GapSem Query Fault₁ Gap₁ Val₁} {sem₂ : GapSem Query Fault₂ Gap₂ Val₂}

theorem ProgramEquiv.on (h : ProgramEquiv rVal rFault sem₁ sem₂)
    (pre : Query → Prop) : ProgramEquivOn pre rVal rFault sem₁ sem₂ :=
  fun q _ => h q

theorem ProgramEquivOn.mono_pre {pre' : Query → Prop}
    (h : ProgramEquivOn pre rVal rFault sem₁ sem₂) (hpre : ∀ q, pre' q → pre q) :
    ProgramEquivOn pre' rVal rFault sem₁ sem₂ :=
  fun q hq => h q (hpre q hq)

theorem ProgramEquivOn.mono {rVal' : Val₁ → Val₂ → Prop}
    {rFault' : Fault₁ → Fault₂ → Prop}
    (hVal : ∀ v₁ v₂, rVal v₁ v₂ → rVal' v₁ v₂)
    (hFault : ∀ e₁ e₂, rFault e₁ e₂ → rFault' e₁ e₂)
    (h : ProgramEquivOn pre rVal rFault sem₁ sem₂) :
    ProgramEquivOn pre rVal' rFault' sem₁ sem₂ :=
  fun q hq => (h q hq).mono (fun _ _ hr => hr.mono hVal hFault)

/-- A `ProgramEquivOn pre` baseline is gap-free on `pre`. -/
theorem ProgramEquivOn.gapFree_left
    (h : ProgramEquivOn pre rVal rFault sem₁ sem₂) : GapFreeOn pre sem₁ := by
  intro q hq _ ho₁
  obtain ⟨_, _, hr⟩ := (h q hq).forward ho₁
  exact hr.isGapFree_left

/-- A `ProgramEquivOn pre` refactored program is gap-free on `pre`. -/
theorem ProgramEquivOn.gapFree_right
    (h : ProgramEquivOn pre rVal rFault sem₁ sem₂) : GapFreeOn pre sem₂ := by
  intro q hq _ ho₂
  obtain ⟨_, _, hr⟩ := (h q hq).backward ho₂
  exact hr.isGapFree_right

theorem ProgramEquivOn.flip (h : ProgramEquivOn pre rVal rFault sem₁ sem₂) :
    ProgramEquivOn pre (fun v₂ v₁ => rVal v₁ v₂) (fun e₂ e₁ => rFault e₁ e₂)
      sem₂ sem₁ :=
  fun q hq => (h q hq).flip.mono (fun _ _ hr => hr.flip)

theorem ProgramEquivOn.comp {rVal' : Val₂ → Val₃ → Prop}
    {rFault' : Fault₂ → Fault₃ → Prop} {sem₃ : GapSem Query Fault₃ Gap₃ Val₃}
    (h₁₂ : ProgramEquivOn pre rVal rFault sem₁ sem₂)
    (h₂₃ : ProgramEquivOn pre rVal' rFault' sem₂ sem₃) :
    ProgramEquivOn pre (fun v₁ v₃ => ∃ v₂, rVal v₁ v₂ ∧ rVal' v₂ v₃)
      (fun e₁ e₃ => ∃ e₂, rFault e₁ e₂ ∧ rFault' e₂ e₃) sem₁ sem₃ :=
  fun q hq => ((h₁₂ q hq).comp (h₂₃ q hq)).mono
    (fun _ _ h => by obtain ⟨_, hab, hbc⟩ := h; exact hab.comp hbc)

/--
Gap-free `ProgramEquivOn` is reflexive exactly on the semantics that are
gap-free on `pre`: unlike `ContextEquivOn.refl`, it carries a gap-freedom
obligation.
-/
theorem ProgramEquivOn.refl {Fault : Type uF} {Gap : Type uG} {Val : Type uV}
    {rVal : Val → Val → Prop} {rFault : Fault → Fault → Prop}
    (hVal : ∀ v, rVal v v) (hFault : ∀ e, rFault e e)
    {sem : GapSem Query Fault Gap Val} (hgf : GapFreeOn pre sem) :
    ProgramEquivOn pre rVal rFault sem sem :=
  (ContextEquivOn.refl hVal hFault pre sem).toProgramEquivOn hgf

theorem ProgramEquivOn.refl_iff {Fault : Type uF} {Gap : Type uG} {Val : Type uV}
    {rVal : Val → Val → Prop} {rFault : Fault → Fault → Prop}
    (hVal : ∀ v, rVal v v) (hFault : ∀ e, rFault e e)
    {sem : GapSem Query Fault Gap Val} :
    ProgramEquivOn pre rVal rFault sem sem ↔ GapFreeOn pre sem :=
  ⟨fun h => h.gapFree_left, ProgramEquivOn.refl hVal hFault⟩

theorem ProgramEquivOn.symm {Fault : Type uF} {Gap : Type uG} {Val : Type uV}
    {rVal : Val → Val → Prop} {rFault : Fault → Fault → Prop}
    {sem₁ sem₂ : GapSem Query Fault Gap Val}
    (hVal : ∀ a b, rVal a b → rVal b a) (hFault : ∀ a b, rFault a b → rFault b a)
    (h : ProgramEquivOn pre rVal rFault sem₁ sem₂) :
    ProgramEquivOn pre rVal rFault sem₂ sem₁ :=
  h.flip.mono (fun b a => hVal a b) (fun b a => hFault a b)

theorem ProgramEquivOn.trans {Fault : Type uF} {Gap : Type uG} {Val : Type uV}
    {rVal : Val → Val → Prop} {rFault : Fault → Fault → Prop}
    {sem₁ sem₂ sem₃ : GapSem Query Fault Gap Val}
    (hVal : ∀ a b c, rVal a b → rVal b c → rVal a c)
    (hFault : ∀ a b c, rFault a b → rFault b c → rFault a c)
    (h₁₂ : ProgramEquivOn pre rVal rFault sem₁ sem₂)
    (h₂₃ : ProgramEquivOn pre rVal rFault sem₂ sem₃) :
    ProgramEquivOn pre rVal rFault sem₁ sem₃ :=
  (h₁₂.comp h₂₃).mono
    (fun a c h => by obtain ⟨b, hab, hbc⟩ := h; exact hVal a b c hab hbc)
    (fun a c h => by obtain ⟨b, hab, hbc⟩ := h; exact hFault a b c hab hbc)

theorem ProgramEquiv.gapFree_left (h : ProgramEquiv rVal rFault sem₁ sem₂) :
    AllGapFree sem₁ :=
  fun q => (h.on (fun _ => True)).gapFree_left q trivial

theorem ProgramEquiv.gapFree_right (h : ProgramEquiv rVal rFault sem₁ sem₂) :
    AllGapFree sem₂ :=
  fun q => (h.on (fun _ => True)).gapFree_right q trivial

theorem ProgramEquiv.flip (h : ProgramEquiv rVal rFault sem₁ sem₂) :
    ProgramEquiv (fun v₂ v₁ => rVal v₁ v₂) (fun e₂ e₁ => rFault e₁ e₂) sem₂ sem₁ :=
  fun q => (h q).flip.mono (fun _ _ hr => hr.flip)

theorem ProgramEquiv.comp {rVal' : Val₂ → Val₃ → Prop}
    {rFault' : Fault₂ → Fault₃ → Prop} {sem₃ : GapSem Query Fault₃ Gap₃ Val₃}
    (h₁₂ : ProgramEquiv rVal rFault sem₁ sem₂)
    (h₂₃ : ProgramEquiv rVal' rFault' sem₂ sem₃) :
    ProgramEquiv (fun v₁ v₃ => ∃ v₂, rVal v₁ v₂ ∧ rVal' v₂ v₃)
      (fun e₁ e₃ => ∃ e₂, rFault e₁ e₂ ∧ rFault' e₂ e₃) sem₁ sem₃ :=
  fun q => ((h₁₂ q).comp (h₂₃ q)).mono
    (fun _ _ h => by obtain ⟨_, hab, hbc⟩ := h; exact hab.comp hbc)

theorem ProgramEquiv.mono {rVal' : Val₁ → Val₂ → Prop}
    {rFault' : Fault₁ → Fault₂ → Prop}
    (hVal : ∀ v₁ v₂, rVal v₁ v₂ → rVal' v₁ v₂)
    (hFault : ∀ e₁ e₂, rFault e₁ e₂ → rFault' e₁ e₂)
    (h : ProgramEquiv rVal rFault sem₁ sem₂) :
    ProgramEquiv rVal' rFault' sem₁ sem₂ :=
  fun q => (h q).mono (fun _ _ hr => hr.mono hVal hFault)

/-- Gap-free `ProgramEquiv` is reflexive exactly on gap-free semantics. -/
theorem ProgramEquiv.refl {Fault : Type uF} {Gap : Type uG} {Val : Type uV}
    {rVal : Val → Val → Prop} {rFault : Fault → Fault → Prop}
    (hVal : ∀ v, rVal v v) (hFault : ∀ e, rFault e e)
    {sem : GapSem Query Fault Gap Val} (hgf : AllGapFree sem) :
    ProgramEquiv rVal rFault sem sem :=
  (ContextEquiv.refl hVal hFault sem).toProgramEquiv hgf

theorem ProgramEquiv.refl_iff {Fault : Type uF} {Gap : Type uG} {Val : Type uV}
    {rVal : Val → Val → Prop} {rFault : Fault → Fault → Prop}
    (hVal : ∀ v, rVal v v) (hFault : ∀ e, rFault e e)
    {sem : GapSem Query Fault Gap Val} :
    ProgramEquiv rVal rFault sem sem ↔ AllGapFree sem :=
  ⟨fun h => h.gapFree_left, ProgramEquiv.refl hVal hFault⟩

theorem ProgramEquiv.symm {Fault : Type uF} {Gap : Type uG} {Val : Type uV}
    {rVal : Val → Val → Prop} {rFault : Fault → Fault → Prop}
    {sem₁ sem₂ : GapSem Query Fault Gap Val}
    (hVal : ∀ a b, rVal a b → rVal b a) (hFault : ∀ a b, rFault a b → rFault b a)
    (h : ProgramEquiv rVal rFault sem₁ sem₂) : ProgramEquiv rVal rFault sem₂ sem₁ :=
  h.flip.mono (fun b a => hVal a b) (fun b a => hFault a b)

theorem ProgramEquiv.trans {Fault : Type uF} {Gap : Type uG} {Val : Type uV}
    {rVal : Val → Val → Prop} {rFault : Fault → Fault → Prop}
    {sem₁ sem₂ sem₃ : GapSem Query Fault Gap Val}
    (hVal : ∀ a b c, rVal a b → rVal b c → rVal a c)
    (hFault : ∀ a b c, rFault a b → rFault b c → rFault a c)
    (h₁₂ : ProgramEquiv rVal rFault sem₁ sem₂)
    (h₂₃ : ProgramEquiv rVal rFault sem₂ sem₃) :
    ProgramEquiv rVal rFault sem₁ sem₃ :=
  (h₁₂.comp h₂₃).mono
    (fun a c h => by obtain ⟨b, hab, hbc⟩ := h; exact hVal a b c hab hbc)
    (fun a c h => by obtain ⟨b, hab, hbc⟩ := h; exact hFault a b c hab hbc)

/-- Sequential-composition congruence for gap-free `ProgramEquivOn`. -/
theorem ProgramEquivOn.bind_congr {ValB₁ : Type uV''} {ValB₂ : Type uP}
    {rValB : ValB₁ → ValB₂ → Prop}
    {k₁ : Query → Val₁ → OutcomeSet Fault₁ Gap₁ ValB₁}
    {k₂ : Query → Val₂ → OutcomeSet Fault₂ Gap₂ ValB₂}
    (h : ProgramEquivOn pre rVal rFault sem₁ sem₂)
    (hk : ∀ q, pre q → ∀ a₁ a₂, rVal a₁ a₂ →
      OutcomeSetEquiv (GapForbidEq rValB rFault) (k₁ q a₁) (k₂ q a₂)) :
    ProgramEquivOn pre rValB rFault (sem₁.bind k₁) (sem₂.bind k₂) :=
  fun q hq => (h q hq).forbid_bind_congr (hk q hq)

theorem ProgramEquiv.bind_congr {ValB₁ : Type uV''} {ValB₂ : Type uP}
    {rValB : ValB₁ → ValB₂ → Prop}
    {k₁ : Query → Val₁ → OutcomeSet Fault₁ Gap₁ ValB₁}
    {k₂ : Query → Val₂ → OutcomeSet Fault₂ Gap₂ ValB₂}
    (h : ProgramEquiv rVal rFault sem₁ sem₂)
    (hk : ∀ q a₁ a₂, rVal a₁ a₂ →
      OutcomeSetEquiv (GapForbidEq rValB rFault) (k₁ q a₁) (k₂ q a₂)) :
    ProgramEquiv rValB rFault (sem₁.bind k₁) (sem₂.bind k₂) :=
  fun q => (h q).forbid_bind_congr (hk q)

/-- On deterministic evaluators `ProgramEquivOn` is pointwise `GapForbidEq`. -/
theorem programEquivOn_det_iff
    {f₁ : Query → OutcomeWithGap Fault₁ Gap₁ Val₁}
    {f₂ : Query → OutcomeWithGap Fault₂ Gap₂ Val₂} :
    ProgramEquivOn pre rVal rFault (GapSem.det f₁) (GapSem.det f₂) ↔
      ∀ q, pre q → GapForbidEq rVal rFault (f₁ q) (f₂ q) :=
  ⟨fun h q hq => OutcomeSetEquiv.singleton_iff.mp (h q hq),
   fun h q hq => OutcomeSetEquiv.singleton_iff.mpr (h q hq)⟩

theorem programEquiv_det_iff
    {f₁ : Query → OutcomeWithGap Fault₁ Gap₁ Val₁}
    {f₂ : Query → OutcomeWithGap Fault₂ Gap₂ Val₂} :
    ProgramEquiv rVal rFault (GapSem.det f₁) (GapSem.det f₂) ↔
      ∀ q, GapForbidEq rVal rFault (f₁ q) (f₂ q) :=
  ⟨fun h q => OutcomeSetEquiv.singleton_iff.mp (h q),
   fun h q => OutcomeSetEquiv.singleton_iff.mpr (h q)⟩

end ProgramEquivLaws

/-! ### Bridges to Layer 1A `Partial`, `Language`, and Pass Specializations

Layer 1A's Smyth `Partial` domain has a single undefined element, so the
projection `OutcomeSet.toPartial` maps both UB faults and modeling gaps to
"undefined" (exactly as `ITree.toPartial` does through `TreeSafe`). A
`ContextEquiv` whose fault relation preserves UB-ness transfers definedness in
both directions, and therefore induces an `ExactPass` (hence `CompilerPass`
and `VerifierPass`) on these projections without any gap-freedom proof for
shared code. Gap-freedom and UB-freedom of the baseline are what make the
induced pass non-vacuous: they establish definedness of both programs.
-/

section LayerOneABridges

variable {Query : Type uQ} {Fault₁ : Type uF} {Fault₂ : Type uF'} {Gap : Type uG}
  {Val₁ : Type uV} {Val₂ : Type uV'}
  {rVal : Val₁ → Val₂ → Prop} {rFault : Fault₁ → Fault₂ → Prop}
  {isUB₁ : Fault₁ → Prop} {isUB₂ : Fault₂ → Prop}

/-- No behavior in `S` is an undefined-behavior fault. -/
def OutcomeSet.NoUB (isUB : Fault₁ → Prop) (S : OutcomeSet Fault₁ Gap Val₁) : Prop :=
  ∀ ⦃e⦄, S (.fault e) → ¬ isUB e

/-- Every behavior in `S` is defined: no modeling gap and no UB fault. -/
def OutcomeSet.Defined (isUB : Fault₁ → Prop) (S : OutcomeSet Fault₁ Gap Val₁) :
    Prop :=
  ∀ ⦃o⦄, S o → o.isDefined isUB

theorem OutcomeSet.defined_iff {S : OutcomeSet Fault₁ Gap Val₁} :
    OutcomeSet.Defined isUB₁ S ↔ NeverGap S ∧ OutcomeSet.NoUB isUB₁ S := by
  constructor
  · intro h
    exact ⟨fun _ ho => (h ho).isGapFree, fun _ he => h he⟩
  · rintro ⟨hg, hu⟩ o ho
    cases o with
    | ok v => trivial
    | fault e => exact hu ho
    | gap g => exact hg ho

theorem OutcomeSet.defined_bind_iff {ValB₁ : Type uV''}
    {S : OutcomeSet Fault₁ Gap Val₁}
    {k : Val₁ → OutcomeSet Fault₁ Gap ValB₁} :
    OutcomeSet.Defined isUB₁ (OutcomeSet.bind S k) ↔
      OutcomeSet.Defined isUB₁ S ∧
        ∀ v, S (.ok v) → OutcomeSet.Defined isUB₁ (k v) := by
  constructor
  · intro h
    refine ⟨fun m hm => ?_, fun v hv o ho => h ⟨.ok v, hv, ho⟩⟩
    cases m with
    | ok v => trivial
    | fault e => exact h ⟨.fault e, hm, rfl⟩
    | gap g => exact h ⟨.gap g, hm, rfl⟩
  · rintro ⟨hS, hk⟩ o ⟨m, hm, ho⟩
    cases m with
    | ok v => exact hk v hm ho
    | fault e => cases ho; exact hS hm
    | gap g => exact False.elim (hS hm)

/--
Project a gap-aware behavior set into Layer 1A's Smyth `Partial` domain: the
projection is defined exactly when the set has no gaps and no UB faults.
-/
def OutcomeSet.toPartial (isUB : Fault₁ → Prop) (S : OutcomeSet Fault₁ Gap Val₁) :
    Partial (OutcomeSet Fault₁ Gap Val₁) where
  defined := OutcomeSet.Defined isUB S
  val _ := S

/-- Layer 1A `Semantics` of a program family with gap-aware semantics `sem`. -/
def gapSemantics {Prog : Type uP} (isUB : Fault₁ → Prop)
    (sem : Prog → GapSem Query Fault₁ Gap Val₁) :
    Semantics Prog (Query → Partial (OutcomeSet Fault₁ Gap Val₁)) :=
  fun p q => OutcomeSet.toPartial isUB (sem p q)

/--
Observation map between gap-aware behaviors: the relational image of each
defined behavior set along `GapEqErr rVal rFault`.
-/
def gapObsMap (rVal : Val₁ → Val₂ → Prop) (rFault : Fault₁ → Fault₂ → Prop) :
    (Query → Partial (OutcomeSet Fault₁ Gap Val₁)) →
      Query → Partial (OutcomeSet Fault₂ Gap Val₂) :=
  fun b q => Partial.map (BehaviorSet.relImage (GapEqErr rVal rFault)) (b q)

theorem gapObsMap_monotone :
    Monotone (gapObsMap (Query := Query) (Gap := Gap) rVal rFault) :=
  fun _ _ h q => Partial.map_monotone (BehaviorSet.relImage_monotone _) (h q)

/-- Guard specification: the behavior is defined on every query. -/
def definedSpec (Query : Type uQ) (B : Type uV) [LE B] :
    Spec (Query → Partial B) where
  holds b := ∀ q, (b q).defined
  downward_closed _ _ h_ref h q := (h_ref q (h q)).1

/--
Equivalent behavior sets are defined together when `rFault` preserves UB-ness:
the refactored program inherits gap-freedom *and* UB-freedom of the baseline.
-/
theorem OutcomeSetEquiv.defined_iff
    {S₁ : OutcomeSet Fault₁ Gap Val₁} {S₂ : OutcomeSet Fault₂ Gap Val₂}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → (isUB₁ e₁ ↔ isUB₂ e₂))
    (h : OutcomeSetEquiv (GapEqErr rVal rFault) S₁ S₂) :
    OutcomeSet.Defined isUB₁ S₁ ↔ OutcomeSet.Defined isUB₂ S₂ := by
  refine ⟨fun h₁ _ ho₂ => ?_, fun h₂ _ ho₁ => ?_⟩
  · obtain ⟨_, ho₁, hr⟩ := h.backward ho₂; exact (hr.isDefined_iff hUB).mp (h₁ ho₁)
  · obtain ⟨_, ho₂, hr⟩ := h.forward ho₁; exact (hr.isDefined_iff hUB).mpr (h₂ ho₂)

/--
Smyth refinement induced by a `GapEqErr`-equivalence: whenever the left
behavior set is defined, so is the right one, and every right behavior is the
image of a left behavior. Only reflection of UB (`isUB₂ e₂ → isUB₁ e₁`) is
needed for this direction.
-/
theorem OutcomeSetEquiv.toPartial_le
    {S₁ : OutcomeSet Fault₁ Gap Val₁} {S₂ : OutcomeSet Fault₂ Gap Val₂}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → isUB₂ e₂ → isUB₁ e₁)
    (h : OutcomeSetEquiv (GapEqErr rVal rFault) S₁ S₂) :
    OutcomeSet.toPartial isUB₂ S₂ ≤
      Partial.map (BehaviorSet.relImage (GapEqErr rVal rFault))
        (OutcomeSet.toPartial isUB₁ S₁) := by
  intro h₁
  refine ⟨fun o₂ ho₂ => ?_, fun o₂ ho₂ => h.backward ho₂⟩
  obtain ⟨o₁, ho₁, hr⟩ := h.backward ho₂
  have hd : o₁.isDefined isUB₁ := h₁ ho₁
  cases o₁ with
  | ok v₁ =>
    cases o₂ with
    | ok v₂ => trivial
    | fault e₂ => exact False.elim hr
    | gap g₂ => exact False.elim hr
  | fault e₁ =>
    cases o₂ with
    | ok v₂ => exact False.elim hr
    | fault e₂ => exact fun h₂ => hd (hUB e₁ e₂ hr h₂)
    | gap g₂ => exact False.elim hr
  | gap g₁ => exact False.elim hd

theorem ContextEquivOn.defined_iff {pre : Query → Prop}
    {sem₁ : GapSem Query Fault₁ Gap Val₁} {sem₂ : GapSem Query Fault₂ Gap Val₂}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → (isUB₁ e₁ ↔ isUB₂ e₂))
    (h : ContextEquivOn pre rVal rFault sem₁ sem₂) {q : Query} (hq : pre q) :
    OutcomeSet.Defined isUB₁ (sem₁ q) ↔ OutcomeSet.Defined isUB₂ (sem₂ q) :=
  (h q hq).defined_iff hUB

/--
Headline upgrade: when the baseline is gap-free and UB-free on `pre`, a
`ContextEquivOn pre` whose fault relation preserves UB-ness is a gap-free
`ProgramEquivOn pre`, and the refactored program is gap-free and UB-free on
`pre` as well.
-/
theorem ContextEquivOn.toProgramEquivOn_of_defined {pre : Query → Prop}
    {sem₁ : GapSem Query Fault₁ Gap Val₁} {sem₂ : GapSem Query Fault₂ Gap Val₂}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → (isUB₁ e₁ ↔ isUB₂ e₂))
    (h : ContextEquivOn pre rVal rFault sem₁ sem₂)
    (h₁ : ∀ q, pre q → OutcomeSet.Defined isUB₁ (sem₁ q)) :
    ProgramEquivOn pre rVal rFault sem₁ sem₂ ∧
      ∀ q, pre q → OutcomeSet.Defined isUB₂ (sem₂ q) :=
  ⟨h.toProgramEquivOn (fun q hq => (OutcomeSet.defined_iff.mp (h₁ q hq)).1),
   fun q hq => (h.defined_iff hUB hq).mp (h₁ q hq)⟩

/--
A `ContextEquiv` whose fault relation preserves UB-ness induces an `ExactPass`
between the Layer 1A projections of the two programs, with no gap-freedom
obligation on either program.
-/
theorem ContextEquiv.toExactPass {Prog₁ : Type uP} {Prog₂ : Type uP'}
    {sem₁ : Prog₁ → GapSem Query Fault₁ Gap Val₁}
    {sem₂ : Prog₂ → GapSem Query Fault₂ Gap Val₂}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → (isUB₁ e₁ ↔ isUB₂ e₂))
    {p₁ : Prog₁} {p₂ : Prog₂}
    (h : ContextEquiv rVal rFault (sem₁ p₁) (sem₂ p₂)) :
    ExactPass (gapSemantics isUB₁ sem₁) (gapSemantics isUB₂ sem₂)
      (gapObsMap rVal rFault)
      (gapObsMap (fun v₂ v₁ => rVal v₁ v₂) (fun e₂ e₁ => rFault e₁ e₂))
      p₁ p₂ where
  up_refines _ q :=
    (h.flip q).toPartial_le (fun e₂ e₁ hr hu => (hUB e₁ e₂ hr).mp hu)
  down_refines _ q :=
    (h q).toPartial_le (fun e₁ e₂ hr hu => (hUB e₁ e₂ hr).mpr hu)

/-- Query-scoped `ExactPass` over the query subtype `{q // pre q}`. -/
theorem ContextEquivOn.toExactPass {Prog₁ : Type uP} {Prog₂ : Type uP'}
    {pre : Query → Prop}
    {sem₁ : Prog₁ → GapSem Query Fault₁ Gap Val₁}
    {sem₂ : Prog₂ → GapSem Query Fault₂ Gap Val₂}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → (isUB₁ e₁ ↔ isUB₂ e₂))
    {p₁ : Prog₁} {p₂ : Prog₂}
    (h : ContextEquivOn pre rVal rFault (sem₁ p₁) (sem₂ p₂)) :
    ExactPass (gapSemantics isUB₁ (fun p => (sem₁ p).restrict pre))
      (gapSemantics isUB₂ (fun p => (sem₂ p).restrict pre))
      (gapObsMap rVal rFault)
      (gapObsMap (fun v₂ v₁ => rVal v₁ v₂) (fun e₂ e₁ => rFault e₁ e₂))
      p₁ p₂ :=
  ContextEquiv.toExactPass (sem₁ := fun p => (sem₁ p).restrict pre)
    (sem₂ := fun p => (sem₂ p).restrict pre) hUB
    (contextEquivOn_iff_restrict.mp h)

/-- `CompilerPass` induced by `ContextEquiv` under any guard `G₁`. -/
theorem ContextEquiv.toCompilerPass {Prog₁ : Type uP} {Prog₂ : Type uP'}
    {sem₁ : Prog₁ → GapSem Query Fault₁ Gap Val₁}
    {sem₂ : Prog₂ → GapSem Query Fault₂ Gap Val₂}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → (isUB₁ e₁ ↔ isUB₂ e₂))
    {p₁ : Prog₁} {p₂ : Prog₂}
    (h : ContextEquiv rVal rFault (sem₁ p₁) (sem₂ p₂))
    (G₁ : Spec (Query → Partial (OutcomeSet Fault₁ Gap Val₁))) :
    CompilerPass (gapSemantics isUB₁ sem₁) (gapSemantics isUB₂ sem₂) G₁
      (gapObsMap rVal rFault) p₁ p₂ :=
  (h.toExactPass hUB).toCompilerPass G₁

/-- `VerifierPass` induced by `ContextEquiv` under any guard `G₂`. -/
theorem ContextEquiv.toVerifierPass {Prog₁ : Type uP} {Prog₂ : Type uP'}
    {sem₁ : Prog₁ → GapSem Query Fault₁ Gap Val₁}
    {sem₂ : Prog₂ → GapSem Query Fault₂ Gap Val₂}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → (isUB₁ e₁ ↔ isUB₂ e₂))
    {p₁ : Prog₁} {p₂ : Prog₂}
    (h : ContextEquiv rVal rFault (sem₁ p₁) (sem₂ p₂))
    (G₂ : Spec (Query → Partial (OutcomeSet Fault₂ Gap Val₂))) :
    VerifierPass (gapSemantics isUB₁ sem₁) (gapSemantics isUB₂ sem₂) G₂
      (gapObsMap (fun v₂ v₁ => rVal v₁ v₂) (fun e₂ e₁ => rFault e₁ e₂))
      p₁ p₂ :=
  (h.toExactPass hUB).toVerifierPass G₂

/--
Definedness reflection through the induced `VerifierPass`: definedness of the
refactored program on every query yields definedness of the baseline.
-/
theorem ContextEquiv.defined_left {Prog₁ : Type uP} {Prog₂ : Type uP'}
    {sem₁ : Prog₁ → GapSem Query Fault₁ Gap Val₁}
    {sem₂ : Prog₂ → GapSem Query Fault₂ Gap Val₂}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → (isUB₁ e₁ ↔ isUB₂ e₂))
    {p₁ : Prog₁} {p₂ : Prog₂}
    (h : ContextEquiv rVal rFault (sem₁ p₁) (sem₂ p₂))
    (h₂ : (definedSpec Query _).holds (gapSemantics isUB₂ sem₂ p₂)) :
    (definedSpec Query _).holds (gapSemantics isUB₁ sem₁ p₁) :=
  VerifierPass.reflect_guard (G₁ := definedSpec Query _)
    (h.toVerifierPass hUB (definedSpec Query _)) (fun hg q => hg q) h₂

/--
Definedness preservation: definedness of the baseline on every query yields
definedness of the refactored program.
-/
theorem ContextEquiv.defined_right {Prog₁ : Type uP} {Prog₂ : Type uP'}
    {sem₁ : Prog₁ → GapSem Query Fault₁ Gap Val₁}
    {sem₂ : Prog₂ → GapSem Query Fault₂ Gap Val₂}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → (isUB₁ e₁ ↔ isUB₂ e₂))
    {p₁ : Prog₁} {p₂ : Prog₂}
    (h : ContextEquiv rVal rFault (sem₁ p₁) (sem₂ p₂))
    (h₁ : (definedSpec Query _).holds (gapSemantics isUB₁ sem₁ p₁)) :
    (definedSpec Query _).holds (gapSemantics isUB₂ sem₂ p₂) :=
  fun q => ((h q).defined_iff hUB).mp (h₁ q)

/-- Every gap-free `ProgramEquiv` induces the same `ExactPass`. -/
theorem ProgramEquiv.toExactPass {Prog₁ : Type uP} {Prog₂ : Type uP'}
    {sem₁ : Prog₁ → GapSem Query Fault₁ Gap Val₁}
    {sem₂ : Prog₂ → GapSem Query Fault₂ Gap Val₂}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → (isUB₁ e₁ ↔ isUB₂ e₂))
    {p₁ : Prog₁} {p₂ : Prog₂}
    (h : ProgramEquiv rVal rFault (sem₁ p₁) (sem₂ p₂)) :
    ExactPass (gapSemantics isUB₁ sem₁) (gapSemantics isUB₂ sem₂)
      (gapObsMap rVal rFault)
      (gapObsMap (fun v₂ v₁ => rVal v₁ v₂) (fun e₂ e₁ => rFault e₁ e₂))
      p₁ p₂ :=
  h.toContextEquiv.toExactPass hUB

/-- Query-scoped `CompilerPass` over `{q // pre q}`. -/
theorem ContextEquivOn.toCompilerPass {Prog₁ : Type uP} {Prog₂ : Type uP'}
    {pre : Query → Prop}
    {sem₁ : Prog₁ → GapSem Query Fault₁ Gap Val₁}
    {sem₂ : Prog₂ → GapSem Query Fault₂ Gap Val₂}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → (isUB₁ e₁ ↔ isUB₂ e₂))
    {p₁ : Prog₁} {p₂ : Prog₂}
    (h : ContextEquivOn pre rVal rFault (sem₁ p₁) (sem₂ p₂))
    (G₁ : Spec ({ q : Query // pre q } → Partial (OutcomeSet Fault₁ Gap Val₁))) :
    CompilerPass (gapSemantics isUB₁ (fun p => (sem₁ p).restrict pre))
      (gapSemantics isUB₂ (fun p => (sem₂ p).restrict pre)) G₁
      (gapObsMap rVal rFault) p₁ p₂ :=
  (h.toExactPass hUB).toCompilerPass G₁

/-- Query-scoped `VerifierPass` over `{q // pre q}`. -/
theorem ContextEquivOn.toVerifierPass {Prog₁ : Type uP} {Prog₂ : Type uP'}
    {pre : Query → Prop}
    {sem₁ : Prog₁ → GapSem Query Fault₁ Gap Val₁}
    {sem₂ : Prog₂ → GapSem Query Fault₂ Gap Val₂}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → (isUB₁ e₁ ↔ isUB₂ e₂))
    {p₁ : Prog₁} {p₂ : Prog₂}
    (h : ContextEquivOn pre rVal rFault (sem₁ p₁) (sem₂ p₂))
    (G₂ : Spec ({ q : Query // pre q } → Partial (OutcomeSet Fault₂ Gap Val₂))) :
    VerifierPass (gapSemantics isUB₁ (fun p => (sem₁ p).restrict pre))
      (gapSemantics isUB₂ (fun p => (sem₂ p).restrict pre)) G₂
      (gapObsMap (fun v₂ v₁ => rVal v₁ v₂) (fun e₂ e₁ => rFault e₁ e₂))
      p₁ p₂ :=
  (h.toExactPass hUB).toVerifierPass G₂

/--
Cross-gap-alphabet observation map for gap-free `ProgramEquiv`: relational
image along `GapForbidEq rVal rFault`, requiring no shared gap type.
-/
def gapForbidObsMap {Gap₁ : Type uG} {Gap₂ : Type uG'}
    (rVal : Val₁ → Val₂ → Prop) (rFault : Fault₁ → Fault₂ → Prop) :
    (Query → Partial (OutcomeSet Fault₁ Gap₁ Val₁)) →
      Query → Partial (OutcomeSet Fault₂ Gap₂ Val₂) :=
  fun b q => Partial.map (BehaviorSet.relImage (GapForbidEq rVal rFault)) (b q)

theorem gapForbidObsMap_monotone {Gap₁ : Type uG} {Gap₂ : Type uG'} :
    Monotone (gapForbidObsMap (Query := Query) (Gap₁ := Gap₁) (Gap₂ := Gap₂)
      rVal rFault) :=
  fun _ _ h q => Partial.map_monotone (BehaviorSet.relImage_monotone _) (h q)

theorem OutcomeSetEquiv.forbid_toPartial_le {Gap₁ : Type uG} {Gap₂ : Type uG'}
    {S₁ : OutcomeSet Fault₁ Gap₁ Val₁} {S₂ : OutcomeSet Fault₂ Gap₂ Val₂}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → isUB₂ e₂ → isUB₁ e₁)
    (h : OutcomeSetEquiv (GapForbidEq rVal rFault) S₁ S₂) :
    OutcomeSet.toPartial isUB₂ S₂ ≤
      Partial.map (BehaviorSet.relImage (GapForbidEq rVal rFault))
        (OutcomeSet.toPartial isUB₁ S₁) := by
  intro h₁
  refine ⟨fun o₂ ho₂ => ?_, fun o₂ ho₂ => h.backward ho₂⟩
  obtain ⟨o₁, ho₁, hr⟩ := h.backward ho₂
  have hd : o₁.isDefined isUB₁ := h₁ ho₁
  cases o₁ with
  | ok v₁ =>
    cases o₂ with
    | ok v₂ => trivial
    | fault e₂ => exact False.elim hr
    | gap g₂ => exact False.elim hr
  | fault e₁ =>
    cases o₂ with
    | ok v₂ => exact False.elim hr
    | fault e₂ => exact fun h₂ => hd (hUB e₁ e₂ hr h₂)
    | gap g₂ => exact False.elim hr
  | gap g₁ => exact False.elim hd

/--
Gap-free `ProgramEquiv` induces an `ExactPass` even across distinct gap
alphabets `Gap₁` and `Gap₂`.
-/
theorem ProgramEquiv.toExactPass_crossGap {Prog₁ : Type uP} {Prog₂ : Type uP'}
    {Gap₁ : Type uG} {Gap₂ : Type uG'}
    {sem₁ : Prog₁ → GapSem Query Fault₁ Gap₁ Val₁}
    {sem₂ : Prog₂ → GapSem Query Fault₂ Gap₂ Val₂}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → (isUB₁ e₁ ↔ isUB₂ e₂))
    {p₁ : Prog₁} {p₂ : Prog₂}
    (h : ProgramEquiv rVal rFault (sem₁ p₁) (sem₂ p₂)) :
    ExactPass (gapSemantics isUB₁ sem₁) (gapSemantics isUB₂ sem₂)
      (gapForbidObsMap rVal rFault)
      (gapForbidObsMap (fun v₂ v₁ => rVal v₁ v₂) (fun e₂ e₁ => rFault e₁ e₂))
      p₁ p₂ where
  up_refines _ q :=
    (h.flip q).forbid_toPartial_le (fun e₂ e₁ hr hu => (hUB e₁ e₂ hr).mp hu)
  down_refines _ q :=
    (h q).forbid_toPartial_le (fun e₁ e₂ hr hu => (hUB e₁ e₂ hr).mpr hu)

theorem ProgramEquiv.toCompilerPass {Prog₁ : Type uP} {Prog₂ : Type uP'}
    {Gap₁ : Type uG} {Gap₂ : Type uG'}
    {sem₁ : Prog₁ → GapSem Query Fault₁ Gap₁ Val₁}
    {sem₂ : Prog₂ → GapSem Query Fault₂ Gap₂ Val₂}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → (isUB₁ e₁ ↔ isUB₂ e₂))
    {p₁ : Prog₁} {p₂ : Prog₂}
    (h : ProgramEquiv rVal rFault (sem₁ p₁) (sem₂ p₂))
    (G₁ : Spec (Query → Partial (OutcomeSet Fault₁ Gap₁ Val₁))) :
    CompilerPass (gapSemantics isUB₁ sem₁) (gapSemantics isUB₂ sem₂) G₁
      (gapForbidObsMap rVal rFault) p₁ p₂ :=
  (h.toExactPass_crossGap hUB).toCompilerPass G₁

theorem ProgramEquiv.toVerifierPass {Prog₁ : Type uP} {Prog₂ : Type uP'}
    {Gap₁ : Type uG} {Gap₂ : Type uG'}
    {sem₁ : Prog₁ → GapSem Query Fault₁ Gap₁ Val₁}
    {sem₂ : Prog₂ → GapSem Query Fault₂ Gap₂ Val₂}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → (isUB₁ e₁ ↔ isUB₂ e₂))
    {p₁ : Prog₁} {p₂ : Prog₂}
    (h : ProgramEquiv rVal rFault (sem₁ p₁) (sem₂ p₂))
    (G₂ : Spec (Query → Partial (OutcomeSet Fault₂ Gap₂ Val₂))) :
    VerifierPass (gapSemantics isUB₁ sem₁) (gapSemantics isUB₂ sem₂) G₂
      (gapForbidObsMap (fun v₂ v₁ => rVal v₁ v₂) (fun e₂ e₁ => rFault e₁ e₂))
      p₁ p₂ :=
  (h.toExactPass_crossGap hUB).toVerifierPass G₂

end LayerOneABridges

/-! ### Fault-Free / Gap-Free Value Projection (`Partial (BehaviorSet Val)`)

Projecting an `OutcomeSet Fault Gap Val` directly into `Partial (BehaviorSet Val)`
erases both `Fault` and `Gap` from the Layer 1A observation domain: the
projection is defined precisely when every reachable behavior is a normal value
(`NeverGap ∧ NoFault`). Both `ContextEquiv` and cross-gap `ProgramEquiv` induce
`ExactPass`, `CompilerPass`, and `VerifierPass` on this value domain without any
side condition on `rFault`, because neither `GapEqErr` nor `GapForbidEq` ever
relates `.ok` to `.fault` or `.gap`.
-/

section ValueProjectionBridges

variable {Query : Type uQ} {Fault₁ : Type uF} {Fault₂ : Type uF'}
  {Gap₁ : Type uG} {Gap₂ : Type uG'} {Val₁ : Type uV} {Val₂ : Type uV'}
  {rVal : Val₁ → Val₂ → Prop} {rFault : Fault₁ → Fault₂ → Prop}

/-- No behavior in `S` is a runtime fault. -/
def OutcomeSet.NoFault (S : OutcomeSet Fault₁ Gap₁ Val₁) : Prop :=
  ∀ ⦃e⦄, ¬ S (.fault e)

/-- Every behavior in `S` is a normal `.ok` value (gap-free and fault-free). -/
def OutcomeSet.OnlyValues (S : OutcomeSet Fault₁ Gap₁ Val₁) : Prop :=
  ∀ ⦃o⦄, S o → ∃ v, o = .ok v

theorem OutcomeSet.onlyValues_iff {S : OutcomeSet Fault₁ Gap₁ Val₁} :
    OutcomeSet.OnlyValues S ↔ NeverGap S ∧ OutcomeSet.NoFault S := by
  constructor
  · intro h
    refine ⟨fun o ho => ?_, fun e he => ?_⟩
    · obtain ⟨v, rfl⟩ := h ho; trivial
    · obtain ⟨v, hv⟩ := h he; cases hv
  · rintro ⟨hg, hf⟩ o ho
    cases o with
    | ok v => exact ⟨v, rfl⟩
    | fault e => exact False.elim (hf ho)
    | gap g => exact False.elim (hg ho)

/--
Fault-free, gap-free projection of `OutcomeSet Fault Gap Val` into Layer 1A's
`Partial (BehaviorSet Val)`.
-/
def OutcomeSet.toValPartial (S : OutcomeSet Fault₁ Gap₁ Val₁) :
    Partial (BehaviorSet Val₁) where
  defined := OutcomeSet.OnlyValues S
  val _ v := S (.ok v)

/-- Layer 1A value-domain `Semantics` erasing both faults and gaps. -/
def valSemantics {Prog : Type uP}
    (sem : Prog → GapSem Query Fault₁ Gap₁ Val₁) :
    Semantics Prog (Query → Partial (BehaviorSet Val₁)) :=
  fun p q => OutcomeSet.toValPartial (sem p q)

/-- Observation map between value-domain behaviors via `BehaviorSet.relImage rVal`. -/
def valObsMap (rVal : Val₁ → Val₂ → Prop) :
    (Query → Partial (BehaviorSet Val₁)) → Query → Partial (BehaviorSet Val₂) :=
  fun b q => Partial.map (BehaviorSet.relImage rVal) (b q)

theorem valObsMap_monotone :
    Monotone (valObsMap (Query := Query) rVal) :=
  fun _ _ h q => Partial.map_monotone (BehaviorSet.relImage_monotone rVal) (h q)

/-- Layer 1A value-domain `Language` erasing both `Fault` and `Gap`. -/
def valLanguage {Prog Query Fault Gap Val : Type}
    (sem : Prog → GapSem Query Fault Gap Val) : Language where
  Prog := Prog
  Query := Query
  Out := Val
  sem p q := OutcomeSet.toValPartial (sem p q)

theorem OutcomeSetEquiv.onlyValues_iff {Gap : Type uG}
    {S₁ : OutcomeSet Fault₁ Gap Val₁} {S₂ : OutcomeSet Fault₂ Gap Val₂}
    (h : OutcomeSetEquiv (GapEqErr rVal rFault) S₁ S₂) :
    OutcomeSet.OnlyValues S₁ ↔ OutcomeSet.OnlyValues S₂ := by
  constructor
  · intro h₁ o₂ ho₂
    obtain ⟨o₁, ho₁, hr⟩ := h.backward ho₂
    obtain ⟨v₁, rfl⟩ := h₁ ho₁
    cases o₂ with
    | ok v₂ => exact ⟨v₂, rfl⟩
    | fault _ => exact False.elim hr
    | gap _ => exact False.elim hr
  · intro h₂ o₁ ho₁
    obtain ⟨o₂, ho₂, hr⟩ := h.forward ho₁
    obtain ⟨v₂, rfl⟩ := h₂ ho₂
    cases o₁ with
    | ok v₁ => exact ⟨v₁, rfl⟩
    | fault _ => exact False.elim hr
    | gap _ => exact False.elim hr

theorem OutcomeSetEquiv.toValPartial_le {Gap : Type uG}
    {S₁ : OutcomeSet Fault₁ Gap Val₁} {S₂ : OutcomeSet Fault₂ Gap Val₂}
    (h : OutcomeSetEquiv (GapEqErr rVal rFault) S₁ S₂) :
    OutcomeSet.toValPartial S₂ ≤
      Partial.map (BehaviorSet.relImage rVal) (OutcomeSet.toValPartial S₁) := by
  intro h₁
  refine ⟨h.onlyValues_iff.mp h₁, fun v₂ hv₂ => ?_⟩
  obtain ⟨o₁, ho₁, hr⟩ := h.backward hv₂
  obtain ⟨v₁, rfl⟩ := h₁ ho₁
  exact ⟨v₁, ho₁, hr⟩

theorem OutcomeSetEquiv.forbid_toValPartial_le
    {S₁ : OutcomeSet Fault₁ Gap₁ Val₁} {S₂ : OutcomeSet Fault₂ Gap₂ Val₂}
    (h : OutcomeSetEquiv (GapForbidEq rVal rFault) S₁ S₂) :
    OutcomeSet.toValPartial S₂ ≤
      Partial.map (BehaviorSet.relImage rVal) (OutcomeSet.toValPartial S₁) := by
  intro h₁
  refine ⟨fun o₂ ho₂ => ?_, fun v₂ hv₂ => ?_⟩
  · obtain ⟨o₁, ho₁, hr⟩ := h.backward ho₂
    obtain ⟨v₁, rfl⟩ := h₁ ho₁
    cases o₂ with
    | ok v₂ => exact ⟨v₂, rfl⟩
    | fault _ => exact False.elim hr
    | gap _ => exact False.elim hr
  · obtain ⟨o₁, ho₁, hr⟩ := h.backward hv₂
    obtain ⟨v₁, rfl⟩ := h₁ ho₁
    exact ⟨v₁, ho₁, hr⟩

/-- `ContextEquiv` induces a gap- and fault-erased `ExactPass` on `valSemantics`. -/
theorem ContextEquiv.toValExactPass {Prog₁ : Type uP} {Prog₂ : Type uP'}
    {Gap : Type uG}
    {sem₁ : Prog₁ → GapSem Query Fault₁ Gap Val₁}
    {sem₂ : Prog₂ → GapSem Query Fault₂ Gap Val₂}
    {p₁ : Prog₁} {p₂ : Prog₂}
    (h : ContextEquiv rVal rFault (sem₁ p₁) (sem₂ p₂)) :
    ExactPass (valSemantics sem₁) (valSemantics sem₂)
      (valObsMap rVal) (valObsMap (fun v₂ v₁ => rVal v₁ v₂)) p₁ p₂ where
  up_refines _ q := (h.flip q).toValPartial_le
  down_refines _ q := (h q).toValPartial_le

/--
Gap-free `ProgramEquiv` induces a gap- and fault-erased `ExactPass` on
`valSemantics` across arbitrary `Fault₁`, `Fault₂`, `Gap₁`, and `Gap₂`.
-/
theorem ProgramEquiv.toValExactPass {Prog₁ : Type uP} {Prog₂ : Type uP'}
    {sem₁ : Prog₁ → GapSem Query Fault₁ Gap₁ Val₁}
    {sem₂ : Prog₂ → GapSem Query Fault₂ Gap₂ Val₂}
    {p₁ : Prog₁} {p₂ : Prog₂}
    (h : ProgramEquiv rVal rFault (sem₁ p₁) (sem₂ p₂)) :
    ExactPass (valSemantics sem₁) (valSemantics sem₂)
      (valObsMap rVal) (valObsMap (fun v₂ v₁ => rVal v₁ v₂)) p₁ p₂ where
  up_refines _ q := (h.flip q).forbid_toValPartial_le
  down_refines _ q := (h q).forbid_toValPartial_le

private theorem forbid_toValPartial_le_eq {Val : Type uV}
    {S₁ : OutcomeSet Fault₁ Gap₁ Val} {S₂ : OutcomeSet Fault₂ Gap₂ Val}
    (h : OutcomeSetEquiv (GapForbidEq (· = ·) rFault) S₁ S₂) :
    OutcomeSet.toValPartial S₂ ≤ OutcomeSet.toValPartial S₁ := by
  intro h₁
  obtain ⟨h₂, hle⟩ := h.forbid_toValPartial_le h₁
  exact ⟨h₂, fun v₂ hv₂ => by obtain ⟨_, hv₁, heq⟩ := hle v₂ hv₂; exact heq ▸ hv₁⟩

private theorem toValPartial_le_eq {Gap : Type uG} {Val : Type uV}
    {S₁ : OutcomeSet Fault₁ Gap Val} {S₂ : OutcomeSet Fault₂ Gap Val}
    (h : OutcomeSetEquiv (GapEqErr (· = ·) rFault) S₁ S₂) :
    OutcomeSet.toValPartial S₂ ≤ OutcomeSet.toValPartial S₁ := by
  intro h₁
  obtain ⟨h₂, hle⟩ := h.toValPartial_le h₁
  exact ⟨h₂, fun v₂ hv₂ => by obtain ⟨_, hv₁, heq⟩ := hle v₂ hv₂; exact heq ▸ hv₁⟩

/--
Exact-value `ProgramEquiv` across arbitrary `Fault₁`, `Fault₂`, `Gap₁`, `Gap₂`
induces an identity-observation `ExactPass` on `valSemantics`.
-/
theorem ProgramEquiv.toValExactPass_eq {Prog₁ : Type uP} {Prog₂ : Type uP'}
    {Val : Type uV}
    {sem₁ : Prog₁ → GapSem Query Fault₁ Gap₁ Val}
    {sem₂ : Prog₂ → GapSem Query Fault₂ Gap₂ Val}
    {p₁ : Prog₁} {p₂ : Prog₂}
    (h : ProgramEquiv (· = ·) rFault (sem₁ p₁) (sem₂ p₂)) :
    ExactPass (valSemantics sem₁) (valSemantics sem₂) id id p₁ p₂ where
  up_refines _ q := forbid_toValPartial_le_eq ((h.flip q).mono (fun _ _ hr =>
    GapForbidEq.mono (fun _ _ hv => Eq.symm hv) (fun _ _ he => he) hr))
  down_refines _ q := forbid_toValPartial_le_eq (h q)

/--
`OutcomeSet.bind S k` admits only normal values iff `S` admits only normal
values and every continuation `k v` for `S (.ok v)` admits only normal values.
-/
theorem OutcomeSet.onlyValues_bind_iff {ValB₁ : Type uV''}
    {S : OutcomeSet Fault₁ Gap₁ Val₁}
    {k : Val₁ → OutcomeSet Fault₁ Gap₁ ValB₁} :
    OutcomeSet.OnlyValues (OutcomeSet.bind S k) ↔
      OutcomeSet.OnlyValues S ∧
        ∀ v, S (.ok v) → OutcomeSet.OnlyValues (k v) := by
  constructor
  · intro h
    refine ⟨fun m hm => ?_, fun v hv o ho => h ⟨.ok v, hv, ho⟩⟩
    cases m with
    | ok v => exact ⟨v, rfl⟩
    | fault e =>
      obtain ⟨w, hw⟩ := h ⟨.fault e, hm, rfl⟩
      cases hw
    | gap g =>
      obtain ⟨w, hw⟩ := h ⟨.gap g, hm, rfl⟩
      cases hw
  · rintro ⟨hS, hk⟩ o ⟨m, hm, ho⟩
    obtain ⟨v, rfl⟩ := hS hm
    exact hk v hm ho

/--
Exact-value `ContextEquiv` across arbitrary `Fault₁`, `Fault₂` and arbitrary
`rFault` induces an identity-observation `ExactPass` on `valSemantics`, WITHOUT
requiring global gap-freedom (`ProgramEquiv`): on queries where either side hits
a gap or fault, both `valSemantics` projections are `Partial.ub` (`⊤`), while on
queries where one side returns only values, `ContextEquiv` forces the other side
to be gap-free, fault-free, and value-identical.
-/
theorem ContextEquiv.toValExactPass_eq {Prog₁ : Type uP} {Prog₂ : Type uP'}
    {Gap : Type uG} {Val : Type uV}
    {sem₁ : Prog₁ → GapSem Query Fault₁ Gap Val}
    {sem₂ : Prog₂ → GapSem Query Fault₂ Gap Val}
    {p₁ : Prog₁} {p₂ : Prog₂}
    (h : ContextEquiv (· = ·) rFault (sem₁ p₁) (sem₂ p₂)) :
    ExactPass (valSemantics sem₁) (valSemantics sem₂) id id p₁ p₂ where
  up_refines _ q := toValPartial_le_eq ((h.flip q).mono (fun _ _ hr =>
    GapEqErr.mono (fun _ _ hv => Eq.symm hv) (fun _ _ he => he) hr))
  down_refines _ q := toValPartial_le_eq (h q)

/-- Layer 1A `Compiles` on `valLanguage` induced by exact-value `ContextEquiv`. -/
theorem ContextEquiv.valCompiles_eq
    {Prog₁ Prog₂ Query Fault₁ Fault₂ Gap Val : Type}
    {rFault : Fault₁ → Fault₂ → Prop}
    {sem₁ : Prog₁ → GapSem Query Fault₁ Gap Val}
    {sem₂ : Prog₂ → GapSem Query Fault₂ Gap Val}
    {p₁ : Prog₁} {p₂ : Prog₂}
    (h : ContextEquiv (· = ·) rFault (sem₁ p₁) (sem₂ p₂)) :
    Compiles (valLanguage sem₁) (valLanguage sem₂) id p₁ p₂ :=
  (h.toValExactPass_eq).down_refines trivial

/--
Relational query-scoped specification transfer across `valLanguage`: supports
custom value relations `rVal` (such as `fun r₁ r₂ : MirReturn => r₁.1 = r₂.1`
across distinct post-return borrow histories) and distinct value/fault/program
types whenever `spec₂` is covered by `pre` and respects `BehaviorSet.relImage rVal`.
-/
theorem ContextEquivOn.valTransfer_spec_rel
    {Prog₁ Prog₂ Query Fault₁ Fault₂ Gap Val₁ Val₂ : Type}
    {pre : Query → Prop} {rVal : Val₁ → Val₂ → Prop} {rFault : Fault₁ → Fault₂ → Prop}
    {sem₁ : Prog₁ → GapSem Query Fault₁ Gap Val₁}
    {sem₂ : Prog₂ → GapSem Query Fault₂ Gap Val₂}
    {p₁ : Prog₁} {p₂ : Prog₂}
    (h : ContextEquivOn pre rVal rFault (sem₁ p₁) (sem₂ p₂))
    {spec₁ : (valLanguage sem₁).Behavior} {spec₂ : (valLanguage sem₂).Behavior}
    (hDef : ∀ q, (spec₂ q).defined → (spec₁ q).defined ∧ pre q)
    (hRel : ∀ q (hd₁ : (spec₁ q).defined) (hd₂ : (spec₂ q).defined),
      pre q → BehaviorSet.relImage rVal ((spec₁ q).val hd₁) ≤ (spec₂ q).val hd₂)
    (h₁ : (valLanguage sem₁).sem p₁ ≤ spec₁) :
    (valLanguage sem₂).sem p₂ ≤ spec₂ := by
  intro q hspec₂
  obtain ⟨hspec₁, hq⟩ := hDef q hspec₂
  obtain ⟨hd₁, hle₁⟩ := h₁ q hspec₁
  obtain ⟨hd₂, hle₂⟩ := (h q hq).toValPartial_le hd₁
  exact ⟨hd₂, fun v₂ hv₂ =>
    hRel q hspec₁ hspec₂ hq v₂ (BehaviorSet.relImage_monotone rVal hle₁ v₂ (hle₂ v₂ hv₂))⟩

/--
Query-scoped specification transfer across `valLanguage`: only `ContextEquivOn pre`
is needed whenever `spec` is defined only on queries satisfying `pre` (so outside
`pre`, `p₁` and `p₂` need NOT even be `ContextEquiv`!).
-/
theorem ContextEquivOn.valTransfer_spec
    {Prog₁ Prog₂ Query Fault₁ Fault₂ Gap Val : Type}
    {pre : Query → Prop} {rFault : Fault₁ → Fault₂ → Prop}
    {sem₁ : Prog₁ → GapSem Query Fault₁ Gap Val}
    {sem₂ : Prog₂ → GapSem Query Fault₂ Gap Val}
    {p₁ : Prog₁} {p₂ : Prog₂}
    (h : ContextEquivOn pre (· = ·) rFault (sem₁ p₁) (sem₂ p₂))
    {spec : (valLanguage sem₁).Behavior}
    (hPre : ∀ q, (spec q).defined → pre q)
    (h₁ : (valLanguage sem₁).sem p₁ ≤ spec) :
    (valLanguage sem₂).sem p₂ ≤ spec :=
  h.valTransfer_spec_rel (fun q hs => ⟨hs, hPre q hs⟩)
    (fun _ _ _ _ _ ⟨_, hv₁, heq⟩ => heq ▸ hv₁) h₁

/--
Transfer any Layer 1A specification (such as `Language.ContractSpec safetyPre
funcPre post` scoped to the gap-free queries `safetyPre`) across `valLanguage`
along an exact-value `ContextEquiv`, even when both programs hit shared gaps
outside `safetyPre`.
-/
theorem ContextEquiv.valTransfer_spec
    {Prog₁ Prog₂ Query Fault₁ Fault₂ Gap Val : Type}
    {rFault : Fault₁ → Fault₂ → Prop}
    {sem₁ : Prog₁ → GapSem Query Fault₁ Gap Val}
    {sem₂ : Prog₂ → GapSem Query Fault₂ Gap Val}
    {p₁ : Prog₁} {p₂ : Prog₂}
    (h : ContextEquiv (· = ·) rFault (sem₁ p₁) (sem₂ p₂))
    {spec : (valLanguage sem₁).Behavior}
    (h₁ : (valLanguage sem₁).sem p₁ ≤ spec) :
    (valLanguage sem₂).sem p₂ ≤ spec :=
  ContextEquivOn.valTransfer_spec (pre := fun _ => True)
    (fun q _ => h q) (fun _ _ => trivial) h₁

/-- At least one outcome is admitted by `S` (non-empty / terminating behavior set). -/
def OutcomeSet.Terminates (S : OutcomeSet Fault₁ Gap₁ Val₁) : Prop :=
  ∃ o, S o

/-- Total definedness: non-empty AND every reachable outcome is gap-free and non-UB. -/
def OutcomeSet.TotalDefined (isUB : Fault₁ → Prop)
    (S : OutcomeSet Fault₁ Gap₁ Val₁) : Prop :=
  S.Terminates ∧ S.Defined isUB

/--
Any `OutcomeSetEquiv` preserves non-emptiness (`Terminates`) in both directions:
a diverging empty behavior set is never equivalent to a terminating, faulting,
or gapping behavior set.
-/
theorem OutcomeSetEquiv.terminates_iff {α : Type uV} {β : Type uV'}
    {R : α → β → Prop} {S₁ : BehaviorSet α} {S₂ : BehaviorSet β}
    (h : OutcomeSetEquiv R S₁ S₂) :
    (∃ a, S₁ a) ↔ (∃ b, S₂ b) := by
  refine ⟨fun ha => ?_, fun hb => ?_⟩
  · obtain ⟨_, ha⟩ := ha; obtain ⟨b, hb, _⟩ := h.forward ha; exact ⟨b, hb⟩
  · obtain ⟨_, hb⟩ := hb; obtain ⟨a, ha, _⟩ := h.backward hb; exact ⟨a, ha⟩

/--
Under a UB-preserving fault relation, `GapEqErr`-equivalence transfers total
definedness (termination + gap-freedom + UB-freedom) in both directions.
-/
theorem OutcomeSetEquiv.totalDefined_iff {Gap : Type uG}
    {isUB₁ : Fault₁ → Prop} {isUB₂ : Fault₂ → Prop}
    {S₁ : OutcomeSet Fault₁ Gap Val₁} {S₂ : OutcomeSet Fault₂ Gap Val₂}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → (isUB₁ e₁ ↔ isUB₂ e₂))
    (h : OutcomeSetEquiv (GapEqErr rVal rFault) S₁ S₂) :
    OutcomeSet.TotalDefined isUB₁ S₁ ↔ OutcomeSet.TotalDefined isUB₂ S₂ :=
  ⟨fun h₁ => ⟨h.terminates_iff.mp h₁.1, (h.defined_iff hUB).mp h₁.2⟩,
   fun h₂ => ⟨h.terminates_iff.mpr h₂.1, (h.defined_iff hUB).mpr h₂.2⟩⟩

/--
Total-correctness upgrade: when the baseline is totally defined on `pre`,
`ContextEquivOn pre` upgrades to gap-free `ProgramEquivOn pre` AND establishes
total definedness (termination + gap-freedom + UB-freedom) of the refactored
program on `pre`.
-/
theorem ContextEquivOn.toProgramEquivOn_of_totalDefined
    {Gap : Type uG} {pre : Query → Prop}
    {isUB₁ : Fault₁ → Prop} {isUB₂ : Fault₂ → Prop}
    {sem₁ : GapSem Query Fault₁ Gap Val₁} {sem₂ : GapSem Query Fault₂ Gap Val₂}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → (isUB₁ e₁ ↔ isUB₂ e₂))
    (h : ContextEquivOn pre rVal rFault sem₁ sem₂)
    (h₁ : ∀ q, pre q → OutcomeSet.TotalDefined isUB₁ (sem₁ q)) :
    ProgramEquivOn pre rVal rFault sem₁ sem₂ ∧
      ∀ q, pre q → OutcomeSet.TotalDefined isUB₂ (sem₂ q) :=
  ⟨h.toProgramEquivOn (fun q hq => (OutcomeSet.defined_iff.mp (h₁ q hq).2).1),
   fun q hq => ((h q hq).totalDefined_iff hUB).mp (h₁ q hq)⟩

end ValueProjectionBridges

section ExactBridges

variable {Fault : Type uF} {Gap : Type uG} {Val : Type uV} {isUB : Fault → Prop}

/-- Under exact matching every behavior of the left set is a right behavior. -/
theorem OutcomeSetEquiv.subset_of_eq {S₁ S₂ : OutcomeSet Fault Gap Val}
    (h : OutcomeSetEquiv (GapEqErr (· = ·) (· = ·)) S₁ S₂) :
    ∀ o, S₁ o → S₂ o := by
  intro _ ho₁
  obtain ⟨_, ho₂, hr⟩ := h.forward ho₁
  exact GapEqErr.eq_iff.mp hr ▸ ho₂

/-- Under exact matching every behavior of the right set is a left behavior. -/
theorem OutcomeSetEquiv.superset_of_eq {S₁ S₂ : OutcomeSet Fault Gap Val}
    (h : OutcomeSetEquiv (GapEqErr (· = ·) (· = ·)) S₁ S₂) :
    ∀ o, S₂ o → S₁ o := by
  intro _ ho₂
  obtain ⟨_, ho₁, hr⟩ := h.backward ho₂
  exact GapEqErr.eq_iff.mp hr ▸ ho₁

theorem OutcomeSet.toPartial_le_of_subset {S₁ S₂ : OutcomeSet Fault Gap Val}
    (h : ∀ o, S₂ o → S₁ o) :
    OutcomeSet.toPartial isUB S₂ ≤ OutcomeSet.toPartial isUB S₁ :=
  fun h₁ => ⟨fun _ ho₂ => h₁ (h _ ho₂), fun o ho₂ => h o ho₂⟩

/--
Exact `ContextEquiv` induces an identity-observation `ExactPass`: the two
programs have the same Layer 1A behavior, defined or not.
-/
theorem ContextEquiv.toExactPass_eq {Query : Type uQ} {Prog : Type uP}
    {sem : Prog → GapSem Query Fault Gap Val} {p₁ p₂ : Prog}
    (h : ContextEquiv (· = ·) (· = ·) (sem p₁) (sem p₂)) :
    ExactPass (gapSemantics isUB sem) (gapSemantics isUB sem) id id p₁ p₂ where
  up_refines _ q := OutcomeSet.toPartial_le_of_subset (h q).subset_of_eq
  down_refines _ q := OutcomeSet.toPartial_le_of_subset (h q).superset_of_eq

/-- Layer 1A `Language` of a program family with gap-aware semantics `sem`. -/
def gapLanguage {Prog Query Fault Gap Val : Type} (isUB : Fault → Prop)
    (sem : Prog → GapSem Query Fault Gap Val) : Language where
  Prog := Prog
  Query := Query
  Out := OutcomeWithGap Fault Gap Val
  sem p q := OutcomeSet.toPartial isUB (sem p q)

/-- Layer 1A `Compiles` induced by `ContextEquiv` on `gapLanguage`. -/
theorem ContextEquiv.compiles {Prog₁ Prog₂ Query Fault₁ Fault₂ Gap Val₁ Val₂ : Type}
    {rVal : Val₁ → Val₂ → Prop} {rFault : Fault₁ → Fault₂ → Prop}
    {isUB₁ : Fault₁ → Prop} {isUB₂ : Fault₂ → Prop}
    {sem₁ : Prog₁ → GapSem Query Fault₁ Gap Val₁}
    {sem₂ : Prog₂ → GapSem Query Fault₂ Gap Val₂}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → (isUB₁ e₁ ↔ isUB₂ e₂))
    {p₁ : Prog₁} {p₂ : Prog₂}
    (h : ContextEquiv rVal rFault (sem₁ p₁) (sem₂ p₂)) :
    Compiles (gapLanguage isUB₁ sem₁) (gapLanguage isUB₂ sem₂)
      (gapObsMap rVal rFault) p₁ p₂ :=
  fun q => (h q).toPartial_le (fun e₁ e₂ hr hu => (hUB e₁ e₂ hr).mpr hu)

/-- Layer 1A `Abstracts` induced by `ContextEquiv` on `gapLanguage`. -/
theorem ContextEquiv.abstracts {Prog₁ Prog₂ Query Fault₁ Fault₂ Gap Val₁ Val₂ : Type}
    {rVal : Val₁ → Val₂ → Prop} {rFault : Fault₁ → Fault₂ → Prop}
    {isUB₁ : Fault₁ → Prop} {isUB₂ : Fault₂ → Prop}
    {sem₁ : Prog₁ → GapSem Query Fault₁ Gap Val₁}
    {sem₂ : Prog₂ → GapSem Query Fault₂ Gap Val₂}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → (isUB₁ e₁ ↔ isUB₂ e₂))
    {p₁ : Prog₁} {p₂ : Prog₂}
    (h : ContextEquiv rVal rFault (sem₁ p₁) (sem₂ p₂)) :
    Abstracts (gapLanguage isUB₂ sem₂) (gapLanguage isUB₁ sem₁)
      (gapObsMap (fun v₂ v₁ => rVal v₁ v₂) (fun e₂ e₁ => rFault e₁ e₂)) p₂ p₁ :=
  fun q => (h.flip q).toPartial_le (fun e₂ e₁ hr hu => (hUB e₁ e₂ hr).mp hu)

/--
Relational query-scoped specification transfer across `gapLanguage`: supports
custom value/fault relations `rVal`, `rFault` (with UB reflection) across distinct
program, value, and fault types.
-/
theorem ContextEquivOn.transfer_spec_rel
    {Prog₁ Prog₂ Query Fault₁ Fault₂ Gap Val₁ Val₂ : Type}
    {pre : Query → Prop} {rVal : Val₁ → Val₂ → Prop} {rFault : Fault₁ → Fault₂ → Prop}
    {isUB₁ : Fault₁ → Prop} {isUB₂ : Fault₂ → Prop}
    {sem₁ : Prog₁ → GapSem Query Fault₁ Gap Val₁}
    {sem₂ : Prog₂ → GapSem Query Fault₂ Gap Val₂}
    {p₁ : Prog₁} {p₂ : Prog₂}
    (hUB : ∀ e₁ e₂, rFault e₁ e₂ → isUB₂ e₂ → isUB₁ e₁)
    (h : ContextEquivOn pre rVal rFault (sem₁ p₁) (sem₂ p₂))
    {spec₁ : (gapLanguage isUB₁ sem₁).Behavior} {spec₂ : (gapLanguage isUB₂ sem₂).Behavior}
    (hDef : ∀ q, (spec₂ q).defined → (spec₁ q).defined ∧ pre q)
    (hRel : ∀ q (hd₁ : (spec₁ q).defined) (hd₂ : (spec₂ q).defined),
      pre q → BehaviorSet.relImage (GapEqErr rVal rFault) ((spec₁ q).val hd₁) ≤ (spec₂ q).val hd₂)
    (h₁ : (gapLanguage isUB₁ sem₁).sem p₁ ≤ spec₁) :
    (gapLanguage isUB₂ sem₂).sem p₂ ≤ spec₂ := by
  intro q hspec₂
  obtain ⟨hspec₁, hq⟩ := hDef q hspec₂
  obtain ⟨hd₁, hle₁⟩ := h₁ q hspec₁
  obtain ⟨hd₂, hle₂⟩ := (h q hq).toPartial_le hUB hd₁
  exact ⟨hd₂, fun o₂ ho₂ =>
    hRel q hspec₁ hspec₂ hq o₂
      (BehaviorSet.relImage_monotone (GapEqErr rVal rFault) hle₁ o₂ (hle₂ o₂ ho₂))⟩

/--
Query-scoped specification transfer across `gapLanguage`: requires `ContextEquivOn pre`
only on queries where `spec` is defined (`(spec q).defined → pre q`).
-/
theorem ContextEquivOn.transfer_spec {Prog Query Fault Gap Val : Type}
    {pre : Query → Prop} {isUB : Fault → Prop}
    {sem : Prog → GapSem Query Fault Gap Val} {p₁ p₂ : Prog}
    (h : ContextEquivOn pre (· = ·) (· = ·) (sem p₁) (sem p₂))
    {spec : (gapLanguage isUB sem).Behavior}
    (hPre : ∀ q, (spec q).defined → pre q)
    (h₁ : (gapLanguage isUB sem).sem p₁ ≤ spec) :
    (gapLanguage isUB sem).sem p₂ ≤ spec :=
  h.transfer_spec_rel (fun _ _ hr hu => hr ▸ hu) (fun q hs => ⟨hs, hPre q hs⟩)
    (fun _ _ _ _ _ ⟨_, ho₁, hr⟩ => GapEqErr.eq_iff.mp hr ▸ ho₁) h₁

/--
Specification transfer: every Layer 1A specification verified for the baseline
(which includes its gap-freedom and UB-freedom wherever the specification is
defined) holds for an exactly `ContextEquiv` refactoring, without re-verifying
shared helpers.
-/
theorem ContextEquiv.transfer_spec {Prog Query Fault Gap Val : Type}
    {isUB : Fault → Prop} {sem : Prog → GapSem Query Fault Gap Val} {p₁ p₂ : Prog}
    (h : ContextEquiv (· = ·) (· = ·) (sem p₁) (sem p₂))
    {spec : (gapLanguage isUB sem).Behavior}
    (h₁ : (gapLanguage isUB sem).sem p₁ ≤ spec) :
    (gapLanguage isUB sem).sem p₂ ≤ spec :=
  ContextEquivOn.transfer_spec (pre := fun _ => True)
    (fun q _ => h q) (fun _ _ => trivial) h₁

end ExactBridges

end GapPreservingEquivalence

end Anneal.Refinement
