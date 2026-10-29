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

end Anneal.Refinement
