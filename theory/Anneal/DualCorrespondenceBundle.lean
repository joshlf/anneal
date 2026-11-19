/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Trusted

/-!
# Dual-authority correspondence bundles

Reusable proof abstraction for Anneal's dual-authority correspondence results:
one Anneal model related to two independent reference authorities (`MiniRust`
and `LeanMiri`) by mode-indexed, choice-coupled simulations that follow
`docs/mir-correspondence-strategy.md` Section 4.6 and
`docs/mir-correspondence-design.md` Section 5.2. The abstraction has four
parts:

1. **Codec laws** (`CodecLaws`): a lawful partial-inverse pair between an
   abstract value domain and a representation domain, with the standard
   combinators (`CodecLaws.id`, `.comp`, `.prod`, `.ofEquiv`) and the fault
   classification codec `mirFailCodec` onto the trusted `MirFailE` requests.
2. **Mode-indexed step simulation** (`ExecOutcome4`,
   `ChoiceCoupledOutcomeRel`, `ModeParamStepRel`, `ModeStepSim`): the four-way
   outcome partition (normal, unwind, fault, diverge), the coupled outcome
   relation enforcing Cases 1–4 of Section 4.6, and a simulation record with
   unconditional forward totality, unconditional reverse totality on faulting
   executions, and optional reverse totality on all executions. From a
   `ModeStepSim` follow `CorrespondenceClaim`, `FaultEquivClaim`, and (with
   reverse totality) `ExactBehaviorEq`.
3. **Paired witnesses** (`PositiveWitness`, `FaultEquivWitness`): inhabited
   agreeing normal-return and faulting traces inside the support gate, which
   rule out antecedent collapse.
4. **Flip-direction and mode-sensitivity guards** (`FlipDirectionWitness`,
   `ModeSensitivityWitness`): a genuine polarity flip of the well-formedness
   verdict between two inputs at one mode, and an outcome reachable at one mode
   but not at another, which rule out constant and mode-blind models.

`DualCorrespondenceBundle` packages the four parts for both authorities over
one coherent Anneal execution relation and provides the combinators
`projectPositive`, `projectFault`, `crossAuthorityFaultEquiv`,
`threeWayNormalAgreement`, `liftMode`, `comp`, `trans`, and `fromEquiv`.

Every declaration is constructive: its axiom closure is contained in
`[propext, Quot.sound]`.
-/

namespace Anneal.DualCorrespondenceBundle

open Trusted.Effect
open Trusted.Rustc.V2026_06_01.MirSemantics

universe u v w u₁ u₂ v₁ v₂ w₁ w₂

/-! ## 1. Codec laws -/

/--
Lawful codec between a value domain `α` and a representation domain `β`.

`decode` is a left inverse of `encode` (`decode_encode`), every encoding is a
valid representation (`encode_valid`), and on valid representations `encode`
is a left inverse of `decode` (`encode_decode_of_valid`), so valid
representations are canonical.
-/
structure CodecLaws (α : Type u) (β : Type v) where
  /-- Encode a value as its representation. -/
  encode : α → β
  /-- Decode a representation, failing on representations of no value. -/
  decode : β → Option α
  /-- Validity (canonicity) predicate on representations. -/
  ValidRep : β → Prop := fun _ => True
  /-- Decoding an encoding returns the encoded value. -/
  decode_encode : ∀ a : α, decode (encode a) = some a
  /-- Every encoding is a valid representation. -/
  encode_valid : ∀ a : α, ValidRep (encode a)
  /-- A valid representation is the encoding of the value it decodes to. -/
  encode_decode_of_valid :
    ∀ (b : β) (a : α), ValidRep b → decode b = some a → encode a = b

namespace CodecLaws

variable {α : Type u} {β : Type v} {γ : Type w}
variable {α₁ : Type u₁} {α₂ : Type u₂} {β₁ : Type v₁} {β₂ : Type v₂}

/-- `encode` is injective. -/
theorem encode_injective (c : CodecLaws α β) {a a' : α}
    (h : c.encode a = c.encode a') : a = a' := by
  have h₁ := c.decode_encode a
  rw [h, c.decode_encode a'] at h₁
  exact (Option.some.inj h₁).symm

/-- `decode` is surjective, already when restricted to valid representations. -/
theorem decode_surjective (c : CodecLaws α β) (a : α) :
    ∃ b : β, c.ValidRep b ∧ c.decode b = some a :=
  ⟨c.encode a, c.encode_valid a, c.decode_encode a⟩

/-- On valid representations, decoding to `a` is being the encoding of `a`. -/
theorem decode_eq_some_iff (c : CodecLaws α β) {b : β} (hb : c.ValidRep b)
    {a : α} : c.decode b = some a ↔ c.encode a = b :=
  ⟨c.encode_decode_of_valid b a hb, fun h => h ▸ c.decode_encode a⟩

/-- `decode` is injective on valid representations that decode. -/
theorem decode_injective_of_valid (c : CodecLaws α β) {b b' : β}
    (hb : c.ValidRep b) (hb' : c.ValidRep b') {a : α}
    (h : c.decode b = some a) (h' : c.decode b' = some a) : b = b' :=
  (c.encode_decode_of_valid b a hb h).symm.trans
    (c.encode_decode_of_valid b' a hb' h')

/-- The identity codec. -/
protected def id (α : Type u) : CodecLaws α α where
  encode := fun a => a
  decode := fun a => some a
  decode_encode := fun _ => rfl
  encode_valid := fun _ => True.intro
  encode_decode_of_valid := fun _ _ _ h => (Option.some.inj h).symm

/--
Sequential composition of codecs. A representation is valid when it is valid
for the outer codec and its outer decoding is valid for the inner codec.
-/
def comp (c₁ : CodecLaws α β) (c₂ : CodecLaws β γ) : CodecLaws α γ where
  encode := fun a => c₂.encode (c₁.encode a)
  decode := fun g => (c₂.decode g).bind c₁.decode
  ValidRep := fun g => c₂.ValidRep g ∧ ∀ b, c₂.decode g = some b → c₁.ValidRep b
  decode_encode := fun a => by
    show (c₂.decode (c₂.encode (c₁.encode a))).bind c₁.decode = some a
    rw [c₂.decode_encode]
    exact c₁.decode_encode a
  encode_valid := fun a =>
    ⟨c₂.encode_valid _, fun b hb => by
      rw [c₂.decode_encode] at hb
      cases hb
      exact c₁.encode_valid a⟩
  encode_decode_of_valid := fun g a hv hd => by
    cases hb : c₂.decode g with
    | none =>
      have hd' : (c₂.decode g).bind c₁.decode = some a := hd
      rw [hb] at hd'
      cases hd'
    | some b =>
      have hd' : (c₂.decode g).bind c₁.decode = some a := hd
      rw [hb] at hd'
      have h₁ : c₁.encode a = b :=
        c₁.encode_decode_of_valid b a (hv.2 b hb) hd'
      have h₂ : c₂.encode b = g := c₂.encode_decode_of_valid g b hv.1 hb
      show c₂.encode (c₁.encode a) = g
      rw [h₁]
      exact h₂

/-- Componentwise product of codecs. -/
def prod (c₁ : CodecLaws α₁ β₁) (c₂ : CodecLaws α₂ β₂) :
    CodecLaws (α₁ × α₂) (β₁ × β₂) where
  encode := fun p => (c₁.encode p.1, c₂.encode p.2)
  decode := fun q =>
    (c₁.decode q.1).bind fun a₁ => (c₂.decode q.2).bind fun a₂ => some (a₁, a₂)
  ValidRep := fun q => c₁.ValidRep q.1 ∧ c₂.ValidRep q.2
  decode_encode := fun p => by
    show (c₁.decode (c₁.encode p.1)).bind
        (fun a₁ => (c₂.decode (c₂.encode p.2)).bind fun a₂ => some (a₁, a₂)) =
      some p
    rw [c₁.decode_encode, c₂.decode_encode]
    rfl
  encode_valid := fun p => ⟨c₁.encode_valid p.1, c₂.encode_valid p.2⟩
  encode_decode_of_valid := fun q p hv hd => by
    have hd' : (c₁.decode q.1).bind
        (fun a₁ => (c₂.decode q.2).bind fun a₂ => some (a₁, a₂)) = some p := hd
    cases h₁ : c₁.decode q.1 with
    | none => rw [h₁] at hd'; cases hd'
    | some a₁ =>
      cases h₂ : c₂.decode q.2 with
      | none => rw [h₁, h₂] at hd'; cases hd'
      | some a₂ =>
        rw [h₁, h₂] at hd'
        cases hd'
        have e₁ := c₁.encode_decode_of_valid q.1 a₁ hv.1 h₁
        have e₂ := c₂.encode_decode_of_valid q.2 a₂ hv.2 h₂
        show (c₁.encode a₁, c₂.encode a₂) = q
        rw [e₁, e₂]

/--
Codec of a bijection presented by mutually inverse functions `f` and `g`
(the constructive content of an equivalence `α ≃ β`). Every representation is
valid and decoding is total.
-/
def ofEquiv (f : α → β) (g : β → α) (left_inv : ∀ a, g (f a) = a)
    (right_inv : ∀ b, f (g b) = b) : CodecLaws α β where
  encode := f
  decode := fun b => some (g b)
  decode_encode := fun a => congrArg some (left_inv a)
  encode_valid := fun _ => True.intro
  encode_decode_of_valid := fun b a _ h => by
    have hg : g b = a := Option.some.inj h
    rw [← hg]
    exact right_inv b

/-- Decoding with an `ofEquiv` codec is total. -/
theorem ofEquiv_decode (f : α → β) (g : β → α) (left_inv : ∀ a, g (f a) = a)
    (right_inv : ∀ b, f (g b) = b) (b : β) :
    (ofEquiv f g left_inv right_inv).decode b = some (g b) := rfl

/-- Symmetric inverse of an `ofEquiv` codec. -/
def ofEquiv_symm (f : α → β) (g : β → α) (left_inv : ∀ a, g (f a) = a)
    (right_inv : ∀ b, f (g b) = b) : CodecLaws β α :=
  ofEquiv g f right_inv left_inv

/-- Left identity of `CodecLaws.comp` on `encode`. -/
theorem comp_id_left_encode (c : CodecLaws α β) (a : α) :
    ((CodecLaws.id α).comp c).encode a = c.encode a := rfl

/-- Left identity of `CodecLaws.comp` on `decode`. -/
theorem comp_id_left_decode (c : CodecLaws α β) (b : β) :
    ((CodecLaws.id α).comp c).decode b = c.decode b := by
  show (c.decode b).bind some = c.decode b
  cases c.decode b <;> rfl

/-- Right identity of `CodecLaws.comp` on `encode`. -/
theorem comp_id_right_encode (c : CodecLaws α β) (a : α) :
    (c.comp (CodecLaws.id β)).encode a = c.encode a := rfl

/-- Right identity of `CodecLaws.comp` on `decode`. -/
theorem comp_id_right_decode (c : CodecLaws α β) (b : β) :
    (c.comp (CodecLaws.id β)).decode b = c.decode b := rfl

/-- Associativity of `CodecLaws.comp` on `encode`. -/
theorem comp_assoc_encode {δ : Type w₁} (c₁ : CodecLaws α β)
    (c₂ : CodecLaws β γ) (c₃ : CodecLaws γ δ) (a : α) :
    ((c₁.comp c₂).comp c₃).encode a = (c₁.comp (c₂.comp c₃)).encode a := rfl

/-- Associativity of `CodecLaws.comp` on `decode`. -/
theorem comp_assoc_decode {δ : Type w₁} (c₁ : CodecLaws α β)
    (c₂ : CodecLaws β γ) (c₃ : CodecLaws γ δ) (d : δ) :
    ((c₁.comp c₂).comp c₃).decode d = (c₁.comp (c₂.comp c₃)).decode d := by
  show (c₃.decode d).bind (fun g => (c₂.decode g).bind c₁.decode) =
    ((c₃.decode d).bind c₂.decode).bind c₁.decode
  cases c₃.decode d with
  | none => rfl
  | some g => rfl

/-- Left identity of `CodecLaws.comp` on `ValidRep`. -/
theorem comp_id_left_validRep (c : CodecLaws α β) (b : β) :
    ((CodecLaws.id α).comp c).ValidRep b ↔ c.ValidRep b :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ _ => True.intro⟩⟩

/-- Right identity of `CodecLaws.comp` on `ValidRep`. -/
theorem comp_id_right_validRep (c : CodecLaws α β) (b : β) :
    (c.comp (CodecLaws.id β)).ValidRep b ↔ c.ValidRep b :=
  ⟨fun h => h.2 b rfl, fun h =>
    ⟨True.intro, fun b' hb => by cases hb; exact h⟩⟩

/-- Associativity of `CodecLaws.comp` on `ValidRep`. -/
theorem comp_assoc_validRep {δ : Type w₁} (c₁ : CodecLaws α β)
    (c₂ : CodecLaws β γ) (c₃ : CodecLaws γ δ) (d : δ) :
    ((c₁.comp c₂).comp c₃).ValidRep d ↔
      (c₁.comp (c₂.comp c₃)).ValidRep d := by
  show (c₃.ValidRep d ∧ ∀ g, c₃.decode d = some g →
      (c₂.ValidRep g ∧ ∀ b, c₂.decode g = some b → c₁.ValidRep b)) ↔
    ((c₃.ValidRep d ∧ ∀ g, c₃.decode d = some g → c₂.ValidRep g) ∧
      ∀ b, ((c₃.decode d).bind c₂.decode) = some b → c₁.ValidRep b)
  constructor
  · intro ⟨hv₃, hgc⟩
    refine ⟨⟨hv₃, fun g hg => (hgc g hg).1⟩, fun b hbind => ?_⟩
    cases hg : c₃.decode d with
    | none => rw [hg] at hbind; cases hbind
    | some g =>
      rw [hg] at hbind
      exact (hgc g hg).2 b hbind
  · intro ⟨⟨hv₃, hg₂⟩, hb₁⟩
    refine ⟨hv₃, fun g hg => ⟨hg₂ g hg, fun b hb => ?_⟩⟩
    apply hb₁ b
    rw [hg]
    exact hb

/-- Extensionality of `CodecLaws`: two codecs with pointwise equal `encode`
and `decode` and equivalent `ValidRep` predicates are equal records. -/
theorem ext {c₁ c₂ : CodecLaws α β} (henc : ∀ a, c₁.encode a = c₂.encode a)
    (hdec : ∀ b, c₁.decode b = c₂.decode b)
    (hval : ∀ b, c₁.ValidRep b ↔ c₂.ValidRep b) : c₁ = c₂ := by
  have he : c₁.encode = c₂.encode := funext henc
  have hd : c₁.decode = c₂.decode := funext hdec
  have hv : c₁.ValidRep = c₂.ValidRep := funext fun b => propext (hval b)
  cases c₁
  cases c₂
  dsimp only [] at he hd hv
  subst he hd hv
  rfl

/-- Full left identity law of `CodecLaws`: `(CodecLaws.id α).comp c = c`. -/
theorem comp_id_left (c : CodecLaws α β) : (CodecLaws.id α).comp c = c :=
  ext (comp_id_left_encode c) (comp_id_left_decode c) (comp_id_left_validRep c)

/-- Full right identity law of `CodecLaws`: `c.comp (CodecLaws.id β) = c`. -/
theorem comp_id_right (c : CodecLaws α β) : c.comp (CodecLaws.id β) = c :=
  ext (comp_id_right_encode c) (comp_id_right_decode c)
    (comp_id_right_validRep c)

/-- Full associativity law of `CodecLaws`. -/
theorem comp_assoc {δ : Type w₁} (c₁ : CodecLaws α β) (c₂ : CodecLaws β γ)
    (c₃ : CodecLaws γ δ) :
    (c₁.comp c₂).comp c₃ = c₁.comp (c₂.comp c₃) :=
  ext (comp_assoc_encode c₁ c₂ c₃) (comp_assoc_decode c₁ c₂ c₃)
    (comp_assoc_validRep c₁ c₂ c₃)

/-- Left inverse law of `ofEquiv` composed with `ofEquiv_symm`. -/
theorem ofEquiv_comp_symm (f : α → β) (g : β → α)
    (left_inv : ∀ a, g (f a) = a) (right_inv : ∀ b, f (g b) = b) :
    (ofEquiv f g left_inv right_inv).comp
        (ofEquiv_symm f g left_inv right_inv) =
      CodecLaws.id α :=
  ext left_inv (fun a => congrArg some (left_inv a))
    (fun _ =>
      ⟨fun _ => True.intro, fun _ => ⟨True.intro, fun _ _ => True.intro⟩⟩)

/-- Right inverse law of `ofEquiv_symm` composed with `ofEquiv`. -/
theorem symm_comp_ofEquiv (f : α → β) (g : β → α)
    (left_inv : ∀ a, g (f a) = a) (right_inv : ∀ b, f (g b) = b) :
    (ofEquiv_symm f g left_inv right_inv).comp
        (ofEquiv f g left_inv right_inv) =
      CodecLaws.id β :=
  ofEquiv_comp_symm g f right_inv left_inv

/-- Identity law for `CodecLaws.prod`: `(id α).prod (id β) = id (α × β)`. -/
theorem prod_id (α : Type u) (β : Type v) :
    (CodecLaws.id α).prod (CodecLaws.id β) = CodecLaws.id (α × β) :=
  ext (fun _ => rfl) (fun _ => rfl)
    (fun _ => ⟨fun _ => True.intro, fun _ => ⟨True.intro, True.intro⟩⟩)

/-- Functoriality of `CodecLaws.prod` on `encode`. -/
theorem prod_comp_encode {γ₁ : Type w₁} {γ₂ : Type w₂}
    (c₁ : CodecLaws α₁ β₁) (d₁ : CodecLaws β₁ γ₁)
    (c₂ : CodecLaws α₂ β₂) (d₂ : CodecLaws β₂ γ₂) (p : α₁ × α₂) :
    ((c₁.comp d₁).prod (c₂.comp d₂)).encode p =
      ((c₁.prod c₂).comp (d₁.prod d₂)).encode p := rfl

/-- Functoriality of `CodecLaws.prod` on `decode`. -/
theorem prod_comp_decode {γ₁ : Type w₁} {γ₂ : Type w₂}
    (c₁ : CodecLaws α₁ β₁) (d₁ : CodecLaws β₁ γ₁)
    (c₂ : CodecLaws α₂ β₂) (d₂ : CodecLaws β₂ γ₂) (q : γ₁ × γ₂) :
    ((c₁.comp d₁).prod (c₂.comp d₂)).decode q =
      ((c₁.prod c₂).comp (d₁.prod d₂)).decode q := by
  show ((d₁.decode q.1).bind c₁.decode).bind
      (fun a₁ => ((d₂.decode q.2).bind c₂.decode).bind fun a₂ => some (a₁, a₂))
    = ((d₁.decode q.1).bind fun b₁ =>
        (d₂.decode q.2).bind fun b₂ => some (b₁, b₂)).bind
      (fun b => (c₁.decode b.1).bind fun a₁ =>
        (c₂.decode b.2).bind fun a₂ => some (a₁, a₂))
  cases d₁.decode q.1 with
  | none => rfl
  | some b₁ =>
    cases d₂.decode q.2 with
    | none =>
      dsimp only [Option.bind]
      cases c₁.decode b₁ <;> rfl
    | some b₂ => rfl

end CodecLaws

/--
Fault classification shared by Anneal and the reference authorities: undefined
behavior versus an unsupported (unmodeled) construct. These are the two
classifications `k` of Case 1 in `docs/mir-correspondence-strategy.md`
Section 4.6.
-/
inductive CorrFaultKind : Type where
  /-- Undefined behavior. -/
  | undefined
  /-- Unsupported construct (fail-closed semantic boundary). -/
  | unsupported
  deriving DecidableEq, Repr

namespace CorrFaultKind

/-- Trusted `FailureKind` of a correspondence fault classification. -/
def toFailureKind : CorrFaultKind → FailureKind
  | .undefined => .ub
  | .unsupported => .unsupported

/--
Correspondence fault classification of a trusted `FailureKind`. Fuel exhaustion
(`FailureKind.outOfFuel`) is an artifact of bounded evaluation, not a fault of
the program, and has no classification.
-/
def ofFailureKind? : FailureKind → Option CorrFaultKind
  | .ub => some .undefined
  | .unsupported => some .unsupported
  | .outOfFuel => none

/-- `ofFailureKind?` inverts `toFailureKind`. -/
theorem ofFailureKind?_toFailureKind (k : CorrFaultKind) :
    ofFailureKind? k.toFailureKind = some k := by
  cases k <;> rfl

/-- A classified `FailureKind` is the image of its classification. -/
theorem toFailureKind_of_ofFailureKind? {fk : FailureKind} {k : CorrFaultKind}
    (h : ofFailureKind? fk = some k) : k.toFailureKind = fk := by
  cases fk with
  | ub => cases h; rfl
  | unsupported => cases h; rfl
  | outOfFuel => cases h

end CorrFaultKind

/--
Codec between correspondence fault classifications and the request type
`MirFailE.I` of the trusted fault effect `MirFailE = FailE FailureKind`.

The value domain is `CorrFaultKind` and the representation domain is
`MirFailE.I`: the trusted effect has the additional request
`.fail .outOfFuel`, which represents no fault classification and is the unique
invalid representation. The opposite orientation is not a lawful codec
(`not_codecLaws_mirFail_corrFaultKind`).
-/
def mirFailCodec : CodecLaws CorrFaultKind MirFailE.I where
  encode := fun k => FailReq.fail k.toFailureKind
  decode := fun r =>
    match r with
    | FailReq.fail fk => CorrFaultKind.ofFailureKind? fk
  ValidRep := fun r => r ≠ FailReq.fail FailureKind.outOfFuel
  decode_encode := fun k => CorrFaultKind.ofFailureKind?_toFailureKind k
  encode_valid := fun k h => by cases k <;> cases h
  encode_decode_of_valid := fun r k _ hd => by
    cases r with
    | fail fk =>
      show FailReq.fail k.toFailureKind = FailReq.fail fk
      rw [CorrFaultKind.toFailureKind_of_ofFailureKind? hd]

/-- `mirFailCodec` sends undefined behavior to the trusted `.fail .ub`. -/
theorem mirFailCodec_encode_undefined :
    mirFailCodec.encode .undefined = FailReq.fail FailureKind.ub := rfl

/-- `mirFailCodec` sends `unsupported` to the trusted `.fail .unsupported`. -/
theorem mirFailCodec_encode_unsupported :
    mirFailCodec.encode .unsupported = FailReq.fail FailureKind.unsupported :=
  rfl

/-- Fuel exhaustion decodes to no fault classification. -/
theorem mirFailCodec_decode_outOfFuel :
    mirFailCodec.decode (FailReq.fail FailureKind.outOfFuel) = none := rfl

/-- Fuel exhaustion is the only invalid `MirFailE` representation. -/
theorem mirFailCodec_validRep_iff (r : MirFailE.I) :
    mirFailCodec.ValidRep r ↔ ∃ k, mirFailCodec.decode r = some k := by
  cases r with
  | fail fk =>
    cases fk with
    | ub => exact ⟨fun _ => ⟨.undefined, rfl⟩, fun _ h => by cases h⟩
    | unsupported => exact ⟨fun _ => ⟨.unsupported, rfl⟩, fun _ h => by cases h⟩
    | outOfFuel =>
      exact ⟨fun h => absurd rfl h, fun ⟨_, h⟩ => by cases h⟩

/--
There is no lawful codec with value domain `MirFailE.I` and representation
domain `CorrFaultKind`: the three trusted fault requests cannot be encoded
injectively into two classifications. This fixes the orientation of
`mirFailCodec`.
-/
theorem not_codecLaws_mirFail_corrFaultKind
    (c : CodecLaws MirFailE.I CorrFaultKind) : False := by
  have ne₁ : (FailReq.fail FailureKind.ub : MirFailE.I) ≠
      FailReq.fail FailureKind.unsupported := fun h => by cases h
  have ne₂ : (FailReq.fail FailureKind.ub : MirFailE.I) ≠
      FailReq.fail FailureKind.outOfFuel := fun h => by cases h
  have ne₃ : (FailReq.fail FailureKind.unsupported : MirFailE.I) ≠
      FailReq.fail FailureKind.outOfFuel := fun h => by cases h
  cases h₁ : c.encode (FailReq.fail FailureKind.ub) <;>
    cases h₂ : c.encode (FailReq.fail FailureKind.unsupported) <;>
    cases h₃ : c.encode (FailReq.fail FailureKind.outOfFuel) <;>
    first
      | exact ne₁ (c.encode_injective (h₁.trans h₂.symm))
      | exact ne₂ (c.encode_injective (h₁.trans h₃.symm))
      | exact ne₃ (c.encode_injective (h₂.trans h₃.symm))

/--
Lawful codec in the opposite orientation (`MirFailE.I → CorrFaultKind`) once
fuel exhaustion (`FailureKind.outOfFuel`) is excluded from the domain: the two
non-fuel trusted fault requests are in constructive bijection with
`CorrFaultKind` (`CodecLaws.ofEquiv`).
-/
def mirFailNonFuelCodec :
    CodecLaws { r : MirFailE.I // r ≠ FailReq.fail FailureKind.outOfFuel }
      CorrFaultKind :=
  CodecLaws.ofEquiv
    (fun ⟨r, hr⟩ =>
      match r with
      | FailReq.fail .ub => .undefined
      | FailReq.fail .unsupported => .unsupported
      | FailReq.fail .outOfFuel => False.elim (hr rfl))
    (fun k =>
      match k with
      | .undefined => ⟨FailReq.fail .ub, fun h => by cases h⟩
      | .unsupported => ⟨FailReq.fail .unsupported, fun h => by cases h⟩)
    (fun ⟨r, hr⟩ => by
      cases r with
      | fail fk =>
        cases fk with
        | ub => rfl
        | unsupported => rfl
        | outOfFuel => exact False.elim (hr rfl))
    (fun k => by cases k <;> rfl)

/-- `mirFailNonFuelCodec` decodes `.undefined` to `.fail .ub`. -/
theorem mirFailNonFuelCodec_decode_undefined :
    (mirFailNonFuelCodec.decode .undefined).map Subtype.val =
      some (FailReq.fail FailureKind.ub) := rfl

/-- `mirFailNonFuelCodec` decodes `.unsupported` to `.fail .unsupported`. -/
theorem mirFailNonFuelCodec_decode_unsupported :
    (mirFailNonFuelCodec.decode .unsupported).map Subtype.val =
      some (FailReq.fail FailureKind.unsupported) := rfl

/-! ## 2. Four-way choice-coupled outcome partition -/

/--
Outcome of one complete execution: the four mutually exclusive outcome classes
of `docs/mir-correspondence-strategy.md` Section 4.6. `diverge` denotes an
infinite productive execution, never fuel exhaustion.
-/
inductive ExecOutcome4 (Ret : Type u) (Unw : Type v) : Type (max u v) where
  /-- Normal return from the entry frame with `ret`. -/
  | normal (ret : Ret)
  /-- Unwinding out of the entry frame with `payload`. -/
  | unwind (payload : Unw)
  /-- Fault with classification `kind`. -/
  | fault (kind : CorrFaultKind)
  /-- Infinite productive execution. -/
  | diverge

namespace ExecOutcome4

variable {Ret : Type u} {Unw : Type v}

/-- The four outcome classes are exhaustive. -/
theorem partition (o : ExecOutcome4 Ret Unw) :
    (∃ r, o = .normal r) ∨ (∃ p, o = .unwind p) ∨ (∃ k, o = .fault k) ∨
      o = .diverge := by
  cases o with
  | normal r => exact Or.inl ⟨r, rfl⟩
  | unwind p => exact Or.inr (Or.inl ⟨p, rfl⟩)
  | fault k => exact Or.inr (Or.inr (Or.inl ⟨k, rfl⟩))
  | diverge => exact Or.inr (Or.inr (Or.inr rfl))

/-- `true` exactly on faulting outcomes. -/
def isFault : ExecOutcome4 Ret Unw → Bool
  | .fault _ => true
  | _ => false

/-- `isFault` characterizes the fault class. -/
theorem isFault_iff (o : ExecOutcome4 Ret Unw) :
    o.isFault = true ↔ ∃ k, o = .fault k := by
  cases o with
  | normal r => exact ⟨fun h => (by cases h), fun ⟨_, h⟩ => by cases h⟩
  | unwind p => exact ⟨fun h => (by cases h), fun ⟨_, h⟩ => by cases h⟩
  | fault k => exact ⟨fun _ => ⟨k, rfl⟩, fun _ => rfl⟩
  | diverge => exact ⟨fun h => (by cases h), fun ⟨_, h⟩ => by cases h⟩

/--
Outcome of a trusted terminal `MirOutcome`: a normal return keeps its
`(value, memory)` payload, a panic is an unwind out of the entry frame, and an
abort is classified `unsupported` (Section 4.6, Case 3: abnormal process
termination stays `unsupported` until an explicit aborted outcome exists).
-/
def ofMirOutcome : MirOutcome → ExecOutcome4 MirReturn Unit
  | .normal r => .normal r
  | .panic => .unwind ()
  | .abort => .fault .unsupported

/--
Outcome observed at a trusted `MirExecState`, if it is terminal. A `running`
state is not an outcome (a finite prefix is not divergence), and a
fuel-exhaustion fault has no classification.
-/
def ofMirExecState : MirExecState → Option (ExecOutcome4 MirReturn Unit)
  | .running _ => none
  | .halted out => some (ofMirOutcome out)
  | .faulted fk => (CorrFaultKind.ofFailureKind? fk).map .fault

/-- A normal trusted outcome is a normal `ExecOutcome4`, and conversely. -/
theorem ofMirOutcome_eq_normal_iff (out : MirOutcome) (r : MirReturn) :
    ofMirOutcome out = .normal r ↔ out = .normal r := by
  cases out with
  | normal r' =>
    exact ⟨fun h => (by cases h; rfl), fun h => by cases h; rfl⟩
  | panic => exact ⟨fun h => (by cases h), fun h => by cases h⟩
  | abort => exact ⟨fun h => (by cases h), fun h => by cases h⟩

/-- A trusted outcome never maps to an undefined-behavior fault. -/
theorem ofMirOutcome_ne_undefined (out : MirOutcome) :
    ofMirOutcome out ≠ .fault .undefined := by
  cases out <;> intro h <;> cases h

/-- A trusted terminal outcome is never divergence. -/
theorem ofMirOutcome_ne_diverge (out : MirOutcome) :
    ofMirOutcome out ≠ .diverge := by
  cases out <;> intro h <;> cases h

/-- No trusted execution state is observed as divergence. -/
theorem ofMirExecState_ne_diverge (st : MirExecState) :
    ofMirExecState st ≠ some .diverge := by
  cases st with
  | running s => intro h; cases h
  | halted out =>
    intro h
    exact ofMirOutcome_ne_diverge out (Option.some.inj h)
  | faulted fk => cases fk <;> intro h <;> cases h

/-- A running state has no outcome. -/
theorem ofMirExecState_running (s : MachineState) :
    ofMirExecState (.running s) = none := rfl

/-- A trusted `.ub` fault is an `undefined` fault. -/
theorem ofMirExecState_faulted_ub :
    ofMirExecState (.faulted .ub) = some (.fault .undefined) := rfl

/-- A trusted `.unsupported` fault is an `unsupported` fault. -/
theorem ofMirExecState_faulted_unsupported :
    ofMirExecState (.faulted .unsupported) = some (.fault .unsupported) := rfl

/-- Fuel exhaustion is not an outcome. -/
theorem ofMirExecState_faulted_outOfFuel :
    ofMirExecState (.faulted .outOfFuel) = none := rfl

/-- A normal halted state has a normal outcome. -/
theorem ofMirExecState_halted_normal (r : MirReturn) :
    ofMirExecState (.halted (.normal r)) = some (.normal r) := rfl

/-- A panicking halted state has an unwind outcome. -/
theorem ofMirExecState_halted_panic :
    ofMirExecState (.halted .panic) = some (.unwind ()) := rfl

/-- An aborting halted state is classified `unsupported`. -/
theorem ofMirExecState_halted_abort :
    ofMirExecState (.halted .abort) = some (.fault .unsupported) := rfl

/--
A faulted state has outcome `.fault k` exactly when its `FailureKind` is the
`mirFailCodec` encoding of `k`.
-/
theorem ofMirExecState_faulted_iff (fk : FailureKind) (k : CorrFaultKind) :
    ofMirExecState (.faulted fk) = some (.fault k) ↔
      mirFailCodec.encode k = FailReq.fail fk := by
  cases fk <;> cases k <;>
    first
      | exact ⟨fun _ => rfl, fun _ => rfl⟩
      | exact ⟨fun h => (by cases h), fun h => by cases h⟩

end ExecOutcome4

/-- Relational composition. -/
def RelComp {α : Type u} {β : Type v} {γ : Type w} (R : α → β → Prop)
    (S : β → γ → Prop) : α → γ → Prop :=
  fun a c => ∃ b, R a b ∧ S b c

/--
Outcome relation on one choice-coupled pair of executions (Anneal outcome
`outA`, reference outcome `outR`), enforcing Cases 1–4 of
`docs/mir-correspondence-strategy.md` Section 4.6:

1. `fault_iff`: either execution faults with classification `k` exactly when
   the other does (universal and bidirectional);
2. `normal_ref_to_anneal`: a normal reference return is matched by a normal
   Anneal return related by `RetRel`;
3. `unwind_ref_to_anneal`: a reference unwind is matched by an Anneal unwind
   related by `UnwRel`;
4. `diverge_ref_to_anneal`: reference divergence is matched by Anneal
   divergence.

Cases 2–4 are stated in the reference-to-Anneal direction only; the converse
directions are the theorem `ChoiceCoupledOutcomeRel.anneal_to_ref`.
-/
structure ChoiceCoupledOutcomeRel {RetA : Type u₁} {RetR : Type u₂}
    {UnwA : Type v₁} {UnwR : Type v₂} (RetRel : RetA → RetR → Prop)
    (UnwRel : UnwA → UnwR → Prop) (outA : ExecOutcome4 RetA UnwA)
    (outR : ExecOutcome4 RetR UnwR) : Prop where
  /-- Case 1: faults agree, with identical classification, both ways. -/
  fault_iff : ∀ k : CorrFaultKind, outA = .fault k ↔ outR = .fault k
  /-- Case 2: a normal reference return has a related normal Anneal return. -/
  normal_ref_to_anneal :
    ∀ r : RetR, outR = .normal r → ∃ a : RetA, outA = .normal a ∧ RetRel a r
  /-- Case 3: a reference unwind has a related Anneal unwind. -/
  unwind_ref_to_anneal :
    ∀ p : UnwR, outR = .unwind p → ∃ a : UnwA, outA = .unwind a ∧ UnwRel a p
  /-- Case 4: reference divergence is Anneal divergence. -/
  diverge_ref_to_anneal : outR = .diverge → outA = .diverge

namespace ChoiceCoupledOutcomeRel

variable {RetA : Type u₁} {RetR : Type u₂} {UnwA : Type v₁} {UnwR : Type v₂}
variable {RetRel : RetA → RetR → Prop} {UnwRel : UnwA → UnwR → Prop}
variable {outA : ExecOutcome4 RetA UnwA} {outR : ExecOutcome4 RetR UnwR}

/-- Related normal returns are coupled. -/
theorem ofNormal {a : RetA} {r : RetR} (h : RetRel a r) :
    ChoiceCoupledOutcomeRel RetRel UnwRel (.normal a) (.normal r) where
  fault_iff := fun _ => ⟨fun e => (by cases e), fun e => by cases e⟩
  normal_ref_to_anneal := fun _ e => by cases e; exact ⟨a, rfl, h⟩
  unwind_ref_to_anneal := fun _ e => by cases e
  diverge_ref_to_anneal := fun e => by cases e

/-- Related unwinds are coupled. -/
theorem ofUnwind {a : UnwA} {p : UnwR} (h : UnwRel a p) :
    ChoiceCoupledOutcomeRel RetRel UnwRel (.unwind a) (.unwind p) where
  fault_iff := fun _ => ⟨fun e => (by cases e), fun e => by cases e⟩
  normal_ref_to_anneal := fun _ e => by cases e
  unwind_ref_to_anneal := fun _ e => by cases e; exact ⟨a, rfl, h⟩
  diverge_ref_to_anneal := fun e => by cases e

/-- Faults with the same classification are coupled. -/
theorem ofFault (k : CorrFaultKind) :
    ChoiceCoupledOutcomeRel RetRel UnwRel (.fault k) (.fault k) where
  fault_iff := fun _ => ⟨fun e => (by cases e; rfl), fun e => by cases e; rfl⟩
  normal_ref_to_anneal := fun _ e => by cases e
  unwind_ref_to_anneal := fun _ e => by cases e
  diverge_ref_to_anneal := fun e => by cases e

/-- Divergent executions are coupled. -/
theorem ofDiverge :
    ChoiceCoupledOutcomeRel RetRel UnwRel
      (.diverge : ExecOutcome4 RetA UnwA) (.diverge : ExecOutcome4 RetR UnwR)
    where
  fault_iff := fun _ => ⟨fun e => (by cases e), fun e => by cases e⟩
  normal_ref_to_anneal := fun _ e => by cases e
  unwind_ref_to_anneal := fun _ e => by cases e
  diverge_ref_to_anneal := fun _ => rfl

/--
**Constructive partition theorem.** Because `ExecOutcome4` partitions outcomes
into four mutually exclusive classes, the reference-to-Anneal Cases 2–4
together with bidirectional Case 1 already force the Anneal-to-reference
directions: a normal, unwinding, or diverging Anneal outcome is matched by a
reference outcome of the same class. The proof is a case split on `outR` and
uses no classical reasoning.
-/
theorem anneal_to_ref (h : ChoiceCoupledOutcomeRel RetRel UnwRel outA outR) :
    (∀ a : RetA, outA = .normal a → ∃ r : RetR, outR = .normal r ∧ RetRel a r) ∧
    (∀ a : UnwA, outA = .unwind a → ∃ p : UnwR, outR = .unwind p ∧ UnwRel a p) ∧
    (outA = .diverge → outR = .diverge) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    cases hR : outR with
    | normal r =>
      obtain ⟨a', ha', hrel⟩ := h.normal_ref_to_anneal r hR
      rw [ha] at ha'
      cases ha'
      exact ⟨r, rfl, hrel⟩
    | unwind p =>
      obtain ⟨a', ha', _⟩ := h.unwind_ref_to_anneal p hR
      rw [ha] at ha'
      cases ha'
    | fault k =>
      have hk := (h.fault_iff k).mpr hR
      rw [ha] at hk
      cases hk
    | diverge =>
      have hd := h.diverge_ref_to_anneal hR
      rw [ha] at hd
      cases hd
  · intro a ha
    cases hR : outR with
    | normal r =>
      obtain ⟨a', ha', _⟩ := h.normal_ref_to_anneal r hR
      rw [ha] at ha'
      cases ha'
    | unwind p =>
      obtain ⟨a', ha', hrel⟩ := h.unwind_ref_to_anneal p hR
      rw [ha] at ha'
      cases ha'
      exact ⟨p, rfl, hrel⟩
    | fault k =>
      have hk := (h.fault_iff k).mpr hR
      rw [ha] at hk
      cases hk
    | diverge =>
      have hd := h.diverge_ref_to_anneal hR
      rw [ha] at hd
      cases hd
  · intro ha
    cases hR : outR with
    | normal r =>
      obtain ⟨a', ha', _⟩ := h.normal_ref_to_anneal r hR
      rw [ha] at ha'
      cases ha'
    | unwind p =>
      obtain ⟨a', ha', _⟩ := h.unwind_ref_to_anneal p hR
      rw [ha] at ha'
      cases ha'
    | fault k =>
      have hk := (h.fault_iff k).mpr hR
      rw [ha] at hk
      cases hk
    | diverge => rfl

/-- A normal Anneal outcome is matched by a related normal reference outcome. -/
theorem normal_anneal_to_ref
    (h : ChoiceCoupledOutcomeRel RetRel UnwRel outA outR) (a : RetA)
    (ha : outA = .normal a) : ∃ r : RetR, outR = .normal r ∧ RetRel a r :=
  h.anneal_to_ref.1 a ha

/-- An unwinding Anneal outcome is matched by a related reference unwind. -/
theorem unwind_anneal_to_ref
    (h : ChoiceCoupledOutcomeRel RetRel UnwRel outA outR) (a : UnwA)
    (ha : outA = .unwind a) : ∃ p : UnwR, outR = .unwind p ∧ UnwRel a p :=
  h.anneal_to_ref.2.1 a ha

/-- Anneal divergence is matched by reference divergence. -/
theorem diverge_anneal_to_ref
    (h : ChoiceCoupledOutcomeRel RetRel UnwRel outA outR)
    (ha : outA = .diverge) : outR = .diverge :=
  h.anneal_to_ref.2.2 ha

/--
The coupled outcome relation is exactly "same outcome class with related
payloads": it is neither weaker nor stronger than the class-wise relation.
-/
theorem iff_sameClass :
    ChoiceCoupledOutcomeRel RetRel UnwRel outA outR ↔
      (match outA, outR with
        | .normal a, .normal r => RetRel a r
        | .unwind a, .unwind p => UnwRel a p
        | .fault k, .fault k' => k = k'
        | .diverge, .diverge => True
        | _, _ => False) := by
  constructor
  · intro h
    cases hR : outR with
    | normal r =>
      obtain ⟨a, ha, hrel⟩ := h.normal_ref_to_anneal r hR
      rw [ha]
      exact hrel
    | unwind p =>
      obtain ⟨a, ha, hrel⟩ := h.unwind_ref_to_anneal p hR
      rw [ha]
      exact hrel
    | fault k =>
      have ha := (h.fault_iff k).mpr hR
      rw [ha]
    | diverge =>
      have ha := h.diverge_ref_to_anneal hR
      rw [ha]
      exact True.intro
  · intro h
    cases outA with
    | normal a =>
      cases outR with
      | normal r => exact ofNormal h
      | unwind p => exact False.elim h
      | fault k => exact False.elim h
      | diverge => exact False.elim h
    | unwind a =>
      cases outR with
      | normal r => exact False.elim h
      | unwind p => exact ofUnwind h
      | fault k => exact False.elim h
      | diverge => exact False.elim h
    | fault k =>
      cases outR with
      | normal r => exact False.elim h
      | unwind p => exact False.elim h
      | fault k' =>
        have hk : k = k' := h
        rw [hk]
        exact ofFault k'
      | diverge => exact False.elim h
    | diverge =>
      cases outR with
      | normal r => exact False.elim h
      | unwind p => exact False.elim h
      | fault k => exact False.elim h
      | diverge => exact ofDiverge

/-- Weakening of the payload relations. -/
theorem mono {RetRel' : RetA → RetR → Prop} {UnwRel' : UnwA → UnwR → Prop}
    (hRet : ∀ a r, RetRel a r → RetRel' a r)
    (hUnw : ∀ a p, UnwRel a p → UnwRel' a p)
    (h : ChoiceCoupledOutcomeRel RetRel UnwRel outA outR) :
    ChoiceCoupledOutcomeRel RetRel' UnwRel' outA outR where
  fault_iff := h.fault_iff
  normal_ref_to_anneal := fun r hr =>
    let ⟨a, ha, hrel⟩ := h.normal_ref_to_anneal r hr
    ⟨a, ha, hRet a r hrel⟩
  unwind_ref_to_anneal := fun p hp =>
    let ⟨a, ha, hrel⟩ := h.unwind_ref_to_anneal p hp
    ⟨a, ha, hUnw a p hrel⟩
  diverge_ref_to_anneal := h.diverge_ref_to_anneal

/-- Reflexivity, for reflexive payload relations. -/
theorem refl {Ret : Type u₁} {Unw : Type v₁} {RetRel : Ret → Ret → Prop}
    {UnwRel : Unw → Unw → Prop} (hRet : ∀ r, RetRel r r)
    (hUnw : ∀ p, UnwRel p p) (o : ExecOutcome4 Ret Unw) :
    ChoiceCoupledOutcomeRel RetRel UnwRel o o where
  fault_iff := fun _ => Iff.rfl
  normal_ref_to_anneal := fun r hr => ⟨r, hr, hRet r⟩
  unwind_ref_to_anneal := fun p hp => ⟨p, hp, hUnw p⟩
  diverge_ref_to_anneal := fun h => h

/-- Transitivity, composing the payload relations. -/
theorem trans {RetB : Type w₁} {UnwB : Type w₂}
    {RetRel₁ : RetA → RetB → Prop} {UnwRel₁ : UnwA → UnwB → Prop}
    {RetRel₂ : RetB → RetR → Prop} {UnwRel₂ : UnwB → UnwR → Prop}
    {outB : ExecOutcome4 RetB UnwB}
    (h₁ : ChoiceCoupledOutcomeRel RetRel₁ UnwRel₁ outA outB)
    (h₂ : ChoiceCoupledOutcomeRel RetRel₂ UnwRel₂ outB outR) :
    ChoiceCoupledOutcomeRel (RelComp RetRel₁ RetRel₂) (RelComp UnwRel₁ UnwRel₂)
      outA outR where
  fault_iff := fun k => (h₁.fault_iff k).trans (h₂.fault_iff k)
  normal_ref_to_anneal := fun r hr =>
    let ⟨b, hb, hbr⟩ := h₂.normal_ref_to_anneal r hr
    let ⟨a, ha, hab⟩ := h₁.normal_ref_to_anneal b hb
    ⟨a, ha, b, hab, hbr⟩
  unwind_ref_to_anneal := fun p hp =>
    let ⟨b, hb, hbp⟩ := h₂.unwind_ref_to_anneal p hp
    let ⟨a, ha, hab⟩ := h₁.unwind_ref_to_anneal b hb
    ⟨a, ha, b, hab, hbp⟩
  diverge_ref_to_anneal := fun hr =>
    h₁.diverge_ref_to_anneal (h₂.diverge_ref_to_anneal hr)

/--
Symmetry up to converse payload relations: by the partition theorem the
coupled relation has no preferred direction.
-/
theorem flip (h : ChoiceCoupledOutcomeRel RetRel UnwRel outA outR) :
    ChoiceCoupledOutcomeRel (fun r a => RetRel a r) (fun p a => UnwRel a p)
      outR outA where
  fault_iff := fun k => (h.fault_iff k).symm
  normal_ref_to_anneal := fun a ha => h.normal_anneal_to_ref a ha
  unwind_ref_to_anneal := fun a ha => h.unwind_anneal_to_ref a ha
  diverge_ref_to_anneal := fun ha => h.diverge_anneal_to_ref ha

end ChoiceCoupledOutcomeRel

/-! ## 3. Mode-indexed step relations and simulations -/

universe uM uP uQ uC uRA uRR uUA uUR uRB uUB uM'

/--
Mode-indexed execution relations of an Anneal model and a reference model on a
shared program, query, and external choice.

`ExecA m p q c out` (resp. `ExecR`) states that the Anneal (resp. reference)
model, in mode `m`, has a complete execution of program `p` on query `q` along
the shared external choice trace `c` with outcome `out`. Sharing `c` is the
choice coupling of `docs/mir-correspondence-strategy.md` Section 4.6: paired
executions never permute distinct external choices. `SupportGate` is the
audited fragment on which correspondence is claimed, and `RetRel` / `UnwRel`
relate normal-return and unwind payloads.
-/
structure ModeParamStepRel (Mode : Type uM) (Prog : Type uP) (Query : Type uQ)
    (Choice : Type uC) (RetA : Type uRA) (RetR : Type uRR) (UnwA : Type uUA)
    (UnwR : Type uUR) where
  /-- Fragment of `(mode, program, query)` triples covered by the claims. -/
  SupportGate : Mode → Prog → Query → Prop
  /-- Complete executions of the Anneal model. -/
  ExecA : Mode → Prog → Query → Choice → ExecOutcome4 RetA UnwA → Prop
  /-- Complete executions of the reference model. -/
  ExecR : Mode → Prog → Query → Choice → ExecOutcome4 RetR UnwR → Prop
  /-- Relation between normal-return payloads. -/
  RetRel : RetA → RetR → Prop
  /-- Relation between unwind payloads. -/
  UnwRel : UnwA → UnwR → Prop

section StepRel

variable {Mode : Type uM} {Prog : Type uP} {Query : Type uQ} {Choice : Type uC}
variable {RetA : Type uRA} {RetR : Type uRR} {UnwA : Type uUA} {UnwR : Type uUR}

namespace ModeParamStepRel

variable (R : ModeParamStepRel Mode Prog Query Choice RetA RetR UnwA UnwR)

/-- Coupled outcome relation of `R` (Cases 1–4 of Section 4.6). -/
abbrev Coupled (outA : ExecOutcome4 RetA UnwA) (outR : ExecOutcome4 RetR UnwR) :
    Prop :=
  ChoiceCoupledOutcomeRel R.RetRel R.UnwRel outA outR

/-- No Anneal execution of `p` on `q` in mode `m` faults. -/
def WellFormedAnneal (m : Mode) (p : Prog) (q : Query) : Prop :=
  ∀ (c : Choice) (k : CorrFaultKind), ¬ R.ExecA m p q c (.fault k)

/-- No reference execution of `p` on `q` in mode `m` faults. -/
def WellFormedRef (m : Mode) (p : Prog) (q : Query) : Prop :=
  ∀ (c : Choice) (k : CorrFaultKind), ¬ R.ExecR m p q c (.fault k)

/--
Anneal productivity (`docs/mir-correspondence-strategy.md` Section 4.5, no
silent stuck states): every gated `(mode, program, query)` triple has at least
one complete Anneal execution.
-/
def ProductiveAnneal : Prop :=
  ∀ (m : Mode) (p : Prog) (q : Query),
    R.SupportGate m p q → ∃ (c : Choice) (outA : ExecOutcome4 RetA UnwA),
      R.ExecA m p q c outA

/--
Reference productivity (`docs/mir-correspondence-strategy.md` Section 4.5, no
silent stuck states): every gated `(mode, program, query)` triple has at least
one complete reference execution.
-/
def ProductiveRef : Prop :=
  ∀ (m : Mode) (p : Prog) (q : Query),
    R.SupportGate m p q → ∃ (c : Choice) (outR : ExecOutcome4 RetR UnwR),
      R.ExecR m p q c outR

/--
Unconditional forward totality (reference to Anneal, across all valid
executions): every reference execution inside the gate has a choice-coupled
Anneal execution satisfying Cases 1–4.
-/
def ForwardTotal : Prop :=
  ∀ (m : Mode) (p : Prog) (q : Query) (c : Choice)
    (outR : ExecOutcome4 RetR UnwR),
    R.SupportGate m p q → R.ExecR m p q c outR →
      ∃ outA, R.ExecA m p q c outA ∧ R.Coupled outA outR

/--
Unconditional reverse totality on faulting executions (Anneal to reference):
every faulting Anneal execution inside the gate has a choice-coupled reference
execution faulting with the same classification.
-/
def ReverseFaultTotal : Prop :=
  ∀ (m : Mode) (p : Prog) (q : Query) (c : Choice) (k : CorrFaultKind),
    R.SupportGate m p q → R.ExecA m p q c (.fault k) →
      R.ExecR m p q c (.fault k)

/--
Reverse totality across all valid executions (Anneal to reference): the
optional third totality condition of Section 4.6.
-/
def ReverseTotal : Prop :=
  ∀ (m : Mode) (p : Prog) (q : Query) (c : Choice)
    (outA : ExecOutcome4 RetA UnwA),
    R.SupportGate m p q → R.ExecA m p q c outA →
      ∃ outR, R.ExecR m p q c outR ∧ R.Coupled outA outR

/-- Reindex the modes of a step relation along `f`. -/
def liftMode {Mode' : Type uM'} (f : Mode' → Mode) :
    ModeParamStepRel Mode' Prog Query Choice RetA RetR UnwA UnwR where
  SupportGate := fun m => R.SupportGate (f m)
  ExecA := fun m => R.ExecA (f m)
  ExecR := fun m => R.ExecR (f m)
  RetRel := R.RetRel
  UnwRel := R.UnwRel

/-- Mode reindexing preserves `ProductiveAnneal`. -/
theorem liftMode_productiveAnneal {Mode' : Type uM'} (f : Mode' → Mode)
    (h : R.ProductiveAnneal) : (R.liftMode f).ProductiveAnneal :=
  fun m p q hg => h (f m) p q hg

/-- Mode reindexing preserves `ProductiveRef`. -/
theorem liftMode_productiveRef {Mode' : Type uM'} (f : Mode' → Mode)
    (h : R.ProductiveRef) : (R.liftMode f).ProductiveRef :=
  fun m p q hg => h (f m) p q hg

/--
Vertical composition of step relations through a middle model: Anneal model of
`R₁`, reference model of `R₂`, both gates, and composed payload relations.
-/
def comp {RetB : Type uRB} {UnwB : Type uUB}
    (R₁ : ModeParamStepRel Mode Prog Query Choice RetA RetB UnwA UnwB)
    (R₂ : ModeParamStepRel Mode Prog Query Choice RetB RetR UnwB UnwR) :
    ModeParamStepRel Mode Prog Query Choice RetA RetR UnwA UnwR where
  SupportGate := fun m p q => R₁.SupportGate m p q ∧ R₂.SupportGate m p q
  ExecA := R₁.ExecA
  ExecR := R₂.ExecR
  RetRel := RelComp R₁.RetRel R₂.RetRel
  UnwRel := RelComp R₁.UnwRel R₂.UnwRel

/--
Step relation of deterministic evaluators: each model has exactly the
execution computed by its evaluator.
-/
def ofEval (gate : Mode → Prog → Query → Prop)
    (evalA : Mode → Prog → Query → Choice → ExecOutcome4 RetA UnwA)
    (evalR : Mode → Prog → Query → Choice → ExecOutcome4 RetR UnwR)
    (RetRel : RetA → RetR → Prop) (UnwRel : UnwA → UnwR → Prop) :
    ModeParamStepRel Mode Prog Query Choice RetA RetR UnwA UnwR where
  SupportGate := gate
  ExecA := fun m p q c out => evalA m p q c = out
  ExecR := fun m p q c out => evalR m p q c = out
  RetRel := RetRel
  UnwRel := UnwRel

end ModeParamStepRel

/--
Correspondence claim (Section 4.6 and `docs/mir-correspondence-design.md`
Section 5.2): inside the gate, if the Anneal model is well-formed on `(p, q)`
then so is the reference model, and every reference execution has a
choice-coupled Anneal execution satisfying Cases 1–4 (behavioral inclusion of
the reference model in the Anneal model).
-/
def CorrespondenceClaim
    (R : ModeParamStepRel Mode Prog Query Choice RetA RetR UnwA UnwR) : Prop :=
  ∀ (m : Mode) (p : Prog) (q : Query),
    R.SupportGate m p q → R.WellFormedAnneal m p q →
      R.WellFormedRef m p q ∧
      ∀ (c : Choice) (outR : ExecOutcome4 RetR UnwR), R.ExecR m p q c outR →
        ∃ outA, R.ExecA m p q c outA ∧ R.Coupled outA outR

/--
Fault-equivalence claim: inside the gate, and without assuming
well-formedness, a fault with classification `k` is reachable in the Anneal
model exactly when it is reachable in the reference model.
-/
def FaultEquivClaim
    (R : ModeParamStepRel Mode Prog Query Choice RetA RetR UnwA UnwR) : Prop :=
  ∀ (m : Mode) (p : Prog) (q : Query) (k : CorrFaultKind),
    R.SupportGate m p q →
      ((∃ c, R.ExecA m p q c (.fault k)) ↔ (∃ c, R.ExecR m p q c (.fault k)))

/--
Exact behavioral equality on `(m, p, q)` up to the payload relations: along
every shared choice, each outcome class is reachable in one model exactly when
it is reachable in the other, with related payloads.
-/
structure ExactBehaviorEq
    (R : ModeParamStepRel Mode Prog Query Choice RetA RetR UnwA UnwR)
    (m : Mode) (p : Prog) (q : Query) : Prop where
  /-- Faults agree with identical classification. -/
  fault_iff : ∀ (c : Choice) (k : CorrFaultKind),
    R.ExecA m p q c (.fault k) ↔ R.ExecR m p q c (.fault k)
  /-- Every normal Anneal return has a related normal reference return. -/
  normal_anneal_to_ref : ∀ (c : Choice) (a : RetA),
    R.ExecA m p q c (.normal a) →
      ∃ r, R.ExecR m p q c (.normal r) ∧ R.RetRel a r
  /-- Every normal reference return has a related normal Anneal return. -/
  normal_ref_to_anneal : ∀ (c : Choice) (r : RetR),
    R.ExecR m p q c (.normal r) →
      ∃ a, R.ExecA m p q c (.normal a) ∧ R.RetRel a r
  /-- Every Anneal unwind has a related reference unwind. -/
  unwind_anneal_to_ref : ∀ (c : Choice) (a : UnwA),
    R.ExecA m p q c (.unwind a) →
      ∃ u, R.ExecR m p q c (.unwind u) ∧ R.UnwRel a u
  /-- Every reference unwind has a related Anneal unwind. -/
  unwind_ref_to_anneal : ∀ (c : Choice) (u : UnwR),
    R.ExecR m p q c (.unwind u) →
      ∃ a, R.ExecA m p q c (.unwind a) ∧ R.UnwRel a u
  /-- Divergence agrees. -/
  diverge_iff : ∀ c : Choice,
    R.ExecA m p q c .diverge ↔ R.ExecR m p q c .diverge

/--
Mode-indexed, choice-coupled step simulation between an Anneal model and a
reference model: the unconditional combined contract of
`docs/mir-correspondence-strategy.md` Section 4.6.

- `forward_total`: unconditional forward totality (reference to Anneal across
  all valid executions, faulting and non-faulting) inside the gate;
- `reverse_fault_total`: unconditional reverse totality on faulting executions
  (Anneal to reference) inside the gate;
- `reverse_total?`: optional reverse totality on all executions, present when
  it has been established (for example when both models are deterministic).
-/
structure ModeStepSim
    (R : ModeParamStepRel Mode Prog Query Choice RetA RetR UnwA UnwR) where
  /-- Every gated reference execution has a coupled Anneal execution. -/
  forward_total : R.ForwardTotal
  /-- Every gated faulting Anneal execution has a coupled reference fault. -/
  reverse_fault_total : R.ReverseFaultTotal
  /-- Optional reverse totality across all valid Anneal executions. -/
  reverse_total? : Option (PLift R.ReverseTotal) := none

namespace ModeStepSim

variable {R : ModeParamStepRel Mode Prog Query Choice RetA RetR UnwA UnwR}

/-- A step simulation proves the correspondence claim. -/
theorem correspondenceClaim (S : ModeStepSim R) : CorrespondenceClaim R := by
  intro m p q hg hwf
  refine ⟨?_, fun c outR hR => S.forward_total m p q c outR hg hR⟩
  intro c k hR
  obtain ⟨outA, hA, hc⟩ := S.forward_total m p q c (.fault k) hg hR
  have hk : outA = .fault k := (hc.fault_iff k).mpr rfl
  rw [hk] at hA
  exact hwf c k hA

/-- A step simulation proves the fault-equivalence claim. -/
theorem faultEquivClaim (S : ModeStepSim R) : FaultEquivClaim R := by
  intro m p q k hg
  constructor
  · intro ⟨c, hA⟩
    exact ⟨c, S.reverse_fault_total m p q c k hg hA⟩
  · intro ⟨c, hR⟩
    obtain ⟨outA, hA, hc⟩ := S.forward_total m p q c (.fault k) hg hR
    have hk : outA = .fault k := (hc.fault_iff k).mpr rfl
    rw [hk] at hA
    exact ⟨c, hA⟩

/--
Per-choice fault equivalence: along every shared choice, the Anneal model
faults with classification `k` exactly when the reference model does. This is
stronger than `FaultEquivClaim`, which only relates reachability.
-/
theorem fault_iff_at_choice (S : ModeStepSim R) {m : Mode} {p : Prog}
    {q : Query} (hg : R.SupportGate m p q) (c : Choice) (k : CorrFaultKind) :
    R.ExecA m p q c (.fault k) ↔ R.ExecR m p q c (.fault k) := by
  constructor
  · exact S.reverse_fault_total m p q c k hg
  · intro hR
    obtain ⟨outA, hA, hc⟩ := S.forward_total m p q c (.fault k) hg hR
    have hk : outA = .fault k := (hc.fault_iff k).mpr rfl
    rw [hk] at hA
    exact hA

/--
With reverse totality across all valid executions, a step simulation yields
exact behavioral equality on every gated `(m, p, q)`, including
mixed-faulting inputs.
-/
theorem exactBehaviorEq_of_reverseTotal (S : ModeStepSim R)
    (hrev : R.ReverseTotal) {m : Mode} {p : Prog} {q : Query}
    (hg : R.SupportGate m p q) : ExactBehaviorEq R m p q where
  fault_iff := S.fault_iff_at_choice hg
  normal_anneal_to_ref := fun c a hA => by
    obtain ⟨outR, hR, hc⟩ := hrev m p q c (.normal a) hg hA
    obtain ⟨r, hr, hrel⟩ := hc.normal_anneal_to_ref a rfl
    rw [hr] at hR
    exact ⟨r, hR, hrel⟩
  normal_ref_to_anneal := fun c r hR => by
    obtain ⟨outA, hA, hc⟩ := S.forward_total m p q c (.normal r) hg hR
    obtain ⟨a, ha, hrel⟩ := hc.normal_ref_to_anneal r rfl
    rw [ha] at hA
    exact ⟨a, hA, hrel⟩
  unwind_anneal_to_ref := fun c a hA => by
    obtain ⟨outR, hR, hc⟩ := hrev m p q c (.unwind a) hg hA
    obtain ⟨u, hu, hrel⟩ := hc.unwind_anneal_to_ref a rfl
    rw [hu] at hR
    exact ⟨u, hR, hrel⟩
  unwind_ref_to_anneal := fun c u hR => by
    obtain ⟨outA, hA, hc⟩ := S.forward_total m p q c (.unwind u) hg hR
    obtain ⟨a, ha, hrel⟩ := hc.unwind_ref_to_anneal u rfl
    rw [ha] at hA
    exact ⟨a, hA, hrel⟩
  diverge_iff := fun c => by
    constructor
    · intro hA
      obtain ⟨outR, hR, hc⟩ := hrev m p q c .diverge hg hA
      have hd : outR = .diverge := hc.diverge_anneal_to_ref rfl
      rw [hd] at hR
      exact hR
    · intro hR
      obtain ⟨outA, hA, hc⟩ := S.forward_total m p q c .diverge hg hR
      have hd : outA = .diverge := hc.diverge_ref_to_anneal rfl
      rw [hd] at hA
      exact hA

/--
Exact behavioral equality from the simulation's own recorded reverse totality
(`reverse_total? = some _`).
-/
theorem exactBehaviorEq_of_reverseTotal? (S : ModeStepSim R)
    {h : PLift R.ReverseTotal} (_hrev : S.reverse_total? = some h) {m : Mode}
    {p : Prog} {q : Query} (hg : R.SupportGate m p q) :
    ExactBehaviorEq R m p q :=
  S.exactBehaviorEq_of_reverseTotal h.down hg

/--
Exact behavioral equality directly from `S.reverse_total?.isSome = true`,
without first unpacking the `PLift` witness.
-/
theorem exactBehaviorEq_of_reverseTotal_isSome (S : ModeStepSim R)
    (hrev : S.reverse_total?.isSome = true) {m : Mode} {p : Prog} {q : Query}
    (hg : R.SupportGate m p q) : ExactBehaviorEq R m p q := by
  cases h : S.reverse_total? with
  | none =>
    rw [h] at hrev
    cases hrev
  | some pf => exact S.exactBehaviorEq_of_reverseTotal pf.down hg

/--
Vertical composition of step simulations through a middle model. `hmid`
states that the reference model of `R₁` and the Anneal model of `R₂` are the
same middle model.
-/
def comp {RetB : Type uRB} {UnwB : Type uUB}
    {R₁ : ModeParamStepRel Mode Prog Query Choice RetA RetB UnwA UnwB}
    {R₂ : ModeParamStepRel Mode Prog Query Choice RetB RetR UnwB UnwR}
    (S₁ : ModeStepSim R₁) (S₂ : ModeStepSim R₂)
    (hmid : ∀ m p q c out, R₁.ExecR m p q c out ↔ R₂.ExecA m p q c out) :
    ModeStepSim (R₁.comp R₂) where
  forward_total := fun m p q c outR hg hR => by
    obtain ⟨outB, hB, hBR⟩ := S₂.forward_total m p q c outR hg.2 hR
    obtain ⟨outA, hA, hAB⟩ :=
      S₁.forward_total m p q c outB hg.1 ((hmid m p q c outB).mpr hB)
    exact ⟨outA, hA, hAB.trans hBR⟩
  reverse_fault_total := fun m p q c k hg hA =>
    S₂.reverse_fault_total m p q c k hg.2
      ((hmid m p q c (.fault k)).mp (S₁.reverse_fault_total m p q c k hg.1 hA))
  reverse_total? :=
    match S₁.reverse_total?, S₂.reverse_total? with
    | some h₁, some h₂ =>
      some ⟨fun m p q c outA hg hA => by
        obtain ⟨outB, hB, hAB⟩ := h₁.down m p q c outA hg.1 hA
        obtain ⟨outR, hR, hBR⟩ :=
          h₂.down m p q c outB hg.2 ((hmid m p q c outB).mp hB)
        exact ⟨outR, hR, hAB.trans hBR⟩⟩
    | _, _ => none

/-- Reindex the modes of a step simulation along `f`. -/
def liftMode {Mode' : Type uM'} (S : ModeStepSim R) (f : Mode' → Mode) :
    ModeStepSim (R.liftMode f) where
  forward_total := fun m p q c outR hg hR =>
    S.forward_total (f m) p q c outR hg hR
  reverse_fault_total := fun m p q c k hg hA =>
    S.reverse_fault_total (f m) p q c k hg hA
  reverse_total? :=
    match S.reverse_total? with
    | some h => some ⟨fun m p q c outA hg hA => h.down (f m) p q c outA hg hA⟩
    | none => none

/--
Lift deterministic evaluators directly into a step simulation: if the
evaluators' outcomes are coupled on every gated input and choice, then all
three totality conditions hold, including reverse totality.
-/
def fromDeterministicEval (gate : Mode → Prog → Query → Prop)
    (evalA : Mode → Prog → Query → Choice → ExecOutcome4 RetA UnwA)
    (evalR : Mode → Prog → Query → Choice → ExecOutcome4 RetR UnwR)
    (RetRel : RetA → RetR → Prop) (UnwRel : UnwA → UnwR → Prop)
    (h : ∀ m p q c, gate m p q →
      ChoiceCoupledOutcomeRel RetRel UnwRel (evalA m p q c) (evalR m p q c)) :
    ModeStepSim (ModeParamStepRel.ofEval gate evalA evalR RetRel UnwRel) where
  forward_total := fun m p q c outR hg hR =>
    ⟨evalA m p q c, rfl, by
      have hR' : evalR m p q c = outR := hR
      rw [← hR']
      exact h m p q c hg⟩
  reverse_fault_total := fun m p q c k hg hA =>
    ((h m p q c hg).fault_iff k).mp hA
  reverse_total? :=
    some ⟨fun m p q c outA hg hA =>
      ⟨evalR m p q c, rfl, by
        have hA' : evalA m p q c = outA := hA
        rw [← hA']
        exact h m p q c hg⟩⟩

/-- The deterministic lift records reverse totality. -/
theorem fromDeterministicEval_reverse_total?_isSome
    (gate : Mode → Prog → Query → Prop)
    (evalA : Mode → Prog → Query → Choice → ExecOutcome4 RetA UnwA)
    (evalR : Mode → Prog → Query → Choice → ExecOutcome4 RetR UnwR)
    (RetRel : RetA → RetR → Prop) (UnwRel : UnwA → UnwR → Prop)
    (h : ∀ m p q c, gate m p q →
      ChoiceCoupledOutcomeRel RetRel UnwRel (evalA m p q c) (evalR m p q c)) :
    (fromDeterministicEval gate evalA evalR RetRel UnwRel
      h).reverse_total?.isSome = true := rfl

/--
Forward totality transfers productivity from the reference model to the Anneal
model: if no gated reference input is silently stuck, no gated Anneal input is
silently stuck.
-/
theorem productiveAnneal_of_productiveRef (S : ModeStepSim R)
    (hprod : R.ProductiveRef) : R.ProductiveAnneal := by
  intro m p q hg
  obtain ⟨c, outR, hR⟩ := hprod m p q hg
  obtain ⟨outA, hA, _⟩ := S.forward_total m p q c outR hg hR
  exact ⟨c, outA, hA⟩

/--
Reverse totality transfers productivity from the Anneal model to the reference
model.
-/
theorem productiveRef_of_reverseTotal (_S : ModeStepSim R)
    (hrev : R.ReverseTotal) (hprod : R.ProductiveAnneal) : R.ProductiveRef := by
  intro m p q hg
  obtain ⟨c, outA, hA⟩ := hprod m p q hg
  obtain ⟨outR, hR, _⟩ := hrev m p q c outA hg hA
  exact ⟨c, outR, hR⟩

end ModeStepSim

/-! ## 4. Witnesses and non-vacuity guards -/

/--
Positive witness: an input `(m, p, q)` inside the gate on which the Anneal
model is well-formed, together with a choice `c` along which both models
return normally with related values. It shows that `WellFormedAnneal` is
inhabited inside the gate, so `CorrespondenceClaim` is not vacuous.
-/
structure PositiveWitness
    (R : ModeParamStepRel Mode Prog Query Choice RetA RetR UnwA UnwR) where
  /-- Witness mode. -/
  m : Mode
  /-- Witness program. -/
  p : Prog
  /-- Witness query. -/
  q : Query
  /-- Witness choice trace. -/
  c : Choice
  /-- The witness input is inside the gate. -/
  gate : R.SupportGate m p q
  /-- The Anneal model is well-formed on the witness input. -/
  wf : R.WellFormedAnneal m p q
  /-- Both models return normally along `c`, with related values. -/
  agree : ∃ (retA : RetA) (retR : RetR),
    R.ExecA m p q c (.normal retA) ∧ R.ExecR m p q c (.normal retR) ∧
      R.RetRel retA retR

/--
Fault-equivalence witness: an input inside the gate and a choice along which
both models fault with the same classification `kind`.
-/
structure FaultEquivWitness
    (R : ModeParamStepRel Mode Prog Query Choice RetA RetR UnwA UnwR) where
  /-- Witness mode. -/
  m : Mode
  /-- Witness program. -/
  p : Prog
  /-- Witness query. -/
  q : Query
  /-- Witness choice trace. -/
  c : Choice
  /-- Fault classification of the witness trace. -/
  kind : CorrFaultKind
  /-- The witness input is inside the gate. -/
  gate : R.SupportGate m p q
  /-- The Anneal model faults with `kind` along `c`. -/
  execA : R.ExecA m p q c (.fault kind)
  /-- The reference model faults with `kind` along `c`. -/
  execR : R.ExecR m p q c (.fault kind)

/--
Mode-sensitivity witness: a fixed input `(p, q)` inside the gate at both modes
`m₁` and `m₂`, and coupled outcomes reachable at `m₁` that are unreachable at
`m₂` along every choice, in both models. Changing the mode therefore flips the
coupled behavior (for example a deterministic versus nondeterministic NaN
payload mode, or a basic-memory versus Tree Borrows machine mode).
-/
structure ModeSensitivityWitness
    (R : ModeParamStepRel Mode Prog Query Choice RetA RetR UnwA UnwR) where
  /-- Mode at which the witness outcomes are reachable. -/
  m₁ : Mode
  /-- Mode at which the witness outcomes are unreachable. -/
  m₂ : Mode
  /-- Witness program. -/
  p : Prog
  /-- Witness query. -/
  q : Query
  /-- Witness choice trace at `m₁`. -/
  c : Choice
  /-- The witness input is inside the gate at `m₁`. -/
  gate₁ : R.SupportGate m₁ p q
  /-- The witness input is inside the gate at `m₂`. -/
  gate₂ : R.SupportGate m₂ p q
  /-- Coupled outcomes reachable at `m₁` and unreachable at `m₂`. -/
  flips : ∃ (outA : ExecOutcome4 RetA UnwA) (outR : ExecOutcome4 RetR UnwR),
    R.ExecA m₁ p q c outA ∧ R.ExecR m₁ p q c outR ∧ R.Coupled outA outR ∧
      (∀ c', ¬ R.ExecA m₂ p q c' outA) ∧ (∀ c', ¬ R.ExecR m₂ p q c' outR)

/--
Flip-direction witness: a genuine polarity flip of the well-formedness verdict
inside the gate at one mode `m`. On `(pOk, qOk)` both models are well-formed
and return normally with related values; on `(pFault, qFault)` both models
fault with the same classification. An optional `ModeSensitivityWitness`
records that the behavior also depends on the mode.
-/
structure FlipDirectionWitness
    (R : ModeParamStepRel Mode Prog Query Choice RetA RetR UnwA UnwR) where
  /-- Mode shared by the two inputs. -/
  m : Mode
  /-- Normally returning program. -/
  pOk : Prog
  /-- Normally returning query. -/
  qOk : Query
  /-- Choice trace of the normal return. -/
  cOk : Choice
  /-- Faulting program. -/
  pFault : Prog
  /-- Faulting query. -/
  qFault : Query
  /-- Choice trace of the fault. -/
  cFault : Choice
  /-- Fault classification on the faulting input. -/
  kind : CorrFaultKind
  /-- The normally returning input is inside the gate. -/
  gateOk : R.SupportGate m pOk qOk
  /-- The faulting input is inside the gate. -/
  gateFault : R.SupportGate m pFault qFault
  /-- Both models return normally on `(pOk, qOk)` with related values. -/
  okAgree : ∃ (retA : RetA) (retR : RetR),
    R.ExecA m pOk qOk cOk (.normal retA) ∧
      R.ExecR m pOk qOk cOk (.normal retR) ∧ R.RetRel retA retR
  /-- The Anneal model never faults on `(pOk, qOk)`. -/
  wfOkA : R.WellFormedAnneal m pOk qOk
  /-- The reference model never faults on `(pOk, qOk)`. -/
  wfOkR : R.WellFormedRef m pOk qOk
  /-- The Anneal model faults on `(pFault, qFault)`. -/
  faultA : R.ExecA m pFault qFault cFault (.fault kind)
  /-- The reference model faults on `(pFault, qFault)`. -/
  faultR : R.ExecR m pFault qFault cFault (.fault kind)
  /-- Optional evidence that behavior also depends on the mode. -/
  modeSensitivity? : Option (ModeSensitivityWitness R) := none

/-- Alias of `FlipDirectionWitness` emphasizing its role as a CI guard. -/
abbrev FlipDirectionGuard
    (R : ModeParamStepRel Mode Prog Query Choice RetA RetR UnwA UnwR) :=
  FlipDirectionWitness R

namespace PositiveWitness

variable {R : ModeParamStepRel Mode Prog Query Choice RetA RetR UnwA UnwR}

/-- Positive witness from explicit agreeing return values. -/
def ofReturns (m : Mode) (p : Prog) (q : Query) (c : Choice) (retA : RetA)
    (retR : RetR) (gate : R.SupportGate m p q) (wf : R.WellFormedAnneal m p q)
    (execA : R.ExecA m p q c (.normal retA))
    (execR : R.ExecR m p q c (.normal retR)) (rel : R.RetRel retA retR) :
    PositiveWitness R :=
  { m := m, p := p, q := q, c := c, gate := gate, wf := wf,
    agree := ⟨retA, retR, execA, execR, rel⟩ }

/-- Under a step simulation, the reference model is well-formed at a positive
witness. -/
theorem wellFormedRef (w : PositiveWitness R) (S : ModeStepSim R) :
    R.WellFormedRef w.m w.p w.q :=
  (S.correspondenceClaim w.m w.p w.q w.gate w.wf).1

/-- A positive witness inhabits the antecedent of `CorrespondenceClaim`. -/
theorem antecedent_inhabited (w : PositiveWitness R) :
    ∃ m p q, R.SupportGate m p q ∧ R.WellFormedAnneal m p q :=
  ⟨w.m, w.p, w.q, w.gate, w.wf⟩

/--
Transport a positive witness along a mode reindexing `f` using a single
preimage `m'` of `w.m` (no global section required).
-/
def liftModeAt {Mode' : Type uM'} (w : PositiveWitness R) (f : Mode' → Mode)
    (m' : Mode') (hm : f m' = w.m) : PositiveWitness (R.liftMode f) where
  m := m'
  p := w.p
  q := w.q
  c := w.c
  gate := by
    show R.SupportGate (f m') w.p w.q
    rw [hm]
    exact w.gate
  wf := by
    show R.WellFormedAnneal (f m') w.p w.q
    rw [hm]
    exact w.wf
  agree := by
    show ∃ (retA : RetA) (retR : RetR),
      R.ExecA (f m') w.p w.q w.c (.normal retA) ∧
        R.ExecR (f m') w.p w.q w.c (.normal retR) ∧ R.RetRel retA retR
    rw [hm]
    exact w.agree

/-- Transport a positive witness along a mode reindexing with a section. -/
def liftMode {Mode' : Type uM'} (w : PositiveWitness R) (f : Mode' → Mode)
    (g : Mode → Mode') (hfg : ∀ m, f (g m) = m) :
    PositiveWitness (R.liftMode f) :=
  w.liftModeAt f (g w.m) (hfg w.m)

/--
Transport a positive witness of `R₂` to the vertical composition `R₁.comp R₂`
along a front simulation `S₁`: forward totality of `S₁` supplies the normal
execution of the new Anneal model, and reverse fault totality of `S₁` supplies
its well-formedness.
-/
def compFront {RetB : Type uRB} {UnwB : Type uUB}
    {R₁ : ModeParamStepRel Mode Prog Query Choice RetA RetB UnwA UnwB}
    {R₂ : ModeParamStepRel Mode Prog Query Choice RetB RetR UnwB UnwR}
    (w : PositiveWitness R₂) (S₁ : ModeStepSim R₁)
    (hmid : ∀ m p q c out, R₁.ExecR m p q c out ↔ R₂.ExecA m p q c out)
    (hgate : ∀ m p q, R₂.SupportGate m p q → R₁.SupportGate m p q) :
    PositiveWitness (R₁.comp R₂) where
  m := w.m
  p := w.p
  q := w.q
  c := w.c
  gate := ⟨hgate _ _ _ w.gate, w.gate⟩
  wf := fun c k hA =>
    w.wf c k ((hmid _ _ _ c (.fault k)).mp
      (S₁.reverse_fault_total _ _ _ c k (hgate _ _ _ w.gate) hA))
  agree := by
    obtain ⟨b, r, hB, hR, hbr⟩ := w.agree
    obtain ⟨outA, hA, hc⟩ :=
      S₁.forward_total _ _ _ w.c (.normal b) (hgate _ _ _ w.gate)
        ((hmid _ _ _ w.c (.normal b)).mpr hB)
    obtain ⟨a, ha, hab⟩ := hc.normal_ref_to_anneal b rfl
    rw [ha] at hA
    exact ⟨a, r, hA, hR, b, hab, hbr⟩

end PositiveWitness

namespace FaultEquivWitness

variable {R : ModeParamStepRel Mode Prog Query Choice RetA RetR UnwA UnwR}

/-- A fault witness refutes well-formedness of both models at its input. -/
theorem not_wellFormed (w : FaultEquivWitness R) :
    ¬ R.WellFormedAnneal w.m w.p w.q ∧ ¬ R.WellFormedRef w.m w.p w.q :=
  ⟨fun h => h w.c w.kind w.execA, fun h => h w.c w.kind w.execR⟩

/--
Transport a fault witness along a mode reindexing `f` using a single preimage
`m'` of `w.m` (no global section required).
-/
def liftModeAt {Mode' : Type uM'} (w : FaultEquivWitness R) (f : Mode' → Mode)
    (m' : Mode') (hm : f m' = w.m) : FaultEquivWitness (R.liftMode f) where
  m := m'
  p := w.p
  q := w.q
  c := w.c
  kind := w.kind
  gate := by
    show R.SupportGate (f m') w.p w.q
    rw [hm]
    exact w.gate
  execA := by
    show R.ExecA (f m') w.p w.q w.c (.fault w.kind)
    rw [hm]
    exact w.execA
  execR := by
    show R.ExecR (f m') w.p w.q w.c (.fault w.kind)
    rw [hm]
    exact w.execR

/-- Transport a fault witness along a mode reindexing with a section. -/
def liftMode {Mode' : Type uM'} (w : FaultEquivWitness R) (f : Mode' → Mode)
    (g : Mode → Mode') (hfg : ∀ m, f (g m) = m) :
    FaultEquivWitness (R.liftMode f) :=
  w.liftModeAt f (g w.m) (hfg w.m)

/--
Transport a fault witness of `R₂` to the vertical composition `R₁.comp R₂`
along a front simulation `S₁` (forward totality and Case 1 of `S₁`).
-/
def compFront {RetB : Type uRB} {UnwB : Type uUB}
    {R₁ : ModeParamStepRel Mode Prog Query Choice RetA RetB UnwA UnwB}
    {R₂ : ModeParamStepRel Mode Prog Query Choice RetB RetR UnwB UnwR}
    (w : FaultEquivWitness R₂) (S₁ : ModeStepSim R₁)
    (hmid : ∀ m p q c out, R₁.ExecR m p q c out ↔ R₂.ExecA m p q c out)
    (hgate : ∀ m p q, R₂.SupportGate m p q → R₁.SupportGate m p q) :
    FaultEquivWitness (R₁.comp R₂) where
  m := w.m
  p := w.p
  q := w.q
  c := w.c
  kind := w.kind
  gate := ⟨hgate _ _ _ w.gate, w.gate⟩
  execA :=
    (S₁.fault_iff_at_choice (hgate _ _ _ w.gate) w.c w.kind).mpr
      ((hmid _ _ _ w.c (.fault w.kind)).mpr w.execA)
  execR := w.execR

end FaultEquivWitness

namespace ModeSensitivityWitness

variable {R : ModeParamStepRel Mode Prog Query Choice RetA RetR UnwA UnwR}

/-- The two modes of a mode-sensitivity witness are distinct. -/
theorem mode_ne (w : ModeSensitivityWitness R) : w.m₁ ≠ w.m₂ := by
  intro h
  obtain ⟨outA, _, hA, _, _, hnA, _⟩ := w.flips
  exact hnA w.c (h ▸ hA)

/--
Neither model is mode-blind: it is false that every outcome reachable at one
mode is reachable at every other mode.
-/
theorem not_mode_invariant (w : ModeSensitivityWitness R) :
    (¬ ∀ m m' p q c out, R.ExecA m p q c out → ∃ c', R.ExecA m' p q c' out) ∧
    (¬ ∀ m m' p q c out, R.ExecR m p q c out → ∃ c', R.ExecR m' p q c' out) :=
    by
  obtain ⟨outA, outR, hA, hR, _, hnA, hnR⟩ := w.flips
  constructor
  · intro h
    obtain ⟨c', hA'⟩ := h w.m₁ w.m₂ w.p w.q w.c outA hA
    exact hnA c' hA'
  · intro h
    obtain ⟨c', hR'⟩ := h w.m₁ w.m₂ w.p w.q w.c outR hR
    exact hnR c' hR'

/--
Transport a mode-sensitivity witness along a mode reindexing `f` using
preimages `m₁'` and `m₂'` of `w.m₁` and `w.m₂` (no global section required).
-/
def liftModeAt {Mode' : Type uM'} (w : ModeSensitivityWitness R)
    (f : Mode' → Mode) (m₁' m₂' : Mode') (h₁ : f m₁' = w.m₁)
    (h₂ : f m₂' = w.m₂) : ModeSensitivityWitness (R.liftMode f) where
  m₁ := m₁'
  m₂ := m₂'
  p := w.p
  q := w.q
  c := w.c
  gate₁ := by
    show R.SupportGate (f m₁') w.p w.q
    rw [h₁]
    exact w.gate₁
  gate₂ := by
    show R.SupportGate (f m₂') w.p w.q
    rw [h₂]
    exact w.gate₂
  flips := by
    show ∃ (outA : ExecOutcome4 RetA UnwA) (outR : ExecOutcome4 RetR UnwR),
      R.ExecA (f m₁') w.p w.q w.c outA ∧
        R.ExecR (f m₁') w.p w.q w.c outR ∧ R.Coupled outA outR ∧
        (∀ c', ¬ R.ExecA (f m₂') w.p w.q c' outA) ∧
        (∀ c', ¬ R.ExecR (f m₂') w.p w.q c' outR)
    rw [h₁, h₂]
    exact w.flips

/-- Transport a mode-sensitivity witness along a mode reindexing with a
section. -/
def liftMode {Mode' : Type uM'} (w : ModeSensitivityWitness R)
    (f : Mode' → Mode) (g : Mode → Mode') (hfg : ∀ m, f (g m) = m) :
    ModeSensitivityWitness (R.liftMode f) :=
  w.liftModeAt f (g w.m₁) (g w.m₂) (hfg w.m₁) (hfg w.m₂)

/--
Unconditionally transport a fault-flipping mode-sensitivity witness of `R₂`
across a front simulation `S₁`: Case 1 and reverse fault totality preserve
fault reachability and unreachability without requiring full `ReverseTotal`.
-/
def compFrontOfFault {RetB : Type uRB} {UnwB : Type uUB}
    {R₁ : ModeParamStepRel Mode Prog Query Choice RetA RetB UnwA UnwB}
    {R₂ : ModeParamStepRel Mode Prog Query Choice RetB RetR UnwB UnwR}
    (w : ModeSensitivityWitness R₂) (S₁ : ModeStepSim R₁)
    (hmid : ∀ m p q c out, R₁.ExecR m p q c out ↔ R₂.ExecA m p q c out)
    (hgate : ∀ m p q, R₂.SupportGate m p q → R₁.SupportGate m p q)
    (hfault : ∃ k : CorrFaultKind,
      R₂.ExecA w.m₁ w.p w.q w.c (.fault k) ∧
      R₂.ExecR w.m₁ w.p w.q w.c (.fault k) ∧
      (∀ c', ¬ R₂.ExecA w.m₂ w.p w.q c' (.fault k)) ∧
      (∀ c', ¬ R₂.ExecR w.m₂ w.p w.q c' (.fault k))) :
    ModeSensitivityWitness (R₁.comp R₂) where
  m₁ := w.m₁
  m₂ := w.m₂
  p := w.p
  q := w.q
  c := w.c
  gate₁ := ⟨hgate _ _ _ w.gate₁, w.gate₁⟩
  gate₂ := ⟨hgate _ _ _ w.gate₂, w.gate₂⟩
  flips := by
    obtain ⟨k, hA₁, hR₁, hnA₂, hnR₂⟩ := hfault
    refine ⟨.fault k, .fault k,
      (S₁.fault_iff_at_choice (hgate _ _ _ w.gate₁) w.c k).mpr
        ((hmid _ _ _ w.c (.fault k)).mpr hA₁),
      hR₁, ChoiceCoupledOutcomeRel.ofFault k, ?_, hnR₂⟩
    intro c' hA₂
    exact hnA₂ c' ((hmid _ _ _ c' (.fault k)).mp
      (S₁.reverse_fault_total _ _ _ c' k (hgate _ _ _ w.gate₂) hA₂))

/--
Transport any mode-sensitivity witness of `R₂` (covering all four outcome
classes) across a front simulation `S₁` that has `ReverseTotal` and functional
payload relations (for example induced by a `CodecLaws`).
-/
def compFrontOfReverseTotal {RetB : Type uRB} {UnwB : Type uUB}
    {R₁ : ModeParamStepRel Mode Prog Query Choice RetA RetB UnwA UnwB}
    {R₂ : ModeParamStepRel Mode Prog Query Choice RetB RetR UnwB UnwR}
    (w : ModeSensitivityWitness R₂) (S₁ : ModeStepSim R₁)
    (hrev₁ : R₁.ReverseTotal)
    (hmid : ∀ m p q c out, R₁.ExecR m p q c out ↔ R₂.ExecA m p q c out)
    (hgate : ∀ m p q, R₂.SupportGate m p q → R₁.SupportGate m p q)
    (hRetFun : ∀ a b₁ b₂, R₁.RetRel a b₁ → R₁.RetRel a b₂ → b₁ = b₂)
    (hUnwFun : ∀ a u₁ u₂, R₁.UnwRel a u₁ → R₁.UnwRel a u₂ → u₁ = u₂) :
    ModeSensitivityWitness (R₁.comp R₂) where
  m₁ := w.m₁
  m₂ := w.m₂
  p := w.p
  q := w.q
  c := w.c
  gate₁ := ⟨hgate _ _ _ w.gate₁, w.gate₁⟩
  gate₂ := ⟨hgate _ _ _ w.gate₂, w.gate₂⟩
  flips := by
    obtain ⟨outB, outR, hB₁, hR₁, hBR, hnB₂, hnR₂⟩ := w.flips
    obtain ⟨outA, hA₁, hAB⟩ :=
      S₁.forward_total _ _ _ w.c outB (hgate _ _ _ w.gate₁)
        ((hmid _ _ _ w.c outB).mpr hB₁)
    refine ⟨outA, outR, hA₁, hR₁, hAB.trans hBR, ?_, hnR₂⟩
    intro c' hA₂
    obtain ⟨outB', hB₂', hAB'⟩ :=
      hrev₁ _ _ _ c' outA (hgate _ _ _ w.gate₂) hA₂
    have heq : outB' = outB := by
      cases outA with
      | normal a =>
        obtain ⟨b, hb, hab⟩ := hAB.normal_anneal_to_ref a rfl
        obtain ⟨b', hb', hab'⟩ := hAB'.normal_anneal_to_ref a rfl
        rw [hb, hb', hRetFun a b' b hab' hab]
      | unwind a =>
        obtain ⟨u, hu, hau⟩ := hAB.unwind_anneal_to_ref a rfl
        obtain ⟨u', hu', hau'⟩ := hAB'.unwind_anneal_to_ref a rfl
        rw [hu, hu', hUnwFun a u' u hau' hau]
      | fault k =>
        rw [(hAB.fault_iff k).mp rfl, (hAB'.fault_iff k).mp rfl]
      | diverge =>
        rw [hAB.diverge_anneal_to_ref rfl, hAB'.diverge_anneal_to_ref rfl]
    rw [heq] at hB₂'
    exact hnB₂ c' ((hmid _ _ _ c' outB).mp hB₂')

/-- Whether a `ModeSensitivityWitness` flips on a fault outcome (reachable at
`w.m₁` along `w.c`, unreachable at `w.m₂` along every choice). -/
def IsFaultFlip (w : ModeSensitivityWitness R) : Prop :=
  ∃ (outA : ExecOutcome4 RetA UnwA) (outR : ExecOutcome4 RetR UnwR),
    R.ExecA w.m₁ w.p w.q w.c outA ∧ R.ExecR w.m₁ w.p w.q w.c outR ∧
      R.Coupled outA outR ∧
      (∀ c', ¬ R.ExecA w.m₂ w.p w.q c' outA) ∧
      (∀ c', ¬ R.ExecR w.m₂ w.p w.q c' outR) ∧
      ∃ k : CorrFaultKind, outA = .fault k

/--
Transport a fault-flipping `ModeSensitivityWitness` across ANY front simulation
`S₁` without requiring `ReverseTotal` or functional payload relations, using `w`
directly via `IsFaultFlip`.
-/
def compFrontOfFaultFlip {RetB : Type uRB} {UnwB : Type uUB}
    {R₁ : ModeParamStepRel Mode Prog Query Choice RetA RetB UnwA UnwB}
    {R₂ : ModeParamStepRel Mode Prog Query Choice RetB RetR UnwB UnwR}
    (w : ModeSensitivityWitness R₂) (hw : w.IsFaultFlip) (S₁ : ModeStepSim R₁)
    (hmid : ∀ m p q c out, R₁.ExecR m p q c out ↔ R₂.ExecA m p q c out)
    (hgate : ∀ m p q, R₂.SupportGate m p q → R₁.SupportGate m p q) :
    ModeSensitivityWitness (R₁.comp R₂) :=
  w.compFrontOfFault S₁ hmid hgate (by
    obtain ⟨outB, outR, hB₁, hR₁, hBR, hnB₂, hnR₂, k, hk⟩ := hw
    have hkR : outR = .fault k := (hBR.fault_iff k).mp hk
    rw [hk] at hB₁ hnB₂
    rw [hkR] at hR₁ hnR₂
    exact ⟨k, hB₁, hR₁, hnB₂, hnR₂⟩)

end ModeSensitivityWitness

namespace FlipDirectionWitness

variable {R : ModeParamStepRel Mode Prog Query Choice RetA RetR UnwA UnwR}

/--
Build a flip-direction witness from a positive witness and a fault witness at
the same mode, with an optional mode-sensitivity witness. The step simulation
supplies well-formedness of the reference model on the positive input.
-/
def ofFaultAndMode (S : ModeStepSim R) (pos : PositiveWitness R)
    (flt : FaultEquivWitness R) (hm : flt.m = pos.m)
    (mode? : Option (ModeSensitivityWitness R) := none) :
    FlipDirectionWitness R where
  m := pos.m
  pOk := pos.p
  qOk := pos.q
  cOk := pos.c
  pFault := flt.p
  qFault := flt.q
  cFault := flt.c
  kind := flt.kind
  gateOk := pos.gate
  gateFault := hm ▸ flt.gate
  okAgree := pos.agree
  wfOkA := pos.wf
  wfOkR := pos.wellFormedRef S
  faultA := hm ▸ flt.execA
  faultR := hm ▸ flt.execR
  modeSensitivity? := mode?

/-- `ofFaultAndMode` records exactly the supplied mode-sensitivity witness. -/
theorem ofFaultAndMode_modeSensitivity? (S : ModeStepSim R)
    (pos : PositiveWitness R) (flt : FaultEquivWitness R) (hm : flt.m = pos.m)
    (mode? : Option (ModeSensitivityWitness R)) :
    (ofFaultAndMode S pos flt hm mode?).modeSensitivity? = mode? := rfl

/-- The positive half of a flip-direction witness. -/
def toPositive (w : FlipDirectionWitness R) : PositiveWitness R where
  m := w.m
  p := w.pOk
  q := w.qOk
  c := w.cOk
  gate := w.gateOk
  wf := w.wfOkA
  agree := w.okAgree

/-- The faulting half of a flip-direction witness. -/
def toFault (w : FlipDirectionWitness R) : FaultEquivWitness R where
  m := w.m
  p := w.pFault
  q := w.qFault
  c := w.cFault
  kind := w.kind
  gate := w.gateFault
  execA := w.faultA
  execR := w.faultR

/--
**Non-vacuity.** Inside the gate, neither the Anneal model nor the reference
model is vacuously all-normal or all-faulting: each has a faulting execution
(so not every gated execution returns normally) and a normally returning
execution (so not every gated execution faults).
-/
theorem not_constant_outcome (w : FlipDirectionWitness R) :
    (¬ ∀ m p q c out, R.SupportGate m p q → R.ExecA m p q c out →
        ∃ a, out = .normal a) ∧
    (¬ ∀ m p q c out, R.SupportGate m p q → R.ExecA m p q c out →
        ∃ k, out = .fault k) ∧
    (¬ ∀ m p q c out, R.SupportGate m p q → R.ExecR m p q c out →
        ∃ r, out = .normal r) ∧
    (¬ ∀ m p q c out, R.SupportGate m p q → R.ExecR m p q c out →
        ∃ k, out = .fault k) := by
  obtain ⟨retA, retR, hA, hR, _⟩ := w.okAgree
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    obtain ⟨a, ha⟩ := h w.m w.pFault w.qFault w.cFault _ w.gateFault w.faultA
    cases ha
  · intro h
    obtain ⟨k, hk⟩ := h w.m w.pOk w.qOk w.cOk _ w.gateOk hA
    cases hk
  · intro h
    obtain ⟨r, hr⟩ := h w.m w.pFault w.qFault w.cFault _ w.gateFault w.faultR
    cases hr
  · intro h
    obtain ⟨k, hk⟩ := h w.m w.pOk w.qOk w.cOk _ w.gateOk hR
    cases hk

/--
**Polarity flip.** The well-formedness verdict genuinely flips between the two
inputs in both models: it holds on `(pOk, qOk)` and fails on
`(pFault, qFault)`.
-/
theorem verdict_flips (w : FlipDirectionWitness R) :
    (R.WellFormedAnneal w.m w.pOk w.qOk ∧
      ¬ R.WellFormedAnneal w.m w.pFault w.qFault) ∧
    (R.WellFormedRef w.m w.pOk w.qOk ∧
      ¬ R.WellFormedRef w.m w.pFault w.qFault) :=
  ⟨⟨w.wfOkA, fun h => h w.cFault w.kind w.faultA⟩,
   ⟨w.wfOkR, fun h => h w.cFault w.kind w.faultR⟩⟩

/-- The two inputs of a flip-direction witness are distinct. -/
theorem inputs_ne (w : FlipDirectionWitness R) :
    ¬ (w.pOk = w.pFault ∧ w.qOk = w.qFault) := by
  intro ⟨hp, hq⟩
  have hf := w.faultA
  rw [← hp, ← hq] at hf
  exact w.wfOkA w.cFault w.kind hf

/--
Neither model ignores its input: no single outcome class verdict is shared by
all gated inputs at mode `w.m`.
-/
theorem not_input_invariant (w : FlipDirectionWitness R) :
    (¬ ∀ p q p' q', R.WellFormedAnneal w.m p q → R.WellFormedAnneal w.m p' q') ∧
    (¬ ∀ p q p' q', R.WellFormedRef w.m p q → R.WellFormedRef w.m p' q') :=
  ⟨fun h => w.verdict_flips.1.2 (h _ _ _ _ w.wfOkA),
   fun h => w.verdict_flips.2.2 (h _ _ _ _ w.wfOkR)⟩

/--
Transport a flip-direction witness along a mode reindexing `f` using a single
preimage `m'` of `w.m` (no global section required).
-/
def liftModeAt {Mode' : Type uM'} (w : FlipDirectionWitness R)
    (f : Mode' → Mode) (m' : Mode') (hm : f m' = w.m)
    (mode? : Option (ModeSensitivityWitness (R.liftMode f)) := none) :
    FlipDirectionWitness (R.liftMode f) where
  m := m'
  pOk := w.pOk
  qOk := w.qOk
  cOk := w.cOk
  pFault := w.pFault
  qFault := w.qFault
  cFault := w.cFault
  kind := w.kind
  gateOk := (w.toPositive.liftModeAt f m' hm).gate
  gateFault := (w.toFault.liftModeAt f m' hm).gate
  okAgree := (w.toPositive.liftModeAt f m' hm).agree
  wfOkA := (w.toPositive.liftModeAt f m' hm).wf
  wfOkR := by
    show R.WellFormedRef (f m') w.pOk w.qOk
    rw [hm]
    exact w.wfOkR
  faultA := (w.toFault.liftModeAt f m' hm).execA
  faultR := (w.toFault.liftModeAt f m' hm).execR
  modeSensitivity? := mode?

/-- Transport a flip-direction witness along a mode reindexing with a
section. -/
def liftMode {Mode' : Type uM'} (w : FlipDirectionWitness R) (f : Mode' → Mode)
    (g : Mode → Mode') (hfg : ∀ m, f (g m) = m) :
    FlipDirectionWitness (R.liftMode f) :=
  w.liftModeAt f (g w.m) (hfg w.m)
    (w.modeSensitivity?.map fun ms => ms.liftMode f g hfg)

/--
Transport a flip-direction witness of `R₂` to the vertical composition
`R₁.comp R₂` along a front simulation `S₁`. Mode sensitivity is a property of
the composed models and is supplied separately (`mode?`).
-/
def compFront {RetB : Type uRB} {UnwB : Type uUB}
    {R₁ : ModeParamStepRel Mode Prog Query Choice RetA RetB UnwA UnwB}
    {R₂ : ModeParamStepRel Mode Prog Query Choice RetB RetR UnwB UnwR}
    (w : FlipDirectionWitness R₂) (S₁ : ModeStepSim R₁)
    (hmid : ∀ m p q c out, R₁.ExecR m p q c out ↔ R₂.ExecA m p q c out)
    (hgate : ∀ m p q, R₂.SupportGate m p q → R₁.SupportGate m p q)
    (mode? : Option (ModeSensitivityWitness (R₁.comp R₂)) := none) :
    FlipDirectionWitness (R₁.comp R₂) where
  m := w.m
  pOk := w.pOk
  qOk := w.qOk
  cOk := w.cOk
  pFault := w.pFault
  qFault := w.qFault
  cFault := w.cFault
  kind := w.kind
  gateOk := (w.toPositive.compFront S₁ hmid hgate).gate
  gateFault := (w.toFault.compFront S₁ hmid hgate).gate
  okAgree := (w.toPositive.compFront S₁ hmid hgate).agree
  wfOkA := (w.toPositive.compFront S₁ hmid hgate).wf
  wfOkR := w.wfOkR
  faultA := (w.toFault.compFront S₁ hmid hgate).execA
  faultR := w.faultR
  modeSensitivity? := mode?

end FlipDirectionWitness

end StepRel


/-! ## 5. Dual-authority correspondence bundles -/

universe uMA uRep uMM uCM uRM uUM uML uCL uRL uUL uMX uRX uUX uMM' uML'

/--
Dual-authority correspondence bundle: one Anneal model related to the two
reference authorities `MiniRust` (`MR`) and `LeanMiri` (`LM`).

The bundle packages the four parts of the correspondence abstraction:

1. `codec`: the lawful codec from Anneal return values to a shared
   representation `Rep`, with `repMR` / `repLM` projecting each authority's
   return values to `Rep` and `mr_ret_codec` / `lm_ret_codec` tying each
   payload relation to the codec;
2. `mrSim` / `lmSim`: mode-indexed choice-coupled step simulations of the
   Anneal model against each authority, over authority-specific mode, choice,
   return, and unwind types;
3. `mrPositive` / `lmPositive` / `mrFault` / `lmFault`: paired positive and
   fault-equivalence witnesses;
4. `mrFlip` / `lmFlip`: flip-direction guards (with optional mode
   sensitivity).

Both simulations observe the same Anneal model: `toAnnealMR` / `toAnnealLM`
map each authority's modes to Anneal modes, and `anneal_exec_coherent` states
that the Anneal executions of each simulation are exactly the executions
`ExecAnneal` of the Anneal model at the mapped mode.
-/
structure DualCorrespondenceBundle (ModeA : Type uMA) (Prog : Type uP)
    (Query : Type uQ) (RetA : Type uRA) (UnwA : Type uUA) (Rep : Type uRep)
    (ModeMR : Type uMM) (ChoiceMR : Type uCM) (RetMR : Type uRM)
    (UnwMR : Type uUM) (ModeLM : Type uML) (ChoiceLM : Type uCL)
    (RetLM : Type uRL) (UnwLM : Type uUL) where
  /-- Codec from Anneal return values to the shared representation. -/
  codec : CodecLaws RetA Rep
  /-- Shared representation of a `MiniRust` return value. -/
  repMR : RetMR → Rep
  /-- Shared representation of a `LeanMiri` return value. -/
  repLM : RetLM → Rep
  /-- Step relation of the Anneal model against `MiniRust`. -/
  mrRel : ModeParamStepRel ModeMR Prog Query ChoiceMR RetA RetMR UnwA UnwMR
  /-- Step relation of the Anneal model against `LeanMiri`. -/
  lmRel : ModeParamStepRel ModeLM Prog Query ChoiceLM RetA RetLM UnwA UnwLM
  /-- Step simulation against `MiniRust`. -/
  mrSim : ModeStepSim mrRel
  /-- Step simulation against `LeanMiri`. -/
  lmSim : ModeStepSim lmRel
  /-- Related `MiniRust` returns have the codec encoding as representation. -/
  mr_ret_codec : ∀ a r, mrRel.RetRel a r → repMR r = codec.encode a
  /-- Related `LeanMiri` returns have the codec encoding as representation. -/
  lm_ret_codec : ∀ a r, lmRel.RetRel a r → repLM r = codec.encode a
  /-- Anneal mode matched with a `MiniRust` mode. -/
  toAnnealMR : ModeMR → ModeA
  /-- Anneal mode matched with a `LeanMiri` mode. -/
  toAnnealLM : ModeLM → ModeA
  /-- Complete executions of the single Anneal model. -/
  ExecAnneal : ModeA → Prog → Query → ExecOutcome4 RetA UnwA → Prop
  /-- Both simulations observe exactly the executions of the Anneal model. -/
  anneal_exec_coherent :
    (∀ m p q out,
      (∃ c, mrRel.ExecA m p q c out) ↔ ExecAnneal (toAnnealMR m) p q out) ∧
    (∀ m p q out,
      (∃ c, lmRel.ExecA m p q c out) ↔ ExecAnneal (toAnnealLM m) p q out)
  /-- Positive witness against `MiniRust`. -/
  mrPositive : PositiveWitness mrRel
  /-- Positive witness against `LeanMiri`. -/
  lmPositive : PositiveWitness lmRel
  /-- Fault-equivalence witness against `MiniRust`. -/
  mrFault : FaultEquivWitness mrRel
  /-- Fault-equivalence witness against `LeanMiri`. -/
  lmFault : FaultEquivWitness lmRel
  /-- Flip-direction guard against `MiniRust`. -/
  mrFlip : FlipDirectionWitness mrRel
  /-- Flip-direction guard against `LeanMiri`. -/
  lmFlip : FlipDirectionWitness lmRel

namespace ModeParamStepRel

variable {ModeA : Type uMA} {Mode : Type uM} {Prog : Type uP} {Query : Type uQ}
variable {Choice : Type uC} {RetA : Type uRA} {RetR : Type uRR}
variable {UnwA : Type uUA} {UnwR : Type uUR}

/--
Step relation of a deterministic, choice-independent Anneal evaluator `evalA`
(read at the Anneal mode `toAnneal m`) against a relational reference model
`ExecR`.
-/
def ofAnnealEval (toAnneal : Mode → ModeA) (gate : Mode → Prog → Query → Prop)
    (evalA : ModeA → Prog → Query → ExecOutcome4 RetA UnwA)
    (ExecR : Mode → Prog → Query → Choice → ExecOutcome4 RetR UnwR → Prop)
    (RetRel : RetA → RetR → Prop) (UnwRel : UnwA → UnwR → Prop) :
    ModeParamStepRel Mode Prog Query Choice RetA RetR UnwA UnwR where
  SupportGate := gate
  ExecA := fun m p q _ out => evalA (toAnneal m) p q = out
  ExecR := ExecR
  RetRel := RetRel
  UnwRel := UnwRel

/--
Choice-gated variant of `ofAnnealEval`: the deterministic Anneal evaluator
emits an execution only along choices admitted by `validChoice`, avoiding
vacuous fault-reflection obligations on invalid reference choices.
-/
def ofAnnealEvalGated (toAnneal : Mode → ModeA)
    (gate : Mode → Prog → Query → Prop)
    (validChoice : Mode → Prog → Query → Choice → Prop)
    (evalA : ModeA → Prog → Query → ExecOutcome4 RetA UnwA)
    (ExecR : Mode → Prog → Query → Choice → ExecOutcome4 RetR UnwR → Prop)
    (RetRel : RetA → RetR → Prop) (UnwRel : UnwA → UnwR → Prop) :
    ModeParamStepRel Mode Prog Query Choice RetA RetR UnwA UnwR where
  SupportGate := gate
  ExecA := fun m p q c out =>
    validChoice m p q c ∧ evalA (toAnneal m) p q = out
  ExecR := ExecR
  RetRel := RetRel
  UnwRel := UnwRel

/--
**Sharpness of choice productivity on `ofAnnealEvalGated` (Section 4.5).** If
`validChoice m p q` is uninhabited at an input, `ofAnnealEvalGated` has no
Anneal executions there and its `WellFormedAnneal` holds vacuously — even when
`evalA (toAnneal m) p q = .fault .undefined`! Safe bundle construction
(`fromEquivGated`) therefore requires `validChoice` to be inhabited.
-/
theorem ofAnnealEvalGated_vacuous_of_empty_choice (toAnneal : Mode → ModeA)
    (gate : Mode → Prog → Query → Prop)
    (validChoice : Mode → Prog → Query → Choice → Prop)
    (evalA : ModeA → Prog → Query → ExecOutcome4 RetA UnwA)
    (ExecR : Mode → Prog → Query → Choice → ExecOutcome4 RetR UnwR → Prop)
    (RetRel : RetA → RetR → Prop) (UnwRel : UnwA → UnwR → Prop)
    {m : Mode} {p : Prog} {q : Query}
    (hempty : ∀ c, ¬ validChoice m p q c) :
    (ofAnnealEvalGated toAnneal gate validChoice evalA ExecR RetRel
      UnwRel).WellFormedAnneal m p q :=
  fun c _ hA => hempty c hA.1

/--
When `validChoice m p q` is inhabited (`∃ c, validChoice m p q c`),
`ofAnnealEvalGated` is non-vacuous: `WellFormedAnneal m p q` holds iff `evalA`
does not fault, and `∃ c, ExecA m p q c out` coincides with `evalA = out`.
-/
theorem ofAnnealEvalGated_wellFormedAnneal_iff (toAnneal : Mode → ModeA)
    (gate : Mode → Prog → Query → Prop)
    (validChoice : Mode → Prog → Query → Choice → Prop)
    (evalA : ModeA → Prog → Query → ExecOutcome4 RetA UnwA)
    (ExecR : Mode → Prog → Query → Choice → ExecOutcome4 RetR UnwR → Prop)
    (RetRel : RetA → RetR → Prop) (UnwRel : UnwA → UnwR → Prop)
    {m : Mode} {p : Prog} {q : Query} (hinh : ∃ c, validChoice m p q c) :
    ((ofAnnealEvalGated toAnneal gate validChoice evalA ExecR RetRel
        UnwRel).WellFormedAnneal m p q ↔
      ∀ k, evalA (toAnneal m) p q ≠ .fault k) ∧
    (∀ out,
      (∃ c, (ofAnnealEvalGated toAnneal gate validChoice evalA ExecR RetRel
          UnwRel).ExecA m p q c out) ↔
        evalA (toAnneal m) p q = out) := by
  obtain ⟨c₀, hc₀⟩ := hinh
  exact ⟨⟨fun hwf k heq => hwf c₀ k ⟨hc₀, heq⟩,
          fun hnf _ k hA => hnf k hA.2⟩,
         fun _ => ⟨fun ⟨_, hA⟩ => hA.2, fun heq => ⟨c₀, hc₀, heq⟩⟩⟩

end ModeParamStepRel

namespace ModeStepSim

variable {ModeA : Type uMA} {Mode : Type uM} {Prog : Type uP} {Query : Type uQ}
variable {Choice : Type uC} {RetA : Type uRA} {RetR : Type uRR}
variable {UnwA : Type uUA} {UnwR : Type uUR}

/--
Step simulation of a deterministic Anneal evaluator against a relational
reference model, from an evaluation equivalence: every gated reference
execution is coupled with the Anneal evaluator's outcome (`fwd`), and every
Anneal fault is a reference fault along every choice (`rev`).
-/
def fromAnnealEval (toAnneal : Mode → ModeA)
    (gate : Mode → Prog → Query → Prop)
    (evalA : ModeA → Prog → Query → ExecOutcome4 RetA UnwA)
    (ExecR : Mode → Prog → Query → Choice → ExecOutcome4 RetR UnwR → Prop)
    (RetRel : RetA → RetR → Prop) (UnwRel : UnwA → UnwR → Prop)
    (fwd : ∀ m p q c out, gate m p q → ExecR m p q c out →
      ChoiceCoupledOutcomeRel RetRel UnwRel (evalA (toAnneal m) p q) out)
    (rev : ∀ m p q c k, gate m p q → evalA (toAnneal m) p q = .fault k →
      ExecR m p q c (.fault k))
    (revTotal? : Option (PLift
      (ModeParamStepRel.ofAnnealEval toAnneal gate evalA ExecR RetRel
        UnwRel).ReverseTotal) := none) :
    ModeStepSim
      (ModeParamStepRel.ofAnnealEval toAnneal gate evalA ExecR RetRel UnwRel)
    where
  forward_total := fun m p q c outR hg hR =>
    ⟨evalA (toAnneal m) p q, rfl, fwd m p q c outR hg hR⟩
  reverse_fault_total := fun m p q c k hg hA => rev m p q c k hg hA
  reverse_total? := revTotal?

/--
Choice-gated version of `fromAnnealEval`: fault reflection is required only on
choices satisfying `validChoice`, and forward totality certifies that every
reference execution uses a valid choice.
-/
def fromAnnealEvalGated (toAnneal : Mode → ModeA)
    (gate : Mode → Prog → Query → Prop)
    (validChoice : Mode → Prog → Query → Choice → Prop)
    (evalA : ModeA → Prog → Query → ExecOutcome4 RetA UnwA)
    (ExecR : Mode → Prog → Query → Choice → ExecOutcome4 RetR UnwR → Prop)
    (RetRel : RetA → RetR → Prop) (UnwRel : UnwA → UnwR → Prop)
    (fwd : ∀ m p q c out, gate m p q → ExecR m p q c out →
      validChoice m p q c ∧
      ChoiceCoupledOutcomeRel RetRel UnwRel (evalA (toAnneal m) p q) out)
    (rev : ∀ m p q c k, gate m p q → validChoice m p q c →
      evalA (toAnneal m) p q = .fault k → ExecR m p q c (.fault k))
    (revTotal? : Option (PLift
      (ModeParamStepRel.ofAnnealEvalGated toAnneal gate validChoice evalA ExecR
        RetRel UnwRel).ReverseTotal) := none) :
    ModeStepSim
      (ModeParamStepRel.ofAnnealEvalGated toAnneal gate validChoice evalA ExecR
        RetRel UnwRel) where
  forward_total := fun m p q c outR hg hR =>
    let ⟨hvc, hc⟩ := fwd m p q c outR hg hR
    ⟨evalA (toAnneal m) p q, ⟨hvc, rfl⟩, hc⟩
  reverse_fault_total := fun m p q c k hg hA => rev m p q c k hg hA.1 hA.2
  reverse_total? := revTotal?

end ModeStepSim

namespace PositiveWitness

variable {ModeA : Type uMA} {Mode : Type uM} {Prog : Type uP} {Query : Type uQ}
variable {Choice : Type uC} {RetA : Type uRA} {RetR : Type uRR}
variable {UnwA : Type uUA} {UnwR : Type uUR}

/--
Positive witness against a deterministic Anneal evaluator: a normal Anneal
evaluation is automatically well-formed.
-/
def ofAnnealEval {toAnneal : Mode → ModeA} {gate : Mode → Prog → Query → Prop}
    {evalA : ModeA → Prog → Query → ExecOutcome4 RetA UnwA}
    {ExecR : Mode → Prog → Query → Choice → ExecOutcome4 RetR UnwR → Prop}
    {RetRel : RetA → RetR → Prop} {UnwRel : UnwA → UnwR → Prop}
    (m : Mode) (p : Prog) (q : Query) (c : Choice) (retA : RetA) (retR : RetR)
    (hg : gate m p q) (hA : evalA (toAnneal m) p q = .normal retA)
    (hR : ExecR m p q c (.normal retR)) (hrel : RetRel retA retR) :
    PositiveWitness
      (ModeParamStepRel.ofAnnealEval toAnneal gate evalA ExecR RetRel UnwRel)
    where
  m := m
  p := p
  q := q
  c := c
  gate := hg
  wf := fun _ k hk => by
    have hk' : evalA (toAnneal m) p q = .fault k := hk
    rw [hA] at hk'
    cases hk'
  agree := ⟨retA, retR, hA, hR, hrel⟩

/-- Positive witness against a choice-gated deterministic Anneal evaluator. -/
def ofAnnealEvalGated {toAnneal : Mode → ModeA}
    {gate : Mode → Prog → Query → Prop}
    {validChoice : Mode → Prog → Query → Choice → Prop}
    {evalA : ModeA → Prog → Query → ExecOutcome4 RetA UnwA}
    {ExecR : Mode → Prog → Query → Choice → ExecOutcome4 RetR UnwR → Prop}
    {RetRel : RetA → RetR → Prop} {UnwRel : UnwA → UnwR → Prop}
    (m : Mode) (p : Prog) (q : Query) (c : Choice) (retA : RetA) (retR : RetR)
    (hg : gate m p q) (hvc : validChoice m p q c)
    (hA : evalA (toAnneal m) p q = .normal retA)
    (hR : ExecR m p q c (.normal retR)) (hrel : RetRel retA retR) :
    PositiveWitness
      (ModeParamStepRel.ofAnnealEvalGated toAnneal gate validChoice evalA ExecR
        RetRel UnwRel) where
  m := m
  p := p
  q := q
  c := c
  gate := hg
  wf := fun _ k hk => by
    have hk' : evalA (toAnneal m) p q = .fault k := hk.2
    rw [hA] at hk'
    cases hk'
  agree := ⟨retA, retR, ⟨hvc, hA⟩, hR, hrel⟩

end PositiveWitness

namespace FaultEquivWitness

variable {ModeA : Type uMA} {Mode : Type uM} {Prog : Type uP} {Query : Type uQ}
variable {Choice : Type uC} {RetA : Type uRA} {RetR : Type uRR}
variable {UnwA : Type uUA} {UnwR : Type uUR}

/-- Fault witness against a deterministic Anneal evaluator. -/
def ofAnnealEval {toAnneal : Mode → ModeA} {gate : Mode → Prog → Query → Prop}
    {evalA : ModeA → Prog → Query → ExecOutcome4 RetA UnwA}
    {ExecR : Mode → Prog → Query → Choice → ExecOutcome4 RetR UnwR → Prop}
    {RetRel : RetA → RetR → Prop} {UnwRel : UnwA → UnwR → Prop}
    (m : Mode) (p : Prog) (q : Query) (c : Choice) (kind : CorrFaultKind)
    (hg : gate m p q) (hA : evalA (toAnneal m) p q = .fault kind)
    (hR : ExecR m p q c (.fault kind)) :
    FaultEquivWitness
      (ModeParamStepRel.ofAnnealEval toAnneal gate evalA ExecR RetRel UnwRel)
    where
  m := m
  p := p
  q := q
  c := c
  kind := kind
  gate := hg
  execA := hA
  execR := hR

/-- Fault witness against a choice-gated deterministic Anneal evaluator. -/
def ofAnnealEvalGated {toAnneal : Mode → ModeA}
    {gate : Mode → Prog → Query → Prop}
    {validChoice : Mode → Prog → Query → Choice → Prop}
    {evalA : ModeA → Prog → Query → ExecOutcome4 RetA UnwA}
    {ExecR : Mode → Prog → Query → Choice → ExecOutcome4 RetR UnwR → Prop}
    {RetRel : RetA → RetR → Prop} {UnwRel : UnwA → UnwR → Prop}
    (m : Mode) (p : Prog) (q : Query) (c : Choice) (kind : CorrFaultKind)
    (hg : gate m p q) (hvc : validChoice m p q c)
    (hA : evalA (toAnneal m) p q = .fault kind)
    (hR : ExecR m p q c (.fault kind)) :
    FaultEquivWitness
      (ModeParamStepRel.ofAnnealEvalGated toAnneal gate validChoice evalA ExecR
        RetRel UnwRel) where
  m := m
  p := p
  q := q
  c := c
  kind := kind
  gate := hg
  execA := ⟨hvc, hA⟩
  execR := hR

end FaultEquivWitness

namespace DualCorrespondenceBundle

variable {ModeA : Type uMA} {Prog : Type uP} {Query : Type uQ}
variable {RetA : Type uRA} {UnwA : Type uUA} {Rep : Type uRep}
variable {ModeMR : Type uMM} {ChoiceMR : Type uCM} {RetMR : Type uRM}
variable {UnwMR : Type uUM} {ModeLM : Type uML} {ChoiceLM : Type uCL}
variable {RetLM : Type uRL} {UnwLM : Type uUL}

/--
Project the positive witnesses to the single Anneal model: at each
authority's witness input, the Anneal model (at the matched Anneal mode)
returns normally and never faults, the authority returns normally with a
related value, and that value's representation is the codec encoding of the
Anneal value.
-/
theorem projectPositive
    (B : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM) :
    (∃ (a : RetA) (r : RetMR),
      B.ExecAnneal (B.toAnnealMR B.mrPositive.m) B.mrPositive.p B.mrPositive.q
        (.normal a) ∧
      B.mrRel.ExecR B.mrPositive.m B.mrPositive.p B.mrPositive.q B.mrPositive.c
        (.normal r) ∧
      B.mrRel.RetRel a r ∧ B.repMR r = B.codec.encode a ∧
      ∀ k, ¬ B.ExecAnneal (B.toAnnealMR B.mrPositive.m) B.mrPositive.p
        B.mrPositive.q (.fault k)) ∧
    (∃ (a : RetA) (r : RetLM),
      B.ExecAnneal (B.toAnnealLM B.lmPositive.m) B.lmPositive.p B.lmPositive.q
        (.normal a) ∧
      B.lmRel.ExecR B.lmPositive.m B.lmPositive.p B.lmPositive.q B.lmPositive.c
        (.normal r) ∧
      B.lmRel.RetRel a r ∧ B.repLM r = B.codec.encode a ∧
      ∀ k, ¬ B.ExecAnneal (B.toAnnealLM B.lmPositive.m) B.lmPositive.p
        B.lmPositive.q (.fault k)) := by
  constructor
  · obtain ⟨a, r, hA, hR, hrel⟩ := B.mrPositive.agree
    refine ⟨a, r, (B.anneal_exec_coherent.1 _ _ _ _).mp ⟨_, hA⟩, hR, hrel,
      B.mr_ret_codec a r hrel, ?_⟩
    intro k hk
    obtain ⟨c, hc⟩ := (B.anneal_exec_coherent.1 _ _ _ _).mpr hk
    exact B.mrPositive.wf c k hc
  · obtain ⟨a, r, hA, hR, hrel⟩ := B.lmPositive.agree
    refine ⟨a, r, (B.anneal_exec_coherent.2 _ _ _ _).mp ⟨_, hA⟩, hR, hrel,
      B.lm_ret_codec a r hrel, ?_⟩
    intro k hk
    obtain ⟨c, hc⟩ := (B.anneal_exec_coherent.2 _ _ _ _).mpr hk
    exact B.lmPositive.wf c k hc

/--
**Cross-authority fault equivalence.** At matched Anneal modes and on an input
inside both gates, `MiniRust` reaches a fault with classification `k` exactly
when `LeanMiri` does: both are equivalent to the single Anneal model reaching
that fault.
-/
theorem crossAuthorityFaultEquiv
    (B : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM)
    {mMR : ModeMR} {mLM : ModeLM} (hmode : B.toAnnealMR mMR = B.toAnnealLM mLM)
    {p : Prog} {q : Query} (hgMR : B.mrRel.SupportGate mMR p q)
    (hgLM : B.lmRel.SupportGate mLM p q) (k : CorrFaultKind) :
    (∃ c, B.mrRel.ExecR mMR p q c (.fault k)) ↔
      (∃ c, B.lmRel.ExecR mLM p q c (.fault k)) := by
  have hMR := B.mrSim.faultEquivClaim mMR p q k hgMR
  have hLM := B.lmSim.faultEquivClaim mLM p q k hgLM
  have cMR := B.anneal_exec_coherent.1 mMR p q (.fault k)
  have cLM := B.anneal_exec_coherent.2 mLM p q (.fault k)
  rw [hmode] at cMR
  exact hMR.symm.trans (cMR.trans (cLM.symm.trans hLM))

/--
Project the fault witnesses to the single Anneal model, together with
cross-authority fault equivalence: at each authority's fault witness the
Anneal model (at the matched Anneal mode) and the authority both fault with
the witness classification, and at matched Anneal modes `MiniRust` and
`LeanMiri` reach exactly the same fault classifications.
-/
theorem projectFault
    (B : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM) :
    (B.ExecAnneal (B.toAnnealMR B.mrFault.m) B.mrFault.p B.mrFault.q
        (.fault B.mrFault.kind) ∧
      B.mrRel.ExecR B.mrFault.m B.mrFault.p B.mrFault.q B.mrFault.c
        (.fault B.mrFault.kind)) ∧
    (B.ExecAnneal (B.toAnnealLM B.lmFault.m) B.lmFault.p B.lmFault.q
        (.fault B.lmFault.kind) ∧
      B.lmRel.ExecR B.lmFault.m B.lmFault.p B.lmFault.q B.lmFault.c
        (.fault B.lmFault.kind)) ∧
    (∀ (mMR : ModeMR) (mLM : ModeLM) (p : Prog) (q : Query) (k : CorrFaultKind),
      B.toAnnealMR mMR = B.toAnnealLM mLM → B.mrRel.SupportGate mMR p q →
      B.lmRel.SupportGate mLM p q →
        ((∃ c, B.mrRel.ExecR mMR p q c (.fault k)) ↔
          (∃ c, B.lmRel.ExecR mLM p q c (.fault k)))) :=
  ⟨⟨(B.anneal_exec_coherent.1 _ _ _ _).mp ⟨_, B.mrFault.execA⟩,
      B.mrFault.execR⟩,
   ⟨(B.anneal_exec_coherent.2 _ _ _ _).mp ⟨_, B.lmFault.execA⟩,
      B.lmFault.execR⟩,
   fun _ _ _ _ k hmode hgMR hgLM =>
     B.crossAuthorityFaultEquiv hmode hgMR hgLM k⟩

/--
**Three-way normal agreement.** At matched Anneal modes, if the Anneal model
is deterministic on `(toAnnealMR mMR, p, q)`, then any normal `MiniRust`
return and any normal `LeanMiri` return on `(p, q)` agree through one Anneal
return value `a`: both are related to `a`, and both have the codec encoding of
`a` as their shared representation.
-/
theorem threeWayNormalAgreement
    (B : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM)
    {mMR : ModeMR} {mLM : ModeLM} (hmode : B.toAnnealMR mMR = B.toAnnealLM mLM)
    {p : Prog} {q : Query} (hgMR : B.mrRel.SupportGate mMR p q)
    (hgLM : B.lmRel.SupportGate mLM p q)
    (hdet : ∀ out out', B.ExecAnneal (B.toAnnealMR mMR) p q out →
      B.ExecAnneal (B.toAnnealMR mMR) p q out' → out = out')
    {cMR : ChoiceMR} {rMR : RetMR}
    (hMR : B.mrRel.ExecR mMR p q cMR (.normal rMR))
    {cLM : ChoiceLM} {rLM : RetLM}
    (hLM : B.lmRel.ExecR mLM p q cLM (.normal rLM)) :
    ∃ a : RetA,
      B.ExecAnneal (B.toAnnealMR mMR) p q (.normal a) ∧
      B.mrRel.RetRel a rMR ∧ B.lmRel.RetRel a rLM ∧
      B.repMR rMR = B.codec.encode a ∧ B.repLM rLM = B.codec.encode a := by
  obtain ⟨outA, hA, hc⟩ :=
    B.mrSim.forward_total mMR p q cMR (.normal rMR) hgMR hMR
  obtain ⟨a, ha, hrel⟩ := hc.normal_ref_to_anneal rMR rfl
  rw [ha] at hA
  obtain ⟨outA', hA', hc'⟩ :=
    B.lmSim.forward_total mLM p q cLM (.normal rLM) hgLM hLM
  obtain ⟨a', ha', hrel'⟩ := hc'.normal_ref_to_anneal rLM rfl
  rw [ha'] at hA'
  have eA := (B.anneal_exec_coherent.1 mMR p q (.normal a)).mp ⟨cMR, hA⟩
  have eA' := (B.anneal_exec_coherent.2 mLM p q (.normal a')).mp ⟨cLM, hA'⟩
  rw [← hmode] at eA'
  have heq : ExecOutcome4.normal (Unw := UnwA) a = .normal a' := hdet _ _ eA eA'
  cases heq
  exact ⟨a, eA, hrel, hrel', B.mr_ret_codec a rMR hrel,
    B.lm_ret_codec a rLM hrel'⟩

/--
Under the hypotheses of `threeWayNormalAgreement`, normal `MiniRust` and
`LeanMiri` returns have the same shared representation, and it decodes to an
Anneal return value.
-/
theorem threeWayNormalAgreement_rep
    (B : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM)
    {mMR : ModeMR} {mLM : ModeLM} (hmode : B.toAnnealMR mMR = B.toAnnealLM mLM)
    {p : Prog} {q : Query} (hgMR : B.mrRel.SupportGate mMR p q)
    (hgLM : B.lmRel.SupportGate mLM p q)
    (hdet : ∀ out out', B.ExecAnneal (B.toAnnealMR mMR) p q out →
      B.ExecAnneal (B.toAnnealMR mMR) p q out' → out = out')
    {cMR : ChoiceMR} {rMR : RetMR}
    (hMR : B.mrRel.ExecR mMR p q cMR (.normal rMR))
    {cLM : ChoiceLM} {rLM : RetLM}
    (hLM : B.lmRel.ExecR mLM p q cLM (.normal rLM)) :
    B.repMR rMR = B.repLM rLM ∧
      ∃ a : RetA, B.codec.decode (B.repMR rMR) = some a ∧
        B.ExecAnneal (B.toAnnealMR mMR) p q (.normal a) := by
  obtain ⟨a, eA, _, _, hMRrep, hLMrep⟩ :=
    B.threeWayNormalAgreement hmode hgMR hgLM hdet hMR hLM
  refine ⟨hMRrep.trans hLMrep.symm, a, ?_, eA⟩
  rw [hMRrep]
  exact B.codec.decode_encode a

/--
Under the hypotheses of `threeWayNormalAgreement`, both authorities' shared
representations are canonical (`B.codec.ValidRep`).
-/
theorem threeWayNormalAgreement_validRep
    (B : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM)
    {mMR : ModeMR} {mLM : ModeLM} (hmode : B.toAnnealMR mMR = B.toAnnealLM mLM)
    {p : Prog} {q : Query} (hgMR : B.mrRel.SupportGate mMR p q)
    (hgLM : B.lmRel.SupportGate mLM p q)
    (hdet : ∀ out out', B.ExecAnneal (B.toAnnealMR mMR) p q out →
      B.ExecAnneal (B.toAnnealMR mMR) p q out' → out = out')
    {cMR : ChoiceMR} {rMR : RetMR}
    (hMR : B.mrRel.ExecR mMR p q cMR (.normal rMR))
    {cLM : ChoiceLM} {rLM : RetLM}
    (hLM : B.lmRel.ExecR mLM p q cLM (.normal rLM)) :
    B.codec.ValidRep (B.repMR rMR) ∧ B.codec.ValidRep (B.repLM rLM) := by
  obtain ⟨a, _, _, _, hMRrep, hLMrep⟩ :=
    B.threeWayNormalAgreement hmode hgMR hgLM hdet hMR hLM
  rw [hMRrep, hLMrep]
  exact ⟨B.codec.encode_valid a, B.codec.encode_valid a⟩

/--
**Three-way unwind agreement (Case 3).** At matched Anneal modes, if Anneal is
deterministic on `(toAnnealMR mMR, p, q)`, then any `MiniRust` unwind and any
`LeanMiri` unwind agree through one Anneal unwind payload `uA`.
-/
theorem threeWayUnwindAgreement
    (B : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM)
    {mMR : ModeMR} {mLM : ModeLM} (hmode : B.toAnnealMR mMR = B.toAnnealLM mLM)
    {p : Prog} {q : Query} (hgMR : B.mrRel.SupportGate mMR p q)
    (hgLM : B.lmRel.SupportGate mLM p q)
    (hdet : ∀ out out', B.ExecAnneal (B.toAnnealMR mMR) p q out →
      B.ExecAnneal (B.toAnnealMR mMR) p q out' → out = out')
    {cMR : ChoiceMR} {uMR : UnwMR}
    (hMR : B.mrRel.ExecR mMR p q cMR (.unwind uMR))
    {cLM : ChoiceLM} {uLM : UnwLM}
    (hLM : B.lmRel.ExecR mLM p q cLM (.unwind uLM)) :
    ∃ uA : UnwA,
      B.ExecAnneal (B.toAnnealMR mMR) p q (.unwind uA) ∧
      B.mrRel.UnwRel uA uMR ∧ B.lmRel.UnwRel uA uLM := by
  obtain ⟨outA, hA, hc⟩ :=
    B.mrSim.forward_total mMR p q cMR (.unwind uMR) hgMR hMR
  obtain ⟨uA, huA, hrelMR⟩ := hc.unwind_ref_to_anneal uMR rfl
  rw [huA] at hA
  obtain ⟨outA', hA', hc'⟩ :=
    B.lmSim.forward_total mLM p q cLM (.unwind uLM) hgLM hLM
  obtain ⟨uA', huA', hrelLM⟩ := hc'.unwind_ref_to_anneal uLM rfl
  rw [huA'] at hA'
  have eA := (B.anneal_exec_coherent.1 mMR p q (.unwind uA)).mp ⟨cMR, hA⟩
  have eA' := (B.anneal_exec_coherent.2 mLM p q (.unwind uA')).mp ⟨cLM, hA'⟩
  rw [← hmode] at eA'
  have heq :
      ExecOutcome4.unwind (Ret := RetA) uA = .unwind uA' := hdet _ _ eA eA'
  cases heq
  exact ⟨uA, eA, hrelMR, hrelLM⟩

/--
**Cross-authority divergence equivalence (Case 4).** At matched Anneal modes
inside both support gates, when both authority simulations have reverse
totality, `MiniRust` diverges iff the single Anneal model diverges iff
`LeanMiri` diverges.
-/
theorem crossAuthorityDivergeEquiv
    (B : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM)
    {mMR : ModeMR} {mLM : ModeLM} (hmode : B.toAnnealMR mMR = B.toAnnealLM mLM)
    {p : Prog} {q : Query} (hgMR : B.mrRel.SupportGate mMR p q)
    (hgLM : B.lmRel.SupportGate mLM p q)
    (hrevMR : B.mrRel.ReverseTotal) (hrevLM : B.lmRel.ReverseTotal) :
    ((∃ c, B.mrRel.ExecR mMR p q c .diverge) ↔
      B.ExecAnneal (B.toAnnealMR mMR) p q .diverge) ∧
    ((∃ c, B.lmRel.ExecR mLM p q c .diverge) ↔
      B.ExecAnneal (B.toAnnealLM mLM) p q .diverge) ∧
    ((∃ c, B.mrRel.ExecR mMR p q c .diverge) ↔
      (∃ c, B.lmRel.ExecR mLM p q c .diverge)) := by
  have eqMR := B.mrSim.exactBehaviorEq_of_reverseTotal hrevMR hgMR
  have eqLM := B.lmSim.exactBehaviorEq_of_reverseTotal hrevLM hgLM
  have hMR : (∃ c, B.mrRel.ExecR mMR p q c .diverge) ↔
      B.ExecAnneal (B.toAnnealMR mMR) p q .diverge := by
    constructor
    · intro ⟨c, hR⟩
      exact (B.anneal_exec_coherent.1 mMR p q .diverge).mp
        ⟨c, (eqMR.diverge_iff c).mpr hR⟩
    · intro hA
      obtain ⟨c, hA'⟩ := (B.anneal_exec_coherent.1 mMR p q .diverge).mpr hA
      exact ⟨c, (eqMR.diverge_iff c).mp hA'⟩
  have hLM : (∃ c, B.lmRel.ExecR mLM p q c .diverge) ↔
      B.ExecAnneal (B.toAnnealLM mLM) p q .diverge := by
    constructor
    · intro ⟨c, hR⟩
      exact (B.anneal_exec_coherent.2 mLM p q .diverge).mp
        ⟨c, (eqLM.diverge_iff c).mpr hR⟩
    · intro hA
      obtain ⟨c, hA'⟩ := (B.anneal_exec_coherent.2 mLM p q .diverge).mpr hA
      exact ⟨c, (eqLM.diverge_iff c).mp hA'⟩
  have hBoth : (∃ c, B.mrRel.ExecR mMR p q c .diverge) ↔
      (∃ c, B.lmRel.ExecR mLM p q c .diverge) := by
    rw [hMR, hLM, hmode]
  exact ⟨hMR, hLM, hBoth⟩

/--
**Cross-authority normal-outcome equivalence (Case 2, nondeterministic).** At
matched Anneal modes inside both support gates, when both authority simulations
have reverse totality (no determinism hypothesis `hdet` required!):
1. `MiniRust` reaches a normal return related to `a` iff `ExecAnneal` reaches
   `.normal a` iff `LeanMiri` reaches a normal return related to `a`;
2. Every normal `MiniRust` return `rMR` is matched by a normal `LeanMiri`
   return `rLM` with identical canonical shared representation
   `B.repMR rMR = B.repLM rLM` (and symmetrically `LeanMiri → MiniRust`).
-/
theorem crossAuthorityNormalEquiv
    (B : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM)
    {mMR : ModeMR} {mLM : ModeLM} (hmode : B.toAnnealMR mMR = B.toAnnealLM mLM)
    {p : Prog} {q : Query} (hgMR : B.mrRel.SupportGate mMR p q)
    (hgLM : B.lmRel.SupportGate mLM p q)
    (hrevMR : B.mrRel.ReverseTotal) (hrevLM : B.lmRel.ReverseTotal) :
    (∀ a : RetA,
      ((∃ c r, B.mrRel.ExecR mMR p q c (.normal r) ∧ B.mrRel.RetRel a r) ↔
        B.ExecAnneal (B.toAnnealMR mMR) p q (.normal a)) ∧
      ((∃ c r, B.lmRel.ExecR mLM p q c (.normal r) ∧ B.lmRel.RetRel a r) ↔
        B.ExecAnneal (B.toAnnealLM mLM) p q (.normal a)) ∧
      ((∃ c r, B.mrRel.ExecR mMR p q c (.normal r) ∧ B.mrRel.RetRel a r) ↔
        (∃ c r, B.lmRel.ExecR mLM p q c (.normal r) ∧ B.lmRel.RetRel a r))) ∧
    (∀ (cMR : ChoiceMR) (rMR : RetMR),
      B.mrRel.ExecR mMR p q cMR (.normal rMR) →
      ∃ (cLM : ChoiceLM) (rLM : RetLM),
        B.lmRel.ExecR mLM p q cLM (.normal rLM) ∧
        B.repMR rMR = B.repLM rLM ∧ B.codec.ValidRep (B.repMR rMR)) ∧
    (∀ (cLM : ChoiceLM) (rLM : RetLM),
      B.lmRel.ExecR mLM p q cLM (.normal rLM) →
      ∃ (cMR : ChoiceMR) (rMR : RetMR),
        B.mrRel.ExecR mMR p q cMR (.normal rMR) ∧
        B.repLM rLM = B.repMR rMR ∧ B.codec.ValidRep (B.repLM rLM)) := by
  have eqMR := B.mrSim.exactBehaviorEq_of_reverseTotal hrevMR hgMR
  have eqLM := B.lmSim.exactBehaviorEq_of_reverseTotal hrevLM hgLM
  have hMRAt : ∀ a : RetA,
      (∃ c r, B.mrRel.ExecR mMR p q c (.normal r) ∧ B.mrRel.RetRel a r) →
        B.ExecAnneal (B.toAnnealMR mMR) p q (.normal a) := by
    intro a ⟨c, r, hR, hrel⟩
    obtain ⟨a', hA', hrel'⟩ := eqMR.normal_ref_to_anneal c r hR
    have heq : B.codec.encode a = B.codec.encode a' :=
      (B.mr_ret_codec a r hrel).symm.trans (B.mr_ret_codec a' r hrel')
    have ha : a = a' := B.codec.encode_injective heq
    rw [← ha] at hA'
    exact (B.anneal_exec_coherent.1 mMR p q (.normal a)).mp ⟨c, hA'⟩
  have hAtMR : ∀ a : RetA,
      B.ExecAnneal (B.toAnnealMR mMR) p q (.normal a) →
        ∃ c r, B.mrRel.ExecR mMR p q c (.normal r) ∧ B.mrRel.RetRel a r := by
    intro a hA
    obtain ⟨c, hA'⟩ := (B.anneal_exec_coherent.1 mMR p q (.normal a)).mpr hA
    obtain ⟨r, hR, hrel⟩ := eqMR.normal_anneal_to_ref c a hA'
    exact ⟨c, r, hR, hrel⟩
  have hLMAt : ∀ a : RetA,
      (∃ c r, B.lmRel.ExecR mLM p q c (.normal r) ∧ B.lmRel.RetRel a r) →
        B.ExecAnneal (B.toAnnealLM mLM) p q (.normal a) := by
    intro a ⟨c, r, hR, hrel⟩
    obtain ⟨a', hA', hrel'⟩ := eqLM.normal_ref_to_anneal c r hR
    have heq : B.codec.encode a = B.codec.encode a' :=
      (B.lm_ret_codec a r hrel).symm.trans (B.lm_ret_codec a' r hrel')
    have ha : a = a' := B.codec.encode_injective heq
    rw [← ha] at hA'
    exact (B.anneal_exec_coherent.2 mLM p q (.normal a)).mp ⟨c, hA'⟩
  have hAtLM : ∀ a : RetA,
      B.ExecAnneal (B.toAnnealLM mLM) p q (.normal a) →
        ∃ c r, B.lmRel.ExecR mLM p q c (.normal r) ∧ B.lmRel.RetRel a r := by
    intro a hA
    obtain ⟨c, hA'⟩ := (B.anneal_exec_coherent.2 mLM p q (.normal a)).mpr hA
    obtain ⟨r, hR, hrel⟩ := eqLM.normal_anneal_to_ref c a hA'
    exact ⟨c, r, hR, hrel⟩
  refine ⟨fun a => ?_, ?_, ?_⟩
  · have iffMR :
        (∃ c r, B.mrRel.ExecR mMR p q c (.normal r) ∧ B.mrRel.RetRel a r) ↔
          B.ExecAnneal (B.toAnnealMR mMR) p q (.normal a) :=
      ⟨hMRAt a, hAtMR a⟩
    have iffLM :
        (∃ c r, B.lmRel.ExecR mLM p q c (.normal r) ∧ B.lmRel.RetRel a r) ↔
          B.ExecAnneal (B.toAnnealLM mLM) p q (.normal a) :=
      ⟨hLMAt a, hAtLM a⟩
    refine ⟨iffMR, iffLM, ?_⟩
    rw [iffMR, iffLM, hmode]
  · intro cMR rMR hR
    obtain ⟨a, hA, hrelMR⟩ := eqMR.normal_ref_to_anneal cMR rMR hR
    have eA := (B.anneal_exec_coherent.1 mMR p q (.normal a)).mp ⟨cMR, hA⟩
    rw [hmode] at eA
    obtain ⟨cLM, rLM, hRLM, hrelLM⟩ := hAtLM a eA
    have hrepMR := B.mr_ret_codec a rMR hrelMR
    have hrepLM := B.lm_ret_codec a rLM hrelLM
    exact ⟨cLM, rLM, hRLM, hrepMR.trans hrepLM.symm,
      hrepMR ▸ B.codec.encode_valid a⟩
  · intro cLM rLM hR
    obtain ⟨a, hA, hrelLM⟩ := eqLM.normal_ref_to_anneal cLM rLM hR
    have eA := (B.anneal_exec_coherent.2 mLM p q (.normal a)).mp ⟨cLM, hA⟩
    rw [← hmode] at eA
    obtain ⟨cMR, rMR, hRMR, hrelMR⟩ := hAtMR a eA
    have hrepMR := B.mr_ret_codec a rMR hrelMR
    have hrepLM := B.lm_ret_codec a rLM hrelLM
    exact ⟨cMR, rMR, hRMR, hrepLM.trans hrepMR.symm,
      hrepLM ▸ B.codec.encode_valid a⟩

/--
**Cross-authority unwind correspondence (Case 3, nondeterministic).** At
matched Anneal modes inside both support gates, when both authority simulations
have reverse totality (no determinism hypothesis `hdet` required!): every
`MiniRust` unwind payload `uMR` is matched through an Anneal unwind payload
`uA` by a `LeanMiri` unwind payload `uLM`, and symmetrically.
-/
theorem crossAuthorityUnwindEquiv
    (B : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM)
    {mMR : ModeMR} {mLM : ModeLM} (hmode : B.toAnnealMR mMR = B.toAnnealLM mLM)
    {p : Prog} {q : Query} (hgMR : B.mrRel.SupportGate mMR p q)
    (hgLM : B.lmRel.SupportGate mLM p q)
    (hrevMR : B.mrRel.ReverseTotal) (hrevLM : B.lmRel.ReverseTotal) :
    (∀ (cMR : ChoiceMR) (uMR : UnwMR),
      B.mrRel.ExecR mMR p q cMR (.unwind uMR) →
      ∃ (uA : UnwA) (cLM : ChoiceLM) (uLM : UnwLM),
        B.ExecAnneal (B.toAnnealMR mMR) p q (.unwind uA) ∧
        B.lmRel.ExecR mLM p q cLM (.unwind uLM) ∧
        B.mrRel.UnwRel uA uMR ∧ B.lmRel.UnwRel uA uLM) ∧
    (∀ (cLM : ChoiceLM) (uLM : UnwLM),
      B.lmRel.ExecR mLM p q cLM (.unwind uLM) →
      ∃ (uA : UnwA) (cMR : ChoiceMR) (uMR : UnwMR),
        B.ExecAnneal (B.toAnnealLM mLM) p q (.unwind uA) ∧
        B.mrRel.ExecR mMR p q cMR (.unwind uMR) ∧
        B.mrRel.UnwRel uA uMR ∧ B.lmRel.UnwRel uA uLM) := by
  have eqMR := B.mrSim.exactBehaviorEq_of_reverseTotal hrevMR hgMR
  have eqLM := B.lmSim.exactBehaviorEq_of_reverseTotal hrevLM hgLM
  constructor
  · intro cMR uMR hR
    obtain ⟨uA, hA, hrelMR⟩ := eqMR.unwind_ref_to_anneal cMR uMR hR
    have eA := (B.anneal_exec_coherent.1 mMR p q (.unwind uA)).mp ⟨cMR, hA⟩
    have eALM : B.ExecAnneal (B.toAnnealLM mLM) p q (.unwind uA) :=
      hmode ▸ eA
    obtain ⟨cLM, hALM⟩ :=
      (B.anneal_exec_coherent.2 mLM p q (.unwind uA)).mpr eALM
    obtain ⟨uLM, hRLM, hrelLM⟩ := eqLM.unwind_anneal_to_ref cLM uA hALM
    exact ⟨uA, cLM, uLM, eA, hRLM, hrelMR, hrelLM⟩
  · intro cLM uLM hR
    obtain ⟨uA, hA, hrelLM⟩ := eqLM.unwind_ref_to_anneal cLM uLM hR
    have eA := (B.anneal_exec_coherent.2 mLM p q (.unwind uA)).mp ⟨cLM, hA⟩
    have eAMR : B.ExecAnneal (B.toAnnealMR mMR) p q (.unwind uA) :=
      hmode.symm ▸ eA
    obtain ⟨cMR, hAMR⟩ :=
      (B.anneal_exec_coherent.1 mMR p q (.unwind uA)).mpr eAMR
    obtain ⟨uMR, hRMR, hrelMR⟩ := eqMR.unwind_anneal_to_ref cMR uA hAMR
    exact ⟨uA, cMR, uMR, eA, hRMR, hrelMR, hrelLM⟩

/--
**Cross-authority unwind equivalence (`↔`, Case 3).** When each authority's
unwind relation is left-injective (`uA` uniquely determined by the authority's
unwind payload), unwind reachability at every `uA : UnwA` agrees by `↔` across
`MiniRust`, `ExecAnneal`, and `LeanMiri` without requiring determinism.
-/
theorem crossAuthorityUnwindIff
    (B : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM)
    {mMR : ModeMR} {mLM : ModeLM} (hmode : B.toAnnealMR mMR = B.toAnnealLM mLM)
    {p : Prog} {q : Query} (hgMR : B.mrRel.SupportGate mMR p q)
    (hgLM : B.lmRel.SupportGate mLM p q)
    (hrevMR : B.mrRel.ReverseTotal) (hrevLM : B.lmRel.ReverseTotal)
    (hinjMR : ∀ u₁ u₂ uR,
      B.mrRel.UnwRel u₁ uR → B.mrRel.UnwRel u₂ uR → u₁ = u₂)
    (hinjLM : ∀ u₁ u₂ uR,
      B.lmRel.UnwRel u₁ uR → B.lmRel.UnwRel u₂ uR → u₁ = u₂) (uA : UnwA) :
    ((∃ c u, B.mrRel.ExecR mMR p q c (.unwind u) ∧ B.mrRel.UnwRel uA u) ↔
      B.ExecAnneal (B.toAnnealMR mMR) p q (.unwind uA)) ∧
    ((∃ c u, B.lmRel.ExecR mLM p q c (.unwind u) ∧ B.lmRel.UnwRel uA u) ↔
      B.ExecAnneal (B.toAnnealLM mLM) p q (.unwind uA)) ∧
    ((∃ c u, B.mrRel.ExecR mMR p q c (.unwind u) ∧ B.mrRel.UnwRel uA u) ↔
      (∃ c u, B.lmRel.ExecR mLM p q c (.unwind u) ∧ B.lmRel.UnwRel uA u)) := by
  have eqMR := B.mrSim.exactBehaviorEq_of_reverseTotal hrevMR hgMR
  have eqLM := B.lmSim.exactBehaviorEq_of_reverseTotal hrevLM hgLM
  have iffMR :
      (∃ c u, B.mrRel.ExecR mMR p q c (.unwind u) ∧ B.mrRel.UnwRel uA u) ↔
        B.ExecAnneal (B.toAnnealMR mMR) p q (.unwind uA) := by
    constructor
    · intro ⟨c, u, hR, hrel⟩
      obtain ⟨uA', hA', hrel'⟩ := eqMR.unwind_ref_to_anneal c u hR
      rw [hinjMR uA uA' u hrel hrel']
      exact (B.anneal_exec_coherent.1 mMR p q (.unwind uA')).mp ⟨c, hA'⟩
    · intro hA
      obtain ⟨c, hA'⟩ := (B.anneal_exec_coherent.1 mMR p q (.unwind uA)).mpr hA
      obtain ⟨u, hR, hrel⟩ := eqMR.unwind_anneal_to_ref c uA hA'
      exact ⟨c, u, hR, hrel⟩
  have iffLM :
      (∃ c u, B.lmRel.ExecR mLM p q c (.unwind u) ∧ B.lmRel.UnwRel uA u) ↔
        B.ExecAnneal (B.toAnnealLM mLM) p q (.unwind uA) := by
    constructor
    · intro ⟨c, u, hR, hrel⟩
      obtain ⟨uA', hA', hrel'⟩ := eqLM.unwind_ref_to_anneal c u hR
      rw [hinjLM uA uA' u hrel hrel']
      exact (B.anneal_exec_coherent.2 mLM p q (.unwind uA')).mp ⟨c, hA'⟩
    · intro hA
      obtain ⟨c, hA'⟩ := (B.anneal_exec_coherent.2 mLM p q (.unwind uA)).mpr hA
      obtain ⟨u, hR, hrel⟩ := eqLM.unwind_anneal_to_ref c uA hA'
      exact ⟨c, u, hR, hrel⟩
  refine ⟨iffMR, iffLM, ?_⟩
  rw [iffMR, iffLM, hmode]

/--
**Unified 4-way cross-authority exact equivalence (Cases 1–4,
nondeterministic).** Packages Cases 1 (`fault`), 2 (`normal`), 3 (`unwind`),
and 4 (`diverge`) at matched Anneal modes inside both gates under
`ReverseTotal` in a single theorem.
-/
theorem crossAuthorityExactEquiv
    (B : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM)
    {mMR : ModeMR} {mLM : ModeLM} (hmode : B.toAnnealMR mMR = B.toAnnealLM mLM)
    {p : Prog} {q : Query} (hgMR : B.mrRel.SupportGate mMR p q)
    (hgLM : B.lmRel.SupportGate mLM p q)
    (hrevMR : B.mrRel.ReverseTotal) (hrevLM : B.lmRel.ReverseTotal) :
    (∀ k,
      (∃ c, B.mrRel.ExecR mMR p q c (.fault k)) ↔
        (∃ c, B.lmRel.ExecR mLM p q c (.fault k))) ∧
    (∀ a,
      (∃ c r, B.mrRel.ExecR mMR p q c (.normal r) ∧ B.mrRel.RetRel a r) ↔
        (∃ c r, B.lmRel.ExecR mLM p q c (.normal r) ∧ B.lmRel.RetRel a r)) ∧
    ((∀ cMR uMR, B.mrRel.ExecR mMR p q cMR (.unwind uMR) →
        ∃ uA cLM uLM,
          B.ExecAnneal (B.toAnnealMR mMR) p q (.unwind uA) ∧
          B.lmRel.ExecR mLM p q cLM (.unwind uLM) ∧
          B.mrRel.UnwRel uA uMR ∧ B.lmRel.UnwRel uA uLM) ∧
      (∀ cLM uLM, B.lmRel.ExecR mLM p q cLM (.unwind uLM) →
        ∃ uA cMR uMR,
          B.ExecAnneal (B.toAnnealLM mLM) p q (.unwind uA) ∧
          B.mrRel.ExecR mMR p q cMR (.unwind uMR) ∧
          B.mrRel.UnwRel uA uMR ∧ B.lmRel.UnwRel uA uLM)) ∧
    ((∃ c, B.mrRel.ExecR mMR p q c .diverge) ↔
      (∃ c, B.lmRel.ExecR mLM p q c .diverge)) := by
  have hNorm := B.crossAuthorityNormalEquiv hmode hgMR hgLM hrevMR hrevLM
  have hUnw := B.crossAuthorityUnwindEquiv hmode hgMR hgLM hrevMR hrevLM
  have hDiv := B.crossAuthorityDivergeEquiv hmode hgMR hgLM hrevMR hrevLM
  exact ⟨fun k => B.crossAuthorityFaultEquiv hmode hgMR hgLM k,
         fun a => (hNorm.1 a).2.2, hUnw, hDiv.2.2⟩

/-- Both authorities' `CorrespondenceClaim`s follow directly from a bundle. -/
theorem correspondenceClaims
    (B : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM) :
    CorrespondenceClaim B.mrRel ∧ CorrespondenceClaim B.lmRel :=
  ⟨B.mrSim.correspondenceClaim, B.lmSim.correspondenceClaim⟩

/-- Both authorities' `FaultEquivClaim`s follow directly from a bundle. -/
theorem faultEquivClaims
    (B : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM) :
    FaultEquivClaim B.mrRel ∧ FaultEquivClaim B.lmRel :=
  ⟨B.mrSim.faultEquivClaim, B.lmSim.faultEquivClaim⟩

/--
**Cross-authority well-formedness equivalence.** At matched Anneal modes inside
both support gates, well-formedness of `MiniRust`, well-formedness of
`LeanMiri`, and fault-freedom of the single Anneal model are pairwise
equivalent.
-/
theorem crossAuthorityWellFormedEquiv
    (B : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM)
    {mMR : ModeMR} {mLM : ModeLM} (hmode : B.toAnnealMR mMR = B.toAnnealLM mLM)
    {p : Prog} {q : Query} (hgMR : B.mrRel.SupportGate mMR p q)
    (hgLM : B.lmRel.SupportGate mLM p q) :
    (B.mrRel.WellFormedRef mMR p q ↔
      ∀ k, ¬ B.ExecAnneal (B.toAnnealMR mMR) p q (.fault k)) ∧
    (B.lmRel.WellFormedRef mLM p q ↔
      ∀ k, ¬ B.ExecAnneal (B.toAnnealLM mLM) p q (.fault k)) ∧
    (B.mrRel.WellFormedRef mMR p q ↔ B.lmRel.WellFormedRef mLM p q) := by
  have hMR : B.mrRel.WellFormedRef mMR p q ↔
      ∀ k, ¬ B.ExecAnneal (B.toAnnealMR mMR) p q (.fault k) := by
    constructor
    · intro hwf k hA
      obtain ⟨c, hA'⟩ := (B.anneal_exec_coherent.1 mMR p q (.fault k)).mpr hA
      exact hwf c k (B.mrSim.reverse_fault_total mMR p q c k hgMR hA')
    · intro hwf c k hR
      have hA := (B.mrSim.faultEquivClaim mMR p q k hgMR).mpr ⟨c, hR⟩
      exact hwf k ((B.anneal_exec_coherent.1 mMR p q (.fault k)).mp hA)
  have hLM : B.lmRel.WellFormedRef mLM p q ↔
      ∀ k, ¬ B.ExecAnneal (B.toAnnealLM mLM) p q (.fault k) := by
    constructor
    · intro hwf k hA
      obtain ⟨c, hA'⟩ := (B.anneal_exec_coherent.2 mLM p q (.fault k)).mpr hA
      exact hwf c k (B.lmSim.reverse_fault_total mLM p q c k hgLM hA')
    · intro hwf c k hR
      have hA := (B.lmSim.faultEquivClaim mLM p q k hgLM).mpr ⟨c, hR⟩
      exact hwf k ((B.anneal_exec_coherent.2 mLM p q (.fault k)).mp hA)
  have hBoth : B.mrRel.WellFormedRef mMR p q ↔ B.lmRel.WellFormedRef mLM p q :=
    by
    rw [hMR, hLM, hmode]
  exact ⟨hMR, hLM, hBoth⟩

/--
Project the flip-direction guards to the single Anneal model: on each
authority's flip witness pair, `ExecAnneal` is well-formed and returns normally
on the positive input and faults on the negative input, and neither authority
nor Anneal has a constant outcome class inside the gate.
-/
theorem projectFlip
    (B : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM) :
    ((∃ a, B.ExecAnneal (B.toAnnealMR B.mrFlip.m) B.mrFlip.pOk B.mrFlip.qOk
          (.normal a)) ∧
      (∀ k, ¬ B.ExecAnneal (B.toAnnealMR B.mrFlip.m) B.mrFlip.pOk B.mrFlip.qOk
          (.fault k)) ∧
      B.ExecAnneal (B.toAnnealMR B.mrFlip.m) B.mrFlip.pFault B.mrFlip.qFault
        (.fault B.mrFlip.kind)) ∧
    ((∃ a, B.ExecAnneal (B.toAnnealLM B.lmFlip.m) B.lmFlip.pOk B.lmFlip.qOk
          (.normal a)) ∧
      (∀ k, ¬ B.ExecAnneal (B.toAnnealLM B.lmFlip.m) B.lmFlip.pOk B.lmFlip.qOk
          (.fault k)) ∧
      B.ExecAnneal (B.toAnnealLM B.lmFlip.m) B.lmFlip.pFault B.lmFlip.qFault
        (.fault B.lmFlip.kind)) := by
  constructor
  · obtain ⟨a, _, hA, _, _⟩ := B.mrFlip.okAgree
    refine ⟨⟨a, (B.anneal_exec_coherent.1 _ _ _ _).mp ⟨_, hA⟩⟩, ?_,
      (B.anneal_exec_coherent.1 _ _ _ _).mp ⟨_, B.mrFlip.faultA⟩⟩
    intro k hk
    obtain ⟨c, hc⟩ := (B.anneal_exec_coherent.1 _ _ _ _).mpr hk
    exact B.mrFlip.wfOkA c k hc
  · obtain ⟨a, _, hA, _, _⟩ := B.lmFlip.okAgree
    refine ⟨⟨a, (B.anneal_exec_coherent.2 _ _ _ _).mp ⟨_, hA⟩⟩, ?_,
      (B.anneal_exec_coherent.2 _ _ _ _).mp ⟨_, B.lmFlip.faultA⟩⟩
    intro k hk
    obtain ⟨c, hc⟩ := (B.anneal_exec_coherent.2 _ _ _ _).mpr hk
    exact B.lmFlip.wfOkA c k hc

/--
**Bundle-level non-constant Anneal outcome.** From the bundle's flip-direction
guards and `anneal_exec_coherent`, the single `ExecAnneal` model is neither
vacuously all-normal nor vacuously all-faulting on gated inputs.
-/
theorem not_constant_anneal_outcome
    (B : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM) :
    (¬ ∀ m p q out, B.mrRel.SupportGate m p q →
        B.ExecAnneal (B.toAnnealMR m) p q out → ∃ a, out = .normal a) ∧
    (¬ ∀ m p q out, B.mrRel.SupportGate m p q →
        B.ExecAnneal (B.toAnnealMR m) p q out → ∃ k, out = .fault k) ∧
    (¬ ∀ m p q out, B.lmRel.SupportGate m p q →
        B.ExecAnneal (B.toAnnealLM m) p q out → ∃ a, out = .normal a) ∧
    (¬ ∀ m p q out, B.lmRel.SupportGate m p q →
        B.ExecAnneal (B.toAnnealLM m) p q out → ∃ k, out = .fault k) := by
  obtain ⟨⟨⟨aMR, hOkMR⟩, _, hFltMR⟩, ⟨⟨aLM, hOkLM⟩, _, hFltLM⟩⟩ :=
    B.projectFlip
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    obtain ⟨a, ha⟩ := h B.mrFlip.m B.mrFlip.pFault B.mrFlip.qFault _
      B.mrFlip.gateFault hFltMR
    cases ha
  · intro h
    obtain ⟨k, hk⟩ := h B.mrFlip.m B.mrFlip.pOk B.mrFlip.qOk _
      B.mrFlip.gateOk hOkMR
    cases hk
  · intro h
    obtain ⟨a, ha⟩ := h B.lmFlip.m B.lmFlip.pFault B.lmFlip.qFault _
      B.lmFlip.gateFault hFltLM
    cases ha
  · intro h
    obtain ⟨k, hk⟩ := h B.lmFlip.m B.lmFlip.pOk B.lmFlip.qOk _
      B.lmFlip.gateOk hOkLM
    cases hk

/--
Restrict/reindex a bundle's authority modes along maps `fMR` and `fLM` that
need not be surjective: only preimages of the witness modes are required.
-/
def restrictMode {ModeMR' : Type uMM'} {ModeLM' : Type uML'}
    (B : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM)
    (fMR : ModeMR' → ModeMR) (fLM : ModeLM' → ModeLM)
    (mMRPos mMRFlt mMRFlip : ModeMR') (hMRPos : fMR mMRPos = B.mrPositive.m)
    (hMRFlt : fMR mMRFlt = B.mrFault.m) (hMRFlip : fMR mMRFlip = B.mrFlip.m)
    (mLMPos mLMFlt mLMFlip : ModeLM') (hLMPos : fLM mLMPos = B.lmPositive.m)
    (hLMFlt : fLM mLMFlt = B.lmFault.m) (hLMFlip : fLM mLMFlip = B.lmFlip.m)
    (mrMode? : Option (ModeSensitivityWitness (B.mrRel.liftMode fMR)) := none)
    (lmMode? : Option (ModeSensitivityWitness (B.lmRel.liftMode fLM)) := none) :
    DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR' ChoiceMR
      RetMR UnwMR ModeLM' ChoiceLM RetLM UnwLM where
  codec := B.codec
  repMR := B.repMR
  repLM := B.repLM
  mrRel := B.mrRel.liftMode fMR
  lmRel := B.lmRel.liftMode fLM
  mrSim := B.mrSim.liftMode fMR
  lmSim := B.lmSim.liftMode fLM
  mr_ret_codec := B.mr_ret_codec
  lm_ret_codec := B.lm_ret_codec
  toAnnealMR := fun m => B.toAnnealMR (fMR m)
  toAnnealLM := fun m => B.toAnnealLM (fLM m)
  ExecAnneal := B.ExecAnneal
  anneal_exec_coherent :=
    ⟨fun m p q out => B.anneal_exec_coherent.1 (fMR m) p q out,
     fun m p q out => B.anneal_exec_coherent.2 (fLM m) p q out⟩
  mrPositive := B.mrPositive.liftModeAt fMR mMRPos hMRPos
  lmPositive := B.lmPositive.liftModeAt fLM mLMPos hLMPos
  mrFault := B.mrFault.liftModeAt fMR mMRFlt hMRFlt
  lmFault := B.lmFault.liftModeAt fLM mLMFlt hLMFlt
  mrFlip := B.mrFlip.liftModeAt fMR mMRFlip hMRFlip mrMode?
  lmFlip := B.lmFlip.liftModeAt fLM mLMFlip hLMFlip lmMode?

/--
Reindex the authority modes of a bundle along `fMR` / `fLM`. The sections
`gMR` / `gLM` (with `fMR (gMR m) = m` and `fLM (gLM m) = m`) transport the
witnesses to the new mode types.
-/
def liftMode {ModeMR' : Type uMM'} {ModeLM' : Type uML'}
    (B : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM)
    (fMR : ModeMR' → ModeMR) (gMR : ModeMR → ModeMR')
    (hMR : ∀ m, fMR (gMR m) = m) (fLM : ModeLM' → ModeLM)
    (gLM : ModeLM → ModeLM') (hLM : ∀ m, fLM (gLM m) = m) :
    DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR' ChoiceMR
      RetMR UnwMR ModeLM' ChoiceLM RetLM UnwLM where
  codec := B.codec
  repMR := B.repMR
  repLM := B.repLM
  mrRel := B.mrRel.liftMode fMR
  lmRel := B.lmRel.liftMode fLM
  mrSim := B.mrSim.liftMode fMR
  lmSim := B.lmSim.liftMode fLM
  mr_ret_codec := B.mr_ret_codec
  lm_ret_codec := B.lm_ret_codec
  toAnnealMR := fun m => B.toAnnealMR (fMR m)
  toAnnealLM := fun m => B.toAnnealLM (fLM m)
  ExecAnneal := B.ExecAnneal
  anneal_exec_coherent :=
    ⟨fun m p q out => B.anneal_exec_coherent.1 (fMR m) p q out,
     fun m p q out => B.anneal_exec_coherent.2 (fLM m) p q out⟩
  mrPositive := B.mrPositive.liftMode fMR gMR hMR
  lmPositive := B.lmPositive.liftMode fLM gLM hLM
  mrFault := B.mrFault.liftMode fMR gMR hMR
  lmFault := B.lmFault.liftMode fLM gLM hLM
  mrFlip := B.mrFlip.liftMode fMR gMR hMR
  lmFlip := B.lmFlip.liftMode fLM gLM hLM

/--
Vertical composition of a bundle with a pair of front step simulations: a
front model (related to the bundle's Anneal model by `mrFrontSim` /
`lmFrontSim`, one per authority mode type) inherits the dual-authority
correspondence of the bundle.

- `hmidMR` / `hmidLM`: the reference model of each front simulation is the
  bundle's Anneal model;
- `hgateMR` / `hgateLM`: each front gate covers the bundle's gate;
- `frontCodec`, `hcodecMR` / `hcodecLM`: the front payload relations are
  graphs of the front codec, so the composed codec is `frontCodec.comp
  B.codec`;
- `toFrontMR`, `toFrontLM`, `ExecFront`, `hcoh`: mode matching and coherent
  executions of the front model.

All witnesses are transported constructively through the front simulations.
Mode sensitivity of the composed models is supplied separately.
-/
def comp {ModeX : Type uMX} {RetX : Type uRX} {UnwX : Type uUX}
    (B : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM)
    (frontCodec : CodecLaws RetX RetA)
    {mrFront : ModeParamStepRel ModeMR Prog Query ChoiceMR RetX RetA UnwX UnwA}
    {lmFront : ModeParamStepRel ModeLM Prog Query ChoiceLM RetX RetA UnwX UnwA}
    (mrFrontSim : ModeStepSim mrFront) (lmFrontSim : ModeStepSim lmFront)
    (hmidMR : ∀ m p q c out,
      mrFront.ExecR m p q c out ↔ B.mrRel.ExecA m p q c out)
    (hmidLM : ∀ m p q c out,
      lmFront.ExecR m p q c out ↔ B.lmRel.ExecA m p q c out)
    (hgateMR : ∀ m p q, B.mrRel.SupportGate m p q → mrFront.SupportGate m p q)
    (hgateLM : ∀ m p q, B.lmRel.SupportGate m p q → lmFront.SupportGate m p q)
    (hcodecMR : ∀ x a, mrFront.RetRel x a → a = frontCodec.encode x)
    (hcodecLM : ∀ x a, lmFront.RetRel x a → a = frontCodec.encode x)
    (toFrontMR : ModeMR → ModeX) (toFrontLM : ModeLM → ModeX)
    (ExecFront : ModeX → Prog → Query → ExecOutcome4 RetX UnwX → Prop)
    (hcoh :
      (∀ m p q out,
        (∃ c, mrFront.ExecA m p q c out) ↔ ExecFront (toFrontMR m) p q out) ∧
      (∀ m p q out,
        (∃ c, lmFront.ExecA m p q c out) ↔ ExecFront (toFrontLM m) p q out))
    (mrMode? : Option (ModeSensitivityWitness (mrFront.comp B.mrRel)) := none)
    (lmMode? : Option (ModeSensitivityWitness (lmFront.comp B.lmRel)) := none) :
    DualCorrespondenceBundle ModeX Prog Query RetX UnwX Rep ModeMR ChoiceMR
      RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM where
  codec := frontCodec.comp B.codec
  repMR := B.repMR
  repLM := B.repLM
  mrRel := mrFront.comp B.mrRel
  lmRel := lmFront.comp B.lmRel
  mrSim := mrFrontSim.comp B.mrSim hmidMR
  lmSim := lmFrontSim.comp B.lmSim hmidLM
  mr_ret_codec := fun x r h => by
    obtain ⟨a, hxa, har⟩ := h
    show B.repMR r = B.codec.encode (frontCodec.encode x)
    rw [← hcodecMR x a hxa]
    exact B.mr_ret_codec a r har
  lm_ret_codec := fun x r h => by
    obtain ⟨a, hxa, har⟩ := h
    show B.repLM r = B.codec.encode (frontCodec.encode x)
    rw [← hcodecLM x a hxa]
    exact B.lm_ret_codec a r har
  toAnnealMR := toFrontMR
  toAnnealLM := toFrontLM
  ExecAnneal := ExecFront
  anneal_exec_coherent := hcoh
  mrPositive := B.mrPositive.compFront mrFrontSim hmidMR hgateMR
  lmPositive := B.lmPositive.compFront lmFrontSim hmidLM hgateLM
  mrFault := B.mrFault.compFront mrFrontSim hmidMR hgateMR
  lmFault := B.lmFault.compFront lmFrontSim hmidLM hgateLM
  mrFlip := B.mrFlip.compFront mrFrontSim hmidMR hgateMR mrMode?
  lmFlip := B.lmFlip.compFront lmFrontSim hmidLM hgateLM lmMode?

/--
Transitivity of bundles. `B₀` relates a front model to the Anneal model of
`B₁` (both "authorities" of `B₀` are views of that Anneal model, with return
values represented by themselves: `hrepMR` / `hrepLM`), and `B₁` relates the
Anneal model to `MiniRust` and `LeanMiri`. The result relates the front model
directly to both authorities, with codec `B₀.codec.comp B₁.codec`.
-/
def trans {ModeX : Type uMX} {RetX : Type uRX} {UnwX : Type uUX}
    (B₀ : DualCorrespondenceBundle ModeX Prog Query RetX UnwX RetA ModeMR
      ChoiceMR RetA UnwA ModeLM ChoiceLM RetA UnwA)
    (B₁ : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM)
    (hmidMR : ∀ m p q c out,
      B₀.mrRel.ExecR m p q c out ↔ B₁.mrRel.ExecA m p q c out)
    (hmidLM : ∀ m p q c out,
      B₀.lmRel.ExecR m p q c out ↔ B₁.lmRel.ExecA m p q c out)
    (hgateMR : ∀ m p q,
      B₁.mrRel.SupportGate m p q → B₀.mrRel.SupportGate m p q)
    (hgateLM : ∀ m p q,
      B₁.lmRel.SupportGate m p q → B₀.lmRel.SupportGate m p q)
    (hrepMR : ∀ a, B₀.repMR a = a) (hrepLM : ∀ a, B₀.repLM a = a)
    (mrMode? : Option (ModeSensitivityWitness (B₀.mrRel.comp B₁.mrRel)) := none)
    (lmMode? : Option (ModeSensitivityWitness (B₀.lmRel.comp B₁.lmRel)) :=
      none) :
    DualCorrespondenceBundle ModeX Prog Query RetX UnwX Rep ModeMR ChoiceMR
      RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM :=
  B₁.comp B₀.codec B₀.mrSim B₀.lmSim hmidMR hmidLM hgateMR hgateLM
    (fun x a h => (hrepMR a).symm.trans (B₀.mr_ret_codec x a h))
    (fun x a h => (hrepLM a).symm.trans (B₀.lm_ret_codec x a h))
    B₀.toAnnealMR B₀.toAnnealLM B₀.ExecAnneal B₀.anneal_exec_coherent
    mrMode? lmMode?

/-- The codec of a transitive bundle is the composition of the codecs. -/
theorem trans_codec {ModeX : Type uMX} {RetX : Type uRX} {UnwX : Type uUX}
    (B₀ : DualCorrespondenceBundle ModeX Prog Query RetX UnwX RetA ModeMR
      ChoiceMR RetA UnwA ModeLM ChoiceLM RetA UnwA)
    (B₁ : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM)
    (hmidMR : ∀ m p q c out,
      B₀.mrRel.ExecR m p q c out ↔ B₁.mrRel.ExecA m p q c out)
    (hmidLM : ∀ m p q c out,
      B₀.lmRel.ExecR m p q c out ↔ B₁.lmRel.ExecA m p q c out)
    (hgateMR : ∀ m p q,
      B₁.mrRel.SupportGate m p q → B₀.mrRel.SupportGate m p q)
    (hgateLM : ∀ m p q,
      B₁.lmRel.SupportGate m p q → B₀.lmRel.SupportGate m p q)
    (hrepMR : ∀ a, B₀.repMR a = a) (hrepLM : ∀ a, B₀.repLM a = a) :
    (B₀.trans B₁ hmidMR hmidLM hgateMR hgateLM hrepMR hrepLM).codec =
      B₀.codec.comp B₁.codec := rfl

/--
Mode-sensitivity-preserving vertical bundle composition: whenever the front
simulations have `ReverseTotal` and functional unwind relations (return
functionality already follows from `hcodecMR` / `hcodecLM`), any recorded
`modeSensitivity?` witnesses on `B` are transported automatically instead of
dropped.
-/
def compPreserveMode {ModeX : Type uMX} {RetX : Type uRX} {UnwX : Type uUX}
    (B : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM)
    (frontCodec : CodecLaws RetX RetA)
    {mrFront : ModeParamStepRel ModeMR Prog Query ChoiceMR RetX RetA UnwX UnwA}
    {lmFront : ModeParamStepRel ModeLM Prog Query ChoiceLM RetX RetA UnwX UnwA}
    (mrFrontSim : ModeStepSim mrFront) (lmFrontSim : ModeStepSim lmFront)
    (hrevMR : mrFront.ReverseTotal) (hrevLM : lmFront.ReverseTotal)
    (hmidMR : ∀ m p q c out,
      mrFront.ExecR m p q c out ↔ B.mrRel.ExecA m p q c out)
    (hmidLM : ∀ m p q c out,
      lmFront.ExecR m p q c out ↔ B.lmRel.ExecA m p q c out)
    (hgateMR : ∀ m p q, B.mrRel.SupportGate m p q → mrFront.SupportGate m p q)
    (hgateLM : ∀ m p q, B.lmRel.SupportGate m p q → lmFront.SupportGate m p q)
    (hcodecMR : ∀ x a, mrFront.RetRel x a → a = frontCodec.encode x)
    (hcodecLM : ∀ x a, lmFront.RetRel x a → a = frontCodec.encode x)
    (hUnwFunMR : ∀ x u₁ u₂, mrFront.UnwRel x u₁ → mrFront.UnwRel x u₂ →
      u₁ = u₂)
    (hUnwFunLM : ∀ x u₁ u₂, lmFront.UnwRel x u₁ → lmFront.UnwRel x u₂ →
      u₁ = u₂)
    (toFrontMR : ModeMR → ModeX) (toFrontLM : ModeLM → ModeX)
    (ExecFront : ModeX → Prog → Query → ExecOutcome4 RetX UnwX → Prop)
    (hcoh :
      (∀ m p q out,
        (∃ c, mrFront.ExecA m p q c out) ↔ ExecFront (toFrontMR m) p q out) ∧
      (∀ m p q out,
        (∃ c, lmFront.ExecA m p q c out) ↔ ExecFront (toFrontLM m) p q out)) :
    DualCorrespondenceBundle ModeX Prog Query RetX UnwX Rep ModeMR ChoiceMR
      RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM :=
  B.comp frontCodec mrFrontSim lmFrontSim hmidMR hmidLM hgateMR hgateLM
    hcodecMR hcodecLM toFrontMR toFrontLM ExecFront hcoh
    (B.mrFlip.modeSensitivity?.map fun ms =>
      ms.compFrontOfReverseTotal mrFrontSim hrevMR hmidMR hgateMR
        (fun x b₁ b₂ h₁ h₂ => (hcodecMR x b₁ h₁).trans (hcodecMR x b₂ h₂).symm)
        hUnwFunMR)
    (B.lmFlip.modeSensitivity?.map fun ms =>
      ms.compFrontOfReverseTotal lmFrontSim hrevLM hmidLM hgateLM
        (fun x b₁ b₂ h₁ h₂ => (hcodecLM x b₁ h₁).trans (hcodecLM x b₂ h₂).symm)
        hUnwFunLM)

/--
Mode-sensitivity-preserving transitive bundle composition: automatically
transports `B₁`'s recorded `modeSensitivity?` witnesses across `B₀`.
-/
def transPreserveMode {ModeX : Type uMX} {RetX : Type uRX} {UnwX : Type uUX}
    (B₀ : DualCorrespondenceBundle ModeX Prog Query RetX UnwX RetA ModeMR
      ChoiceMR RetA UnwA ModeLM ChoiceLM RetA UnwA)
    (B₁ : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM)
    (hrevMR : B₀.mrRel.ReverseTotal) (hrevLM : B₀.lmRel.ReverseTotal)
    (hmidMR : ∀ m p q c out,
      B₀.mrRel.ExecR m p q c out ↔ B₁.mrRel.ExecA m p q c out)
    (hmidLM : ∀ m p q c out,
      B₀.lmRel.ExecR m p q c out ↔ B₁.lmRel.ExecA m p q c out)
    (hgateMR : ∀ m p q,
      B₁.mrRel.SupportGate m p q → B₀.mrRel.SupportGate m p q)
    (hgateLM : ∀ m p q,
      B₁.lmRel.SupportGate m p q → B₀.lmRel.SupportGate m p q)
    (hrepMR : ∀ a, B₀.repMR a = a) (hrepLM : ∀ a, B₀.repLM a = a)
    (hUnwFunMR : ∀ x u₁ u₂, B₀.mrRel.UnwRel x u₁ → B₀.mrRel.UnwRel x u₂ →
      u₁ = u₂)
    (hUnwFunLM : ∀ x u₁ u₂, B₀.lmRel.UnwRel x u₁ → B₀.lmRel.UnwRel x u₂ →
      u₁ = u₂) :
    DualCorrespondenceBundle ModeX Prog Query RetX UnwX Rep ModeMR ChoiceMR
      RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM :=
  B₁.compPreserveMode B₀.codec B₀.mrSim B₀.lmSim hrevMR hrevLM hmidMR hmidLM
    hgateMR hgateLM
    (fun x a h => (hrepMR a).symm.trans (B₀.mr_ret_codec x a h))
    (fun x a h => (hrepLM a).symm.trans (B₀.lm_ret_codec x a h))
    hUnwFunMR hUnwFunLM B₀.toAnnealMR B₀.toAnnealLM B₀.ExecAnneal
    B₀.anneal_exec_coherent

/--
Fault-flipping mode-sensitivity-preserving vertical bundle composition: unlike
`compPreserveMode`, requires NEITHER `ReverseTotal` NOR functional unwind
relations when `B`'s mode-sensitivity witnesses flip on faults (`IsFaultFlip`).
-/
def compPreserveFaultMode {ModeX : Type uMX} {RetX : Type uRX}
    {UnwX : Type uUX}
    (B : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM)
    (frontCodec : CodecLaws RetX RetA)
    {mrFront : ModeParamStepRel ModeMR Prog Query ChoiceMR RetX RetA UnwX UnwA}
    {lmFront : ModeParamStepRel ModeLM Prog Query ChoiceLM RetX RetA UnwX UnwA}
    (mrFrontSim : ModeStepSim mrFront) (lmFrontSim : ModeStepSim lmFront)
    (hmidMR : ∀ m p q c out,
      mrFront.ExecR m p q c out ↔ B.mrRel.ExecA m p q c out)
    (hmidLM : ∀ m p q c out,
      lmFront.ExecR m p q c out ↔ B.lmRel.ExecA m p q c out)
    (hgateMR : ∀ m p q, B.mrRel.SupportGate m p q → mrFront.SupportGate m p q)
    (hgateLM : ∀ m p q, B.lmRel.SupportGate m p q → lmFront.SupportGate m p q)
    (hcodecMR : ∀ x a, mrFront.RetRel x a → a = frontCodec.encode x)
    (hcodecLM : ∀ x a, lmFront.RetRel x a → a = frontCodec.encode x)
    (hFaultMR : ∀ ms, B.mrFlip.modeSensitivity? = some ms → ms.IsFaultFlip)
    (hFaultLM : ∀ ms, B.lmFlip.modeSensitivity? = some ms → ms.IsFaultFlip)
    (toFrontMR : ModeMR → ModeX) (toFrontLM : ModeLM → ModeX)
    (ExecFront : ModeX → Prog → Query → ExecOutcome4 RetX UnwX → Prop)
    (hcoh :
      (∀ m p q out,
        (∃ c, mrFront.ExecA m p q c out) ↔ ExecFront (toFrontMR m) p q out) ∧
      (∀ m p q out,
        (∃ c, lmFront.ExecA m p q c out) ↔ ExecFront (toFrontLM m) p q out)) :
    DualCorrespondenceBundle ModeX Prog Query RetX UnwX Rep ModeMR ChoiceMR
      RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM :=
  let mrMs? : Option (ModeSensitivityWitness (mrFront.comp B.mrRel)) :=
    match hMR : B.mrFlip.modeSensitivity? with
    | none => none
    | some ms =>
      some (ms.compFrontOfFaultFlip (hFaultMR ms hMR) mrFrontSim hmidMR hgateMR)
  let lmMs? : Option (ModeSensitivityWitness (lmFront.comp B.lmRel)) :=
    match hLM : B.lmFlip.modeSensitivity? with
    | none => none
    | some ms =>
      some (ms.compFrontOfFaultFlip (hFaultLM ms hLM) lmFrontSim hmidLM hgateLM)
  B.comp frontCodec mrFrontSim lmFrontSim hmidMR hmidLM hgateMR hgateLM
    hcodecMR hcodecLM toFrontMR toFrontLM ExecFront hcoh mrMs? lmMs?

/-- Transitive bundle composition preserving fault-flipping mode sensitivity
without `ReverseTotal` or functional unwind relations. -/
def transPreserveFaultMode {ModeX : Type uMX} {RetX : Type uRX}
    {UnwX : Type uUX}
    (B₀ : DualCorrespondenceBundle ModeX Prog Query RetX UnwX RetA ModeMR
      ChoiceMR RetA UnwA ModeLM ChoiceLM RetA UnwA)
    (B₁ : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM)
    (hmidMR : ∀ m p q c out,
      B₀.mrRel.ExecR m p q c out ↔ B₁.mrRel.ExecA m p q c out)
    (hmidLM : ∀ m p q c out,
      B₀.lmRel.ExecR m p q c out ↔ B₁.lmRel.ExecA m p q c out)
    (hgateMR : ∀ m p q,
      B₁.mrRel.SupportGate m p q → B₀.mrRel.SupportGate m p q)
    (hgateLM : ∀ m p q,
      B₁.lmRel.SupportGate m p q → B₀.lmRel.SupportGate m p q)
    (hrepMR : ∀ a, B₀.repMR a = a) (hrepLM : ∀ a, B₀.repLM a = a)
    (hFaultMR : ∀ ms, B₁.mrFlip.modeSensitivity? = some ms → ms.IsFaultFlip)
    (hFaultLM : ∀ ms, B₁.lmFlip.modeSensitivity? = some ms → ms.IsFaultFlip) :
    DualCorrespondenceBundle ModeX Prog Query RetX UnwX Rep ModeMR ChoiceMR
      RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM :=
  B₁.compPreserveFaultMode B₀.codec B₀.mrSim B₀.lmSim hmidMR hmidLM hgateMR
    hgateLM
    (fun x a h => (hrepMR a).symm.trans (B₀.mr_ret_codec x a h))
    (fun x a h => (hrepLM a).symm.trans (B₀.lm_ret_codec x a h))
    hFaultMR hFaultLM B₀.toAnnealMR B₀.toAnnealLM B₀.ExecAnneal
    B₀.anneal_exec_coherent

/--
Per-authority constructive mode-sensitivity transport strategy for vertical
bundle composition: either the witness flips on a fault (`faultFlip`, needing
neither `ReverseTotal` nor functional unwind relations), or the front
simulation has `ReverseTotal` and a functional unwind relation (`reverseTotal`).
-/
inductive ModeSensitivityTransport
    {Mode : Type uM} {Choice : Type uC} {RetX : Type uRX} {RetA : Type uRA}
    {RetR : Type uRR} {UnwX : Type uUX} {UnwA : Type uUA} {UnwR : Type uUR}
    (R₁ : ModeParamStepRel Mode Prog Query Choice RetX RetA UnwX UnwA)
    (R₂ : ModeParamStepRel Mode Prog Query Choice RetA RetR UnwA UnwR)
    (ms? : Option (ModeSensitivityWitness R₂)) : Type _ where
  /-- Transport a fault-flipping witness without `ReverseTotal`. -/
  | faultFlip (h : ∀ ms, ms? = some ms → ms.IsFaultFlip)
  /-- Transport any witness via front `ReverseTotal` and functional unwind. -/
  | reverseTotal (hrev : R₁.ReverseTotal)
      (hUnw : ∀ x y₁ y₂, R₁.UnwRel x y₁ → R₁.UnwRel x y₂ → y₁ = y₂)

/--
Mixed mode-sensitivity-preserving vertical bundle composition: each authority
independently transports its `modeSensitivity?` witness via EITHER `faultFlip`
(requiring no `ReverseTotal`) OR `reverseTotal`, unifying `compPreserveMode`
and `compPreserveFaultMode` on asymmetric bundles.
-/
def compPreserveModeMixed {ModeX : Type uMX} {RetX : Type uRX}
    {UnwX : Type uUX}
    (B : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM)
    (frontCodec : CodecLaws RetX RetA)
    {mrFront : ModeParamStepRel ModeMR Prog Query ChoiceMR RetX RetA UnwX UnwA}
    {lmFront : ModeParamStepRel ModeLM Prog Query ChoiceLM RetX RetA UnwX UnwA}
    (mrFrontSim : ModeStepSim mrFront) (lmFrontSim : ModeStepSim lmFront)
    (hmidMR : ∀ m p q c out,
      mrFront.ExecR m p q c out ↔ B.mrRel.ExecA m p q c out)
    (hmidLM : ∀ m p q c out,
      lmFront.ExecR m p q c out ↔ B.lmRel.ExecA m p q c out)
    (hgateMR : ∀ m p q, B.mrRel.SupportGate m p q → mrFront.SupportGate m p q)
    (hgateLM : ∀ m p q, B.lmRel.SupportGate m p q → lmFront.SupportGate m p q)
    (hcodecMR : ∀ x a, mrFront.RetRel x a → a = frontCodec.encode x)
    (hcodecLM : ∀ x a, lmFront.RetRel x a → a = frontCodec.encode x)
    (trMR :
      ModeSensitivityTransport mrFront B.mrRel B.mrFlip.modeSensitivity?)
    (trLM :
      ModeSensitivityTransport lmFront B.lmRel B.lmFlip.modeSensitivity?)
    (toFrontMR : ModeMR → ModeX) (toFrontLM : ModeLM → ModeX)
    (ExecFront : ModeX → Prog → Query → ExecOutcome4 RetX UnwX → Prop)
    (hcoh :
      (∀ m p q out,
        (∃ c, mrFront.ExecA m p q c out) ↔ ExecFront (toFrontMR m) p q out) ∧
      (∀ m p q out,
        (∃ c, lmFront.ExecA m p q c out) ↔ ExecFront (toFrontLM m) p q out)) :
    DualCorrespondenceBundle ModeX Prog Query RetX UnwX Rep ModeMR ChoiceMR
      RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM :=
  let mrMs? : Option (ModeSensitivityWitness (mrFront.comp B.mrRel)) :=
    match hMR : B.mrFlip.modeSensitivity? with
    | none => none
    | some ms =>
      match trMR with
      | .faultFlip hF =>
        some (ms.compFrontOfFaultFlip (hF ms hMR) mrFrontSim hmidMR hgateMR)
      | .reverseTotal hrev hUnw =>
        some (ms.compFrontOfReverseTotal mrFrontSim hrev hmidMR hgateMR
          (fun x y₁ y₂ h₁ h₂ =>
            (hcodecMR x y₁ h₁).trans (hcodecMR x y₂ h₂).symm)
          hUnw)
  let lmMs? : Option (ModeSensitivityWitness (lmFront.comp B.lmRel)) :=
    match hLM : B.lmFlip.modeSensitivity? with
    | none => none
    | some ms =>
      match trLM with
      | .faultFlip hF =>
        some (ms.compFrontOfFaultFlip (hF ms hLM) lmFrontSim hmidLM hgateLM)
      | .reverseTotal hrev hUnw =>
        some (ms.compFrontOfReverseTotal lmFrontSim hrev hmidLM hgateLM
          (fun x y₁ y₂ h₁ h₂ =>
            (hcodecLM x y₁ h₁).trans (hcodecLM x y₂ h₂).symm)
          hUnw)
  B.comp frontCodec mrFrontSim lmFrontSim hmidMR hmidLM hgateMR hgateLM
    hcodecMR hcodecLM toFrontMR toFrontLM ExecFront hcoh mrMs? lmMs?

/-- Reference productivity transfers to Anneal productivity on both
authorities of a bundle. -/
theorem productiveAnneal_of_productiveRef
    (B : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM)
    (hMR : B.mrRel.ProductiveRef) (hLM : B.lmRel.ProductiveRef) :
    B.mrRel.ProductiveAnneal ∧ B.lmRel.ProductiveAnneal :=
  ⟨B.mrSim.productiveAnneal_of_productiveRef hMR,
   B.lmSim.productiveAnneal_of_productiveRef hLM⟩

/-- Reverse totality transfers Anneal productivity to reference productivity on
both authorities of a bundle. -/
theorem productiveRef_of_reverseTotal
    (B : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM)
    (hrevMR : B.mrRel.ReverseTotal) (hrevLM : B.lmRel.ReverseTotal)
    (hMR : B.mrRel.ProductiveAnneal) (hLM : B.lmRel.ProductiveAnneal) :
    B.mrRel.ProductiveRef ∧ B.lmRel.ProductiveRef :=
  ⟨B.mrSim.productiveRef_of_reverseTotal hrevMR hMR,
   B.lmSim.productiveRef_of_reverseTotal hrevLM hLM⟩

/-- `DualCorrespondenceBundle.liftMode` preserves Anneal productivity. -/
theorem liftMode_productiveAnneal {ModeMR' : Type uMM'} {ModeLM' : Type uML'}
    (B : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM)
    (fMR : ModeMR' → ModeMR) (gMR : ModeMR → ModeMR')
    (hMR : ∀ m, fMR (gMR m) = m) (fLM : ModeLM' → ModeLM)
    (gLM : ModeLM → ModeLM') (hLM : ∀ m, fLM (gLM m) = m)
    (hpMR : B.mrRel.ProductiveAnneal) (hpLM : B.lmRel.ProductiveAnneal) :
    (B.liftMode fMR gMR hMR fLM gLM hLM).mrRel.ProductiveAnneal ∧
      (B.liftMode fMR gMR hMR fLM gLM hLM).lmRel.ProductiveAnneal :=
  ⟨B.mrRel.liftMode_productiveAnneal fMR hpMR,
   B.lmRel.liftMode_productiveAnneal fLM hpLM⟩

/-- Vertical bundle composition inherits Anneal productivity from the front
step relations. -/
theorem comp_productiveAnneal {ModeX : Type uMX} {RetX : Type uRX}
    {UnwX : Type uUX}
    (B : DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR
      ChoiceMR RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM)
    (frontCodec : CodecLaws RetX RetA)
    {mrFront : ModeParamStepRel ModeMR Prog Query ChoiceMR RetX RetA UnwX UnwA}
    {lmFront : ModeParamStepRel ModeLM Prog Query ChoiceLM RetX RetA UnwX UnwA}
    (mrFrontSim : ModeStepSim mrFront) (lmFrontSim : ModeStepSim lmFront)
    (hmidMR : ∀ m p q c out,
      mrFront.ExecR m p q c out ↔ B.mrRel.ExecA m p q c out)
    (hmidLM : ∀ m p q c out,
      lmFront.ExecR m p q c out ↔ B.lmRel.ExecA m p q c out)
    (hgateMR : ∀ m p q, B.mrRel.SupportGate m p q → mrFront.SupportGate m p q)
    (hgateLM : ∀ m p q, B.lmRel.SupportGate m p q → lmFront.SupportGate m p q)
    (hcodecMR : ∀ x a, mrFront.RetRel x a → a = frontCodec.encode x)
    (hcodecLM : ∀ x a, lmFront.RetRel x a → a = frontCodec.encode x)
    (toFrontMR : ModeMR → ModeX) (toFrontLM : ModeLM → ModeX)
    (ExecFront : ModeX → Prog → Query → ExecOutcome4 RetX UnwX → Prop)
    (hcoh :
      (∀ m p q out,
        (∃ c, mrFront.ExecA m p q c out) ↔ ExecFront (toFrontMR m) p q out) ∧
      (∀ m p q out,
        (∃ c, lmFront.ExecA m p q c out) ↔ ExecFront (toFrontLM m) p q out))
    (hpMR : mrFront.ProductiveAnneal) (hpLM : lmFront.ProductiveAnneal) :
    (B.comp frontCodec mrFrontSim lmFrontSim hmidMR hmidLM hgateMR hgateLM
        hcodecMR hcodecLM toFrontMR toFrontLM ExecFront
        hcoh).mrRel.ProductiveAnneal ∧
      (B.comp frontCodec mrFrontSim lmFrontSim hmidMR hmidLM hgateMR hgateLM
        hcodecMR hcodecLM toFrontMR toFrontLM ExecFront
        hcoh).lmRel.ProductiveAnneal :=
  ⟨fun m p q hg => hpMR m p q hg.1, fun m p q hg => hpLM m p q hg.1⟩

/--
Ergonomic constructor from evaluation-equivalence theorems. The Anneal model
is a deterministic, choice-independent evaluator `evalA`; each authority is a
relational model (`ExecMR`, `ExecLM`). The simulations follow from, per
authority, coupling of every gated reference execution with the Anneal
evaluation (`fwdMR`, `fwdLM`) and reflection of Anneal faults (`revMR`,
`revLM`). The flip-direction guards are assembled from the positive and fault
witnesses, which must share a mode (`hmMR`, `hmLM`), plus optional
mode-sensitivity witnesses.
-/
def fromEquiv (codec : CodecLaws RetA Rep) (repMR : RetMR → Rep)
    (repLM : RetLM → Rep)
    (evalA : ModeA → Prog → Query → ExecOutcome4 RetA UnwA)
    (toAnnealMR : ModeMR → ModeA) (toAnnealLM : ModeLM → ModeA)
    (gateMR : ModeMR → Prog → Query → Prop)
    (gateLM : ModeLM → Prog → Query → Prop)
    (ExecMR :
      ModeMR → Prog → Query → ChoiceMR → ExecOutcome4 RetMR UnwMR → Prop)
    (ExecLM :
      ModeLM → Prog → Query → ChoiceLM → ExecOutcome4 RetLM UnwLM → Prop)
    (RetRelMR : RetA → RetMR → Prop) (UnwRelMR : UnwA → UnwMR → Prop)
    (RetRelLM : RetA → RetLM → Prop) (UnwRelLM : UnwA → UnwLM → Prop)
    (hRetMR : ∀ a r, RetRelMR a r → repMR r = codec.encode a)
    (hRetLM : ∀ a r, RetRelLM a r → repLM r = codec.encode a)
    (fwdMR : ∀ m p q c out, gateMR m p q → ExecMR m p q c out →
      ChoiceCoupledOutcomeRel RetRelMR UnwRelMR (evalA (toAnnealMR m) p q) out)
    (revMR : ∀ m p q c k, gateMR m p q →
      evalA (toAnnealMR m) p q = .fault k → ExecMR m p q c (.fault k))
    (fwdLM : ∀ m p q c out, gateLM m p q → ExecLM m p q c out →
      ChoiceCoupledOutcomeRel RetRelLM UnwRelLM (evalA (toAnnealLM m) p q) out)
    (revLM : ∀ m p q c k, gateLM m p q →
      evalA (toAnnealLM m) p q = .fault k → ExecLM m p q c (.fault k))
    (mrPositive : PositiveWitness
      (ModeParamStepRel.ofAnnealEval toAnnealMR gateMR evalA ExecMR RetRelMR
        UnwRelMR))
    (lmPositive : PositiveWitness
      (ModeParamStepRel.ofAnnealEval toAnnealLM gateLM evalA ExecLM RetRelLM
        UnwRelLM))
    (mrFault : FaultEquivWitness
      (ModeParamStepRel.ofAnnealEval toAnnealMR gateMR evalA ExecMR RetRelMR
        UnwRelMR))
    (lmFault : FaultEquivWitness
      (ModeParamStepRel.ofAnnealEval toAnnealLM gateLM evalA ExecLM RetRelLM
        UnwRelLM))
    (hmMR : mrFault.m = mrPositive.m) (hmLM : lmFault.m = lmPositive.m)
    (mrMode? : Option (ModeSensitivityWitness
      (ModeParamStepRel.ofAnnealEval toAnnealMR gateMR evalA ExecMR RetRelMR
        UnwRelMR)) := none)
    (lmMode? : Option (ModeSensitivityWitness
      (ModeParamStepRel.ofAnnealEval toAnnealLM gateLM evalA ExecLM RetRelLM
        UnwRelLM)) := none)
    (mrRevTotal? : Option (PLift
      (ModeParamStepRel.ofAnnealEval toAnnealMR gateMR evalA ExecMR RetRelMR
        UnwRelMR).ReverseTotal) := none)
    (lmRevTotal? : Option (PLift
      (ModeParamStepRel.ofAnnealEval toAnnealLM gateLM evalA ExecLM RetRelLM
        UnwRelLM).ReverseTotal) := none) :
    DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR ChoiceMR
      RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM :=
  let mrSim :=
    ModeStepSim.fromAnnealEval toAnnealMR gateMR evalA ExecMR RetRelMR UnwRelMR
      fwdMR revMR mrRevTotal?
  let lmSim :=
    ModeStepSim.fromAnnealEval toAnnealLM gateLM evalA ExecLM RetRelLM UnwRelLM
      fwdLM revLM lmRevTotal?
  { codec := codec
    repMR := repMR
    repLM := repLM
    mrRel :=
      ModeParamStepRel.ofAnnealEval toAnnealMR gateMR evalA ExecMR RetRelMR
        UnwRelMR
    lmRel :=
      ModeParamStepRel.ofAnnealEval toAnnealLM gateLM evalA ExecLM RetRelLM
        UnwRelLM
    mrSim := mrSim
    lmSim := lmSim
    mr_ret_codec := hRetMR
    lm_ret_codec := hRetLM
    toAnnealMR := toAnnealMR
    toAnnealLM := toAnnealLM
    ExecAnneal := fun mA p q out => evalA mA p q = out
    anneal_exec_coherent :=
      ⟨fun _ _ _ _ => ⟨fun ⟨_, h⟩ => h, fun h => ⟨mrPositive.c, h⟩⟩,
       fun _ _ _ _ => ⟨fun ⟨_, h⟩ => h, fun h => ⟨lmPositive.c, h⟩⟩⟩
    mrPositive := mrPositive
    lmPositive := lmPositive
    mrFault := mrFault
    lmFault := lmFault
    mrFlip :=
      FlipDirectionWitness.ofFaultAndMode mrSim mrPositive mrFault hmMR mrMode?
    lmFlip :=
      FlipDirectionWitness.ofFaultAndMode lmSim lmPositive lmFault hmLM
        lmMode? }

/-- Every bundle built with `fromEquiv` satisfies `ProductiveAnneal` on both
authorities (using the witness choice from `mrPositive` / `lmPositive`). -/
theorem fromEquiv_productiveAnneal (codec : CodecLaws RetA Rep)
    (repMR : RetMR → Rep) (repLM : RetLM → Rep)
    (evalA : ModeA → Prog → Query → ExecOutcome4 RetA UnwA)
    (toAnnealMR : ModeMR → ModeA) (toAnnealLM : ModeLM → ModeA)
    (gateMR : ModeMR → Prog → Query → Prop)
    (gateLM : ModeLM → Prog → Query → Prop)
    (ExecMR :
      ModeMR → Prog → Query → ChoiceMR → ExecOutcome4 RetMR UnwMR → Prop)
    (ExecLM :
      ModeLM → Prog → Query → ChoiceLM → ExecOutcome4 RetLM UnwLM → Prop)
    (RetRelMR : RetA → RetMR → Prop) (UnwRelMR : UnwA → UnwMR → Prop)
    (RetRelLM : RetA → RetLM → Prop) (UnwRelLM : UnwA → UnwLM → Prop)
    (hRetMR : ∀ a r, RetRelMR a r → repMR r = codec.encode a)
    (hRetLM : ∀ a r, RetRelLM a r → repLM r = codec.encode a)
    (fwdMR : ∀ m p q c out, gateMR m p q → ExecMR m p q c out →
      ChoiceCoupledOutcomeRel RetRelMR UnwRelMR (evalA (toAnnealMR m) p q) out)
    (revMR : ∀ m p q c k, gateMR m p q →
      evalA (toAnnealMR m) p q = .fault k → ExecMR m p q c (.fault k))
    (fwdLM : ∀ m p q c out, gateLM m p q → ExecLM m p q c out →
      ChoiceCoupledOutcomeRel RetRelLM UnwRelLM (evalA (toAnnealLM m) p q) out)
    (revLM : ∀ m p q c k, gateLM m p q →
      evalA (toAnnealLM m) p q = .fault k → ExecLM m p q c (.fault k))
    (mrPositive : PositiveWitness
      (ModeParamStepRel.ofAnnealEval toAnnealMR gateMR evalA ExecMR RetRelMR
        UnwRelMR))
    (lmPositive : PositiveWitness
      (ModeParamStepRel.ofAnnealEval toAnnealLM gateLM evalA ExecLM RetRelLM
        UnwRelLM))
    (mrFault : FaultEquivWitness
      (ModeParamStepRel.ofAnnealEval toAnnealMR gateMR evalA ExecMR RetRelMR
        UnwRelMR))
    (lmFault : FaultEquivWitness
      (ModeParamStepRel.ofAnnealEval toAnnealLM gateLM evalA ExecLM RetRelLM
        UnwRelLM))
    (hmMR : mrFault.m = mrPositive.m) (hmLM : lmFault.m = lmPositive.m)
    (mrMode? : Option (ModeSensitivityWitness
      (ModeParamStepRel.ofAnnealEval toAnnealMR gateMR evalA ExecMR RetRelMR
        UnwRelMR)) := none)
    (lmMode? : Option (ModeSensitivityWitness
      (ModeParamStepRel.ofAnnealEval toAnnealLM gateLM evalA ExecLM RetRelLM
        UnwRelLM)) := none)
    (mrRevTotal? : Option (PLift
      (ModeParamStepRel.ofAnnealEval toAnnealMR gateMR evalA ExecMR RetRelMR
        UnwRelMR).ReverseTotal) := none)
    (lmRevTotal? : Option (PLift
      (ModeParamStepRel.ofAnnealEval toAnnealLM gateLM evalA ExecLM RetRelLM
        UnwRelLM).ReverseTotal) := none) :
    let B :=
      fromEquiv codec repMR repLM evalA toAnnealMR toAnnealLM gateMR gateLM
        ExecMR ExecLM RetRelMR UnwRelMR RetRelLM UnwRelLM hRetMR hRetLM fwdMR
        revMR fwdLM revLM mrPositive lmPositive mrFault lmFault hmMR hmLM
        mrMode? lmMode? mrRevTotal? lmRevTotal?
    B.mrRel.ProductiveAnneal ∧ B.lmRel.ProductiveAnneal :=
  ⟨fun m p q _ => ⟨mrPositive.c, evalA (toAnnealMR m) p q, rfl⟩,
   fun m p q _ => ⟨lmPositive.c, evalA (toAnnealLM m) p q, rfl⟩⟩

/--
Choice-gated deterministic-Anneal constructor (`fromEquivGated`), completing
`ofAnnealEvalGated` / `fromAnnealEvalGated` into a full
`DualCorrespondenceBundle`. Requiring `hChoiceMR` and `hChoiceLM` (at least one
valid choice per `(m, p, q)`) guarantees choice productivity (`Section 4.5`,
ruling out `ofAnnealEvalGated_vacuous_of_empty_choice`) and discharges
`anneal_exec_coherent` against `fun mA p q out => evalA mA p q = out`.
-/
def fromEquivGated (codec : CodecLaws RetA Rep) (repMR : RetMR → Rep)
    (repLM : RetLM → Rep)
    (evalA : ModeA → Prog → Query → ExecOutcome4 RetA UnwA)
    (toAnnealMR : ModeMR → ModeA) (toAnnealLM : ModeLM → ModeA)
    (gateMR : ModeMR → Prog → Query → Prop)
    (gateLM : ModeLM → Prog → Query → Prop)
    (validChoiceMR : ModeMR → Prog → Query → ChoiceMR → Prop)
    (validChoiceLM : ModeLM → Prog → Query → ChoiceLM → Prop)
    (hChoiceMR : ∀ m p q, ∃ c, validChoiceMR m p q c)
    (hChoiceLM : ∀ m p q, ∃ c, validChoiceLM m p q c)
    (ExecMR :
      ModeMR → Prog → Query → ChoiceMR → ExecOutcome4 RetMR UnwMR → Prop)
    (ExecLM :
      ModeLM → Prog → Query → ChoiceLM → ExecOutcome4 RetLM UnwLM → Prop)
    (RetRelMR : RetA → RetMR → Prop) (UnwRelMR : UnwA → UnwMR → Prop)
    (RetRelLM : RetA → RetLM → Prop) (UnwRelLM : UnwA → UnwLM → Prop)
    (hRetMR : ∀ a r, RetRelMR a r → repMR r = codec.encode a)
    (hRetLM : ∀ a r, RetRelLM a r → repLM r = codec.encode a)
    (fwdMR : ∀ m p q c out, gateMR m p q → ExecMR m p q c out →
      validChoiceMR m p q c ∧
      ChoiceCoupledOutcomeRel RetRelMR UnwRelMR (evalA (toAnnealMR m) p q) out)
    (revMR : ∀ m p q c k, gateMR m p q → validChoiceMR m p q c →
      evalA (toAnnealMR m) p q = .fault k → ExecMR m p q c (.fault k))
    (fwdLM : ∀ m p q c out, gateLM m p q → ExecLM m p q c out →
      validChoiceLM m p q c ∧
      ChoiceCoupledOutcomeRel RetRelLM UnwRelLM (evalA (toAnnealLM m) p q) out)
    (revLM : ∀ m p q c k, gateLM m p q → validChoiceLM m p q c →
      evalA (toAnnealLM m) p q = .fault k → ExecLM m p q c (.fault k))
    (mrPositive : PositiveWitness
      (ModeParamStepRel.ofAnnealEvalGated toAnnealMR gateMR validChoiceMR evalA
        ExecMR RetRelMR UnwRelMR))
    (lmPositive : PositiveWitness
      (ModeParamStepRel.ofAnnealEvalGated toAnnealLM gateLM validChoiceLM evalA
        ExecLM RetRelLM UnwRelLM))
    (mrFault : FaultEquivWitness
      (ModeParamStepRel.ofAnnealEvalGated toAnnealMR gateMR validChoiceMR evalA
        ExecMR RetRelMR UnwRelMR))
    (lmFault : FaultEquivWitness
      (ModeParamStepRel.ofAnnealEvalGated toAnnealLM gateLM validChoiceLM evalA
        ExecLM RetRelLM UnwRelLM))
    (hmMR : mrFault.m = mrPositive.m) (hmLM : lmFault.m = lmPositive.m)
    (mrMode? : Option (ModeSensitivityWitness
      (ModeParamStepRel.ofAnnealEvalGated toAnnealMR gateMR validChoiceMR evalA
        ExecMR RetRelMR UnwRelMR)) := none)
    (lmMode? : Option (ModeSensitivityWitness
      (ModeParamStepRel.ofAnnealEvalGated toAnnealLM gateLM validChoiceLM evalA
        ExecLM RetRelLM UnwRelLM)) := none)
    (mrRevTotal? : Option (PLift
      (ModeParamStepRel.ofAnnealEvalGated toAnnealMR gateMR validChoiceMR evalA
        ExecMR RetRelMR UnwRelMR).ReverseTotal) := none)
    (lmRevTotal? : Option (PLift
      (ModeParamStepRel.ofAnnealEvalGated toAnnealLM gateLM validChoiceLM evalA
        ExecLM RetRelLM UnwRelLM).ReverseTotal) := none) :
    DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR ChoiceMR
      RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM :=
  let mrSim :=
    ModeStepSim.fromAnnealEvalGated toAnnealMR gateMR validChoiceMR evalA
      ExecMR RetRelMR UnwRelMR fwdMR revMR mrRevTotal?
  let lmSim :=
    ModeStepSim.fromAnnealEvalGated toAnnealLM gateLM validChoiceLM evalA
      ExecLM RetRelLM UnwRelLM fwdLM revLM lmRevTotal?
  { codec := codec
    repMR := repMR
    repLM := repLM
    mrRel :=
      ModeParamStepRel.ofAnnealEvalGated toAnnealMR gateMR validChoiceMR evalA
        ExecMR RetRelMR UnwRelMR
    lmRel :=
      ModeParamStepRel.ofAnnealEvalGated toAnnealLM gateLM validChoiceLM evalA
        ExecLM RetRelLM UnwRelLM
    mrSim := mrSim
    lmSim := lmSim
    mr_ret_codec := hRetMR
    lm_ret_codec := hRetLM
    toAnnealMR := toAnnealMR
    toAnnealLM := toAnnealLM
    ExecAnneal := fun mA p q out => evalA mA p q = out
    anneal_exec_coherent :=
      ⟨fun m p q out =>
        (ModeParamStepRel.ofAnnealEvalGated_wellFormedAnneal_iff toAnnealMR
          gateMR validChoiceMR evalA ExecMR RetRelMR UnwRelMR
          (hChoiceMR m p q)).2 out,
       fun m p q out =>
        (ModeParamStepRel.ofAnnealEvalGated_wellFormedAnneal_iff toAnnealLM
          gateLM validChoiceLM evalA ExecLM RetRelLM UnwRelLM
          (hChoiceLM m p q)).2 out⟩
    mrPositive := mrPositive
    lmPositive := lmPositive
    mrFault := mrFault
    lmFault := lmFault
    mrFlip :=
      FlipDirectionWitness.ofFaultAndMode mrSim mrPositive mrFault hmMR mrMode?
    lmFlip :=
      FlipDirectionWitness.ofFaultAndMode lmSim lmPositive lmFault hmLM
        lmMode? }

/-- Every bundle built with `fromEquivGated` satisfies `ProductiveAnneal` on
both authorities, directly discharging Section 4.5 choice productivity from
`hChoiceMR` and `hChoiceLM`. -/
theorem fromEquivGated_productiveAnneal (codec : CodecLaws RetA Rep)
    (repMR : RetMR → Rep) (repLM : RetLM → Rep)
    (evalA : ModeA → Prog → Query → ExecOutcome4 RetA UnwA)
    (toAnnealMR : ModeMR → ModeA) (toAnnealLM : ModeLM → ModeA)
    (gateMR : ModeMR → Prog → Query → Prop)
    (gateLM : ModeLM → Prog → Query → Prop)
    (validChoiceMR : ModeMR → Prog → Query → ChoiceMR → Prop)
    (validChoiceLM : ModeLM → Prog → Query → ChoiceLM → Prop)
    (hChoiceMR : ∀ m p q, ∃ c, validChoiceMR m p q c)
    (hChoiceLM : ∀ m p q, ∃ c, validChoiceLM m p q c)
    (ExecMR :
      ModeMR → Prog → Query → ChoiceMR → ExecOutcome4 RetMR UnwMR → Prop)
    (ExecLM :
      ModeLM → Prog → Query → ChoiceLM → ExecOutcome4 RetLM UnwLM → Prop)
    (RetRelMR : RetA → RetMR → Prop) (UnwRelMR : UnwA → UnwMR → Prop)
    (RetRelLM : RetA → RetLM → Prop) (UnwRelLM : UnwA → UnwLM → Prop)
    (hRetMR : ∀ a r, RetRelMR a r → repMR r = codec.encode a)
    (hRetLM : ∀ a r, RetRelLM a r → repLM r = codec.encode a)
    (fwdMR : ∀ m p q c out, gateMR m p q → ExecMR m p q c out →
      validChoiceMR m p q c ∧
      ChoiceCoupledOutcomeRel RetRelMR UnwRelMR (evalA (toAnnealMR m) p q) out)
    (revMR : ∀ m p q c k, gateMR m p q → validChoiceMR m p q c →
      evalA (toAnnealMR m) p q = .fault k → ExecMR m p q c (.fault k))
    (fwdLM : ∀ m p q c out, gateLM m p q → ExecLM m p q c out →
      validChoiceLM m p q c ∧
      ChoiceCoupledOutcomeRel RetRelLM UnwRelLM (evalA (toAnnealLM m) p q) out)
    (revLM : ∀ m p q c k, gateLM m p q → validChoiceLM m p q c →
      evalA (toAnnealLM m) p q = .fault k → ExecLM m p q c (.fault k))
    (mrPositive : PositiveWitness
      (ModeParamStepRel.ofAnnealEvalGated toAnnealMR gateMR validChoiceMR evalA
        ExecMR RetRelMR UnwRelMR))
    (lmPositive : PositiveWitness
      (ModeParamStepRel.ofAnnealEvalGated toAnnealLM gateLM validChoiceLM evalA
        ExecLM RetRelLM UnwRelLM))
    (mrFault : FaultEquivWitness
      (ModeParamStepRel.ofAnnealEvalGated toAnnealMR gateMR validChoiceMR evalA
        ExecMR RetRelMR UnwRelMR))
    (lmFault : FaultEquivWitness
      (ModeParamStepRel.ofAnnealEvalGated toAnnealLM gateLM validChoiceLM evalA
        ExecLM RetRelLM UnwRelLM))
    (hmMR : mrFault.m = mrPositive.m) (hmLM : lmFault.m = lmPositive.m)
    (mrMode? : Option (ModeSensitivityWitness
      (ModeParamStepRel.ofAnnealEvalGated toAnnealMR gateMR validChoiceMR evalA
        ExecMR RetRelMR UnwRelMR)) := none)
    (lmMode? : Option (ModeSensitivityWitness
      (ModeParamStepRel.ofAnnealEvalGated toAnnealLM gateLM validChoiceLM evalA
        ExecLM RetRelLM UnwRelLM)) := none)
    (mrRevTotal? : Option (PLift
      (ModeParamStepRel.ofAnnealEvalGated toAnnealMR gateMR validChoiceMR evalA
        ExecMR RetRelMR UnwRelMR).ReverseTotal) := none)
    (lmRevTotal? : Option (PLift
      (ModeParamStepRel.ofAnnealEvalGated toAnnealLM gateLM validChoiceLM evalA
        ExecLM RetRelLM UnwRelLM).ReverseTotal) := none) :
    let B :=
      fromEquivGated codec repMR repLM evalA toAnnealMR toAnnealLM gateMR
        gateLM validChoiceMR validChoiceLM hChoiceMR hChoiceLM ExecMR ExecLM
        RetRelMR UnwRelMR RetRelLM UnwRelLM hRetMR hRetLM fwdMR revMR fwdLM
        revLM mrPositive lmPositive mrFault lmFault hmMR hmLM mrMode? lmMode?
        mrRevTotal? lmRevTotal?
    B.mrRel.ProductiveAnneal ∧ B.lmRel.ProductiveAnneal :=
  ⟨fun m p q _ =>
      let ⟨c, hc⟩ := hChoiceMR m p q
      ⟨c, evalA (toAnnealMR m) p q, hc, rfl⟩,
   fun m p q _ =>
      let ⟨c, hc⟩ := hChoiceLM m p q
      ⟨c, evalA (toAnnealLM m) p q, hc, rfl⟩⟩

/--
`fromEquiv` specialized to deterministic authority evaluators `evalMR` /
`evalLM`: the only hypotheses are that the evaluators' outcomes are coupled
with the Anneal evaluator on every gated input and choice. Reverse totality is
recorded for both simulations.
-/
def fromDetEquiv (codec : CodecLaws RetA Rep) (repMR : RetMR → Rep)
    (repLM : RetLM → Rep)
    (evalA : ModeA → Prog → Query → ExecOutcome4 RetA UnwA)
    (toAnnealMR : ModeMR → ModeA) (toAnnealLM : ModeLM → ModeA)
    (gateMR : ModeMR → Prog → Query → Prop)
    (gateLM : ModeLM → Prog → Query → Prop)
    (evalMR : ModeMR → Prog → Query → ChoiceMR → ExecOutcome4 RetMR UnwMR)
    (evalLM : ModeLM → Prog → Query → ChoiceLM → ExecOutcome4 RetLM UnwLM)
    (RetRelMR : RetA → RetMR → Prop) (UnwRelMR : UnwA → UnwMR → Prop)
    (RetRelLM : RetA → RetLM → Prop) (UnwRelLM : UnwA → UnwLM → Prop)
    (hRetMR : ∀ a r, RetRelMR a r → repMR r = codec.encode a)
    (hRetLM : ∀ a r, RetRelLM a r → repLM r = codec.encode a)
    (hMR : ∀ m p q c, gateMR m p q →
      ChoiceCoupledOutcomeRel RetRelMR UnwRelMR (evalA (toAnnealMR m) p q)
        (evalMR m p q c))
    (hLM : ∀ m p q c, gateLM m p q →
      ChoiceCoupledOutcomeRel RetRelLM UnwRelLM (evalA (toAnnealLM m) p q)
        (evalLM m p q c))
    (mrPositive : PositiveWitness
      (ModeParamStepRel.ofAnnealEval toAnnealMR gateMR evalA
        (fun m p q c out => evalMR m p q c = out) RetRelMR UnwRelMR))
    (lmPositive : PositiveWitness
      (ModeParamStepRel.ofAnnealEval toAnnealLM gateLM evalA
        (fun m p q c out => evalLM m p q c = out) RetRelLM UnwRelLM))
    (mrFault : FaultEquivWitness
      (ModeParamStepRel.ofAnnealEval toAnnealMR gateMR evalA
        (fun m p q c out => evalMR m p q c = out) RetRelMR UnwRelMR))
    (lmFault : FaultEquivWitness
      (ModeParamStepRel.ofAnnealEval toAnnealLM gateLM evalA
        (fun m p q c out => evalLM m p q c = out) RetRelLM UnwRelLM))
    (hmMR : mrFault.m = mrPositive.m) (hmLM : lmFault.m = lmPositive.m)
    (mrMode? : Option (ModeSensitivityWitness
      (ModeParamStepRel.ofAnnealEval toAnnealMR gateMR evalA
        (fun m p q c out => evalMR m p q c = out) RetRelMR UnwRelMR)) := none)
    (lmMode? : Option (ModeSensitivityWitness
      (ModeParamStepRel.ofAnnealEval toAnnealLM gateLM evalA
        (fun m p q c out => evalLM m p q c = out) RetRelLM UnwRelLM)) := none) :
    DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR ChoiceMR
      RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM :=
  fromEquiv codec repMR repLM evalA toAnnealMR toAnnealLM gateMR gateLM
    (fun m p q c out => evalMR m p q c = out)
    (fun m p q c out => evalLM m p q c = out)
    RetRelMR UnwRelMR RetRelLM UnwRelLM hRetMR hRetLM
    (fun m p q c out hg hR => by
      have hR' : evalMR m p q c = out := hR
      rw [← hR']
      exact hMR m p q c hg)
    (fun m p q c k hg hA => ((hMR m p q c hg).fault_iff k).mp hA)
    (fun m p q c out hg hR => by
      have hR' : evalLM m p q c = out := hR
      rw [← hR']
      exact hLM m p q c hg)
    (fun m p q c k hg hA => ((hLM m p q c hg).fault_iff k).mp hA)
    mrPositive lmPositive mrFault lmFault hmMR hmLM mrMode? lmMode?
    (some ⟨fun m p q c outA hg hA =>
      ⟨evalMR m p q c, rfl, by
        have hA' : evalA (toAnnealMR m) p q = outA := hA
        rw [← hA']
        exact hMR m p q c hg⟩⟩)
    (some ⟨fun m p q c outA hg hA =>
      ⟨evalLM m p q c, rfl, by
        have hA' : evalA (toAnnealLM m) p q = outA := hA
        rw [← hA']
        exact hLM m p q c hg⟩⟩)

/--
Relational evaluation-equivalence constructor for nondeterministic Anneal
models: unlike `fromEquiv` (which assumes a deterministic, choice-independent
`evalA`), `ExecAnneal` and the choice-coupled Anneal executions `ExecAMR` /
`ExecALM` are arbitrary relations, supporting nondeterministic modes such as
NaN payload draws or allocator address draws.
-/
def fromRelEquiv (codec : CodecLaws RetA Rep) (repMR : RetMR → Rep)
    (repLM : RetLM → Rep)
    (ExecAnneal : ModeA → Prog → Query → ExecOutcome4 RetA UnwA → Prop)
    (toAnnealMR : ModeMR → ModeA) (toAnnealLM : ModeLM → ModeA)
    (mrRel : ModeParamStepRel ModeMR Prog Query ChoiceMR RetA RetMR UnwA UnwMR)
    (lmRel : ModeParamStepRel ModeLM Prog Query ChoiceLM RetA RetLM UnwA UnwLM)
    (hRetMR : ∀ a r, mrRel.RetRel a r → repMR r = codec.encode a)
    (hRetLM : ∀ a r, lmRel.RetRel a r → repLM r = codec.encode a)
    (hCohMR : ∀ m p q out,
      (∃ c, mrRel.ExecA m p q c out) ↔ ExecAnneal (toAnnealMR m) p q out)
    (hCohLM : ∀ m p q out,
      (∃ c, lmRel.ExecA m p q c out) ↔ ExecAnneal (toAnnealLM m) p q out)
    (fwdMR : mrRel.ForwardTotal) (revMR : mrRel.ReverseFaultTotal)
    (fwdLM : lmRel.ForwardTotal) (revLM : lmRel.ReverseFaultTotal)
    (mrPositive : PositiveWitness mrRel) (lmPositive : PositiveWitness lmRel)
    (mrFault : FaultEquivWitness mrRel) (lmFault : FaultEquivWitness lmRel)
    (hmMR : mrFault.m = mrPositive.m) (hmLM : lmFault.m = lmPositive.m)
    (mrMode? : Option (ModeSensitivityWitness mrRel) := none)
    (lmMode? : Option (ModeSensitivityWitness lmRel) := none)
    (mrRevTotal? : Option (PLift mrRel.ReverseTotal) := none)
    (lmRevTotal? : Option (PLift lmRel.ReverseTotal) := none) :
    DualCorrespondenceBundle ModeA Prog Query RetA UnwA Rep ModeMR ChoiceMR
      RetMR UnwMR ModeLM ChoiceLM RetLM UnwLM :=
  let mrSim : ModeStepSim mrRel :=
    { forward_total := fwdMR
      reverse_fault_total := revMR
      reverse_total? := mrRevTotal? }
  let lmSim : ModeStepSim lmRel :=
    { forward_total := fwdLM
      reverse_fault_total := revLM
      reverse_total? := lmRevTotal? }
  { codec := codec
    repMR := repMR
    repLM := repLM
    mrRel := mrRel
    lmRel := lmRel
    mrSim := mrSim
    lmSim := lmSim
    mr_ret_codec := hRetMR
    lm_ret_codec := hRetLM
    toAnnealMR := toAnnealMR
    toAnnealLM := toAnnealLM
    ExecAnneal := ExecAnneal
    anneal_exec_coherent := ⟨hCohMR, hCohLM⟩
    mrPositive := mrPositive
    lmPositive := lmPositive
    mrFault := mrFault
    lmFault := lmFault
    mrFlip :=
      FlipDirectionWitness.ofFaultAndMode mrSim mrPositive mrFault hmMR mrMode?
    lmFlip :=
      FlipDirectionWitness.ofFaultAndMode lmSim lmPositive lmFault hmLM
        lmMode? }

end DualCorrespondenceBundle

/-! ## 6. Worked instance: mode-sensitive checked division

A small closed instance exercising every part of the abstraction. Programs are
trivial, queries are `(dividend, divisor)` pairs, and the mode selects whether
division by zero is undefined behavior (`strict = true`) or returns `0`
(`strict = false`). Both authorities run the same evaluator, and the shared
representation of a return value is the value itself.
-/

namespace Example

/-- Mode-sensitive division: division by zero is undefined behavior in strict
mode and returns `0` otherwise. -/
def evalDiv (strict : Bool) (_p : Unit) (q : Nat × Nat) :
    ExecOutcome4 Nat Unit :=
  match q.2, strict with
  | 0, true => .fault .undefined
  | 0, false => .normal 0
  | d + 1, _ => .normal (q.1 / (d + 1))

/-- Dual-authority bundle of `evalDiv` against two copies of itself. -/
def divBundle :
    DualCorrespondenceBundle Bool Unit (Nat × Nat) Nat Unit Nat Bool Unit Nat
      Unit Bool Unit Nat Unit :=
  DualCorrespondenceBundle.fromDetEquiv (CodecLaws.id Nat) (fun r => r)
    (fun r => r) evalDiv (fun m => m) (fun m => m) (fun _ _ _ => True)
    (fun _ _ _ => True) (fun m p q _ => evalDiv m p q)
    (fun m p q _ => evalDiv m p q) (fun a r => a = r) (fun _ _ => True)
    (fun a r => a = r) (fun _ _ => True) (fun _ _ h => h.symm)
    (fun _ _ h => h.symm)
    (fun _ _ _ _ _ =>
      ChoiceCoupledOutcomeRel.refl (fun _ => rfl) (fun _ => True.intro) _)
    (fun _ _ _ _ _ =>
      ChoiceCoupledOutcomeRel.refl (fun _ => rfl) (fun _ => True.intro) _)
    (PositiveWitness.ofAnnealEval true () (4, 2) () 2 2 True.intro rfl rfl rfl)
    (PositiveWitness.ofAnnealEval true () (4, 2) () 2 2 True.intro rfl rfl rfl)
    (FaultEquivWitness.ofAnnealEval true () (1, 0) () .undefined True.intro rfl
      rfl)
    (FaultEquivWitness.ofAnnealEval true () (1, 0) () .undefined True.intro rfl
      rfl)
    rfl rfl
    (some
      { m₁ := true, m₂ := false, p := (), q := (1, 0), c := ()
        gate₁ := True.intro, gate₂ := True.intro
        flips :=
          ⟨.fault .undefined, .fault .undefined, rfl, rfl,
            ChoiceCoupledOutcomeRel.ofFault .undefined,
            fun _ h => (by cases h), fun _ h => (by cases h)⟩ })
    (some
      { m₁ := true, m₂ := false, p := (), q := (1, 0), c := ()
        gate₁ := True.intro, gate₂ := True.intro
        flips :=
          ⟨.fault .undefined, .fault .undefined, rfl, rfl,
            ChoiceCoupledOutcomeRel.ofFault .undefined,
            fun _ h => (by cases h), fun _ h => (by cases h)⟩ })

/-- The worked bundle records mode sensitivity for both authorities. -/
theorem divBundle_modeSensitive :
    divBundle.mrFlip.modeSensitivity?.isSome = true ∧
      divBundle.lmFlip.modeSensitivity?.isSome = true :=
  ⟨rfl, rfl⟩

/-- The worked bundle records reverse totality for both simulations. -/
theorem divBundle_reverseTotal :
    divBundle.mrSim.reverse_total?.isSome = true ∧
      divBundle.lmSim.reverse_total?.isSome = true :=
  ⟨rfl, rfl⟩

/-- In the worked bundle both authorities fault on division by zero in strict
mode, and neither does in lax mode. -/
theorem divBundle_fault_iff (m : Bool) (n : Nat) :
    (∃ c, divBundle.mrRel.ExecR m () (n, 0) c (.fault .undefined)) ↔
      (∃ c, divBundle.lmRel.ExecR m () (n, 0) c (.fault .undefined)) :=
  divBundle.crossAuthorityFaultEquiv rfl True.intro True.intro .undefined

/-! ### Nondeterministic NaN-payload instance (`fromRelEquiv`)

Exercises relational (nondeterministic) Anneal executions, a non-identity
`CodecLaws` with a non-trivial `ValidRep`, distinct authority mode and return
types (`ModeMR := Unit × Bool`, `ModeLM := Bool × Unit`, `RetMR := Nat × Bool`,
`RetLM := Option Nat`), choice coupling over `Bool`, and a normal-outcome
mode-sensitivity witness separating deterministic (`false`) from
nondeterministic (`true`) NaN payload selection.
-/

/-- Canonical representation codec `(n, true)` for `Nat` into `Nat × Bool`. -/
def nanRepCodec : CodecLaws Nat (Nat × Bool) where
  encode := fun n => (n, true)
  decode := fun p => if p.2 then some p.1 else none
  ValidRep := fun p => p.2 = true
  decode_encode := fun _ => rfl
  encode_valid := fun _ => rfl
  encode_decode_of_valid := fun p a hv hd => by
    cases p with
    | mk n b =>
      have hb : b = true := hv
      rw [hb] at hd ⊢
      have ha : n = a := Option.some.inj hd
      rw [ha]

/-- Choice-indexed relational NaN execution: `q = 0` is UB; `q = 1` returns
canonical payload `0` when `c = false` and alternate payload `1` when
`nondet = true` and `c = true`; `q = n + 2` returns `n + 2` when `c = false`. -/
def nanExecChoice (nondet : Bool) (_p : Unit) (q : Nat) (c : Bool)
    (out : ExecOutcome4 Nat Unit) : Prop :=
  match q with
  | 0 => c = false ∧ out = .fault .undefined
  | 1 =>
    (c = false ∧ out = .normal 0) ∨
      (nondet = true ∧ c = true ∧ out = .normal 1)
  | n + 2 => c = false ∧ out = .normal (n + 2)

/-- Aggregate nondeterministic Anneal executions of the NaN model. -/
def nanExecAnneal (nondet : Bool) (p : Unit) (q : Nat)
    (out : ExecOutcome4 Nat Unit) : Prop :=
  ∃ c : Bool, nanExecChoice nondet p q c out

/-- `MiniRust`-side step relation with `ModeMR := Unit × Bool` and
`RetMR := Nat × Bool`. -/
def nanMrRel :
    ModeParamStepRel (Unit × Bool) Unit Nat Bool Nat (Nat × Bool) Unit Unit
    where
  SupportGate := fun _ _ _ => True
  ExecA := fun m p q c out => nanExecChoice m.2 p q c out
  ExecR := fun m p q c out =>
    match out with
    | .normal r => r.2 = true ∧ nanExecChoice m.2 p q c (.normal r.1)
    | .unwind u => nanExecChoice m.2 p q c (.unwind u)
    | .fault k => nanExecChoice m.2 p q c (.fault k)
    | .diverge => nanExecChoice m.2 p q c .diverge
  RetRel := fun a r => r = (a, true)
  UnwRel := fun _ _ => True

/-- `LeanMiri`-side step relation with `ModeLM := Bool × Unit` and
`RetLM := Option Nat`. -/
def nanLmRel :
    ModeParamStepRel (Bool × Unit) Unit Nat Bool Nat (Option Nat) Unit Unit
    where
  SupportGate := fun _ _ _ => True
  ExecA := fun m p q c out => nanExecChoice m.1 p q c out
  ExecR := fun m p q c out =>
    match out with
    | .normal (some n) => nanExecChoice m.1 p q c (.normal n)
    | .normal none => False
    | .unwind u => nanExecChoice m.1 p q c (.unwind u)
    | .fault k => nanExecChoice m.1 p q c (.fault k)
    | .diverge => nanExecChoice m.1 p q c .diverge
  RetRel := fun a r => r = some a
  UnwRel := fun _ _ => True

/-- `MiniRust` forward totality for `nanMrRel`. -/
theorem nanMrRel_forward : nanMrRel.ForwardTotal := by
  intro m p q c outR _ hR
  cases outR with
  | normal r =>
    cases r with
    | mk n b =>
      obtain ⟨hb, hch⟩ := hR
      have hb' : b = true := hb
      rw [hb']
      exact ⟨.normal n, hch, ChoiceCoupledOutcomeRel.ofNormal rfl⟩
  | unwind u =>
    exact ⟨.unwind u, hR, ChoiceCoupledOutcomeRel.ofUnwind True.intro⟩
  | fault k => exact ⟨.fault k, hR, ChoiceCoupledOutcomeRel.ofFault k⟩
  | diverge => exact ⟨.diverge, hR, ChoiceCoupledOutcomeRel.ofDiverge⟩

/-- `LeanMiri` forward totality for `nanLmRel`. -/
theorem nanLmRel_forward : nanLmRel.ForwardTotal := by
  intro m p q c outR _ hR
  cases outR with
  | normal r =>
    cases r with
    | none => exact False.elim hR
    | some n => exact ⟨.normal n, hR, ChoiceCoupledOutcomeRel.ofNormal rfl⟩
  | unwind u =>
    exact ⟨.unwind u, hR, ChoiceCoupledOutcomeRel.ofUnwind True.intro⟩
  | fault k => exact ⟨.fault k, hR, ChoiceCoupledOutcomeRel.ofFault k⟩
  | diverge => exact ⟨.diverge, hR, ChoiceCoupledOutcomeRel.ofDiverge⟩

/-- `MiniRust` reverse totality for `nanMrRel`. -/
theorem nanMrRel_reverse : nanMrRel.ReverseTotal := by
  intro m p q c outA _ hA
  cases outA with
  | normal a =>
    exact ⟨.normal (a, true), ⟨rfl, hA⟩, ChoiceCoupledOutcomeRel.ofNormal rfl⟩
  | unwind u =>
    exact ⟨.unwind u, hA, ChoiceCoupledOutcomeRel.ofUnwind True.intro⟩
  | fault k => exact ⟨.fault k, hA, ChoiceCoupledOutcomeRel.ofFault k⟩
  | diverge => exact ⟨.diverge, hA, ChoiceCoupledOutcomeRel.ofDiverge⟩

/-- `LeanMiri` reverse totality for `nanLmRel`. -/
theorem nanLmRel_reverse : nanLmRel.ReverseTotal := by
  intro m p q c outA _ hA
  cases outA with
  | normal a =>
    exact ⟨.normal (some a), hA, ChoiceCoupledOutcomeRel.ofNormal rfl⟩
  | unwind u =>
    exact ⟨.unwind u, hA, ChoiceCoupledOutcomeRel.ofUnwind True.intro⟩
  | fault k => exact ⟨.fault k, hA, ChoiceCoupledOutcomeRel.ofFault k⟩
  | diverge => exact ⟨.diverge, hA, ChoiceCoupledOutcomeRel.ofDiverge⟩

/-- Nondeterministic dual-authority NaN bundle built via `fromRelEquiv`. -/
def nanBundle :
    DualCorrespondenceBundle Bool Unit Nat Nat Unit (Nat × Bool) (Unit × Bool)
      Bool (Nat × Bool) Unit (Bool × Unit) Bool (Option Nat) Unit :=
  DualCorrespondenceBundle.fromRelEquiv nanRepCodec (fun r => r)
    (fun r => match r with | some n => (n, true) | none => (0, false))
    nanExecAnneal (fun m => m.2) (fun m => m.1) nanMrRel nanLmRel
    (fun _ _ h => h)
    (fun _ _ h => by rw [h]; rfl)
    (fun _ _ _ _ => Iff.rfl)
    (fun _ _ _ _ => Iff.rfl)
    nanMrRel_forward (fun _ _ _ _ _ _ hA => hA)
    nanLmRel_forward (fun _ _ _ _ _ _ hA => hA)
    (PositiveWitness.ofReturns ((), true) () 2 false 2 (2, true) True.intro
      (fun _ _ h => by cases h.2) ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ rfl)
    (PositiveWitness.ofReturns (true, ()) () 2 false 2 (some 2) True.intro
      (fun _ _ h => by cases h.2) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ rfl)
    { m := ((), true), p := (), q := 0, c := false, kind := .undefined
      gate := True.intro, execA := ⟨rfl, rfl⟩, execR := ⟨rfl, rfl⟩ }
    { m := (true, ()), p := (), q := 0, c := false, kind := .undefined
      gate := True.intro, execA := ⟨rfl, rfl⟩, execR := ⟨rfl, rfl⟩ }
    rfl rfl
    (some
      { m₁ := ((), true), m₂ := ((), false), p := (), q := 1, c := true
        gate₁ := True.intro, gate₂ := True.intro
        flips :=
          ⟨.normal 1, .normal (1, true), Or.inr ⟨rfl, rfl, rfl⟩,
            ⟨rfl, Or.inr ⟨rfl, rfl, rfl⟩⟩, ChoiceCoupledOutcomeRel.ofNormal rfl,
            (fun _ h => by
              cases h with
              | inl h0 => cases h0.2
              | inr h1 => cases h1.1),
            (fun _ h => by
              cases h.2 with
              | inl h0 => cases h0.2
              | inr h1 => cases h1.1)⟩ })
    (some
      { m₁ := (true, ()), m₂ := (false, ()), p := (), q := 1, c := true
        gate₁ := True.intro, gate₂ := True.intro
        flips :=
          ⟨.normal 1, .normal (some 1), Or.inr ⟨rfl, rfl, rfl⟩,
            Or.inr ⟨rfl, rfl, rfl⟩, ChoiceCoupledOutcomeRel.ofNormal rfl,
            (fun _ h => by
              cases h with
              | inl h0 => cases h0.2
              | inr h1 => cases h1.1),
            (fun _ h => by
              cases h with
              | inl h0 => cases h0.2
              | inr h1 => cases h1.1)⟩ })
    (some ⟨nanMrRel_reverse⟩) (some ⟨nanLmRel_reverse⟩)

/-- `nanBundle` is genuinely nondeterministic at `q = 1` in nondet mode. -/
theorem nanBundle_nondet :
    nanBundle.ExecAnneal true () 1 (.normal 0) ∧
      nanBundle.ExecAnneal true () 1 (.normal 1) :=
  ⟨⟨false, Or.inl ⟨rfl, rfl⟩⟩, ⟨true, Or.inr ⟨rfl, rfl, rfl⟩⟩⟩

/-- `nanBundle` satisfies cross-authority well-formedness equivalence. -/
theorem nanBundle_crossAuthorityWellFormed (m : Bool) (q : Nat) :
    nanBundle.mrRel.WellFormedRef ((), m) () q ↔
      nanBundle.lmRel.WellFormedRef (m, ()) () q :=
  (nanBundle.crossAuthorityWellFormedEquiv rfl True.intro True.intro).2.2

/--
`nanBundle` satisfies cross-authority normal-outcome equivalence at `m = true,
q = 1` where `ExecAnneal` is genuinely nondeterministic (`nanBundle_nondet`), so
`threeWayNormalAgreement` (`hdet`) does not apply while
`crossAuthorityNormalEquiv` does.
-/
theorem nanBundle_crossAuthorityNormalEquiv (a : Nat) :
    (∃ c r, nanBundle.mrRel.ExecR ((), true) () 1 c (.normal r) ∧
        nanBundle.mrRel.RetRel a r) ↔
      (∃ c r, nanBundle.lmRel.ExecR (true, ()) () 1 c (.normal r) ∧
        nanBundle.lmRel.RetRel a r) :=
  ((nanBundle.crossAuthorityNormalEquiv rfl True.intro True.intro
    nanMrRel_reverse nanLmRel_reverse).1 a).2.2

/-- Choice-restricted reference execution of `evalDiv`: only `c = false` is a
valid choice (`c = true` has no transitions, so `fromEquiv` would fail fault
reflection at `c = true`, whereas `fromEquivGated` handles it cleanly). -/
def gatedDivExecR (m : Bool) (p : Unit) (q : Nat × Nat) (c : Bool)
    (out : ExecOutcome4 Nat Unit) : Prop :=
  c = false ∧ evalDiv m p q = out

/-- Choice-gated division bundle built via `fromEquivGated`. -/
def gatedDivBundle :
    DualCorrespondenceBundle Bool Unit (Nat × Nat) Nat Unit Nat Bool Bool Nat
      Unit Bool Bool Nat Unit :=
  DualCorrespondenceBundle.fromEquivGated (CodecLaws.id Nat) (fun r => r)
    (fun r => r) evalDiv (fun m => m) (fun m => m) (fun _ _ _ => True)
    (fun _ _ _ => True) (fun _ _ _ c => c = false) (fun _ _ _ c => c = false)
    (fun _ _ _ => ⟨false, rfl⟩) (fun _ _ _ => ⟨false, rfl⟩)
    gatedDivExecR gatedDivExecR (fun a r => a = r) (fun _ _ => True)
    (fun a r => a = r) (fun _ _ => True) (fun _ _ h => h.symm)
    (fun _ _ h => h.symm)
    (fun _ _ _ _ _ _ hR =>
      ⟨hR.1, hR.2 ▸ ChoiceCoupledOutcomeRel.refl (fun _ => rfl)
        (fun _ => True.intro) _⟩)
    (fun _ _ _ _ _ _ hvc hA => ⟨hvc, hA⟩)
    (fun _ _ _ _ _ _ hR =>
      ⟨hR.1, hR.2 ▸ ChoiceCoupledOutcomeRel.refl (fun _ => rfl)
        (fun _ => True.intro) _⟩)
    (fun _ _ _ _ _ _ hvc hA => ⟨hvc, hA⟩)
    (PositiveWitness.ofAnnealEvalGated true () (4, 2) false 2 2 True.intro rfl
      rfl ⟨rfl, rfl⟩ rfl)
    (PositiveWitness.ofAnnealEvalGated true () (4, 2) false 2 2 True.intro rfl
      rfl ⟨rfl, rfl⟩ rfl)
    (FaultEquivWitness.ofAnnealEvalGated true () (1, 0) false .undefined
      True.intro rfl rfl ⟨rfl, rfl⟩)
    (FaultEquivWitness.ofAnnealEvalGated true () (1, 0) false .undefined
      True.intro rfl rfl ⟨rfl, rfl⟩)
    rfl rfl

end Example

end Anneal.DualCorrespondenceBundle
