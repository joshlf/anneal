import Trusted
import Anneal.EffectWP
import Anneal.ITreeWP
import Anneal.Memory
import Anneal.UnsafeObligations

namespace Anneal.SepLogic

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.EffectWP
open Anneal.ITreeWP
open Anneal.Memory
open Anneal.UnsafeObligations

/-!
Disjoint-footprint separation logic (`Footprint`, `PartialHeap`, `SepProp`),
Tree Borrows and lifetime ownership tokens (`PointsTo`, `BorrowToken`,
`LifetimeToken`), pointer and unaligned-wrapper typestate invariants
(`PtrInvariant`, `UnalignInvariant`), and footprint-grounded ITree framing
(`dwlp_frame_disjoint`, `dwp_frame_disjoint`,
`statefulVerificationResult_frame_disjoint`) (`#100`, `#102`, `#103`).

Rather than duplicating assertions across a non-disjoint `Memory → Prop` layer
and a separate `PartialHeap → Prop` layer, this module defines a single
genuine disjoint-footprint separation logic `SepProp := PartialHeap → Prop` and
projects assertions onto full `Memory` states via `SepProp.atFootprint` and
`SepProp.holdsIn`.
-/

/-! ## 1. Spatial Footprints, Partial Heaps, and `SepProp` Connectives -/

/-- Spatial footprint of owned `(allocId, offset)` cells and provenance tags. -/
structure Footprint : Type where
  /-- Owned `(allocId, offset)` address cells. -/
  addrs : List (Nat × Nat) := []
  /-- Owned Tree Borrows and lifetime provenance tags. -/
  tags : List Nat := []
  deriving DecidableEq, Repr

/-- Empty spatial footprint. -/
def Footprint.empty : Footprint := {}

/-- Union of two spatial footprints by list concatenation. -/
def Footprint.union (fp₁ fp₂ : Footprint) : Footprint :=
  { addrs := fp₁.addrs ++ fp₂.addrs, tags := fp₁.tags ++ fp₂.tags }

/-- Two footprints are disjoint when they share no address cells and no tags. -/
def DisjointFootprints (fp₁ fp₂ : Footprint) : Prop :=
  (∀ a, a ∈ fp₁.addrs → a ∉ fp₂.addrs) ∧
  (∀ t, t ∈ fp₁.tags → t ∉ fp₂.tags)

theorem disjointFootprints_symm
    {fp₁ fp₂ : Footprint} (h : DisjointFootprints fp₁ fp₂) :
    DisjointFootprints fp₂ fp₁ :=
  ⟨fun a h₂ h₁ => h.1 a h₁ h₂, fun t h₂ h₁ => h.2 t h₁ h₂⟩

theorem disjointFootprints_empty_left (fp : Footprint) :
    DisjointFootprints .empty fp :=
  ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩

theorem disjointFootprints_empty_right (fp : Footprint) :
    DisjointFootprints fp .empty :=
  disjointFootprints_symm (disjointFootprints_empty_left fp)

/-- Partial heap pairing a `Memory` state with the owned spatial `Footprint`. -/
structure PartialHeap : Type where
  /-- Underlying full machine memory state. -/
  state : Memory
  /-- Spatial footprint owned by this partial heap view. -/
  footprint : Footprint

/--
Relational split of partial heap `h` into `h₁` and `h₂` sharing `h.state` with
disjoint footprints whose union is extensionally `h.footprint`.
-/
def PartialHeapSplit (h h₁ h₂ : PartialHeap) : Prop :=
  h₁.state = h.state ∧
  h₂.state = h.state ∧
  DisjointFootprints h₁.footprint h₂.footprint ∧
  (∀ a, a ∈ h.footprint.addrs ↔ a ∈ h₁.footprint.addrs ∨ a ∈ h₂.footprint.addrs) ∧
  (∀ t, t ∈ h.footprint.tags ↔ t ∈ h₁.footprint.tags ∨ t ∈ h₂.footprint.tags)

theorem partialHeapSplit_comm
    {h h₁ h₂ : PartialHeap} (hs : PartialHeapSplit h h₁ h₂) :
    PartialHeapSplit h h₂ h₁ := by
  rcases hs with ⟨hs₁, hs₂, hdisj, haddrs, htags⟩
  exact ⟨hs₂, hs₁, disjointFootprints_symm hdisj,
         fun a => (haddrs a).trans or_comm,
         fun t => (htags t).trans or_comm⟩

/-- Footprint-aware separation-logic assertion over `PartialHeap`. -/
abbrev SepProp : Type := PartialHeap → Prop

/-- Predicate over full `Memory` states (used by `StatefulClaim`). -/
abbrev HeapPred : Type := Memory → Prop

/-- Evaluate `P : SepProp` on `m` at an explicit footprint `fp`. -/
def SepProp.atFootprint (P : SepProp) (fp : Footprint) : HeapPred :=
  fun m => P ⟨m, fp⟩

/-- Evaluate `P : SepProp` on `m` at some owned footprint in `m`. -/
def SepProp.holdsIn (P : SepProp) : HeapPred :=
  fun m => ∃ fp, P ⟨m, fp⟩

/-- Empty-footprint assertion (`emp`). -/
def emp : SepProp :=
  fun h => h.footprint = .empty

/-- Pure proposition lifted into `SepProp` with an empty footprint (`⌜P⌝`). -/
def pureProp (P : Prop) : SepProp :=
  fun h => P ∧ emp h

/-- Separating conjunction (`P ∗ Q`) enforcing genuine footprint disjointness. -/
def sepConj (P Q : SepProp) : SepProp :=
  fun h => ∃ h₁ h₂, PartialHeapSplit h h₁ h₂ ∧ P h₁ ∧ Q h₂

/-- Separating implication / magic wand (`P -∗ Q`). -/
def sepImp (P Q : SepProp) : SepProp :=
  fun h => ∀ h₁ h₂, PartialHeapSplit h₂ h h₁ → P h₁ → Q h₂

theorem sepConj_comm (P Q : SepProp) (h : PartialHeap) :
    sepConj P Q h ↔ sepConj Q P h :=
  ⟨fun ⟨h₁, h₂, hs, hp, hq⟩ => ⟨h₂, h₁, partialHeapSplit_comm hs, hq, hp⟩,
   fun ⟨h₂, h₁, hs, hq, hp⟩ => ⟨h₁, h₂, partialHeapSplit_comm hs, hp, hq⟩⟩

private theorem sepConj_assoc_mp
    {P Q R : SepProp} {h : PartialHeap} (hl : sepConj (sepConj P Q) R h) :
    sepConj P (sepConj Q R) h := by
  rcases hl with ⟨h₁₂, h₃, ⟨hs₁₂, hs₃, hdisj₁₂_₃, haddrs, htags⟩,
                  ⟨h₁, h₂, ⟨hs₁, hs₂, hdisj₁_₂, haddrs₁₂, htags₁₂⟩, hp, hq⟩, hr⟩
  let h₂₃ : PartialHeap :=
    { state := h.state, footprint := h₂.footprint.union h₃.footprint }
  have hs₁' : h₁.state = h.state := hs₁.trans hs₁₂
  have hs₂' : h₂.state = h.state := hs₂.trans hs₁₂
  have hdisj₂_₃ : DisjointFootprints h₂.footprint h₃.footprint :=
    ⟨fun a ha₂ => hdisj₁₂_₃.1 a ((haddrs₁₂ a).2 (.inr ha₂)),
     fun t ht₂ => hdisj₁₂_₃.2 t ((htags₁₂ t).2 (.inr ht₂))⟩
  have hdisj₁_₂₃ : DisjointFootprints h₁.footprint h₂₃.footprint := by
    refine ⟨fun a ha₁ ha₂₃ => ?_, fun t ht₁ ht₂₃ => ?_⟩
    · simp only [h₂₃, Footprint.union, List.mem_append] at ha₂₃
      rcases ha₂₃ with ha₂ | ha₃
      · exact hdisj₁_₂.1 a ha₁ ha₂
      · exact hdisj₁₂_₃.1 a ((haddrs₁₂ a).2 (.inl ha₁)) ha₃
    · simp only [h₂₃, Footprint.union, List.mem_append] at ht₂₃
      rcases ht₂₃ with ht₂ | ht₃
      · exact hdisj₁_₂.2 t ht₁ ht₂
      · exact hdisj₁₂_₃.2 t ((htags₁₂ t).2 (.inl ht₁)) ht₃
  refine ⟨h₁, h₂₃, ⟨hs₁', rfl, hdisj₁_₂₃, ?_, ?_⟩, hp,
          h₂, h₃, ⟨hs₂', hs₃, hdisj₂_₃, ?_, ?_⟩, hq, hr⟩
  · intro a
    simp only [h₂₃, Footprint.union, List.mem_append]
    rw [haddrs a, haddrs₁₂ a, or_assoc]
  · intro t
    simp only [h₂₃, Footprint.union, List.mem_append]
    rw [htags t, htags₁₂ t, or_assoc]
  · intro a; simp [h₂₃, Footprint.union]
  · intro t; simp [h₂₃, Footprint.union]

theorem sepConj_assoc (P Q R : SepProp) (h : PartialHeap) :
    sepConj (sepConj P Q) R h ↔ sepConj P (sepConj Q R) h := by
  constructor
  · exact sepConj_assoc_mp
  · intro hr
    rw [sepConj_comm] at hr
    rcases hr with ⟨h₂₃, h₁, hs, hqr, hp⟩
    rw [sepConj_comm] at hqr
    have h₁' : sepConj R (sepConj Q P) h :=
      sepConj_assoc_mp ⟨h₂₃, h₁, hs, hqr, hp⟩
    rcases h₁' with ⟨h₃, h₁₂, hs', hr', hqp⟩
    rw [sepConj_comm] at hqp
    exact ⟨h₁₂, h₃, partialHeapSplit_comm hs', hqp, hr'⟩

theorem sepConj_emp_left (P : SepProp) (h : PartialHeap) (hp : P h) :
    sepConj emp P h := by
  refine ⟨⟨h.state, .empty⟩, h, ⟨rfl, rfl, disjointFootprints_empty_left _, ?_, ?_⟩, rfl, hp⟩
  · intro a; simp [Footprint.empty]
  · intro t; simp [Footprint.empty]

theorem sepConj_emp_right (P : SepProp) (h : PartialHeap) (hp : P h) :
    sepConj P emp h :=
  (sepConj_comm emp P h).1 (sepConj_emp_left P h hp)

theorem sepImp_elim
    {P Q : SepProp} {h h₁ h₂ : PartialHeap}
    (hw : sepImp P Q h) (hs : PartialHeapSplit h₂ h h₁) (hp : P h₁) :
    Q h₂ :=
  hw h₁ h₂ hs hp

theorem sepImp_adj (P Q R : SepProp) :
    (∀ h, sepConj P Q h → R h) ↔ (∀ h, P h → sepImp Q R h) :=
  ⟨fun himp h hp h₁ h₂ hs hq => himp h₂ ⟨h, h₁, hs, hp, hq⟩,
   fun hadj h ⟨h₁, h₂, hs, hp, hq⟩ => hadj h₁ hp h₂ h hs hq⟩

/-! ## 2. Spatial Resource Assertions and Exclusivity -/

/-- Active local-slot store of `m.callStack`'s head frame (or `m.callerLocals` when `m.callStack = []`). -/
def memoryLocals (m : Memory) : List LocalValue :=
  match m.callStack with
  | frame :: _ => frame.frame.locals
  | [] => m.callerLocals

/--
Points-to assertion (`rp ↦ v`): allocation `rp.allocId` at `rp.offset` holds
initialized value `v` in `memoryLocals h.state`, with singleton address
footprint `[(rp.allocId, rp.offset)]`.
-/
def PointsTo (rp : RawPtrVal) (v : Value) : SepProp :=
  fun h =>
    readAllocAt? (memoryLocals h.state) rp = some v ∧
    h.footprint = { addrs := [(rp.allocId, rp.offset)], tags := [] }

/--
Tree Borrows ownership token (`BorrowToken rp perm`): tag `rp.tag` targets
`rp.allocId` with permission `perm` in `h.state.borrows`, with singleton tag
footprint `[rp.tag]`.
-/
def BorrowToken (rp : RawPtrVal) (perm : TreeBorrowPerm) : SepProp :=
  fun h =>
    (∃ entry,
      lookupBorrow h.state.borrows rp.tag = some entry ∧
      entry.targetLocal = rp.allocId ∧
      entry.perm = perm) ∧
    h.footprint = { addrs := [], tags := [rp.tag] }

/--
Active lifetime token (`LifetimeToken lft`): tag `lft` is a non-disabled
protector in `h.state.borrows`, with singleton tag footprint `[lft]`.
-/
def LifetimeToken (lft : Nat) : SepProp :=
  fun h =>
    (∃ entry,
      lookupBorrow h.state.borrows lft = some entry ∧
      entry.perm ≠ .disabled) ∧
    h.footprint = { addrs := [], tags := [lft] }

/-- Two `PointsTo` assertions at the same `(allocId, offset)` cannot coexist. -/
theorem pointsTo_star_exclusive
    (rp : RawPtrVal) (v₁ v₂ : Value) (h : PartialHeap) :
    ¬ sepConj (PointsTo rp v₁) (PointsTo rp v₂) h := by
  rintro ⟨h₁, h₂, ⟨_, _, ⟨hdisj, _⟩, _, _⟩, ⟨_, hfp₁⟩, ⟨_, hfp₂⟩⟩
  have hm₁ : (rp.allocId, rp.offset) ∈ h₁.footprint.addrs := by simp [hfp₁]
  have hm₂ : (rp.allocId, rp.offset) ∈ h₂.footprint.addrs := by simp [hfp₂]
  exact hdisj (rp.allocId, rp.offset) hm₁ hm₂

/-- Two `BorrowToken`s for the same provenance tag cannot coexist. -/
theorem borrowToken_star_exclusive
    (rp : RawPtrVal) (p₁ p₂ : TreeBorrowPerm) (h : PartialHeap) :
    ¬ sepConj (BorrowToken rp p₁) (BorrowToken rp p₂) h := by
  rintro ⟨h₁, h₂, ⟨_, _, ⟨_, hdisj⟩, _, _⟩, ⟨_, hfp₁⟩, ⟨_, hfp₂⟩⟩
  have hm₁ : rp.tag ∈ h₁.footprint.tags := by simp [hfp₁]
  have hm₂ : rp.tag ∈ h₂.footprint.tags := by simp [hfp₂]
  exact hdisj rp.tag hm₁ hm₂

/-- Separating conjunction of two `PointsTo` cells entails distinct cells. -/
theorem pointsTo_star_disjoint
    {rp₁ rp₂ : RawPtrVal} {v₁ v₂ : Value} {h : PartialHeap}
    (hsep : sepConj (PointsTo rp₁ v₁) (PointsTo rp₂ v₂) h) :
    (rp₁.allocId, rp₁.offset) ≠ (rp₂.allocId, rp₂.offset) := by
  rcases hsep with ⟨h₁, h₂, ⟨_, _, ⟨hdisj, _⟩, _, _⟩, ⟨_, hfp₁⟩, ⟨_, hfp₂⟩⟩
  intro heq
  have hm₁ : (rp₁.allocId, rp₁.offset) ∈ h₁.footprint.addrs := by simp [hfp₁]
  have hm₂ : (rp₁.allocId, rp₁.offset) ∈ h₂.footprint.addrs := by simp [hfp₂, heq]
  exact hdisj (rp₁.allocId, rp₁.offset) hm₁ hm₂

theorem borrowToken_frozen_hasReadAccess
    {rp : RawPtrVal} {h : PartialHeap}
    (htok : BorrowToken rp .frozen h) :
    HasTreeBorrowAccess h.state rp false := by
  rcases htok with ⟨⟨entry, hlookup, _, hperm⟩, _⟩
  exact ⟨h.state, by simp [stepTreeBorrowAccess?, hlookup, hperm]⟩

theorem borrowToken_active_hasWriteAccess
    {rp : RawPtrVal} {h : PartialHeap}
    (htok : BorrowToken rp .active h) :
    HasTreeBorrowAccess h.state rp true := by
  rcases htok with ⟨⟨entry, hlookup, _, hperm⟩, _⟩
  exact
    ⟨{ h.state with
       borrows :=
         invalidateConflictingBorrows h.state.borrows entry.targetLocal (some rp.tag) },
     by simp [stepTreeBorrowAccess?, hlookup, hperm]⟩

theorem pointsTo_implies_liveAllocAt
    {rp : RawPtrVal} {v : Value} {h : PartialHeap}
    (hpts : PointsTo rp v h) :
    LiveAllocAt h.state (memoryLocals h.state) rp :=
  .inl ⟨v, hpts.1⟩

/-! ## 3. Pointer and Unaligned-Wrapper Typestate Invariants -/

/-- Aliasing typestate parameter of `zerocopy::Ptr<'a, T, I>`. -/
inductive AliasingMode : Type where
  | Shared
  | Exclusive
  | Invariant
  deriving DecidableEq, Repr

/-- Alignment typestate parameter of `zerocopy::Ptr<'a, T, I>`. -/
inductive AlignmentMode : Type where
  | Unaligned
  | Aligned
  deriving DecidableEq, Repr

/-- Validity typestate parameter of `zerocopy::Ptr<'a, T, I>`. -/
inductive PtrValidityMode : Type where
  | Uninit
  | AsInitialized
  | Initialized
  | BitValid
  | Valid
  deriving DecidableEq, Repr

/-- `SepProp` ownership invariant corresponding to `AliasingMode`. -/
def AliasingInv (rp : RawPtrVal) : AliasingMode → SepProp
  | .Shared => BorrowToken rp .frozen
  | .Exclusive => BorrowToken rp .active
  | .Invariant => fun h => BorrowToken rp .active h ∨ BorrowToken rp .frozen h

/-- Pure alignment obligation corresponding to `AlignmentMode`. -/
def AlignmentInv (rp : RawPtrVal) (alignBytes : Nat) : AlignmentMode → Prop
  | .Unaligned => True
  | .Aligned => AlignedPtr rp alignBytes

/-- `SepProp` pointee invariant corresponding to `PtrValidityMode`. -/
def ValidityInv
    (rp : RawPtrVal) (validity : PtrValidityMode) (vPred : Value → Prop) :
    SepProp :=
  match validity with
  | .Uninit | .AsInitialized => emp
  | .Initialized | .BitValid => fun h => ∃ v, PointsTo rp v h
  | .Valid => fun h => ∃ v, PointsTo rp v h ∧ vPred v

/--
Combined disjoint-footprint separation-logic invariant for
`zerocopy::Ptr<'a, T, (aliasing, alignment, validity)>`.
-/
def PtrInvariant
    (lft : Nat) (rp : RawPtrVal) (alignBytes : Nat)
    (aliasing : AliasingMode) (alignment : AlignmentMode)
    (validity : PtrValidityMode) (vPred : Value → Prop) : SepProp :=
  sepConj (LifetimeToken lft)
    (sepConj (AliasingInv rp aliasing)
      (sepConj (pureProp (AlignmentInv rp alignBytes alignment))
        (ValidityInv rp validity vPred)))

/-- Invariant for a pointer to `zerocopy::Unalign<T>`. -/
def UnalignInvariant
    (lft : Nat) (rp : RawPtrVal) (alignBytes : Nat)
    (aliasing : AliasingMode) (vPred : Value → Prop) : SepProp :=
  PtrInvariant lft rp alignBytes aliasing .Unaligned .Valid vPred

theorem ptr_forget_aligned_sound
    {lft : Nat} {rp : RawPtrVal} {alignBytes : Nat}
    {aliasing : AliasingMode} {alignment : AlignmentMode}
    {validity : PtrValidityMode} {vPred : Value → Prop} {h : PartialHeap}
    (hinv : PtrInvariant lft rp alignBytes aliasing alignment validity vPred h) :
    PtrInvariant lft rp alignBytes aliasing .Unaligned validity vPred h := by
  rcases hinv with ⟨h₁, h₂₃₄, hs₁, hlft, h₂, h₃₄, hs₂, hali, h₃, h₄, hs₃, ⟨_, hemp₃⟩, hval⟩
  exact ⟨h₁, h₂₃₄, hs₁, hlft, h₂, h₃₄, hs₂, hali, h₃, h₄, hs₃, ⟨trivial, hemp₃⟩, hval⟩

theorem unalign_into_inner_sound
    {lft : Nat} {rp : RawPtrVal} {alignBytes : Nat}
    {aliasing : AliasingMode} {vPred : Value → Prop} {h : PartialHeap}
    (hinv : UnalignInvariant lft rp alignBytes aliasing vPred h) :
    ∃ v, readAllocAt? (memoryLocals h.state) rp = some v ∧ vPred v := by
  rcases hinv with ⟨_, h₂₃₄, hs₁, _, _, h₃₄, hs₂, _, _, h₄, hs₃, _, v, hpts, hv⟩
  have hs : h₄.state = h.state := hs₃.2.1.trans (hs₂.2.1.trans hs₁.2.1)
  exact ⟨v, hs ▸ hpts.1, hv⟩

theorem unalign_deref_mut_unchecked_sound
    {lft : Nat} {rp : RawPtrVal} {alignBytes : Nat}
    {vPred : Value → Prop} {h : PartialHeap}
    (hinv : UnalignInvariant lft rp alignBytes .Exclusive vPred h) :
    HasTreeBorrowAccess h.state rp true ∧
    ∃ v, readAllocAt? (memoryLocals h.state) rp = some v ∧ vPred v := by
  rcases hinv with ⟨h₁, h₂₃₄, hs₁, hlft, h₂, h₃₄, hs₂, hali, h₃, h₄, hs₃, hpure, v, hpts, hv⟩
  have hs₂' : h₂.state = h.state := hs₂.1.trans hs₁.2.1
  have hs₄' : h₄.state = h.state := hs₃.2.1.trans (hs₂.2.1.trans hs₁.2.1)
  exact ⟨hs₂' ▸ borrowToken_active_hasWriteAccess hali, v, hs₄' ▸ hpts.1, hv⟩

/-! ## 4. Footprint Agreement, Locality, and ITree Framing -/

/--
Two `Memory` states agree on `fp` when every `(allocId, offset) ∈ fp.addrs`
reads the same value in `memoryLocals` and every `tag ∈ fp.tags` resolves to
the same `BorrowEntry` in `borrows`.
-/
def AgreeOnFootprint (fp : Footprint) (m₁ m₂ : Memory) : Prop :=
  (∀ allocId offset,
    (allocId, offset) ∈ fp.addrs →
    readAllocAt? (memoryLocals m₁) { allocId, offset, tag := allocId } =
      readAllocAt? (memoryLocals m₂) { allocId, offset, tag := allocId }) ∧
  (∀ tag, tag ∈ fp.tags → lookupBorrow m₁.borrows tag = lookupBorrow m₂.borrows tag)

theorem agreeOnFootprint_refl (fp : Footprint) (m : Memory) :
    AgreeOnFootprint fp m m :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩

theorem agreeOnFootprint_symm
    {fp : Footprint} {m₁ m₂ : Memory} (h : AgreeOnFootprint fp m₁ m₂) :
    AgreeOnFootprint fp m₂ m₁ :=
  ⟨fun a o hin => (h.1 a o hin).symm, fun t hin => (h.2 t hin).symm⟩

theorem agreeOnFootprint_trans
    {fp : Footprint} {m₁ m₂ m₃ : Memory}
    (h₁₂ : AgreeOnFootprint fp m₁ m₂) (h₂₃ : AgreeOnFootprint fp m₂ m₃) :
    AgreeOnFootprint fp m₁ m₃ :=
  ⟨fun a o hin => (h₁₂.1 a o hin).trans (h₂₃.1 a o hin),
   fun t hin => (h₁₂.2 t hin).trans (h₂₃.2 t hin)⟩

theorem agreeOnFootprint_union_left
    {fp₁ fp₂ : Footprint} {m₁ m₂ : Memory}
    (h : AgreeOnFootprint (fp₁.union fp₂) m₁ m₂) :
    AgreeOnFootprint fp₁ m₁ m₂ :=
  ⟨fun a o hin => h.1 a o (List.mem_append_left _ hin),
   fun t hin => h.2 t (List.mem_append_left _ hin)⟩

theorem agreeOnFootprint_union_right
    {fp₁ fp₂ : Footprint} {m₁ m₂ : Memory}
    (h : AgreeOnFootprint (fp₁.union fp₂) m₁ m₂) :
    AgreeOnFootprint fp₂ m₁ m₂ :=
  ⟨fun a o hin => h.1 a o (List.mem_append_right _ hin),
   fun t hin => h.2 t (List.mem_append_right _ hin)⟩

/--
A `HeapPred` `R : Memory → Prop` is supported by `fp` when agreement on `fp`
preserves `R`.
-/
def SupportedBy (R : HeapPred) (fp : Footprint) : Prop :=
  ∀ m₁ m₂ : Memory, AgreeOnFootprint fp m₁ m₂ → R m₁ → R m₂

/--
A `SepProp` `P` is footprint-local when `P ⟨m, fp⟩` depends only on the cells
and tags inside its own `fp`.
-/
def LocalSepProp (P : SepProp) : Prop :=
  ∀ fp : Footprint, SupportedBy (P.atFootprint fp) fp

theorem localSepProp_emp : LocalSepProp emp :=
  fun _ _ _ _ h => h

theorem localSepProp_pureProp (P : Prop) : LocalSepProp (pureProp P) :=
  fun _ _ _ _ h => h

theorem localSepProp_pointsTo (rp : RawPtrVal) (v : Value) :
    LocalSepProp (PointsTo rp v) := by
  intro fp m₁ m₂ hagree ⟨hread, hfp⟩
  dsimp at hfp
  refine ⟨?_, hfp⟩
  have hin : (rp.allocId, rp.offset) ∈ fp.addrs := by simp [hfp]
  have heq := hagree.1 rp.allocId rp.offset hin
  have htag₁ :
      readAllocAt? (memoryLocals m₁) rp =
        readAllocAt? (memoryLocals m₁)
          { allocId := rp.allocId, offset := rp.offset, tag := rp.allocId } := rfl
  have htag₂ :
      readAllocAt? (memoryLocals m₂) rp =
        readAllocAt? (memoryLocals m₂)
          { allocId := rp.allocId, offset := rp.offset, tag := rp.allocId } := rfl
  rw [htag₂, ← heq, ← htag₁]
  exact hread

theorem localSepProp_borrowToken (rp : RawPtrVal) (perm : TreeBorrowPerm) :
    LocalSepProp (BorrowToken rp perm) := by
  intro fp m₁ m₂ hagree ⟨⟨entry, hlookup, htarget, hperm⟩, hfp⟩
  dsimp at hfp
  have hin : rp.tag ∈ fp.tags := by simp [hfp]
  exact ⟨⟨entry, (hagree.2 rp.tag hin) ▸ hlookup, htarget, hperm⟩, hfp⟩

theorem localSepProp_lifetimeToken (lft : Nat) :
    LocalSepProp (LifetimeToken lft) := by
  intro fp m₁ m₂ hagree ⟨⟨entry, hlookup, hperm⟩, hfp⟩
  dsimp at hfp
  have hin : lft ∈ fp.tags := by simp [hfp]
  exact ⟨⟨entry, (hagree.2 lft hin) ▸ hlookup, hperm⟩, hfp⟩

theorem localSepProp_sepConj
    {P Q : SepProp} (hP : LocalSepProp P) (hQ : LocalSepProp Q) :
    LocalSepProp (sepConj P Q) := by
  intro fp m₁ m₂ hagree ⟨⟨s₁, fp₁⟩, ⟨s₂, fp₂⟩, ⟨hs₁, hs₂, hdisj, haddrs, htags⟩, hp, hq⟩
  dsimp at hs₁ hs₂
  subst s₁ s₂
  have hagree₁ : AgreeOnFootprint fp₁ m₁ m₂ :=
    ⟨fun a o hin => hagree.1 a o ((haddrs (a, o)).2 (.inl hin)),
     fun t hin => hagree.2 t ((htags t).2 (.inl hin))⟩
  have hagree₂ : AgreeOnFootprint fp₂ m₁ m₂ :=
    ⟨fun a o hin => hagree.1 a o ((haddrs (a, o)).2 (.inr hin)),
     fun t hin => hagree.2 t ((htags t).2 (.inr hin))⟩
  exact ⟨⟨m₂, fp₁⟩, ⟨m₂, fp₂⟩,
          ⟨rfl, rfl, hdisj, haddrs, htags⟩,
          hP fp₁ m₁ m₂ hagree₁ hp,
          hQ fp₂ m₁ m₂ hagree₂ hq⟩

theorem supportedBy_borrowToken (rp : RawPtrVal) (perm : TreeBorrowPerm) :
    SupportedBy
      ((BorrowToken rp perm).atFootprint { addrs := [], tags := [rp.tag] })
      { addrs := [], tags := [rp.tag] } :=
  localSepProp_borrowToken rp perm { addrs := [], tags := [rp.tag] }

theorem supportedBy_pointsTo (rp : RawPtrVal) (v : Value) :
    SupportedBy
      ((PointsTo rp v).atFootprint
        { addrs := [(rp.allocId, rp.offset)], tags := [] })
      { addrs := [(rp.allocId, rp.offset)], tags := [] } :=
  localSepProp_pointsTo rp v { addrs := [(rp.allocId, rp.offset)], tags := [] }

/--
Disjoint-footprint `DWLP` frame rule over `(α × Memory)` return values.
-/
theorem dwlp_frame_disjoint
    {S : Type u} {E : Effect.{u}} {α : Type u}
    (ewp : StateEffectWP S E)
    {t : ITree E (α × Memory)}
    {Q : (α × Memory) → S → Prop}
    {R : HeapPred} {fp : Footprint} {m₀ : Memory} {s₀ : S}
    (hsupp : SupportedBy R fp)
    (hdwlp :
      DWLP ewp t (fun res s => Q res s ∧ AgreeOnFootprint fp m₀ res.2) s₀)
    (hr : R m₀) :
    DWLP ewp t (fun res s => Q res s ∧ R res.2) s₀ :=
  DWLP.mono
    (fun res _ ⟨hq, hagree⟩ => ⟨hq, hsupp m₀ res.2 hagree hr⟩)
    hdwlp

/--
Disjoint-footprint `DWP` frame rule over `(α × Memory)` return values.
-/
theorem dwp_frame_disjoint
    {S : Type u} {E : Effect.{u}} {α : Type u}
    (ewp : StateEffectWP S E)
    {t : ITree E (α × Memory)}
    {Q : (α × Memory) → S → Prop}
    {R : HeapPred} {fp : Footprint} {m₀ : Memory} {s₀ : S}
    (hsupp : SupportedBy R fp)
    (hdwp :
      DWP ewp t (fun res s => Q res s ∧ AgreeOnFootprint fp m₀ res.2) s₀)
    (hr : R m₀) :
    DWP ewp t (fun res s => Q res s ∧ R res.2) s₀ :=
  DWP.mono
    (fun res _ ⟨hq, hagree⟩ => ⟨hq, hsupp m₀ res.2 hagree hr⟩)
    hdwp

/-- Conjoin a frame predicate `frame : HeapPred` onto a `StatefulClaim`. -/
def frameStatefulClaim (c : StatefulClaim) (frame : HeapPred) : StatefulClaim where
  body := c.body
  pre args mem := c.pre args mem ∧ frame mem
  post args mem retVal mem' := c.post args mem retVal mem' ∧ frame mem'

/--
Disjoint-footprint frame theorem lifting an audited
`StatefulVerificationResult c` to `StatefulVerificationResult (frameStatefulClaim c frame)`
without re-verifying `c.body`.
-/
theorem statefulVerificationResult_frame_disjoint
    {c : StatefulClaim} {frame : HeapPred} {fp : Footprint}
    (hver : StatefulVerificationResult c)
    (hsupp : SupportedBy frame fp)
    (hpres :
      ∀ args mem retVal mem',
        c.pre args mem → c.post args mem retVal mem' →
          AgreeOnFootprint fp mem mem') :
    StatefulVerificationResult (frameStatefulClaim c frame) := by
  refine ⟨fun args mem ⟨hcpre, hfin⟩ => ?_⟩
  rcases hver.proof args mem hcpre with ⟨hsafe, href⟩
  refine ⟨hsafe, fun outPair hret _ retVal mem' hout => ?_⟩
  have hcpost := href outPair hret hcpre retVal mem' hout
  exact ⟨hcpost, hsupp mem mem' (hpres args mem retVal mem' hcpre hcpost) hfin⟩

private theorem updateBorrowPerm_tag
    (entry : BorrowEntry) (targetLocal : Local) (writerTag : Option Nat) :
    (updateBorrowPerm entry targetLocal writerTag).tag = entry.tag := by
  unfold updateBorrowPerm
  cases Nat.beq entry.targetLocal targetLocal
  · rfl
  · cases writerTag with
    | none => cases entry.perm <;> rfl
    | some wtag =>
      dsimp only
      cases Nat.beq entry.tag wtag
      · rfl
      · cases entry.perm <;> rfl

/--
Looking up `tag` in `invalidateConflictingBorrows borrows targetLocal writerTag`
maps `updateBorrowPerm` over `lookupBorrow borrows tag`.
-/
theorem lookupBorrow_invalidateConflictingBorrows
    (borrows : List BorrowEntry) (targetLocal : Local)
    (writerTag : Option Nat) (tag : Nat) :
    lookupBorrow (invalidateConflictingBorrows borrows targetLocal writerTag) tag =
      (lookupBorrow borrows tag).map
        (fun entry => updateBorrowPerm entry targetLocal writerTag) := by
  induction borrows with
  | nil => rfl
  | cons entry rest ih =>
    unfold invalidateConflictingBorrows lookupBorrow
    rw [updateBorrowPerm_tag]
    cases Nat.beq entry.tag tag
    · exact ih
    · rfl

theorem updateBorrowPerm_of_targetLocal_ne
    (entry : BorrowEntry) (targetLocal : Local) (writerTag : Option Nat)
    (hne : entry.targetLocal ≠ targetLocal) :
    updateBorrowPerm entry targetLocal writerTag = entry := by
  unfold updateBorrowPerm
  cases hbeq : Nat.beq entry.targetLocal targetLocal
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hbeq) hne

/--
Updating `m.borrows` via `invalidateConflictingBorrows` for `targetLocal`
preserves `AgreeOnFootprint fp` for every tag in `fp.tags` targeting a local
distinct from `targetLocal`.
-/
theorem agreeOnFootprint_of_disjoint_borrow_update
    (fp : Footprint) (m : Memory) (targetLocal : Local)
    (writerTag : Option Nat)
    (hdisj :
      ∀ tag ∈ fp.tags,
        ∃ entry,
          lookupBorrow m.borrows tag = some entry ∧
          entry.targetLocal ≠ targetLocal) :
    AgreeOnFootprint fp m
      { m with
        borrows :=
          invalidateConflictingBorrows m.borrows targetLocal writerTag } := by
  refine ⟨fun _ _ _ => rfl, fun tag hin => ?_⟩
  rcases hdisj tag hin with ⟨entry, hlookup, hne⟩
  rw [lookupBorrow_invalidateConflictingBorrows, hlookup]
  exact congrArg some (updateBorrowPerm_of_targetLocal_ne entry targetLocal writerTag hne).symm

end Anneal.SepLogic
