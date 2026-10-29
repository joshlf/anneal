import Trusted
import Anneal.Refinement
import Anneal.ITree
import Anneal.ITreeWP
import Anneal.SepLogic
import Anneal.Rustc.V2026_06_01.Lower

namespace Anneal.FunctionalTranslation

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Refinement
open Anneal.Effect
open Anneal.ITree
open Anneal.EffectWP
open Anneal.ITreeWP
open Anneal.Memory
open Anneal.UnsafeObligations
open Anneal.SepLogic
open Anneal.Rustc.V2026_06_01.Lower

/-!
Plan-guided functional translation, spine-preserving symbolic value merging,
forward/backward `&mut` lenses, and program-to-program Layer 1A Smyth refinement
bridges over `Trusted.Rustc.V2026_06_01` MIR interaction trees (`#100`, `#103`,
`#109`).

This module resides entirely outside the trusted base (`theory/Anneal/`) and
connects directly to `mirTree`, `mirCallTree` (`mirOpenTree`), and
`mirStatefulTree` via `DWLP`, `DWP`, and `ITree.toPartial`:

1. **Pillar 1 — Spine-Preserving Symbolic Values (`SymVal`, `zipSymVal`,
   `SymSlot`, `SymLocals`, `zipSymLocals`)**:
   Pushes branch conditionals `if cond then ... else ...` inward through
   matching scalar, boolean, pointer, and tuple/ADT constructor spines so
   post-join projections and arithmetic reduce without path explosion.
2. **Pillar 2 — Plan-Guided CFG & Loop Translation (`TransPlan`, `wpTransPlan`)**:
   Guides `DWP` / `DWLP` verification over `V2026_06_01` `CapturedMir` basic
   blocks (`.ret`, `.jump`, `.seq`, `.branch` diamond joins via `zipSymLocals`,
   `.splitBranch`, and `.loop` verified by `Nat` fuel/rank induction), producing
   `VerificationResult`, `StatefulVerificationResult`, and
   `TotalVerificationResult`.
3. **Pillar 3 — Forward/Backward `&mut` Lenses (`MutLens`, `LawfulMutLens`,
   `memoryPtrMutLens`, `MutRefSpec`)**:
   Packages `(readView, writeBack)` lenses over `Memory` (`PartialHeap` /
   `PointsTo` + active Tree Borrows `BorrowToken`) and `CapturedMir` `&mut T`
   methods, translating imperative mutations into pure Lean state updates
   `α → α × β`.
4. **Pillar 4 — Program-to-Program Behavioral Equivalence & Refinement Bridge**:
   Connects `DWLP` and `DWP` specifications through constructive trace/return
   adequacy directly to Layer 1A `Partial` refinement (`≤` and `=`) on
   `mirStatefulTree` (and observation-erased `mirObsErasedStatefulTree`),
   establishing both behavioral refinement and `MirTerminatesAndNoUB`.
-/

/-- Alias for `mirCallTree`: stateless open interaction tree of `body` on `args`. -/
abbrev mirOpenTree (body : CapturedMir) (args : List Value) :
    ITree MirEffect MirOutcome :=
  mirCallTree body args

/-! ## Scalar Arithmetic Simplification Helpers -/

theorem nat_ble_eq_false_of_lt {m v : Nat} (h : v < m) :
    Nat.ble m v = false := by
  cases hb : Nat.ble m v
  · rfl
  · exact absurd (Nat.le_of_ble_eq_true hb) (Nat.not_le_of_lt h)

theorem nat_ble_eq_true_of_le {m v : Nat} (h : m ≤ v) :
    Nat.ble m v = true :=
  Nat.ble_eq_true_of_le h

theorem wrapScalarBits_of_lt {val modulus : Nat} (h : val < modulus) :
    wrapScalarBits val modulus = val := by
  unfold wrapScalarBits
  rw [nat_ble_eq_false_of_lt h]

@[simp]
theorem not_beq_boolToScalar_zero (b : Bool) :
    (!(Nat.beq (boolToScalar b).bits 0)) = b := by
  cases b <;> rfl

@[simp]
theorem beq_boolToScalar_zero (b : Bool) :
    Nat.beq (boolToScalar b).bits 0 = !b := by
  cases b <;> rfl

@[simp]
theorem beq_boolToScalar_one (b : Bool) :
    Nat.beq (boolToScalar b).bits 1 = b := by
  cases b <;> rfl

/-! ## Pillar 1: Spine-Preserving Symbolic Values & Symbolic Local Frames -/

/--
Symbolic representation of a `V2026_06_01` runtime `Value` preserving outer
scalar, boolean, pointer, and aggregate/ADT constructor spines across control-flow
joins (`zipSymVal`).
-/
inductive SymVal : Type where
  /-- Zero-sized unit value (`Value.unit`). -/
  | unit : SymVal
  /-- Fixed-width integer or character scalar (`Value.scalar`). -/
  | scalar (bits : Nat) (sizeBytes : Nat) : SymVal
  /-- Canonical 1-byte Rust boolean (`0x00` or `0x01`). -/
  | bool (b : Bool) : SymVal
  /-- Pointer value with allocation provenance (`Value.ptr`). -/
  | ptr (allocId : AllocId) (offsetBytes : Nat) (sizeBytes : Nat) : SymVal
  /-- Tuple, struct, array, or enum variant with fixed constructor & field spine. -/
  | adt (variantIdx : VariantIdx) (fields : List SymVal) : SymVal
  /-- Fallback wrapping an arbitrary runtime `Value`. -/
  | opaque (val : Value) : SymVal

mutual
/-- Denote a symbolic `SymVal` into a concrete `V2026_06_01` runtime `Value`. -/
def SymVal.denote : SymVal → Value
  | .unit => .unit
  | .scalar bits sz => .scalar { bits := bits, sizeBytes := sz }
  | .bool b => .scalar (boolToScalar b)
  | .ptr alloc off sz => .ptr { allocId := alloc, offsetBytes := off } sz
  | .adt variant fields => .aggregate variant (SymVal.denoteList fields)
  | .opaque val => val

/-- Pointwise denotation of a list of `SymVal` fields. -/
def SymVal.denoteList : List SymVal → List Value
  | [] => []
  | v :: vs => v.denote :: SymVal.denoteList vs
end

@[simp] theorem SymVal.denote_unit : SymVal.unit.denote = .unit := rfl
@[simp] theorem SymVal.denote_scalar (bits sz : Nat) :
    (SymVal.scalar bits sz).denote = .scalar { bits := bits, sizeBytes := sz } := rfl
@[simp] theorem SymVal.denote_bool (b : Bool) :
    (SymVal.bool b).denote = .scalar (boolToScalar b) := rfl
@[simp] theorem SymVal.denote_ptr (alloc off sz : Nat) :
    (SymVal.ptr alloc off sz).denote =
      .ptr { allocId := alloc, offsetBytes := off } sz := rfl
@[simp] theorem SymVal.denote_adt (variant : VariantIdx) (fields : List SymVal) :
    (SymVal.adt variant fields).denote =
      .aggregate variant (SymVal.denoteList fields) := rfl
@[simp] theorem SymVal.denote_opaque (val : Value) :
    (SymVal.opaque val).denote = val := rfl
@[simp] theorem SymVal.denoteList_nil : SymVal.denoteList [] = [] := rfl
@[simp] theorem SymVal.denoteList_cons (v : SymVal) (vs : List SymVal) :
    SymVal.denoteList (v :: vs) = v.denote :: SymVal.denoteList vs := rfl

theorem SymVal.denoteList_eq_map (vs : List SymVal) :
    SymVal.denoteList vs = vs.map SymVal.denote := by
  induction vs with
  | nil => rfl
  | cons v rest ih => simp [ih]

mutual
/-- Lift a runtime `Value` into `SymVal`, exposing its full constructor spine. -/
def SymVal.ofValue : Value → SymVal
  | .unit => .unit
  | .scalar sc => .scalar sc.bits sc.sizeBytes
  | .ptr p sz => .ptr p.allocId p.offsetBytes sz
  | .aggregate variant fields => .adt variant (SymVal.ofValueList fields)

/-- Lift a `List Value` pointwise into `List SymVal`. -/
def SymVal.ofValueList : List Value → List SymVal
  | [] => []
  | v :: vs => SymVal.ofValue v :: SymVal.ofValueList vs
end

mutual
theorem SymVal.denote_ofValue (v : Value) :
    (SymVal.ofValue v).denote = v := by
  cases v with
  | unit => rfl
  | scalar sc => cases sc; rfl
  | ptr p sz => cases p; rfl
  | aggregate variant fields =>
    dsimp [SymVal.ofValue, SymVal.denote]
    rw [SymVal.denoteList_ofValueList]

theorem SymVal.denoteList_ofValueList (vs : List Value) :
    SymVal.denoteList (SymVal.ofValueList vs) = vs := by
  cases vs with
  | nil => rfl
  | cons v rest =>
    dsimp [SymVal.ofValueList, SymVal.denoteList]
    rw [SymVal.denote_ofValue, SymVal.denoteList_ofValueList]
end

attribute [simp] SymVal.denote_ofValue SymVal.denoteList_ofValueList

mutual
/--
Merge two `SymVal` branches under `cond : Bool`, pushing `if cond then ... else ...`
inward across matching scalar widths, booleans, pointers, and ADT constructor/field
spines, falling back to `.opaque` only when outer shapes diverge.
-/
def zipSymVal (cond : Bool) : SymVal → SymVal → SymVal
  | .unit, .unit => .unit
  | .scalar bt szt, .scalar be sze =>
    if Nat.beq szt sze then
      .scalar (if cond then bt else be) szt
    else
      .opaque (if cond then .scalar ⟨bt, szt⟩ else .scalar ⟨be, sze⟩)
  | .bool bt, .bool be => .bool (if cond then bt else be)
  | .ptr at_ ot szt, .ptr ae oe sze =>
    if Nat.beq szt sze then
      .ptr (if cond then at_ else ae) (if cond then ot else oe) szt
    else
      .opaque (if cond then .ptr ⟨at_, ot⟩ szt else .ptr ⟨ae, oe⟩ sze)
  | .adt vt ft, .adt ve fe =>
    if Nat.beq vt ve then
      match zipSymValList cond ft fe with
      | some fz => .adt vt fz
      | none =>
        .opaque
          (if cond then .aggregate vt (SymVal.denoteList ft)
           else .aggregate ve (SymVal.denoteList fe))
    else
      .opaque
        (if cond then .aggregate vt (SymVal.denoteList ft)
         else .aggregate ve (SymVal.denoteList fe))
  | t, e => .opaque (if cond then t.denote else e.denote)

/-- Elementwise spine-preserving zip across equal-length `SymVal` field lists. -/
def zipSymValList (cond : Bool) :
    List SymVal → List SymVal → Option (List SymVal)
  | [], [] => some []
  | t :: ts, e :: es =>
    match zipSymValList cond ts es with
    | some zs => some (zipSymVal cond t e :: zs)
    | none => none
  | _, _ => none
end

mutual
/-- Fundamental spine-preservation adequacy theorem for `zipSymVal`. -/
theorem denote_zipSymVal (cond : Bool) (t e : SymVal) :
    (zipSymVal cond t e).denote = if cond then t.denote else e.denote := by
  unfold zipSymVal
  split
  · cases cond <;> rfl
  · next bt szt be sze =>
    cases h_sz : Nat.beq szt sze
    · simp
    · have h_eq : szt = sze := Nat.eq_of_beq_eq_true h_sz
      subst h_eq
      cases cond <;> simp
  · next bt be =>
    cases cond <;> rfl
  · next at_ ot szt ae oe sze =>
    cases h_sz : Nat.beq szt sze
    · simp
    · have h_eq : szt = sze := Nat.eq_of_beq_eq_true h_sz
      subst h_eq
      cases cond <;> simp
  · next vt ft ve fe =>
    cases h_var : Nat.beq vt ve
    · simp
    · have h_eq : vt = ve := Nat.eq_of_beq_eq_true h_var
      subst h_eq
      cases h_zip : zipSymValList cond ft fe with
      | none => simp
      | some fz =>
        have h_list := denoteList_zipSymValList cond ft fe fz h_zip
        cases cond <;> simp [h_list]
  · simp

theorem denoteList_zipSymValList (cond : Bool) :
    ∀ (ts es zs : List SymVal),
      zipSymValList cond ts es = some zs →
      SymVal.denoteList zs =
        if cond then SymVal.denoteList ts else SymVal.denoteList es
  | [], [], _, h => by
    injection h with h_eq; subst h_eq; cases cond <;> rfl
  | [], _ :: _, _, h => by nomatch h
  | _ :: _, [], _, h => by nomatch h
  | t :: ts, e :: es, zs, h => by
    unfold zipSymValList at h
    cases h_rest : zipSymValList cond ts es with
    | none => rw [h_rest] at h; nomatch h
    | some zrest =>
      rw [h_rest] at h
      injection h with h_eq
      subst h_eq
      have ih := denoteList_zipSymValList cond ts es zrest h_rest
      have hd := denote_zipSymVal cond t e
      cases cond <;> simp [hd, ih]
end

attribute [simp] denote_zipSymVal

/-- Symbolic MIR local variable slot mirroring `LocalSlot`. -/
inductive SymSlot : Type where
  | dead : SymSlot
  | uninit : SymSlot
  | init (val : SymVal) : SymSlot
  | opaque (slot : LocalSlot) : SymSlot

/-- Denote a `SymSlot` into a concrete `LocalSlot`. -/
def SymSlot.denote : SymSlot → LocalSlot
  | .dead => .dead
  | .uninit => .uninit
  | .init v => .init v.denote
  | .opaque s => s

@[simp] theorem SymSlot.denote_dead : SymSlot.dead.denote = .dead := rfl
@[simp] theorem SymSlot.denote_uninit : SymSlot.uninit.denote = .uninit := rfl
@[simp] theorem SymSlot.denote_init (v : SymVal) :
    (SymSlot.init v).denote = .init v.denote := rfl
@[simp] theorem SymSlot.denote_opaque (s : LocalSlot) :
    (SymSlot.opaque s).denote = s := rfl

/-- Lift a runtime `LocalSlot` into `SymSlot`. -/
def SymSlot.ofLocalSlot : LocalSlot → SymSlot
  | .dead => .dead
  | .uninit => .uninit
  | .init v => .init (SymVal.ofValue v)

@[simp]
theorem SymSlot.denote_ofLocalSlot (s : LocalSlot) :
    (SymSlot.ofLocalSlot s).denote = s := by
  cases s <;> simp [SymSlot.ofLocalSlot]

/-- Merge two symbolic local slots under `cond : Bool`. -/
def zipSymSlot (cond : Bool) : SymSlot → SymSlot → SymSlot
  | .dead, .dead => .dead
  | .uninit, .uninit => .uninit
  | .init vt, .init ve => .init (zipSymVal cond vt ve)
  | st, se => .opaque (if cond then st.denote else se.denote)

@[simp]
theorem denote_zipSymSlot (cond : Bool) (st se : SymSlot) :
    (zipSymSlot cond st se).denote = if cond then st.denote else se.denote := by
  unfold zipSymSlot
  split
  · cases cond <;> rfl
  · cases cond <;> rfl
  · cases cond <;> simp
  · rfl

/-- Symbolic local variable frame for an active MIR function activation. -/
abbrev SymLocals : Type := List SymSlot

/-- Pointwise denotation of a `SymLocals` frame into `List LocalSlot`. -/
def SymLocals.denote (ls : SymLocals) : List LocalSlot :=
  ls.map SymSlot.denote

@[simp] theorem SymLocals.denote_nil : SymLocals.denote [] = [] := rfl
@[simp] theorem SymLocals.denote_cons (s : SymSlot) (rest : SymLocals) :
    SymLocals.denote (s :: rest) = s.denote :: SymLocals.denote rest := rfl
@[simp] theorem SymLocals.length_denote (ls : SymLocals) :
    (SymLocals.denote ls).length = ls.length :=
  List.length_map _

/-- Lift a runtime `List LocalSlot` into `SymLocals`. -/
def SymLocals.ofLocalSlots (ls : List LocalSlot) : SymLocals :=
  ls.map SymSlot.ofLocalSlot

@[simp]
theorem SymLocals.length_ofLocalSlots (ls : List LocalSlot) :
    (SymLocals.ofLocalSlots ls).length = ls.length :=
  List.length_map _

@[simp]
theorem SymLocals.denote_ofLocalSlots (ls : List LocalSlot) :
    (SymLocals.ofLocalSlots ls).denote = ls := by
  induction ls with
  | nil => rfl
  | cons s rest ih =>
    unfold SymLocals.ofLocalSlots at ih ⊢
    simp [ih]

/--
Pointwise spine-preserving merge of two `SymLocals` frames under `cond : Bool`.
-/
def zipSymLocals (cond : Bool) : SymLocals → SymLocals → SymLocals
  | [], [] => []
  | s₁ :: rest₁, s₂ :: rest₂ =>
    zipSymSlot cond s₁ s₂ :: zipSymLocals cond rest₁ rest₂
  | ls₁, _ => ls₁

@[simp]
theorem length_zipSymLocals (cond : Bool) :
    ∀ {ls₁ ls₂ : SymLocals},
      ls₁.length = ls₂.length →
      (zipSymLocals cond ls₁ ls₂).length = ls₁.length
  | [], [], _ => rfl
  | _ :: rest₁, _ :: rest₂, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [zipSymLocals, length_zipSymLocals cond h]

/-- Fundamental frame-merge adequacy theorem for `zipSymLocals`. -/
theorem denote_zipSymLocals (cond : Bool) :
    ∀ {ls₁ ls₂ : SymLocals},
      ls₁.length = ls₂.length →
      (zipSymLocals cond ls₁ ls₂).denote =
        if cond then ls₁.denote else ls₂.denote
  | [], [], _ => by cases cond <;> rfl
  | s₁ :: rest₁, s₂ :: rest₂, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    have ih := denote_zipSymLocals cond h
    cases cond <;> simp [zipSymLocals, ih]

/--
Lift, spine-zip, and denote two concrete-spine `List LocalSlot` frames under
`cond : Bool`. Reduces definitionally on explicit frames to a single list of
`LocalSlot`s with `if cond` pushed inside `.scalar`, `.ptr`, and `.aggregate`
payloads.
-/
def zipLocalSlots (cond : Bool) (ls₁ ls₂ : List LocalSlot) : List LocalSlot :=
  (zipSymLocals cond
    (SymLocals.ofLocalSlots ls₁)
    (SymLocals.ofLocalSlots ls₂)).denote

theorem zipLocalSlots_eq_ite (cond : Bool) {ls₁ ls₂ : List LocalSlot}
    (h_len : ls₁.length = ls₂.length) :
    zipLocalSlots cond ls₁ ls₂ = if cond then ls₁ else ls₂ := by
  unfold zipLocalSlots
  rw [denote_zipSymLocals cond (by simp [h_len])]
  simp

/-! ## Pillar 2: Plan-Guided CFG & Loop Translation (`TransPlan`) over `CapturedMir` -/

/--
Typeclass witnessing that an `EffectWP MirEffect` treats internal `MirObsE`
branch-tag emissions transparently (`obsIgnoreWP`). Satisfied automatically by
`mirDefaultWP`, `mirNoCallWP`, and `mirModularWP C`.
-/
class ObsTransparentWP (ewp : EffectWP MirEffect) : Prop where
  emit_wp :
    ∀ (obs : MirObs) (Q : PUnit → PUnit → Prop),
      Q PUnit.unit PUnit.unit →
      ewp.wp (.inr (.inl (.emit obs))) Q PUnit.unit

instance : ObsTransparentWP mirDefaultWP where
  emit_wp _ _ h := h

instance : ObsTransparentWP mirNoCallWP where
  emit_wp _ _ h := h

instance (C : CallContract MirCallReq (fun _ => MirCallAns)) :
    ObsTransparentWP (mirModularWP C) where
  emit_wp _ _ h := h

/-! ### Fundamental One-Step & Block-Step `DWP` / `DWLP` Lemmas on `mirTree` -/

/-- Step `DWP` across a single silent `.tau` transition of `stepMirFn`. -/
theorem dwp_mirTree_tau
    {S : Type} {ewp : StateEffectWP S MirEffect}
    {body : CapturedMir} {s s' : MachineState}
    {Q : MirOutcome → S → Prop} {st : S}
    (h_step : stepMirFn body s = .tau (.running s'))
    (h_next : DWP ewp (mirTree body s') Q st) :
    DWP ewp (mirTree body s) Q st := by
  unfold mirTree at h_next ⊢
  rw [DWP.unfold_eq, ITree.observe_cofix]
  dsimp only [stepMirState]
  rw [h_step]
  exact h_next

/-- Step `DWP` across a `MirObsE` `.event tag` emission of `stepMirFn`. -/
theorem dwp_mirTree_emitEvent
    {S : Type} {ewp : StateEffectWP S MirEffect}
    {body : CapturedMir} {s s' : MachineState} {tag : Nat}
    {Q : MirOutcome → S → Prop} {st : S}
    (h_step : stepMirFn body s = MirStepNode.emitStep (.event tag) s')
    (h_next :
      ewp.wp (.inr (.inl (.emit (.event tag))))
        (fun _ st' => DWP ewp (mirTree body s') Q st') st) :
    DWP ewp (mirTree body s) Q st := by
  unfold mirTree at h_next ⊢
  rw [DWP.unfold_eq, ITree.observe_cofix]
  dsimp only [stepMirState]
  rw [h_step]
  exact h_next

/-- Conclude `DWP` at a terminal `.ret out` transition of `stepMirFn`. -/
theorem dwp_mirTree_ret
    {S : Type} {ewp : StateEffectWP S MirEffect}
    {body : CapturedMir} {s : MachineState} {out : MirOutcome}
    {Q : MirOutcome → S → Prop} {st : S}
    (h_step : stepMirFn body s = .ret out)
    (h_post : Q out st) :
    DWP ewp (mirTree body s) Q st := by
  unfold mirTree
  rw [DWP.unfold_eq, ITree.observe_cofix]
  dsimp only [stepMirState]
  rw [h_step]
  exact h_post

/--
Pure silent-step bounded runner: steps `stepMirFn body` through `.tau` transitions
until reaching `(targetBlock, 0)`. Preserves arbitrary logical state `S`
(including exact `List (Event MirEffect)` traces).
-/
def runMirTauToBlock
    (fuel : Nat) (body : CapturedMir) (targetBlock : BasicBlockIdx)
    (s : MachineState) : Option MachineState :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    if Nat.beq s.frame.blockIdx targetBlock && Nat.beq s.frame.stmtIdx 0 then
      some s
    else
      match stepMirFn body s with
      | .tau (.running s') => runMirTauToBlock fuel' body targetBlock s'
      | _ => none

/-- Soundness of `runMirTauToBlock` for any `StateEffectWP S MirEffect`. -/
theorem dwp_of_runMirTauToBlock
    {S : Type} {ewp : StateEffectWP S MirEffect}
    {body : CapturedMir} {targetBlock : BasicBlockIdx}
    {Q : MirOutcome → S → Prop} :
    (fuel : Nat) → ∀ {s s' : MachineState} {st : S},
      runMirTauToBlock fuel body targetBlock s = some s' →
      DWP ewp (mirTree body s') Q st →
      DWP ewp (mirTree body s) Q st
  | 0, _, _, _, h, _ => by nomatch h
  | fuel' + 1, s, s', st, h, h_next => by
    unfold runMirTauToBlock at h
    split at h
    · injection h with h_eq; subst h_eq; exact h_next
    · cases h_step : stepMirFn body s with
      | ret _ => rw [h_step] at h; nomatch h
      | vis _ _ => rw [h_step] at h; nomatch h
      | tau execNext =>
        rw [h_step] at h
        cases execNext with
        | running s₁ =>
          exact dwp_mirTree_tau h_step (dwp_of_runMirTauToBlock fuel' h h_next)
        | halted _ => nomatch h
        | faulted _ => nomatch h

private theorem dwlp_mirTree_tau
    {S : Type} {ewp : StateEffectWP S MirEffect}
    {body : CapturedMir} {s s' : MachineState}
    {Q : MirOutcome → S → Prop} {st : S}
    (h_step : stepMirFn body s = .tau (.running s'))
    (h_next : DWLP ewp (mirTree body s') Q st) :
    DWLP ewp (mirTree body s) Q st := by
  unfold mirTree
  rw [DWLP.unfold_eq, ITree.observe_cofix]
  dsimp only [stepMirState]
  rw [h_step]
  exact h_next

/-- Partial-correctness (`DWLP`) soundness of `runMirTauToBlock`. -/
theorem dwlp_of_runMirTauToBlock
    {S : Type} {ewp : StateEffectWP S MirEffect}
    {body : CapturedMir} {targetBlock : BasicBlockIdx}
    {Q : MirOutcome → S → Prop} :
    (fuel : Nat) → ∀ {s s' : MachineState} {st : S},
      runMirTauToBlock fuel body targetBlock s = some s' →
      DWLP ewp (mirTree body s') Q st →
      DWLP ewp (mirTree body s) Q st
  | 0, _, _, _, h, _ => by nomatch h
  | fuel' + 1, s, s', st, h, h_next => by
    unfold runMirTauToBlock at h
    split at h
    · injection h with h_eq; subst h_eq; exact h_next
    · cases h_step : stepMirFn body s with
      | ret _ => rw [h_step] at h; nomatch h
      | vis _ _ => rw [h_step] at h; nomatch h
      | tau execNext =>
        rw [h_step] at h
        cases execNext with
        | running s₁ =>
          exact dwlp_mirTree_tau h_step (dwlp_of_runMirTauToBlock fuel' h h_next)
        | halted _ => nomatch h
        | faulted _ => nomatch h

/-- Pure silent-step bounded runner to a root `.ret out` node (zero visible events). -/
def runMirTauToRet
    (fuel : Nat) (body : CapturedMir) (s : MachineState) : Option MirOutcome :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match stepMirFn body s with
    | .ret out => some out
    | .tau (.running s') => runMirTauToRet fuel' body s'
    | .tau (.halted out) => some out
    | _ => none

/-- Soundness of `runMirTauToRet` for any `StateEffectWP S MirEffect`. -/
theorem dwp_of_runMirTauToRet
    {S : Type} {ewp : StateEffectWP S MirEffect}
    {body : CapturedMir} {Q : MirOutcome → S → Prop} :
    (fuel : Nat) → ∀ {s : MachineState} {out : MirOutcome} {st : S},
      runMirTauToRet fuel body s = some out →
      Q out st →
      DWP ewp (mirTree body s) Q st
  | 0, _, _, _, h, _ => by nomatch h
  | fuel' + 1, s, out, st, h, h_q => by
    unfold runMirTauToRet at h
    cases h_step : stepMirFn body s with
    | ret out₀ =>
      rw [h_step] at h; injection h with h_eq; subst h_eq
      exact dwp_mirTree_ret h_step h_q
    | vis _ _ => rw [h_step] at h; nomatch h
    | tau execNext =>
      rw [h_step] at h
      cases execNext with
      | running s₁ =>
        exact dwp_mirTree_tau h_step (dwp_of_runMirTauToRet fuel' h h_q)
      | halted out₀ =>
        injection h with h_eq; subst h_eq
        unfold mirTree
        rw [DWP.unfold_eq, ITree.observe_cofix]
        dsimp only [stepMirState]
        rw [h_step]
        dsimp only [ITreeF.map]
        rw [DWP.unfold_eq, ITree.observe_cofix]
        exact h_q
      | faulted _ => nomatch h

/--
Pure bounded MIR stepper running `stepMirFn body` (consuming both silent `.tau`
steps and `MirObsE` emissions) until reaching `(targetBlock, 0)`.
-/
def runMirToBlock
    (fuel : Nat) (body : CapturedMir) (targetBlock : BasicBlockIdx)
    (s : MachineState) : Option MachineState :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    if Nat.beq s.frame.blockIdx targetBlock && Nat.beq s.frame.stmtIdx 0 then
      some s
    else
      match stepMirFn body s with
      | .tau (.running s') => runMirToBlock fuel' body targetBlock s'
      | .vis (.inr (.inl (.emit _))) k =>
        match k PUnit.unit with
        | .running s' => runMirToBlock fuel' body targetBlock s'
        | _ => none
      | _ => none

/-- Soundness of `runMirToBlock` under `[ObsTransparentWP ewp]`. -/
theorem dwp_of_runMirToBlock
    {ewp : EffectWP MirEffect} [h_obs : ObsTransparentWP ewp]
    {body : CapturedMir} {targetBlock : BasicBlockIdx}
    {Q : MirOutcome → PUnit → Prop} :
    (fuel : Nat) → ∀ {s s' : MachineState},
      runMirToBlock fuel body targetBlock s = some s' →
      DWP ewp (mirTree body s') Q PUnit.unit →
      DWP ewp (mirTree body s) Q PUnit.unit
  | 0, _, _, h, _ => by nomatch h
  | fuel' + 1, s, s', h, h_next => by
    unfold runMirToBlock at h
    split at h
    · injection h with h_eq; subst h_eq; exact h_next
    · cases h_step : stepMirFn body s with
      | ret _ => rw [h_step] at h; nomatch h
      | tau execNext =>
        rw [h_step] at h
        cases execNext with
        | running s₁ =>
          exact dwp_mirTree_tau h_step (dwp_of_runMirToBlock fuel' h h_next)
        | halted _ => nomatch h
        | faulted _ => nomatch h
      | vis req k =>
        rw [h_step] at h
        cases req with
        | inl _ => nomatch h
        | inr rest =>
          cases rest with
          | inr _ => nomatch h
          | inl obsReq =>
            cases obsReq with
            | emit obs =>
              dsimp only at h
              cases hk : k PUnit.unit with
              | running s₁ =>
                rw [hk] at h
                unfold mirTree
                rw [DWP.unfold_eq, ITree.observe_cofix]
                dsimp only [stepMirState]
                rw [h_step]
                dsimp only [ITreeF.map]
                apply h_obs.emit_wp obs
                rw [hk]
                exact dwp_of_runMirToBlock fuel' h h_next
              | halted _ => rw [hk] at h; nomatch h
              | faulted _ => rw [hk] at h; nomatch h

/--
Inspect whether `s` is positioned at a binary `TerminatorKind.switchInt`
(`branches = [(matchVal, elseBb)]`, `otherwise = thenBb`), returning
`(cond, discrBits, sThen₀, sElse₀)` where `cond = !(Nat.beq discrBits matchVal)`.
-/
def inspectBinarySwitch
    (body : CapturedMir) (s : MachineState) :
    Option (Bool × Nat × MachineState × MachineState) :=
  let currentBody := s.memory.activeCallee.getD body
  match currentBody.phase with
  | .other _ => none
  | _ =>
    match get? currentBody.basicBlocks s.frame.blockIdx with
    | none => none
    | some bb =>
      match get? bb.statements s.frame.stmtIdx with
      | some _ => none
      | none =>
        if s.frame.stmtIdx == length bb.statements then
          match bb.terminator.kind with
          | .switchInt discr { branches := [(matchVal, elseBb)], otherwise := thenBb } =>
            match
              evalOperand
                s.frame.locals
                discr
                s.memory.borrows
                s.memory.globals
                currentBody.layouts
                s.memory.callerLocals
            with
            | .ok (.scalar sc) locals' =>
              let cond := !(Nat.beq sc.bits matchVal)
              let sThen :=
                { s with frame := { blockIdx := thenBb, stmtIdx := 0, locals := locals' } }
              let sElse :=
                { s with frame := { blockIdx := elseBb, stmtIdx := 0, locals := locals' } }
              some (cond, sc.bits, sThen, sElse)
            | _ => none
          | _ => none
        else
          none

theorem stepMirFn_of_inspectBinarySwitch
    {body : CapturedMir} {s : MachineState}
    {cond : Bool} {bits : Nat} {sThen sElse : MachineState}
    (h : inspectBinarySwitch body s = some (cond, bits, sThen, sElse)) :
    stepMirFn body s =
      MirStepNode.emitStep (.event bits) (if cond then sThen else sElse) := by
  unfold inspectBinarySwitch at h
  unfold stepMirFn
  dsimp only at h ⊢
  split at h
  · nomatch h
  · next _ h_not_other =>
    split
    · next msg h_other => exact False.elim (h_not_other msg h_other)
    · cases h_bb : get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx with
      | none => rw [h_bb] at h; nomatch h
      | some bb =>
        rw [h_bb] at h
        dsimp only at h ⊢
        cases h_st : get? bb.statements s.frame.stmtIdx with
        | some _ => rw [h_st] at h; nomatch h
        | none =>
          rw [h_st] at h
          dsimp only at h ⊢
          cases h_len : (s.frame.stmtIdx == length bb.statements) with
          | false => rw [h_len] at h; nomatch h
          | true =>
            rw [h_len] at h
            simp only [ite_true] at h ⊢
            cases h_tk : bb.terminator.kind with
            | switchInt discr targets =>
              rw [h_tk] at h
              rcases targets with ⟨branches, thenBb⟩
              cases branches with
              | nil => nomatch h
              | cons hd tl =>
                rcases hd with ⟨matchVal, elseBb⟩
                cases tl with
                | cons _ _ => nomatch h
                | nil =>
                  dsimp only at h
                  unfold evalTerminator
                  rw [h_tk]
                  dsimp only
                  cases h_op :
                      evalOperand
                        s.frame.locals
                        discr
                        s.memory.borrows
                        s.memory.globals
                        (s.memory.activeCallee.getD body).layouts
                        s.memory.callerLocals with
                  | ub => rw [h_op] at h; nomatch h
                  | unsupported => rw [h_op] at h; nomatch h
                  | ok v locals' =>
                    rw [h_op] at h
                    cases v with
                    | unit => nomatch h
                    | ptr _ _ => nomatch h
                    | aggregate _ _ => nomatch h
                    | scalar sc =>
                      dsimp only at h
                      injection h with h_tuple
                      injection h_tuple with hc h_rest
                      injection h_rest with hb h_states
                      injection h_states with ht he
                      subst hc hb ht he
                      dsimp only
                      unfold lookupSwitchTarget
                      cases Nat.beq sc.bits matchVal <;>
                        simp [lookupSwitchTarget]
            | _ => rw [h_tk] at h; nomatch h

/--
Step `s` through silent `.tau` transitions within `fuel` steps until reaching a
binary `TerminatorKind.switchInt`.
-/
def runMirToBinarySwitch
    (fuel : Nat) (body : CapturedMir) (s : MachineState) :
    Option (Bool × Nat × MachineState × MachineState) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match inspectBinarySwitch body s with
    | some res => some res
    | none =>
      match stepMirFn body s with
      | .tau (.running s') => runMirToBinarySwitch fuel' body s'
      | _ => none

/--
Trace-general soundness of `runMirToBinarySwitch` for any `StateEffectWP S MirEffect`.
-/
theorem dwp_any_of_runMirToBinarySwitch
    {S : Type} {ewp : StateEffectWP S MirEffect}
    {body : CapturedMir} {Q : MirOutcome → S → Prop} :
    (fuel : Nat) →
      ∀ {s : MachineState} {cond : Bool} {bits : Nat}
        {sThen sElse : MachineState} {st : S},
        runMirToBinarySwitch fuel body s = some (cond, bits, sThen, sElse) →
        ewp.wp (.inr (.inl (.emit (.event bits))))
          (fun _ st' =>
            DWP ewp (mirTree body (if cond then sThen else sElse)) Q st')
          st →
        DWP ewp (mirTree body s) Q st
  | 0, _, _, _, _, _, _, h, _ => by nomatch h
  | fuel' + 1, s, cond, bits, sThen, sElse, st, h, h_after => by
    unfold runMirToBinarySwitch at h
    cases h_sw : inspectBinarySwitch body s with
    | some res =>
      rw [h_sw] at h
      injection h with h_eq; subst h_eq
      exact dwp_mirTree_emitEvent (stepMirFn_of_inspectBinarySwitch h_sw) h_after
    | none =>
      rw [h_sw] at h
      cases h_step : stepMirFn body s with
      | ret _ => rw [h_step] at h; nomatch h
      | vis _ _ => rw [h_step] at h; nomatch h
      | tau execNext =>
        rw [h_step] at h
        cases execNext with
        | running s₁ =>
          exact dwp_mirTree_tau h_step
            (dwp_any_of_runMirToBinarySwitch fuel' h h_after)
        | halted _ => nomatch h
        | faulted _ => nomatch h

/-- Stateless soundness of `runMirToBinarySwitch` under `[ObsTransparentWP ewp]`. -/
theorem dwp_of_runMirToBinarySwitch
    {ewp : EffectWP MirEffect} [h_obs : ObsTransparentWP ewp]
    {body : CapturedMir} {Q : MirOutcome → PUnit → Prop}
    {fuel : Nat} {s : MachineState} {cond : Bool} {bits : Nat}
    {sThen sElse : MachineState}
    (h : runMirToBinarySwitch fuel body s = some (cond, bits, sThen, sElse))
    (h_next : DWP ewp (mirTree body (if cond then sThen else sElse)) Q PUnit.unit) :
    DWP ewp (mirTree body s) Q PUnit.unit :=
  dwp_any_of_runMirToBinarySwitch fuel h (h_obs.emit_wp (.event bits) _ h_next)

/-! ### `TransPlan` Datatype, Symbolic Diamond Joining, and Loop Translation -/

/--
Untrusted control-flow & loop translation plan guiding `DWP` / `DWLP` execution
over a `V2026_06_01` `CapturedMir` body (`#100`, `#103`, `#109`).
-/
inductive TransPlan : Type where
  /-- Current basic block reaches `.return_` within `fuel` steps. -/
  | ret (fuel : Nat := 32)
  /-- Sub-plan leaf reaching `(targetBlock, 0)` within `fuel` steps. -/
  | jump (targetBlock : BasicBlockIdx) (fuel : Nat := 32)
  /-- Straight-line block(s) reaching `(nextBlock, 0)` within `fuel` steps,
      continuing with `nextPlan`. -/
  | seq (nextBlock : BasicBlockIdx) (nextPlan : TransPlan) (fuel : Nat := 32)
  /-- Diamond `switchInt` branch whose `thenPlan` (non-zero / `otherwise` arm)
      and `elsePlan` (matched / `0` arm) converge at `joinBlock`, where both
      symbolic frames merge into **one** `SymLocals` state via `zipLocalSlots`
      before running `joinPlan` once without path splitting. -/
  | branch
      (joinBlock : BasicBlockIdx)
      (thenPlan : TransPlan)
      (elsePlan : TransPlan)
      (joinPlan : TransPlan)
      (preFuel : Nat := 32)
  /-- Non-merging `switchInt` branch executing `thenPlan` on the non-zero arm
      and `elsePlan` on the matched / `0` arm. -/
  | splitBranch
      (thenPlan : TransPlan)
      (elsePlan : TransPlan)
      (preFuel : Nat := 32)
  /-- Natural `while` loop rooted at `headerBlock` with `Nat` termination rank /
      fuel `fuel`: steps the header condition within `condFuel` steps, executes
      `bodyPlan` back to `(headerBlock, 0)` when `cond = true`, and exits via
      `exitPlan` when `cond = false`. -/
  | loop
      (headerBlock : BasicBlockIdx)
      (fuel : Nat)
      (bodyPlan : TransPlan)
      (exitPlan : TransPlan)
      (condFuel : Nat := 32)
  deriving DecidableEq, Repr

/--
Execute a join-targeting sub-plan (`.jump`, `.seq`, or nested `.branch`) to its
join `MachineState`, merging nested diamonds via `zipLocalSlots`.
-/
def evalPlanToJoin
    (body : CapturedMir) : TransPlan → MachineState → Option MachineState
  | .jump targetBlock fuel, s =>
    runMirToBlock fuel body targetBlock s
  | .seq nextBlock nextPlan fuel, s =>
    match runMirToBlock fuel body nextBlock s with
    | some s' => evalPlanToJoin body nextPlan s'
    | none => none
  | .branch joinBlock thenPlan elsePlan joinPlan preFuel, s =>
    match runMirToBinarySwitch preFuel body s with
    | none => none
    | some (cond, _, sThen₀, sElse₀) =>
      match evalPlanToJoin body thenPlan sThen₀,
            evalPlanToJoin body elsePlan sElse₀ with
      | some sThen, some sElse =>
        if Nat.beq sThen.frame.blockIdx joinBlock &&
           Nat.beq sElse.frame.blockIdx joinBlock &&
           Nat.beq sThen.frame.stmtIdx 0 &&
           Nat.beq sElse.frame.stmtIdx 0 &&
           Nat.beq sThen.frame.locals.length sElse.frame.locals.length then
          evalPlanToJoin body joinPlan
            { frame := {
                blockIdx := joinBlock
                stmtIdx := 0
                locals := zipLocalSlots cond sThen.frame.locals sElse.frame.locals
              }
              memory := sThen.memory }
        else
          none
      | _, _ => none
  | _, _ => none

/--
Propositional memory-agreement side condition across any nested `.branch` nodes
inside an `evalPlanToJoin` sub-plan (`True` for `.jump` and `.seq`).
-/
def joinPlanMemConsistent
    (body : CapturedMir) : TransPlan → MachineState → Prop
  | .jump _ _, _ => True
  | .seq nextBlock nextPlan fuel, s =>
    match runMirToBlock fuel body nextBlock s with
    | some s' => joinPlanMemConsistent body nextPlan s'
    | none => False
  | .branch joinBlock thenPlan elsePlan joinPlan preFuel, s =>
    match runMirToBinarySwitch preFuel body s with
    | none => False
    | some (cond, _, sThen₀, sElse₀) =>
      match evalPlanToJoin body thenPlan sThen₀,
            evalPlanToJoin body elsePlan sElse₀ with
      | some sThen, some sElse =>
        sThen.memory = sElse.memory ∧
        joinPlanMemConsistent body thenPlan sThen₀ ∧
        joinPlanMemConsistent body elsePlan sElse₀ ∧
        joinPlanMemConsistent body joinPlan
          { frame := {
              blockIdx := joinBlock
              stmtIdx := 0
              locals := zipLocalSlots cond sThen.frame.locals sElse.frame.locals
            }
            memory := sThen.memory }
      | _, _ => False
  | _, _ => False

/-- Soundness of `evalPlanToJoin` for `DWP` on `mirTree`. -/
theorem dwp_of_evalPlanToJoin
    {ewp : EffectWP MirEffect} [ObsTransparentWP ewp]
    {body : CapturedMir} {Q : MirOutcome → PUnit → Prop} :
    (plan : TransPlan) → ∀ {s sJoin : MachineState},
      evalPlanToJoin body plan s = some sJoin →
      joinPlanMemConsistent body plan s →
      DWP ewp (mirTree body sJoin) Q PUnit.unit →
      DWP ewp (mirTree body s) Q PUnit.unit
  | .ret _, _, _, h, _, _ => by nomatch h
  | .splitBranch _ _ _, _, _, h, _, _ => by nomatch h
  | .loop _ _ _ _ _, _, _, h, _, _ => by nomatch h
  | .jump targetBlock fuel, _, _, h, _, h_next =>
    dwp_of_runMirToBlock fuel h h_next
  | .seq nextBlock nextPlan fuel, s, sJoin, h, h_mem, h_next => by
    unfold evalPlanToJoin at h
    unfold joinPlanMemConsistent at h_mem
    cases h_blk : runMirToBlock fuel body nextBlock s with
    | none => rw [h_blk] at h; nomatch h
    | some s' =>
      rw [h_blk] at h h_mem
      exact dwp_of_runMirToBlock fuel h_blk
        (dwp_of_evalPlanToJoin nextPlan h h_mem h_next)
  | .branch joinBlock thenPlan elsePlan joinPlan preFuel, s, sJoin, h, h_mem, h_next => by
    unfold evalPlanToJoin at h
    unfold joinPlanMemConsistent at h_mem
    cases h_sw : runMirToBinarySwitch preFuel body s with
    | none => rw [h_sw] at h; nomatch h
    | some swRes =>
      rcases swRes with ⟨cond, bits, sThen₀, sElse₀⟩
      rw [h_sw] at h h_mem
      dsimp only at h h_mem
      cases h_t : evalPlanToJoin body thenPlan sThen₀ with
      | none => rw [h_t] at h; nomatch h
      | some sThen =>
        cases h_e : evalPlanToJoin body elsePlan sElse₀ with
        | none => rw [h_t, h_e] at h; nomatch h
        | some sElse =>
          rw [h_t, h_e] at h h_mem
          rcases h_mem with ⟨h_meq, h_mt, h_me, h_mj⟩
          dsimp only at h
          cases h_chk :
            (Nat.beq sThen.frame.blockIdx joinBlock &&
             Nat.beq sElse.frame.blockIdx joinBlock &&
             Nat.beq sThen.frame.stmtIdx 0 &&
             Nat.beq sElse.frame.stmtIdx 0 &&
             Nat.beq sThen.frame.locals.length sElse.frame.locals.length) with
          | false => rw [h_chk] at h; nomatch h
          | true =>
            rw [h_chk] at h
            simp only [ite_true] at h
            simp only [Bool.and_eq_true] at h_chk
            rcases h_chk with ⟨⟨⟨⟨h_tb, h_eb⟩, h_ts⟩, h_es⟩, h_len⟩
            have h_tb' : sThen.frame.blockIdx = joinBlock := Nat.eq_of_beq_eq_true h_tb
            have h_eb' : sElse.frame.blockIdx = joinBlock := Nat.eq_of_beq_eq_true h_eb
            have h_ts' : sThen.frame.stmtIdx = 0 := Nat.eq_of_beq_eq_true h_ts
            have h_es' : sElse.frame.stmtIdx = 0 := Nat.eq_of_beq_eq_true h_es
            have h_len' : sThen.frame.locals.length = sElse.frame.locals.length :=
              Nat.eq_of_beq_eq_true h_len
            have h_zipped :=
              dwp_of_evalPlanToJoin joinPlan h h_mj h_next
            apply dwp_of_runMirToBinarySwitch h_sw
            cases cond with
            | true =>
              rw [zipLocalSlots_eq_ite true h_len'] at h_zipped
              simp only [ite_true] at h_zipped
              have h_st_eq :
                  ({ frame := { blockIdx := joinBlock, stmtIdx := 0, locals := sThen.frame.locals }
                     memory := sThen.memory } : MachineState) = sThen := by
                rcases sThen with ⟨⟨_, _, _⟩, _⟩
                dsimp only at h_tb' h_ts'
                subst h_tb' h_ts'
                rfl
              rw [h_st_eq] at h_zipped
              exact dwp_of_evalPlanToJoin thenPlan h_t h_mt h_zipped
            | false =>
              rw [zipLocalSlots_eq_ite false h_len'] at h_zipped
              simp only [Bool.false_eq_true, ite_false] at h_zipped
              have h_st_eq :
                  ({ frame := { blockIdx := joinBlock, stmtIdx := 0, locals := sElse.frame.locals }
                     memory := sThen.memory } : MachineState) = sElse := by
                rw [h_meq]
                rcases sElse with ⟨⟨_, _, _⟩, _⟩
                dsimp only at h_eb' h_es'
                subst h_eb' h_es'
                rfl
              rw [h_st_eq] at h_zipped
              exact dwp_of_evalPlanToJoin elsePlan h_e h_me h_zipped

/--
Plan-guided weakest-precondition translator over `V2026_06_01` `CapturedMir`.
-/
def wpTransPlan
    (ewp : EffectWP MirEffect) (body : CapturedMir)
    (plan : TransPlan) (post : MirOutcome → Prop) (s : MachineState) : Prop :=
  match plan with
  | .ret fuel =>
    wpCoalBounded fuel ewp (stepMirState body)
      (fun out _ => post out) (.running s) PUnit.unit
  | .jump _ _ => False
  | .seq nextBlock nextPlan fuel =>
    match runMirToBlock fuel body nextBlock s with
    | some s' => wpTransPlan ewp body nextPlan post s'
    | none => False
  | .branch joinBlock thenPlan elsePlan joinPlan preFuel =>
    match runMirToBinarySwitch preFuel body s with
    | none => False
    | some (cond, _, sThen₀, sElse₀) =>
      match evalPlanToJoin body thenPlan sThen₀,
            evalPlanToJoin body elsePlan sElse₀ with
      | some sThen, some sElse =>
        sThen.frame.blockIdx = joinBlock ∧
        sElse.frame.blockIdx = joinBlock ∧
        sThen.frame.stmtIdx = 0 ∧
        sElse.frame.stmtIdx = 0 ∧
        sThen.frame.locals.length = sElse.frame.locals.length ∧
        sThen.memory = sElse.memory ∧
        joinPlanMemConsistent body thenPlan sThen₀ ∧
        joinPlanMemConsistent body elsePlan sElse₀ ∧
        wpTransPlan ewp body joinPlan post
          { frame := {
              blockIdx := joinBlock
              stmtIdx := 0
              locals := zipLocalSlots cond sThen.frame.locals sElse.frame.locals
            }
            memory := sThen.memory }
      | _, _ => False
  | .splitBranch thenPlan elsePlan preFuel =>
    match runMirToBinarySwitch preFuel body s with
    | none => False
    | some (cond, _, sThen₀, sElse₀) =>
      (cond = true → wpTransPlan ewp body thenPlan post sThen₀) ∧
      (cond = false → wpTransPlan ewp body elsePlan post sElse₀)
  | .loop headerBlock fuel bodyPlan exitPlan condFuel =>
    s.frame.blockIdx = headerBlock ∧
    s.frame.stmtIdx = 0 ∧
    match runMirToBinarySwitch condFuel body s with
    | none => False
    | some (cond, _, sThen₀, sElse₀) =>
      match fuel with
      | 0 =>
        cond = false ∧ wpTransPlan ewp body exitPlan post sElse₀
      | fuel' + 1 =>
        (cond = false → wpTransPlan ewp body exitPlan post sElse₀) ∧
        (cond = true →
          match evalPlanToJoin body bodyPlan sThen₀ with
          | none => False
          | some sNext =>
            joinPlanMemConsistent body bodyPlan sThen₀ ∧
            wpTransPlan ewp body
              (.loop headerBlock fuel' bodyPlan exitPlan condFuel) post sNext)
termination_by sizeOf plan

private theorem _materialize_transPlan_eqs : True :=
  let _ := @wpTransPlan.eq_1
  let _ := @wpTransPlan.eq_2
  let _ := @wpTransPlan.eq_3
  let _ := @wpTransPlan.eq_4
  let _ := @wpTransPlan.eq_5
  let _ := @wpTransPlan.eq_6
  let _ := @wpTransPlan.eq_def
  let _ := @evalPlanToJoin.eq_1
  let _ := @evalPlanToJoin.eq_2
  let _ := @evalPlanToJoin.eq_3
  let _ := @evalPlanToJoin.eq_4
  let _ := @evalPlanToJoin.eq_def
  let _ := @joinPlanMemConsistent.eq_1
  let _ := @joinPlanMemConsistent.eq_2
  let _ := @joinPlanMemConsistent.eq_3
  let _ := @joinPlanMemConsistent.eq_4
  let _ := @joinPlanMemConsistent.eq_def
  True.intro

private theorem wpCoalBounded_mono
    {S State : Type} {E : Effect} {R : Type}
    {ewp : StateEffectWP S E} {step : State → ITreeF E R State}
    {P Q : R → S → Prop} (h_imp : ∀ r s, P r s → Q r s) :
    (fuel : Nat) → ∀ {st : State} {s : S},
      wpCoalBounded fuel ewp step P st s →
      wpCoalBounded fuel ewp step Q st s
  | 0, _, _, h => False.elim h
  | fuel' + 1, st, s, h => by
    unfold wpCoalBounded at h ⊢
    cases h_st : step st <;> simp only [h_st] at h ⊢
    · exact h_imp _ _ h
    · exact wpCoalBounded_mono h_imp fuel' h
    · exact ewp.mono (fun _ _ hw => wpCoalBounded_mono h_imp fuel' hw) h

/-- Postcondition monotonicity for `wpTransPlan`. -/
theorem wpTransPlan_mono
    {ewp : EffectWP MirEffect} {body : CapturedMir}
    {P Q : MirOutcome → Prop} (h_imp : ∀ out, P out → Q out) :
    ∀ {plan : TransPlan} {s : MachineState},
      wpTransPlan ewp body plan P s →
      wpTransPlan ewp body plan Q s
  | .ret fuel, _, h => by
    unfold wpTransPlan at h ⊢
    exact wpCoalBounded_mono (fun out _ hp => h_imp out hp) fuel h
  | .jump _ _, _, h => by
    unfold wpTransPlan at h
    exact False.elim h
  | .seq nextBlock nextPlan fuel, s, h => by
    unfold wpTransPlan at h ⊢
    cases h_blk : runMirToBlock fuel body nextBlock s with
    | none => rw [h_blk] at h; exact False.elim h
    | some s' =>
      rw [h_blk] at h
      exact wpTransPlan_mono h_imp h
  | .branch joinBlock thenPlan elsePlan joinPlan preFuel, s, h => by
    unfold wpTransPlan at h ⊢
    cases h_sw : runMirToBinarySwitch preFuel body s with
    | none => rw [h_sw] at h; exact False.elim h
    | some swRes =>
      rcases swRes with ⟨cond, bits, sThen₀, sElse₀⟩
      rw [h_sw] at h
      dsimp only at h ⊢
      cases h_t : evalPlanToJoin body thenPlan sThen₀ with
      | none => rw [h_t] at h; exact False.elim h
      | some sThen =>
        cases h_e : evalPlanToJoin body elsePlan sElse₀ with
        | none => rw [h_t, h_e] at h; exact False.elim h
        | some sElse =>
          rw [h_t, h_e] at h
          rcases h with
            ⟨h_tb, h_eb, h_ts, h_es, h_len, h_meq, h_mt, h_me, h_join⟩
          exact ⟨h_tb, h_eb, h_ts, h_es, h_len, h_meq, h_mt, h_me,
                 wpTransPlan_mono h_imp h_join⟩
  | .splitBranch thenPlan elsePlan preFuel, s, h => by
    unfold wpTransPlan at h ⊢
    cases h_sw : runMirToBinarySwitch preFuel body s with
    | none => rw [h_sw] at h; exact False.elim h
    | some swRes =>
      rcases swRes with ⟨cond, bits, sThen₀, sElse₀⟩
      rw [h_sw] at h
      exact ⟨fun ht => wpTransPlan_mono h_imp (h.1 ht),
             fun hf => wpTransPlan_mono h_imp (h.2 hf)⟩
  | .loop headerBlock fuel bodyPlan exitPlan condFuel, s, h => by
    unfold wpTransPlan at h ⊢
    rcases h with ⟨hb, hs, h_rest⟩
    refine ⟨hb, hs, ?_⟩
    cases h_sw : runMirToBinarySwitch condFuel body s with
    | none => rw [h_sw] at h_rest; exact False.elim h_rest
    | some swRes =>
      rcases swRes with ⟨cond, bits, sThen₀, sElse₀⟩
      rw [h_sw] at h_rest
      cases fuel with
      | zero =>
        exact ⟨h_rest.1, wpTransPlan_mono h_imp h_rest.2⟩
      | succ fuel' =>
        refine ⟨fun hf => wpTransPlan_mono h_imp (h_rest.1 hf), fun ht => ?_⟩
        have h_body := h_rest.2 ht
        cases h_join : evalPlanToJoin body bodyPlan sThen₀ with
        | none => rw [h_join] at h_body; exact False.elim h_body
        | some sNext =>
          rw [h_join] at h_body
          exact ⟨h_body.1,
            wpTransPlan_mono h_imp
              (plan := .loop headerBlock fuel' bodyPlan exitPlan condFuel)
              h_body.2⟩
termination_by plan => sizeOf plan

/--
Fundamental total-correctness (`DWP`) soundness theorem for `wpTransPlan`.
-/
theorem dwp_of_wpTransPlan
    {ewp : EffectWP MirEffect} [ObsTransparentWP ewp]
    {body : CapturedMir} {post : MirOutcome → Prop} :
    (plan : TransPlan) → ∀ {s : MachineState},
      wpTransPlan ewp body plan post s →
      DWP ewp (mirTree body s) (fun out _ => post out) PUnit.unit
  | .ret fuel, _, h => by
    unfold wpTransPlan at h
    exact dwp_cofix_of_wpCoalBounded fuel h
  | .jump _ _, _, h => by
    unfold wpTransPlan at h
    exact False.elim h
  | .seq nextBlock nextPlan fuel, s, h => by
    unfold wpTransPlan at h
    cases h_blk : runMirToBlock fuel body nextBlock s with
    | none => rw [h_blk] at h; exact False.elim h
    | some s' =>
      rw [h_blk] at h
      exact dwp_of_runMirToBlock fuel h_blk (dwp_of_wpTransPlan nextPlan h)
  | .branch joinBlock thenPlan elsePlan joinPlan preFuel, s, h => by
    unfold wpTransPlan at h
    cases h_sw : runMirToBinarySwitch preFuel body s with
    | none => rw [h_sw] at h; exact False.elim h
    | some swRes =>
      rcases swRes with ⟨cond, bits, sThen₀, sElse₀⟩
      rw [h_sw] at h
      dsimp only at h
      cases h_t : evalPlanToJoin body thenPlan sThen₀ with
      | none => rw [h_t] at h; exact False.elim h
      | some sThen =>
        cases h_e : evalPlanToJoin body elsePlan sElse₀ with
        | none => rw [h_t, h_e] at h; exact False.elim h
        | some sElse =>
          rw [h_t, h_e] at h
          rcases h with
            ⟨h_tb, h_eb, h_ts, h_es, h_len, h_meq, h_mt, h_me, h_join⟩
          have h_dwp_join := dwp_of_wpTransPlan joinPlan h_join
          apply dwp_of_runMirToBinarySwitch h_sw
          cases cond with
          | true =>
            rw [zipLocalSlots_eq_ite true h_len] at h_dwp_join
            simp only [ite_true] at h_dwp_join
            have h_st_eq :
                ({ frame := { blockIdx := joinBlock, stmtIdx := 0, locals := sThen.frame.locals }
                   memory := sThen.memory } : MachineState) = sThen := by
              rcases sThen with ⟨⟨_, _, _⟩, _⟩
              dsimp only at h_tb h_ts
              subst h_tb h_ts
              rfl
            rw [h_st_eq] at h_dwp_join
            exact dwp_of_evalPlanToJoin thenPlan h_t h_mt h_dwp_join
          | false =>
            rw [zipLocalSlots_eq_ite false h_len] at h_dwp_join
            simp only [Bool.false_eq_true, ite_false] at h_dwp_join
            have h_st_eq :
                ({ frame := { blockIdx := joinBlock, stmtIdx := 0, locals := sElse.frame.locals }
                   memory := sThen.memory } : MachineState) = sElse := by
              rw [h_meq]
              rcases sElse with ⟨⟨_, _, _⟩, _⟩
              dsimp only at h_eb h_es
              subst h_eb h_es
              rfl
            rw [h_st_eq] at h_dwp_join
            exact dwp_of_evalPlanToJoin elsePlan h_e h_me h_dwp_join
  | .splitBranch thenPlan elsePlan preFuel, s, h => by
    unfold wpTransPlan at h
    cases h_sw : runMirToBinarySwitch preFuel body s with
    | none => rw [h_sw] at h; exact False.elim h
    | some swRes =>
      rcases swRes with ⟨cond, bits, sThen₀, sElse₀⟩
      rw [h_sw] at h
      apply dwp_of_runMirToBinarySwitch h_sw
      cases cond with
      | true =>
        exact dwp_of_wpTransPlan thenPlan (h.1 rfl)
      | false =>
        exact dwp_of_wpTransPlan elsePlan (h.2 rfl)
  | .loop headerBlock fuel bodyPlan exitPlan condFuel, s, h => by
    unfold wpTransPlan at h
    rcases h with ⟨_, _, h_rest⟩
    cases h_sw : runMirToBinarySwitch condFuel body s with
    | none => rw [h_sw] at h_rest; exact False.elim h_rest
    | some swRes =>
      rcases swRes with ⟨cond, bits, sThen₀, sElse₀⟩
      rw [h_sw] at h_rest
      cases fuel with
      | zero =>
        rcases h_rest with ⟨h_cond, h_exit⟩
        subst h_cond
        apply dwp_of_runMirToBinarySwitch h_sw
        exact dwp_of_wpTransPlan exitPlan h_exit
      | succ fuel' =>
        rcases h_rest with ⟨h_false, h_true⟩
        apply dwp_of_runMirToBinarySwitch h_sw
        cases cond with
        | false =>
          exact dwp_of_wpTransPlan exitPlan (h_false rfl)
        | true =>
          have h_body := h_true rfl
          cases h_join : evalPlanToJoin body bodyPlan sThen₀ with
          | none => rw [h_join] at h_body; exact False.elim h_body
          | some sNext =>
            rw [h_join] at h_body
            rcases h_body with ⟨h_mem, h_rec⟩
            exact dwp_of_evalPlanToJoin bodyPlan h_join h_mem
              (dwp_of_wpTransPlan (.loop headerBlock fuel' bodyPlan exitPlan condFuel) h_rec)
termination_by plan => sizeOf plan

/-- Partial-correctness (`DWLP`) corollary of `dwp_of_wpTransPlan`. -/
theorem dwlp_of_wpTransPlan
    {ewp : EffectWP MirEffect} [ObsTransparentWP ewp]
    {body : CapturedMir} {plan : TransPlan} {post : MirOutcome → Prop}
    {s : MachineState}
    (h : wpTransPlan ewp body plan post s) :
    DWLP ewp (mirTree body s) (fun out _ => post out) PUnit.unit :=
  (dwp_of_wpTransPlan plan h).toDWLP

/-- Lift `wpTransPlan` to `DWP` on `mirStatefulTree`. -/
theorem dwp_mirStatefulTree_of_transPlan
    {ewp : EffectWP MirEffect} [ObsTransparentWP ewp]
    {body : CapturedMir} {args : List Value} {mem : Memory}
    {plan : TransPlan} {post : MirOutcome → Prop}
    (h : wpTransPlan ewp body plan post (initMachineStateWithMemory body args mem)) :
    DWP ewp (mirStatefulTree body args mem) (fun out _ => post out) PUnit.unit :=
  dwp_of_wpTransPlan plan h

/-- Lift `wpTransPlan` to `DWP` on `mirOpenTree` (`mirCallTree`). -/
theorem dwp_mirOpenTree_of_transPlan
    {ewp : EffectWP MirEffect} [ObsTransparentWP ewp]
    {body : CapturedMir} {args : List Value}
    {plan : TransPlan} {post : MirOutcome → Prop}
    (h : wpTransPlan ewp body plan post (initMachineState body args)) :
    DWP ewp (mirOpenTree body args) (fun out _ => post out) PUnit.unit :=
  dwp_of_wpTransPlan plan h

/-- Prove a stateless `VerificationResult c` via an input-indexed `TransPlan`. -/
theorem verifyByTransPlan
    {ewp : EffectWP MirEffect} [ObsTransparentWP ewp] [PureSoundWP ewp]
    (c : Claim)
    (plan : List Value → TransPlan)
    (h_plan :
      ∀ args : List Value,
        c.pre args →
        wpTransPlan ewp c.body (plan args)
          (fun out =>
            ∀ retVal mem', out = .normal (retVal, mem') → c.post args retVal)
          (initMachineState c.body args)) :
    VerificationResult c := by
  refine ⟨fun args h_pre => ?_⟩
  have h_adeq :=
    dwlp_pure_adequacy (dwp_mirOpenTree_of_transPlan (h_plan args h_pre)).toDWLP
  exact ⟨h_adeq.1, fun outPair h_ret _ retVal mem' h_out =>
    h_adeq.2 outPair.1 outPair.2 h_ret retVal mem' h_out⟩

/-- Prove a `StatefulVerificationResult c` via an input-indexed `TransPlan`. -/
theorem verifyStatefulByTransPlan
    {ewp : EffectWP MirEffect} [ObsTransparentWP ewp] [PureSoundWP ewp]
    (c : StatefulClaim)
    (plan : List Value → Memory → TransPlan)
    (h_plan :
      ∀ args mem,
        c.pre args mem →
        wpTransPlan ewp c.body (plan args mem)
          (fun out =>
            ∀ retVal mem',
              out = .normal (retVal, mem') → c.post args mem retVal mem')
          (initMachineStateWithMemory c.body args mem)) :
    StatefulVerificationResult c := by
  refine ⟨fun args mem h_pre => ?_⟩
  have h_adeq :=
    dwlp_pure_adequacy (dwp_mirStatefulTree_of_transPlan (h_plan args mem h_pre)).toDWLP
  exact ⟨h_adeq.1, fun outPair h_ret _ retVal mem' h_out =>
    h_adeq.2 outPair.1 outPair.2 h_ret retVal mem' h_out⟩

/-- Prove a `TotalVerificationResult c` via an input-indexed `TransPlan`. -/
theorem verifyTotalByTransPlan
    {ewp : EffectWP MirEffect} [ObsTransparentWP ewp] [PureSoundWP ewp]
    (c : TotalClaim)
    (plan : List Value → Memory → TransPlan)
    (h_plan :
      ∀ args mem,
        c.pre args mem →
        wpTransPlan ewp c.body (plan args mem)
          (fun out =>
            ∃ retVal mem',
              out = .normal (retVal, mem') ∧ c.post args mem retVal mem')
          (initMachineStateWithMemory c.body args mem)) :
    TotalVerificationResult c :=
  ⟨fun args mem h_pre =>
    dwp_pure_adequacy (dwp_mirStatefulTree_of_transPlan (h_plan args mem h_pre))⟩

/-! ### Coinductive `DWLP` Loop-Invariant Rule for Unbounded Loops -/

private inductive MirStepStar
    (body : CapturedMir) (Target : MachineState → Prop) : MachineState → Prop where
  | done {s : MachineState} : Target s → MirStepStar body Target s
  | tau {s s' : MachineState} :
      stepMirFn body s = .tau (.running s') →
      MirStepStar body Target s' →
      MirStepStar body Target s
  | emit {s s' : MachineState} {obs : MirObs} {k : PUnit → MirExecState} :
      stepMirFn body s = .vis (.inr (.inl (.emit obs))) k →
      k PUnit.unit = .running s' →
      MirStepStar body Target s' →
      MirStepStar body Target s

private theorem MirStepStar.mono
    {body : CapturedMir} {P Q : MachineState → Prop}
    (h_imp : ∀ s, P s → Q s) :
    ∀ {s : MachineState}, MirStepStar body P s → MirStepStar body Q s
  | _, .done hp => .done (h_imp _ hp)
  | _, .tau h_st h_rest => .tau h_st (MirStepStar.mono h_imp h_rest)
  | _, .emit h_st hk h_rest => .emit h_st hk (MirStepStar.mono h_imp h_rest)

private theorem MirStepStar.trans
    {body : CapturedMir} {P Q : MachineState → Prop}
    (h_pq : ∀ s, P s → MirStepStar body Q s) :
    ∀ {s : MachineState}, MirStepStar body P s → MirStepStar body Q s
  | _, .done hp => h_pq _ hp
  | _, .tau h_st h_rest => .tau h_st (MirStepStar.trans h_pq h_rest)
  | _, .emit h_st hk h_rest => .emit h_st hk (MirStepStar.trans h_pq h_rest)

private theorem mirStepStar_of_runMirToBlock
    {body : CapturedMir} {targetBlock : BasicBlockIdx} :
    (fuel : Nat) → ∀ {s s' : MachineState},
      runMirToBlock fuel body targetBlock s = some s' →
      MirStepStar body (· = s') s
  | 0, _, _, h => by nomatch h
  | fuel' + 1, s, s', h => by
    unfold runMirToBlock at h
    split at h
    · injection h with h_eq; subst h_eq; exact .done rfl
    · cases h_step : stepMirFn body s with
      | ret _ => rw [h_step] at h; nomatch h
      | tau execNext =>
        rw [h_step] at h
        cases execNext with
        | running s₁ =>
          exact .tau h_step (mirStepStar_of_runMirToBlock fuel' h)
        | halted _ => nomatch h
        | faulted _ => nomatch h
      | vis req k =>
        rw [h_step] at h
        cases req with
        | inl _ => nomatch h
        | inr rest =>
          cases rest with
          | inr _ => nomatch h
          | inl obsReq =>
            cases obsReq with
            | emit obs =>
              dsimp only at h
              cases hk : k PUnit.unit with
              | running s₁ =>
                rw [hk] at h
                exact .emit h_step hk (mirStepStar_of_runMirToBlock fuel' h)
              | halted _ => rw [hk] at h; nomatch h
              | faulted _ => rw [hk] at h; nomatch h

private theorem mirStepStar_of_runMirToBinarySwitch
    {body : CapturedMir} :
    (fuel : Nat) → ∀ {s : MachineState} {cond : Bool} {bits : Nat}
      {sThen sElse : MachineState},
      runMirToBinarySwitch fuel body s = some (cond, bits, sThen, sElse) →
      MirStepStar body
        (fun sSw =>
          inspectBinarySwitch body sSw = some (cond, bits, sThen, sElse)) s
  | 0, _, _, _, _, _, h => by nomatch h
  | fuel' + 1, s, cond, bits, sThen, sElse, h => by
    unfold runMirToBinarySwitch at h
    cases h_ins : inspectBinarySwitch body s with
    | some res =>
      rw [h_ins] at h; injection h with h_eq; subst h_eq
      exact .done h_ins
    | none =>
      rw [h_ins] at h
      cases h_step : stepMirFn body s with
      | ret _ => rw [h_step] at h; nomatch h
      | vis _ _ => rw [h_step] at h; nomatch h
      | tau execNext =>
        rw [h_step] at h
        cases execNext with
        | running s₁ =>
          exact .tau h_step (mirStepStar_of_runMirToBinarySwitch fuel' h)
        | halted _ => nomatch h
        | faulted _ => nomatch h

private theorem mirStepStar_of_evalPlanToJoin
    {body : CapturedMir} :
    (plan : TransPlan) → ∀ {s sJoin : MachineState},
      evalPlanToJoin body plan s = some sJoin →
      joinPlanMemConsistent body plan s →
      MirStepStar body (· = sJoin) s
  | .ret _, _, _, h, _ => by nomatch h
  | .splitBranch _ _ _, _, _, h, _ => by nomatch h
  | .loop _ _ _ _ _, _, _, h, _ => by nomatch h
  | .jump _ fuel, _, _, h, _ =>
    mirStepStar_of_runMirToBlock fuel h
  | .seq nextBlock nextPlan fuel, s, sJoin, h, h_mem => by
    unfold evalPlanToJoin at h
    unfold joinPlanMemConsistent at h_mem
    cases h_blk : runMirToBlock fuel body nextBlock s with
    | none => rw [h_blk] at h; nomatch h
    | some s' =>
      rw [h_blk] at h h_mem
      exact MirStepStar.trans
        (fun _ h_eq => h_eq ▸ mirStepStar_of_evalPlanToJoin nextPlan h h_mem)
        (mirStepStar_of_runMirToBlock fuel h_blk)
  | .branch joinBlock thenPlan elsePlan joinPlan preFuel, s, sJoin, h, h_mem => by
    unfold evalPlanToJoin at h
    unfold joinPlanMemConsistent at h_mem
    cases h_sw : runMirToBinarySwitch preFuel body s with
    | none => rw [h_sw] at h; nomatch h
    | some swRes =>
      rcases swRes with ⟨cond, bits, sThen₀, sElse₀⟩
      rw [h_sw] at h h_mem
      dsimp only at h h_mem
      cases h_t : evalPlanToJoin body thenPlan sThen₀ with
      | none => rw [h_t] at h; nomatch h
      | some sThen =>
        cases h_e : evalPlanToJoin body elsePlan sElse₀ with
        | none => rw [h_t, h_e] at h; nomatch h
        | some sElse =>
          rw [h_t, h_e] at h h_mem
          rcases h_mem with ⟨h_meq, h_mt, h_me, h_mj⟩
          dsimp only at h
          cases h_chk :
            (Nat.beq sThen.frame.blockIdx joinBlock &&
             Nat.beq sElse.frame.blockIdx joinBlock &&
             Nat.beq sThen.frame.stmtIdx 0 &&
             Nat.beq sElse.frame.stmtIdx 0 &&
             Nat.beq sThen.frame.locals.length sElse.frame.locals.length) with
          | false => rw [h_chk] at h; nomatch h
          | true =>
            rw [h_chk] at h
            simp only [ite_true] at h
            simp only [Bool.and_eq_true] at h_chk
            rcases h_chk with ⟨⟨⟨⟨h_tb, h_eb⟩, h_ts⟩, h_es⟩, h_len⟩
            have h_tb' : sThen.frame.blockIdx = joinBlock := Nat.eq_of_beq_eq_true h_tb
            have h_eb' : sElse.frame.blockIdx = joinBlock := Nat.eq_of_beq_eq_true h_eb
            have h_ts' : sThen.frame.stmtIdx = 0 := Nat.eq_of_beq_eq_true h_ts
            have h_es' : sElse.frame.stmtIdx = 0 := Nat.eq_of_beq_eq_true h_es
            have h_len' : sThen.frame.locals.length = sElse.frame.locals.length :=
              Nat.eq_of_beq_eq_true h_len
            have h_zipped := mirStepStar_of_evalPlanToJoin joinPlan h h_mj
            refine MirStepStar.trans ?_ (mirStepStar_of_runMirToBinarySwitch preFuel h_sw)
            intro sSw h_ins
            refine .emit (stepMirFn_of_inspectBinarySwitch h_ins) rfl ?_
            cases cond with
            | true =>
              rw [zipLocalSlots_eq_ite true h_len'] at h_zipped
              simp only [ite_true] at h_zipped
              have h_st_eq :
                  ({ frame := { blockIdx := joinBlock, stmtIdx := 0, locals := sThen.frame.locals }
                     memory := sThen.memory } : MachineState) = sThen := by
                rcases sThen with ⟨⟨_, _, _⟩, _⟩
                dsimp only at h_tb' h_ts'; subst h_tb' h_ts'; rfl
              rw [h_st_eq] at h_zipped
              exact MirStepStar.trans
                (fun _ h_eq => h_eq ▸ h_zipped)
                (mirStepStar_of_evalPlanToJoin thenPlan h_t h_mt)
            | false =>
              rw [zipLocalSlots_eq_ite false h_len'] at h_zipped
              simp only [Bool.false_eq_true, ite_false] at h_zipped
              have h_st_eq :
                  ({ frame := { blockIdx := joinBlock, stmtIdx := 0, locals := sElse.frame.locals }
                     memory := sThen.memory } : MachineState) = sElse := by
                rw [h_meq]
                rcases sElse with ⟨⟨_, _, _⟩, _⟩
                dsimp only at h_eb' h_es'; subst h_eb' h_es'; rfl
              rw [h_st_eq] at h_zipped
              exact MirStepStar.trans
                (fun _ h_eq => h_eq ▸ h_zipped)
                (mirStepStar_of_evalPlanToJoin elsePlan h_e h_me)

/--
Coinductive partial-correctness (`DWLP`) `while`-loop invariant rule on `mirTree`
for potentially unbounded loops without a termination rank.
-/
theorem dwlp_mirTree_while_invariant
    {ewp : EffectWP MirEffect} [h_obs : ObsTransparentWP ewp]
    (body : CapturedMir)
    (Inv : MachineState → Prop)
    (condFuel : Nat)
    (bodyPlan exitPlan : TransPlan)
    {post : MirOutcome → Prop}
    (h_step :
      ∀ s : MachineState,
        Inv s →
        ∃ cond bits sThen₀ sElse₀,
          runMirToBinarySwitch condFuel body s =
            some (cond, bits, sThen₀, sElse₀) ∧
          (cond = false → wpTransPlan ewp body exitPlan post sElse₀) ∧
          (cond = true →
            ∃ sNext,
              evalPlanToJoin body bodyPlan sThen₀ = some sNext ∧
              joinPlanMemConsistent body bodyPlan sThen₀ ∧
              Inv sNext))
    {s₀ : MachineState} (h_init : Inv s₀) :
    DWLP ewp (mirTree body s₀) (fun out _ => post out) PUnit.unit := by
  let AtSwitch : MachineState → Prop := fun sSw =>
    ∃ cond bits sThen₀ sElse₀,
      inspectBinarySwitch body sSw = some (cond, bits, sThen₀, sElse₀) ∧
      (cond = false → wpTransPlan ewp body exitPlan post sElse₀) ∧
      (cond = true →
        ∃ sNext,
          evalPlanToJoin body bodyPlan sThen₀ = some sNext ∧
          joinPlanMemConsistent body bodyPlan sThen₀ ∧
          Inv sNext)
  have invToStar : ∀ {s : MachineState}, Inv s → MirStepStar body AtSwitch s := by
    intro s hs
    obtain ⟨cond, bits, sThen₀, sElse₀, h_sw, hf, ht⟩ := h_step s hs
    exact MirStepStar.mono
      (fun _ h_ins => ⟨cond, bits, sThen₀, sElse₀, h_ins, hf, ht⟩)
      (mirStepStar_of_runMirToBinarySwitch condFuel h_sw)
  let CoInv : ITree MirEffect MirOutcome → PUnit → Prop := fun t _ =>
    DWLP ewp t (fun out _ => post out) PUnit.unit ∨
    ∃ s, t = mirTree body s ∧ MirStepStar body AtSwitch s
  refine DWLP.coinduct CoInv ?_ (Or.inr ⟨s₀, rfl, invToStar h_init⟩)
  intro t ⟨⟩ h_cinv
  rcases h_cinv with h_dwlp | ⟨s, rfl, h_star⟩
  · rw [DWLP.unfold_eq] at h_dwlp
    cases h_obs_t : t.observe <;> simp only [h_obs_t] at h_dwlp
    · exact h_dwlp
    · exact Or.inl h_dwlp
    · exact ewp.mono (fun _ _ hd => Or.inl hd) h_dwlp
  · cases h_star with
    | tau h_st h_rest =>
      rename_i s₁
      have h_obs_s : (mirTree body s).observe = .tau (mirTree body s₁) := by
        unfold mirTree; rw [ITree.observe_cofix]; dsimp only [stepMirState]
        rw [h_st]; rfl
      rw [h_obs_s]
      exact Or.inr ⟨s₁, rfl, h_rest⟩
    | emit h_st hk h_rest =>
      rename_i s₁ obs k
      have h_obs_s :
          (mirTree body s).observe =
            .vis (.inr (.inl (.emit obs)))
              (fun o => ITree.cofix (stepMirState body) (k o)) := by
        unfold mirTree; rw [ITree.observe_cofix]; dsimp only [stepMirState]
        rw [h_st]; rfl
      rw [h_obs_s]
      apply h_obs.emit_wp obs
      clear h_st h_obs_s
      change CoInv (ITree.cofix (stepMirState body) (k PUnit.unit)) PUnit.unit
      rw [hk]
      exact Or.inr ⟨s₁, rfl, h_rest⟩
    | done h_at =>
      rcases h_at with ⟨cond, bits, sThen₀, sElse₀, h_ins, hf, ht⟩
      have h_emit := stepMirFn_of_inspectBinarySwitch h_ins
      have h_obs_s :
          (mirTree body s).observe =
            .vis (.inr (.inl (.emit (.event bits))))
              (fun _ => mirTree body (if cond then sThen₀ else sElse₀)) := by
        unfold mirTree; rw [ITree.observe_cofix]; dsimp only [stepMirState]
        rw [h_emit]; rfl
      rw [h_obs_s]
      apply h_obs.emit_wp (.event bits)
      cases cond with
      | false =>
        dsimp only [Bool.false_eq_true, ite_false]
        exact Or.inl (dwlp_of_wpTransPlan (hf rfl))
      | true =>
        dsimp only [ite_true]
        obtain ⟨sNext, h_join, h_mem, h_inv_next⟩ := ht rfl
        exact Or.inr ⟨sThen₀, rfl,
          MirStepStar.trans
            (fun _ h_eq => h_eq ▸ invToStar h_inv_next)
            (mirStepStar_of_evalPlanToJoin bodyPlan h_join h_mem)⟩

/-! ## Pillar 3: Forward/Backward `&mut` Lenses (`MutLens`) & State-Update Specs -/

/--
Forward/backward mutable reference lens (`MutLens Carrier α`), packaging
`readView : Carrier → α` (forward view extraction) and
`writeBack : α → Carrier → Carrier` (backward mutation commit) so `&mut α`
mutations translate cleanly to pure Lean state updates `α → α × β`.
-/
structure MutLens (Carrier α : Type) : Type where
  /-- Extract the logical value `α` currently behind the mutable reference. -/
  readView : Carrier → α
  /-- Commit an updated logical value `α` back into `Carrier`. -/
  writeBack : α → Carrier → Carrier

/-- Pure state-update signature corresponding to `fn(&mut α) -> β`. -/
abbrev MutUpdate (α β : Type) : Type := α → α × β

/-- Identity lens on `α`. -/
def MutLens.id (α : Type) : MutLens α α where
  readView a := a
  writeBack a _ := a

/-- Compose an outer lens `Carrier ⟶ α` with a sub-place lens `α ⟶ γ` (`&mut s.field`). -/
def MutLens.comp {Carrier α γ : Type}
    (outer : MutLens Carrier α) (inner : MutLens α γ) :
    MutLens Carrier γ where
  readView c := inner.readView (outer.readView c)
  writeBack g c := outer.writeBack (inner.writeBack g (outer.readView c)) c

/-- Lift a pure state update `f : α → α × β` across `L : MutLens Carrier α`. -/
def MutLens.applyUpdate {Carrier α β : Type}
    (L : MutLens Carrier α) (f : MutUpdate α β) (c : Carrier) :
    Carrier × β :=
  let (s', ret) := f (L.readView c)
  (L.writeBack s' c, ret)

/-- Sequentially compose two pure `&mut α` state updates. -/
def MutUpdate.seq {α β₁ β₂ : Type}
    (f₁ : MutUpdate α β₁) (f₂ : β₁ → MutUpdate α β₂) :
    MutUpdate α (β₁ × β₂) :=
  fun s₀ =>
    let (s₁, r₁) := f₁ s₀
    let (s₂, r₂) := f₂ r₁ s₁
    (s₂, (r₁, r₂))

/-- Get-Put / Put-Get / Put-Put algebraic lens laws relative to domain `Valid`. -/
structure LawfulMutLens {Carrier α : Type}
    (L : MutLens Carrier α) (Valid : Carrier → Prop) : Prop where
  valid_writeBack : ∀ a c, Valid c → Valid (L.writeBack a c)
  readView_writeBack : ∀ a c, Valid c → L.readView (L.writeBack a c) = a
  writeBack_readView : ∀ c, Valid c → L.writeBack (L.readView c) c = c
  writeBack_writeBack :
    ∀ a₁ a₂ c, Valid c → L.writeBack a₂ (L.writeBack a₁ c) = L.writeBack a₂ c

theorem LawfulMutLens.id (α : Type) :
    LawfulMutLens (MutLens.id α) (fun _ => True) where
  valid_writeBack _ _ _ := trivial
  readView_writeBack _ _ _ := rfl
  writeBack_readView _ _ := rfl
  writeBack_writeBack _ _ _ _ := rfl

theorem LawfulMutLens.comp {Carrier α γ : Type}
    {outer : MutLens Carrier α} {inner : MutLens α γ}
    {ValidC : Carrier → Prop} {ValidA : α → Prop}
    (h_outer : LawfulMutLens outer ValidC)
    (h_inner : LawfulMutLens inner ValidA)
    (h_view : ∀ c, ValidC c → ValidA (outer.readView c)) :
    LawfulMutLens (outer.comp inner) ValidC where
  valid_writeBack _ _ hc := h_outer.valid_writeBack _ _ hc
  readView_writeBack g c hc := by
    dsimp [MutLens.comp]
    rw [h_outer.readView_writeBack _ _ hc,
        h_inner.readView_writeBack g _ (h_view c hc)]
  writeBack_readView c hc := by
    dsimp [MutLens.comp]
    rw [h_inner.writeBack_readView _ (h_view c hc),
        h_outer.writeBack_readView c hc]
  writeBack_writeBack g₁ g₂ c hc := by
    dsimp [MutLens.comp]
    rw [h_outer.readView_writeBack _ _ hc,
        h_inner.writeBack_writeBack g₁ g₂ _ (h_view c hc),
        h_outer.writeBack_writeBack _ _ c hc]

theorem LawfulMutLens.readView_applyUpdate {Carrier α β : Type}
    {L : MutLens Carrier α} {Valid : Carrier → Prop}
    (hL : LawfulMutLens L Valid) (f : MutUpdate α β) {c : Carrier}
    (hc : Valid c) :
    L.readView (L.applyUpdate f c).1 = (f (L.readView c)).1 := by
  unfold MutLens.applyUpdate
  exact hL.readView_writeBack (f (L.readView c)).1 c hc

theorem LawfulMutLens.applyUpdate_seq {Carrier α β₁ β₂ : Type}
    {L : MutLens Carrier α} {Valid : Carrier → Prop}
    (hL : LawfulMutLens L Valid)
    (f₁ : MutUpdate α β₁) (f₂ : β₁ → MutUpdate α β₂)
    {c : Carrier} (hc : Valid c) :
    let (c₁, r₁) := L.applyUpdate f₁ c
    let (c₂, r₂) := L.applyUpdate (f₂ r₁) c₁
    (c₂, (r₁, r₂)) = L.applyUpdate (MutUpdate.seq f₁ f₂) c := by
  dsimp only [MutLens.applyUpdate, MutUpdate.seq]
  rw [hL.readView_writeBack _ c hc, hL.writeBack_writeBack _ _ c hc]

/-! ### Value Codecs & Concrete `Memory` / `PartialHeap` Active-Borrow Lens -/

/-- Retraction pair encoding a Lean domain `α` into `V2026_06_01` `Value`. -/
structure ValueCodec (α : Type) : Type where
  encode : α → Value
  decode : Value → Option α
  default : α
  decode_encode : ∀ a : α, decode (encode a) = some a

attribute [simp] ValueCodec.decode_encode

/-- Identity codec on raw `Value`. -/
def ValueCodec.rawValue : ValueCodec Value where
  encode v := v
  decode v := some v
  default := .unit
  decode_encode _ := rfl

/-- Codec for fixed-width unsigned scalar `Nat` values at byte width `sizeBytes`. -/
def ValueCodec.scalarNat (sizeBytes : Nat) : ValueCodec Nat where
  encode n := .scalar { bits := n, sizeBytes := sizeBytes }
  decode
    | .scalar sc => if sc.sizeBytes == sizeBytes then some sc.bits else none
    | _ => none
  default := 0
  decode_encode n := by simp

/-- Codec for 1-byte Rust booleans (`Bool`). -/
def ValueCodec.rustBool : ValueCodec Bool where
  encode b := .scalar (boolToScalar b)
  decode
    | .scalar ⟨0, 1⟩ => some false
    | .scalar ⟨1, 1⟩ => some true
    | _ => none
  default := false
  decode_encode b := by cases b <;> rfl

/-- Codec for 2-field Rust structs / tuples (`Value.aggregate 0 [f₀, f₁]`). -/
def ValueCodec.pair {α β : Type}
    (c₁ : ValueCodec α) (c₂ : ValueCodec β) : ValueCodec (α × β) where
  encode p := .aggregate 0 [c₁.encode p.1, c₂.encode p.2]
  decode
    | .aggregate 0 [v₁, v₂] =>
      match c₁.decode v₁, c₂.decode v₂ with
      | some a, some b => some (a, b)
      | _, _ => none
    | _ => none
  default := (c₁.default, c₂.default)
  decode_encode p := by rcases p with ⟨a, b⟩; simp

/-- Update the local-slot list of `m.callStack`'s head caller activation record (or `m.callerLocals` at the root call). -/
def updateMemoryLocals (m : Memory) (locals' : List LocalValue) : Memory :=
  match m.callStack with
  | head :: tail =>
    { m with
      callStack :=
        { head with frame := { head.frame with locals := locals' } } :: tail }
  | [] => { m with callerLocals := locals' }

/--
Concrete `MutLens Memory α` backed by an active Tree Borrows pointer `rp : RawPtrVal`
into `memoryLocals m`, updating both the pointee cell via `writeAllocAt?` and
Tree Borrows permissions via `stepTreeBorrowAccess? m rp true`.
-/
def memoryPtrMutLens (rp : RawPtrVal) (codec : ValueCodec α) : MutLens Memory α where
  readView m :=
    match readAllocAt? (memoryLocals m) rp with
    | some v => (codec.decode v).getD codec.default
    | none => codec.default
  writeBack a m :=
    let m₁ := (stepTreeBorrowAccess? m rp true).getD m
    match writeAllocAt? (memoryLocals m₁) rp (codec.encode a) with
    | some locals' => updateMemoryLocals m₁ locals'
    | none => m₁

theorem readAllocAt_writeAllocAt_self
    {locals : List LocalValue} {rp : RawPtrVal} {oldVal newVal : Value}
    (h_read : readAllocAt? locals rp = some oldVal) :
    ∃ locals',
      writeAllocAt? locals rp newVal = some locals' ∧
      readAllocAt? locals' rp = some newVal := by
  unfold readAllocAt? at h_read
  unfold writeAllocAt? readAllocAt?
  cases h_get : get? locals rp.allocId with
  | none => rw [h_get] at h_read; nomatch h_read
  | some slot =>
    rw [h_get] at h_read
    cases slot with
    | dead => nomatch h_read
    | uninit => nomatch h_read
    | init rootVal =>
      have h_lt : rp.allocId < locals.length :=
        (List.getElem?_eq_some_iff.mp h_get).1
      cases h_off : rp.offset with
      | zero =>
        dsimp only
        unfold set? get?
        simp only [h_lt, ite_true]
        refine ⟨locals.set rp.allocId (.init newVal), rfl, ?_⟩
        rw [List.getElem?_set_self h_lt]
      | succ k =>
        rw [h_off] at h_read
        dsimp only at h_read
        cases rootVal with
        | unit => nomatch h_read
        | scalar _ => nomatch h_read
        | ptr _ _ => nomatch h_read
        | aggregate variant elems =>
          cases variant with
          | succ _ => nomatch h_read
          | zero =>
            have h_k_lt : k + 1 < elems.length :=
              (List.getElem?_eq_some_iff.mp h_read).1
            dsimp only
            unfold set? get?
            simp only [h_k_lt, h_lt, ite_true]
            refine ⟨locals.set rp.allocId
              (.init (.aggregate 0 (elems.set (k + 1) newVal))), rfl, ?_⟩
            rw [List.getElem?_set_self h_lt]
            dsimp only
            exact List.getElem?_set_self h_k_lt

private theorem lookupBorrow_tag_eq
    {borrows : List BorrowEntry} {tag : Nat} {entry : BorrowEntry}
    (h : lookupBorrow borrows tag = some entry) :
    entry.tag = tag := by
  induction borrows with
  | nil => nomatch h
  | cons hd tl ih =>
    unfold lookupBorrow at h
    cases h_eq : Nat.beq hd.tag tag with
    | false =>
      rw [h_eq] at h
      exact ih h
    | true =>
      rw [h_eq] at h
      injection h with h_hd
      subst h_hd
      exact Nat.eq_of_beq_eq_true h_eq

private theorem lookupBorrow_invalidate_self_active
    (borrows : List BorrowEntry) (tag : Nat)
    {entry : BorrowEntry}
    (h_look : lookupBorrow borrows tag = some entry)
    (h_perm : entry.perm = .active ∨ entry.perm = .reserved) :
    ∃ entry',
      lookupBorrow
        (invalidateConflictingBorrows borrows entry.targetLocal (some tag))
        tag = some entry' ∧
      entry'.targetLocal = entry.targetLocal ∧
      entry'.perm = .active := by
  have h_etag : entry.tag = tag := lookupBorrow_tag_eq h_look
  rw [lookupBorrow_invalidateConflictingBorrows, h_look]
  dsimp only [Option.map]
  refine ⟨updateBorrowPerm entry entry.targetLocal (some tag), rfl, ?_, ?_⟩
  · unfold updateBorrowPerm
    simp only [Nat.beq_refl, h_etag]
    cases entry.perm <;> rfl
  · unfold updateBorrowPerm
    simp only [Nat.beq_refl, h_etag]
    rcases h_perm with hp | hp <;> simp [hp]

@[simp]
theorem memoryLocals_updateMemoryLocals
    (m : Memory) (locals' : List LocalValue) :
    memoryLocals (updateMemoryLocals m locals') = locals' := by
  unfold updateMemoryLocals memoryLocals
  cases m.callStack <;> rfl

private theorem memoryLocals_updateMemoryLocals_of_readAllocAt
    {m : Memory} {rp : RawPtrVal} {v : Value}
    (_h_read : readAllocAt? (memoryLocals m) rp = some v)
    (locals' : List LocalValue) :
    memoryLocals (updateMemoryLocals m locals') = locals' :=
  memoryLocals_updateMemoryLocals m locals'

@[simp]
private theorem borrows_updateMemoryLocals
    (m : Memory) (locals' : List LocalValue) :
    (updateMemoryLocals m locals').borrows = m.borrows := by
  unfold updateMemoryLocals
  cases m.callStack <;> rfl

private theorem get?_set?_ne
    {α : Type} {xs xs' : List α} {idx otherIdx : Nat} {val : α}
    (h_set : set? xs idx val = some xs')
    (h_ne : otherIdx ≠ idx) :
    get? xs' otherIdx = get? xs otherIdx := by
  unfold set? at h_set
  split at h_set
  · injection h_set with h_eq
    subst h_eq
    unfold get?
    exact List.getElem?_set_ne h_ne.symm
  · nomatch h_set

theorem readAllocAt_writeAllocAt_ne_alloc
    {locals locals' : List LocalValue} {rp other : RawPtrVal} {newVal : Value}
    (h_write : writeAllocAt? locals rp newVal = some locals')
    (h_ne : other.allocId ≠ rp.allocId) :
    readAllocAt? locals' other = readAllocAt? locals other := by
  have h_slot : ∃ slot', set? locals rp.allocId slot' = some locals' := by
    unfold writeAllocAt? at h_write
    cases h_off : rp.offset with
    | zero =>
      rw [h_off] at h_write
      cases h_get : get? locals rp.allocId with
      | none => rw [h_get] at h_write; nomatch h_write
      | some s =>
        rw [h_get] at h_write
        cases s with
        | dead => nomatch h_write
        | uninit => exact ⟨.init newVal, h_write⟩
        | init _ => exact ⟨.init newVal, h_write⟩
    | succ k =>
      rw [h_off] at h_write
      cases h_get : get? locals rp.allocId with
      | none => rw [h_get] at h_write; nomatch h_write
      | some s =>
        rw [h_get] at h_write
        cases s with
        | dead => nomatch h_write
        | uninit => nomatch h_write
        | init v =>
          cases v with
          | unit => nomatch h_write
          | scalar _ => nomatch h_write
          | ptr _ _ => nomatch h_write
          | aggregate variant elems =>
            cases variant with
            | succ _ => nomatch h_write
            | zero =>
              simp only [Nat.zero_eq] at h_write
              cases h_se : set? elems (k + 1) newVal with
              | none => rw [h_se] at h_write; nomatch h_write
              | some elems' =>
                rw [h_se] at h_write
                exact ⟨.init (.aggregate 0 elems'), h_write⟩
  rcases h_slot with ⟨slot', h_set⟩
  unfold readAllocAt?
  rw [get?_set?_ne h_set h_ne]

/--
Combined `SepProp` ownership assertion (`rp ↦ encode a ∗ BorrowToken rp .active`)
representing an exclusive typed Rust mutable borrow `&mut α` at `rp`.
-/
def ActiveTypedMutBorrow
    (rp : RawPtrVal) (codec : ValueCodec α) (a : α) : SepProp :=
  sepConj (PointsTo rp (codec.encode a)) (BorrowToken rp .active)

theorem localSepProp_activeTypedMutBorrow
    (rp : RawPtrVal) (codec : ValueCodec α) (a : α) :
    LocalSepProp (ActiveTypedMutBorrow rp codec a) :=
  localSepProp_sepConj
    (localSepProp_pointsTo rp (codec.encode a))
    (localSepProp_borrowToken rp .active)

/-- Canonical spatial footprint of `ActiveTypedMutBorrow rp codec a`. -/
def mutBorrowFootprint (rp : RawPtrVal) : Footprint :=
  { addrs := [(rp.allocId, rp.offset)], tags := [rp.tag] }

/-- Construct `ActiveTypedMutBorrow rp codec a` at `mutBorrowFootprint rp`. -/
theorem activeTypedMutBorrow_intro
    {rp : RawPtrVal} {codec : ValueCodec α} {a : α} {m : Memory}
    (h_read : readAllocAt? (memoryLocals m) rp = some (codec.encode a))
    (h_tok :
      ∃ entry,
        lookupBorrow m.borrows rp.tag = some entry ∧
        entry.targetLocal = rp.allocId ∧
        entry.perm = .active) :
    ActiveTypedMutBorrow rp codec a ⟨m, mutBorrowFootprint rp⟩ := by
  refine
    ⟨⟨m, { addrs := [(rp.allocId, rp.offset)], tags := [] }⟩,
     ⟨m, { addrs := [], tags := [rp.tag] }⟩,
     ⟨rfl, rfl, ⟨fun _ _ h => (by cases h), fun _ h => (by cases h)⟩,
      fun addr => by simp [mutBorrowFootprint],
      fun tag => by simp [mutBorrowFootprint]⟩,
     ⟨h_read, rfl⟩,
     ⟨h_tok, rfl⟩⟩

/-- Forward view extraction: `PointsTo rp (codec.encode a)` reads back `a`. -/
theorem memoryPtrMutLens_readView_of_pointsTo
    {rp : RawPtrVal} {codec : ValueCodec α} {a : α} {h : PartialHeap}
    (h_pts : PointsTo rp (codec.encode a) h) :
    (memoryPtrMutLens rp codec).readView h.state = a := by
  unfold memoryPtrMutLens
  dsimp only
  rw [h_pts.1]
  dsimp only
  rw [codec.decode_encode]
  rfl

/-- Forward view extraction from `ActiveTypedMutBorrow rp codec a`. -/
theorem memoryPtrMutLens_readView_of_sep
    {rp : RawPtrVal} {codec : ValueCodec α} {a : α} {h : PartialHeap}
    (h_sep : ActiveTypedMutBorrow rp codec a h) :
    (memoryPtrMutLens rp codec).readView h.state = a := by
  rcases h_sep with ⟨h₁, _, ⟨hs₁, _, _, _, _⟩, h_pts, _⟩
  rw [← hs₁]
  exact memoryPtrMutLens_readView_of_pointsTo h_pts

/--
Backward mutation commit: `writeBack a' m` updates the pointee cell to
`codec.encode a'` while preserving active Tree Borrows permission and footprint
splitting in `ActiveTypedMutBorrow`.
-/
theorem memoryPtrMutLens_writeBack_sep
    {rp : RawPtrVal} {codec : ValueCodec α} {a : α} (a' : α)
    {m : Memory} {fp : Footprint}
    (h_sep : ActiveTypedMutBorrow rp codec a ⟨m, fp⟩) :
    ActiveTypedMutBorrow rp codec a'
      ⟨(memoryPtrMutLens rp codec).writeBack a' m, fp⟩ := by
  rcases h_sep with
    ⟨h₁, h₂, ⟨hs₁, hs₂, h_disj, h_addrs, h_tags⟩,
     ⟨h_read₁, hfp₁⟩, ⟨⟨entry, h_look₂, h_tloc, h_perm⟩, hfp₂⟩⟩
  dsimp only at hs₁ hs₂
  rw [hs₁] at h_read₁
  rw [hs₂] at h_look₂
  let m₁ : Memory :=
    { m with
      borrows :=
        invalidateConflictingBorrows m.borrows entry.targetLocal (some rp.tag) }
  have h_tb : stepTreeBorrowAccess? m rp true = some m₁ := by
    simp [stepTreeBorrowAccess?, h_look₂, h_perm, m₁]
  have h_ml₁ : memoryLocals m₁ = memoryLocals m := rfl
  obtain ⟨locals', h_write, h_read_new⟩ :=
    readAllocAt_writeAllocAt_self (newVal := codec.encode a')
      (h_ml₁.symm ▸ h_read₁)
  have h_wb_eq :
      (memoryPtrMutLens rp codec).writeBack a' m =
        updateMemoryLocals m₁ locals' := by
    unfold memoryPtrMutLens
    dsimp only
    rw [h_tb]
    dsimp only [Option.getD]
    rw [h_write]
  rw [h_wb_eq]
  have h_ml_upd :
      memoryLocals (updateMemoryLocals m₁ locals') = locals' :=
    memoryLocals_updateMemoryLocals_of_readAllocAt (h_ml₁.symm ▸ h_read₁) locals'
  obtain ⟨entry', h_look_new, h_tloc_new, h_perm_new⟩ :=
    lookupBorrow_invalidate_self_active m.borrows rp.tag h_look₂ (.inl h_perm)
  refine
    ⟨⟨updateMemoryLocals m₁ locals', h₁.footprint⟩,
     ⟨updateMemoryLocals m₁ locals', h₂.footprint⟩,
     ⟨rfl, rfl, h_disj, h_addrs, h_tags⟩,
     ⟨by dsimp only; rw [h_ml_upd]; exact h_read_new, hfp₁⟩,
     ⟨⟨entry', by dsimp only; rw [borrows_updateMemoryLocals]; exact h_look_new,
       h_tloc_new.trans h_tloc, h_perm_new⟩, hfp₂⟩⟩

/--
Lifting a pure state update `f : MutUpdate α β` (`α → α × β`) across
`memoryPtrMutLens rp codec` produces `(f a).2` and transitions
`ActiveTypedMutBorrow rp codec a` to `ActiveTypedMutBorrow rp codec (f a).1`.
-/
theorem memoryPtrMutLens_applyUpdate_sep
    {rp : RawPtrVal} {codec : ValueCodec α} {a : α}
    (f : MutUpdate α β) {m : Memory} {fp : Footprint}
    (h_sep : ActiveTypedMutBorrow rp codec a ⟨m, fp⟩) :
    let res := (memoryPtrMutLens rp codec).applyUpdate f m
    res.2 = (f a).2 ∧
    ActiveTypedMutBorrow rp codec (f a).1 ⟨res.1, fp⟩ := by
  dsimp only [MutLens.applyUpdate]
  rw [memoryPtrMutLens_readView_of_sep h_sep]
  exact ⟨rfl, memoryPtrMutLens_writeBack_sep (f a).1 h_sep⟩

/--
`LawfulMutLens` Get-Put law for `memoryPtrMutLens rp codec` on every heap
satisfying `ActiveTypedMutBorrow`.
-/
theorem memoryPtrMutLens_readView_writeBack
    {rp : RawPtrVal} {codec : ValueCodec α} {a : α} (a' : α)
    {m : Memory} {fp : Footprint}
    (h_sep : ActiveTypedMutBorrow rp codec a ⟨m, fp⟩) :
    (memoryPtrMutLens rp codec).readView
      ((memoryPtrMutLens rp codec).writeBack a' m) = a' :=
  memoryPtrMutLens_readView_of_sep (memoryPtrMutLens_writeBack_sep a' h_sep)

/--
Disjoint-allocation frame preservation for `memoryPtrMutLens`: writing `a'`
through `rp` preserves `AgreeOnFootprint frameFp` for every frame footprint
whose addresses and borrow tags target allocations distinct from `rp.allocId`.
-/
theorem memoryPtrMutLens_writeBack_agreeOnDisjointAllocs
    {rp : RawPtrVal} {codec : ValueCodec α} {a : α} (a' : α)
    {m : Memory} {fp : Footprint} (frameFp : Footprint)
    (h_sep : ActiveTypedMutBorrow rp codec a ⟨m, fp⟩)
    (h_disj_addrs : ∀ allocId offset,
      (allocId, offset) ∈ frameFp.addrs → allocId ≠ rp.allocId)
    (h_disj_tags : ∀ tag ∈ frameFp.tags,
      ∃ entry,
        lookupBorrow m.borrows tag = some entry ∧
        entry.targetLocal ≠ rp.allocId) :
    AgreeOnFootprint frameFp m
      ((memoryPtrMutLens rp codec).writeBack a' m) := by
  rcases h_sep with
    ⟨_, _, ⟨hs₁, hs₂, _, _, _⟩,
     ⟨h_read₁, _⟩, ⟨⟨entry, h_look₂, h_tloc, h_perm⟩, _⟩⟩
  dsimp only at hs₁ hs₂
  rw [hs₁] at h_read₁
  rw [hs₂] at h_look₂
  let m₁ : Memory :=
    { m with
      borrows :=
        invalidateConflictingBorrows m.borrows entry.targetLocal (some rp.tag) }
  have h_tb : stepTreeBorrowAccess? m rp true = some m₁ := by
    simp [stepTreeBorrowAccess?, h_look₂, h_perm, m₁]
  have h_ml₁ : memoryLocals m₁ = memoryLocals m := rfl
  obtain ⟨locals', h_write, _⟩ :=
    readAllocAt_writeAllocAt_self (newVal := codec.encode a')
      (h_ml₁.symm ▸ h_read₁)
  have h_wb_eq :
      (memoryPtrMutLens rp codec).writeBack a' m =
        updateMemoryLocals m₁ locals' := by
    unfold memoryPtrMutLens
    dsimp only
    rw [h_tb]
    dsimp only [Option.getD]
    rw [h_write]
  rw [h_wb_eq]
  have h_ml_upd :
      memoryLocals (updateMemoryLocals m₁ locals') = locals' :=
    memoryLocals_updateMemoryLocals_of_readAllocAt (h_ml₁.symm ▸ h_read₁) locals'
  refine ⟨fun allocId offset h_in => ?_, fun tag h_in => ?_⟩
  · rw [h_ml_upd]
    exact (readAllocAt_writeAllocAt_ne_alloc h_write
      (h_disj_addrs allocId offset h_in)).symm
  · rw [borrows_updateMemoryLocals]
    have h_disj' :
        ∀ t ∈ frameFp.tags,
          ∃ e, lookupBorrow m.borrows t = some e ∧ e.targetLocal ≠ entry.targetLocal := by
      intro t ht
      rcases h_disj_tags t ht with ⟨e, hl, hne⟩
      exact ⟨e, hl, h_tloc.symm ▸ hne⟩
    exact (agreeOnFootprint_of_disjoint_borrow_update
      frameFp m entry.targetLocal (some rp.tag) h_disj').2 tag h_in

/--
Specification bundle translating a `V2026_06_01` `CapturedMir` body performing
`&mut α` state updates into a pure Lean state-update function
`update : List Value → MutUpdate α β` (`α → α × β`), returning the updated
carrier and return value encoded via `ValueCodec.pair stateCodec retCodec`.
-/
structure MutRefLocalSpec (α β : Type) : Type where
  body : CapturedMir
  stateCodec : ValueCodec α
  retCodec : ValueCodec β
  pre : α → List Value → Memory → Prop
  update : List Value → MutUpdate α β
  postMem : α → List Value → Memory → Memory → Prop := fun _ _ _ _ => True

/-- Project `spec : MutRefLocalSpec α β` to an audited `StatefulClaim`. -/
def MutRefLocalSpec.toStatefulClaim (spec : MutRefLocalSpec α β) : StatefulClaim where
  body := spec.body
  pre args mem :=
    ∃ s₀ extraArgs,
      args = spec.stateCodec.encode s₀ :: extraArgs ∧
      spec.pre s₀ extraArgs mem
  post args mem retVal mem' :=
    ∀ s₀ extraArgs,
      args = spec.stateCodec.encode s₀ :: extraArgs →
      retVal = (ValueCodec.pair spec.stateCodec spec.retCodec).encode
        (spec.update extraArgs s₀) ∧
      spec.postMem s₀ extraArgs mem mem'

/-- Project `spec : MutRefLocalSpec α β` to an audited `TotalClaim`. -/
def MutRefLocalSpec.toTotalClaim (spec : MutRefLocalSpec α β) : TotalClaim where
  body := spec.body
  pre args mem :=
    ∃ s₀ extraArgs,
      args = spec.stateCodec.encode s₀ :: extraArgs ∧
      spec.pre s₀ extraArgs mem
  post args mem retVal mem' :=
    ∀ s₀ extraArgs,
      args = spec.stateCodec.encode s₀ :: extraArgs →
      retVal = (ValueCodec.pair spec.stateCodec spec.retCodec).encode
        (spec.update extraArgs s₀) ∧
      spec.postMem s₀ extraArgs mem mem'

/-- Verify `spec.toTotalClaim` via an input-indexed `TransPlan`. -/
theorem verifyMutRefLocalTotalByTransPlan
    {ewp : EffectWP MirEffect} [ObsTransparentWP ewp] [PureSoundWP ewp]
    {α β : Type}
    (spec : MutRefLocalSpec α β)
    (plan : α → List Value → Memory → TransPlan)
    (h_plan :
      ∀ (s₀ : α) (extraArgs : List Value) (mem : Memory),
        spec.pre s₀ extraArgs mem →
        wpTransPlan ewp spec.body (plan s₀ extraArgs mem)
          (fun out =>
            ∃ mem',
              out = .normal
                ((ValueCodec.pair spec.stateCodec spec.retCodec).encode
                  (spec.update extraArgs s₀), mem') ∧
              spec.postMem s₀ extraArgs mem mem')
          (initMachineStateWithMemory spec.body
            (spec.stateCodec.encode s₀ :: extraArgs) mem)) :
    TotalVerificationResult spec.toTotalClaim := by
  refine ⟨fun args mem h_pre_all => ?_⟩
  rcases h_pre_all with ⟨s₀, extraArgs, rfl, h_pre⟩
  refine dwp_pure_adequacy
    (DWP.mono ?_ (dwp_mirStatefulTree_of_transPlan (h_plan s₀ extraArgs mem h_pre)))
  rintro out _ ⟨mem', rfl, h_pmem⟩
  refine ⟨_, mem', rfl, ?_⟩
  intro s₁ extra₁ h_eq
  injection h_eq with h_s h_extra
  have h_dec :
      spec.stateCodec.decode (spec.stateCodec.encode s₀) =
        spec.stateCodec.decode (spec.stateCodec.encode s₁) :=
    congrArg spec.stateCodec.decode h_s
  rw [spec.stateCodec.decode_encode, spec.stateCodec.decode_encode] at h_dec
  injection h_dec with h_s_eq
  subst h_s_eq h_extra
  exact ⟨rfl, h_pmem⟩

/-- Derive `StatefulVerificationResult spec.toStatefulClaim` from `TotalVerificationResult`. -/
theorem statefulOfTotalMutRefLocal
    {α β : Type} {spec : MutRefLocalSpec α β}
    (h_tot : TotalVerificationResult spec.toTotalClaim) :
    StatefulVerificationResult spec.toStatefulClaim := by
  refine ⟨fun args mem h_pre => ?_⟩
  obtain ⟨h_safe, _, _, h_ret⟩ := h_tot.proof args mem h_pre
  refine ⟨h_safe, fun outPair h_reaches _ retVal mem' h_out => ?_⟩
  obtain ⟨ret₀, mem₀, h_eq, h_post⟩ := h_ret outPair.1 outPair.2 h_reaches
  rw [h_out] at h_eq
  injection h_eq with h_pair
  injection h_pair with h_r h_m
  subst h_r h_m
  exact h_post

/-! ## Pillar 4: Program-to-Program Behavioral Equivalence & Layer 1A Refinement -/

section Pillar4

universe u

/--
Strengthening of `PureSoundWP ewp` requiring every request `i : E.I` admitted by
`ewp.wp i Q ()` to have an inhabited response type `Nonempty (E.O i)`.

Ruling out uninhabited demonic requests (`ITree.stuck` / `PickE PEmpty`) makes
`DWP` constructively adequate: every `DWP` proof witnesses a concrete completed
execution `ReachesRet t tr r`.
-/
class ConstructivePureWP
    {E : Effect.{u}} [FaultEffect E] (ewp : EffectWP E) : Prop
    extends PureSoundWP ewp where
  has_answer :
    ∀ {i : E.I} {Q : E.O i → PUnit.{u + 1} → Prop},
      ewp.wp i Q PUnit.unit → Nonempty (E.O i)

instance : ConstructivePureWP mirClosedWP where
  has_answer {i} _ h :=
    match i with
    | .inl (.fail _) => False.elim h
    | .inr (.emit _) => ⟨PUnit.unit⟩

instance : ConstructivePureWP mirNoCallWP where
  has_answer {i} _ h :=
    match i with
    | .inl (.fail _) => False.elim h
    | .inr (.inl (.emit _)) => ⟨PUnit.unit⟩
    | .inr (.inr (.call _)) => False.elim h

instance : ConstructivePureWP mirDefaultWP where
  has_answer {i} _ h :=
    match i with
    | .inl (.fail _) => False.elim h
    | .inr (.inl (.emit _)) => ⟨PUnit.unit⟩
    | .inr (.inr (.call _)) => ⟨.aborted⟩

/--
Constructive existence of a completed `ReachesRet` execution from `DWP` under
`[ConstructivePureWP ewp]`.
-/
theorem dwp_constructive_pure_reachesRet
    {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {ewp : EffectWP E} [h_c : ConstructivePureWP ewp]
    {t : ITree E R} {post : R → Prop}
    (h_dwp : DWP ewp t (fun r _ => post r) PUnit.unit) :
    ∃ tr r, ReachesRet t tr r ∧ post r := by
  refine DWP.induct
    (fun x _ => ∃ tr r, ReachesRet x tr r ∧ post r) ?_ h_dwp
  intro x _ hx
  cases h_obs : x.observe with
  | ret r =>
    simp only [h_obs] at hx
    exact ⟨[], r, ⟨x, .refl x, h_obs⟩, hx⟩
  | tau x' =>
    simp only [h_obs] at hx
    rcases hx with ⟨tr, r, ⟨u, h_reach, h_ret⟩, hp⟩
    exact ⟨tr, r, ⟨u, .tau h_obs h_reach, h_ret⟩, hp⟩
  | vis i k =>
    simp only [h_obs] at hx
    obtain ⟨h_nf, h_all⟩ := h_c.sound hx
    rcases h_c.has_answer hx with ⟨o⟩
    rcases h_all o with ⟨tr, r, ⟨u, h_reach, h_ret⟩, hp⟩
    exact ⟨⟨i, o⟩ :: tr, r, ⟨u, .vis h_obs h_nf o h_reach, h_ret⟩, hp⟩

/--
Full constructive total-correctness adequacy for stateless `DWP`: guarantees
`TreeSafe`, `Productive`, `¬ MayDiverge`, existence of a `ReachesRet` return,
and `post` on all `ReachesRet` returns.
-/
theorem dwp_constructive_pure_adequacy
    {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {ewp : EffectWP E} [ConstructivePureWP ewp]
    {t : ITree E R} {post : R → Prop}
    (h_dwp : DWP ewp t (fun r _ => post r) PUnit.unit) :
    TreeSafe t ∧ Productive t ∧ ¬ MayDiverge t ∧
      (∃ tr r, ReachesRet t tr r ∧ post r) ∧
      (∀ tr r, ReachesRet t tr r → post r) := by
  obtain ⟨h_safe, h_prod, h_ndiv, h_all⟩ := dwp_pure_adequacy h_dwp
  exact ⟨h_safe, h_prod, h_ndiv, dwp_constructive_pure_reachesRet h_dwp, h_all⟩

/--
Strengthening of `TraceSoundWP ewp` requiring every request `i : E.I` admitted
by `ewp.wp i Q tr` to have an inhabited response type `Nonempty (E.O i)`.
-/
class ConstructiveTraceWP
    {E : Effect.{u}} [FaultEffect E]
    (ewp : StateEffectWP (List (Event E)) E) : Prop
    extends TraceSoundWP ewp where
  has_answer :
    ∀ {i : E.I} {Q : E.O i → List (Event E) → Prop} {tr : List (Event E)},
      ewp.wp i Q tr → Nonempty (E.O i)

private theorem dwp_stabilizes_any
    {S : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} {t : ITree E R} {Q : R → S → Prop} {s : S}
    (h_dwp : DWP ewp t Q s) :
    ∃ u' : ITree E R, TauStar t u' ∧ ∀ w, u'.observe ≠ .tau w := by
  refine DWP.induct
    (fun x _ => ∃ u', TauStar x u' ∧ ∀ w, u'.observe ≠ .tau w) ?_ h_dwp
  intro x _ hx
  cases h_obs : x.observe with
  | ret _ =>
    exact ⟨x, .refl x, fun _ hw => by rw [h_obs] at hw; nomatch hw⟩
  | tau x' =>
    simp only [h_obs] at hx
    rcases hx with ⟨u', hs, hnt⟩
    exact ⟨u', .step h_obs hs, hnt⟩
  | vis _ _ =>
    exact ⟨x, .refl x, fun _ hw => by rw [h_obs] at hw; nomatch hw⟩

private theorem dwp_trace_reaches
    {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {ewp : StateEffectWP (List (Event E)) E} [h_sound : TraceSoundWP ewp]
    {t u : ITree E R} {tr : List (Event E)} {Q : R → List (Event E) → Prop}
    (h_reach : Reaches t tr u) :
    ∀ {tr₀ : List (Event E)},
      DWP ewp t Q tr₀ → DWP ewp u Q (tr₀ ++ tr) := by
  induction h_reach with
  | refl =>
    intro tr₀ h
    simpa using h
  | tau ht _ ih =>
    intro tr₀ h
    rw [DWP.unfold_eq, ht] at h
    exact ih h
  | vis hv _ o _ ih =>
    intro tr₀ h
    rw [DWP.unfold_eq, hv] at h
    have h_next := ih ((h_sound.sound h).2 o)
    simpa [List.append_assoc] using h_next

/-- Event-trace total-correctness (`DWP`) adequacy starting from `[]`. -/
theorem dwp_trace_adequacy
    {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {ewp : StateEffectWP (List (Event E)) E} [TraceSoundWP ewp]
    {t : ITree E R} {post : R → List (Event E) → Prop}
    (h_dwp : DWP ewp t post []) :
    TreeSafe t ∧ Productive t ∧ ¬ MayDiverge t ∧
      ∀ tr r, ReachesRet t tr r → post r tr := by
  have h_part := dwlp_trace_adequacy h_dwp.toDWLP
  have h_prod : Productive t :=
    fun _ _ h_reach => dwp_stabilizes_any (dwp_trace_reaches h_reach h_dwp)
  exact ⟨h_part.1, h_prod, productive_not_mayDiverge h_prod, h_part.2⟩

/--
Constructive existence of a completed `(trace, returnValue)` execution from
trace-recording `DWP` under `[ConstructiveTraceWP ewp]`.
-/
theorem dwp_constructive_trace_reachesRet
    {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {ewp : StateEffectWP (List (Event E)) E} [h_c : ConstructiveTraceWP ewp]
    {t : ITree E R} {post : R → List (Event E) → Prop}
    (h_dwp : DWP ewp t post []) :
    ∃ tr r, ReachesRet t tr r ∧ post r tr := by
  have h_gen :
      ∀ (x : ITree E R) (tr₀ : List (Event E)),
        DWP ewp x post tr₀ →
        ∃ trSuff r, ReachesRet x trSuff r ∧ post r (tr₀ ++ trSuff) := by
    intro x tr₀ hx₀
    refine DWP.induct
      (fun y trBase =>
        ∃ trSuff r, ReachesRet y trSuff r ∧ post r (trBase ++ trSuff))
      ?_ hx₀
    intro y trBase hy
    cases h_obs : y.observe with
    | ret r =>
      simp only [h_obs] at hy
      exact ⟨[], r, ⟨y, .refl y, h_obs⟩, by simpa using hy⟩
    | tau y' =>
      simp only [h_obs] at hy
      rcases hy with ⟨trSuff, r, ⟨u, h_reach, h_ret⟩, hp⟩
      exact ⟨trSuff, r, ⟨u, .tau h_obs h_reach, h_ret⟩, hp⟩
    | vis i k =>
      simp only [h_obs] at hy
      obtain ⟨h_nf, h_all⟩ := h_c.sound hy
      rcases h_c.has_answer hy with ⟨o⟩
      rcases h_all o with ⟨trSuff, r, ⟨u, h_reach, h_ret⟩, hp⟩
      refine ⟨⟨i, o⟩ :: trSuff, r, ⟨u, .vis h_obs h_nf o h_reach, h_ret⟩, ?_⟩
      simpa [List.append_assoc] using hp
  rcases h_gen t [] h_dwp with ⟨tr, r, h_ret, hp⟩
  exact ⟨tr, r, h_ret, by simpa using hp⟩

/-- Full constructive trace-aware total-correctness adequacy for `DWP`. -/
theorem dwp_constructive_trace_adequacy
    {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {ewp : StateEffectWP (List (Event E)) E} [ConstructiveTraceWP ewp]
    {t : ITree E R} {post : R → List (Event E) → Prop}
    (h_dwp : DWP ewp t post []) :
    TreeSafe t ∧ Productive t ∧ ¬ MayDiverge t ∧
      (∃ tr r, ReachesRet t tr r ∧ post r tr) ∧
      (∀ tr r, ReachesRet t tr r → post r tr) := by
  obtain ⟨h_safe, h_prod, h_ndiv, h_all⟩ := dwp_trace_adequacy h_dwp
  exact ⟨h_safe, h_prod, h_ndiv, dwp_constructive_trace_reachesRet h_dwp, h_all⟩

/-! ### Direct `DWLP` / `DWP` → Layer 1A `ITree.toPartial` Refinement & Equality -/

/--
Fundamental program-to-program Layer 1A refinement bridge (`implTree ≤ specTree`):
if `implTree` satisfies partial-correctness `DWLP` with postcondition `P`, and
`specTree` satisfies constructive total-correctness `DWP` witnessing an outcome
`(tr_s, r_s)` matching every `(tr_i, r_i)` permitted by `P`, then
`implTree.toPartial ≤ specTree.toPartial`.
-/
theorem dwlp_toPartial_refines_dwp
    {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {ewp₁ ewp₂ : StateEffectWP (List (Event E)) E}
    [TraceSoundWP ewp₁] [ConstructiveTraceWP ewp₂]
    {implTree specTree : ITree E R}
    {P : R → List (Event E) → Prop}
    (h_impl : DWLP ewp₁ implTree P [])
    (h_spec :
      DWP ewp₂ specTree
        (fun r_s tr_s => ∀ r_i tr_i, P r_i tr_i → tr_s = tr_i ∧ r_s = r_i) []) :
    implTree.toPartial ≤ specTree.toPartial := by
  obtain ⟨h_safe_impl, h_post_impl⟩ := dwlp_trace_adequacy h_impl
  obtain ⟨tr_s, r_s, h_ret_spec, h_match⟩ :=
    dwp_constructive_trace_reachesRet h_spec
  intro _
  refine ⟨h_safe_impl, fun ⟨tr_i, r_i⟩ h_ret_impl => ?_⟩
  rcases h_match r_i tr_i (h_post_impl tr_i r_i h_ret_impl) with ⟨rfl, rfl⟩
  exact h_ret_spec

/--
Total-to-total program-to-program Layer 1A refinement (`implTree ≤ specTree`)
when both trees compute the same pure `(expectedTr, expectedOut)` model.
-/
theorem dwp_toPartial_refines_dwp
    {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {ewp₁ ewp₂ : StateEffectWP (List (Event E)) E}
    [TraceSoundWP ewp₁] [ConstructiveTraceWP ewp₂]
    {implTree specTree : ITree E R}
    {expectedTr : List (Event E)} {expectedOut : R}
    (h_impl :
      DWP ewp₁ implTree (fun r tr => tr = expectedTr ∧ r = expectedOut) [])
    (h_spec :
      DWP ewp₂ specTree (fun r tr => tr = expectedTr ∧ r = expectedOut) []) :
    implTree.toPartial ≤ specTree.toPartial :=
  dwlp_toPartial_refines_dwp h_impl.toDWLP
    (DWP.mono
      (fun _ _ ⟨h_ts, h_rs⟩ _ _ ⟨h_ti, h_ri⟩ =>
        ⟨h_ts.trans h_ti.symm, h_rs.trans h_ri.symm⟩)
      h_spec)

/--
Program-to-program Layer 1A behavioral equivalence (`implTree.toPartial =
specTree.toPartial`) via antisymmetry of Smyth `Partial` refinement when both
trees compute the same pure `(expectedTr, expectedOut)` model.
-/
theorem dwp_toPartial_eq_dwp
    {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {ewp₁ ewp₂ : StateEffectWP (List (Event E)) E}
    [ConstructiveTraceWP ewp₁] [ConstructiveTraceWP ewp₂]
    {implTree specTree : ITree E R}
    {expectedTr : List (Event E)} {expectedOut : R}
    (h_impl :
      DWP ewp₁ implTree (fun r tr => tr = expectedTr ∧ r = expectedOut) [])
    (h_spec :
      DWP ewp₂ specTree (fun r tr => tr = expectedTr ∧ r = expectedOut) []) :
    implTree.toPartial = specTree.toPartial :=
  Std.le_antisymm
    (dwp_toPartial_refines_dwp h_impl h_spec)
    (dwp_toPartial_refines_dwp h_spec h_impl)

/-! ### Monotone Trace-Erasing Layer 1A Observation Map (`eraseTracePartial`) -/

/--
Monotone Layer 1A observation map projecting `(trace, outcome)` partial
behaviors to return-outcome partial behaviors `Partial (BehaviorSet R)`.
-/
def eraseTracePartial {E : Effect.{u}} {R : Type u}
    (p : Partial (BehaviorSet (List (Event E) × R))) :
    Partial (BehaviorSet R) where
  defined := p.defined
  val h := BehaviorSet.map Prod.snd (p.val h)

theorem eraseTracePartial_monotone {E : Effect.{u}} {R : Type u} :
    Monotone (@eraseTracePartial E R) :=
  fun _ _ h_le h₂ =>
    let ⟨h₁, h_sub⟩ := h_le h₂
    ⟨h₁, BehaviorSet.map_monotone Prod.snd h_sub⟩

/--
Trace-free `DWLP` + `DWP` program-to-program refinement under
`eraseTracePartial`, comparing return outcomes independently of internal
`switchInt` branch-tag traces.
-/
theorem dwlp_eraseTracePartial_refines_dwp
    {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {ewp₁ ewp₂ : EffectWP E}
    [PureSoundWP ewp₁] [ConstructivePureWP ewp₂]
    {implTree specTree : ITree E R} {P : R → Prop}
    (h_impl : DWLP ewp₁ implTree (fun r _ => P r) PUnit.unit)
    (h_spec : DWP ewp₂ specTree (fun r_s _ => ∀ r_i, P r_i → r_s = r_i) PUnit.unit) :
    eraseTracePartial implTree.toPartial ≤
      eraseTracePartial specTree.toPartial := by
  obtain ⟨h_safe_impl, h_post_impl⟩ := dwlp_pure_adequacy h_impl
  obtain ⟨tr_s, r_s, h_ret_spec, h_match⟩ :=
    dwp_constructive_pure_reachesRet h_spec
  intro _
  refine ⟨h_safe_impl, fun r_i ⟨⟨tr_i, r_i'⟩, h_ret_impl, h_snd⟩ => ?_⟩
  dsimp only at h_snd
  subst h_snd
  have h_eq := h_match r_i' (h_post_impl tr_i r_i' h_ret_impl)
  subst h_eq
  exact ⟨(tr_s, r_s), h_ret_spec, rfl⟩

/--
Trace-free `DWP` + `DWP` program-to-program behavioral equality under
`eraseTracePartial`.
-/
theorem dwp_eraseTracePartial_eq_dwp
    {E : Effect.{u}} {R : Type u} [FaultEffect E]
    {ewp₁ ewp₂ : EffectWP E}
    [ConstructivePureWP ewp₁] [ConstructivePureWP ewp₂]
    {implTree specTree : ITree E R} {expectedOut : R}
    (h_impl : DWP ewp₁ implTree (fun r _ => r = expectedOut) PUnit.unit)
    (h_spec : DWP ewp₂ specTree (fun r _ => r = expectedOut) PUnit.unit) :
    eraseTracePartial implTree.toPartial =
      eraseTracePartial specTree.toPartial := by
  apply Std.le_antisymm
  · exact dwlp_eraseTracePartial_refines_dwp h_impl.toDWLP
      (DWP.mono (fun _ _ hs _ hi => hs.trans hi.symm) h_spec)
  · exact dwlp_eraseTracePartial_refines_dwp h_spec.toDWLP
      (DWP.mono (fun _ _ hi _ hs => hi.trans hs.symm) h_impl)

end Pillar4

/-! ### `V2026_06_01` MIR Termination, Trace Transformers, and Refinement Theorems -/

/--
Semantic total-termination and UB/panic/abort-freedom property for a stateful
`V2026_06_01` MIR execution `(body, args, mem)`.
-/
def MirTerminatesAndNoUB
    (body : CapturedMir) (args : List Value) (mem : Memory) : Prop :=
  let t := mirStatefulTree body args mem
  TreeSafe t ∧
  Productive t ∧
  ¬ MayDiverge t ∧
  (∃ tr retVal mem', ReachesRet t tr (.normal (retVal, mem'))) ∧
  (∀ tr out, ReachesRet t tr out →
    ∃ retVal mem', out = .normal (retVal, mem'))

/-- Establish `MirTerminatesAndNoUB` from any constructive stateless `DWP` proof. -/
theorem mirTerminatesAndNoUB_of_dwp
    {ewp : EffectWP MirEffect} [ConstructivePureWP ewp]
    {body : CapturedMir} {args : List Value} {mem : Memory}
    {P : Value → Memory → Prop}
    (h_dwp :
      DWP ewp (mirStatefulTree body args mem)
        (fun out _ =>
          ∃ retVal mem', out = .normal (retVal, mem') ∧ P retVal mem')
        PUnit.unit) :
    MirTerminatesAndNoUB body args mem := by
  obtain ⟨h_safe, h_prod, h_ndiv, ⟨tr, out, h_ret, retVal, mem', h_eq, _⟩, h_all⟩ :=
    dwp_constructive_pure_adequacy h_dwp
  subst h_eq
  refine ⟨h_safe, h_prod, h_ndiv, ⟨tr, retVal, mem', h_ret⟩, ?_⟩
  intro tr' out' h_ret'
  obtain ⟨rv, mm, h_eq', _⟩ := h_all tr' out' h_ret'
  exact ⟨rv, mm, h_eq'⟩

/-- Completed `Event MirEffect` emitted by a `TerminatorKind.switchInt` on `bits`. -/
def mirSwitchEvent (bits : Nat) : Event MirEffect :=
  ⟨.inr (.inl (.emit (.event bits))), PUnit.unit⟩

/--
Call-forbidding trace-recording predicate transformer for closed `MirEffect`
programs: rejects faults and unlinked external calls while recording `MirObsE`
events (`mirSwitchEvent bits`) onto `List (Event MirEffect)`.
-/
def mirNoCallTraceWP : StateEffectWP (List (Event MirEffect)) MirEffect where
  wp
    | .inl (.fail _), _, _ => False
    | .inr (.inl (.emit obs)), Q, tr =>
      Q PUnit.unit (tr ++ [⟨.inr (.inl (.emit obs)), PUnit.unit⟩])
    | .inr (.inr (.call _)), _, _ => False
  mono {i} _ _ _ h_imp h_wp :=
    match i with
    | .inl (.fail _) => False.elim h_wp
    | .inr (.inl (.emit _)) => h_imp PUnit.unit _ h_wp
    | .inr (.inr (.call _)) => False.elim h_wp

instance : StateEffectWP.Conjunctive mirNoCallTraceWP where
  conj {i} _ _ _ hp hq :=
    match i with
    | .inl (.fail _) => False.elim hp
    | .inr (.inl (.emit _)) => ⟨hp, hq⟩
    | .inr (.inr (.call _)) => False.elim hp

instance : StateEffectWP.ExcludedMiracle mirNoCallTraceWP where
  no_miracle {i} _ h :=
    match i with
    | .inl (.fail _) => h
    | .inr (.inl (.emit _)) => h
    | .inr (.inr (.call _)) => h

instance : TraceSoundWP mirNoCallTraceWP where
  sound {i} _ _ h_wp :=
    match i with
    | .inl (.fail _) => False.elim h_wp
    | .inr (.inl (.emit _)) => ⟨fun hf => hf, fun | .unit => h_wp⟩
    | .inr (.inr (.call _)) => False.elim h_wp

instance : ConstructiveTraceWP mirNoCallTraceWP where
  has_answer {i} _ _ h_wp :=
    match i with
    | .inl (.fail _) => False.elim h_wp
    | .inr (.inl (.emit _)) => ⟨PUnit.unit⟩
    | .inr (.inr (.call _)) => False.elim h_wp

/-- Establish `MirTerminatesAndNoUB` from a trace-aware `DWP mirNoCallTraceWP` proof. -/
theorem mirTerminatesAndNoUB_of_trace_dwp
    {body : CapturedMir} {args : List Value} {mem : Memory}
    {P : List (Event MirEffect) → Value → Memory → Prop}
    (h_dwp :
      DWP mirNoCallTraceWP (mirStatefulTree body args mem)
        (fun out tr =>
          ∃ retVal mem', out = .normal (retVal, mem') ∧ P tr retVal mem')
        []) :
    MirTerminatesAndNoUB body args mem := by
  obtain ⟨h_safe, h_prod, h_ndiv, ⟨tr, out, h_ret, retVal, mem', h_eq, _⟩, h_all⟩ :=
    dwp_constructive_trace_adequacy h_dwp
  subst h_eq
  refine ⟨h_safe, h_prod, h_ndiv, ⟨tr, retVal, mem', h_ret⟩, ?_⟩
  intro tr' out' h_ret'
  obtain ⟨rv, mm, h_eq', _⟩ := h_all tr' out' h_ret'
  exact ⟨rv, mm, h_eq'⟩

/--
`Nat`-ranked total-correctness (`DWP`) `while`-loop rule on `mirTree` for any
stateful or trace-recording `ewp : StateEffectWP S MirEffect` (including
`mirNoCallTraceWP`).
-/
theorem dwp_mirTree_stateful_while_ranked
    {S : Type} {ewp : StateEffectWP S MirEffect}
    (body : CapturedMir)
    (headerBlock : BasicBlockIdx)
    (condFuel bodyFuel : Nat)
    (Inv : Nat → MachineState → S → Prop)
    {Q : MirOutcome → S → Prop}
    (h_zero :
      ∀ s st,
        Inv 0 s st →
        ∃ bits sThen₀ sElse₀,
          runMirToBinarySwitch condFuel body s =
            some (false, bits, sThen₀, sElse₀) ∧
          ewp.wp (.inr (.inl (.emit (.event bits))))
            (fun _ st' => DWP ewp (mirTree body sElse₀) Q st') st)
    (h_succ :
      ∀ r s st,
        Inv (r + 1) s st →
        ∃ bits sThen₀ sElse₀ sNext,
          runMirToBinarySwitch condFuel body s =
            some (true, bits, sThen₀, sElse₀) ∧
          runMirTauToBlock bodyFuel body headerBlock sThen₀ = some sNext ∧
          ewp.wp (.inr (.inl (.emit (.event bits))))
            (fun _ st' => Inv r sNext st') st) :
    (rank : Nat) → ∀ {s : MachineState} {st : S},
      Inv rank s st → DWP ewp (mirTree body s) Q st
  | 0, s, st, h_inv => by
    obtain ⟨bits, sThen₀, sElse₀, h_sw, h_wp⟩ := h_zero s st h_inv
    exact dwp_any_of_runMirToBinarySwitch condFuel h_sw h_wp
  | r + 1, s, st, h_inv => by
    obtain ⟨bits, sThen₀, sElse₀, sNext, h_sw, h_body, h_wp⟩ :=
      h_succ r s st h_inv
    refine dwp_any_of_runMirToBinarySwitch condFuel h_sw ?_
    exact ewp.mono
      (fun _ _ h_next =>
        dwp_of_runMirTauToBlock bodyFuel h_body
          (dwp_mirTree_stateful_while_ranked body headerBlock condFuel bodyFuel
            Inv h_zero h_succ r h_next))
      h_wp

/--
Top-level program-to-program Layer 1A refinement bridge on `mirStatefulTree`:
proving `DWLP` for `implBody` and `DWP mirNoCallTraceWP` for `specBody` against
a shared pure Lean model `(expectedTr, expectedRet, expectedMem)` establishes
literal `(mirStatefulTree implBody args mem).toPartial ≤
(mirStatefulTree specBody args mem).toPartial`.
-/
theorem verifyStatefulRefinesViaPureModel
    {implBody specBody : CapturedMir}
    {args : List Value} {mem : Memory}
    {expectedTr : List (Event MirEffect)}
    {expectedRet : Value} {expectedMem : Memory}
    (h_impl :
      DWLP mirNoCallTraceWP (mirStatefulTree implBody args mem)
        (fun out tr =>
          tr = expectedTr ∧ out = .normal (expectedRet, expectedMem))
        [])
    (h_spec :
      DWP mirNoCallTraceWP (mirStatefulTree specBody args mem)
        (fun out tr =>
          tr = expectedTr ∧ out = .normal (expectedRet, expectedMem))
        []) :
    (mirStatefulTree implBody args mem).toPartial ≤
      (mirStatefulTree specBody args mem).toPartial :=
  dwlp_toPartial_refines_dwp h_impl
    (DWP.mono
      (fun _ _ ⟨h_ts, h_rs⟩ _ _ ⟨h_ti, h_ri⟩ =>
        ⟨h_ts.trans h_ti.symm, h_rs.trans h_ri.symm⟩)
      h_spec)

/--
Top-level program-to-program Layer 1A equivalence & termination theorem on
`mirStatefulTree`: proving `DWP mirNoCallTraceWP` for both `implBody` and
`specBody` against a shared pure Lean model `(expectedTr, expectedRet,
expectedMem)` establishes:
1. `(mirStatefulTree implBody args mem).toPartial ≤ (mirStatefulTree specBody args mem).toPartial`,
2. `(mirStatefulTree implBody args mem).toPartial = (mirStatefulTree specBody args mem).toPartial`,
3. `MirTerminatesAndNoUB implBody args mem`, and
4. `MirTerminatesAndNoUB specBody args mem`.
-/
theorem verifyTraceStatefulEquivViaPureModel
    {implBody specBody : CapturedMir}
    {args : List Value} {mem : Memory}
    {expectedTr : List (Event MirEffect)}
    {expectedRet : Value} {expectedMem : Memory}
    (h_impl :
      DWP mirNoCallTraceWP (mirStatefulTree implBody args mem)
        (fun out tr =>
          tr = expectedTr ∧ out = .normal (expectedRet, expectedMem))
        [])
    (h_spec :
      DWP mirNoCallTraceWP (mirStatefulTree specBody args mem)
        (fun out tr =>
          tr = expectedTr ∧ out = .normal (expectedRet, expectedMem))
        []) :
    (mirStatefulTree implBody args mem).toPartial ≤
      (mirStatefulTree specBody args mem).toPartial ∧
    (mirStatefulTree implBody args mem).toPartial =
      (mirStatefulTree specBody args mem).toPartial ∧
    MirTerminatesAndNoUB implBody args mem ∧
    MirTerminatesAndNoUB specBody args mem := by
  have h_eq := dwp_toPartial_eq_dwp h_impl h_spec
  refine ⟨dwp_toPartial_refines_dwp h_impl h_spec, h_eq, ?_, ?_⟩
  · exact mirTerminatesAndNoUB_of_trace_dwp (P := fun _ _ _ => True)
      (DWP.mono (fun _ _ ⟨_, h_out⟩ => ⟨expectedRet, expectedMem, h_out, trivial⟩) h_impl)
  · exact mirTerminatesAndNoUB_of_trace_dwp (P := fun _ _ _ => True)
      (DWP.mono (fun _ _ ⟨_, h_out⟩ => ⟨expectedRet, expectedMem, h_out, trivial⟩) h_spec)

/-! ### Branch-Observation-Erased `ITree.toPartial` Refinement (`mirObsErasedStatefulTree`) -/

/--
Lift any trace-free `DWP mirNoCallWP` proof (including proofs produced directly
by `wpTransPlan mirNoCallWP`) to `DWP mirNoCallTraceWP` on
`ITree.interp silenceMirObs t` with empty event trace `[]`.
-/
theorem dwp_silenceMirObs_of_dwp_noCall
    {t : ITree MirEffect MirOutcome} {post : MirOutcome → Prop}
    (h_dwp : DWP mirNoCallWP t (fun out _ => post out) PUnit.unit) :
    DWP mirNoCallTraceWP (ITree.interp silenceMirObs t)
      (fun out tr => tr = [] ∧ post out) [] := by
  have h_gen :
      ∀ (x : ITree MirEffect MirOutcome),
        DWP mirNoCallWP x (fun out _ => post out) PUnit.unit →
        ∀ tr₀ : List (Event MirEffect),
          DWP mirNoCallTraceWP (ITree.interp silenceMirObs x)
            (fun out tr => tr = tr₀ ∧ post out) tr₀ := by
    intro x hx
    refine DWP.induct
      (fun y _ =>
        ∀ tr₀ : List (Event MirEffect),
          DWP mirNoCallTraceWP (ITree.interp silenceMirObs y)
            (fun out tr => tr = tr₀ ∧ post out) tr₀)
      ?_ hx
    intro y _ hy tr₀
    cases h_obs : y.observe with
    | ret out =>
      simp only [h_obs] at hy
      have hEq : y = .ret out := by rw [← ITree.fold_observe y, h_obs]; rfl
      rw [hEq, interp_ret]
      exact DWP.ret ⟨rfl, hy⟩
    | tau y' =>
      simp only [h_obs] at hy
      have hEq : y = .tau y' := by rw [← ITree.fold_observe y, h_obs]; rfl
      rw [hEq, interp_tau]
      exact DWP.tau (hy tr₀)
    | vis i k =>
      simp only [h_obs] at hy
      have hEq : y = .vis i k := by rw [← ITree.fold_observe y, h_obs]; rfl
      rw [hEq, interp_vis]
      cases i with
      | inl fk => exact False.elim hy
      | inr rest =>
        cases rest with
        | inr callReq => exact False.elim hy
        | inl obsReq =>
          have h_bind :
              (silenceMirObs (.inr (.inl obsReq)) >>=
                fun o => (ITree.interp silenceMirObs (k o)).tau) =
              (ITree.interp silenceMirObs (k PUnit.unit)).tau :=
            ret_bind PUnit.unit (fun o => (ITree.interp silenceMirObs (k o)).tau)
          exact h_bind.symm ▸ DWP.tau (by cases obsReq; exact hy tr₀)
  exact h_gen t h_dwp []

/--
Program-to-program Layer 1A equivalence & termination across CFG-changing
optimizations directly from trace-free `wpTransPlan mirNoCallWP` plans!
-/
theorem verifyObsErasedStatefulEquivByTransPlan
    {implBody specBody : CapturedMir}
    {args : List Value} {mem : Memory}
    (implPlan specPlan : TransPlan)
    {expectedRet : Value} {expectedMem : Memory}
    (h_impl :
      wpTransPlan mirNoCallWP implBody implPlan
        (· = .normal (expectedRet, expectedMem))
        (initMachineStateWithMemory implBody args mem))
    (h_spec :
      wpTransPlan mirNoCallWP specBody specPlan
        (· = .normal (expectedRet, expectedMem))
        (initMachineStateWithMemory specBody args mem)) :
    (mirObsErasedStatefulTree implBody args mem).toPartial ≤
      (mirObsErasedStatefulTree specBody args mem).toPartial ∧
    (mirObsErasedStatefulTree implBody args mem).toPartial =
      (mirObsErasedStatefulTree specBody args mem).toPartial ∧
    eraseTracePartial (mirStatefulTree implBody args mem).toPartial =
      eraseTracePartial (mirStatefulTree specBody args mem).toPartial ∧
    MirTerminatesAndNoUB implBody args mem ∧
    MirTerminatesAndNoUB specBody args mem := by
  have hd_impl := dwp_mirStatefulTree_of_transPlan h_impl
  have hd_spec := dwp_mirStatefulTree_of_transPlan h_spec
  have ht_impl := dwp_silenceMirObs_of_dwp_noCall hd_impl
  have ht_spec := dwp_silenceMirObs_of_dwp_noCall hd_spec
  refine
    ⟨dwp_toPartial_refines_dwp ht_impl ht_spec,
     dwp_toPartial_eq_dwp ht_impl ht_spec,
     dwp_eraseTracePartial_eq_dwp hd_impl hd_spec,
     mirTerminatesAndNoUB_of_dwp (P := fun _ _ => True)
       (DWP.mono (fun _ _ h => ⟨expectedRet, expectedMem, h, trivial⟩) hd_impl),
     mirTerminatesAndNoUB_of_dwp (P := fun _ _ => True)
       (DWP.mono (fun _ _ h => ⟨expectedRet, expectedMem, h, trivial⟩) hd_spec)⟩

/--
Discharge an audited `StatefulEquivVerificationResult c` directly from
`wpTransPlan mirNoCallWP` translation plans on `c.implBody` and `c.specBody`.
-/
theorem verifyStatefulEquivClaimByTransPlan
    (c : StatefulEquivClaim)
    (implPlan specPlan : TransPlan)
    (model : List Value → Memory → Value × Memory)
    (h_impl :
      ∀ args mem,
        c.pre args mem →
        wpTransPlan mirNoCallWP c.implBody implPlan
          (fun out =>
            out = .normal (model args mem) ∧
            c.post args mem (model args mem).1 (model args mem).2)
          (initMachineStateWithMemory c.implBody args mem))
    (h_spec :
      ∀ args mem,
        c.pre args mem →
        wpTransPlan mirNoCallWP c.specBody specPlan
          (fun out => out = .normal (model args mem))
          (initMachineStateWithMemory c.specBody args mem)) :
    StatefulEquivVerificationResult c :=
  verifyStatefulEquivViaPureModel c model
    (fun args mem h_pre => dwp_mirStatefulTree_of_transPlan (h_impl args mem h_pre))
    (fun args mem h_pre => dwp_mirStatefulTree_of_transPlan (h_spec args mem h_pre))

end Anneal.FunctionalTranslation

