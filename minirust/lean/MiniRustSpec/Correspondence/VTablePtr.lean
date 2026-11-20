/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Interp

/-!
# Vtable pointers and trait-object safe pointers in `Machine::check_ptr`

`Machine::check_ptr` and `Machine::check_ptr_metadata`
(`spec/lang/representation.md`) decide three things that need the machine:

* a stand-alone vtable pointer (`PtrType::VTablePtr(trait_name)`) must be one of
  the machine's vtable pointers (`Machine::vtable_from_ptr`,
  `spec/lang/machine.md`), for a vtable of the named trait;
* vtable-pointer metadata (`PointerMeta::VTablePointer` at
  `PointerMetaKind::VTablePointer(trait_name)`) is checked by the recursive call
  `self.check_ptr(ptr.widen(None), PtrType::VTablePtr(trait_name))`;
* a safe pointer (`PtrType::Ref` / `PtrType::Box`) to a trait object
  (`LayoutStrategy::TraitObject(trait_name)`) takes its size and alignment from
  the vtable its metadata points to, and must be non-null, aligned, inhabited,
  and dereferenceable for that size.

`MiniRustSpec.Interp` transcribes them as `vtableFromPtr` / `checkPtrMetadata` /
`checkPtr` on `Mach = Machine<BasicMemory>` and `vtableFromPtrM` /
`checkPtrMetadataM` / `checkPtrM` on every `Machine M` (in particular `MachTB =
Machine<TreeBorrowsMemory>`). This module characterizes them symbolically, for
every machine:

1. `vtableFromPtrM_eq_ok_iff`, `vtableFromPtrM_eq_ub_iff`,
   `vtableFromPtrM_registered_missing_specPanic`, `vtableFromPtrM_noUnsupported`,
   `vtableLookupM_of_vtableFromPtrM_ok`: the lookup succeeds exactly when the pointer
   is registered in `vtable_ptrs` under a name bound in `prog.vtables`, is UB
   (`"invalid pointer for vtable lookup"`) exactly when the pointer is unregistered,
   is a spec panic (never UB, never `unsupported`) when a registered name has no
   vtable, and after it succeeds the `unwrap`ping `vtable_lookup` closure agrees.
2. `checkPtrMetadataM_vtablePointer_eq_checkPtrM`: the inlined metadata check is the
   spec's recursive `check_ptr` call (`checkPtrMetadataM_vtable_kind_mismatch_ub`
   covers the mismatching metadata kinds).
3. `checkPtrM_vtablePtr_eq_ok_iff` and the UB lemmas `checkPtrM_oob_ub`,
   `checkPtrM_vtablePtr_metadata_ub`, `checkPtrM_vtablePtr_unregistered_ub`,
   `checkPtrM_vtablePtr_wrong_trait_ub`: a stand-alone vtable pointer.
4. `checkPtrM_traitObject_eq` (normal form: the recursive vtable-pointer check, then
   the safe-pointer tail `safePtrTail` at the vtable's size and alignment),
   `checkPtrM_traitObject_eq_ok_iff`, `checkPtrM_traitObject_bad_metadata_ub`,
   `checkPtrM_traitObject_vtable_cases`, `safePtrTail_eq_ok_iff`, `safePtrTail_ub`:
   `&dyn Trait` / `Box<dyn Trait>`, with one UB lemma per violated requirement.
5. `checkPtrM_noUnsupported`, `checkValueM_noUnsupported`, `transmuteM_noUnsupported`,
   `evalUnOpM_transmute_noUnsupported`: with a machine supplied, `check_ptr` and
   `check_value` never stop with `Stop.unsupported` (for every memory whose
   `dereferenceable` does not: `derefNoUnsupported_BM`, `derefNoUnsupported_TBM`), and
   `Machine::transmute` / `CastOp::Transmute` do not either unless their
   machine-independent re-encoding (`Type::layout`, `encode`, `decode`) does.
6. `checkPtr_eq_checkPtrM`, `checkPtrMetadata_eq_checkPtrMetadataM`,
   `vtableFromPtr_eq_vtableFromPtrM`: the `Mach` transcription is the polymorphic one
   at `BasicMemory`, so the statements above hold for `Mach` (`vtableFromPtr_eq_ok_iff`,
   `vtableFromPtr_eq_ub_iff`, `checkPtrMetadata_vtablePointer_eq_checkPtr`,
   `checkPtr_vtablePtr_eq_ok_iff`, `checkPtr_vtablePtr_ub`,
   `checkPtr_traitObject_eq_ok_iff`, `checkPtr_noUnsupported`; `checkValue` and
   `evalUnOp` on `Mach` are covered in `Correspondence.WideSliceDst`, which has the
   `checkValueM_bm_eq` transfer in scope).
7. `VTablesAgree`, `PathFaithful`, `vtableFromPtr_agree`, `checkPtr_vtablePtr_agree`,
   `checkPtr_traitObject_agree`: `Mach` and `MachTB` machines with the same vtables
   and corresponding vtable pointers decide vtable pointers and trait-object safe
   pointers identically on every pointer whose Tree Borrows path is not confused with
   a registered vtable pointer; `vtablePtr_child_path_divergence` shows that this
   side condition is necessary.
8. Concrete witnesses on a `Mach` and a `MachTB` with two registered vtables
   (`vtMach`, `vtMachTB`): `vtableFromPtr_witness`, `checkPtr_vtablePtr_witness`,
   `checkPtr_dynRef_witness`, `transmute_vtablePtr_witness`, `vtMach_vtMachTB_agree`
   realise every `ok` and UB outcome above on both machines.
-/

namespace MiniRustSpec.Correspondence.VTablePtr

open MiniRustSpec
open MiniRustSpec.Gen
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp

/-! ## Monad and list helpers -/

private theorem okBind {α β : Type} (a : α) (f : α → Interp β) :
    (Except.ok a >>= f) = f a := rfl

private theorem errorBind {α β : Type} (e : Stop) (f : α → Interp β) :
    ((Except.error e : Interp α) >>= f) = .error e := rfl

private theorem pure_eq_ok {α : Type} (a : α) : (pure a : Interp α) = .ok a := rfl

private theorem ub_eq {α : Type} (msg : String) : (ub msg : Interp α) = .error (.ub msg) := rfl

private theorem ensureElseUb_true (msg : String) : ensureElseUb true msg = .ok () := rfl

private theorem ensureElseUb_false (msg : String) :
    ensureElseUb false msg = .error (.ub msg) := rfl

private theorem ensureElseUb_eq_ok_iff (b : Bool) (msg : String) :
    ensureElseUb b msg = .ok () ↔ b = true := by
  cases b
  · rw [ensureElseUb_false]; constructor <;> intro h <;> cases h
  · rw [ensureElseUb_true]; exact ⟨fun _ => rfl, fun _ => rfl⟩

private theorem bind_eq_ok_iff {α β : Type} (x : Interp α) (f : α → Interp β) (b : β) :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e =>
    rw [errorBind]
    constructor
    · intro h; cases h
    · rintro ⟨a, h, _⟩; cases h
  | ok a =>
    rw [okBind]
    constructor
    · intro h; exact ⟨a, rfl, h⟩
    · rintro ⟨a', h, h'⟩; cases h; exact h'

private theorem bindCongr {α β : Type} {x y : Interp α} {f g : α → Interp β}
    (hxy : x = y) (hfg : ∀ a, f a = g a) : (x >>= f) = (y >>= g) := by
  subst hxy
  cases x with
  | error _ => rfl
  | ok a => exact hfg a

private theorem find?_congr {α : Type} {p q : α → Bool} (h : ∀ x, p x = q x) :
    ∀ xs : List α, xs.find? p = xs.find? q
  | [] => rfl
  | x :: xs => by
    simp only [List.find?, h x]
    cases q x
    · exact find?_congr h xs
    · rfl

private theorem mapIndex_of_get {K V : Type} [DecidableEq K] (m : Map K V) (k : K)
    (what : String) (v : V) (h : mapGet m k = some v) : mapIndex m k what = .ok v := by
  unfold Interp.mapIndex; rw [h]; rfl

private theorem mapIndex_of_none {K V : Type} [DecidableEq K] (m : Map K V) (k : K)
    (what : String) (h : mapGet m k = none) :
    ∃ msg, mapIndex m k what = .error (.specPanic msg) := by
  unfold Interp.mapIndex; rw [h]; exact ⟨_, rfl⟩

private theorem mapIndex_eq_ok_iff {K V : Type} [DecidableEq K] (m : Map K V) (k : K)
    (what : String) (v : V) : mapIndex m k what = .ok v ↔ mapGet m k = some v := by
  cases hg : mapGet m k with
  | none =>
    rcases mapIndex_of_none m k what hg with ⟨msg, hmsg⟩
    rw [hmsg]
    constructor <;> intro h <;> cases h
  | some v' =>
    rw [mapIndex_of_get m k what v' hg]
    constructor
    · intro h; cases h; rfl
    · intro h; cases h; rfl

private theorem mapIndex_ne_ub {K V : Type} [DecidableEq K] (m : Map K V) (k : K)
    (what : String) (msg : String) : mapIndex m k what ≠ .error (.ub msg) := by
  cases hg : mapGet m k with
  | none =>
    rcases mapIndex_of_none m k what hg with ⟨msg', hmsg⟩
    rw [hmsg]; intro h; cases h
  | some v' => rw [mapIndex_of_get m k what v' hg]; intro h; cases h

/-- A computation that never stops with `Stop.unsupported`: every outcome is a
result, UB, or another genuine stop of the specification. -/
def NoUnsupported {α : Type} (x : Interp α) : Prop :=
  ∀ w : String, x ≠ .error (.unsupported w)

theorem NoUnsupported.ok {α : Type} (a : α) : NoUnsupported (Except.ok a : Interp α) :=
  fun _ h => by cases h

theorem NoUnsupported.pure {α : Type} (a : α) : NoUnsupported (Pure.pure a : Interp α) :=
  fun _ h => by cases h

theorem NoUnsupported.ub {α : Type} (msg : String) : NoUnsupported (ub msg : Interp α) :=
  fun _ h => by cases h

theorem NoUnsupported.specPanic {α : Type} (msg : String) :
    NoUnsupported (specPanic msg : Interp α) :=
  fun _ h => by cases h

theorem NoUnsupported.ensureElseUb (b : Bool) (msg : String) :
    NoUnsupported (ensureElseUb b msg) := by
  cases b
  · exact NoUnsupported.ub msg
  · exact NoUnsupported.ok ()

theorem NoUnsupported.bind {α β : Type} {x : Interp α} {f : α → Interp β}
    (hx : NoUnsupported x) (hf : ∀ a, NoUnsupported (f a)) : NoUnsupported (x >>= f) := by
  cases x with
  | error e =>
    intro w h
    rw [errorBind] at h
    have he : e = Stop.unsupported w := by cases h; rfl
    exact hx w (by rw [he])
  | ok a => exact hf a

theorem NoUnsupported.mapIndex {K V : Type} [DecidableEq K] (m : Map K V) (k : K)
    (what : String) : NoUnsupported (mapIndex m k what) := by
  unfold Interp.mapIndex
  cases mapGet m k with
  | none => exact NoUnsupported.specPanic _
  | some v => exact NoUnsupported.pure v

theorem NoUnsupported.forM {α : Type} (f : α → Interp Unit) (hf : ∀ a, NoUnsupported (f a)) :
    ∀ xs : List α, NoUnsupported (xs.forM f)
  | [] => NoUnsupported.pure ()
  | x :: xs => by
    show NoUnsupported (f x >>= fun _ => xs.forM f)
    exact NoUnsupported.bind (hf x) (fun _ => NoUnsupported.forM f hf xs)

/-! ## `Machine::vtable_from_ptr` -/

section Polymorphic

variable {M : Type} [Memory M] [MemoryOps M]

/-- `ptr` is registered in the vtable-pointer table `entries` and `name` is the
first name it is registered under, which is the entry `iter().find(..)` returns. -/
def FirstVTableName {P : Type} (entries : List (VTableName × ThinPointer P))
    (ptr : ThinPointer P) (name : VTableName) : Prop :=
  ∃ pre post, entries = pre ++ (name, ptr) :: post ∧ ∀ e ∈ pre, e.2 ≠ ptr

/-- `Machine::vtable_from_ptr` as a `find?` on the vtable-pointer table followed
by the `prog.vtables` index. -/
theorem vtableFromPtrM_eq (m : Machine M) (ptr : ThinPointer (Memory.Provenance M)) :
    vtableFromPtrM m ptr =
      match m.vtable_ptrs.entries.find? (fun e => decide (e.2 = ptr)) with
      | some e => mapIndex m.prog.vtables e.1 "self.prog.vtables[vtable_name]"
      | none => ub "invalid pointer for vtable lookup" := by
  unfold vtableFromPtrM
  rw [find?_congr (q := fun e : VTableName × ThinPointer (Memory.Provenance M) =>
    decide (e.2 = ptr)) (by intro ⟨_, _⟩; rfl)]
  cases m.vtable_ptrs.entries.find? (fun e => decide (e.2 = ptr)) with
  | none => rfl
  | some e => rcases e with ⟨_, _⟩; rfl

/-- `Machine::vtable_lookup` as a `find?` on the vtable-pointer table followed by
the `vtables` index (both failures are spec panics). -/
theorem vtableLookupM_eq (m : Machine M) (ptr : ThinPointer (Memory.Provenance M)) :
    vtableLookupM m ptr =
      match m.vtable_ptrs.entries.find? (fun e => decide (e.2 = ptr)) with
      | some e => mapIndex m.prog.vtables e.1 "vtables[name]"
      | none => specPanic "ptrs.iter().find(|(_, vtable_ptr)| *vtable_ptr == ptr).unwrap()" := by
  unfold vtableLookupM
  rw [find?_congr (q := fun e : VTableName × ThinPointer (Memory.Provenance M) =>
    decide (e.2 = ptr)) (by intro ⟨_, _⟩; rfl)]
  cases m.vtable_ptrs.entries.find? (fun e => decide (e.2 = ptr)) with
  | none => rfl
  | some e => rcases e with ⟨_, _⟩; rfl

private theorem find?_vtable_eq_some_iff {P : Type} [DecidableEq P]
    (entries : List (VTableName × ThinPointer P)) (ptr : ThinPointer P)
    (e : VTableName × ThinPointer P) :
    entries.find? (fun e => decide (e.2 = ptr)) = some e ↔
      e.2 = ptr ∧ FirstVTableName entries ptr e.1 := by
  rw [List.find?_eq_some_iff_append]
  constructor
  · rintro ⟨he, pre, post, hsplit, hpre⟩
    have he' : e.2 = ptr := of_decide_eq_true he
    refine ⟨he', pre, post, ?_, ?_⟩
    · rw [hsplit]; rcases e with ⟨n, p⟩; cases he'; rfl
    · intro a ha h
      have := hpre a ha
      simp [h] at this
  · rintro ⟨he, pre, post, hsplit, hpre⟩
    refine ⟨decide_eq_true he, pre, post, ?_, ?_⟩
    · rw [hsplit]; rcases e with ⟨n, p⟩; cases he; rfl
    · intro a ha
      simp [hpre a ha]

private theorem find?_vtable_eq_none_iff {P : Type} [DecidableEq P]
    (entries : List (VTableName × ThinPointer P)) (ptr : ThinPointer P) :
    entries.find? (fun e => decide (e.2 = ptr)) = none ↔ ∀ e ∈ entries, e.2 ≠ ptr := by
  rw [List.find?_eq_none]
  constructor
  · intro h e he heq; exact absurd (decide_eq_true heq) (by simpa using h e he)
  · intro h e he; simpa using h e he

private theorem exists_first_of_registered {P : Type} [DecidableEq P]
    (entries : List (VTableName × ThinPointer P)) (ptr : ThinPointer P)
    (h : ¬ ∀ e ∈ entries, e.2 ≠ ptr) : ∃ name, FirstVTableName entries ptr name := by
  cases hf : entries.find? (fun e => decide (e.2 = ptr)) with
  | none => exact absurd ((find?_vtable_eq_none_iff _ _).1 hf) h
  | some e => exact ⟨e.1, ((find?_vtable_eq_some_iff _ _ _).1 hf).2⟩

private theorem find?_of_first {P : Type} [DecidableEq P]
    (entries : List (VTableName × ThinPointer P)) (ptr : ThinPointer P) (name : VTableName)
    (hreg : FirstVTableName entries ptr name) :
    entries.find? (fun e => decide (e.2 = ptr)) = some (name, ptr) := by
  rcases hreg with ⟨pre, post, hsplit, hpre⟩
  exact (find?_vtable_eq_some_iff _ _ (name, ptr)).2 ⟨rfl, pre, post, hsplit, hpre⟩

/-- An unregistered (dangling, forged, or data) pointer is never a vtable pointer:
UB `"invalid pointer for vtable lookup"`. -/
theorem vtableFromPtrM_unregistered_ub (m : Machine M)
    (ptr : ThinPointer (Memory.Provenance M))
    (h : ∀ e ∈ m.vtable_ptrs.entries, e.2 ≠ ptr) :
    vtableFromPtrM m ptr = .error (.ub "invalid pointer for vtable lookup") := by
  rw [vtableFromPtrM_eq, (find?_vtable_eq_none_iff _ _).2 h]
  rfl

/-- `vtable_from_ptr` on a pointer with first registered name `name` is the
`prog.vtables` index at `name`. -/
theorem vtableFromPtrM_eq_of_first (m : Machine M)
    (ptr : ThinPointer (Memory.Provenance M)) (name : VTableName)
    (hreg : FirstVTableName m.vtable_ptrs.entries ptr name) :
    vtableFromPtrM m ptr = mapIndex m.prog.vtables name "self.prog.vtables[vtable_name]" := by
  rw [vtableFromPtrM_eq, find?_of_first _ _ _ hreg]

/-- **`vtable_from_ptr` succeeds exactly on registered pointers with a vtable.** The
lookup returns `vtable` iff `ptr` is registered in `vtable_ptrs` and the first name
it is registered under is bound to `vtable` in `prog.vtables`. -/
theorem vtableFromPtrM_eq_ok_iff (m : Machine M) (ptr : ThinPointer (Memory.Provenance M))
    (vtable : VTable) :
    vtableFromPtrM m ptr = .ok vtable ↔
      ∃ name, FirstVTableName m.vtable_ptrs.entries ptr name ∧
        mapGet m.prog.vtables name = some vtable := by
  constructor
  · intro h
    by_cases hunreg : ∀ e ∈ m.vtable_ptrs.entries, e.2 ≠ ptr
    · rw [vtableFromPtrM_unregistered_ub m ptr hunreg] at h; cases h
    · rcases exists_first_of_registered _ _ hunreg with ⟨name, hfirst⟩
      rw [vtableFromPtrM_eq_of_first m ptr name hfirst] at h
      exact ⟨name, hfirst, (mapIndex_eq_ok_iff _ _ _ _).1 h⟩
  · rintro ⟨name, hfirst, hget⟩
    rw [vtableFromPtrM_eq_of_first m ptr name hfirst]
    exact (mapIndex_eq_ok_iff _ _ _ _).2 hget

/-- **`vtable_from_ptr` is UB exactly on unregistered pointers.** The lookup raises
UB iff no entry of `vtable_ptrs` is `ptr`, and the message is the spec's. -/
theorem vtableFromPtrM_eq_ub_iff (m : Machine M) (ptr : ThinPointer (Memory.Provenance M))
    (msg : String) :
    vtableFromPtrM m ptr = .error (.ub msg) ↔
      msg = "invalid pointer for vtable lookup" ∧ ∀ e ∈ m.vtable_ptrs.entries, e.2 ≠ ptr := by
  constructor
  · intro h
    by_cases hunreg : ∀ e ∈ m.vtable_ptrs.entries, e.2 ≠ ptr
    · rw [vtableFromPtrM_unregistered_ub m ptr hunreg] at h
      cases h
      exact ⟨rfl, hunreg⟩
    · rcases exists_first_of_registered _ _ hunreg with ⟨name, hfirst⟩
      rw [vtableFromPtrM_eq_of_first m ptr name hfirst] at h
      exact absurd h (mapIndex_ne_ub _ _ _ _)
  · rintro ⟨rfl, hunreg⟩
    exact vtableFromPtrM_unregistered_ub m ptr hunreg

/-- A registered pointer whose name has no vtable in `prog.vtables` is the spec's
`self.prog.vtables[vtable_name]` index panic (an ill-formed machine), not UB. -/
theorem vtableFromPtrM_registered_missing_specPanic (m : Machine M)
    (ptr : ThinPointer (Memory.Provenance M)) (name : VTableName)
    (hreg : FirstVTableName m.vtable_ptrs.entries ptr name)
    (hmissing : mapGet m.prog.vtables name = none) :
    ∃ msg, vtableFromPtrM m ptr = .error (.specPanic msg) := by
  rw [vtableFromPtrM_eq_of_first m ptr name hreg]
  exact mapIndex_of_none _ _ _ hmissing

/-- `vtable_from_ptr` never stops with `Stop.unsupported`. -/
theorem vtableFromPtrM_noUnsupported (m : Machine M)
    (ptr : ThinPointer (Memory.Provenance M)) : NoUnsupported (vtableFromPtrM m ptr) := by
  rw [vtableFromPtrM_eq]
  cases m.vtable_ptrs.entries.find? (fun e => decide (e.2 = ptr)) with
  | none => exact NoUnsupported.ub _
  | some e => exact NoUnsupported.mapIndex _ _ _

/-- After `vtable_from_ptr` succeeded, the `unwrap`ping `Machine::vtable_lookup`
closure returns the same vtable: computing the size and alignment of a checked
trait-object pointer cannot hit the closure's spec panic. -/
theorem vtableLookupM_of_vtableFromPtrM_ok (m : Machine M)
    (ptr : ThinPointer (Memory.Provenance M)) (vtable : VTable)
    (h : vtableFromPtrM m ptr = .ok vtable) : vtableLookupM m ptr = .ok vtable := by
  rcases (vtableFromPtrM_eq_ok_iff m ptr vtable).1 h with ⟨name, hfirst, hget⟩
  rw [vtableLookupM_eq, find?_of_first _ _ _ hfirst]
  exact mapIndex_of_get _ _ _ _ hget

/-! ## `Machine::check_ptr_metadata` and `Machine::check_ptr` at `PtrType::VTablePtr` -/

/-- **The inlined vtable-metadata check is the spec's recursive call.**
`check_ptr_metadata` on `(Some(PointerMeta::VTablePointer(ptr)),
PointerMetaKind::VTablePointer(trait_name))` is
`self.check_ptr(ptr.widen(None), PtrType::VTablePtr(trait_name))`. -/
theorem checkPtrMetadataM_vtablePointer_eq_checkPtrM (m : Machine M)
    (vp : ThinPointer (Memory.Provenance M)) (traitName : TraitName) :
    checkPtrMetadataM (some (.VTablePointer vp)) (.VTablePointer traitName) (some m) =
      checkPtrM (ThinPointer.widen vp none) (.VTablePtr traitName) (some m) := by
  unfold checkPtrMetadataM checkPtrM
  rfl

/-- Vtable-pointer metadata never matches another metadata kind, and the vtable
metadata kind accepts only vtable-pointer metadata: UB `"Value::Ptr: invalid
metadata"`, with or without a machine. -/
theorem checkPtrMetadataM_vtable_kind_mismatch_ub (mo : Option (Machine M))
    (vp : ThinPointer (Memory.Provenance M)) (traitName : TraitName) (num : Int) :
    checkPtrMetadataM (some (.VTablePointer vp)) .None mo =
        .error (.ub "Value::Ptr: invalid metadata") ∧
      checkPtrMetadataM (some (.VTablePointer vp)) .ElementCount mo =
        .error (.ub "Value::Ptr: invalid metadata") ∧
      checkPtrMetadataM (M := M) none (.VTablePointer traitName) mo =
        .error (.ub "Value::Ptr: invalid metadata") ∧
      checkPtrMetadataM (M := M) (some (.ElementCount num)) (.VTablePointer traitName) mo =
        .error (.ub "Value::Ptr: invalid metadata") :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- An address outside `[0, 2^64)` is rejected first, at every pointer type:
UB `"Value::Ptr: pointer out-of-bounds"`. -/
theorem checkPtrM_oob_ub (mo : Option (Machine M)) (ptr : Pointer (Memory.Provenance M))
    (ptrTy : PtrType)
    (hoob : inBounds ptr.thin_pointer.addr .Unsigned x86_64.PTR_SIZE = false) :
    checkPtrM ptr ptrTy mo = .error (.ub "Value::Ptr: pointer out-of-bounds") := by
  unfold checkPtrM
  rw [hoob, ensureElseUb_false, errorBind]

/-- `check_ptr` at a stand-alone vtable pointer without metadata and with an
in-bounds address is `vtable_from_ptr` followed by the trait-name check. -/
theorem checkPtrM_vtablePtr_thin_eq (m : Machine M) (tp : ThinPointer (Memory.Provenance M))
    (traitName : TraitName)
    (hin : inBounds tp.addr .Unsigned x86_64.PTR_SIZE = true) :
    checkPtrM ⟨tp, none⟩ (.VTablePtr traitName) (some m) =
      (vtableFromPtrM m tp >>= fun vtable =>
        ensureElseUb (decide (vtable.trait_name = traitName))
          "Value::Ptr: invalid vtable in metadata") := by
  unfold checkPtrM
  rw [hin, ensureElseUb_true, okBind]
  rfl

/-- **`check_ptr` accepts a stand-alone vtable pointer exactly when** its address
fits a `usize`, it carries no metadata, and it is one of the machine's vtable
pointers, for a vtable of trait `traitName`. -/
theorem checkPtrM_vtablePtr_eq_ok_iff (m : Machine M) (ptr : Pointer (Memory.Provenance M))
    (traitName : TraitName) :
    checkPtrM ptr (.VTablePtr traitName) (some m) = .ok () ↔
      inBounds ptr.thin_pointer.addr .Unsigned x86_64.PTR_SIZE = true ∧
      ptr.metadata = none ∧
      ∃ vtable, vtableFromPtrM m ptr.thin_pointer = .ok vtable ∧
        vtable.trait_name = traitName := by
  rcases ptr with ⟨tp, md⟩
  cases hin : inBounds tp.addr .Unsigned x86_64.PTR_SIZE with
  | false =>
    rw [checkPtrM_oob_ub _ _ _ hin]
    constructor
    · intro h; cases h
    · rintro ⟨h, _⟩; cases h
  | true =>
    cases md with
    | some md =>
      have hub : checkPtrM ⟨tp, some md⟩ (.VTablePtr traitName) (some m) =
          .error (.ub "Value::Ptr: invalid metadata") := by
        unfold checkPtrM
        rw [hin, ensureElseUb_true, okBind]
        cases md <;> rfl
      rw [hub]
      constructor
      · intro h; cases h
      · rintro ⟨_, h, _⟩; cases h
    | none =>
      rw [checkPtrM_vtablePtr_thin_eq m tp traitName hin, bind_eq_ok_iff]
      constructor
      · rintro ⟨vtable, hv, ht⟩
        exact ⟨rfl, rfl, vtable, hv, of_decide_eq_true ((ensureElseUb_eq_ok_iff _ _).1 ht)⟩
      · rintro ⟨_, _, vtable, hv, ht⟩
        exact ⟨vtable, hv, (ensureElseUb_eq_ok_iff _ _).2 (decide_eq_true ht)⟩

/-- A stand-alone vtable pointer with metadata is UB (`"Value::Ptr: invalid
metadata"`): `PtrType::VTablePtr(_).meta_kind()` is `PointerMetaKind::None`. -/
theorem checkPtrM_vtablePtr_metadata_ub (m : Machine M)
    (tp : ThinPointer (Memory.Provenance M)) (md : PointerMeta (Memory.Provenance M))
    (traitName : TraitName)
    (hin : inBounds tp.addr .Unsigned x86_64.PTR_SIZE = true) :
    checkPtrM ⟨tp, some md⟩ (.VTablePtr traitName) (some m) =
      .error (.ub "Value::Ptr: invalid metadata") := by
  unfold checkPtrM
  rw [hin, ensureElseUb_true, okBind]
  cases md <;> rfl

/-- A stand-alone vtable pointer that is not registered in `vtable_ptrs` is UB
(`"invalid pointer for vtable lookup"`). -/
theorem checkPtrM_vtablePtr_unregistered_ub (m : Machine M)
    (tp : ThinPointer (Memory.Provenance M)) (traitName : TraitName)
    (hin : inBounds tp.addr .Unsigned x86_64.PTR_SIZE = true)
    (hunreg : ∀ e ∈ m.vtable_ptrs.entries, e.2 ≠ tp) :
    checkPtrM ⟨tp, none⟩ (.VTablePtr traitName) (some m) =
      .error (.ub "invalid pointer for vtable lookup") := by
  rw [checkPtrM_vtablePtr_thin_eq m tp traitName hin,
    vtableFromPtrM_unregistered_ub m tp hunreg, errorBind]

/-- A registered vtable pointer for a vtable of another trait is UB
(`"Value::Ptr: invalid vtable in metadata"`). -/
theorem checkPtrM_vtablePtr_wrong_trait_ub (m : Machine M)
    (tp : ThinPointer (Memory.Provenance M)) (traitName : TraitName) (vtable : VTable)
    (hin : inBounds tp.addr .Unsigned x86_64.PTR_SIZE = true)
    (hv : vtableFromPtrM m tp = .ok vtable)
    (hne : vtable.trait_name ≠ traitName) :
    checkPtrM ⟨tp, none⟩ (.VTablePtr traitName) (some m) =
      .error (.ub "Value::Ptr: invalid vtable in metadata") := by
  rw [checkPtrM_vtablePtr_thin_eq m tp traitName hin, hv, okBind, decide_eq_false hne,
    ensureElseUb_false]

/-! ## `Machine::check_ptr` at trait-object safe pointers (`&dyn Trait`, `Box<dyn Trait>`) -/

private theorem traitObject_meta_kind (ptrTy : PtrType) (pointee : PointeeInfo)
    (traitName : TraitName)
    (hsafe : PtrType.safe_pointee ptrTy = some pointee)
    (hlay : pointee.layout = .TraitObject traitName) :
    PtrType.meta_kind ptrTy = .VTablePointer traitName := by
  cases ptrTy with
  | Ref mutbl p =>
    have hp : p = pointee := Option.some.inj hsafe
    subst hp
    simp only [PtrType.meta_kind, hlay, LayoutStrategy.meta_kind]
  | Box p =>
    have hp : p = pointee := Option.some.inj hsafe
    subst hp
    simp only [PtrType.meta_kind, hlay, LayoutStrategy.meta_kind]
  | Raw _ => cases hsafe
  | FnPtr => cases hsafe
  | VTablePtr _ => cases hsafe

/-- The dereferenceability requirement of `check_ptr`,
`ensure_else_ub(self.mem.dereferenceable(..).is_ok(), ..)`, on the result `r` of
`dereferenceable`: UB of the memory becomes UB `"Value::Ptr: non-dereferenceable safe
pointer"`. -/
def derefStep (r : Interp Unit) : Interp Unit :=
  match r with
  | .ok () => pure ()
  | .error (.ub _) => ub "Value::Ptr: non-dereferenceable safe pointer"
  | .error e => .error e

/-- The safe-pointer requirements of `check_ptr` that follow the metadata check,
for a pointee of dynamic size `size` and alignment `align` (the spec's order). -/
def safePtrTail (m : Machine M) (tp : ThinPointer (Memory.Provenance M))
    (pointee : PointeeInfo) (size : Size) (align : Align) : Interp Unit := do
  ensureElseUb (inBounds size.bytes .Signed x86_64.PTR_SIZE)
    "Value::Ptr: total size exeeds isize::MAX"
  ensureElseUb (tp.addr != 0) "Value::Ptr: null safe pointer"
  ensureElseUb (Align.is_aligned align tp.addr) "Value::Ptr: unaligned safe pointer"
  ensureElseUb pointee.inhabited "Value::Ptr: safe pointer to uninhabited type"
  derefStep (ConcurrentMemory.dereferenceable m.mem tp size)

/-- **Normal form of `check_ptr` at a safe pointer to a trait object.** After the
address bound, the metadata must be a vtable pointer that passes `check_ptr` at
`PtrType::VTablePtr(trait_name)` (the spec's recursive call); the vtable then
supplies the dynamic size and alignment of the remaining safe-pointer requirements. -/
theorem checkPtrM_traitObject_eq (m : Machine M) (tp : ThinPointer (Memory.Provenance M))
    (vp : ThinPointer (Memory.Provenance M)) (ptrTy : PtrType) (pointee : PointeeInfo)
    (traitName : TraitName)
    (hsafe : PtrType.safe_pointee ptrTy = some pointee)
    (hlay : pointee.layout = .TraitObject traitName)
    (hin : inBounds tp.addr .Unsigned x86_64.PTR_SIZE = true) :
    checkPtrM ⟨tp, some (.VTablePointer vp)⟩ ptrTy (some m) =
      (checkPtrM ⟨vp, none⟩ (.VTablePtr traitName) (some m) >>= fun _ =>
        vtableLookupM m vp >>= fun vtable =>
          safePtrTail m tp pointee vtable.size vtable.align) := by
  unfold checkPtrM
  rw [traitObject_meta_kind ptrTy pointee traitName hsafe hlay, hsafe]
  dsimp only
  rw [hin, ensureElseUb_true, okBind, hlay, checkPtrMetadataM_vtablePointer_eq_checkPtrM]
  refine bindCongr rfl (fun _ => ?_)
  unfold LayoutStrategy.compute_size_and_align
  cases vtableLookupM m vp with
  | error e => rfl
  | ok vtable => rfl

/-- Trait-object safe pointers reject thin pointers and slice metadata: UB
`"Value::Ptr: invalid metadata"`. -/
theorem checkPtrM_traitObject_bad_metadata_ub (m : Machine M)
    (tp : ThinPointer (Memory.Provenance M)) (ptrTy : PtrType) (pointee : PointeeInfo)
    (traitName : TraitName)
    (hsafe : PtrType.safe_pointee ptrTy = some pointee)
    (hlay : pointee.layout = .TraitObject traitName)
    (hin : inBounds tp.addr .Unsigned x86_64.PTR_SIZE = true) :
    checkPtrM ⟨tp, none⟩ ptrTy (some m) = .error (.ub "Value::Ptr: invalid metadata") ∧
    ∀ num, checkPtrM ⟨tp, some (.ElementCount num)⟩ ptrTy (some m) =
      .error (.ub "Value::Ptr: invalid metadata") := by
  constructor
  · unfold checkPtrM
    rw [traitObject_meta_kind ptrTy pointee traitName hsafe hlay, hin, ensureElseUb_true, okBind]
    rfl
  · intro num
    unfold checkPtrM
    rw [traitObject_meta_kind ptrTy pointee traitName hsafe hlay, hin, ensureElseUb_true, okBind]
    rfl

private theorem derefStep_eq_ok_iff (r : Interp Unit) : derefStep r = .ok () ↔ r = .ok () := by
  unfold derefStep
  cases r with
  | ok u => cases u; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | error e =>
    cases e <;> constructor <;> intro h <;> cases h

/-- The safe-pointer tail succeeds exactly when every requirement holds. -/
theorem safePtrTail_eq_ok_iff (m : Machine M) (tp : ThinPointer (Memory.Provenance M))
    (pointee : PointeeInfo) (size : Size) (align : Align) :
    safePtrTail m tp pointee size align = .ok () ↔
      inBounds size.bytes .Signed x86_64.PTR_SIZE = true ∧
      tp.addr ≠ 0 ∧
      Align.is_aligned align tp.addr = true ∧
      pointee.inhabited = true ∧
      ConcurrentMemory.dereferenceable m.mem tp size = .ok () := by
  unfold safePtrTail
  constructor
  · intro h
    rcases (bind_eq_ok_iff _ _ _).1 h with ⟨u1, h1, h⟩
    rcases (bind_eq_ok_iff _ _ _).1 h with ⟨u2, h2, h⟩
    rcases (bind_eq_ok_iff _ _ _).1 h with ⟨u3, h3, h⟩
    rcases (bind_eq_ok_iff _ _ _).1 h with ⟨u4, h4, h⟩
    exact ⟨(ensureElseUb_eq_ok_iff _ _).1 h1,
      bne_iff_ne.1 ((ensureElseUb_eq_ok_iff _ _).1 h2),
      (ensureElseUb_eq_ok_iff _ _).1 h3, (ensureElseUb_eq_ok_iff _ _).1 h4,
      (derefStep_eq_ok_iff _).1 h⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    rw [h1, ensureElseUb_true, okBind, bne_iff_ne.2 h2, ensureElseUb_true, okBind, h3,
      ensureElseUb_true, okBind, h4, ensureElseUb_true, okBind]
    exact (derefStep_eq_ok_iff _).2 h5

/-- UB outcomes of the safe-pointer tail, one per violated requirement, each under
the hypothesis that the earlier requirements hold (the spec's order). -/
theorem safePtrTail_ub (m : Machine M) (tp : ThinPointer (Memory.Provenance M))
    (pointee : PointeeInfo) (size : Size) (align : Align) :
    (inBounds size.bytes .Signed x86_64.PTR_SIZE = false →
      safePtrTail m tp pointee size align =
        .error (.ub "Value::Ptr: total size exeeds isize::MAX")) ∧
    (inBounds size.bytes .Signed x86_64.PTR_SIZE = true →
      (tp.addr = 0 →
        safePtrTail m tp pointee size align = .error (.ub "Value::Ptr: null safe pointer")) ∧
      (tp.addr ≠ 0 →
        (Align.is_aligned align tp.addr = false →
          safePtrTail m tp pointee size align =
            .error (.ub "Value::Ptr: unaligned safe pointer")) ∧
        (Align.is_aligned align tp.addr = true →
          (pointee.inhabited = false →
            safePtrTail m tp pointee size align =
              .error (.ub "Value::Ptr: safe pointer to uninhabited type")) ∧
          (pointee.inhabited = true →
            ∀ msg, ConcurrentMemory.dereferenceable m.mem tp size = .error (.ub msg) →
              safePtrTail m tp pointee size align =
                .error (.ub "Value::Ptr: non-dereferenceable safe pointer"))))) := by
  unfold safePtrTail
  refine ⟨fun hsz => ?_, fun hsz => ⟨fun hnull => ?_, fun hnn => ⟨fun hal => ?_, fun hal =>
    ⟨fun hinh => ?_, fun hinh msg hd => ?_⟩⟩⟩⟩
  · rw [hsz, ensureElseUb_false, errorBind]
  · have hb : (tp.addr != 0) = false := by rw [hnull]; rfl
    rw [hsz, ensureElseUb_true, okBind, hb, ensureElseUb_false, errorBind]
  · have hb : (tp.addr != 0) = true := bne_iff_ne.2 hnn
    rw [hsz, ensureElseUb_true, okBind, hb, ensureElseUb_true, okBind, hal,
      ensureElseUb_false, errorBind]
  · have hb : (tp.addr != 0) = true := bne_iff_ne.2 hnn
    rw [hsz, ensureElseUb_true, okBind, hb, ensureElseUb_true, okBind, hal,
      ensureElseUb_true, okBind, hinh, ensureElseUb_false, errorBind]
  · have hb : (tp.addr != 0) = true := bne_iff_ne.2 hnn
    rw [hsz, ensureElseUb_true, okBind, hb, ensureElseUb_true, okBind, hal,
      ensureElseUb_true, okBind, hinh, ensureElseUb_true, okBind, hd]
    rfl

/-- **`check_ptr` accepts `&dyn Trait` / `Box<dyn Trait>` exactly when** the address
fits a `usize`, the metadata is a registered in-bounds vtable pointer for
`traitName`, the vtable's dynamic size fits `isize::MAX`, the address is non-null
and aligned to the vtable's alignment, the pointee is inhabited, and the memory is
dereferenceable for the vtable's size. -/
theorem checkPtrM_traitObject_eq_ok_iff (m : Machine M)
    (ptr : Pointer (Memory.Provenance M)) (ptrTy : PtrType) (pointee : PointeeInfo)
    (traitName : TraitName)
    (hsafe : PtrType.safe_pointee ptrTy = some pointee)
    (hlay : pointee.layout = .TraitObject traitName) :
    checkPtrM ptr ptrTy (some m) = .ok () ↔
      inBounds ptr.thin_pointer.addr .Unsigned x86_64.PTR_SIZE = true ∧
      ∃ vp vtable, ptr.metadata = some (.VTablePointer vp) ∧
        inBounds vp.addr .Unsigned x86_64.PTR_SIZE = true ∧
        vtableFromPtrM m vp = .ok vtable ∧ vtable.trait_name = traitName ∧
        inBounds vtable.size.bytes .Signed x86_64.PTR_SIZE = true ∧
        ptr.thin_pointer.addr ≠ 0 ∧
        Align.is_aligned vtable.align ptr.thin_pointer.addr = true ∧
        pointee.inhabited = true ∧
        ConcurrentMemory.dereferenceable m.mem ptr.thin_pointer vtable.size = .ok () := by
  rcases ptr with ⟨tp, md⟩
  cases hin : inBounds tp.addr .Unsigned x86_64.PTR_SIZE with
  | false =>
    rw [checkPtrM_oob_ub _ _ _ hin]
    constructor
    · intro h; cases h
    · rintro ⟨h, _⟩; cases h
  | true =>
    have hbad := checkPtrM_traitObject_bad_metadata_ub m tp ptrTy pointee traitName hsafe hlay hin
    rcases md with _ | (num | vp)
    · rw [hbad.1]
      constructor
      · intro h; cases h
      · rintro ⟨_, _, _, h, _⟩; cases h
    · rw [hbad.2 num]
      constructor
      · intro h; cases h
      · rintro ⟨_, _, _, h, _⟩; cases h
    · rw [checkPtrM_traitObject_eq m tp vp ptrTy pointee traitName hsafe hlay hin,
        bind_eq_ok_iff]
      constructor
      · rintro ⟨_, hmeta, htail⟩
        rcases (checkPtrM_vtablePtr_eq_ok_iff m _ traitName).1 hmeta with
          ⟨hinv, _, vtable, hv, ht⟩
        have hlook : vtableLookupM m vp = .ok vtable :=
          vtableLookupM_of_vtableFromPtrM_ok m vp vtable hv
        rw [hlook, okBind] at htail
        rcases (safePtrTail_eq_ok_iff m tp pointee _ _).1 htail with ⟨h1, h2, h3, h4, h5⟩
        exact ⟨rfl, vp, vtable, rfl, hinv, hv, ht, h1, h2, h3, h4, h5⟩
      · rintro ⟨_, vp', vtable, hmd, hinv, hv, ht, h1, h2, h3, h4, h5⟩
        cases hmd
        refine ⟨(), (checkPtrM_vtablePtr_eq_ok_iff m _ traitName).2
          ⟨hinv, rfl, vtable, hv, ht⟩, ?_⟩
        rw [vtableLookupM_of_vtableFromPtrM_ok m vp vtable hv, okBind]
        exact (safePtrTail_eq_ok_iff m tp pointee _ _).2 ⟨h1, h2, h3, h4, h5⟩

/-- **UB of `check_ptr` at `&dyn Trait` / `Box<dyn Trait>` through the vtable
pointer.** With an in-bounds data address: an unregistered vtable pointer in the
metadata is UB `"invalid pointer for vtable lookup"`, a vtable of another trait is UB
`"Value::Ptr: invalid vtable in metadata"`, and with a vtable of the right trait the
outcome is the safe-pointer tail at the vtable's size and alignment (whose UB
outcomes are `safePtrTail_ub`). -/
theorem checkPtrM_traitObject_vtable_cases (m : Machine M)
    (tp vp : ThinPointer (Memory.Provenance M)) (ptrTy : PtrType) (pointee : PointeeInfo)
    (traitName : TraitName)
    (hsafe : PtrType.safe_pointee ptrTy = some pointee)
    (hlay : pointee.layout = .TraitObject traitName)
    (hin : inBounds tp.addr .Unsigned x86_64.PTR_SIZE = true)
    (hinv : inBounds vp.addr .Unsigned x86_64.PTR_SIZE = true) :
    ((∀ e ∈ m.vtable_ptrs.entries, e.2 ≠ vp) →
      checkPtrM ⟨tp, some (.VTablePointer vp)⟩ ptrTy (some m) =
        .error (.ub "invalid pointer for vtable lookup")) ∧
    (∀ vtable, vtableFromPtrM m vp = .ok vtable →
      (vtable.trait_name ≠ traitName →
        checkPtrM ⟨tp, some (.VTablePointer vp)⟩ ptrTy (some m) =
          .error (.ub "Value::Ptr: invalid vtable in metadata")) ∧
      (vtable.trait_name = traitName →
        checkPtrM ⟨tp, some (.VTablePointer vp)⟩ ptrTy (some m) =
          safePtrTail m tp pointee vtable.size vtable.align)) := by
  have hnf := checkPtrM_traitObject_eq m tp vp ptrTy pointee traitName hsafe hlay hin
  refine ⟨fun hunreg => ?_, fun vtable hv => ⟨fun hne => ?_, fun ht => ?_⟩⟩
  · rw [hnf, checkPtrM_vtablePtr_unregistered_ub m vp traitName hinv hunreg, errorBind]
  · rw [hnf, checkPtrM_vtablePtr_wrong_trait_ub m vp traitName vtable hinv hv hne, errorBind]
  · rw [hnf, (checkPtrM_vtablePtr_eq_ok_iff m _ traitName).2 ⟨hinv, rfl, vtable, hv, ht⟩,
      okBind, vtableLookupM_of_vtableFromPtrM_ok m vp vtable hv, okBind]

/-! ## With a machine, validity checking never stops with `Stop.unsupported` -/

/-- Memories whose `dereferenceable` never reports `Stop.unsupported` (`BasicMemory` and
`TreeBorrowsMemory` are, `derefNoUnsupported_BM` / `derefNoUnsupported_TBM`). -/
def DerefNoUnsupported (M : Type) [Memory M] [MemoryOps M] : Prop :=
  ∀ (mem : M) (ptr : ThinPointer (Memory.Provenance M)) (len : Size),
    NoUnsupported (MemoryOps.dereferenceable mem ptr len)

theorem vtableLookupM_noUnsupported (m : Machine M)
    (ptr : ThinPointer (Memory.Provenance M)) : NoUnsupported (vtableLookupM m ptr) := by
  unfold vtableLookupM
  rw [find?_congr (q := fun e : VTableName × ThinPointer (Memory.Provenance M) =>
    decide (e.2 = ptr)) (by intro ⟨_, _⟩; rfl)]
  cases m.vtable_ptrs.entries.find? (fun e => decide (e.2 = ptr)) with
  | none => exact NoUnsupported.specPanic _
  | some e => rcases e with ⟨name, _⟩; exact NoUnsupported.mapIndex _ _ _

theorem compute_size_and_align_noUnsupported {P : Type}
    (lookup : ThinPointer P → Interp VTable) (hl : ∀ p, NoUnsupported (lookup p)) :
    ∀ (layout : LayoutStrategy) (md : Option (PointerMeta P)),
      NoUnsupported (LayoutStrategy.compute_size_and_align lookup layout md)
  | .Sized _ _, none => by
    unfold LayoutStrategy.compute_size_and_align; exact NoUnsupported.pure _
  | .Sized _ _, some _ => by
    unfold LayoutStrategy.compute_size_and_align; exact NoUnsupported.specPanic _
  | .Slice _ _, none => by
    unfold LayoutStrategy.compute_size_and_align; exact NoUnsupported.specPanic _
  | .Slice _ _, some (.ElementCount _) => by
    unfold LayoutStrategy.compute_size_and_align
    dsimp only
    split
    · exact NoUnsupported.pure _
    · exact NoUnsupported.specPanic _
  | .Slice _ _, some (.VTablePointer _) => by
    unfold LayoutStrategy.compute_size_and_align; exact NoUnsupported.specPanic _
  | .TraitObject _, none => by
    unfold LayoutStrategy.compute_size_and_align; exact NoUnsupported.specPanic _
  | .TraitObject _, some (.ElementCount _) => by
    unfold LayoutStrategy.compute_size_and_align; exact NoUnsupported.specPanic _
  | .TraitObject _, some (.VTablePointer vp) => by
    unfold LayoutStrategy.compute_size_and_align
    exact NoUnsupported.bind (hl vp) (fun _ => NoUnsupported.pure _)
  | .Tuple _ _, none => by
    unfold LayoutStrategy.compute_size_and_align; exact NoUnsupported.specPanic _
  | .Tuple _ tail, some md => by
    unfold LayoutStrategy.compute_size_and_align
    exact NoUnsupported.bind (compute_size_and_align_noUnsupported lookup hl tail (some md))
      (fun ⟨_, _⟩ => NoUnsupported.pure _)

theorem checkPtrMetadataM_noUnsupported (m : Machine M)
    (pm : Option (PointerMeta (Memory.Provenance M))) (kind : PointerMetaKind) :
    NoUnsupported (checkPtrMetadataM pm kind (some m)) := by
  unfold checkPtrMetadataM
  rcases pm with _ | (num | vp) <;> cases kind
  all_goals first
    | exact NoUnsupported.pure _
    | exact NoUnsupported.ub _
    | exact NoUnsupported.ensureElseUb _ _
    | exact NoUnsupported.bind (NoUnsupported.ensureElseUb _ _) (fun _ =>
        NoUnsupported.bind (vtableFromPtrM_noUnsupported m _) (fun _ =>
          NoUnsupported.ensureElseUb _ _))

/-- **`check_ptr` with a machine never stops with `Stop.unsupported`**: the
`m = none` fallbacks for vtable pointers, vtable metadata, trait-object safe
pointers, and safe-pointer dereferenceability are unreachable from a machine. -/
theorem checkPtrM_noUnsupported (hderef : DerefNoUnsupported M) (m : Machine M)
    (ptr : Pointer (Memory.Provenance M)) (ptrTy : PtrType) :
    NoUnsupported (checkPtrM ptr ptrTy (some m)) := by
  unfold checkPtrM
  refine NoUnsupported.bind (NoUnsupported.ensureElseUb _ _) (fun _ => ?_)
  refine NoUnsupported.bind (checkPtrMetadataM_noUnsupported m _ _) (fun _ => ?_)
  cases PtrType.safe_pointee ptrTy with
  | some pointee =>
    dsimp only
    refine NoUnsupported.bind
      (compute_size_and_align_noUnsupported _ (vtableLookupM_noUnsupported m) _ _)
      (fun ⟨size, align⟩ => ?_)
    dsimp only
    refine NoUnsupported.bind (NoUnsupported.ensureElseUb _ _) (fun _ => ?_)
    refine NoUnsupported.bind (NoUnsupported.ensureElseUb _ _) (fun _ => ?_)
    refine NoUnsupported.bind (NoUnsupported.ensureElseUb _ _) (fun _ => ?_)
    refine NoUnsupported.bind (NoUnsupported.ensureElseUb _ _) (fun _ => ?_)
    have hd := hderef m.mem.memory ptr.thin_pointer size
    unfold ConcurrentMemory.dereferenceable
    cases hres : MemoryOps.dereferenceable m.mem.memory ptr.thin_pointer size with
    | ok u => cases u; exact NoUnsupported.pure ()
    | error e =>
      cases e with
      | ub _ => exact NoUnsupported.ub _
      | unsupported w => exact absurd hres (hd w)
      | _ => intro w h; cases h
  | none =>
    dsimp only
    cases ptrTy with
    | VTablePtr t =>
      exact NoUnsupported.bind (vtableFromPtrM_noUnsupported m _)
        (fun _ => NoUnsupported.ensureElseUb _ _)
    | _ => exact NoUnsupported.pure ()

theorem checkUnionChunksM_noUnsupported {P : Type} :
    ∀ (chunkData : List (List (AbstractByte P))) (chunks : List (Offset × Size)),
      NoUnsupported (checkUnionChunksM chunkData chunks)
  | [], _ => by unfold checkUnionChunksM; exact NoUnsupported.pure _
  | (_ :: _), [] => by unfold checkUnionChunksM; exact NoUnsupported.pure _
  | data :: chunkData, (_, size) :: chunks => by
    unfold checkUnionChunksM
    exact NoUnsupported.bind (NoUnsupported.ensureElseUb _ _)
      (fun _ => checkUnionChunksM_noUnsupported chunkData chunks)

mutual

/-- **`check_value` with a machine never stops with `Stop.unsupported`**, at every
type and for every value (including values nested in tuples, arrays, and enums). -/
theorem checkValueM_noUnsupported (hderef : DerefNoUnsupported M) (m : Machine M) :
    ∀ (val : Value M) (ty : «Type»), NoUnsupported (checkValueM val ty (some m))
  | val, .Int _ => by
    unfold checkValueM
    cases val <;> first
      | exact NoUnsupported.ensureElseUb _ _
      | exact NoUnsupported.specPanic _
  | val, .Bool => by
    unfold checkValueM
    cases val <;> first
      | exact NoUnsupported.pure _
      | exact NoUnsupported.specPanic _
  | val, .Ptr ptrTy => by
    unfold checkValueM
    cases val with
    | Ptr ptr => exact checkPtrM_noUnsupported hderef m ptr ptrTy
    | _ => exact NoUnsupported.specPanic _
  | val, .Tuple fields _ unsizedField => by
    unfold checkValueM
    cases val with
    | Tuple vals =>
      cases unsizedField with
      | some _ => exact NoUnsupported.specPanic _
      | none =>
        dsimp only
        exact NoUnsupported.bind (NoUnsupported.ensureElseUb _ _)
          (fun _ => checkFieldsM_noUnsupported hderef m vals fields)
    | _ => exact NoUnsupported.specPanic _
  | val, .Array elem count => by
    unfold checkValueM
    cases val with
    | Tuple vals =>
      dsimp only
      exact NoUnsupported.bind (NoUnsupported.ensureElseUb _ _)
        (fun _ => NoUnsupported.forM _
          (fun v => checkValueM_noUnsupported hderef m v elem) vals)
    | _ => exact NoUnsupported.specPanic _
  | val, .Union _ chunks _ _ => by
    unfold checkValueM
    cases val with
    | Union chunkData =>
      dsimp only
      exact NoUnsupported.bind (NoUnsupported.ensureElseUb _ _)
        (fun _ => checkUnionChunksM_noUnsupported chunkData chunks)
    | _ => exact NoUnsupported.specPanic _
  | val, .Enum ⟨variants⟩ _ _ _ _ => by
    unfold checkValueM
    cases val with
    | Variant disc data => exact checkVariantM_noUnsupported hderef m variants disc data
    | _ => exact NoUnsupported.specPanic _
  | val, .Slice _ => by
    unfold checkValueM
    cases val <;> exact NoUnsupported.specPanic _
  | val, .TraitObject _ => by
    unfold checkValueM
    cases val <;> exact NoUnsupported.specPanic _

theorem checkFieldsM_noUnsupported (hderef : DerefNoUnsupported M) (m : Machine M) :
    ∀ (vals : List (Value M)) (fields : List (Offset × «Type»)),
      NoUnsupported (checkFieldsM vals fields (some m))
  | [], _ => by unfold checkFieldsM; exact NoUnsupported.pure _
  | (_ :: _), [] => by unfold checkFieldsM; exact NoUnsupported.pure _
  | val :: vals, (_, ty) :: fields => by
    unfold checkFieldsM
    exact NoUnsupported.bind (checkValueM_noUnsupported hderef m val ty)
      (fun _ => checkFieldsM_noUnsupported hderef m vals fields)

theorem checkVariantM_noUnsupported (hderef : DerefNoUnsupported M) (m : Machine M) :
    ∀ (variants : List (Int × Variant)) (disc : Int) (data : Value M),
      NoUnsupported (checkVariantM variants disc data (some m))
  | [], _, _ => by unfold checkVariantM; exact NoUnsupported.ub _
  | (_, ⟨ty, _⟩) :: rest, disc, data => by
    unfold checkVariantM
    split
    · exact checkValueM_noUnsupported hderef m data ty
    · exact checkVariantM_noUnsupported hderef m rest disc data

end

theorem expect_size_noUnsupported (l : LayoutStrategy) (msg : String) :
    NoUnsupported (LayoutStrategy.expect_size l msg) := by
  unfold LayoutStrategy.expect_size
  cases l <;> first
    | exact NoUnsupported.pure _
    | exact NoUnsupported.specPanic _

/-- **`transmute` with a machine: the validity check contributes no
`Stop.unsupported`.** `Machine::transmute` never stops with `unsupported` whenever its
machine-independent re-encoding (`Type::layout`, `type1.encode`, `type2.decode`) does
not: checking the result at the new type (vtable pointers, trait-object safe
pointers, and safe-pointer dereferenceability included) cannot. -/
theorem transmuteM_noUnsupported (hderef : DerefNoUnsupported M) (m : Machine M)
    (val : Value M) (type1 type2 : «Type»)
    (hl1 : NoUnsupported (Type.layout type1)) (hl2 : NoUnsupported (Type.layout type2))
    (henc : NoUnsupported (Type.encodeM type1 val))
    (hdec : ∀ bytes, NoUnsupported (Type.decodeM (M := M) type2 bytes)) :
    NoUnsupported (transmuteM val type1 type2 (some m)) := by
  unfold transmuteM
  refine NoUnsupported.bind hl1 (fun l1 => ?_)
  refine NoUnsupported.bind (expect_size_noUnsupported _ _) (fun s1 => ?_)
  refine NoUnsupported.bind hl2 (fun l2 => ?_)
  refine NoUnsupported.bind (expect_size_noUnsupported _ _) (fun s2 => ?_)
  split
  · exact NoUnsupported.specPanic _
  · refine NoUnsupported.bind henc (fun bytes => ?_)
    refine NoUnsupported.bind (hdec bytes) (fun o => ?_)
    cases o with
    | none => exact NoUnsupported.ub _
    | some raw =>
      exact NoUnsupported.bind (checkValueM_noUnsupported hderef m raw type2)
        (fun _ => NoUnsupported.pure _)

/-- **`eval_un_op` for `CastOp::Transmute` with a machine: the validity check
contributes no `Stop.unsupported`** (see `transmuteM_noUnsupported`). -/
theorem evalUnOpM_transmute_noUnsupported (hderef : DerefNoUnsupported M) (m : Machine M)
    (newTy oldTy : «Type») (operand : Value M)
    (hl1 : NoUnsupported (Type.layout oldTy)) (hl2 : NoUnsupported (Type.layout newTy))
    (henc : NoUnsupported (Type.encodeM oldTy operand))
    (hdec : ∀ bytes, NoUnsupported (Type.decodeM (M := M) newTy bytes)) :
    NoUnsupported (evalUnOpM (.Cast (.Transmute newTy)) (operand, oldTy) (some m)) := by
  show NoUnsupported (evalCastOpM (.Transmute newTy) (operand, oldTy) (some m))
  unfold evalCastOpM
  dsimp only
  refine NoUnsupported.bind hl1 (fun l1 => ?_)
  refine NoUnsupported.bind (expect_size_noUnsupported _ _) (fun s1 => ?_)
  refine NoUnsupported.bind hl2 (fun l2 => ?_)
  refine NoUnsupported.bind (expect_size_noUnsupported _ _) (fun s2 => ?_)
  split
  · exact NoUnsupported.ub _
  · exact NoUnsupported.bind
      (transmuteM_noUnsupported hderef m operand oldTy newTy hl1 hl2 henc hdec)
      (fun _ => NoUnsupported.pure _)

/-- `Type::layout` of a pointer type never stops with `Stop.unsupported`. -/
theorem layout_ptr_noUnsupported (p : PtrType) : NoUnsupported (Type.layout (.Ptr p)) := by
  unfold Type.layout
  split
  · exact NoUnsupported.pure _
  · exact NoUnsupported.pure _

/-! ### `BasicMemory` and `TreeBorrowsMemory` -/

theorem listIndex_noUnsupported {T : Type} (xs : List T) (i : Int) (what : String) :
    NoUnsupported (listIndex xs i what) := by
  unfold listIndex
  split
  · split
    · exact NoUnsupported.pure _
    · exact NoUnsupported.specPanic _
  · exact NoUnsupported.specPanic _

theorem BasicMemory.check_ptr_noUnsupported {ProvExtra AllocExtra : Type}
    (mem : BasicMemory x86_64 ProvExtra AllocExtra)
    (ptr : ThinPointer (Provenance ProvExtra)) (len : Size) :
    NoUnsupported (BasicMemory.check_ptr mem ptr len) := by
  unfold BasicMemory.check_ptr
  split
  · exact NoUnsupported.pure _
  · split
    · exact NoUnsupported.ub _
    · refine NoUnsupported.bind (listIndex_noUnsupported _ _ _) (fun allocation => ?_)
      split
      · exact NoUnsupported.ub _
      · dsimp only
        split
        · exact NoUnsupported.ub _
        · exact NoUnsupported.pure _

theorem BM.check_ptr_noUnsupported (mem : BM) (ptr : Ptr) (len : Size) :
    NoUnsupported (BM.check_ptr mem ptr len) := by
  unfold BM.check_ptr
  split
  · exact NoUnsupported.pure _
  · split
    · exact NoUnsupported.ub _
    · refine NoUnsupported.bind (listIndex_noUnsupported _ _ _) (fun allocation => ?_)
      split
      · exact NoUnsupported.ub _
      · dsimp only
        split
        · exact NoUnsupported.ub _
        · exact NoUnsupported.pure _

/-- `BasicMemory::dereferenceable` never reports `Stop.unsupported`. -/
theorem derefNoUnsupported_BM : DerefNoUnsupported BM := by
  intro mem ptr len
  show NoUnsupported (BM.dereferenceable mem ptr len)
  unfold BM.dereferenceable
  exact NoUnsupported.bind (BM.check_ptr_noUnsupported mem ptr len) (fun _ => NoUnsupported.pure _)

/-- `TreeBorrowsMemory::dereferenceable` never reports `Stop.unsupported`. -/
theorem derefNoUnsupported_TBM : DerefNoUnsupported TBM := by
  intro mem ptr len
  show NoUnsupported (TreeBorrowsMemory.dereferenceable mem ptr len)
  unfold TreeBorrowsMemory.dereferenceable
  exact NoUnsupported.bind (BasicMemory.check_ptr_noUnsupported mem.mem ptr len)
    (fun _ => NoUnsupported.pure _)


end Polymorphic

/-! ## `MachTB`: the statements above at `TreeBorrowsMemory`

Every theorem of the previous sections holds for `MachTB = Machine TBM` by
instantiating `M := TBM`; the `Stop.unsupported`-freedom statements are recorded
here because they discharge `DerefNoUnsupported TBM`. -/

/-- `check_ptr` on a Tree Borrows machine never stops with `Stop.unsupported`. -/
theorem checkPtrTB_noUnsupported (mt : MachTB) (ptr : Pointer TreeBorrowsProvenance)
    (ptrTy : PtrType) : NoUnsupported (checkPtrM ptr ptrTy (some mt)) :=
  checkPtrM_noUnsupported derefNoUnsupported_TBM mt ptr ptrTy

/-- `check_value` on a Tree Borrows machine never stops with `Stop.unsupported`. -/
theorem checkValueTB_noUnsupported (mt : MachTB) (val : Value TBM) (ty : «Type») :
    NoUnsupported (checkValueM val ty (some mt)) :=
  checkValueM_noUnsupported derefNoUnsupported_TBM mt val ty

/-- `check_value` on the polymorphic machine at `BasicMemory` never stops with
`Stop.unsupported` (`checkValue_noUnsupported` in `Correspondence.WideSliceDst`
transfers it to `checkValue` on `Mach`). -/
theorem checkValueBM_noUnsupported (m : Mach) (val : Val) (ty : «Type») :
    NoUnsupported (checkValueM (M := BM) val ty (some m)) :=
  checkValueM_noUnsupported derefNoUnsupported_BM m val ty

/-- `CastOp::Transmute` on a Tree Borrows machine never stops with
`Stop.unsupported` when its machine-independent re-encoding does not. -/
theorem evalUnOpTB_transmute_noUnsupported (mt : MachTB) (newTy oldTy : «Type»)
    (operand : Value TBM)
    (hl1 : NoUnsupported (Type.layout oldTy)) (hl2 : NoUnsupported (Type.layout newTy))
    (henc : NoUnsupported (Type.encodeM oldTy operand))
    (hdec : ∀ bytes, NoUnsupported (Type.decodeM (M := TBM) newTy bytes)) :
    NoUnsupported (evalUnOpM (.Cast (.Transmute newTy)) (operand, oldTy) (some mt)) :=
  evalUnOpM_transmute_noUnsupported derefNoUnsupported_TBM mt newTy oldTy operand
    hl1 hl2 henc hdec

/-! ## `Mach`: the `BasicMemory` transcription is the polymorphic one -/

/-- `vtableFromPtr` is `vtableFromPtrM` at `BasicMemory`. -/
theorem vtableFromPtr_eq_vtableFromPtrM (m : Mach) :
    vtableFromPtr m = vtableFromPtrM (M := BM) m := by
  funext (ptr : Ptr)
  unfold vtableFromPtrM vtableFromPtr
  conv =>
    rhs
    rw [find?_congr (q := fun e : VTableName × Ptr => decide (e.2 = ptr))
      (by intro ⟨_, vp⟩; exact congrArg (@decide (vp = ptr)) (Subsingleton.elim _ _))]
  conv =>
    lhs
    rw [find?_congr (q := fun e : VTableName × Ptr => decide (e.2 = ptr))
      (by intro ⟨_, vp⟩; rfl)]
  rcases m.vtable_ptrs.entries.find? (fun e : VTableName × Ptr => decide (e.2 = ptr)) with
    _ | ⟨_, _⟩ <;> rfl

private theorem vtableLookup_eq_vtableLookupM (m : Mach) :
    vtableLookup m = vtableLookupM (M := BM) m := by
  funext (ptr : Ptr)
  unfold vtableLookupM vtableLookup
  conv =>
    rhs
    rw [find?_congr (q := fun e : VTableName × Ptr => decide (e.2 = ptr))
      (by intro ⟨_, vp⟩; exact congrArg (@decide (vp = ptr)) (Subsingleton.elim _ _))]
  conv =>
    lhs
    rw [find?_congr (q := fun e : VTableName × Ptr => decide (e.2 = ptr))
      (by intro ⟨_, vp⟩; rfl)]
  rcases m.vtable_ptrs.entries.find? (fun e : VTableName × Ptr => decide (e.2 = ptr)) with
    _ | ⟨_, _⟩ <;> rfl

/-- `checkPtrMetadata` is `checkPtrMetadataM` at `BasicMemory`, with or without a machine. -/
theorem checkPtrMetadata_eq_checkPtrMetadataM (pm : Option (PointerMeta Prov))
    (kind : PointerMetaKind) (mo : Option Mach) :
    checkPtrMetadata pm kind mo = checkPtrMetadataM (M := BM) pm kind mo := by
  unfold checkPtrMetadataM checkPtrMetadata
  rcases pm with _ | (_ | vp) <;> cases kind <;> try rfl
  cases mo with
  | none => rfl
  | some mach => dsimp only; rw [vtableFromPtr_eq_vtableFromPtrM]

/-- `checkPtr` is `checkPtrM` at `BasicMemory`, with or without a machine: every
statement about `checkPtrM` above holds for `Mach`. -/
theorem checkPtr_eq_checkPtrM (ptr : Pointer Prov) (ptrTy : PtrType) (mo : Option Mach) :
    checkPtr ptr ptrTy mo = checkPtrM (M := BM) ptr ptrTy mo := by
  unfold checkPtrM checkPtr
  refine bindCongr rfl (fun _ => ?_)
  refine bindCongr (checkPtrMetadata_eq_checkPtrMetadataM _ _ _) (fun _ => ?_)
  cases PtrType.safe_pointee ptrTy with
  | none =>
    cases ptrTy <;> try rfl
    cases mo with
    | none => rfl
    | some mach => dsimp only; rw [vtableFromPtr_eq_vtableFromPtrM]
  | some pointee =>
    dsimp only
    refine bindCongr ?_ (fun ⟨size, align⟩ => ?_)
    · cases mo with
      | none => rfl
      | some mach => dsimp only; rw [vtableLookup_eq_vtableLookupM]
    · dsimp only
      refine bindCongr rfl (fun _ => ?_)
      refine bindCongr rfl (fun _ => ?_)
      refine bindCongr rfl (fun _ => ?_)
      refine bindCongr rfl (fun _ => ?_)
      cases mo with
      | none =>
        dsimp only
        split
        · rfl
        · cases ptr.thin_pointer.provenance <;> rfl
      | some mach => rfl

/-- `vtable_from_ptr` on `Mach` succeeds exactly on registered pointers with a vtable. -/
theorem vtableFromPtr_eq_ok_iff (m : Mach) (ptr : Ptr) (vtable : VTable) :
    vtableFromPtr m ptr = .ok vtable ↔
      ∃ name, FirstVTableName m.vtable_ptrs.entries ptr name ∧
        mapGet m.prog.vtables name = some vtable := by
  rw [vtableFromPtr_eq_vtableFromPtrM]
  exact vtableFromPtrM_eq_ok_iff (M := BM) m ptr vtable

/-- `vtable_from_ptr` on `Mach` is UB exactly on unregistered pointers. -/
theorem vtableFromPtr_eq_ub_iff (m : Mach) (ptr : Ptr) (msg : String) :
    vtableFromPtr m ptr = .error (.ub msg) ↔
      msg = "invalid pointer for vtable lookup" ∧ ∀ e ∈ m.vtable_ptrs.entries, e.2 ≠ ptr := by
  rw [vtableFromPtr_eq_vtableFromPtrM]
  exact vtableFromPtrM_eq_ub_iff (M := BM) m ptr msg

/-- `vtable_from_ptr` on `Mach` never stops with `Stop.unsupported`. -/
theorem vtableFromPtr_noUnsupported (m : Mach) (ptr : Ptr) :
    NoUnsupported (vtableFromPtr m ptr) := by
  rw [vtableFromPtr_eq_vtableFromPtrM]
  exact vtableFromPtrM_noUnsupported (M := BM) m ptr

/-- On `Mach`, the inlined vtable-metadata check is the spec's recursive call
`self.check_ptr(ptr.widen(None), PtrType::VTablePtr(trait_name))`. -/
theorem checkPtrMetadata_vtablePointer_eq_checkPtr (m : Mach) (vp : Ptr)
    (traitName : TraitName) :
    checkPtrMetadata (some (.VTablePointer vp)) (.VTablePointer traitName) (some m) =
      checkPtr (ThinPointer.widen vp none) (.VTablePtr traitName) (some m) := by
  rw [checkPtrMetadata_eq_checkPtrMetadataM, checkPtr_eq_checkPtrM]
  exact checkPtrMetadataM_vtablePointer_eq_checkPtrM (M := BM) m vp traitName

/-- `check_ptr` on `Mach` accepts a stand-alone vtable pointer exactly when its
address fits a `usize`, it carries no metadata, and it is one of the machine's
vtable pointers, for a vtable of trait `traitName`. -/
theorem checkPtr_vtablePtr_eq_ok_iff (m : Mach) (ptr : Pointer Prov) (traitName : TraitName) :
    checkPtr ptr (.VTablePtr traitName) (some m) = .ok () ↔
      inBounds ptr.thin_pointer.addr .Unsigned x86_64.PTR_SIZE = true ∧
      ptr.metadata = none ∧
      ∃ vtable, vtableFromPtr m ptr.thin_pointer = .ok vtable ∧
        vtable.trait_name = traitName := by
  rw [checkPtr_eq_checkPtrM, vtableFromPtr_eq_vtableFromPtrM]
  exact checkPtrM_vtablePtr_eq_ok_iff (M := BM) m ptr traitName

/-- UB outcomes of `check_ptr` on `Mach` at a stand-alone vtable pointer: an
out-of-bounds address, metadata, an unregistered pointer, and a vtable of another
trait, each with the spec's message. -/
theorem checkPtr_vtablePtr_ub (m : Mach) (tp : Ptr) (traitName : TraitName) :
    (inBounds tp.addr .Unsigned x86_64.PTR_SIZE = false →
      ∀ md, checkPtr ⟨tp, md⟩ (.VTablePtr traitName) (some m) =
        .error (.ub "Value::Ptr: pointer out-of-bounds")) ∧
    (inBounds tp.addr .Unsigned x86_64.PTR_SIZE = true →
      (∀ md, checkPtr ⟨tp, some md⟩ (.VTablePtr traitName) (some m) =
        .error (.ub "Value::Ptr: invalid metadata")) ∧
      ((∀ e ∈ m.vtable_ptrs.entries, e.2 ≠ tp) →
        checkPtr ⟨tp, none⟩ (.VTablePtr traitName) (some m) =
          .error (.ub "invalid pointer for vtable lookup")) ∧
      (∀ vtable, vtableFromPtr m tp = .ok vtable → vtable.trait_name ≠ traitName →
        checkPtr ⟨tp, none⟩ (.VTablePtr traitName) (some m) =
          .error (.ub "Value::Ptr: invalid vtable in metadata"))) := by
  refine ⟨fun hoob md => ?_, fun hin => ⟨fun md => ?_, fun hunreg => ?_, fun vtable hv hne => ?_⟩⟩
  · rw [checkPtr_eq_checkPtrM]; exact checkPtrM_oob_ub (M := BM) _ _ _ hoob
  · rw [checkPtr_eq_checkPtrM]
    exact checkPtrM_vtablePtr_metadata_ub (M := BM) m tp md traitName hin
  · rw [checkPtr_eq_checkPtrM]
    exact checkPtrM_vtablePtr_unregistered_ub (M := BM) m tp traitName hin hunreg
  · rw [checkPtr_eq_checkPtrM]
    rw [vtableFromPtr_eq_vtableFromPtrM] at hv
    exact checkPtrM_vtablePtr_wrong_trait_ub (M := BM) m tp traitName vtable hin hv hne

/-- `check_ptr` on `Mach` accepts `&dyn Trait` / `Box<dyn Trait>` exactly when the
address fits a `usize`, the metadata is a registered in-bounds vtable pointer for
`traitName`, the vtable's dynamic size fits `isize::MAX`, the address is non-null
and aligned to the vtable's alignment, the pointee is inhabited, and the memory is
dereferenceable for the vtable's size. -/
theorem checkPtr_traitObject_eq_ok_iff (m : Mach) (ptr : Pointer Prov) (ptrTy : PtrType)
    (pointee : PointeeInfo) (traitName : TraitName)
    (hsafe : PtrType.safe_pointee ptrTy = some pointee)
    (hlay : pointee.layout = .TraitObject traitName) :
    checkPtr ptr ptrTy (some m) = .ok () ↔
      inBounds ptr.thin_pointer.addr .Unsigned x86_64.PTR_SIZE = true ∧
      ∃ vp vtable, ptr.metadata = some (.VTablePointer vp) ∧
        inBounds vp.addr .Unsigned x86_64.PTR_SIZE = true ∧
        vtableFromPtr m vp = .ok vtable ∧ vtable.trait_name = traitName ∧
        inBounds vtable.size.bytes .Signed x86_64.PTR_SIZE = true ∧
        ptr.thin_pointer.addr ≠ 0 ∧
        Align.is_aligned vtable.align ptr.thin_pointer.addr = true ∧
        pointee.inhabited = true ∧
        CM.dereferenceable m.mem ptr.thin_pointer vtable.size = .ok () := by
  rw [checkPtr_eq_checkPtrM, vtableFromPtr_eq_vtableFromPtrM]
  exact checkPtrM_traitObject_eq_ok_iff (M := BM) m ptr ptrTy pointee traitName hsafe hlay

/-- `check_ptr` on `Mach` with a machine never stops with `Stop.unsupported`. -/
theorem checkPtr_noUnsupported (m : Mach) (ptr : Pointer Prov) (ptrTy : PtrType) :
    NoUnsupported (checkPtr ptr ptrTy (some m)) := by
  rw [checkPtr_eq_checkPtrM]
  exact checkPtrM_noUnsupported derefNoUnsupported_BM m ptr ptrTy

/-! ## `Mach` ↔ `MachTB` agreement -/

/-- The `BasicMemory` thin pointer that a Tree Borrows thin pointer denotes: the same
address and allocation, with the borrow-tree path forgotten. -/
def erasePath (ptr : ThinPointer TreeBorrowsProvenance) : Ptr :=
  { addr := ptr.addr, provenance := ptr.provenance.map (fun p => (p.1, ())) }

/-- `erasePath` on (possibly wide) pointers, including vtable-pointer metadata. -/
def erasePathPtr (ptr : Pointer TreeBorrowsProvenance) : Pointer Prov :=
  { thin_pointer := erasePath ptr.thin_pointer,
    metadata :=
      match ptr.metadata with
      | none => none
      | some (.ElementCount n) => some (.ElementCount n)
      | some (.VTablePointer vp) => some (.VTablePointer (erasePath vp)) }

/-- A `Mach` and a `MachTB` agree on vtables: they run the same vtables, and the
`Mach` vtable-pointer table is the `MachTB` one with borrow-tree paths forgotten. -/
structure VTablesAgree (m : Mach) (mt : MachTB) : Prop where
  vtables : m.prog.vtables = mt.prog.vtables
  ptrs : m.vtable_ptrs.entries = mt.vtable_ptrs.entries.map (fun e => (e.1, erasePath e.2))

/-- Forgetting paths does not confuse `ptr` with a registered vtable pointer: every
registered pointer with the same address and allocation is `ptr` itself. (A pointer
to a vtable allocation with a non-root path violates this, and the two machines
then disagree, `vtablePtr_child_path_divergence`.) -/
def PathFaithful (mt : MachTB) (ptr : ThinPointer TreeBorrowsProvenance) : Prop :=
  ∀ e ∈ mt.vtable_ptrs.entries, erasePath e.2 = erasePath ptr → e.2 = ptr

private theorem unregistered_agree (m : Mach) (mt : MachTB) (h : VTablesAgree m mt)
    (ptr : ThinPointer TreeBorrowsProvenance) (hf : PathFaithful mt ptr)
    (hunreg : ∀ e ∈ mt.vtable_ptrs.entries, e.2 ≠ ptr) :
    ∀ e' ∈ m.vtable_ptrs.entries, e'.2 ≠ erasePath ptr := by
  intro e' he' heq
  rw [h.ptrs, List.mem_map] at he'
  rcases he' with ⟨e, he, rfl⟩
  exact hunreg e he (hf e he heq)

private theorem first_agree (m : Mach) (mt : MachTB) (h : VTablesAgree m mt)
    (ptr : ThinPointer TreeBorrowsProvenance) (hf : PathFaithful mt ptr) (name : VTableName)
    (hfirst : FirstVTableName mt.vtable_ptrs.entries ptr name) :
    FirstVTableName m.vtable_ptrs.entries (erasePath ptr) name := by
  rcases hfirst with ⟨pre, post, hsplit, hpre⟩
  refine ⟨pre.map (fun e => (e.1, erasePath e.2)), post.map (fun e => (e.1, erasePath e.2)),
    ?_, ?_⟩
  · rw [h.ptrs, hsplit, List.map_append, List.map_cons]
  · intro e' he' heq
    rw [List.mem_map] at he'
    rcases he' with ⟨e, he, rfl⟩
    have hmem : e ∈ mt.vtable_ptrs.entries := by
      rw [hsplit]; exact List.mem_append_left _ he
    exact hpre e he (hf e hmem heq)

/-- **`Mach` and `MachTB` look up the same vtable.** For machines that agree on
vtables and a path-faithful pointer, `vtable_from_ptr` returns the same vtable, the
same UB, or the same spec panic on both machines. -/
theorem vtableFromPtr_agree (m : Mach) (mt : MachTB) (h : VTablesAgree m mt)
    (ptr : ThinPointer TreeBorrowsProvenance) (hf : PathFaithful mt ptr) :
    vtableFromPtr m (erasePath ptr) = vtableFromPtrM mt ptr := by
  rw [vtableFromPtr_eq_vtableFromPtrM]
  by_cases hunreg : ∀ e ∈ mt.vtable_ptrs.entries, e.2 ≠ ptr
  · rw [vtableFromPtrM_unregistered_ub mt ptr hunreg]
    exact vtableFromPtrM_unregistered_ub (M := BM) m (erasePath ptr)
      (unregistered_agree m mt h ptr hf hunreg)
  · rcases exists_first_of_registered _ _ hunreg with ⟨name, hfirst⟩
    rw [vtableFromPtrM_eq_of_first mt ptr name hfirst,
      vtableFromPtrM_eq_of_first (M := BM) m (erasePath ptr) name
        (first_agree m mt h ptr hf name hfirst), h.vtables]

private theorem vtableLookup_agree (m : Mach) (mt : MachTB) (h : VTablesAgree m mt)
    (ptr : ThinPointer TreeBorrowsProvenance) (hf : PathFaithful mt ptr) :
    vtableLookupM (M := BM) m (erasePath ptr) = vtableLookupM mt ptr := by
  by_cases hunreg : ∀ e ∈ mt.vtable_ptrs.entries, e.2 ≠ ptr
  · rw [vtableLookupM_eq, vtableLookupM_eq, (find?_vtable_eq_none_iff _ _).2 hunreg,
      (find?_vtable_eq_none_iff _ _).2 (unregistered_agree m mt h ptr hf hunreg)]
  · rcases exists_first_of_registered _ _ hunreg with ⟨name, hfirst⟩
    rw [vtableLookupM_eq, vtableLookupM_eq, find?_of_first _ _ _ hfirst,
      find?_of_first _ _ _ (first_agree m mt h ptr hf name hfirst), h.vtables]

/-- **`Mach` and `MachTB` decide stand-alone vtable pointers identically**: for
machines that agree on vtables and a path-faithful pointer, `check_ptr` at
`PtrType::VTablePtr(trait_name)` has the same outcome (`ok` or the same UB). -/
theorem checkPtr_vtablePtr_agree (m : Mach) (mt : MachTB) (h : VTablesAgree m mt)
    (ptr : Pointer TreeBorrowsProvenance) (traitName : TraitName)
    (hf : PathFaithful mt ptr.thin_pointer) :
    checkPtr (erasePathPtr ptr) (.VTablePtr traitName) (some m) =
      checkPtrM ptr (.VTablePtr traitName) (some mt) := by
  rw [checkPtr_eq_checkPtrM]
  rcases ptr with ⟨tp, md⟩
  cases hin : inBounds tp.addr .Unsigned x86_64.PTR_SIZE with
  | false =>
    rw [checkPtrM_oob_ub (some mt) ⟨tp, md⟩ _ hin]
    exact checkPtrM_oob_ub (M := BM) (some m) (erasePathPtr ⟨tp, md⟩) _ hin
  | true =>
    cases md with
    | some md =>
      rw [checkPtrM_vtablePtr_metadata_ub mt tp md traitName hin]
      cases md with
      | ElementCount n =>
        exact checkPtrM_vtablePtr_metadata_ub (M := BM) m (erasePath tp) (.ElementCount n)
          traitName hin
      | VTablePointer vp =>
        exact checkPtrM_vtablePtr_metadata_ub (M := BM) m (erasePath tp)
          (.VTablePointer (erasePath vp)) traitName hin
    | none =>
      have h3 : vtableFromPtrM (M := BM) m (erasePath tp) = vtableFromPtrM mt tp := by
        rw [← vtableFromPtr_eq_vtableFromPtrM]
        exact vtableFromPtr_agree m mt h tp hf
      show checkPtrM (M := BM) ⟨erasePath tp, none⟩ (.VTablePtr traitName) (some m) = _
      rw [checkPtrM_vtablePtr_thin_eq (M := BM) m (erasePath tp) traitName hin,
        checkPtrM_vtablePtr_thin_eq mt tp traitName hin, h3]

/-- **`Mach` and `MachTB` decide `&dyn Trait` / `Box<dyn Trait>` identically**: for
machines that agree on vtables, a path-faithful vtable pointer in the metadata, and
memories that agree on the dereferenceability of the data pointer, `check_ptr` at a
trait-object safe pointer has the same outcome on both machines. -/
theorem checkPtr_traitObject_agree (m : Mach) (mt : MachTB) (h : VTablesAgree m mt)
    (ptr : Pointer TreeBorrowsProvenance) (ptrTy : PtrType) (pointee : PointeeInfo)
    (traitName : TraitName)
    (hsafe : PtrType.safe_pointee ptrTy = some pointee)
    (hlay : pointee.layout = .TraitObject traitName)
    (hf : ∀ vp, ptr.metadata = some (.VTablePointer vp) → PathFaithful mt vp)
    (hderef : ∀ size, CM.dereferenceable m.mem (erasePath ptr.thin_pointer) size =
      ConcurrentMemory.dereferenceable mt.mem ptr.thin_pointer size) :
    checkPtr (erasePathPtr ptr) ptrTy (some m) = checkPtrM ptr ptrTy (some mt) := by
  rw [checkPtr_eq_checkPtrM]
  rcases ptr with ⟨tp, md⟩
  cases hin : inBounds tp.addr .Unsigned x86_64.PTR_SIZE with
  | false =>
    rw [checkPtrM_oob_ub (some mt) ⟨tp, md⟩ _ hin]
    exact checkPtrM_oob_ub (M := BM) (some m) (erasePathPtr ⟨tp, md⟩) _ hin
  | true =>
    have hbadT := checkPtrM_traitObject_bad_metadata_ub mt tp ptrTy pointee traitName
      hsafe hlay hin
    have hbadB := checkPtrM_traitObject_bad_metadata_ub (M := BM) m (erasePath tp) ptrTy
      pointee traitName hsafe hlay hin
    rcases md with _ | (n | vp)
    · rw [hbadT.1]; exact hbadB.1
    · rw [hbadT.2 n]; exact hbadB.2 n
    · have hmeta : checkPtrM (M := BM) ⟨erasePath vp, none⟩ (.VTablePtr traitName) (some m) =
          checkPtrM ⟨vp, none⟩ (.VTablePtr traitName) (some mt) := by
        have hagree := checkPtr_vtablePtr_agree m mt h ⟨vp, none⟩ traitName (hf vp rfl)
        rw [checkPtr_eq_checkPtrM] at hagree
        exact hagree
      show checkPtrM (M := BM) ⟨erasePath tp, some (.VTablePointer (erasePath vp))⟩ ptrTy
        (some m) = _
      rw [checkPtrM_traitObject_eq (M := BM) m (erasePath tp) (erasePath vp) ptrTy pointee
          traitName hsafe hlay hin,
        checkPtrM_traitObject_eq mt tp vp ptrTy pointee traitName hsafe hlay hin, hmeta,
        vtableLookup_agree m mt h vp (hf vp rfl)]
      refine bindCongr rfl (fun _ => ?_)
      refine bindCongr rfl (fun vtable => ?_)
      unfold safePtrTail
      refine bindCongr rfl (fun _ => ?_)
      refine bindCongr rfl (fun _ => ?_)
      refine bindCongr rfl (fun _ => ?_)
      refine bindCongr rfl (fun _ => ?_)
      exact congrArg derefStep (hderef vtable.size)

/-! ## Concrete witnesses on `Mach` and `MachTB`

Two machines with the same program: vtables `vtableA` (trait `traitA`, size 4, align
4) and `vtableB` (trait `traitB`, size 8, align 8), registered at addresses `4096` and
`8192`, a third pointer registered under a name without a vtable (`12288`), a live
8-byte allocation at address `64`, and a dead one at address `128`. -/

def traitA : TraitName := ⟨⟨0⟩⟩
def traitB : TraitName := ⟨⟨1⟩⟩
def vtNameA : VTableName := ⟨⟨0⟩⟩
def vtNameB : VTableName := ⟨⟨1⟩⟩
def vtNameMissing : VTableName := ⟨⟨2⟩⟩

def vtableA : VTable :=
  { trait_name := traitA, size := ⟨4⟩, align := ⟨4⟩, cells := [], methods := ⟨[]⟩ }

def vtableB : VTable :=
  { trait_name := traitB, size := ⟨8⟩, align := ⟨8⟩, cells := [], methods := ⟨[]⟩ }

def vtProg : Program :=
  { functions := ⟨[]⟩, start := ⟨⟨0⟩⟩, globals := ⟨[]⟩, traits := ⟨[]⟩,
    vtables := ⟨[(vtNameA, vtableA), (vtNameB, vtableB)]⟩ }

/-- The `Mach` vtable pointers of `vtableA`, `vtableB`, and the name without a vtable. -/
def vtPtrA : Ptr := { addr := 4096, provenance := some (⟨7⟩, ()) }
def vtPtrB : Ptr := { addr := 8192, provenance := some (⟨8⟩, ()) }
def vtPtrMissing : Ptr := { addr := 12288, provenance := some (⟨9⟩, ()) }

/-- The `MachTB` vtable pointers (root paths). -/
def vtPtrATB : ThinPointer TreeBorrowsProvenance := { addr := 4096, provenance := some (⟨7⟩, []) }
def vtPtrBTB : ThinPointer TreeBorrowsProvenance := { addr := 8192, provenance := some (⟨8⟩, []) }
def vtPtrMissingTB : ThinPointer TreeBorrowsProvenance :=
  { addr := 12288, provenance := some (⟨9⟩, []) }

/-- The `BasicMemory` allocations: 8 live bytes at address 64 and a dead allocation at 128. -/
def vtAllocs : List (Allocation Unit Unit) :=
  [{ data := List.replicate 8 .Uninit, addr := 64, align := ⟨8⟩, kind := .Stack,
     live := true, extra := () },
   { data := List.replicate 8 .Uninit, addr := 128, align := ⟨8⟩, kind := .Stack,
     live := false, extra := () }]

/-- The same allocations for `TreeBorrowsMemory` (each with a trivial borrow tree). -/
def vtAllocsTB : List (Allocation Path TreeBorrowsAllocationExtra) :=
  [{ data := List.replicate 8 .Uninit, addr := 64, align := ⟨8⟩, kind := .Stack,
     live := true, extra := { root := ⟨[], [], .No⟩ } },
   { data := List.replicate 8 .Uninit, addr := 128, align := ⟨8⟩, kind := .Stack,
     live := false, extra := { root := ⟨[], [], .No⟩ } }]

def vtMach : Mach :=
  { prog := vtProg,
    mem := { memory := { allocations := vtAllocs, _phantom := {} }, accesses := [] },
    intptrcast := ⟨⟨[]⟩⟩, threads := [], active_thread := 0, synchronized_threads := ⟨[]⟩,
    locks := [], global_ptrs := ⟨[]⟩, fn_ptrs := ⟨[]⟩,
    vtable_ptrs := ⟨[(vtNameA, vtPtrA), (vtNameB, vtPtrB), (vtNameMissing, vtPtrMissing)]⟩,
    stdout := ⟨[]⟩, stderr := ⟨[]⟩ }

def vtMachTB : MachTB :=
  { prog := vtProg,
    mem := { memory := { params := ⟨false⟩, mem := { allocations := vtAllocsTB, _phantom := {} } },
             accesses := [] },
    intptrcast := ⟨⟨[]⟩⟩, threads := [], active_thread := 0, synchronized_threads := ⟨[]⟩,
    locks := [], global_ptrs := ⟨[]⟩, fn_ptrs := ⟨[]⟩,
    vtable_ptrs := ⟨[(vtNameA, vtPtrATB), (vtNameB, vtPtrBTB), (vtNameMissing, vtPtrMissingTB)]⟩,
    stdout := ⟨[]⟩, stderr := ⟨[]⟩ }

/-- `&dyn TraitA` (`PtrType::Ref` to a trait object of `traitA`). -/
def dynRefA : PtrType :=
  .Ref .Immutable { layout := .TraitObject traitA, inhabited := true,
                    unsafe_cells := .TraitObject, freeze := true, unpin := true }

/-- `Box<dyn TraitA>`. -/
def dynBoxA : PtrType :=
  .Box { layout := .TraitObject traitA, inhabited := true,
         unsafe_cells := .TraitObject, freeze := true, unpin := true }

/-- `&dyn TraitA` whose pointee is uninhabited. -/
def dynRefAUninhabited : PtrType :=
  .Ref .Immutable { layout := .TraitObject traitA, inhabited := false,
                    unsafe_cells := .TraitObject, freeze := true, unpin := true }

/-- Data pointers into the live allocation (`Mach` / `MachTB`), at a given address. -/
def dataPtr (addr : Int) : Ptr := { addr := addr, provenance := some (⟨0⟩, ()) }
def dataPtrTB (addr : Int) : ThinPointer TreeBorrowsProvenance :=
  { addr := addr, provenance := some (⟨0⟩, []) }

/-- `vtable_from_ptr` on both machines: a registered pointer returns its vtable, an
unregistered pointer (here a data pointer and a provenance-free address) is UB, and
a registered name without a vtable is a spec panic. -/
theorem vtableFromPtr_witness :
    vtableFromPtr vtMach vtPtrA = .ok vtableA ∧
    vtableFromPtrM vtMachTB vtPtrATB = .ok vtableA ∧
    vtableFromPtr vtMach vtPtrB = .ok vtableB ∧
    vtableFromPtrM vtMachTB vtPtrBTB = .ok vtableB ∧
    vtableFromPtr vtMach (dataPtr 64) = .error (.ub "invalid pointer for vtable lookup") ∧
    vtableFromPtrM vtMachTB (dataPtrTB 64) =
      .error (.ub "invalid pointer for vtable lookup") ∧
    vtableFromPtr vtMach { addr := 4096, provenance := none } =
      .error (.ub "invalid pointer for vtable lookup") ∧
    vtableFromPtrM vtMachTB { addr := 4096, provenance := none } =
      .error (.ub "invalid pointer for vtable lookup") ∧
    (∃ msg, vtableFromPtr vtMach vtPtrMissing = .error (.specPanic msg)) ∧
    (∃ msg, vtableFromPtrM vtMachTB vtPtrMissingTB = .error (.specPanic msg)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-- `check_ptr` at `PtrType::VTablePtr` on both machines: `ok` for the registered
pointer of the named trait, and UB for an out-of-bounds address, metadata, an
unregistered pointer, and the vtable of another trait. -/
theorem checkPtr_vtablePtr_witness :
    -- ok
    checkPtr ⟨vtPtrA, none⟩ (.VTablePtr traitA) (some vtMach) = .ok () ∧
    checkPtrM ⟨vtPtrATB, none⟩ (.VTablePtr traitA) (some vtMachTB) = .ok () ∧
    -- out-of-bounds address (`2^64`)
    checkPtr ⟨{ vtPtrA with addr := 18446744073709551616 }, none⟩ (.VTablePtr traitA)
      (some vtMach) = .error (.ub "Value::Ptr: pointer out-of-bounds") ∧
    checkPtrM ⟨{ vtPtrATB with addr := 18446744073709551616 }, none⟩ (.VTablePtr traitA)
      (some vtMachTB) = .error (.ub "Value::Ptr: pointer out-of-bounds") ∧
    -- metadata on a stand-alone vtable pointer
    checkPtr ⟨vtPtrA, some (.ElementCount 1)⟩ (.VTablePtr traitA) (some vtMach) =
      .error (.ub "Value::Ptr: invalid metadata") ∧
    checkPtrM ⟨vtPtrATB, some (.VTablePointer vtPtrATB)⟩ (.VTablePtr traitA) (some vtMachTB) =
      .error (.ub "Value::Ptr: invalid metadata") ∧
    -- unregistered pointer
    checkPtr ⟨dataPtr 64, none⟩ (.VTablePtr traitA) (some vtMach) =
      .error (.ub "invalid pointer for vtable lookup") ∧
    checkPtrM ⟨dataPtrTB 64, none⟩ (.VTablePtr traitA) (some vtMachTB) =
      .error (.ub "invalid pointer for vtable lookup") ∧
    -- vtable of another trait
    checkPtr ⟨vtPtrB, none⟩ (.VTablePtr traitA) (some vtMach) =
      .error (.ub "Value::Ptr: invalid vtable in metadata") ∧
    checkPtrM ⟨vtPtrBTB, none⟩ (.VTablePtr traitA) (some vtMachTB) =
      .error (.ub "Value::Ptr: invalid vtable in metadata") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `check_ptr` at `&dyn TraitA` / `Box<dyn TraitA>` on both machines: `ok` for an
aligned, non-null, dereferenceable data pointer with the vtable pointer of `traitA`,
and one UB outcome per violated requirement. -/
theorem checkPtr_dynRef_witness :
    -- ok: `&dyn TraitA` and `Box<dyn TraitA>` at address 64 (4 bytes, align 4)
    checkPtr ⟨dataPtr 64, some (.VTablePointer vtPtrA)⟩ dynRefA (some vtMach) = .ok () ∧
    checkPtrM ⟨dataPtrTB 64, some (.VTablePointer vtPtrATB)⟩ dynRefA (some vtMachTB) = .ok () ∧
    checkPtr ⟨dataPtr 68, some (.VTablePointer vtPtrA)⟩ dynBoxA (some vtMach) = .ok () ∧
    checkPtrM ⟨dataPtrTB 68, some (.VTablePointer vtPtrATB)⟩ dynBoxA (some vtMachTB) = .ok () ∧
    -- thin pointer / slice metadata
    checkPtr ⟨dataPtr 64, none⟩ dynRefA (some vtMach) =
      .error (.ub "Value::Ptr: invalid metadata") ∧
    checkPtrM ⟨dataPtrTB 64, some (.ElementCount 1)⟩ dynRefA (some vtMachTB) =
      .error (.ub "Value::Ptr: invalid metadata") ∧
    -- unregistered vtable pointer in the metadata
    checkPtr ⟨dataPtr 64, some (.VTablePointer (dataPtr 64))⟩ dynRefA (some vtMach) =
      .error (.ub "invalid pointer for vtable lookup") ∧
    checkPtrM ⟨dataPtrTB 64, some (.VTablePointer (dataPtrTB 64))⟩ dynRefA (some vtMachTB) =
      .error (.ub "invalid pointer for vtable lookup") ∧
    -- vtable of another trait in the metadata
    checkPtr ⟨dataPtr 64, some (.VTablePointer vtPtrB)⟩ dynRefA (some vtMach) =
      .error (.ub "Value::Ptr: invalid vtable in metadata") ∧
    checkPtrM ⟨dataPtrTB 64, some (.VTablePointer vtPtrBTB)⟩ dynRefA (some vtMachTB) =
      .error (.ub "Value::Ptr: invalid vtable in metadata") ∧
    -- null
    checkPtr ⟨{ addr := 0, provenance := none }, some (.VTablePointer vtPtrA)⟩ dynRefA
      (some vtMach) = .error (.ub "Value::Ptr: null safe pointer") ∧
    checkPtrM ⟨{ addr := 0, provenance := none }, some (.VTablePointer vtPtrATB)⟩ dynRefA
      (some vtMachTB) = .error (.ub "Value::Ptr: null safe pointer") ∧
    -- unaligned (address 66, vtable alignment 4)
    checkPtr ⟨dataPtr 66, some (.VTablePointer vtPtrA)⟩ dynRefA (some vtMach) =
      .error (.ub "Value::Ptr: unaligned safe pointer") ∧
    checkPtrM ⟨dataPtrTB 66, some (.VTablePointer vtPtrATB)⟩ dynRefA (some vtMachTB) =
      .error (.ub "Value::Ptr: unaligned safe pointer") ∧
    -- uninhabited pointee
    checkPtr ⟨dataPtr 64, some (.VTablePointer vtPtrA)⟩ dynRefAUninhabited (some vtMach) =
      .error (.ub "Value::Ptr: safe pointer to uninhabited type") ∧
    checkPtrM ⟨dataPtrTB 64, some (.VTablePointer vtPtrATB)⟩ dynRefAUninhabited
      (some vtMachTB) = .error (.ub "Value::Ptr: safe pointer to uninhabited type") ∧
    -- out of bounds (address 72 is one past the 8-byte allocation; 4 bytes needed)
    checkPtr ⟨dataPtr 72, some (.VTablePointer vtPtrA)⟩ dynRefA (some vtMach) =
      .error (.ub "Value::Ptr: non-dereferenceable safe pointer") ∧
    checkPtrM ⟨dataPtrTB 72, some (.VTablePointer vtPtrATB)⟩ dynRefA (some vtMachTB) =
      .error (.ub "Value::Ptr: non-dereferenceable safe pointer") ∧
    -- dead allocation
    checkPtr ⟨{ addr := 128, provenance := some (⟨1⟩, ()) }, some (.VTablePointer vtPtrA)⟩
      dynRefA (some vtMach) = .error (.ub "Value::Ptr: non-dereferenceable safe pointer") ∧
    checkPtrM ⟨{ addr := 128, provenance := some (⟨1⟩, []) }, some (.VTablePointer vtPtrATB)⟩
      dynRefA (some vtMachTB) = .error (.ub "Value::Ptr: non-dereferenceable safe pointer") ∧
    -- provenance-free data pointer
    checkPtr ⟨{ addr := 64, provenance := none }, some (.VTablePointer vtPtrA)⟩ dynRefA
      (some vtMach) = .error (.ub "Value::Ptr: non-dereferenceable safe pointer") ∧
    checkPtrM ⟨{ addr := 64, provenance := none }, some (.VTablePointer vtPtrATB)⟩ dynRefA
      (some vtMachTB) = .error (.ub "Value::Ptr: non-dereferenceable safe pointer") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl⟩

/-- `check_value` and `CastOp::Transmute` on both machines reach the vtable and
safe-pointer checks (no `Stop.unsupported`): transmuting a thin raw pointer to a
stand-alone vtable pointer, and a wide raw `*const dyn TraitA` to `&dyn TraitA`. -/
theorem transmute_vtablePtr_witness :
    -- `check_value` at `PtrType::VTablePtr` and at `&dyn TraitA`
    checkValue (.Ptr ⟨vtPtrA, none⟩) (.Ptr (.VTablePtr traitA)) (some vtMach) = .ok () ∧
    checkValueM (.Ptr ⟨vtPtrATB, none⟩) (.Ptr (.VTablePtr traitA)) (some vtMachTB) = .ok () ∧
    checkValue (.Ptr ⟨dataPtr 64, some (.VTablePointer vtPtrA)⟩) (.Ptr dynRefA) (some vtMach) =
      .ok () ∧
    checkValueM (.Ptr ⟨dataPtrTB 64, some (.VTablePointer vtPtrATB)⟩) (.Ptr dynRefA)
      (some vtMachTB) = .ok () ∧
    -- thin raw pointer -> stand-alone vtable pointer: ok, unregistered UB, wrong-trait UB
    evalUnOp (.Cast (.Transmute (.Ptr (.VTablePtr traitA))))
      (.Ptr ⟨vtPtrA, none⟩, .Ptr (.Raw .None)) (some vtMach) =
      .ok (.Ptr ⟨vtPtrA, none⟩, .Ptr (.VTablePtr traitA)) ∧
    evalUnOpM (.Cast (.Transmute (.Ptr (.VTablePtr traitA))))
      (.Ptr ⟨vtPtrATB, none⟩, .Ptr (.Raw .None)) (some vtMachTB) =
      .ok (.Ptr ⟨vtPtrATB, none⟩, .Ptr (.VTablePtr traitA)) ∧
    evalUnOp (.Cast (.Transmute (.Ptr (.VTablePtr traitA))))
      (.Ptr ⟨dataPtr 64, none⟩, .Ptr (.Raw .None)) (some vtMach) =
      .error (.ub "invalid pointer for vtable lookup") ∧
    evalUnOpM (.Cast (.Transmute (.Ptr (.VTablePtr traitA))))
      (.Ptr ⟨dataPtrTB 64, none⟩, .Ptr (.Raw .None)) (some vtMachTB) =
      .error (.ub "invalid pointer for vtable lookup") ∧
    evalUnOp (.Cast (.Transmute (.Ptr (.VTablePtr traitA))))
      (.Ptr ⟨vtPtrB, none⟩, .Ptr (.Raw .None)) (some vtMach) =
      .error (.ub "Value::Ptr: invalid vtable in metadata") ∧
    evalUnOpM (.Cast (.Transmute (.Ptr (.VTablePtr traitA))))
      (.Ptr ⟨vtPtrBTB, none⟩, .Ptr (.Raw .None)) (some vtMachTB) =
      .error (.ub "Value::Ptr: invalid vtable in metadata") ∧
    -- wide raw `*const dyn TraitA` -> `&dyn TraitA`: ok and unaligned UB
    evalUnOp (.Cast (.Transmute (.Ptr dynRefA)))
      (.Ptr ⟨dataPtr 64, some (.VTablePointer vtPtrA)⟩,
        .Ptr (.Raw (.VTablePointer traitA))) (some vtMach) =
      .ok (.Ptr ⟨dataPtr 64, some (.VTablePointer vtPtrA)⟩, .Ptr dynRefA) ∧
    evalUnOpM (.Cast (.Transmute (.Ptr dynRefA)))
      (.Ptr ⟨dataPtrTB 64, some (.VTablePointer vtPtrATB)⟩,
        .Ptr (.Raw (.VTablePointer traitA))) (some vtMachTB) =
      .ok (.Ptr ⟨dataPtrTB 64, some (.VTablePointer vtPtrATB)⟩, .Ptr dynRefA) ∧
    evalUnOp (.Cast (.Transmute (.Ptr dynRefA)))
      (.Ptr ⟨dataPtr 66, some (.VTablePointer vtPtrA)⟩,
        .Ptr (.Raw (.VTablePointer traitA))) (some vtMach) =
      .error (.ub "Value::Ptr: unaligned safe pointer") ∧
    evalUnOpM (.Cast (.Transmute (.Ptr dynRefA)))
      (.Ptr ⟨dataPtrTB 66, some (.VTablePointer vtPtrATB)⟩,
        .Ptr (.Raw (.VTablePointer traitA))) (some vtMachTB) =
      .error (.ub "Value::Ptr: unaligned safe pointer") := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The two witness machines agree on vtables, and their registered vtable pointers
and data pointers are path-faithful: the agreement theorems apply to them. -/
theorem vtMach_vtMachTB_agree :
    VTablesAgree vtMach vtMachTB ∧
    PathFaithful vtMachTB vtPtrATB ∧ PathFaithful vtMachTB vtPtrBTB ∧
    PathFaithful vtMachTB (dataPtrTB 64) ∧
    checkPtr (erasePathPtr ⟨vtPtrATB, none⟩) (.VTablePtr traitA) (some vtMach) =
      checkPtrM ⟨vtPtrATB, none⟩ (.VTablePtr traitA) (some vtMachTB) := by
  have hagree : VTablesAgree vtMach vtMachTB := ⟨rfl, rfl⟩
  have hA : PathFaithful vtMachTB vtPtrATB := by unfold PathFaithful; decide
  have hB : PathFaithful vtMachTB vtPtrBTB := by unfold PathFaithful; decide
  have hD : PathFaithful vtMachTB (dataPtrTB 64) := by unfold PathFaithful; decide
  exact ⟨hagree, hA, hB, hD,
    checkPtr_vtablePtr_agree vtMach vtMachTB hagree ⟨vtPtrATB, none⟩ traitA hA⟩

/-- A Tree Borrows pointer to the vtable allocation of `vtableA` with a non-root path. -/
def vtPtrAChildTB : ThinPointer TreeBorrowsProvenance :=
  { addr := 4096, provenance := some (⟨7⟩, [0]) }

/-- **Path faithfulness is necessary.** A Tree Borrows pointer to the vtable
allocation of `vtableA` with a non-root path is not one of the machine's vtable
pointers (UB on `MachTB`), while the `BasicMemory` pointer it denotes is (`ok` on
`Mach`): `BasicMemory` provenance cannot tell the two apart. -/
theorem vtablePtr_child_path_divergence :
    ¬ PathFaithful vtMachTB vtPtrAChildTB ∧
    erasePath vtPtrAChildTB = vtPtrA ∧
    checkPtrM ⟨vtPtrAChildTB, none⟩ (.VTablePtr traitA) (some vtMachTB) =
      .error (.ub "invalid pointer for vtable lookup") ∧
    checkPtr ⟨vtPtrA, none⟩ (.VTablePtr traitA) (some vtMach) = .ok () := by
  refine ⟨?_, rfl, rfl, rfl⟩
  unfold PathFaithful
  decide

end MiniRustSpec.Correspondence.VTablePtr
