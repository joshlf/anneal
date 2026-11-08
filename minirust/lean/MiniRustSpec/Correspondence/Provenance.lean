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
# Angelic `IntPtrCast::int2ptr` prediction invariants (MR-3.3)

`IntPtrCast::int2ptr` (`spec/mem/intptrcast.md`) resolves the provenance of an
integer-to-pointer cast with MiniRust's angelic `predict`:

> "let provenance = predict(|prov: Option<Provenance>| {
>     prov.map_or(
>         true, // `None` is always an option
>         |p| self.exposed.contains(p),
>     )
> })?;"

The executable interpretation commits to one resolution (`int2ptrProvenance`
for `BasicMemory`, `int2ptrProvenanceM` for any `Memory` with a `MemoryOps`
instance, in particular `TreeBorrowsMemory`). This module proves what that
resolution guarantees, independently of any concrete program:

1. **Admissibility** (`int2ptrProvenance_admissible`,
   `int2ptrProvenanceM_admissible`, `IntPtrCast.int2ptr_admissible`): every
   provenance the interpretation returns satisfies `predict`'s predicate
   (`Int2ptrAdmissible`), so every completed run is a genuine MiniRust run.
2. **`None` only when forced** (`int2ptrProvenance_eq_none_iff`): the
   interpretation predicts `None` exactly when nothing is exposed, i.e. when
   `None` is the *only* admissible provenance.
3. **Failure is never UB** (`int2ptrProvenance_error_unsupported`): the
   prediction itself only ever stops with `Stop.unsupported`, never with
   fabricated UB.
4. **Uniqueness of the committed choice** (`int2ptrProvenanceM_unique`): any
   exposed provenance whose live allocation contains the address *is* the
   predicted one, for every memory model whose filtering hook only returns
   exposed provenances (`ExposedInBoundsSound`, proved for `BM` and `TBM`).
5. **Angelic optimality for the immediate access**
   (`int2ptr_checkPtr_angelic_optimal`, `int2ptr_checkPtr_ub_forced`): if any
   admissible provenance makes `BasicMemory::check_ptr` succeed at the cast
   address, the predicted pointer succeeds too; contrapositively, UB that the
   predicted pointer raises on its first access is raised by *every*
   admissible choice, so it is genuine angelic UB rather than an artifact of
   the resolution.
6. **Ambiguity is exactly a shared boundary**
   (`int2ptrCandidates_two_boundary`, `int2ptrProvenance_boundary_unsupported`):
   under the `BasicMemory::allocate` invariant that live allocations do not
   overlap (`LiveDisjoint`), two distinct candidates only arise where one live
   exposed allocation ends and another begins, and every such meeting point
   stops with `Stop.unsupported`.
7. **Round trip** (`IntPtrCast.int2ptr_expose_empty_roundtrip`,
   `IntPtrCast.int2ptr_expose_unique_roundtrip`): exposing a pointer and
   casting its address back reconstructs exactly that pointer when its
   provenance is the only admissible in-bounds choice.
8. **Tree Borrows multi-tag ambiguity**
   (`int2ptrProvenanceM_tb_two_tags_unsupported`): two exposed tags of one
   live `TreeBorrowsMemory` allocation containing the address always stop with
   `Stop.unsupported` (the tag choice changes Tree Borrows UB, so no
   resolution is exact), even though `BasicMemory`'s `()` provenance
   deduplicates them.
-/

namespace MiniRustSpec.Correspondence

open MiniRustSpec
open MiniRustSpec.Gen
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp

/-! ## Admissibility -/

/-- The predicate of MiniRust's `predict` in `IntPtrCast::int2ptr`
(`spec/mem/intptrcast.md`):
> "prov.map_or(
>     true, // `None` is always an option
>     |p| self.exposed.contains(p),
> )" -/
def Int2ptrAdmissible {P : Type} [DecidableEq P] (exposed : Set P) : Option P → Prop
  | none => True
  | some p => setContains exposed p = true

theorem mem_int2ptrCandidates {allocs : List Gen.Allocation} {exposed : Set Prov} {addr : Int}
    {p : Prov} (h : p ∈ int2ptrCandidates allocs exposed addr) :
    ∃ (i : Nat) (a : Gen.Allocation), allocs[i]? = some a ∧ a.live = true ∧
      (a.addr : Int) ≤ addr ∧ addr ≤ (a.addr : Int) + (Allocation.size a).bytes ∧
      setContains exposed (⟨(i : Int)⟩, ()) = true ∧ p = (⟨(i : Int)⟩, ()) := by
  simp only [int2ptrCandidates, List.mem_map, List.mem_filter, Prod.exists, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨a, i, ⟨hzip, ⟨⟨hlive, hlo⟩, hhi⟩, hexp⟩, rfl⟩ := h
  exact ⟨i, a, List.mem_zipIdx_iff_getElem?.mp hzip, hlive, hlo, hhi, hexp, rfl⟩

theorem int2ptrCandidates_mem_of {allocs : List Gen.Allocation} {exposed : Set Prov}
    {addr : Int} {i : Nat} {a : Gen.Allocation}
    (ha : allocs[i]? = some a) (hlive : a.live = true) (hlo : (a.addr : Int) ≤ addr)
    (hhi : addr ≤ (a.addr : Int) + (Allocation.size a).bytes)
    (hexp : setContains exposed (⟨(i : Int)⟩, ()) = true) :
    ((⟨(i : Int)⟩, ()) : Prov) ∈ int2ptrCandidates allocs exposed addr := by
  simp only [int2ptrCandidates, List.mem_map, List.mem_filter, Prod.exists, Bool.and_eq_true,
    decide_eq_true_eq]
  exact ⟨a, i, ⟨List.mem_zipIdx_iff_getElem?.mpr ha, ⟨⟨hlive, hlo⟩, hhi⟩, hexp⟩, rfl⟩

theorem int2ptrCandidates_exposed {allocs : List Gen.Allocation} {exposed : Set Prov}
    {addr : Int} {p : Prov} (h : p ∈ int2ptrCandidates allocs exposed addr) :
    setContains exposed p = true := by
  obtain ⟨i, a, _, _, _, _, hexp, rfl⟩ := mem_int2ptrCandidates h
  exact hexp

theorem setContains_of_elems_eq_singleton {P : Type} [DecidableEq P] {s : Set P} {p q : P}
    (hs : s.elems = [p]) (hq : setContains s q = true) : q = p := by
  simpa [setContains, hs] using hq

theorem setContains_of_elems_eq_singleton_self {P : Type} [DecidableEq P] {s : Set P} {p : P}
    (hs : s.elems = [p]) : setContains s p = true := by
  simp [setContains, hs]

/-- Every provenance `int2ptrProvenance` predicts is admissible for MiniRust's
`predict`: `None`, or an exposed provenance. -/
theorem int2ptrProvenance_admissible {m : Mach} {addr : Int} {prov : Option Prov}
    (h : int2ptrProvenance m addr = .ok prov) :
    Int2ptrAdmissible m.intptrcast.exposed prov := by
  unfold int2ptrProvenance at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    trivial
  · next p hel =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact setContains_of_elems_eq_singleton_self hel
  · split at h
    · next p hc =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact int2ptrCandidates_exposed (p := p) (by rw [hc]; exact List.mem_singleton_self p)
    · simp [unsupported] at h
    · simp [unsupported] at h

theorem IntPtrCast.int2ptr_admissible {m : Mach} {addr : Int} {ptr : Ptr}
    (h : IntPtrCast.int2ptr m addr = .ok ptr) :
    ptr.addr = addr ∧ Int2ptrAdmissible m.intptrcast.exposed ptr.provenance := by
  unfold IntPtrCast.int2ptr at h
  cases hp : int2ptrProvenance m addr with
  | error e => simp [hp, bind, Except.bind] at h
  | ok prov =>
    simp only [hp, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, int2ptrProvenance_admissible hp⟩

/-- `int2ptrProvenance` predicts `None` exactly when nothing is exposed, i.e.
exactly when `None` is the only admissible provenance. -/
theorem int2ptrProvenance_eq_none_iff {m : Mach} {addr : Int} :
    int2ptrProvenance m addr = .ok none ↔ m.intptrcast.exposed.elems = [] := by
  constructor
  · intro h
    unfold int2ptrProvenance at h
    split at h
    · next hel => exact hel
    · simp [pure, Except.pure] at h
    · split at h
      · simp [pure, Except.pure] at h
      · simp [unsupported] at h
      · simp [unsupported] at h
  · intro hel
    simp [int2ptrProvenance, hel, pure, Except.pure]

/-- The prediction only ever stops with `Stop.unsupported`: it never fabricates
UB (or a spec panic) by guessing. -/
theorem int2ptrProvenance_error_unsupported {m : Mach} {addr : Int} {e : Stop}
    (h : int2ptrProvenance m addr = .error e) : ∃ msg, e = .unsupported msg := by
  unfold int2ptrProvenance at h
  split at h
  · simp [pure, Except.pure] at h
  · simp [pure, Except.pure] at h
  · split at h
    · simp [pure, Except.pure] at h
    · simp only [unsupported, Except.error.injEq] at h
      exact ⟨_, h.symm⟩
    · simp only [unsupported, Except.error.injEq] at h
      exact ⟨_, h.symm⟩

theorem IntPtrCast.int2ptr_error_unsupported {m : Mach} {addr : Int} {e : Stop}
    (h : IntPtrCast.int2ptr m addr = .error e) : ∃ msg, e = .unsupported msg := by
  unfold IntPtrCast.int2ptr at h
  cases hp : int2ptrProvenance m addr with
  | error e' =>
    simp only [hp, bind, Except.bind, Except.error.injEq] at h
    subst h
    exact int2ptrProvenance_error_unsupported hp
  | ok prov => simp [hp, bind, Except.bind, pure, Except.pure] at h

/-! ## Polymorphic admissibility and uniqueness (`BM` and `TBM`) -/

/-- The filtering hook `MemoryOps.exposedInBounds` only returns exposed
provenances (MiniRust's `predict` admits no other `Some` provenance). -/
def ExposedInBoundsSound (M : Type) [Memory M] [MemoryOps M] : Prop :=
  ∀ (mem : M) (exposed : Set (Memory.Provenance M)) (addr : Int) (p : Memory.Provenance M),
    p ∈ MemoryOps.exposedInBounds mem exposed addr → setContains exposed p = true

theorem exposedInBoundsSound_BM : ExposedInBoundsSound BM := by
  intro mem exposed addr p hp
  exact int2ptrCandidates_exposed hp

theorem mem_tbmExposedInBounds {tbm : TBM} {exposed : Set TreeBorrowsProvenance} {addr : Int}
    {p : TreeBorrowsProvenance} :
    p ∈ tbmExposedInBounds tbm exposed addr ↔
      p ∈ exposed.elems ∧ 0 ≤ p.1._0 ∧
        ∃ a, tbm.mem.allocations[p.1._0.toNat]? = some a ∧ a.live = true ∧
          (a.addr : Int) ≤ addr ∧ addr ≤ (a.addr : Int) + (Allocation.size a).bytes := by
  obtain ⟨⟨id⟩, tag⟩ := p
  simp only [tbmExposedInBounds, List.mem_filter]
  constructor
  · rintro ⟨hmem, hcond⟩
    refine ⟨hmem, ?_⟩
    split at hcond
    · next hid =>
      refine ⟨hid, ?_⟩
      split at hcond
      · next a ha =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        exact ⟨a, ha, hcond.1.1, hcond.1.2, hcond.2⟩
      · simp at hcond
    · simp at hcond
  · rintro ⟨hmem, hid, a, ha, hlive, hlo, hhi⟩
    refine ⟨hmem, ?_⟩
    simp only [hid, ↓reduceIte, ha, hlive, hlo, hhi, decide_true, Bool.and_self]

theorem exposedInBoundsSound_TBM : ExposedInBoundsSound TBM := by
  intro mem exposed addr p hp
  have hp' : p ∈ tbmExposedInBounds mem exposed addr := hp
  simpa [setContains] using (mem_tbmExposedInBounds.mp hp').1

/-- Every provenance `int2ptrProvenanceM` predicts is admissible for MiniRust's
`predict`, for any memory model whose hook is `ExposedInBoundsSound`. -/
theorem int2ptrProvenanceM_admissible {M : Type} [Memory M] [MemoryOps M]
    (hsound : ExposedInBoundsSound M) {m : Machine M} {addr : Int}
    {prov : Option (Memory.Provenance M)} (h : int2ptrProvenanceM m addr = .ok prov) :
    Int2ptrAdmissible m.intptrcast.exposed prov := by
  unfold int2ptrProvenanceM at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    trivial
  · next p hel =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact setContains_of_elems_eq_singleton_self hel
  · split at h
    · next p hc =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact hsound _ _ _ p (by rw [hc]; exact List.mem_singleton_self p)
    · simp [unsupported] at h
    · simp [unsupported] at h

theorem int2ptrProvenanceM_admissible_BM {m : Machine BM} {addr : Int} {prov : Option Prov}
    (h : int2ptrProvenanceM m addr = .ok prov) : Int2ptrAdmissible m.intptrcast.exposed prov :=
  int2ptrProvenanceM_admissible exposedInBoundsSound_BM h

theorem int2ptrProvenanceM_admissible_TBM {m : MachTB} {addr : Int}
    {prov : Option TreeBorrowsProvenance}
    (h : int2ptrProvenanceM m addr = .ok prov) : Int2ptrAdmissible m.intptrcast.exposed prov :=
  int2ptrProvenanceM_admissible exposedInBoundsSound_TBM h

theorem int2ptrProvenanceM_error_unsupported {M : Type} [Memory M] [MemoryOps M]
    {m : Machine M} {addr : Int} {e : Stop}
    (h : int2ptrProvenanceM m addr = .error e) : ∃ msg, e = .unsupported msg := by
  unfold int2ptrProvenanceM at h
  split at h
  · simp [pure, Except.pure] at h
  · simp [pure, Except.pure] at h
  · split at h
    · simp [pure, Except.pure] at h
    · simp only [unsupported, Except.error.injEq] at h
      exact ⟨_, h.symm⟩
    · simp only [unsupported, Except.error.injEq] at h
      exact ⟨_, h.symm⟩

/-- The committed choice is the unique in-bounds candidate: any provenance that
`MemoryOps.exposedInBounds` returns at `addr` *is* the predicted provenance. -/
theorem int2ptrProvenanceM_unique {M : Type} [Memory M] [MemoryOps M]
    (hsound : ExposedInBoundsSound M) {m : Machine M} {addr : Int}
    {p q : Memory.Provenance M} (h : int2ptrProvenanceM m addr = .ok (some p))
    (hq : q ∈ MemoryOps.exposedInBounds m.mem.memory m.intptrcast.exposed addr) : q = p := by
  unfold int2ptrProvenanceM at h
  split at h
  · simp [pure, Except.pure] at h
  · next p' hel =>
    simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
    subst h
    exact setContains_of_elems_eq_singleton hel (hsound _ _ _ q hq)
  · split at h
    · next p' hc =>
      simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
      subst h
      rw [hc] at hq
      exact List.mem_singleton.mp hq
    · simp [unsupported] at h
    · simp [unsupported] at h

/-- `BasicMemory` uniqueness: every `int2ptrCandidates` candidate at `addr` is
the provenance `int2ptrProvenance` predicted. -/
theorem int2ptrProvenance_unique_cand {m : Mach} {addr : Int} {p q : Prov}
    (h : int2ptrProvenance m addr = .ok (some p))
    (hq : q ∈ int2ptrCandidates m.mem.memory.allocations m.intptrcast.exposed addr) : q = p := by
  unfold int2ptrProvenance at h
  split at h
  · simp [pure, Except.pure] at h
  · next p' hel =>
    simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
    subst h
    exact setContains_of_elems_eq_singleton hel (int2ptrCandidates_exposed hq)
  · split at h
    · next p' hc =>
      simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
      subst h
      rw [hc] at hq
      exact List.mem_singleton.mp hq
    · simp [unsupported] at h
    · simp [unsupported] at h

/-- `BasicMemory` instance of `int2ptrProvenanceM_unique`: every exposed live
allocation whose range contains `addr` is the predicted one. -/
theorem int2ptrProvenance_unique {m : Mach} {addr : Int} {p : Prov} {i : Nat}
    {a : Gen.Allocation} (h : int2ptrProvenance m addr = .ok (some p))
    (ha : m.mem.memory.allocations[i]? = some a) (hlive : a.live = true)
    (hlo : (a.addr : Int) ≤ addr) (hhi : addr ≤ (a.addr : Int) + (Allocation.size a).bytes)
    (hexp : setContains m.intptrcast.exposed (⟨(i : Int)⟩, ()) = true) :
    ((⟨(i : Int)⟩, ()) : Prov) = p :=
  int2ptrProvenance_unique_cand h (int2ptrCandidates_mem_of ha hlive hlo hhi hexp)

/-! ## Angelic optimality for the immediate access (`BasicMemory::check_ptr`) -/

/-- A successful positive-size `BasicMemory::check_ptr` through `(addr, some q)`
locates `q`'s live allocation around `addr`. -/
theorem checkPtr_ok_some_inv {mem : BM} {addr : Int} {q : Prov} {len : Size}
    {r : Option (AllocId × Unit × Size)} (hlen : len.bytes ≠ 0)
    (hok : BM.check_ptr mem { addr := addr, provenance := some q } len = .ok r) :
    0 ≤ q.1._0 ∧ ∃ a, mem.allocations[q.1._0.toNat]? = some a ∧ a.live = true ∧
      (a.addr : Int) ≤ addr ∧ addr + len.bytes ≤ (a.addr : Int) + (Allocation.size a).bytes := by
  obtain ⟨⟨id⟩, ⟨⟩⟩ := q
  simp only [BM.check_ptr, hlen, ↓reduceIte, listIndex] at hok
  by_cases hid : 0 ≤ id
  · simp only [hid, ↓reduceIte] at hok
    cases ha : mem.allocations[id.toNat]? with
    | none => simp [ha, bind, Except.bind, specPanic] at hok
    | some a =>
      simp only [ha, bind, Except.bind, pure, Except.pure] at hok
      by_cases hlive : a.live = true
      · by_cases hin : addr - (a.addr : Int) < 0 ∨
            addr - (a.addr : Int) + (len.bytes : Int) > ((Allocation.size a).bytes : Int)
        · simp [hlive, hin, ub] at hok
        · refine ⟨hid, a, rfl, hlive, ?_, ?_⟩ <;> (dsimp only [Address] at *; omega)
      · simp [hlive, ub] at hok
  · simp [hid, bind, Except.bind, specPanic] at hok

/-- A positive-size `BasicMemory::check_ptr` without provenance is UB. -/
theorem checkPtr_none_error {mem : BM} {addr : Int} {len : Size} (hlen : len.bytes ≠ 0) :
    ∃ e, BM.check_ptr mem { addr := addr, provenance := none } len = .error e :=
  ⟨.ub "dereferencing pointer without provenance", by simp [BM.check_ptr, hlen, ub]⟩

/-- **Angelic optimality.** If *some* admissible provenance `q` makes
`BasicMemory::check_ptr` succeed for an access of `len` bytes at the cast
address, then the pointer `IntPtrCast.int2ptr` predicted succeeds as well. -/
theorem int2ptr_checkPtr_angelic_optimal {m : Mach} {addr : Int} {ptr : Ptr} {len : Size}
    (hint : IntPtrCast.int2ptr m addr = .ok ptr) {q : Option Prov}
    (hq : Int2ptrAdmissible m.intptrcast.exposed q)
    {r : Option (AllocId × Unit × Size)}
    (hok : BM.check_ptr m.mem.memory { addr := addr, provenance := q } len = .ok r) :
    ∃ r', BM.check_ptr m.mem.memory ptr len = .ok r' := by
  by_cases hlen : len.bytes = 0
  · exact ⟨none, by simp [BM.check_ptr, hlen, pure, Except.pure]⟩
  · cases q with
    | none =>
      obtain ⟨e, he⟩ := checkPtr_none_error (mem := m.mem.memory) (addr := addr) hlen
      rw [he] at hok
      cases hok
    | some qp =>
      have hexp : setContains m.intptrcast.exposed qp = true := hq
      obtain ⟨hid, a, ha, hlive, hlo, hhi⟩ := checkPtr_ok_some_inv hlen hok
      have hqp : qp = (⟨((qp.1._0.toNat : Nat) : Int)⟩, ()) := by
        obtain ⟨⟨id⟩, ⟨⟩⟩ := qp
        simp only at hid ⊢
        congr 2
        omega
      have hcand : qp ∈ int2ptrCandidates m.mem.memory.allocations m.intptrcast.exposed addr := by
        rw [hqp]
        exact int2ptrCandidates_mem_of ha hlive hlo (by dsimp only [Address] at *; omega) (hqp ▸ hexp)
      unfold IntPtrCast.int2ptr at hint
      cases hp : int2ptrProvenance m addr with
      | error e => simp [hp, bind, Except.bind] at hint
      | ok prov =>
        simp only [hp, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hint
        subst hint
        cases prov with
        | none =>
          have hel := int2ptrProvenance_eq_none_iff.mp hp
          simp [setContains, hel] at hexp
        | some p =>
          have heq : qp = p := int2ptrProvenance_unique_cand hp hcand
          subst heq
          exact ⟨r, hok⟩

/-- **Forced UB.** If the pointer `IntPtrCast.int2ptr` predicted fails
`BasicMemory::check_ptr` (UB on its first access), every admissible provenance
fails it too: the UB holds for MiniRust's angelic choice, not just for this
resolution. -/
theorem int2ptr_checkPtr_ub_forced {m : Mach} {addr : Int} {ptr : Ptr} {len : Size} {e : Stop}
    (hint : IntPtrCast.int2ptr m addr = .ok ptr)
    (hfail : BM.check_ptr m.mem.memory ptr len = .error e) {q : Option Prov}
    (hq : Int2ptrAdmissible m.intptrcast.exposed q) :
    ∃ e', BM.check_ptr m.mem.memory { addr := addr, provenance := q } len = .error e' := by
  cases hc : BM.check_ptr m.mem.memory { addr := addr, provenance := q } len with
  | error e' => exact ⟨e', rfl⟩
  | ok r =>
    obtain ⟨r', hr'⟩ := int2ptr_checkPtr_angelic_optimal hint hq hc
    rw [hr'] at hfail
    cases hfail

/-! ## Ambiguity: exactly a shared allocation boundary -/

/-- The `BasicMemory::allocate` invariant (`spec/mem/basic.md`, `Allocation::overlaps`):
distinct live allocations do not overlap. -/
def LiveDisjoint (allocs : List Gen.Allocation) : Prop :=
  ∀ (i j : Nat) (a b : Gen.Allocation), i ≠ j → allocs[i]? = some a → allocs[j]? = some b →
    a.live = true → b.live = true →
    (a.addr : Int) + (Allocation.size a).bytes ≤ b.addr ∨
      (b.addr : Int) + (Allocation.size b).bytes ≤ a.addr

/-- Under `LiveDisjoint`, two distinct `int2ptrCandidates` at `addr` belong to
live exposed allocations of which one ends exactly at `addr` and the other
starts exactly at `addr`. -/
theorem int2ptrCandidates_two_boundary {allocs : List Gen.Allocation} {exposed : Set Prov}
    {addr : Int} (hdisj : LiveDisjoint allocs) {p q : Prov}
    (hp : p ∈ int2ptrCandidates allocs exposed addr)
    (hq : q ∈ int2ptrCandidates allocs exposed addr) (hne : p ≠ q) :
    ∃ (i j : Nat) (a b : Gen.Allocation),
      p = (⟨(i : Int)⟩, ()) ∧ q = (⟨(j : Int)⟩, ()) ∧
      allocs[i]? = some a ∧ allocs[j]? = some b ∧
      (((a.addr : Int) + (Allocation.size a).bytes = addr ∧ (b.addr : Int) = addr) ∨
       ((b.addr : Int) + (Allocation.size b).bytes = addr ∧ (a.addr : Int) = addr)) := by
  obtain ⟨i, a, ha, hla, hlo1, hhi1, _, rfl⟩ := mem_int2ptrCandidates hp
  obtain ⟨j, b, hb, hlb, hlo2, hhi2, _, rfl⟩ := mem_int2ptrCandidates hq
  have hij : i ≠ j := by
    intro h
    subst h
    exact hne rfl
  refine ⟨i, j, a, b, rfl, rfl, ha, hb, ?_⟩
  rcases hdisj i j a b hij ha hb hla hlb with h | h
  · exact .inl ⟨by dsimp only [Address] at *; omega, by dsimp only [Address] at *; omega⟩
  · exact .inr ⟨by dsimp only [Address] at *; omega, by dsimp only [Address] at *; omega⟩

/-- Two exposed live allocations meeting at `addr` (one ending, the other
starting there) make `int2ptrProvenance` stop with `Stop.unsupported`. -/
theorem int2ptrProvenance_boundary_unsupported {m : Mach} {addr : Int} {i j : Nat}
    {a b : Gen.Allocation} (hij : i ≠ j)
    (ha : m.mem.memory.allocations[i]? = some a) (hb : m.mem.memory.allocations[j]? = some b)
    (hla : a.live = true) (hlb : b.live = true)
    (hend : (a.addr : Int) + (Allocation.size a).bytes = addr) (hstart : (b.addr : Int) = addr)
    (hexi : setContains m.intptrcast.exposed (⟨(i : Int)⟩, ()) = true)
    (hexj : setContains m.intptrcast.exposed (⟨(j : Int)⟩, ()) = true) :
    ∃ msg, int2ptrProvenance m addr = .error (.unsupported msg) := by
  have hpi : ((⟨(i : Int)⟩, ()) : Prov) ∈
      int2ptrCandidates m.mem.memory.allocations m.intptrcast.exposed addr :=
    int2ptrCandidates_mem_of ha hla (by
      have : (0 : Int) ≤ (Allocation.size a).bytes := Int.natCast_nonneg _
      dsimp only [Address] at *; omega) (by dsimp only [Address] at *; omega) hexi
  have hpj : ((⟨(j : Int)⟩, ()) : Prov) ∈
      int2ptrCandidates m.mem.memory.allocations m.intptrcast.exposed addr :=
    int2ptrCandidates_mem_of hb hlb (by dsimp only [Address] at *; omega) (by
      have : (0 : Int) ≤ (Allocation.size b).bytes := Int.natCast_nonneg _
      dsimp only [Address] at *; omega) hexj
  have hne : ((⟨(i : Int)⟩, ()) : Prov) ≠ (⟨(j : Int)⟩, ()) := by
    intro h
    apply hij
    have := congrArg (fun p : Prov => p.1._0) h
    simp only at this
    omega
  cases hp : int2ptrProvenance m addr with
  | error e => exact int2ptrProvenance_error_unsupported hp |>.imp fun msg h => by rw [h]
  | ok prov =>
    exfalso
    have hadm := int2ptrProvenance_admissible hp
    cases prov with
    | none =>
      have hel := int2ptrProvenance_eq_none_iff.mp hp
      simp [setContains, hel] at hexi
    | some p =>
      have h1 := int2ptrProvenance_unique hp ha hla (by
        have : (0 : Int) ≤ (Allocation.size a).bytes := Int.natCast_nonneg _
        dsimp only [Address] at *; omega) (by dsimp only [Address] at *; omega) hexi
      have h2 := int2ptrProvenance_unique hp hb hlb (by dsimp only [Address] at *; omega) (by
        have : (0 : Int) ≤ (Allocation.size b).bytes := Int.natCast_nonneg _
        dsimp only [Address] at *; omega) hexj
      exact hne (h1.trans h2.symm)

/-! ## Round trip -/

theorem setContains_expose_self_some (ipc : Gen.IntPtrCast Prov) (addr : Int) (p : Prov) :
    setContains (IntPtrCast.expose ipc { addr := addr, provenance := some p }).exposed p = true := by
  simp only [IntPtrCast.expose, setInsert, setContains]
  split
  · next h => exact h
  · simp

/-- Exposing a pointer when nothing else is exposed and casting its address
back reconstructs exactly that pointer (`None` provenance included). -/
theorem IntPtrCast.int2ptr_expose_empty_roundtrip {m : Mach} (ptr : Ptr)
    (hempty : m.intptrcast.exposed.elems = []) :
    IntPtrCast.int2ptr { m with intptrcast := IntPtrCast.expose m.intptrcast ptr } ptr.addr =
      .ok ptr := by
  obtain ⟨addr, _ | p⟩ := ptr
  · simp [IntPtrCast.int2ptr, IntPtrCast.expose, int2ptrProvenance, hempty, bind, Except.bind,
      pure, Except.pure]
  · simp [IntPtrCast.int2ptr, IntPtrCast.expose, int2ptrProvenance, setInsert, hempty, bind,
      Except.bind, pure, Except.pure]

/-- `int2ptrCandidates` never lists an allocation twice. -/
theorem int2ptrCandidates_nodup (allocs : List Gen.Allocation) (exposed : Set Prov) (addr : Int) :
    (int2ptrCandidates allocs exposed addr).Nodup := by
  have key : ∀ (l : List (Gen.Allocation × Nat)), (l.map Prod.snd).Nodup →
      (l.map (fun (x : Gen.Allocation × Nat) => ((⟨(x.2 : Int)⟩, ()) : Prov))).Nodup := by
    intro l hl
    have hmap : l.map (fun (x : Gen.Allocation × Nat) => ((⟨(x.2 : Int)⟩, ()) : Prov)) =
        (l.map Prod.snd).map (fun i : Nat => ((⟨(i : Int)⟩, ()) : Prov)) := by
      rw [List.map_map]
      rfl
    rw [hmap]
    refine List.Pairwise.map _ (fun a b hab h => hab ?_) hl
    have := congrArg (fun p : Prov => p.1._0) h
    simp only at this
    omega
  apply key
  refine (List.filter_sublist.map Prod.snd).nodup ?_
  rw [List.zipIdx_map_snd]
  exact List.nodup_range' ..

/-- When `p` is exposed and is the only `int2ptrCandidates` candidate at
`addr`, `IntPtrCast.int2ptr` returns exactly `(addr, some p)`. -/
theorem IntPtrCast.int2ptr_of_unique_candidate {m : Mach} {addr : Int} {p : Prov}
    (hexp : setContains m.intptrcast.exposed p = true)
    (hcand : p ∈ int2ptrCandidates m.mem.memory.allocations m.intptrcast.exposed addr)
    (honly : ∀ q ∈ int2ptrCandidates m.mem.memory.allocations m.intptrcast.exposed addr, q = p) :
    IntPtrCast.int2ptr m addr = .ok { addr := addr, provenance := some p } := by
  have hcands : int2ptrCandidates m.mem.memory.allocations m.intptrcast.exposed addr = [p] := by
    have hnd := int2ptrCandidates_nodup m.mem.memory.allocations m.intptrcast.exposed addr
    generalize int2ptrCandidates m.mem.memory.allocations m.intptrcast.exposed addr = cs
      at hnd hcand honly
    match cs, hnd, hcand, honly with
    | [], _, h, _ => cases h
    | [x], _, h, _ => rw [List.mem_singleton.mp h]
    | x :: y :: rest, hnd, _, hall =>
      have hx := hall x (by simp)
      have hy := hall y (by simp)
      exact absurd (by rw [hx, ← hy]; exact List.mem_cons_self ..) (List.nodup_cons.mp hnd).1
  have hprov : int2ptrProvenance m addr = .ok (some p) := by
    unfold int2ptrProvenance
    split
    · next hel => simp [setContains, hel] at hexp
    · next p' hel =>
      have := setContains_of_elems_eq_singleton hel hexp
      subst this
      rfl
    · rw [hcands]
      rfl
  simp [IntPtrCast.int2ptr, hprov, bind, Except.bind, pure, Except.pure]

/-- **Round trip.** Exposing a pointer with provenance `(AllocId(i), ())` whose
live allocation contains its address, when that allocation is the only live
exposed one whose range contains the address afterwards, and casting the address
back reconstructs exactly that pointer. -/
theorem IntPtrCast.int2ptr_expose_unique_roundtrip {m : Mach} {addr : Int} {i : Nat}
    {a : Gen.Allocation}
    (ha : m.mem.memory.allocations[i]? = some a) (hlive : a.live = true)
    (hlo : (a.addr : Int) ≤ addr) (hhi : addr ≤ (a.addr : Int) + (Allocation.size a).bytes)
    (honly : ∀ q ∈ int2ptrCandidates m.mem.memory.allocations
        (IntPtrCast.expose m.intptrcast { addr := addr, provenance := some (⟨(i : Int)⟩, ()) }).exposed
        addr, q = (⟨(i : Int)⟩, ())) :
    IntPtrCast.int2ptr
        { m with intptrcast := IntPtrCast.expose m.intptrcast
                  { addr := addr, provenance := some (⟨(i : Int)⟩, ()) } } addr =
      .ok { addr := addr, provenance := some (⟨(i : Int)⟩, ()) } := by
  have hexp := setContains_expose_self_some m.intptrcast addr (⟨(i : Int)⟩, ())
  exact IntPtrCast.int2ptr_of_unique_candidate
    (m := { m with intptrcast := (IntPtrCast.expose m.intptrcast
      { addr := addr, provenance := some (⟨(i : Int)⟩, ()) }) }) hexp
    (int2ptrCandidates_mem_of ha hlive hlo hhi hexp) honly

/-! ## Tree Borrows: several exposed tags of one allocation -/

/-- Two distinct exposed Tree Borrows provenances of one live allocation whose
range contains `addr` make `int2ptrProvenanceM` stop with `Stop.unsupported`:
the tag decides Tree Borrows UB, so no committed resolution is exact. -/
theorem int2ptrProvenanceM_tb_two_tags_unsupported {m : MachTB} {addr : Int}
    {p q : TreeBorrowsProvenance} (hne : p ≠ q)
    (hp : p ∈ tbmExposedInBounds m.mem.memory m.intptrcast.exposed addr)
    (hq : q ∈ tbmExposedInBounds m.mem.memory m.intptrcast.exposed addr) :
    ∃ msg, int2ptrProvenanceM m addr = .error (.unsupported msg) := by
  cases h : int2ptrProvenanceM m addr with
  | error e => exact int2ptrProvenanceM_error_unsupported h |>.imp fun msg he => by rw [he]
  | ok prov =>
    exfalso
    cases prov with
    | none =>
      have hpe := (mem_tbmExposedInBounds.mp hp).1
      unfold int2ptrProvenanceM at h
      split at h
      · next hel => rw [hel] at hpe; cases hpe
      · simp [pure, Except.pure] at h
      · split at h
        · simp [pure, Except.pure] at h
        · simp [unsupported] at h
        · simp [unsupported] at h
    | some r =>
      have h1 := int2ptrProvenanceM_unique (M := TBM) exposedInBoundsSound_TBM h hp
      have h2 := int2ptrProvenanceM_unique (M := TBM) exposedInBoundsSound_TBM h hq
      exact hne (h1.trans h2.symm)

/-- **Singleton arbitrary-offset angelic optimality.** When `m.intptrcast.exposed`
is a singleton `[p0]`, `IntPtrCast.int2ptr` is optimal not only at the cast
address `addr` (`offset = 0`), but across **every** arbitrary byte offset
`off : Int` (e.g., struct field projection `(*ptr).field` or `wrapping_offset`
bringing an out-of-bounds integer address back into allocation `p0`): if *some*
admissible provenance `q` makes `BasicMemory::check_ptr` succeed at `addr + off`
for `len` bytes, then the pointer `ptr` predicted by `IntPtrCast.int2ptr m addr`
succeeds at `ptr.addr + off` as well. -/
theorem int2ptr_singleton_offset_checkPtr_optimal {m : Mach} {addr off : Int}
    {p0 : Prov} {ptr : Ptr} {len : Size}
    (hsing : m.intptrcast.exposed.elems = [p0])
    (hint : IntPtrCast.int2ptr m addr = .ok ptr) {q : Option Prov}
    (hq : Int2ptrAdmissible m.intptrcast.exposed q)
    {r : Option (AllocId × Unit × Size)}
    (hok : BM.check_ptr m.mem.memory { addr := addr + off, provenance := q } len = .ok r) :
    ∃ r', BM.check_ptr m.mem.memory { addr := ptr.addr + off, provenance := ptr.provenance } len = .ok r' := by
  have hptr : ptr = { addr := addr, provenance := some p0 } := by
    simp [IntPtrCast.int2ptr, int2ptrProvenance, hsing, bind, Except.bind, pure, Except.pure] at hint
    exact hint.symm
  subst hptr
  by_cases hlen : len.bytes = 0
  · exact ⟨none, by simp [BM.check_ptr, hlen, pure, Except.pure]⟩
  · cases q with
    | none =>
      obtain ⟨e, he⟩ := checkPtr_none_error (mem := m.mem.memory) (addr := addr + off) hlen
      rw [he] at hok
      cases hok
    | some qp =>
      have hexp : setContains m.intptrcast.exposed qp = true := hq
      have hqp : qp = p0 := setContains_of_elems_eq_singleton hsing hexp
      subst hqp
      exact ⟨r, hok⟩

/-- **Tree Borrows singleton counterexample at negative offset on ZST reborrow.**
Unlike `BasicMemory` (where `int2ptr_singleton_offset_checkPtr_optimal` holds for
every continuation), in `TreeBorrowsMemory` (`MachTB`) when `exposed` is a
singleton `[p0]` (`p0 = (AllocId(0), parentPath)`) and `addr < a.addr` (strictly
before allocation `0`'s start address), `IntPtrCast.int2ptrM` commits to
`some p0`, which causes a zero-sized `TreeBorrowsMemory.reborrow` (`settings.inside = []`)
at `addr` to fail with `Stop.specPanic "Offset::from_bytes(ptr.addr - allocation.addr).unwrap()"`,
whereas the admissible `predict` choice `provenance = none` (`Int2ptrAdmissible`)
takes the `ptr.provenance = none` branch and succeeds! -/
theorem int2ptrSingletonZstNegOffset_tb_specPanic_vs_none_ok {m : MachTB} {addr : Int}
    {parentPath : Gen.Path} {a}
    {settings : Gen.ReborrowSettings} {fe : Gen.TreeBorrowsFrameExtra}
    (hsing : m.intptrcast.exposed.elems = [(⟨0⟩, parentPath)])
    (ha0 : m.mem.memory.mem.allocations[0]? = some a)
    (hneg : addr < a.addr)
    (hzst : settings.inside = []) :
    IntPtrCast.int2ptrM m addr = .ok { addr := addr, provenance := some (⟨0⟩, parentPath) } ∧
    Int2ptrAdmissible m.intptrcast.exposed (none : Option TreeBorrowsProvenance) ∧
    TreeBorrowsMemory.reborrow m.mem.memory
        { addr := addr, provenance := some (⟨0⟩, parentPath) } settings fe =
      .error (.specPanic "Offset::from_bytes(ptr.addr - allocation.addr).unwrap()") ∧
    TreeBorrowsMemory.reborrow m.mem.memory
        { addr := addr, provenance := none } settings fe =
      .ok ({ addr := addr, provenance := none }, m.mem.memory, fe) := by
  refine ⟨by simp [IntPtrCast.int2ptrM, int2ptrProvenanceM, hsing, bind, Except.bind, pure, Except.pure],
    trivial, ?_, ?_⟩
  · have hnot_le : ¬ (a.addr ≤ addr) := by dsimp only [Address] at hneg ⊢; omega
    simp [TreeBorrowsMemory.reborrow, BasicMemory.check_ptr, hzst,
      listMutateAt, listIndex, ha0, Size.from_bytes, hnot_le, specPanic,
      bind, Except.bind, pure, Except.pure]
  · simp [TreeBorrowsMemory.reborrow, BasicMemory.check_ptr, hzst, bind, Except.bind, pure, Except.pure]

end MiniRustSpec.Correspondence
