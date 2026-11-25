/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.PointersMachine

/-!
# Raw pointers and references in both semantics (MR-3.1, MR-3.2)

This module collects what both semantics do with thin raw pointers (`*const T`,
`*mut T`) and safe references (`&T`, `&mut T`), as the foundation for extending
the correspondence (`step_correspondence`) across `&raw const` / `&raw mut`,
`&` / `&mut`, reborrowing (`&*p`, `&mut *p`, `&raw *p`), `CopyForDeref`, `*p`,
`Offset`, and pointer casts:

* **MiniRust's representation of thin pointers and safe references.**
  `ptrBytes addr prov` is the encoding `encode_ptr` produces for an address in
  `[0, 2^64)`: the eight little-endian address bytes, each carrying the
  fragment of the pointer's provenance at its own position. `decode_ptr` reads
  the pointer back (`decode_thinRawPtr`, `decode_refTy`). `check_value` accepts
  any in-bounds address at `PtrType::Raw` (`checkValue_thinRawPtr`) and
  additionally checks non-null, pointee alignment, and dereferenceability in
  `m.mem` at `PtrType::Ref` (`checkValue_refTy`, `checkValue_refTy_null_ub`,
  `checkValue_refTy_unaligned_ub`, `checkValue_refTy_dangling_ub`, including
  across `CastOp::Transmute` and `Statement::Validate`). A byte whose fragment
  belongs to another provenance makes the decoded pointer lose its provenance
  (`decodePtrProvenance_mixed`).
* **Anneal's model of raw pointers and references** (unstable `b076d6a3`).
  `&raw const p` / `&p` (`Frozen` on `Freeze` integer targets) and
  `&raw mut p` / `&mut p` (`Active`) push a fresh Tree Borrows root entry and
  return a pointer whose `allocId` is the entry's tag (`evalRvalue_rawPtr_local`,
  `evalRvalue_ref_local`); reborrows push a child entry linked to the parent tag
  (`rawReborrowEntry`, `refReborrowEntry`: mutable reference reborrows start
  `Reserved`, and reference reborrows first read through the parent,
  `evalRvalue_rawPtr_reborrow`, `evalRvalue_ref_reborrow`). A dereference at
  offset `0` reads or writes the entry's target local at the entry's projection
  (`needsThinPtrElemResolution = false`); a dereference read freezes overlapping
  foreign `Active` entries (`freezeDerefReadBorrowsAt`), and a dereference write
  applies the Tree Borrows write transition to every entry
  (`invalidateDerefWriteBorrows_eq_map`); `Offset(p, n)` scales the 8-byte count
  `n` by the pointee stride, bounds-checks it, and faults on `Disabled` tags
  (`evalRvalue_offset`); and `PointerExposeProvenance` returns the canonical
  address `ptrAddress?` of the borrowed place and records the tag in
  `Memory.exposedAllocIds` (`evalRvalue_expose`).

The two models agree on creating raw pointers and references to locals, array
elements, or struct/tuple fields, on reborrowing and copying them, on reading
and writing through non-disabled tags (tracked flow-sensitively across arbitrary
CFGs by `ptrAliasingOk` / `PtrEnvOk`, including cold `hot = false` two-phase and
reference reborrow `.reserved` entries across foreign reads), on stride-scaled
`BinOp::Offset` bounds checks and array element byte-offset dereferencing, on
`PtrToPtr` casts, and on rejecting reads through dangling or uninitialized
pointers/references. Under the places-ptr `Trusted` semantics they also agree
on misaligned sub-scalar byte-offset dereferences (UB in both, `misaligned`)
and on exposed addresses (two pointers to the same local expose the same
canonical address, `exposeTwice`); both stay outside `inFragment` (they were
divergences before the places-ptr `Trusted` semantics). They disagree, with
MiniRust as the ground truth, on:

1. **Aliasing on `BasicMemory`**: Anneal's Tree Borrows entries make a write
   through a `Frozen` pointer (including an `Active` entry frozen by a foreign
   read), or an access through a tag disabled by a foreign write, UB;
   `BasicMemory` has no aliasing model (`retag_ptr` is the identity) and accepts
   both (while `TreeBorrowsMemory` agrees with Anneal). The static analysis
   disables every pointer local such an access could reach (`stepDerefWrite`,
   `stepForeignRead`; soundness `PtrEnvOk.foreignRead`, `PtrEnvOk.derefRead`).

Here Anneal is
merely stricter than `BasicMemory`, and `ptrAliasingOk` tracks tag liveness,
reservation (`hot : Bool`), and ancestor writability (`writable : Bool`)
flow-sensitively across CFGs so safe Rust
borrow/reborrow patterns (two-phase borrows with foreign reads, mutable reborrow
+ write + child use, sequential NLL borrows, `Retag([raw])`, and loop
borrows/reborrows) stay
inside `inFragment`. `MiniRustSpec.Correspondence.PointerWitness` and
`RefWitness` check each case on concrete programs.

## Module structure

The development is split, without changing any declaration, name, or proof, into four
modules that import one another in this order (so that elaborating one module fits in the
memory budget of an 8 GiB build host); importing this module re-exports all of them:

1. `MiniRustSpec.Correspondence.PointersCore`: the representations, Anneal's raw pointer and
   reference model, and Tree Borrows preservation under `ptrAliasingOk`;
2. `MiniRustSpec.Correspondence.PointersLattice`: the `PtrLocalState` join-semilattice,
   fixed-point theory, and symbolic Tree Borrows state-machine invariants;
3. `MiniRustSpec.Correspondence.PointersMachine` (with pure `Machine<BM>` / `Mach` submodules
   `PointersMachineCodec`, `PointersMachineExpr`, and `PointersMachineStep`): the
   `Machine<BM>` / `Mach` equivalence, vtable and trait-object pointers, `UnOp::GetMetadata`,
   and wide-pointer laws;
4. this module: the Tree Borrows structural invariants (`TreeBorrowsMemory.wf` / `wfLive`)
   and panic-freedom (`spec/mem/tree_borrows/*`).
-/

namespace MiniRustSpec.Correspondence

open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp
open Trusted.Sequence

/-! ## Tree Borrows structural invariants and panic-freedom (`spec/mem/tree_borrows/*`) -/

mutual

/-- Structural well-formedness of a `TreeBorrows` borrow-tree node for an
allocation of `sz` bytes: its per-byte `permissions` list has length `sz`,
every byte permission matches the node's `protected` state
(`Permission.matches_protector`), and all child nodes are recursively
well-formed at the same allocation byte length `sz`. -/
def Node.wf (sz : Nat) : Gen.Node → Prop
  | ⟨children, permissions, prot⟩ =>
    permissions.length = sz ∧
    (∀ p ∈ permissions, Permission.matches_protector p prot = true) ∧
    Node.childrenWf sz children

/-- Pointwise `Node.wf sz` across a child-node list. -/
def Node.childrenWf (sz : Nat) : List Gen.Node → Prop
  | [] => True
  | c :: cs => Node.wf sz c ∧ Node.childrenWf sz cs

end

/-- Every allocation in `tbm` (live or dead) has a well-formed borrow tree
whose byte-permission vectors match `(Allocation.size alloc).bytes`. -/
def TreeBorrowsMemory.wf (tbm : Gen.TreeBorrowsMemory Gen.x86_64) : Prop :=
  ∀ alloc ∈ tbm.mem.allocations, Node.wf (Allocation.size alloc).bytes alloc.extra.root

/-- Every **live** allocation in `tbm` has a well-formed borrow tree whose
byte-permission vectors match `(Allocation.size alloc).bytes`. (`release_protector`
and `end_call` preserve `wfLive` even when a weakly protected `Box<T>` was
deallocated before function return.) -/
def TreeBorrowsMemory.wfLive (tbm : Gen.TreeBorrowsMemory Gen.x86_64) : Prop :=
  ∀ alloc ∈ tbm.mem.allocations, alloc.live = true →
    Node.wf (Allocation.size alloc).bytes alloc.extra.root

theorem TreeBorrowsMemory.wfLive_of_wf {tbm : Gen.TreeBorrowsMemory Gen.x86_64}
    (h : TreeBorrowsMemory.wf tbm) : TreeBorrowsMemory.wfLive tbm :=
  fun alloc hm _ => h alloc hm

private theorem bind_ok {α β : Type} {m : Interp α} {f : α → Interp β} {y : β}
    (h : (m >>= f) = .ok y) : ∃ x, m = .ok x ∧ f x = .ok y := by
  cases m with
  | error _ => cases h
  | ok x => exact ⟨x, rfl, h⟩

private theorem interp_pure_ok {α : Type} {x y : α}
    (h : (pure x : Interp α) = .ok y) : x = y := by
  cases h
  rfl

private theorem bind_err {α β : Type} {m : Interp α} {f : α → Interp β} {e : Stop}
    (h : (m >>= f) = .error e) : m = .error e ∨ ∃ x, m = .ok x ∧ f x = .error e := by
  cases m with
  | error _ => cases h; exact .inl rfl
  | ok x => exact .inr ⟨x, rfl, h⟩

private theorem mem_set_or {T : Type} : ∀ {xs : List T} {k : Nat} {x y : T},
    y ∈ xs.set k x → y = x ∨ y ∈ xs
  | [], _, _, _, hy => False.elim (List.not_mem_nil hy)
  | _ :: _, 0, _, _, hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact .inl rfl
    · exact .inr (List.mem_cons_of_mem _ hy)
  | _ :: _, _ + 1, _, _, hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact .inr (List.mem_cons_self ..)
    · rcases mem_set_or hy with rfl | hy'
      · exact .inl rfl
      · exact .inr (List.mem_cons_of_mem _ hy')

private theorem mem_take_sub {T : Type} : ∀ {n : Nat} {xs : List T} {y : T},
    y ∈ xs.take n → y ∈ xs
  | 0, _, _, hy => False.elim (List.not_mem_nil hy)
  | _ + 1, [], _, hy => False.elim (List.not_mem_nil hy)
  | _ + 1, _ :: _, _, hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_take_sub hy)

private theorem mem_drop_sub {T : Type} : ∀ {n : Nat} {xs : List T} {y : T},
    y ∈ xs.drop n → y ∈ xs
  | 0, _, _, hy => hy
  | _ + 1, [], _, hy => False.elim (List.not_mem_nil hy)
  | _ + 1, _ :: _, _, hy => List.mem_cons_of_mem _ (mem_drop_sub hy)

private theorem listIndex_ok {T : Type} {xs : List T} {i : Int} {what : String} {x : T}
    (h : listIndex xs i what = .ok x) :
    0 ≤ i ∧ i.toNat < xs.length ∧ xs[i.toNat]? = some x := by
  unfold listIndex at h
  split at h
  · rename_i hge
    generalize hget : xs[i.toNat]? = opt at h
    cases opt with
    | none => cases h
    | some elem =>
      dsimp only at h
      obtain rfl := interp_pure_ok h
      exact ⟨hge, (List.getElem?_eq_some_iff.mp hget).1, rfl⟩
  · cases h

private theorem listSet_ok {T : Type} {xs : List T} {i : Int} {x : T} {what : String}
    {xs' : List T} (h : listSet xs i x what = .ok xs') :
    0 ≤ i ∧ i.toNat < xs.length ∧ xs' = xs.set i.toNat x := by
  unfold listSet at h
  split at h
  · rename_i hb
    exact ⟨hb.1, hb.2, (interp_pure_ok h).symm⟩
  · cases h

private theorem listMutateAt_ok {T O : Type} {xs : List T} {i : Int} {what : String}
    {f : T → Interp (O × T)} {out : O} {xs' : List T}
    (h : listMutateAt xs i what f = .ok (out, xs')) :
    ∃ elem elem', 0 ≤ i ∧ i.toNat < xs.length ∧ xs[i.toNat]? = some elem ∧
      f elem = .ok (out, elem') ∧ xs' = xs.set i.toNat elem' := by
  unfold listMutateAt at h
  obtain ⟨elem, hidx, h⟩ := bind_ok h
  obtain ⟨⟨o, elem'⟩, hf, h⟩ := bind_ok h
  obtain ⟨ys, hset, h⟩ := bind_ok h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
  obtain ⟨hge, hlt, hget⟩ := listIndex_ok hidx
  obtain ⟨_, _, rfl⟩ := listSet_ok hset
  exact ⟨elem, elem', hge, hlt, hget, hf, rfl⟩

private theorem writeSubsliceAtIndex_ok {T : Type} {xs : List T} {start : Int} {src ys : List T}
    (h : writeSubsliceAtIndex xs start src = .ok ys) :
    0 ≤ start ∧ start + src.length ≤ xs.length ∧
      ys.length = xs.length ∧ (∀ y ∈ ys, y ∈ xs ∨ y ∈ src) := by
  unfold writeSubsliceAtIndex at h
  split at h
  · rename_i hb
    obtain rfl := interp_pure_ok h
    refine ⟨hb.1, hb.2, ?_, fun y hy => ?_⟩
    · simp only [List.length_append, List.length_take, List.length_drop]
      omega
    · simp only [List.mem_append] at hy
      rcases hy with (hy | hy) | hy
      · exact .inl (mem_take_sub hy)
      · exact .inr hy
      · exact .inl (mem_drop_sub hy)
  · cases h

private theorem list_mapM_loop_ok {α β : Type} {f : α → Interp β} {P : β → Prop}
    (hf : ∀ x y, f x = .ok y → P y) :
    ∀ (xs : List α) (acc ys : List β),
      List.mapM.loop f xs acc = .ok ys →
      (∀ y ∈ acc, P y) →
      ys.length = acc.length + xs.length ∧ ∀ y ∈ ys, P y
  | [], acc, ys, h, hacc => by
    unfold List.mapM.loop at h
    obtain rfl := interp_pure_ok h
    exact ⟨by simp, fun y hy => hacc y (List.mem_reverse.mp hy)⟩
  | x :: xs, acc, ys, h, hacc => by
    unfold List.mapM.loop at h
    obtain ⟨b, hfx, h⟩ := bind_ok h
    obtain ⟨hlen, hP⟩ := list_mapM_loop_ok hf xs (b :: acc) ys h fun y hy => by
      rcases List.mem_cons.mp hy with hy_eq | hy
      · rw [hy_eq]
        exact hf x b hfx
      · exact hacc y hy
    exact ⟨by simp only [List.length_cons] at hlen ⊢; omega, hP⟩

/-- `Permission.transition` never raises `Stop.specPanic` (every failure is
well-typed Tree Borrows UB). -/
theorem Permission.transition_no_specPanic (p : Gen.Permission) (ak : Gen.AccessKind)
    (nr : Gen.NodeRelation) (msg : String) :
    Permission.transition p ak nr ≠ .error (.specPanic msg) := by
  cases p with
  | Unprot u =>
    cases nr <;> cases ak <;> cases u <;>
      simp [Permission.transition, PermissionUnprot.transition,
        PermissionUnprot.local_read, PermissionUnprot.local_write,
        PermissionUnprot.foreign_read, PermissionUnprot.foreign_write,
        pure, Except.pure, bind, Except.bind, ub]
  | Prot q =>
    cases nr <;> cases ak <;> cases q <;>
      repeat (first
        | simp [Permission.transition, PermissionProt.transition,
            PermissionProt.local_read, PermissionProt.local_write,
            PermissionProt.foreign_read, PermissionProt.foreign_write,
            pure, Except.pure, bind, Except.bind, ub]
        | (rename_i b; cases b))

/-- `Node.transitionRange` preserves permission-list byte length and
`Permission.matches_protector`. -/
theorem Node.transitionRange_wf (nr : Gen.NodeRelation) (ak : Gen.AccessKind)
    (prot : Gen.Protected) :
    ∀ (rem offset : Nat) (perms perms' : List Gen.Permission),
      (∀ p ∈ perms, Permission.matches_protector p prot = true) →
      Node.transitionRange nr ak offset rem perms = .ok perms' →
      perms'.length = perms.length ∧
      ∀ p ∈ perms', Permission.matches_protector p prot = true
  | 0, _, perms, perms', hmp, h => by
    unfold Node.transitionRange at h
    obtain rfl := interp_pure_ok h
    exact ⟨rfl, hmp⟩
  | rem + 1, offset, perms, perms', hmp, h => by
    unfold Node.transitionRange at h
    obtain ⟨⟨_, mid⟩, hm, h⟩ := bind_ok h
    obtain ⟨elem, elem', _, _, hget, hf, rfl⟩ := listMutateAt_ok hm
    obtain ⟨p', htr, hf⟩ := bind_ok hf
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hf)
    have helem : Permission.matches_protector p' prot = true :=
      Permission.transition_preserves_matches_protector
        (hmp elem (List.mem_of_getElem? hget)) htr
    have hmid : ∀ p ∈ perms.set (Int.ofNat offset).toNat p',
        Permission.matches_protector p prot = true := by
      intro p hp
      rcases mem_set_or hp with rfl | hp'
      · exact helem
      · exact hmp p hp'
    obtain ⟨hlen, hmp'⟩ := Node.transitionRange_wf nr ak prot rem (offset + 1) _ perms' hmid h
    exact ⟨hlen.trans (List.length_set ..), hmp'⟩

/-- In-bounds `Node.transitionRange` (`offset + rem ≤ perms.length`) never
raises `Stop.specPanic`. -/
theorem Node.transitionRange_no_specPanic (nr : Gen.NodeRelation) (ak : Gen.AccessKind)
    (msg : String) :
    ∀ (rem offset : Nat) (perms : List Gen.Permission),
      offset + rem ≤ perms.length →
      Node.transitionRange nr ak offset rem perms ≠ .error (.specPanic msg)
  | 0, _, _, _, h => by
    unfold Node.transitionRange at h
    cases h
  | rem + 1, offset, perms, hle, h => by
    unfold Node.transitionRange at h
    have hlt : offset < perms.length := by omega
    rcases bind_err h with hm | ⟨⟨_, mid⟩, hm, h⟩
    · unfold listMutateAt at hm
      obtain ⟨elem, hget⟩ : ∃ e, perms[offset]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
      have hidx : listIndex perms (Int.ofNat offset) "Node::transition" = .ok elem := by
        simp [listIndex, hget, pure, Except.pure]
      rcases bind_err hm with hidx_err | ⟨elem0, hidx0, hm⟩
      · rw [hidx] at hidx_err; cases hidx_err
      · rw [hidx] at hidx0; obtain rfl := Except.ok.inj hidx0
        rcases bind_err hm with hf_err | ⟨⟨_, elem'⟩, _, hset_err⟩
        · rcases bind_err hf_err with htr_err | ⟨_, _, hpure_err⟩
          · exact Permission.transition_no_specPanic elem ak nr msg htr_err
          · cases hpure_err
        · rcases bind_err hset_err with hs_err | ⟨_, _, hpure_err⟩
          · have hset_ok : listSet perms (Int.ofNat offset) elem' "Node::transition" =
                .ok (perms.set offset elem') := by
              simp [listSet, hlt, pure, Except.pure]
            rw [hset_ok] at hs_err; cases hs_err
          · cases hpure_err
    · obtain ⟨_, elem', _, _, _, _, rfl⟩ := listMutateAt_ok hm
      exact Node.transitionRange_no_specPanic nr ak msg rem (offset + 1)
        (perms.set (Int.ofNat offset).toNat elem') (by rw [List.length_set]; omega) h

/-- `Node.transition` preserves `Node.wf sz` (keeping child subtrees intact). -/
theorem Node.transition_wf {sz : Nat} {n n' : Gen.Node} {nr : Gen.NodeRelation}
    {ak : Gen.AccessKind} {offset : Gen.Offset} {size : Size}
    (hwf : Node.wf sz n) (h : Node.transition n nr ak offset size = .ok n') :
    Node.wf sz n' := by
  rcases n with ⟨children, perms, prot⟩
  obtain ⟨hlen, hmp, hch⟩ := hwf
  unfold Node.transition at h
  obtain ⟨perms', htr, h⟩ := bind_ok h
  obtain rfl := interp_pure_ok h
  obtain ⟨hlen', hmp'⟩ :=
    Node.transitionRange_wf nr ak prot size.bytes offset.bytes perms perms' hmp htr
  exact ⟨hlen'.trans hlen, hmp', hch⟩

mutual

/-- `Node.access` preserves `Node.wf sz` across the entire borrow tree. -/
theorem Node.access_wf {sz : Nat} :
    ∀ {n n' : Gen.Node} {path : Option Gen.Path} {ak : Gen.AccessKind}
      {offset : Gen.Offset} {size : Size},
      Node.wf sz n → Node.access n path ak offset size = .ok n' → Node.wf sz n'
  | ⟨children, permissions, prot⟩, n', path, ak, offset, size, hwf, h => by
    unfold Node.access at h
    obtain ⟨self1, htr, h⟩ := bind_ok h
    obtain ⟨children', hch, h⟩ := bind_ok h
    obtain rfl := interp_pure_ok h
    have hwf1 := Node.transition_wf hwf htr
    rcases self1 with ⟨_, perms1, prot1⟩
    exact ⟨hwf1.1, hwf1.2.1, Node.accessChildren_wf hwf.2.2 hch⟩

/-- `Node.accessChildren` preserves `Node.childrenWf sz`. -/
theorem Node.accessChildren_wf {sz : Nat} :
    ∀ {cs cs' : List Gen.Node} {childId : Int} {path : Option Gen.Path}
      {ak : Gen.AccessKind} {offset : Gen.Offset} {size : Size},
      Node.childrenWf sz cs →
      Node.accessChildren childId path ak offset size cs = .ok cs' →
      Node.childrenWf sz cs'
  | [], cs', _, _, _, _, _, _, h => by
    unfold Node.accessChildren at h
    obtain rfl := interp_pure_ok h
    trivial
  | c :: cs, cs', childId, path, ak, offset, size, ⟨hc, hcs⟩, h => by
    unfold Node.accessChildren at h
    obtain ⟨c', h1, h⟩ := bind_ok h
    obtain ⟨rest', h2, h⟩ := bind_ok h
    obtain rfl := interp_pure_ok h
    exact ⟨Node.access_wf hc h1, Node.accessChildren_wf hcs h2⟩

end

mutual

/-- On a well-formed node (`Node.wf sz n`), any in-bounds `Node.access`
(`offset.bytes + size.bytes ≤ sz`) never fails with `Stop.specPanic`. -/
theorem Node.access_no_specPanic {sz : Nat} :
    ∀ (n : Gen.Node) (path : Option Gen.Path) (ak : Gen.AccessKind)
      (offset : Gen.Offset) (size : Size) (msg : String),
      Node.wf sz n → offset.bytes + size.bytes ≤ sz →
      Node.access n path ak offset size ≠ .error (.specPanic msg)
  | ⟨children, permissions, prot⟩, path, ak, offset, size, msg, ⟨hlen, _, hch⟩, hle, h => by
    unfold Node.access at h
    rcases bind_err h with htr | ⟨self1, _, h⟩
    · unfold Node.transition at htr
      rcases bind_err htr with hrange | ⟨_, _, hpure⟩
      · exact Node.transitionRange_no_specPanic (if path.isSome then .Local else .Foreign)
          ak msg size.bytes offset.bytes permissions (by omega) hrange
      · cases hpure
    · rcases bind_err h with hcs | ⟨_, _, hpure⟩
      · exact Node.accessChildren_no_specPanic children 0 path ak offset size msg hch hle hcs
      · cases hpure

/-- In-bounds `Node.accessChildren` on well-formed children never raises
`Stop.specPanic`. -/
theorem Node.accessChildren_no_specPanic {sz : Nat} :
    ∀ (cs : List Gen.Node) (childId : Int) (path : Option Gen.Path)
      (ak : Gen.AccessKind) (offset : Gen.Offset) (size : Size) (msg : String),
      Node.childrenWf sz cs → offset.bytes + size.bytes ≤ sz →
      Node.accessChildren childId path ak offset size cs ≠ .error (.specPanic msg)
  | [], _, _, _, _, _, _, _, _, h => by
    unfold Node.accessChildren at h
    cases h
  | c :: cs, childId, path, ak, offset, size, msg, ⟨hc, hcs⟩, hle, h => by
    unfold Node.accessChildren at h
    rcases bind_err h with h1 | ⟨c', _, h⟩
    · exact Node.access_no_specPanic c _ ak offset size msg hc hle h1
    · rcases bind_err h with h2 | ⟨_, _, hpure⟩
      · exact Node.accessChildren_no_specPanic cs (childId + 1) path ak offset size msg hcs hle h2
      · cases hpure

end

/-- When `settings` satisfies `matches_protector settings.outside prot` and
`(∀ p ∈ settings.inside, matches_protector p prot)` (as established by
`ReborrowSettings.new_matches_protector`), splicing `settings.inside` into
`List.replicate allocSize settings.outside` yields a permission list that
satisfies `permissions.all (matches_protector · prot) = true` (proving the
assertion in `TreeBorrowsMemory.reborrow` unreachable for all
`ReborrowSettings.new` outputs). -/
theorem reborrow_childPermissions_matches_protector {s : Gen.ReborrowSettings}
    (hout : Permission.matches_protector s.outside s.«protected» = true)
    (hins : ∀ p ∈ s.inside, Permission.matches_protector p s.«protected» = true)
    (allocSize : Nat) :
    ((List.replicate allocSize s.outside).all
      (fun x => Permission.matches_protector x s.«protected») = true) ∧
    ∀ (offset : Int) (ys : List Gen.Permission),
      writeSubsliceAtIndex (List.replicate allocSize s.outside) offset s.inside = .ok ys →
      ys.all (fun x => Permission.matches_protector x s.«protected») = true := by
  have hrep : ∀ p ∈ List.replicate allocSize s.outside,
      Permission.matches_protector p s.«protected» = true := by
    intro p hp
    rw [List.eq_of_mem_replicate hp]
    exact hout
  refine ⟨List.all_eq_true.mpr hrep, fun offset ys hws => List.all_eq_true.mpr fun p hp => ?_⟩
  rcases (writeSubsliceAtIndex_ok hws).2.2.2 p hp with hp' | hp'
  · exact hrep p hp'
  · exact hins p hp'

/-- `Node.access_node` preserves `Node.wf sz` whenever `f` preserves `Node.wf sz`
at the visited target node. -/
theorem Node.access_node_wf {O : Type} {sz : Nat} {f : Gen.Node → Interp (O × Gen.Node)}
    (hf : ∀ u u' o, Node.wf sz u → f u = .ok (o, u') → Node.wf sz u') :
    ∀ (path : Gen.Path) {n n' : Gen.Node} {out : O},
      Node.wf sz n → Node.access_node f path n = .ok (out, n') → Node.wf sz n'
  | [], n, n', out, hwf, h => hf n n' out hwf h
  | subRootId :: subPath, ⟨children, permissions, prot⟩, n', out, ⟨hlen, hmp, hch⟩, h => by
    unfold Node.access_node at h
    split at h
    · cases h
    · obtain ⟨⟨o, children'⟩, hm, h⟩ := bind_ok h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
      obtain ⟨elem, elem', _, _, hget, hsub, rfl⟩ := listMutateAt_ok hm
      have hch_mem : ∀ {cs : List Gen.Node}, Node.childrenWf sz cs → ∀ c ∈ cs, Node.wf sz c := by
        intro cs hcs c hc
        induction cs with
        | nil => exact False.elim (List.not_mem_nil hc)
        | cons d ds ih =>
          rcases List.mem_cons.mp hc with rfl | hc
          · exact hcs.1
          · exact ih hcs.2 hc
      have helem' : Node.wf sz elem' :=
        Node.access_node_wf hf subPath (hch_mem hch elem (List.mem_of_getElem? hget)) hsub
      have hch_set : ∀ {cs : List Gen.Node} (k : Nat),
          Node.childrenWf sz cs → Node.childrenWf sz (cs.set k elem') := by
        intro cs k hcs
        induction cs generalizing k with
        | nil => trivial
        | cons d ds ih =>
          cases k with
          | zero => exact ⟨helem', hcs.2⟩
          | succ k => exact ⟨hcs.1, ih k hcs.2⟩
      exact ⟨hlen, hmp, hch_set subRootId.toNat hch⟩

private theorem childrenWf_append_singleton {sz : Nat} {child : Gen.Node}
    (hc : Node.wf sz child) :
    ∀ {cs : List Gen.Node}, Node.childrenWf sz cs → Node.childrenWf sz (cs ++ [child])
  | [], _ => ⟨hc, trivial⟩
  | _ :: _, ⟨hd, hds⟩ => ⟨hd, childrenWf_append_singleton hc hds⟩

/-- `Node.add_node` preserves `Node.wf sz` when both the parent tree and the
appended child node satisfy `Node.wf sz`. -/
theorem Node.add_node_wf {sz : Nat} {root root' child : Gen.Node} {parentPath childPath : Gen.Path}
    (hroot : Node.wf sz root) (hchild : Node.wf sz child)
    (h : Node.add_node root parentPath child = .ok (childPath, root')) :
    Node.wf sz root' := by
  unfold Node.add_node at h
  obtain ⟨⟨idx, r1⟩, hm, h⟩ := bind_ok h
  obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
  refine Node.access_node_wf (fun u u' o hu hfu => ?_) parentPath hroot hm
  rcases u with ⟨uch, uperms, uprot⟩
  obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hfu)
  exact ⟨hu.1, hu.2.1, childrenWf_append_singleton hchild hu.2.2⟩

/-- `TreeBorrowsMemory.reborrowInitAccess` preserves `Node.wf sz`. -/
theorem TreeBorrowsMemory.reborrowInitAccess_wf {sz : Nat} (childPath : Gen.Path)
    (offset : Gen.Offset) :
    ∀ (idx : Nat) (inside : List Gen.Permission) {root root' : Gen.Node},
      Node.wf sz root →
      TreeBorrowsMemory.reborrowInitAccess childPath offset idx inside root = .ok root' →
      Node.wf sz root'
  | _, [], _, _, hwf, h => by
    unfold TreeBorrowsMemory.reborrowInitAccess at h
    obtain rfl := interp_pure_ok h
    exact hwf
  | idx, perm :: rest, root, root', hwf, h => by
    unfold TreeBorrowsMemory.reborrowInitAccess at h
    dsimp only at h
    cases hp : Permission.init_access perm with
    | none =>
      simp only [hp, pure, Except.pure, bind, Except.bind] at h
      exact TreeBorrowsMemory.reborrowInitAccess_wf childPath offset (idx + 1) rest hwf h
    | some access =>
      simp only [hp] at h
      obtain ⟨root1, hstep, h⟩ := bind_ok h
      exact TreeBorrowsMemory.reborrowInitAccess_wf childPath offset (idx + 1) rest
        (Node.access_wf hwf hstep) h

/-- `TreeBorrowsMemory.new` constructs an empty, well-formed Tree Borrows memory. -/
theorem TreeBorrowsMemory.new_wf (params : Gen.TreeBorrowsParams) :
    TreeBorrowsMemory.wf (TreeBorrowsMemory.new params) := by
  intro alloc hm
  exact False.elim (List.not_mem_nil hm)

/-- `TreeBorrowsMemory.allocate` preserves `TreeBorrowsMemory.wf` (initializing a
fresh unprotected `.Unique` root node of byte length `size.bytes`). -/
theorem TreeBorrowsMemory.allocate_wf {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {kind : Gen.AllocationKind} {size : Size} {align : Align}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance}
    (hwf : TreeBorrowsMemory.wf tbm)
    (h : TreeBorrowsMemory.allocate tbm kind size align = .ok (ptr, tbm')) :
    TreeBorrowsMemory.wf tbm' := by
  unfold TreeBorrowsMemory.allocate at h
  obtain ⟨⟨ptr1, mem'⟩, halloc, h⟩ := bind_ok h
  dsimp only at h
  obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
  unfold BasicMemory.allocate at halloc
  split at halloc
  · cases halloc
  · cases hpick : BasicMemory.pickAddr tbm.mem size align with
    | none =>
      simp only [hpick] at halloc
      cases halloc
    | some addr =>
      simp only [hpick] at halloc
      obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok halloc)
      intro alloc hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hwf alloc hm
      · rw [List.mem_singleton.mp hm]
        refine ⟨by simp [Allocation.size], fun p hp => ?_, trivial⟩
        rw [List.eq_of_mem_replicate hp]
        rfl

/-- `TreeBorrowsMemory.load` preserves `TreeBorrowsMemory.wf`. -/
theorem TreeBorrowsMemory.load_wf {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} {len : Size} {align : Align}
    {bytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)}
    (hwf : TreeBorrowsMemory.wf tbm)
    (h : TreeBorrowsMemory.load tbm ptr len align = .ok (bytes, tbm')) :
    TreeBorrowsMemory.wf tbm' := by
  unfold TreeBorrowsMemory.load at h
  obtain ⟨⟨bs, mem'⟩, hload, h⟩ := bind_ok h
  obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
  unfold BasicMemory.load at hload
  split at hload
  · cases hload
  · obtain ⟨opt, hck, hload⟩ := bind_ok hload
    cases opt with
    | none =>
      obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hload)
      exact hwf
    | some triple =>
      rcases triple with ⟨id, provExtra, offset⟩
      obtain ⟨allocation, hidx, hload⟩ := bind_ok hload
      obtain ⟨extra', hextra, hload⟩ := bind_ok hload
      obtain ⟨allocations', hset, hload⟩ := bind_ok hload
      obtain ⟨_, _, hload⟩ := bind_ok hload
      obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hload)
      obtain ⟨root', hacc, hextra⟩ := bind_ok hextra
      obtain rfl := interp_pure_ok hextra
      obtain ⟨_, _, rfl⟩ := listSet_ok hset
      obtain ⟨_, _, hget⟩ := listIndex_ok hidx
      intro alloc hm
      rcases mem_set_or hm with rfl | hm'
      · exact Node.access_wf (hwf allocation (List.mem_of_getElem? hget)) hacc
      · exact hwf alloc hm'

/-- `TreeBorrowsMemory.store` preserves `TreeBorrowsMemory.wf` (since
`writeSubsliceAtIndex` preserves `allocation.data.length`). -/
theorem TreeBorrowsMemory.store_wf {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance}
    {bytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)} {align : Align}
    (hwf : TreeBorrowsMemory.wf tbm)
    (h : TreeBorrowsMemory.store tbm ptr bytes align = .ok tbm') :
    TreeBorrowsMemory.wf tbm' := by
  unfold TreeBorrowsMemory.store at h
  obtain ⟨mem', hstore, h⟩ := bind_ok h
  obtain rfl := interp_pure_ok h
  unfold BasicMemory.store at hstore
  split at hstore
  · cases hstore
  · obtain ⟨opt, hck, hstore⟩ := bind_ok hstore
    cases opt with
    | none =>
      obtain rfl := interp_pure_ok hstore
      exact hwf
    | some triple =>
      rcases triple with ⟨id, provExtra, offset⟩
      obtain ⟨allocation, hidx, hstore⟩ := bind_ok hstore
      obtain ⟨extra', hextra, hstore⟩ := bind_ok hstore
      obtain ⟨data', hws, hstore⟩ := bind_ok hstore
      obtain ⟨allocations', hset, hstore⟩ := bind_ok hstore
      obtain rfl := interp_pure_ok hstore
      obtain ⟨root', hacc, hextra⟩ := bind_ok hextra
      obtain rfl := interp_pure_ok hextra
      obtain ⟨_, _, rfl⟩ := listSet_ok hset
      obtain ⟨_, _, hget⟩ := listIndex_ok hidx
      have hdata_len := (writeSubsliceAtIndex_ok hws).2.2.1
      intro alloc hm
      rcases mem_set_or hm with rfl | hm'
      · dsimp only [Allocation.size]
        rw [hdata_len]
        exact Node.access_wf (hwf allocation (List.mem_of_getElem? hget)) hacc
      · exact hwf alloc hm'

/-- `TreeBorrowsMemory.deallocate` preserves `TreeBorrowsMemory.wf`. -/
theorem TreeBorrowsMemory.deallocate_wf {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} {kind : Gen.AllocationKind}
    {size : Size} {align : Align}
    (hwf : TreeBorrowsMemory.wf tbm)
    (h : TreeBorrowsMemory.deallocate tbm ptr kind size align = .ok tbm') :
    TreeBorrowsMemory.wf tbm' := by
  unfold TreeBorrowsMemory.deallocate at h
  obtain ⟨mem', hdealloc, h⟩ := bind_ok h
  obtain rfl := interp_pure_ok h
  unfold BasicMemory.deallocate at hdealloc
  cases hprov : ptr.provenance with
  | none =>
    simp only [hprov] at hdealloc
    cases hdealloc
  | some pair =>
    rcases pair with ⟨id, provExtra⟩
    simp only [hprov] at hdealloc
    obtain ⟨allocation, hidx, hdealloc⟩ := bind_ok hdealloc
    split at hdealloc; · cases hdealloc
    split at hdealloc; · cases hdealloc
    split at hdealloc; · dsimp only [ub] at hdealloc; cases hdealloc
    split at hdealloc; · cases hdealloc
    split at hdealloc; · cases hdealloc
    obtain ⟨extra', hextra, hdealloc⟩ := bind_ok hdealloc
    obtain ⟨allocations', hset, hdealloc⟩ := bind_ok hdealloc
    obtain rfl := interp_pure_ok hdealloc
    obtain ⟨root', hacc, hextra⟩ := bind_ok hextra
    split at hextra; · cases hextra
    obtain rfl := interp_pure_ok hextra
    obtain ⟨_, _, rfl⟩ := listSet_ok hset
    obtain ⟨_, _, hget⟩ := listIndex_ok hidx
    intro alloc hm
    rcases mem_set_or hm with rfl | hm'
    · exact Node.access_wf (hwf allocation (List.mem_of_getElem? hget)) hacc
    · exact hwf alloc hm'

/-- `TreeBorrowsMemory.reborrow` unconditionally preserves `TreeBorrowsMemory.wf`
on every `.ok` step (guarded by `writeSubsliceAtIndex` length preservation,
`Permission.matches_protector` validation, `Node.add_node_wf`, and
`reborrowInitAccess_wf`). -/
theorem TreeBorrowsMemory.reborrow_wf {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {ptr ptr' : Gen.ThinPointer Gen.TreeBorrowsProvenance} {settings : Gen.ReborrowSettings}
    {fe fe' : Gen.TreeBorrowsFrameExtra}
    (hwf : TreeBorrowsMemory.wf tbm)
    (h : TreeBorrowsMemory.reborrow tbm ptr settings fe = .ok (ptr', tbm', fe')) :
    TreeBorrowsMemory.wf tbm' := by
  unfold TreeBorrowsMemory.reborrow at h
  dsimp only at h
  obtain ⟨_, hck, h⟩ := bind_ok h
  cases hprov : ptr.provenance with
  | none =>
    simp only [hprov] at h
    split at h
    · cases h
    · obtain ⟨_, h⟩ := Prod.mk.inj (interp_pure_ok h)
      obtain ⟨rfl, _⟩ := Prod.mk.inj h
      exact hwf
  | some pair =>
    rcases pair with ⟨allocId, parentPath⟩
    simp only [hprov] at h
    obtain ⟨⟨childPath, allocations'⟩, hm, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨_, h⟩ := Prod.mk.inj (interp_pure_ok h)
    obtain ⟨rfl, _⟩ := Prod.mk.inj h
    obtain ⟨allocation, alloc', _, _, hget, hf, rfl⟩ := listMutateAt_ok hm
    cases hoff : Size.from_bytes (ptr.addr - allocation.addr) with
    | none =>
      simp [hoff, specPanic, bind, Except.bind] at hf
    | some offset =>
      simp only [hoff, pure, Except.pure, bind, Except.bind] at hf
      have hbody : ∀ (permissions : List Gen.Permission),
          permissions.length = (Allocation.size allocation).bytes →
          (let childNode : Gen.Node :=
            { children := [], permissions := permissions, «protected» := settings.«protected» }
           if (!childNode.permissions.all fun x =>
               Permission.matches_protector x childNode.«protected») = true then
             specPanic
               "assertion failed: child_node.permissions.all(|x| x.matches_protector(child_node.protected))"
           else do
             let (cp, root1) ← Node.add_node allocation.extra.root parentPath childNode
             let root2 ← TreeBorrowsMemory.reborrowInitAccess cp offset 0 settings.inside root1
             pure (cp, { data := allocation.data, addr := allocation.addr, align := allocation.align,
                         kind := allocation.kind, live := allocation.live, extra := { root := root2 } })) =
            .ok (childPath, alloc') →
          TreeBorrowsMemory.wf
            { params := tbm.params,
              mem := { allocations := tbm.mem.allocations.set allocId._0.toNat alloc',
                       _phantom := tbm.mem._phantom } } := by
        intro permissions hplen hfb
        dsimp only at hfb
        cases hall : permissions.all (fun x => Permission.matches_protector x settings.«protected») with
        | false =>
          simp only [hall, Bool.not_false, ↓reduceIte] at hfb
          cases hfb
        | true =>
          simp only [hall, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfb
          obtain ⟨⟨cp, root1⟩, hadd, hfb⟩ := bind_ok hfb
          dsimp only at hfb
          obtain ⟨root2, hinit, hfb⟩ := bind_ok hfb
          obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hfb)
          have hchild_wf : Node.wf (Allocation.size allocation).bytes
              { children := [], permissions := permissions, «protected» := settings.«protected» } :=
            ⟨hplen, List.all_eq_true.mp hall, trivial⟩
          have hr1 := Node.add_node_wf (hwf allocation (List.mem_of_getElem? hget)) hchild_wf hadd
          have hr2 := TreeBorrowsMemory.reborrowInitAccess_wf cp offset 0 settings.inside hr1 hinit
          intro alloc hm'
          rcases mem_set_or hm' with rfl | hm''
          · exact hr2
          · exact hwf alloc hm''
      by_cases hgt : settings.inside.length > 0
      · simp only [hgt, ↓reduceIte] at hf
        obtain ⟨permissions, hps, hf⟩ := bind_ok hf
        exact hbody permissions ((writeSubsliceAtIndex_ok hps).2.2.1.trans (List.length_replicate ..)) hf
      · simp only [hgt, ↓reduceIte] at hf
        exact hbody _ (List.length_replicate ..) hf

/-- `TreeBorrowsMemory.retag_ptr` preserves `TreeBorrowsMemory.wf`. -/
theorem TreeBorrowsMemory.retag_ptr_wf {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {fe fe' : Gen.TreeBorrowsFrameExtra} {ptr ptr' : Gen.Pointer Gen.TreeBorrowsProvenance}
    {ptrType : Gen.PtrType} {fnEntry fnImplicitWrites : Bool}
    {vtableLookup : Gen.ThinPointer Gen.TreeBorrowsProvenance → Interp Gen.VTable}
    (hwf : TreeBorrowsMemory.wf tbm)
    (h : TreeBorrowsMemory.retag_ptr tbm fe ptr ptrType fnEntry fnImplicitWrites vtableLookup =
      .ok (ptr', tbm', fe')) :
    TreeBorrowsMemory.wf tbm' := by
  unfold TreeBorrowsMemory.retag_ptr at h
  obtain ⟨opt, hs, h⟩ := bind_ok h
  cases opt with
  | none =>
    obtain ⟨_, h⟩ := Prod.mk.inj (interp_pure_ok h)
    obtain ⟨rfl, _⟩ := Prod.mk.inj h
    exact hwf
  | some perms =>
    obtain ⟨⟨thin', tbm1, fe1⟩, hreb, h⟩ := bind_ok h
    obtain ⟨_, h⟩ := Prod.mk.inj (interp_pure_ok h)
    obtain ⟨rfl, _⟩ := Prod.mk.inj h
    exact TreeBorrowsMemory.reborrow_wf hwf hreb

/-- Non-ZST relative-offset and slice-bounds safety of `BasicMemory.check_ptr`
inside `TreeBorrowsMemory.reborrow`: whenever `settings.inside.length > 0`
(a non-zero-sized pointee), `BasicMemory.check_ptr` guarantees that
`ptr.addr - allocation.addr ≥ 0` (so `Size.from_bytes` returns `some offset` and
`Offset::from_bytes(...).unwrap()` cannot panic!) AND
`offset.bytes + settings.inside.length ≤ (Allocation.size allocation).bytes`
(so `writeSubsliceAtIndex` cannot panic either!). By contrast, for a ZST
reference (`settings.inside = []`), `BasicMemory.check_ptr` returns `Ok(None)`
immediately without checking `ptr.addr ≥ allocation.addr`, allowing
`Offset::from_bytes(ptr.addr - allocation.addr).unwrap()` to hit `Stop.specPanic`
on negative-offset `wrapping_offset` pointers (exhibited in `TbWitness.lean`). -/
theorem TreeBorrowsMemory.reborrow_nonzst_no_offset_panic
    {tbm : Gen.TreeBorrowsMemory Gen.x86_64}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance}
    {allocId : Gen.AllocId} {parentPath : Gen.Path}
    {settings : Gen.ReborrowSettings}
    {opt : Option (Gen.AllocId × Gen.Path × Size)}
    (hpos : settings.inside.length > 0)
    (hprov : ptr.provenance = some (allocId, parentPath))
    (hck : BasicMemory.check_ptr tbm.mem ptr ⟨settings.inside.length⟩ = .ok opt) :
    ∃ (allocation : _) (offset : Size),
      listIndex tbm.mem.allocations allocId._0 "TreeBorrowsMemory::reborrow" = .ok allocation ∧
      allocation.live = true ∧
      Size.from_bytes (ptr.addr - allocation.addr) = some offset ∧
      offset.bytes + settings.inside.length ≤ (Allocation.size allocation).bytes := by
  unfold BasicMemory.check_ptr at hck
  have hnz : ¬(⟨settings.inside.length⟩ : Size).bytes = 0 := by dsimp; omega
  simp only [hnz, ↓reduceIte, hprov] at hck
  obtain ⟨allocation, hidx, hck⟩ := bind_ok hck
  obtain ⟨hge, _, hget⟩ := listIndex_ok hidx
  have hidx2 : listIndex tbm.mem.allocations allocId._0 "TreeBorrowsMemory::reborrow" =
      .ok allocation := by
    simp [listIndex, hge, hget, pure, Except.pure]
  cases hlive : allocation.live with
  | false =>
    simp only [hlive, Bool.not_false, ↓reduceIte] at hck
    cases hck
  | true =>
    simp only [hlive, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hck
    split at hck
    · cases hck
    · rename_i hbounds
      have hoff_nn : (0 : Int) ≤ ptr.addr - allocation.addr :=
        Int.not_lt.mp fun h => hbounds (.inl h)
      have h2 : ¬(ptr.addr - allocation.addr + (settings.inside.length : Int) >
          ((Allocation.size allocation).bytes : Int)) := fun h => hbounds (.inr h)
      refine ⟨allocation, ⟨(ptr.addr - allocation.addr).toNat⟩, hidx2, hlive, ?_, ?_⟩
      · unfold Size.from_bytes
        simp only [hoff_nn, ↓reduceIte]
      · change (ptr.addr - allocation.addr).toNat + settings.inside.length ≤
            (Allocation.size allocation).bytes
        omega

mutual

/-- Intermediate borrow-tree invariant after Step 1 of
`TreeBorrowsMemory.release_protector`: the node at `path` has already had its
`permissions` mapped through `Permission.unprotect` (so they have length `sz` and
match `.No`), while every other node in the tree satisfies `Node.wf sz`. -/
def Node.wfUnprotAt (sz : Nat) : Gen.Path → Gen.Node → Prop
  | [], ⟨children, permissions, _⟩ =>
    permissions.length = sz ∧
    (∀ p ∈ permissions, Permission.matches_protector p .No = true) ∧
    Node.childrenWf sz children
  | idx :: rest, ⟨children, permissions, prot⟩ =>
    permissions.length = sz ∧
    (∀ p ∈ permissions, Permission.matches_protector p prot = true) ∧
    Node.childrenWfUnprotAt sz idx rest 0 children

/-- Child-list invariant locating the unique child `target` along `idx :: rest`. -/
def Node.childrenWfUnprotAt (sz : Nat) (target : Int) (rest : Gen.Path) :
    Nat → List Gen.Node → Prop
  | _, [] => False
  | cur, c :: cs =>
    (target = Int.ofNat cur ∧ Node.wfUnprotAt sz rest c ∧ Node.childrenWf sz cs) ∨
    (target ≠ Int.ofNat cur ∧ Node.wf sz c ∧ Node.childrenWfUnprotAt sz target rest (cur + 1) cs)

end

/-- `Node.releaseProtectorPermissions` preserves byte length and
`Permission.matches_protector`. -/
theorem Node.releaseProtectorPermissions_wf (nr : Gen.NodeRelation) (prot : Gen.Protected) :
    ∀ (accesses : List (Option Gen.AccessKind)) (offset : Nat)
      (perms perms' : List Gen.Permission),
      (∀ p ∈ perms, Permission.matches_protector p prot = true) →
      Node.releaseProtectorPermissions nr offset accesses perms = .ok perms' →
      perms'.length = perms.length ∧
      ∀ p ∈ perms', Permission.matches_protector p prot = true
  | [], _, perms, perms', hmp, h => by
    unfold Node.releaseProtectorPermissions at h
    obtain rfl := interp_pure_ok h
    exact ⟨rfl, hmp⟩
  | none :: rest, offset, perms, perms', hmp, h =>
    Node.releaseProtectorPermissions_wf nr prot rest (offset + 1) perms perms' hmp h
  | some access :: rest, offset, perms, perms', hmp, h => by
    unfold Node.releaseProtectorPermissions at h
    obtain ⟨⟨_, mid⟩, hm, h⟩ := bind_ok h
    obtain ⟨elem, elem', _, _, hget, hf, rfl⟩ := listMutateAt_ok hm
    obtain ⟨p', htr, hf⟩ := bind_ok hf
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hf)
    have helem : Permission.matches_protector p' prot = true :=
      Permission.transition_preserves_matches_protector
        (hmp elem (List.mem_of_getElem? hget)) htr
    have hmid : ∀ p ∈ perms.set (Int.ofNat offset).toNat p',
        Permission.matches_protector p prot = true := by
      intro p hp
      rcases mem_set_or hp with rfl | hp'
      · exact helem
      · exact hmp p hp'
    obtain ⟨hlen, hmp'⟩ :=
      Node.releaseProtectorPermissions_wf nr prot rest (offset + 1) _ perms' hmid h
    exact ⟨hlen.trans (List.length_set ..), hmp'⟩

mutual

/-- Foreign (`path = none`) `Node.release_protector` preserves `Node.wf sz`. -/
theorem Node.release_protector_none_wf {sz : Nat} :
    ∀ {n n' : Gen.Node} {accesses : List (Option Gen.AccessKind)},
      Node.wf sz n → Node.release_protector n none accesses = .ok n' → Node.wf sz n'
  | ⟨children, permissions, prot⟩, n', accesses, ⟨hlen, hmp, hch⟩, h => by
    unfold Node.release_protector at h
    obtain ⟨perms', hp, h⟩ := bind_ok h
    obtain ⟨children', hcs, h⟩ := bind_ok h
    obtain rfl := interp_pure_ok h
    obtain ⟨hlen', hmp'⟩ :=
      Node.releaseProtectorPermissions_wf .Foreign prot accesses 0 permissions perms' hmp hp
    exact ⟨hlen'.trans hlen, hmp', Node.releaseProtectorChildren_none_wf hch hcs⟩

/-- Foreign (`path = none`) `Node.releaseProtectorChildren` preserves
`Node.childrenWf sz`. -/
theorem Node.releaseProtectorChildren_none_wf {sz : Nat} :
    ∀ {cs cs' : List Gen.Node} {childId : Int} {accesses : List (Option Gen.AccessKind)},
      Node.childrenWf sz cs →
      Node.releaseProtectorChildren childId none accesses cs = .ok cs' →
      Node.childrenWf sz cs'
  | [], cs', _, _, _, h => by
    unfold Node.releaseProtectorChildren at h
    obtain rfl := interp_pure_ok h
    trivial
  | c :: cs, cs', childId, accesses, ⟨hc, hcs⟩, h => by
    unfold Node.releaseProtectorChildren at h
    obtain ⟨c', h1, h⟩ := bind_ok h
    obtain ⟨rest', h2, h⟩ := bind_ok h
    obtain rfl := interp_pure_ok h
    exact ⟨Node.release_protector_none_wf hc h1,
      Node.releaseProtectorChildren_none_wf hcs h2⟩

end

private theorem releaseProtectorChildren_gt_wf {sz : Nat} (head : Int) (tail : Gen.Path)
    (accesses : List (Option Gen.AccessKind)) :
    ∀ {cs cs' : List Gen.Node} (childId : Int),
      head < childId → Node.childrenWf sz cs →
      Node.releaseProtectorChildren childId (some (head :: tail)) accesses cs = .ok cs' →
      Node.childrenWf sz cs'
  | [], cs', _, _, _, h => by
    unfold Node.releaseProtectorChildren at h
    obtain rfl := interp_pure_ok h
    trivial
  | c :: cs, cs', childId, hlt, ⟨hc, hcs⟩, h => by
    unfold Node.releaseProtectorChildren at h
    have hne : (head == childId) = false := beq_false_of_ne (by omega)
    simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨c', h1, h⟩ := bind_ok h
    obtain ⟨rest', h2, h⟩ := bind_ok h
    obtain rfl := interp_pure_ok h
    exact ⟨Node.release_protector_none_wf hc h1,
      releaseProtectorChildren_gt_wf head tail accesses (childId + 1) (by omega) hcs h2⟩

mutual

/-- Step 2 of `TreeBorrowsMemory.release_protector`: `Node.release_protector`
clears `protected := .No` at `path` and transitions all other nodes, restoring
`Node.wf sz` from `Node.wfUnprotAt sz path`. -/
theorem Node.release_protector_some_wf {sz : Nat} :
    ∀ (path : Gen.Path) {n n' : Gen.Node} {accesses : List (Option Gen.AccessKind)},
      Node.wfUnprotAt sz path n →
      Node.release_protector n (some path) accesses = .ok n' →
      Node.wf sz n'
  | [], ⟨children, permissions, prot⟩, n', _, hwf, h => by
    unfold Node.release_protector at h
    dsimp only at h
    obtain rfl := interp_pure_ok h
    exact hwf
  | head :: tail, ⟨children, permissions, prot⟩, n', accesses, ⟨hlen, hmp, hch⟩, h => by
    unfold Node.release_protector at h
    simp only [Option.isSome_some, ↓reduceIte] at h
    obtain ⟨perms', hp, h⟩ := bind_ok h
    obtain ⟨children', hcs, h⟩ := bind_ok h
    obtain rfl := interp_pure_ok h
    obtain ⟨hlen', hmp'⟩ :=
      Node.releaseProtectorPermissions_wf .Local prot accesses 0 permissions perms' hmp hp
    exact ⟨hlen'.trans hlen, hmp',
      Node.releaseProtectorChildren_some_wf head tail 0 hch hcs⟩

/-- Child-list companion to `Node.release_protector_some_wf`. -/
theorem Node.releaseProtectorChildren_some_wf {sz : Nat} (head : Int) (tail : Gen.Path) :
    ∀ (cur : Nat) {cs cs' : List Gen.Node} {accesses : List (Option Gen.AccessKind)},
      Node.childrenWfUnprotAt sz head tail cur cs →
      Node.releaseProtectorChildren (Int.ofNat cur) (some (head :: tail)) accesses cs = .ok cs' →
      Node.childrenWf sz cs'
  | _, [], _, _, hch, _ => False.elim hch
  | cur, c :: cs, cs', accesses, hch, h => by
    unfold Node.releaseProtectorChildren at h
    rcases hch with ⟨rfl, hc, hcs⟩ | ⟨hne, hc, hcs⟩
    · simp only [beq_self_eq_true, ↓reduceIte] at h
      obtain ⟨c', h1, h⟩ := bind_ok h
      obtain ⟨rest', h2, h⟩ := bind_ok h
      obtain rfl := interp_pure_ok h
      exact ⟨Node.release_protector_some_wf tail hc h1,
        releaseProtectorChildren_gt_wf (Int.ofNat cur) tail accesses (Int.ofNat cur + 1)
          (by omega) hcs h2⟩
    · have hbeq : (head == Int.ofNat cur) = false := beq_false_of_ne hne
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨c', h1, h⟩ := bind_ok h
      obtain ⟨rest', h2, h⟩ := bind_ok h
      obtain rfl := interp_pure_ok h
      have hcur : Int.ofNat cur + 1 = Int.ofNat (cur + 1) := rfl
      rw [hcur] at h2
      exact ⟨Node.release_protector_none_wf hc h1,
        Node.releaseProtectorChildren_some_wf head tail (cur + 1) hcs h2⟩

end

private theorem childrenWfUnprotAt_of_set {sz : Nat} {subPath : Gen.Path} {elem' : Gen.Node}
    (helem' : Node.wfUnprotAt sz subPath elem') :
    ∀ (cs : List Gen.Node) (cur k : Nat),
      k < cs.length → Node.childrenWf sz cs →
      Node.childrenWfUnprotAt sz (Int.ofNat (cur + k)) subPath cur (cs.set k elem')
  | [], _, _, hk, _ => by simp at hk
  | _ :: cs, cur, 0, _, ⟨_, hcs⟩ =>
    .inl ⟨by simp, helem', hcs⟩
  | c :: cs, cur, k + 1, hk, ⟨hc, hcs⟩ => by
    have hlt : k < cs.length := by simp at hk; omega
    have hadd : cur + (k + 1) = cur + 1 + k := by omega
    rw [hadd]
    have hne : Int.ofNat (cur + 1 + k) ≠ Int.ofNat cur := by
      intro heq
      injection heq with heq
      omega
    exact .inr ⟨hne, hc, childrenWfUnprotAt_of_set helem' cs (cur + 1) k hlt hcs⟩

private theorem access_node_wfUnprotAt {O : Type} {sz : Nat} {f : Gen.Node → Interp (O × Gen.Node)}
    (hf : ∀ u u' o, Node.wf sz u → f u = .ok (o, u') → Node.wfUnprotAt sz [] u') :
    ∀ (path : Gen.Path) {n n' : Gen.Node} {out : O},
      Node.wf sz n → Node.access_node f path n = .ok (out, n') → Node.wfUnprotAt sz path n'
  | [], n, n', out, hwf, h => hf n n' out hwf h
  | subRootId :: subPath, ⟨children, permissions, prot⟩, n', out, ⟨hlen, hmp, hch⟩, h => by
    unfold Node.access_node at h
    split at h
    · cases h
    · obtain ⟨⟨o, children'⟩, hm, h⟩ := bind_ok h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
      obtain ⟨elem, elem', hge, hlt, hget, hsub, rfl⟩ := listMutateAt_ok hm
      have hch_mem : ∀ {cs : List Gen.Node}, Node.childrenWf sz cs → ∀ c ∈ cs, Node.wf sz c := by
        intro cs hcs c hc
        induction cs with
        | nil => exact False.elim (List.not_mem_nil hc)
        | cons d ds ih =>
          rcases List.mem_cons.mp hc with rfl | hc
          · exact hcs.1
          · exact ih hcs.2 hc
      have helem' := access_node_wfUnprotAt hf subPath
        (hch_mem hch elem (List.mem_of_getElem? hget)) hsub
      have hcwf := childrenWfUnprotAt_of_set helem' children 0 subRootId.toNat hlt hch
      have hid : Int.ofNat (0 + subRootId.toNat) = subRootId := by
        rw [Nat.zero_add]
        exact Int.toNat_of_nonneg hge
      rw [hid] at hcwf
      exact ⟨hlen, hmp, hcwf⟩

/-- `TreeBorrowsMemory.release_protector` preserves `TreeBorrowsMemory.wfLive`:
every live allocation's borrow tree remains well-formed after unprotecting the
node at `provenance.2` and releasing its protector across the tree. -/
theorem TreeBorrowsMemory.release_protector_wfLive
    {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {provenance : Gen.TreeBorrowsProvenance}
    (hwf : TreeBorrowsMemory.wfLive tbm)
    (h : TreeBorrowsMemory.release_protector tbm provenance = .ok tbm') :
    TreeBorrowsMemory.wfLive tbm' := by
  rcases provenance with ⟨allocId, path⟩
  unfold TreeBorrowsMemory.release_protector at h
  obtain ⟨⟨_, allocations'⟩, hpair, h⟩ := bind_ok h
  dsimp only at h
  obtain rfl := interp_pure_ok h
  obtain ⟨allocation, alloc', _, _, hget, hf, rfl⟩ := listMutateAt_ok hpair
  intro alloc hm' hlive
  rcases mem_set_or hm' with rfl | hm''
  · obtain ⟨⟨protectorAccesses, root1⟩, hacc, hf⟩ := bind_ok hf
    cases halloc_live : allocation.live with
    | false =>
      simp only [halloc_live, Bool.not_false, ↓reduceIte] at hf
      obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hf)
      simp at hlive
    | true =>
      simp only [halloc_live, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hf
      obtain ⟨root2, hrel, hf⟩ := bind_ok hf
      obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hf)
      have hroot0 := hwf allocation (List.mem_of_getElem? hget) halloc_live
      have hroot1 : Node.wfUnprotAt (Allocation.size allocation).bytes path root1 := by
        refine access_node_wfUnprotAt (fun u u' o hu hfu => ?_) path hroot0 hacc
        rcases u with ⟨uch, uperms, uprot⟩
        cases hy : Protected.yes uprot with
        | false =>
          simp only [hy, Bool.not_false, ↓reduceIte] at hfu
          cases hfu
        | true =>
          simp only [hy, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfu
          obtain ⟨pairs, hmap, hfu⟩ := bind_ok hfu
          obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hfu)
          have hunp : ∀ x y, Permission.unprotect x = .ok y →
              Permission.matches_protector y.1 .No = true := by
            intro x y hx
            cases x with
            | Unprot _ => cases hx
            | Prot q =>
              obtain rfl := interp_pure_ok hx
              rfl
          obtain ⟨hpairs_len, hpairs_mp⟩ := list_mapM_loop_ok hunp uperms [] pairs hmap
            (fun _ hy' => False.elim (List.not_mem_nil hy'))
          refine ⟨by simp [hpairs_len, hu.1], fun p hp => ?_, hu.2.2⟩
          obtain ⟨pair, hpm, rfl⟩ := List.mem_map.mp hp
          exact hpairs_mp pair hpm
      exact Node.release_protector_some_wf path hroot1 hrel
  · exact hwf alloc hm'' hlive

/-- `TreeBorrowsMemory.end_call` preserves `TreeBorrowsMemory.wfLive` across the
frame's entire `protectors` release list. -/
theorem TreeBorrowsMemory.end_call_wfLive {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {extra : Gen.TreeBorrowsFrameExtra}
    (hwf : TreeBorrowsMemory.wfLive tbm)
    (h : TreeBorrowsMemory.end_call tbm extra = .ok tbm') :
    TreeBorrowsMemory.wfLive tbm' := by
  unfold TreeBorrowsMemory.end_call at h
  have key : ∀ (ps : List Gen.TreeBorrowsProvenance)
      {acc out : Gen.TreeBorrowsMemory Gen.x86_64},
      TreeBorrowsMemory.wfLive acc →
      ps.foldlM (fun a prov => TreeBorrowsMemory.release_protector a prov) acc = .ok out →
      TreeBorrowsMemory.wfLive out := by
    intro ps
    induction ps with
    | nil =>
      intro acc out hacc hf
      rw [List.foldlM_nil] at hf
      obtain rfl := interp_pure_ok hf
      exact hacc
    | cons prov rest ih =>
      intro acc out hacc hf
      rw [List.foldlM_cons] at hf
      obtain ⟨mid, hr, hf⟩ := bind_ok hf
      exact ih (TreeBorrowsMemory.release_protector_wfLive hacc hr) hf
  exact key extra.protectors hwf h

/-- Every provenance carried by `ptr` refers to an existing allocation slot in `tbm`
(`spec/mem/basic.md`: "since AllocId cannot be faked"). -/
def TreeBorrowsMemory.validPtrAlloc (tbm : Gen.TreeBorrowsMemory Gen.x86_64)
    (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance) : Prop :=
  ∀ id p, ptr.provenance = some (id, p) →
    0 ≤ id._0 ∧ id._0.toNat < tbm.mem.allocations.length

private theorem check_ptr_tb_no_specPanic {tbm : Gen.TreeBorrowsMemory Gen.x86_64}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} (len : Size) (msg : String)
    (hvalid : TreeBorrowsMemory.validPtrAlloc tbm ptr) :
    BasicMemory.check_ptr tbm.mem ptr len ≠ .error (.specPanic msg) := by
  intro h
  unfold BasicMemory.check_ptr at h
  split at h
  · cases h
  · cases hprov : ptr.provenance with
    | none => simp only [hprov] at h; cases h
    | some pair =>
      rcases pair with ⟨id, provExtra⟩
      simp only [hprov] at h
      obtain ⟨hge, hlt⟩ := hvalid id provExtra hprov
      obtain ⟨alloc, hget⟩ : ∃ a, tbm.mem.allocations[id._0.toNat]? = some a :=
        ⟨_, List.getElem?_eq_getElem hlt⟩
      have hidx : listIndex tbm.mem.allocations id._0 "self.allocations[id.0]" = .ok alloc := by
        simp [listIndex, hge, hget, pure, Except.pure]
      rw [hidx] at h
      dsimp only [bind, Except.bind] at h
      split at h
      · cases h
      · split at h <;> cases h

private theorem check_ptr_tb_some_ok {tbm : Gen.TreeBorrowsMemory Gen.x86_64}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} {len : Size}
    {id : Gen.AllocId} {provExtra : Gen.Path} {offset : Size}
    (hck : BasicMemory.check_ptr tbm.mem ptr len = .ok (some (id, provExtra, offset))) :
    ∃ allocation,
      0 ≤ id._0 ∧ id._0.toNat < tbm.mem.allocations.length ∧
      tbm.mem.allocations[id._0.toNat]? = some allocation ∧
      listIndex tbm.mem.allocations id._0 "self.allocations[id.0]" = .ok allocation ∧
      allocation.live = true ∧
      offset.bytes + len.bytes ≤ allocation.data.length := by
  unfold BasicMemory.check_ptr at hck
  split at hck
  · cases hck
  · cases hprov : ptr.provenance with
    | none => simp only [hprov] at hck; cases hck
    | some pair =>
      rcases pair with ⟨id0, pe0⟩
      simp only [hprov] at hck
      obtain ⟨allocation, hidx, hck⟩ := bind_ok hck
      obtain ⟨hge, hlt, hget⟩ := listIndex_ok hidx
      cases hlive : allocation.live with
      | false =>
        simp only [hlive, Bool.not_false, ↓reduceIte] at hck
        cases hck
      | true =>
        simp only [hlive, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hck
        dsimp only [Allocation.size] at hck
        by_cases hbounds :
            ptr.addr - allocation.addr < 0 ∨
              ptr.addr - allocation.addr + (len.bytes : Int) > (allocation.data.length : Int)
        · simp only [hbounds, ↓reduceIte] at hck; cases hck
        · simp only [hbounds, ↓reduceIte] at hck
          have hnn : (0 : Int) ≤ ptr.addr - allocation.addr :=
            Int.not_lt.mp fun hlt => hbounds (.inl hlt)
          have hle : ptr.addr - allocation.addr + (len.bytes : Int) ≤ (allocation.data.length : Int) :=
            Int.not_lt.mp fun hgt => hbounds (.inr hgt)
          have hinj := Option.some.inj (interp_pure_ok hck)
          obtain ⟨rfl, hpair⟩ := Prod.mk.inj hinj
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
          refine ⟨allocation, hge, hlt, hget, hidx, hlive, ?_⟩
          dsimp only
          cases hdiff : ptr.addr - allocation.addr with
          | ofNat k =>
            rw [hdiff] at hle
            exact Int.ofNat_le.mp hle
          | negSucc k =>
            rw [hdiff] at hnn
            cases hnn

/-- `TreeBorrowsMemory.allocate` never raises `Stop.specPanic`. -/
theorem TreeBorrowsMemory.allocate_no_specPanic (tbm : Gen.TreeBorrowsMemory Gen.x86_64)
    (kind : Gen.AllocationKind) (size : Size) (align : Align) (msg : String) :
    TreeBorrowsMemory.allocate tbm kind size align ≠ .error (.specPanic msg) := by
  intro h
  unfold TreeBorrowsMemory.allocate BasicMemory.allocate at h
  rcases bind_err h with ha | ⟨_, _, hp⟩
  · split at ha
    · cases ha
    · split at ha <;> cases ha
  · cases hp

/-- On a `wfLive` Tree Borrows memory, `TreeBorrowsMemory.load` on any pointer
with a valid allocation ID never raises `Stop.specPanic` (every misaligned,
provenance-less, dangling, out-of-bounds, or permission-violating read cleanly
raises `Stop.ub`). -/
theorem TreeBorrowsMemory.load_no_specPanic {tbm : Gen.TreeBorrowsMemory Gen.x86_64}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} (len : Size) (align : Align)
    (msg : String)
    (hwf : TreeBorrowsMemory.wfLive tbm)
    (hvalid : TreeBorrowsMemory.validPtrAlloc tbm ptr) :
    TreeBorrowsMemory.load tbm ptr len align ≠ .error (.specPanic msg) := by
  intro h
  unfold TreeBorrowsMemory.load BasicMemory.load at h
  rcases bind_err h with hload | ⟨_, _, hp⟩
  · split at hload
    · cases hload
    · rcases bind_err hload with hck_err | ⟨opt, hck, hload⟩
      · exact check_ptr_tb_no_specPanic len msg hvalid hck_err
      · cases opt with
        | none => cases hload
        | some triple =>
          rcases triple with ⟨id, provExtra, offset⟩
          obtain ⟨allocation, hge, hlt, hget, hidx, hlive, hbounds⟩ :=
            check_ptr_tb_some_ok hck
          dsimp only at hload
          rw [hidx] at hload
          dsimp only [bind, Except.bind] at hload
          rcases bind_err hload with hextra_err | ⟨extra', _, hload⟩
          · rcases bind_err hextra_err with hacc_err | ⟨_, _, hp⟩
            · exact Node.access_no_specPanic _ _ .Read offset len msg
                (hwf allocation (List.mem_of_getElem? hget) hlive) hbounds hacc_err
            · cases hp
          · have hset : listSet tbm.mem.allocations id._0
                { allocation with extra := extra' } "set" =
                .ok (tbm.mem.allocations.set id._0.toNat { allocation with extra := extra' }) := by
              simp [listSet, hge, hlt, pure, Except.pure]
            rw [hset] at hload
            dsimp only [bind, Except.bind] at hload
            have hsub : subsliceWithLength allocation.data (offset.bytes : Int) (len.bytes : Int) =
                .ok ((allocation.data.drop (offset.bytes : Int).toNat).take
                  (len.bytes : Int).toNat) := by
              unfold subsliceWithLength
              have hcond : (0 : Int) ≤ offset.bytes ∧ (0 : Int) ≤ len.bytes ∧
                  (offset.bytes : Int) + (len.bytes : Int) ≤ allocation.data.length :=
                ⟨by omega, by omega, by omega⟩
              simp only [hcond, and_self, ↓reduceIte]
              rfl
            rw [hsub] at hload
            cases hload
  · cases hp

/-- On a `wfLive` Tree Borrows memory, `TreeBorrowsMemory.store` on any pointer
with a valid allocation ID never raises `Stop.specPanic`. -/
theorem TreeBorrowsMemory.store_no_specPanic {tbm : Gen.TreeBorrowsMemory Gen.x86_64}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance}
    (bytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (align : Align)
    (msg : String)
    (hwf : TreeBorrowsMemory.wfLive tbm)
    (hvalid : TreeBorrowsMemory.validPtrAlloc tbm ptr) :
    TreeBorrowsMemory.store tbm ptr bytes align ≠ .error (.specPanic msg) := by
  intro h
  unfold TreeBorrowsMemory.store BasicMemory.store at h
  rcases bind_err h with hstore | ⟨_, _, hp⟩
  · split at hstore
    · cases hstore
    · rcases bind_err hstore with hck_err | ⟨opt, hck, hstore⟩
      · exact check_ptr_tb_no_specPanic ⟨bytes.length⟩ msg hvalid hck_err
      · cases opt with
        | none => cases hstore
        | some triple =>
          rcases triple with ⟨id, provExtra, offset⟩
          obtain ⟨allocation, hge, hlt, hget, hidx, hlive, hbounds⟩ :=
            check_ptr_tb_some_ok hck
          dsimp only at hbounds
          dsimp only at hstore
          rw [hidx] at hstore
          dsimp only [bind, Except.bind] at hstore
          rcases bind_err hstore with hextra_err | ⟨extra', _, hstore⟩
          · rcases bind_err hextra_err with hacc_err | ⟨_, _, hp⟩
            · exact Node.access_no_specPanic _ _ .Write offset ⟨bytes.length⟩ msg
                (hwf allocation (List.mem_of_getElem? hget) hlive) hbounds hacc_err
            · cases hp
          · have hws : writeSubsliceAtIndex allocation.data (offset.bytes : Int) bytes =
                .ok (allocation.data.take (offset.bytes : Int).toNat ++ bytes ++
                  allocation.data.drop ((offset.bytes : Int).toNat + bytes.length)) := by
              unfold writeSubsliceAtIndex
              have hcond : (0 : Int) ≤ offset.bytes ∧
                  (offset.bytes : Int) + (bytes.length : Int) ≤ allocation.data.length :=
                ⟨by omega, by omega⟩
              simp only [hcond, and_self, ↓reduceIte]
              rfl
            rw [hws] at hstore
            dsimp only [bind, Except.bind] at hstore
            have hset : listSet tbm.mem.allocations id._0
                { allocation with
                  data := allocation.data.take (offset.bytes : Int).toNat ++ bytes ++
                    allocation.data.drop ((offset.bytes : Int).toNat + bytes.length),
                  extra := extra' } "set" =
                .ok (tbm.mem.allocations.set id._0.toNat
                  { allocation with
                    data := allocation.data.take (offset.bytes : Int).toNat ++ bytes ++
                      allocation.data.drop ((offset.bytes : Int).toNat + bytes.length),
                    extra := extra' }) := by
              simp [listSet, hge, hlt, pure, Except.pure]
            rw [hset] at hstore
            cases hstore
  · cases hp

/-- On a `wfLive` Tree Borrows memory, `TreeBorrowsMemory.deallocate` on any
pointer with a valid allocation ID never raises `Stop.specPanic`. -/
theorem TreeBorrowsMemory.deallocate_no_specPanic {tbm : Gen.TreeBorrowsMemory Gen.x86_64}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} (kind : Gen.AllocationKind)
    (size : Size) (align : Align) (msg : String)
    (hwf : TreeBorrowsMemory.wfLive tbm)
    (hvalid : TreeBorrowsMemory.validPtrAlloc tbm ptr) :
    TreeBorrowsMemory.deallocate tbm ptr kind size align ≠ .error (.specPanic msg) := by
  intro h
  unfold TreeBorrowsMemory.deallocate BasicMemory.deallocate at h
  rcases bind_err h with hd | ⟨_, _, hp⟩
  · cases hprov : ptr.provenance with
    | none => simp only [hprov] at hd; cases hd
    | some pair =>
      rcases pair with ⟨id, provExtra⟩
      simp only [hprov] at hd
      obtain ⟨hge, hlt⟩ := hvalid id provExtra hprov
      obtain ⟨allocation, hget⟩ : ∃ a, tbm.mem.allocations[id._0.toNat]? = some a :=
        ⟨_, List.getElem?_eq_getElem hlt⟩
      have hidx : listIndex tbm.mem.allocations id._0 "self.allocations[id.0]" =
          .ok allocation := by
        simp [listIndex, hge, hget, pure, Except.pure]
      rw [hidx] at hd
      dsimp only [bind, Except.bind] at hd
      cases hlive : allocation.live with
      | false =>
        simp only [hlive, Bool.not_false, ↓reduceIte] at hd
        cases hd
      | true =>
        simp only [hlive, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hd
        split at hd; · cases hd
        split at hd; · dsimp only [ub] at hd; cases hd
        by_cases hsz : size = Allocation.size allocation
        · simp only [hsz, ne_eq, not_true_eq_false, ↓reduceIte] at hd
          split at hd; · cases hd
          rcases bind_err hd with hextra_err | ⟨extra', _, hd⟩
          · rcases bind_err hextra_err with hacc_err | ⟨root', _, hextra_err⟩
            · exact Node.access_no_specPanic _ _ .Write ⟨0⟩ (Allocation.size allocation) msg
                (hwf allocation (List.mem_of_getElem? hget) hlive)
                (by change 0 + allocation.data.length ≤ allocation.data.length; omega) hacc_err
            · split at hextra_err <;> cases hextra_err
          · have hset : listSet tbm.mem.allocations id._0
                { allocation with live := false, extra := extra' } "set" =
                .ok (tbm.mem.allocations.set id._0.toNat
                  { allocation with live := false, extra := extra' }) := by
              simp [listSet, hge, hlt, pure, Except.pure]
            rw [hset] at hd
            cases hd
        · simp only [ne_eq, hsz, not_false_eq_true, ↓reduceIte] at hd; cases hd
  · cases hp

/-- `TreeBorrowsMemory.new` satisfies `TreeBorrowsMemory.wfLive`. -/
theorem TreeBorrowsMemory.new_wfLive (params : Gen.TreeBorrowsParams) :
    TreeBorrowsMemory.wfLive (TreeBorrowsMemory.new params) :=
  TreeBorrowsMemory.wfLive_of_wf (TreeBorrowsMemory.new_wf params)

/-- `TreeBorrowsMemory.allocate` preserves `TreeBorrowsMemory.wfLive`. -/
theorem TreeBorrowsMemory.allocate_wfLive {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {kind : Gen.AllocationKind} {size : Size} {align : Align}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance}
    (hwf : TreeBorrowsMemory.wfLive tbm)
    (h : TreeBorrowsMemory.allocate tbm kind size align = .ok (ptr, tbm')) :
    TreeBorrowsMemory.wfLive tbm' := by
  unfold TreeBorrowsMemory.allocate BasicMemory.allocate at h
  obtain ⟨⟨ptr1, mem'⟩, halloc, h⟩ := bind_ok h
  obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
  split at halloc
  · cases halloc
  · cases hpick : BasicMemory.pickAddr tbm.mem size align with
    | none => simp only [hpick] at halloc; cases halloc
    | some addr =>
      simp only [hpick] at halloc
      obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok halloc)
      intro alloc hm hlive
      rcases List.mem_append.mp hm with hm | hm
      · exact hwf alloc hm hlive
      · rw [List.mem_singleton.mp hm]
        refine ⟨by simp [Allocation.size], fun p hp => ?_, trivial⟩
        rw [List.eq_of_mem_replicate hp]
        rfl

/-- `TreeBorrowsMemory.load` preserves `TreeBorrowsMemory.wfLive`. -/
theorem TreeBorrowsMemory.load_wfLive {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} {len : Size} {align : Align}
    {bytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)}
    (hwf : TreeBorrowsMemory.wfLive tbm)
    (h : TreeBorrowsMemory.load tbm ptr len align = .ok (bytes, tbm')) :
    TreeBorrowsMemory.wfLive tbm' := by
  unfold TreeBorrowsMemory.load BasicMemory.load at h
  obtain ⟨⟨bs, mem'⟩, hload, h⟩ := bind_ok h
  obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
  split at hload
  · cases hload
  · obtain ⟨opt, _, hload⟩ := bind_ok hload
    cases opt with
    | none =>
      obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hload)
      exact hwf
    | some triple =>
      rcases triple with ⟨id, provExtra, offset⟩
      obtain ⟨allocation, hidx, hload⟩ := bind_ok hload
      obtain ⟨extra', hextra, hload⟩ := bind_ok hload
      obtain ⟨allocations', hset, hload⟩ := bind_ok hload
      obtain ⟨_, _, hload⟩ := bind_ok hload
      obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hload)
      obtain ⟨root', hacc, hextra⟩ := bind_ok hextra
      obtain rfl := interp_pure_ok hextra
      obtain ⟨_, _, rfl⟩ := listSet_ok hset
      obtain ⟨_, _, hget⟩ := listIndex_ok hidx
      intro alloc hm hlive
      rcases mem_set_or hm with rfl | hm'
      · exact Node.access_wf (hwf allocation (List.mem_of_getElem? hget) hlive) hacc
      · exact hwf alloc hm' hlive

/-- `TreeBorrowsMemory.store` preserves `TreeBorrowsMemory.wfLive`. -/
theorem TreeBorrowsMemory.store_wfLive {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance}
    {bytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)} {align : Align}
    (hwf : TreeBorrowsMemory.wfLive tbm)
    (h : TreeBorrowsMemory.store tbm ptr bytes align = .ok tbm') :
    TreeBorrowsMemory.wfLive tbm' := by
  unfold TreeBorrowsMemory.store BasicMemory.store at h
  obtain ⟨mem', hstore, h⟩ := bind_ok h
  obtain rfl := interp_pure_ok h
  split at hstore
  · cases hstore
  · obtain ⟨opt, _, hstore⟩ := bind_ok hstore
    cases opt with
    | none =>
      obtain rfl := interp_pure_ok hstore
      exact hwf
    | some triple =>
      rcases triple with ⟨id, provExtra, offset⟩
      obtain ⟨allocation, hidx, hstore⟩ := bind_ok hstore
      obtain ⟨extra', hextra, hstore⟩ := bind_ok hstore
      obtain ⟨data', hws, hstore⟩ := bind_ok hstore
      obtain ⟨allocations', hset, hstore⟩ := bind_ok hstore
      obtain rfl := interp_pure_ok hstore
      obtain ⟨root', hacc, hextra⟩ := bind_ok hextra
      obtain rfl := interp_pure_ok hextra
      obtain ⟨_, _, rfl⟩ := listSet_ok hset
      obtain ⟨_, _, hget⟩ := listIndex_ok hidx
      have hdata_len := (writeSubsliceAtIndex_ok hws).2.2.1
      intro alloc hm hlive
      rcases mem_set_or hm with rfl | hm'
      · dsimp only [Allocation.size]
        rw [hdata_len]
        exact Node.access_wf (hwf allocation (List.mem_of_getElem? hget) hlive) hacc
      · exact hwf alloc hm' hlive

/-- `TreeBorrowsMemory.deallocate` preserves `TreeBorrowsMemory.wfLive` (the
deallocated slot is marked `live := false`). -/
theorem TreeBorrowsMemory.deallocate_wfLive {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} {kind : Gen.AllocationKind}
    {size : Size} {align : Align}
    (hwf : TreeBorrowsMemory.wfLive tbm)
    (h : TreeBorrowsMemory.deallocate tbm ptr kind size align = .ok tbm') :
    TreeBorrowsMemory.wfLive tbm' := by
  unfold TreeBorrowsMemory.deallocate BasicMemory.deallocate at h
  obtain ⟨mem', hdealloc, h⟩ := bind_ok h
  obtain rfl := interp_pure_ok h
  cases hprov : ptr.provenance with
  | none => simp only [hprov] at hdealloc; cases hdealloc
  | some pair =>
    rcases pair with ⟨id, provExtra⟩
    simp only [hprov] at hdealloc
    obtain ⟨allocation, _, hdealloc⟩ := bind_ok hdealloc
    split at hdealloc; · cases hdealloc
    split at hdealloc; · cases hdealloc
    split at hdealloc; · dsimp only [ub] at hdealloc; cases hdealloc
    split at hdealloc; · cases hdealloc
    split at hdealloc; · cases hdealloc
    obtain ⟨extra', _, hdealloc⟩ := bind_ok hdealloc
    obtain ⟨allocations', hset, hdealloc⟩ := bind_ok hdealloc
    obtain rfl := interp_pure_ok hdealloc
    obtain ⟨_, _, rfl⟩ := listSet_ok hset
    intro alloc hm hlive
    rcases mem_set_or hm with rfl | hm'
    · simp at hlive
    · exact hwf alloc hm' hlive

/-- `TreeBorrowsMemory.reborrow` preserves `TreeBorrowsMemory.wfLive` (including
for zero-sized reborrows, since `reborrow` preserves `allocation.live` and
`allocation.data`). -/
theorem TreeBorrowsMemory.reborrow_wfLive {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {ptr ptr' : Gen.ThinPointer Gen.TreeBorrowsProvenance} {settings : Gen.ReborrowSettings}
    {fe fe' : Gen.TreeBorrowsFrameExtra}
    (hwf : TreeBorrowsMemory.wfLive tbm)
    (h : TreeBorrowsMemory.reborrow tbm ptr settings fe = .ok (ptr', tbm', fe')) :
    TreeBorrowsMemory.wfLive tbm' := by
  unfold TreeBorrowsMemory.reborrow at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bind_ok h
  cases hprov : ptr.provenance with
  | none =>
    simp only [hprov] at h
    split at h
    · cases h
    · obtain ⟨_, h⟩ := Prod.mk.inj (interp_pure_ok h)
      obtain ⟨rfl, _⟩ := Prod.mk.inj h
      exact hwf
  | some pair =>
    rcases pair with ⟨allocId, parentPath⟩
    simp only [hprov] at h
    obtain ⟨⟨childPath, allocations'⟩, hm, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨_, h⟩ := Prod.mk.inj (interp_pure_ok h)
    obtain ⟨rfl, _⟩ := Prod.mk.inj h
    obtain ⟨allocation, alloc', _, _, hget, hf, rfl⟩ := listMutateAt_ok hm
    cases hoff : Size.from_bytes (ptr.addr - allocation.addr) with
    | none => simp [hoff, specPanic, bind, Except.bind] at hf
    | some offset =>
      simp only [hoff, pure, Except.pure, bind, Except.bind] at hf
      have hbody : ∀ (permissions : List Gen.Permission),
          permissions.length = (Allocation.size allocation).bytes →
          (let childNode : Gen.Node :=
            { children := [], permissions := permissions, «protected» := settings.«protected» }
           if (!childNode.permissions.all fun x =>
               Permission.matches_protector x childNode.«protected») = true then
             specPanic
               "assertion failed: child_node.permissions.all(|x| x.matches_protector(child_node.protected))"
           else do
             let (cp, root1) ← Node.add_node allocation.extra.root parentPath childNode
             let root2 ← TreeBorrowsMemory.reborrowInitAccess cp offset 0 settings.inside root1
             pure (cp, { data := allocation.data, addr := allocation.addr, align := allocation.align,
                         kind := allocation.kind, live := allocation.live, extra := { root := root2 } })) =
            .ok (childPath, alloc') →
          TreeBorrowsMemory.wfLive
            { params := tbm.params,
              mem := { allocations := tbm.mem.allocations.set allocId._0.toNat alloc',
                       _phantom := tbm.mem._phantom } } := by
        intro permissions hplen hfb
        dsimp only at hfb
        cases hall : permissions.all (fun x => Permission.matches_protector x settings.«protected») with
        | false =>
          simp only [hall, Bool.not_false, ↓reduceIte] at hfb
          cases hfb
        | true =>
          simp only [hall, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfb
          obtain ⟨⟨cp, root1⟩, hadd, hfb⟩ := bind_ok hfb
          dsimp only at hfb
          obtain ⟨root2, hinit, hfb⟩ := bind_ok hfb
          obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hfb)
          have hchild_wf : Node.wf (Allocation.size allocation).bytes
              { children := [], permissions := permissions, «protected» := settings.«protected» } :=
            ⟨hplen, List.all_eq_true.mp hall, trivial⟩
          intro alloc hm' hlive
          rcases mem_set_or hm' with rfl | hm''
          · have hr1 := Node.add_node_wf
              (hwf allocation (List.mem_of_getElem? hget) hlive) hchild_wf hadd
            exact TreeBorrowsMemory.reborrowInitAccess_wf cp offset 0 settings.inside hr1 hinit
          · exact hwf alloc hm'' hlive
      by_cases hgt : settings.inside.length > 0
      · simp only [hgt, ↓reduceIte] at hf
        obtain ⟨permissions, hps, hf⟩ := bind_ok hf
        exact hbody permissions
          ((writeSubsliceAtIndex_ok hps).2.2.1.trans (List.length_replicate ..)) hf
      · simp only [hgt, ↓reduceIte] at hf
        exact hbody _ (List.length_replicate ..) hf

/-- `TreeBorrowsMemory.retag_ptr` preserves `TreeBorrowsMemory.wfLive`. -/
theorem TreeBorrowsMemory.retag_ptr_wfLive {tbm tbm' : Gen.TreeBorrowsMemory Gen.x86_64}
    {fe fe' : Gen.TreeBorrowsFrameExtra} {ptr ptr' : Gen.Pointer Gen.TreeBorrowsProvenance}
    {ptrType : Gen.PtrType} {fnEntry fnImplicitWrites : Bool}
    {vtableLookup : Gen.ThinPointer Gen.TreeBorrowsProvenance → Interp Gen.VTable}
    (hwf : TreeBorrowsMemory.wfLive tbm)
    (h : TreeBorrowsMemory.retag_ptr tbm fe ptr ptrType fnEntry fnImplicitWrites vtableLookup =
      .ok (ptr', tbm', fe')) :
    TreeBorrowsMemory.wfLive tbm' := by
  unfold TreeBorrowsMemory.retag_ptr at h
  obtain ⟨opt, _, h⟩ := bind_ok h
  cases opt with
  | none =>
    obtain ⟨_, h⟩ := Prod.mk.inj (interp_pure_ok h)
    obtain ⟨rfl, _⟩ := Prod.mk.inj h
    exact hwf
  | some perms =>
    obtain ⟨⟨thin', tbm1, fe1⟩, hreb, h⟩ := bind_ok h
    obtain ⟨_, h⟩ := Prod.mk.inj (interp_pure_ok h)
    obtain ⟨rfl, _⟩ := Prod.mk.inj h
    exact TreeBorrowsMemory.reborrow_wfLive hwf hreb

/-- Machine-level Tree Borrows live-allocation invariant on `MachTB`
(`Machine<TreeBorrowsMemory<x86_64>>`): every live allocation in `m` carries a
well-formed borrow tree (`Node.wf`). -/
def MachTB.wfLive (m : MachTB) : Prop :=
  TreeBorrowsMemory.wfLive m.mem.memory

private theorem cm_tb_load_wfLive {cm cm' : Gen.ConcurrentMemory TBM}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} {len : Size} {align : Align}
    {atomicity : Gen.Atomicity}
    {bytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)}
    (hwf : TreeBorrowsMemory.wfLive cm.memory)
    (h : ConcurrentMemory.load cm ptr len align atomicity = .ok (bytes, cm')) :
    TreeBorrowsMemory.wfLive cm'.memory := by
  unfold ConcurrentMemory.load at h
  obtain ⟨⟨_, mem'⟩, hload, h⟩ := bind_ok h
  obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
  exact TreeBorrowsMemory.load_wfLive hwf hload

private theorem cm_tb_store_wfLive {cm cm' : Gen.ConcurrentMemory TBM}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance}
    {bytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)} {align : Align}
    {atomicity : Gen.Atomicity}
    (hwf : TreeBorrowsMemory.wfLive cm.memory)
    (h : ConcurrentMemory.store cm ptr bytes align atomicity = .ok cm') :
    TreeBorrowsMemory.wfLive cm'.memory := by
  unfold ConcurrentMemory.store at h
  obtain ⟨mem', hstore, h⟩ := bind_ok h
  obtain rfl := interp_pure_ok h
  exact TreeBorrowsMemory.store_wfLive hwf hstore

private theorem cm_tb_deinit_wfLive {cm cm' : Gen.ConcurrentMemory TBM}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} {len : Size} {align : Align}
    (hwf : TreeBorrowsMemory.wfLive cm.memory)
    (h : ConcurrentMemory.deinit cm ptr len align = .ok cm') :
    TreeBorrowsMemory.wfLive cm'.memory :=
  cm_tb_store_wfLive hwf h

private theorem cm_tb_allocate_wfLive {cm cm' : Gen.ConcurrentMemory TBM}
    {kind : Gen.AllocationKind} {size : Size} {align : Align}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance}
    (hwf : TreeBorrowsMemory.wfLive cm.memory)
    (h : ConcurrentMemory.allocate cm kind size align = .ok (ptr, cm')) :
    TreeBorrowsMemory.wfLive cm'.memory := by
  unfold ConcurrentMemory.allocate at h
  obtain ⟨⟨_, mem'⟩, halloc, h⟩ := bind_ok h
  obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
  exact TreeBorrowsMemory.allocate_wfLive hwf halloc

private theorem cm_tb_deallocate_wfLive {cm cm' : Gen.ConcurrentMemory TBM}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} {kind : Gen.AllocationKind}
    {size : Size} {align : Align}
    (hwf : TreeBorrowsMemory.wfLive cm.memory)
    (h : ConcurrentMemory.deallocate cm ptr kind size align = .ok cm') :
    TreeBorrowsMemory.wfLive cm'.memory := by
  unfold ConcurrentMemory.deallocate at h
  obtain ⟨mem', hdealloc, h⟩ := bind_ok h
  obtain rfl := interp_pure_ok h
  exact TreeBorrowsMemory.deallocate_wfLive hwf hdealloc

private theorem cm_tb_retag_ptr_wfLive {cm cm' : Gen.ConcurrentMemory TBM}
    {fe fe' : Gen.TreeBorrowsFrameExtra} {ptr ptr' : Gen.Pointer Gen.TreeBorrowsProvenance}
    {ptrType : Gen.PtrType} {fnEntry fnImplicitWrites : Bool}
    {vtableLookup : Gen.ThinPointer Gen.TreeBorrowsProvenance → Interp Gen.VTable}
    (hwf : TreeBorrowsMemory.wfLive cm.memory)
    (h : ConcurrentMemory.retag_ptr cm fe ptr ptrType fnEntry fnImplicitWrites vtableLookup =
      .ok (ptr', cm', fe')) :
    TreeBorrowsMemory.wfLive cm'.memory := by
  unfold ConcurrentMemory.retag_ptr at h
  obtain ⟨⟨_, mem', _⟩, hret, h⟩ := bind_ok h
  obtain ⟨_, h⟩ := Prod.mk.inj (interp_pure_ok h)
  obtain ⟨rfl, _⟩ := Prod.mk.inj h
  exact TreeBorrowsMemory.retag_ptr_wfLive hwf hret

private theorem cm_tb_end_call_wfLive {cm cm' : Gen.ConcurrentMemory TBM}
    {extra : Gen.TreeBorrowsFrameExtra}
    (hwf : TreeBorrowsMemory.wfLive cm.memory)
    (h : ConcurrentMemory.end_call cm extra = .ok cm') :
    TreeBorrowsMemory.wfLive cm'.memory := by
  unfold ConcurrentMemory.end_call at h
  obtain ⟨mem', hend, h⟩ := bind_ok h
  obtain rfl := interp_pure_ok h
  exact TreeBorrowsMemory.end_call_wfLive hwf hend

private theorem mutateCurFrameM_tb_wfLive {m m' : MachTB}
    {f : Gen.StackFrame TBM → Gen.StackFrame TBM}
    (hwf : MachTB.wfLive m) (h : mutateCurFrameM m f = .ok m') :
    MachTB.wfLive m' := by
  unfold mutateCurFrameM at h
  obtain ⟨t, _, h⟩ := bind_ok h
  cases hlast : t.stack.getLast? with
  | none => simp only [hlast] at h; cases h
  | some fr =>
    simp only [hlast] at h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain rfl := interp_pure_ok h
    exact hwf

private theorem jumpToBlockM_tb_wfLive {m m' : MachTB} {b : Gen.BbName}
    (hwf : MachTB.wfLive m) (h : jumpToBlockM m b = .ok m') :
    MachTB.wfLive m' :=
  mutateCurFrameM_tb_wfLive hwf h

private theorem terminateActiveThreadM_tb_wfLive {m m' : MachTB}
    (hwf : MachTB.wfLive m) (h : terminateActiveThreadM m = .ok m') :
    MachTB.wfLive m' := by
  unfold terminateActiveThreadM at h
  dsimp only at h
  by_cases ha : m.active_thread = 0
  · simp only [ha, ↓reduceIte] at h; cases h
  · simp only [ha, ↓reduceIte] at h
    obtain ⟨t, _, h⟩ := bind_ok h
    by_cases hst : t.stack.length = 0
    · simp only [hst, ne_eq, not_true_eq_false, ↓reduceIte] at h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain rfl := interp_pure_ok h
      exact hwf
    · simp only [ne_eq, hst, not_false_eq_true, ↓reduceIte] at h; cases h

private theorem mutateCurFrameOutM_tb_wfLive {α : Type} {m m' : MachTB} {out : α}
    {f : Gen.StackFrame TBM → Gen.ConcurrentMemory TBM →
      Interp (α × Gen.StackFrame TBM × Gen.ConcurrentMemory TBM)}
    (hf : ∀ fr o fr' cm', f fr m.mem = .ok (o, fr', cm') → TreeBorrowsMemory.wfLive cm'.memory)
    (h : mutateCurFrameOutM m f = .ok (out, m')) :
    MachTB.wfLive m' := by
  unfold mutateCurFrameOutM at h
  obtain ⟨t, _, h⟩ := bind_ok h
  cases hlast : t.stack.getLast? with
  | none => simp only [hlast] at h; cases h
  | some fr =>
    simp only [hlast] at h
    obtain ⟨⟨o, fr', cm'⟩, hfr, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact hf fr o fr' cm' hfr

private theorem tryMutateCurFrameM_tb_wfLive {m m' : MachTB}
    {f : Gen.StackFrame TBM → Gen.ConcurrentMemory TBM →
      Interp (Gen.StackFrame TBM × Gen.ConcurrentMemory TBM)}
    (hf : ∀ fr fr' cm', f fr m.mem = .ok (fr', cm') → TreeBorrowsMemory.wfLive cm'.memory)
    (h : tryMutateCurFrameM m f = .ok m') :
    MachTB.wfLive m' := by
  unfold tryMutateCurFrameM at h
  obtain ⟨t, _, h⟩ := bind_ok h
  cases hlast : t.stack.getLast? with
  | none => simp only [hlast] at h; cases h
  | some fr =>
    simp only [hlast] at h
    obtain ⟨⟨fr', cm'⟩, hfr, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain rfl := interp_pure_ok h
    exact hf fr fr' cm' hfr

/-- `typedLoadM` on `MachTB` preserves `MachTB.wfLive`. -/
theorem typedLoadM_tb_wfLive {m m' : MachTB}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} {ty : Gen.Type}
    {align : Align} {atomicity : Gen.Atomicity} {val : Gen.Value TBM}
    (hwf : MachTB.wfLive m)
    (h : typedLoadM m ptr ty align atomicity = .ok (val, m')) :
    MachTB.wfLive m' := by
  unfold typedLoadM at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨⟨bytes, cm⟩, hload, h⟩ := bind_ok h
  dsimp only at h
  have hcm := cm_tb_load_wfLive hwf hload
  obtain ⟨opt, _, h⟩ := bind_ok h
  cases opt with
  | none => cases h
  | some v =>
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact hcm

/-- `typedStoreM` on `MachTB` preserves `MachTB.wfLive`. -/
theorem typedStoreM_tb_wfLive {m m' : MachTB}
    {ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance} {val : Gen.Value TBM}
    {ty : Gen.Type} {align : Align} {atomicity : Gen.Atomicity}
    (hwf : MachTB.wfLive m)
    (h : typedStoreM m ptr val ty align atomicity = .ok m') :
    MachTB.wfLive m' := by
  unfold typedStoreM at h
  dsimp only at h
  rcases hcv : checkValueM val ty (some m) with _ | ⟨⟩
  · simp only [hcv] at h; cases h
  · simp only [hcv] at h
    obtain ⟨bytes, _, h⟩ := bind_ok h
    obtain ⟨cm, hstore, h⟩ := bind_ok h
    obtain rfl := interp_pure_ok h
    exact cm_tb_store_wfLive hwf hstore

/-- `placeLoadM` on `MachTB` preserves `MachTB.wfLive`. -/
theorem placeLoadM_tb_wfLive {m m' : MachTB} {place : Gen.Place TBM}
    {ty : Gen.Type} {val : Gen.Value TBM}
    (hwf : MachTB.wfLive m) (h : placeLoadM m place ty = .ok (val, m')) :
    MachTB.wfLive m' := by
  unfold placeLoadM at h
  cases hpa : place.aligned with
  | false => simp only [hpa, Bool.not_false, ↓reduceIte] at h; cases h
  | true => simp only [hpa, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h; exact typedLoadM_tb_wfLive hwf h

/-- `placeStoreM` on `MachTB` preserves `MachTB.wfLive`. -/
theorem placeStoreM_tb_wfLive {m m' : MachTB} {place : Gen.Place TBM}
    {val : Gen.Value TBM} {ty : Gen.Type}
    (hwf : MachTB.wfLive m) (h : placeStoreM m place val ty = .ok m') :
    MachTB.wfLive m' := by
  unfold placeStoreM at h
  cases hpa : place.aligned with
  | false => simp only [hpa, Bool.not_false, ↓reduceIte] at h; cases h
  | true => simp only [hpa, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h; exact typedStoreM_tb_wfLive hwf h

mutual

/-- `decodeDiscriminantM` preserves every invariant `P` of the threaded state
that each call of its accessor preserves. -/
private theorem decodeDiscriminantM_inv {M : Type} [Gen.Memory M] {σ : Type} (P : σ → Prop)
    {accessor : σ → Gen.Offset → Size → Interp (List (Gen.AbstractByte (Gen.Memory.Provenance M)) × σ)}
    (hacc : ∀ s offset sz bs s', P s → accessor s offset sz = .ok (bs, s') → P s') :
    ∀ (d : Gen.Discriminator) {s s' : σ} {opt : Option Int},
      P s → decodeDiscriminantM (M := M) accessor d s = .ok (opt, s') → P s'
  | .Known _, _, _, _, hs, h => by
    unfold decodeDiscriminantM at h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact hs
  | .Invalid, _, _, _, hs, h => by
    unfold decodeDiscriminantM at h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact hs
  | .Branch offset valueType fallback ⟨children⟩, _, _, _, hs, h => by
    unfold decodeDiscriminantM at h
    obtain ⟨⟨bs, s1⟩, ha, h⟩ := bind_ok h
    have hs1 := hacc _ _ _ _ _ hs ha
    obtain ⟨optv, _, h⟩ := bind_ok h
    cases optv with
    | none =>
      obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
      exact hs1
    | some v =>
      cases v with
      | Int val =>
        exact decodeDiscriminantChildrenM_inv P hacc val
          (decodeDiscriminantM (M := M) accessor fallback)
          (fun hs' hfb => decodeDiscriminantM_inv P hacc fallback hs' hfb)
          children hs1 h
      | _ =>
        obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
        exact hs1

private theorem decodeDiscriminantChildrenM_inv {M : Type} [Gen.Memory M] {σ : Type} (P : σ → Prop)
    {accessor : σ → Gen.Offset → Size → Interp (List (Gen.AbstractByte (Gen.Memory.Provenance M)) × σ)}
    (hacc : ∀ s offset sz bs s', P s → accessor s offset sz = .ok (bs, s') → P s')
    (val : Int) (onFallback : σ → Interp (Option Int × σ))
    (hfb : ∀ {s s' : σ} {opt : Option Int}, P s → onFallback s = .ok (opt, s') → P s') :
    ∀ (children : List ((Int × Int) × Gen.Discriminator)) {s s' : σ} {opt : Option Int},
      P s → decodeDiscriminantChildrenM (M := M) accessor val onFallback children s = .ok (opt, s') → P s'
  | [], _, _, _, hs, h => hfb hs h
  | ((start, end_), child) :: rest, _, _, _, hs, h => by
    unfold decodeDiscriminantChildrenM at h
    split at h
    · exact decodeDiscriminantM_inv P hacc child hs h
    · exact decodeDiscriminantChildrenM_inv P hacc val onFallback hfb rest hs h

end

mutual

/-- `evalPlaceM` on `MachTB` preserves `MachTB.wfLive`. -/
theorem evalPlaceM_tb_wfLive :
    ∀ (pe : Gen.PlaceExpr) {m m' : MachTB} {out : Gen.Place TBM × Gen.Type},
      MachTB.wfLive m → evalPlaceM m pe = .ok (out, m') → MachTB.wfLive m'
  | .Local name, m, _, _, hwf, h => by
    unfold evalPlaceM at h
    obtain ⟨fr, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    cases hmg : mapGet fr.locals name with
    | none => simp only [hmg] at h; cases h
    | some _ =>
      simp only [hmg] at h
      obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
      exact hwf
  | .Field root field, _, _, _, hwf, h => by
    unfold evalPlaceM at h
    obtain ⟨⟨⟨rootPl, ty⟩, m1⟩, hr, h⟩ := bind_ok h
    dsimp only at h
    have hm1 := evalPlaceM_tb_wfLive root hwf hr
    cases ty with
    | Tuple sizedFields sizedHeadLayout unsizedField =>
      dsimp only at h
      by_cases h1 : 0 ≤ field ∧ field < (sizedFields.length : Int)
      · simp only [h1] at h
        obtain ⟨⟨offset, fieldTy⟩, _, h⟩ := bind_ok h
        dsimp only at h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨rootSize, _, h⟩ := bind_ok h
        by_cases hle : offset.bytes ≤ rootSize.bytes
        · simp only [hle, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
          exact hm1
        · simp only [hle, decide_false, Bool.not_false, ↓reduceIte] at h; cases h
      · simp only [h1, ↓reduceIte] at h
        by_cases h2 : field = (sizedFields.length : Int)
        · simp only [h2, ↓reduceIte] at h
          cases unsizedField with
          | none => cases h
          | some tailTy =>
            dsimp only at h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨tailAlign, _, h⟩ := bind_ok h
            dsimp only [pure, Except.pure, bind, Except.bind] at h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨rootSize, _, h⟩ := bind_ok h
            by_cases hle : (TupleHeadLayout.tail_offset sizedHeadLayout tailAlign).bytes ≤ rootSize.bytes
            · simp only [hle, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
              obtain ⟨_, _, h⟩ := bind_ok h
              obtain ⟨_, _, h⟩ := bind_ok h
              obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
              exact hm1
            · simp only [hle, decide_false, Bool.not_false, ↓reduceIte] at h; cases h
        · simp only [h2, ↓reduceIte] at h; cases h
    | Union fields _ _ _ =>
      dsimp only at h
      obtain ⟨⟨offset, fieldTy⟩, _, h⟩ := bind_ok h
      dsimp only at h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨rootSize, _, h⟩ := bind_ok h
      by_cases hle : offset.bytes ≤ rootSize.bytes
      · simp only [hle, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
        exact hm1
      · simp only [hle, decide_false, Bool.not_false, ↓reduceIte] at h; cases h
    | _ => cases h
  | .Index root index, _, _, _, hwf, h => by
    unfold evalPlaceM at h
    obtain ⟨⟨⟨rootPl, ty⟩, m1⟩, hr, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨⟨⟨idxVal, _⟩, m2⟩, hi, h⟩ := bind_ok h
    dsimp only at h
    have hm2 := evalValueM_tb_wfLive index (evalPlaceM_tb_wfLive root hwf hr) hi
    cases idxVal with
    | Int idx =>
      dsimp only [pure, Except.pure, bind, Except.bind] at h
      cases ty with
      | Array elemTy count =>
        dsimp only [pure, Except.pure, bind, Except.bind] at h
        by_cases hob : idx < 0 ∨ idx ≥ count
        · simp only [hob, ↓reduceIte] at h; cases h
        · simp only [hob, ↓reduceIte] at h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨offset, _, h⟩ := bind_ok h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨rootSize, _, h⟩ := bind_ok h
          by_cases hle : offset.bytes ≤ rootSize.bytes
          · simp only [hle, ↓reduceIte] at h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
            exact hm2
          · simp only [hle, ↓reduceIte] at h; cases h
      | Slice elemTy =>
        dsimp only at h
        rcases hmeta : rootPl.ptr.metadata with _ | (count | _) <;> simp only [hmeta] at h
        · cases h
        · by_cases hob : idx < 0 ∨ idx ≥ count
          · simp only [hob, ↓reduceIte] at h; cases h
          · simp only [hob, ↓reduceIte] at h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨offset, _, h⟩ := bind_ok h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨rootSize, _, h⟩ := bind_ok h
            by_cases hle : offset.bytes ≤ rootSize.bytes
            · simp only [hle, ↓reduceIte] at h
              obtain ⟨_, _, h⟩ := bind_ok h
              obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
              exact hm2
            · simp only [hle, ↓reduceIte] at h; cases h
        · cases h
      | _ => cases h
    | _ => cases h
  | .Deref operand _, _, _, _, hwf, h => by
    unfold evalPlaceM at h
    obtain ⟨⟨⟨v, vTy⟩, m1⟩, hv, h⟩ := bind_ok h
    dsimp only at h
    have hm1 := evalValueM_tb_wfLive operand hwf hv
    cases v with
    | Ptr ptr =>
      cases vTy with
      | Ptr ptrType =>
        dsimp only at h
        cases hsp : PtrType.safe_pointee ptrType with
        | none =>
          simp only [hsp, pure, Except.pure, bind, Except.bind] at h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
          exact hm1
        | some pointee =>
          simp only [hsp] at h
          obtain ⟨pointeeAlign, _, h⟩ := bind_ok h
          cases hal : Align.is_aligned pointeeAlign ptr.thin_pointer.addr with
          | false => simp only [hal, Bool.not_false, ↓reduceIte] at h; cases h
          | true =>
            simp only [hal, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, _, h⟩ := bind_ok h
            obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
            exact hm1
      | _ => cases h
    | _ => cases h
  | .Downcast root _, _, _, _, hwf, h => by
    unfold evalPlaceM at h
    obtain ⟨⟨⟨_, ty⟩, m1⟩, hr, h⟩ := bind_ok h
    have hm1 := evalPlaceM_tb_wfLive root hwf hr
    cases ty with
    | Enum _ _ _ _ _ =>
      dsimp only at h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
      exact hm1
    | _ => dsimp only at h; cases h

/-- `evalValueM` on `MachTB` preserves `MachTB.wfLive`. -/
theorem evalValueM_tb_wfLive :
    ∀ (ve : Gen.ValueExpr) {m m' : MachTB} {out : Gen.Value TBM × Gen.Type},
      MachTB.wfLive m → evalValueM m ve = .ok (out, m') → MachTB.wfLive m'
  | .Constant _ _, _, _, _, hwf, h => by
    unfold evalValueM at h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact hwf
  | .Tuple exprs _, _, _, _, hwf, h => by
    unfold evalValueM at h
    obtain ⟨⟨_, m1⟩, hes, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact evalValuesM_tb_wfLive exprs hwf hes
  | .Load source, _, _, _, hwf, h => by
    unfold evalValueM at h
    obtain ⟨⟨⟨place, ty⟩, m1⟩, hp, h⟩ := bind_ok h
    obtain ⟨⟨_, m2⟩, hl, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact placeLoadM_tb_wfLive (evalPlaceM_tb_wfLive source hwf hp) hl
  | .AddrOf target _, _, _, _, hwf, h => by
    unfold evalValueM at h
    obtain ⟨⟨_, m1⟩, hp, h⟩ := bind_ok h
    have hm1 := evalPlaceM_tb_wfLive target hwf hp
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨⟨_, m2⟩, hm, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    refine mutateCurFrameOutM_tb_wfLive (fun fr o fr' cm' hfr => ?_) hm
    obtain ⟨⟨_, cm1, _⟩, hret, hfr⟩ := bind_ok hfr
    obtain ⟨_, hfr⟩ := Prod.mk.inj (interp_pure_ok hfr)
    obtain ⟨_, rfl⟩ := Prod.mk.inj hfr
    exact cm_tb_retag_ptr_wfLive hm1 hret
  | .UnOp _ operand, _, _, _, hwf, h => by
    unfold evalValueM at h
    obtain ⟨⟨_, m1⟩, ho, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact evalValueM_tb_wfLive operand hwf ho
  | .BinOp operator left right, _, _, _, hwf, h => by
    cases operator <;> {
      unfold evalValueM at h
      obtain ⟨⟨_, m1⟩, hl, h⟩ := bind_ok h
      obtain ⟨⟨_, m2⟩, hr, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
      exact evalValueM_tb_wfLive right (evalValueM_tb_wfLive left hwf hl) hr
    }
  | .Union _ expr unionTy, _, _, _, hwf, h => by
    unfold evalValueM at h
    cases unionTy with
    | Union _ _ _ _ =>
      dsimp only [pure, Except.pure, bind, Except.bind] at h
      obtain ⟨⟨_, _⟩, _, h⟩ := bind_ok h
      obtain ⟨⟨_, m1⟩, he, h⟩ := bind_ok h
      have hm1 := evalValueM_tb_wfLive expr hwf he
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨opt, _, h⟩ := bind_ok h
      cases opt with
      | none => cases h
      | some _ =>
        obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
        exact hm1
    | _ => dsimp only at h; cases h
  | .Variant _ data _, _, _, _, hwf, h => by
    unfold evalValueM at h
    obtain ⟨⟨_, m1⟩, hd, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact evalValueM_tb_wfLive data hwf hd
  | .GetDiscriminant place, _, _, _, hwf, h => by
    unfold evalValueM at h
    obtain ⟨⟨⟨pl, ty⟩, m1⟩, hp, h⟩ := bind_ok h
    have hm1 := evalPlaceM_tb_wfLive place hwf hp
    cases ty with
    | Enum _ _ discriminator _ _ =>
      dsimp only at h
      cases hpa : pl.aligned with
      | false => simp only [hpa, Bool.not_false, ↓reduceIte] at h; cases h
      | true =>
        simp only [hpa, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨⟨opt, m2⟩, hdd, h⟩ := bind_ok h
        have hm2 := decodeDiscriminantM_inv MachTB.wfLive
          (fun s idx sz bs s' hs hacc => by
            obtain ⟨p, _, hacc⟩ := bind_ok hacc
            obtain ⟨⟨_, cm⟩, hld, hacc⟩ := bind_ok hacc
            obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hacc)
            exact cm_tb_load_wfLive hs hld)
          discriminator hm1 hdd
        cases opt with
        | none => cases h
        | some _ =>
          obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
          exact hm2
    | _ => dsimp only at h; cases h

/-- `evalValuesM` on `MachTB` preserves `MachTB.wfLive`. -/
theorem evalValuesM_tb_wfLive :
    ∀ (es : List Gen.ValueExpr) {m m' : MachTB} {vals : List (Gen.Value TBM)},
      MachTB.wfLive m → evalValuesM m es = .ok (vals, m') → MachTB.wfLive m'
  | [], _, _, _, hwf, h => by
    unfold evalValuesM at h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact hwf
  | e :: es, _, _, _, hwf, h => by
    unfold evalValuesM at h
    obtain ⟨⟨_, m1⟩, he, h⟩ := bind_ok h
    obtain ⟨⟨_, m2⟩, hes, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact evalValuesM_tb_wfLive es (evalValueM_tb_wfLive e hwf he) hes

end

/-- `storageDeadM` on `TBM` preserves `TreeBorrowsMemory.wfLive`. -/
theorem storageDeadM_tb_wfLive {fr fr' : Gen.StackFrame TBM}
    {cm cm' : Gen.ConcurrentMemory TBM} {local_ : Gen.LocalName}
    (hwf : TreeBorrowsMemory.wfLive cm.memory)
    (h : storageDeadM fr cm local_ = .ok (fr', cm')) :
    TreeBorrowsMemory.wfLive cm'.memory := by
  unfold storageDeadM at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  rcases hrem : mapRemove fr.locals local_ with ⟨_ | ptr, locals⟩
  · simp only [hrem] at h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact hwf
  · simp only [hrem] at h
    obtain ⟨cm1, hd, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact cm_tb_deallocate_wfLive hwf hd

/-- `storageLiveM` on `TBM` preserves `TreeBorrowsMemory.wfLive`. -/
theorem storageLiveM_tb_wfLive {fr fr' : Gen.StackFrame TBM}
    {cm cm' : Gen.ConcurrentMemory TBM} {local_ : Gen.LocalName}
    (hwf : TreeBorrowsMemory.wfLive cm.memory)
    (h : storageLiveM fr cm local_ = .ok (fr', cm')) :
    TreeBorrowsMemory.wfLive cm'.memory := by
  unfold storageLiveM at h
  obtain ⟨⟨fr2, cm2⟩, hsd, h⟩ := bind_ok h
  have hcm2 := storageDeadM_tb_wfLive hwf hsd
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨⟨_, cm3⟩, ha, h⟩ := bind_ok h
  obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
  exact cm_tb_allocate_wfLive hcm2 ha

mutual

/-- `retagValM` on `MachTB` preserves `MachTB.wfLive`. -/
theorem retagValM_tb_wfLive :
    ∀ (val : Gen.Value TBM) (ty : Gen.Type) {m m' : MachTB} {fnEntry : Bool}
      {val' : Gen.Value TBM},
      MachTB.wfLive m → retagValM m fnEntry val ty = .ok (val', m') → MachTB.wfLive m'
  | .Int _, _, _, _, _, _, hwf, h => by
    unfold retagValM at h; obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h); exact hwf
  | .Bool _, _, _, _, _, _, hwf, h => by
    unfold retagValM at h; obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h); exact hwf
  | .Union _, _, _, _, _, _, hwf, h => by
    unfold retagValM at h; obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h); exact hwf
  | .Ptr ptr, .Ptr ptrType, _, _, _, _, hwf, h => by
    unfold retagValM at h
    obtain ⟨⟨_, m1⟩, hm, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    refine mutateCurFrameOutM_tb_wfLive (fun fr o fr' cm' hfr => ?_) hm
    obtain ⟨⟨_, cm1, _⟩, hret, hfr⟩ := bind_ok hfr
    obtain ⟨_, hfr⟩ := Prod.mk.inj (interp_pure_ok hfr)
    obtain ⟨_, rfl⟩ := Prod.mk.inj hfr
    exact cm_tb_retag_ptr_wfLive hwf hret
  | .Ptr _, .Int _, _, _, _, _, _, h | .Ptr _, .Bool, _, _, _, _, _, h
  | .Ptr _, .Union _ _ _ _, _, _, _, _, _, h | .Ptr _, .Tuple _ _ _, _, _, _, _, _, h
  | .Ptr _, .Array _ _, _, _, _, _, _, h | .Ptr _, .Enum _ _ _ _ _, _, _, _, _, _, h
  | .Ptr _, .Slice _, _, _, _, _, _, h | .Ptr _, .TraitObject _, _, _, _, _, _, h => by
    unfold retagValM at h; cases h
  | .Tuple vals, .Tuple sizedFields _ _, _, _, _, _, hwf, h => by
    unfold retagValM at h
    obtain ⟨⟨_, m1⟩, ht, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact retagTupleFieldsM_tb_wfLive vals sizedFields hwf ht
  | .Tuple vals, .Array elemTy _, _, _, _, _, hwf, h => by
    unfold retagValM at h
    obtain ⟨⟨_, m1⟩, ha, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact retagArrayElemsM_tb_wfLive elemTy vals hwf ha
  | .Tuple _, .Int _, _, _, _, _, _, h | .Tuple _, .Bool, _, _, _, _, _, h
  | .Tuple _, .Union _ _ _ _, _, _, _, _, _, h | .Tuple _, .Ptr _, _, _, _, _, _, h
  | .Tuple _, .Enum _ _ _ _ _, _, _, _, _, _, h | .Tuple _, .Slice _, _, _, _, _, _, h
  | .Tuple _, .TraitObject _, _, _, _, _, _, h => by
    unfold retagValM at h; cases h
  | .Variant discriminant data, .Enum variants _ _ _ _, _, _, _, _, hwf, h => by
    unfold retagValM at h
    obtain ⟨variant, _, h⟩ := bind_ok h
    obtain ⟨⟨_, m1⟩, hr, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact retagValM_tb_wfLive data variant.ty hwf hr
  | .Variant _ _, .Int _, _, _, _, _, _, h | .Variant _ _, .Bool, _, _, _, _, _, h
  | .Variant _ _, .Union _ _ _ _, _, _, _, _, _, h | .Variant _ _, .Ptr _, _, _, _, _, _, h
  | .Variant _ _, .Tuple _ _ _, _, _, _, _, _, h | .Variant _ _, .Array _ _, _, _, _, _, _, h
  | .Variant _ _, .Slice _, _, _, _, _, _, h | .Variant _ _, .TraitObject _, _, _, _, _, _, h => by
    unfold retagValM at h; cases h

/-- `retagTupleFieldsM` on `MachTB` preserves `MachTB.wfLive`. -/
theorem retagTupleFieldsM_tb_wfLive :
    ∀ (vals : List (Gen.Value TBM)) (fields : List (Gen.Offset × Gen.Type))
      {m m' : MachTB} {fnEntry : Bool} {vals' : List (Gen.Value TBM)},
      MachTB.wfLive m → retagTupleFieldsM m fnEntry vals fields = .ok (vals', m') →
      MachTB.wfLive m'
  | [], [], _, _, _, _, hwf, h => by
    unfold retagTupleFieldsM at h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact hwf
  | [], _ :: _, _, _, _, _, _, h => by unfold retagTupleFieldsM at h; cases h
  | _ :: _, [], _, _, _, _, _, h => by unfold retagTupleFieldsM at h; cases h
  | val :: vals, (_, ty) :: fields, _, _, _, _, hwf, h => by
    unfold retagTupleFieldsM at h
    obtain ⟨⟨_, m1⟩, hv, h⟩ := bind_ok h
    obtain ⟨⟨_, m2⟩, hvs, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact retagTupleFieldsM_tb_wfLive vals fields (retagValM_tb_wfLive val ty hwf hv) hvs

/-- `retagArrayElemsM` on `MachTB` preserves `MachTB.wfLive`. -/
theorem retagArrayElemsM_tb_wfLive (elemTy : Gen.Type) :
    ∀ (vals : List (Gen.Value TBM)) {m m' : MachTB} {fnEntry : Bool}
      {vals' : List (Gen.Value TBM)},
      MachTB.wfLive m → retagArrayElemsM m fnEntry elemTy vals = .ok (vals', m') →
      MachTB.wfLive m'
  | [], _, _, _, _, hwf, h => by
    unfold retagArrayElemsM at h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact hwf
  | val :: vals, _, _, _, _, hwf, h => by
    unfold retagArrayElemsM at h
    obtain ⟨⟨_, m1⟩, hv, h⟩ := bind_ok h
    obtain ⟨⟨_, m2⟩, hvs, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact retagArrayElemsM_tb_wfLive elemTy vals (retagValM_tb_wfLive val elemTy hwf hv) hvs

end

/-- `encodeDiscriminantM` preserves every invariant `P` of the threaded state
that each call of its accessor preserves. -/
private theorem encodeDiscriminantM_inv {M : Type} [Gen.Memory M] {σ : Type} (P : σ → Prop)
    {accessor : σ → Gen.Offset → List (Gen.AbstractByte (Gen.Memory.Provenance M)) → Interp σ}
    (hacc : ∀ s offset bytes s', P s → accessor s offset bytes = .ok s' → P s')
    {tagger : Map Gen.Offset (Gen.IntType × Int)} {s s' : σ}
    (hs : P s) (h : encodeDiscriminantM (M := M) accessor tagger s = .ok s') : P s' := by
  unfold encodeDiscriminantM at h
  generalize tagger.entries = entries at h
  induction entries generalizing s with
  | nil =>
    obtain rfl := interp_pure_ok h
    exact hs
  | cons e es ih =>
    obtain ⟨offset, valueType, value⟩ := e
    rw [List.foldlM_cons] at h
    obtain ⟨s1, h1, h⟩ := bind_ok h
    obtain ⟨bytes, _, h1⟩ := bind_ok h1
    exact ih (hacc _ _ _ _ hs h1) h

/-- `evalStatementM` on `MachTB` preserves `MachTB.wfLive`. -/
theorem evalStatementM_tb_wfLive {m m' : MachTB} {stmt : Gen.Statement}
    (hwf : MachTB.wfLive m) (h : evalStatementM m stmt = .ok m') :
    MachTB.wfLive m' := by
  cases stmt with
  | Assign dst src =>
    unfold evalStatementM at h
    obtain ⟨⟨⟨place, ty⟩, m1⟩, hp, h⟩ := bind_ok h
    obtain ⟨⟨⟨val, _⟩, m2⟩, hv, h⟩ := bind_ok h
    exact placeStoreM_tb_wfLive
      (evalValueM_tb_wfLive src (evalPlaceM_tb_wfLive dst hwf hp) hv) h
  | PlaceMention place =>
    unfold evalStatementM at h
    obtain ⟨⟨_, m1⟩, hp, h⟩ := bind_ok h
    obtain rfl := interp_pure_ok h
    exact evalPlaceM_tb_wfLive place hwf hp
  | Validate place fnEntry =>
    unfold evalStatementM at h
    obtain ⟨⟨⟨p, ty⟩, m1⟩, hp, h⟩ := bind_ok h
    obtain ⟨⟨val, m2⟩, hl, h⟩ := bind_ok h
    obtain ⟨⟨val', m3⟩, hr, h⟩ := bind_ok h
    exact placeStoreM_tb_wfLive
      (retagValM_tb_wfLive val ty
        (placeLoadM_tb_wfLive (evalPlaceM_tb_wfLive place hwf hp) hl) hr) h
  | StorageLive local_ =>
    unfold evalStatementM at h
    exact tryMutateCurFrameM_tb_wfLive (fun _ _ _ hfr => storageLiveM_tb_wfLive hwf hfr) h
  | StorageDead local_ =>
    unfold evalStatementM at h
    exact tryMutateCurFrameM_tb_wfLive (fun _ _ _ hfr => storageDeadM_tb_wfLive hwf hfr) h
  | Deinit place =>
    unfold evalStatementM at h
    obtain ⟨⟨⟨p, ty⟩, m1⟩, hp, h⟩ := bind_ok h
    dsimp only at h
    have hm1 := evalPlaceM_tb_wfLive place hwf hp
    cases hpa : p.aligned with
    | false => simp only [hpa, Bool.not_false, ↓reduceIte] at h; cases h
    | true =>
      simp only [hpa, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨cm, hd, h⟩ := bind_ok h
      obtain rfl := interp_pure_ok h
      exact cm_tb_deinit_wfLive hm1 hd
  | SetDiscriminant dst value =>
    unfold evalStatementM evalSetDiscriminantM at h
    obtain ⟨⟨⟨place, ty⟩, m1⟩, hp, h⟩ := bind_ok h
    have hm1 := evalPlaceM_tb_wfLive dst hwf hp
    cases ty with
    | Enum variants _ _ _ _ =>
      dsimp only at h
      cases hpa : place.aligned with
      | false => simp only [hpa, Bool.not_false, ↓reduceIte] at h; cases h
      | true =>
        simp only [hpa, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        cases hv : mapGet variants value with
        | none => simp only [hv] at h; cases h
        | some variant =>
          simp only [hv] at h
          refine encodeDiscriminantM_inv MachTB.wfLive
            (fun s offset bytes s' hs hacc => ?_) hm1 h
          obtain ⟨p, _, hacc⟩ := bind_ok hacc
          obtain ⟨cm, hst, hacc⟩ := bind_ok hacc
          obtain rfl := interp_pure_ok hacc
          exact cm_tb_store_wfLive hs hst
    | _ => dsimp only at h; cases h

/-- `machineExitM` never returns normally (`Machine::exit` ends in
`throw_machine_stop!()` or a memory leak). -/
private theorem machineExitM_tb_ne_ok {α : Type} {m : MachTB} {x : α} :
    machineExitM (α := α) m ≠ .ok x := by
  intro h
  unfold machineExitM at h
  obtain ⟨_, _, h⟩ := bind_ok h
  cases h

/-- `loadRawDataM` on `MachTB` preserves `MachTB.wfLive`. -/
private theorem loadRawDataM_tb_wfLive {m m' : MachTB}
    {ptr : Gen.Pointer Gen.TreeBorrowsProvenance} {ptrTy : Gen.PtrType} {data : List UInt8}
    (hwf : MachTB.wfLive m) (h : loadRawDataM m ptr ptrTy = .ok (data, m')) :
    MachTB.wfLive m' := by
  unfold loadRawDataM at h
  split at h
  · split at h
    · obtain ⟨⟨bytes, cm⟩, hl, h⟩ := bind_ok h
      dsimp only at h
      split at h
      · obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
        exact cm_tb_load_wfLive hwf hl
      · cases h
    · cases h
  · cases h

/-- `prepareForInplacePassingM` on `MachTB` preserves `MachTB.wfLive`. -/
private theorem prepareForInplacePassingM_tb_wfLive {m m' : MachTB} {place : Gen.Place TBM}
    {ty : Gen.Type} (hwf : MachTB.wfLive m) (h : prepareForInplacePassingM m place ty = .ok m') :
    MachTB.wfLive m' := by
  unfold prepareForInplacePassingM at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨cm, hd, h⟩ := bind_ok h
  obtain rfl := interp_pure_ok h
  exact cm_tb_deinit_wfLive hwf hd

/-- `evalArgumentM` on `MachTB` preserves `MachTB.wfLive`. -/
private theorem evalArgumentM_tb_wfLive {m m' : MachTB} {arg : Gen.ArgumentExpr}
    {v : Gen.Value TBM × Gen.Type} (hwf : MachTB.wfLive m)
    (h : evalArgumentM m arg = .ok (v, m')) : MachTB.wfLive m' := by
  cases arg with
  | ByValue e =>
    unfold evalArgumentM at h
    exact evalValueM_tb_wfLive e hwf h
  | InPlace p =>
    unfold evalArgumentM at h
    obtain ⟨⟨⟨place, ty⟩, m1⟩, hp, h⟩ := bind_ok h
    obtain ⟨⟨val, m2⟩, hl, h⟩ := bind_ok h
    obtain ⟨m3, hprep, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact prepareForInplacePassingM_tb_wfLive
      (placeLoadM_tb_wfLive (evalPlaceM_tb_wfLive p hwf hp) hl) hprep

/-- `evalArgumentsM` on `MachTB` preserves `MachTB.wfLive`. -/
private theorem evalArgumentsM_tb_wfLive :
    ∀ (args : List Gen.ArgumentExpr) {m m' : MachTB} {vs : List (Gen.Value TBM × Gen.Type)},
      MachTB.wfLive m → evalArgumentsM m args = .ok (vs, m') → MachTB.wfLive m'
  | [], _, _, _, hwf, h => by
    unfold evalArgumentsM at h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact hwf
  | a :: as, _, _, _, hwf, h => by
    unfold evalArgumentsM at h
    obtain ⟨⟨_, m1⟩, ha, h⟩ := bind_ok h
    obtain ⟨⟨_, m2⟩, has, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact evalArgumentsM_tb_wfLive as (evalArgumentM_tb_wfLive hwf ha) has

/-- `allocFrameArgsM` on `TBM` preserves `TreeBorrowsMemory.wfLive`. -/
private theorem allocFrameArgsM_tb_wfLive :
    ∀ (ls : List Gen.LocalName) {fr fr' : Gen.StackFrame TBM} {cm cm' : Gen.ConcurrentMemory TBM},
      TreeBorrowsMemory.wfLive cm.memory →
      allocFrameArgsM fr cm ls = .ok (fr', cm') → TreeBorrowsMemory.wfLive cm'.memory
  | [], _, _, _, _, hwf, h => by
    unfold allocFrameArgsM at h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact hwf
  | l :: ls, _, _, _, _, hwf, h => by
    unfold allocFrameArgsM at h
    obtain ⟨⟨fr1, cm1⟩, hsl, h⟩ := bind_ok h
    exact allocFrameArgsM_tb_wfLive ls (storageLiveM_tb_wfLive hwf hsl) h

/-- `initFrameArgsM` on `MachTB` preserves `MachTB.wfLive`. -/
private theorem initFrameArgsM_tb_wfLive (frame : Gen.StackFrame TBM) :
    ∀ (ls : List Gen.LocalName) (args : List (Gen.Value TBM × Gen.Type)) {m m' : MachTB},
      MachTB.wfLive m → initFrameArgsM m frame ls args = .ok m' → MachTB.wfLive m'
  | [], _, _, _, hwf, h => by
    unfold initFrameArgsM at h
    obtain rfl := interp_pure_ok h
    exact hwf
  | _ :: _, [], _, _, hwf, h => by
    unfold initFrameArgsM at h
    obtain rfl := interp_pure_ok h
    exact hwf
  | l :: ls, (v, ty) :: args, m, _, hwf, h => by
    unfold initFrameArgsM at h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨ok, _, h⟩ := bind_ok h
    split at h
    · cases h
    · obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨ptr, _, h⟩ := bind_ok h
      dsimp only at h
      split at h
      · rename_i m2 hst
        obtain ⟨m3, hm3, h⟩ := bind_ok h
        obtain rfl := interp_pure_ok hm3
        exact initFrameArgsM_tb_wfLive frame ls args (typedStoreM_tb_wfLive hwf hst) h
      all_goals
        obtain ⟨_, hbad, _⟩ := bind_ok h
        cases hbad

/-- `createFrameM` on `MachTB` preserves `MachTB.wfLive`. -/
private theorem createFrameM_tb_wfLive {m m' : MachTB} {func : Gen.Function}
    {spa : Gen.StackPopAction TBM} {conv : Gen.CallingConvention} {retTy : Gen.Type}
    {args : List (Gen.Value TBM × Gen.Type)} {fr : Gen.StackFrame TBM}
    (hwf : MachTB.wfLive m) (h : createFrameM m func spa conv retTy args = .ok (fr, m')) :
    MachTB.wfLive m' := by
  unfold createFrameM at h
  obtain ⟨⟨fr1, cm1⟩, hsl, h⟩ := bind_ok h
  obtain ⟨⟨fr2, cm2⟩, hal, h⟩ := bind_ok h
  dsimp only at h
  have hcm2 : TreeBorrowsMemory.wfLive cm2.memory :=
    allocFrameArgsM_tb_wfLive func.args (storageLiveM_tb_wfLive hwf hsl) hal
  split at h
  · cases h
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    split at h
    · cases h
    · split at h
      · cases h
      · obtain ⟨m3, hinit, h⟩ := bind_ok h
        obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
        exact initFrameArgsM_tb_wfLive fr2 func.args args (m := { m with mem := cm2 }) hcm2 hinit

/-- `evalCallM` on `MachTB` preserves `MachTB.wfLive`. -/
private theorem evalCallM_tb_wfLive {m m' : MachTB} {callee : Gen.Function}
    {conv : Gen.CallingConvention} {args : List (Gen.Value TBM × Gen.Type)}
    {ret : Gen.Place TBM × Gen.Type} {nb ub' : Option Gen.BbName}
    (hwf : MachTB.wfLive m) (h : evalCallM m callee conv args ret nb ub' = .ok m') :
    MachTB.wfLive m' := by
  unfold evalCallM at h
  obtain ⟨⟨fr, m1⟩, hc, h⟩ := bind_ok h
  dsimp only at h
  have hm1 := createFrameM_tb_wfLive hwf hc
  unfold mutateCurStackM at h
  obtain ⟨⟨_, m2⟩, hs, h⟩ := bind_ok h
  obtain rfl := interp_pure_ok h
  obtain ⟨_, _, hs⟩ := bind_ok hs
  obtain ⟨_, hpure, hs⟩ := bind_ok hs
  obtain ⟨_, _, hs⟩ := bind_ok hs
  obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok hs)
  exact hm1

/-- `evalIntrinsicM` on `MachTB` preserves `MachTB.wfLive`. -/
theorem evalIntrinsicM_tb_wfLive {m m' : MachTB} {intrinsic : Gen.IntrinsicOp}
    {arguments : List (Gen.Value TBM × Gen.Type)} {retTy : Gen.Type} {val : Gen.Value TBM}
    (hwf : MachTB.wfLive m) (h : evalIntrinsicM m intrinsic arguments retTy = .ok (val, m')) :
    MachTB.wfLive m' := by
  cases intrinsic with
  | PointerExposeProvenance =>
    dsimp only [evalIntrinsicM] at h
    by_cases hlen : arguments.length = 1
    · simp only [hlen, ne_eq, not_true_eq_false, ↓reduceIte] at h
      rcases arguments with _ | ⟨⟨v, _⟩, _ | ⟨_, _⟩⟩
      · simp at hlen
      · rcases v with _ | _ | ⟨ptr, _ | _⟩ | _ | _
        · dsimp only [ub] at h; cases h
        · dsimp only [ub] at h; cases h
        · rcases retTy with ⟨_ | _, ⟨sz⟩⟩ | _ | _ | _ | _ | _ | _ | _
          · by_cases hsz : sz = 8
            · subst hsz
              dsimp only at h
              obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
              exact hwf
            · simp [hsz, ub] at h
          all_goals (dsimp only [ub] at h; cases h)
        all_goals (dsimp only [ub] at h; cases h)
      · simp at hlen
    · simp only [ne_eq, hlen, not_false_eq_true, ↓reduceIte, ub] at h; cases h
  | PointerWithExposedProvenance =>
    dsimp only [evalIntrinsicM] at h
    by_cases hlen : arguments.length = 1
    · simp only [hlen, ne_eq, not_true_eq_false, ↓reduceIte] at h
      rcases arguments with _ | ⟨⟨v, _⟩, _ | ⟨_, _⟩⟩
      · simp at hlen
      · rcases v with addr | _ | _ | _ | _
        · cases retTy with
          | Ptr retPtrTy =>
            dsimp only at h
            by_cases hmk : PtrType.meta_kind retPtrTy = .None
            · simp only [hmk, not_true_eq_false, ↓reduceIte] at h
              obtain ⟨_, _, h⟩ := bind_ok h
              obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
              exact hwf
            · simp only [hmk, not_false_eq_true, ↓reduceIte] at h
              dsimp only [ub] at h; cases h
          | _ => dsimp only [ub] at h; cases h
        all_goals (dsimp only [ub] at h; cases h)
      · simp at hlen
    · simp only [ne_eq, hlen, not_false_eq_true, ↓reduceIte, ub] at h; cases h
  | Exit =>
    dsimp only [evalIntrinsicM] at h
    exact absurd h machineExitM_tb_ne_ok
  | Abort =>
    dsimp only [evalIntrinsicM, abort] at h; cases h
  | Assume =>
    dsimp only [evalIntrinsicM] at h
    repeat' split at h
    all_goals first
      | (obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h); exact hwf)
      | (dsimp only [ub] at h; cases h)
  | PrintStdout =>
    dsimp only [evalIntrinsicM] at h
    split at h
    · obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
      exact hwf
    · dsimp only [ub] at h; cases h
  | PrintStderr =>
    dsimp only [evalIntrinsicM] at h
    split at h
    · obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
      exact hwf
    · dsimp only [ub] at h; cases h
  | Allocate =>
    dsimp only [evalIntrinsicM] at h
    repeat' split at h
    all_goals first
      | (dsimp only [ub] at h; cases h)
      | (obtain ⟨⟨_, cm⟩, ha, h⟩ := bind_ok h
         obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
         exact cm_tb_allocate_wfLive hwf ha)
  | Deallocate =>
    dsimp only [evalIntrinsicM] at h
    repeat' split at h
    all_goals first
      | (dsimp only [ub] at h; cases h)
      | (obtain ⟨cm, hd, h⟩ := bind_ok h
         obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
         exact cm_tb_deallocate_wfLive hwf hd)
  | RawEq =>
    dsimp only [evalIntrinsicM] at h
    repeat' split at h
    all_goals first
      | (dsimp only [ub] at h; cases h)
      | (obtain ⟨⟨_, m1⟩, hl1, h⟩ := bind_ok h
         obtain ⟨⟨_, m2⟩, hl2, h⟩ := bind_ok h
         obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
         exact loadRawDataM_tb_wfLive (loadRawDataM_tb_wfLive hwf hl1) hl2)
  | GetUnwindPayload =>
    dsimp only [evalIntrinsicM] at h
    repeat' split at h
    all_goals first
      | (dsimp only [ub] at h; cases h)
      | (obtain ⟨_, _, h⟩ := bind_ok h
         repeat' split at h
         all_goals first
           | (obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h); exact hwf)
           | (dsimp only [ub] at h; cases h))
  | AtomicStore =>
    dsimp only [evalIntrinsicM] at h
    repeat' split at h
    all_goals first
      | (dsimp only [ub] at h; cases h)
      | (obtain ⟨_, _, h⟩ := bind_ok h
         repeat' split at h
         all_goals first
           | (dsimp only [ub] at h; cases h)
           | (obtain ⟨_, hs, h⟩ := bind_ok h
              obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
              exact typedStoreM_tb_wfLive hwf hs))
  | AtomicLoad =>
    dsimp only [evalIntrinsicM] at h
    repeat' split at h
    all_goals first
      | (dsimp only [ub] at h; cases h)
      | (obtain ⟨_, _, h⟩ := bind_ok h
         obtain ⟨_, _, h⟩ := bind_ok h
         repeat' split at h
         all_goals first
           | (dsimp only [ub] at h; cases h)
           | exact typedLoadM_tb_wfLive hwf h)
  | AtomicCompareExchange =>
    dsimp only [evalIntrinsicM] at h
    repeat' split at h
    all_goals first
      | (dsimp only [ub] at h; cases h)
      | (obtain ⟨_, _, h⟩ := bind_ok h
         obtain ⟨_, _, h⟩ := bind_ok h
         repeat' split at h
         all_goals first
           | (dsimp only [ub, specPanic] at h; cases h)
           | (obtain ⟨⟨_, m1⟩, hl, h⟩ := bind_ok h
              have hm1 := typedLoadM_tb_wfLive hwf hl
              try dsimp only at h
              split at h
              · obtain ⟨_, hs, h⟩ := bind_ok h
                obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
                exact typedStoreM_tb_wfLive hm1 hs
              · obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
                exact hm1))
  | AtomicFetchAndOp binOp =>
    dsimp only [evalIntrinsicM] at h
    repeat' split at h
    all_goals first
      | (dsimp only [ub] at h; cases h)
      | (obtain ⟨_, _, h⟩ := bind_ok h
         obtain ⟨_, _, h⟩ := bind_ok h
         repeat' split at h
         all_goals first
           | (dsimp only [ub, specPanic] at h; cases h)
           | (obtain ⟨⟨_, m1⟩, hl, h⟩ := bind_ok h
              have hm1 := typedLoadM_tb_wfLive hwf hl
              try dsimp only at h
              repeat' split at h
              all_goals first
                | (dsimp only [specPanic] at h; cases h)
                | (obtain ⟨_, _, h⟩ := bind_ok h
                   obtain ⟨_, hs, h⟩ := bind_ok h
                   obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
                   exact typedStoreM_tb_wfLive hm1 hs)))
  | _ =>
    dsimp only [evalIntrinsicM, unsupported] at h; cases h

/-- `evalArgsM` on `MachTB` preserves `MachTB.wfLive`. -/
theorem evalArgsM_tb_wfLive :
    ∀ (es : List Gen.ValueExpr) {m m' : MachTB} {args : List (Gen.Value TBM × Gen.Type)},
      MachTB.wfLive m → evalArgsM m es = .ok (args, m') → MachTB.wfLive m'
  | [], _, _, _, hwf, h => by
    unfold evalArgsM at h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact hwf
  | e :: es, _, _, _, hwf, h => by
    unfold evalArgsM at h
    obtain ⟨⟨_, m1⟩, he, h⟩ := bind_ok h
    obtain ⟨⟨_, m2⟩, hes, h⟩ := bind_ok h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
    exact evalArgsM_tb_wfLive es (evalValueM_tb_wfLive e hwf he) hes

/-- `deallocAllM` on `TBM` preserves `TreeBorrowsMemory.wfLive`. -/
theorem deallocAllM_tb_wfLive :
    ∀ (fuel : Nat) {fr fr' : Gen.StackFrame TBM} {cm cm' : Gen.ConcurrentMemory TBM},
      TreeBorrowsMemory.wfLive cm.memory →
      deallocAllM fuel fr cm = .ok (fr', cm') →
      TreeBorrowsMemory.wfLive cm'.memory
  | 0, fr, _, _, _, hwf, h => by
    unfold deallocAllM at h
    rcases hent : fr.locals.entries with _ | ⟨⟨_, _⟩, _⟩ <;> simp only [hent] at h
    · obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h); exact hwf
    · cases h
  | fuel + 1, fr, _, _, _, hwf, h => by
    unfold deallocAllM at h
    rcases hent : fr.locals.entries with _ | ⟨⟨local_, _⟩, _⟩ <;> simp only [hent] at h
    · obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h); exact hwf
    · obtain ⟨⟨fr1, cm1⟩, hsd, h⟩ := bind_ok h
      exact deallocAllM_tb_wfLive fuel (storageDeadM_tb_wfLive hwf hsd) h

/-- `evalReturnM` on `MachTB` preserves `MachTB.wfLive` across return-value
loading, local teardown (`deallocAllM`), and frame protector release (`end_call`). -/
theorem evalReturnM_tb_wfLive {m m' : MachTB}
    (hwf : MachTB.wfLive m) (h : evalReturnM m = .ok m') :
    MachTB.wfLive m' := by
  unfold evalReturnM at h
  obtain ⟨t, _, h⟩ := bind_ok h
  dsimp only at h
  cases hlast : t.stack.getLast? with
  | none => simp only [hlast] at h; cases h
  | some f =>
    simp only [hlast] at h
    obtain ⟨frame, hfr, h⟩ := bind_ok h
    cases interp_pure_ok hfr
    obtain ⟨threads, _, h⟩ := bind_ok h
    obtain ⟨calleeTy, _, h⟩ := bind_ok h
    obtain ⟨lay, _, h⟩ := bind_ok h
    obtain ⟨align, _, h⟩ := bind_ok h
    obtain ⟨retPtr, _, h⟩ := bind_ok h
    obtain ⟨⟨retVal, m1⟩, hload, h⟩ := bind_ok h
    have hm1 := typedLoadM_tb_wfLive (m := { m with threads := threads }) hwf hload
    obtain ⟨⟨frame1, cm1⟩, hdealloc, h⟩ := bind_ok h
    dsimp only at h
    have hcm1 := deallocAllM_tb_wfLive f.locals.entries.length hm1 hdealloc
    obtain ⟨cm2, hend, h⟩ := bind_ok h
    have hcm2 : MachTB.wfLive { m1 with mem := cm2 } := cm_tb_end_call_wfLive hcm1 hend
    cases hspa : frame1.stack_pop_action with
    | BottomOfStack =>
      simp only [hspa] at h
      exact terminateActiveThreadM_tb_wfLive hcm2 h
    | BackToCaller nextBlock _ callerRetPtr =>
      simp only [hspa] at h
      obtain ⟨t2, _, h⟩ := bind_ok h
      by_cases hst : t2.stack.length = 0
      · simp only [hst, ↓reduceIte] at h; cases h
      · simp only [hst, ↓reduceIte] at h
        obtain ⟨m2, hstore, h⟩ := bind_ok h
        have hm2 := typedStoreM_tb_wfLive hcm2 hstore
        cases nextBlock with
        | none => cases h
        | some nb => exact jumpToBlockM_tb_wfLive hm2 h

/-- `mutateActiveThreadM` on `MachTB` preserves `MachTB.wfLive`: it rewrites
one thread and leaves the memory alone. -/
private theorem mutateActiveThreadM_tb_wfLive {α : Type} {m m' : MachTB} {out : α}
    {f : Gen.Thread TBM → Interp (α × Gen.Thread TBM)}
    (hwf : MachTB.wfLive m) (h : mutateActiveThreadM m f = .ok (out, m')) :
    MachTB.wfLive m' := by
  unfold mutateActiveThreadM at h
  obtain ⟨t, _, h⟩ := bind_ok h
  obtain ⟨⟨_, t'⟩, _, h⟩ := bind_ok h
  obtain ⟨threads, _, h⟩ := bind_ok h
  obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_ok h)
  exact hwf

/-- `evalResumeUnwindM` on `MachTB` preserves `MachTB.wfLive` across local
teardown (`deallocAllM`), frame protector release (`end_call`), and the jump
to the caller's unwind block. -/
private theorem evalResumeUnwindM_tb_wfLive {m m' : MachTB}
    (hwf : MachTB.wfLive m) (h : evalResumeUnwindM m = .ok m') :
    MachTB.wfLive m' := by
  unfold evalResumeUnwindM at h
  obtain ⟨t, _, h⟩ := bind_ok h
  dsimp only at h
  cases hlast : t.stack.getLast? with
  | none => simp only [hlast] at h; cases h
  | some f =>
    simp only [hlast] at h
    obtain ⟨frame, hfr, h⟩ := bind_ok h
    cases interp_pure_ok hfr
    obtain ⟨threads, _, h⟩ := bind_ok h
    obtain ⟨⟨frame1, cm1⟩, hdealloc, h⟩ := bind_ok h
    dsimp only at h
    have hcm1 := deallocAllM_tb_wfLive f.locals.entries.length (cm := m.mem) hwf hdealloc
    obtain ⟨cm2, hend, h⟩ := bind_ok h
    have hcm2 : MachTB.wfLive { { m with threads := threads } with mem := cm2 } :=
      cm_tb_end_call_wfLive hcm1 hend
    cases hspa : frame1.stack_pop_action with
    | BottomOfStack => simp only [hspa] at h; cases h
    | BackToCaller _ unwindBlock _ =>
      simp only [hspa] at h
      cases unwindBlock with
      | none => cases h
      | some unwindBlock => exact jumpToBlockM_tb_wfLive hcm2 h

/-- `evalTerminatorM` on `MachTB` preserves `MachTB.wfLive`. -/
theorem evalTerminatorM_tb_wfLive {m m' : MachTB} {term : Gen.Terminator}
    (hwf : MachTB.wfLive m) (h : evalTerminatorM m term = .ok m') :
    MachTB.wfLive m' := by
  cases term with
  | Goto blockName => exact jumpToBlockM_tb_wfLive hwf h
  | Switch value cases fallback =>
    unfold evalTerminatorM at h
    obtain ⟨⟨⟨v, _⟩, m1⟩, hv, h⟩ := bind_ok h
    dsimp only at h
    have hm1 := evalValueM_tb_wfLive value hwf hv
    cases v with
    | Int i => exact jumpToBlockM_tb_wfLive hm1 h
    | _ => cases h
  | Unreachable => unfold evalTerminatorM at h; cases h
  | Call callee conv arguments retExpr nextBlock unwindBlock =>
    unfold evalTerminatorM at h
    obtain ⟨⟨⟨retPlace, retTy⟩, m1⟩, hp, h⟩ := bind_ok h
    obtain ⟨m2, hprep, h⟩ := bind_ok h
    obtain ⟨⟨⟨calleeVal, _⟩, m3⟩, hv, h⟩ := bind_ok h
    obtain ⟨calleeFn, _, h⟩ := bind_ok h
    obtain ⟨⟨args, m4⟩, hargs, h⟩ := bind_ok h
    exact evalCallM_tb_wfLive
      (evalArgumentsM_tb_wfLive arguments
        (evalValueM_tb_wfLive callee
          (prepareForInplacePassingM_tb_wfLive (evalPlaceM_tb_wfLive retExpr hwf hp) hprep) hv)
        hargs) h
  | Return => exact evalReturnM_tb_wfLive hwf h
  | Intrinsic intrinsic arguments retExpr nextBlock =>
    unfold evalTerminatorM at h
    obtain ⟨⟨⟨retPlace, retTy⟩, m1⟩, hp, h⟩ := bind_ok h
    obtain ⟨⟨args, m2⟩, ha, h⟩ := bind_ok h
    obtain ⟨⟨val, m3⟩, hi, h⟩ := bind_ok h
    obtain ⟨m4, hs, h⟩ := bind_ok h
    have hm4 := placeStoreM_tb_wfLive
      (evalIntrinsicM_tb_wfLive
        (evalArgsM_tb_wfLive arguments (evalPlaceM_tb_wfLive retExpr hwf hp) ha) hi) hs
    cases nextBlock with
    | none => cases h
    | some nb => exact jumpToBlockM_tb_wfLive hm4 h
  | StartUnwind payload blk =>
    unfold evalTerminatorM at h
    obtain ⟨⟨⟨v, ty⟩, m1⟩, hv, h⟩ := bind_ok h
    dsimp only at h
    have hm1 := evalValueM_tb_wfLive payload hwf hv
    split at h
    · obtain ⟨⟨_, m2⟩, hmut, h⟩ := bind_ok h
      exact jumpToBlockM_tb_wfLive (mutateActiveThreadM_tb_wfLive hm1 hmut) h
    · cases h
  | StopUnwind blk =>
    unfold evalTerminatorM at h
    obtain ⟨⟨_, m1⟩, hmut, h⟩ := bind_ok h
    exact jumpToBlockM_tb_wfLive (mutateActiveThreadM_tb_wfLive hwf hmut) h
  | ResumeUnwind => exact evalResumeUnwindM_tb_wfLive hwf h

/-- Every single step of `MachTB` (`stepTB`) preserves `MachTB.wfLive`. -/
theorem stepTB_wfLive {m m' : MachTB}
    (hwf : MachTB.wfLive m) (h : stepTB m = .ok m') :
    MachTB.wfLive m' := by
  unfold stepTB stepM at h
  cases hany : m.threads.any (fun t => decide (t.state = .Enabled)) with
  | false => simp only [hany, Bool.not_false, ↓reduceIte] at h; cases h
  | true =>
    simp only [hany, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    dsimp only [resetDataRaceTrackingM] at h
    obtain ⟨tid, _, h⟩ := bind_ok h
    obtain ⟨frame, _, h⟩ := bind_ok h
    obtain ⟨block, _, h⟩ := bind_ok h
    have hm0 : MachTB.wfLive
        { { m with mem := { m.mem with accesses := [] } } with active_thread := tid } := hwf
    by_cases hns : frame.next_stmt = (block.statements.length : Int)
    · simp only [hns, ↓reduceIte] at h
      obtain ⟨m2, hterm, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain rfl := interp_pure_ok h
      exact evalTerminatorM_tb_wfLive hm0 hterm
    · simp only [hns, ↓reduceIte] at h
      obtain ⟨stmt, _, h⟩ := bind_ok h
      obtain ⟨m1, hev, h⟩ := bind_ok h
      obtain ⟨m2, hmut, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain rfl := interp_pure_ok h
      exact mutateCurFrameM_tb_wfLive (evalStatementM_tb_wfLive hm0 hev) hmut

/-- Arbitrary multi-step execution of `MachTB` (`stepsTB n`) preserves
`MachTB.wfLive` across every `n : Nat` (statements, reborrows, `Validate`/`Retag`,
`StorageLive`/`StorageDead`, `Box` deallocations, loops, and `Return`/`end_call`). -/
theorem stepsTB_wfLive :
    ∀ {n : Nat} {m m' : MachTB},
      MachTB.wfLive m → stepsTB n m = .ok m' → MachTB.wfLive m'
  | 0, _, _, hwf, h => by
    unfold stepsTB stepsM at h
    obtain rfl := interp_pure_ok h
    exact hwf
  | _ + 1, _, _, hwf, h => by
    unfold stepsTB stepsM at h
    obtain ⟨m1, hs, h⟩ := bind_ok h
    exact stepsTB_wfLive (stepTB_wfLive hwf hs) h

end MiniRustSpec.Correspondence
