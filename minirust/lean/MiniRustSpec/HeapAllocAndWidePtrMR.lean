/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import MiniRustSpec.Interp
import MiniRustSpec.Correspondence.Pointers

/-!
# MiniRust heap allocation, deallocation, leak check, and wide-pointer `addr_eq`

This module is about MiniRust `d821c6e3` only. It studies the heap intrinsics
`IntrinsicOp::{Allocate, Deallocate}` of `spec/lang/step/intrinsics.md`, the
memory-model operations behind them (`BasicMemory::{allocate, deallocate,
leak_check}` of `spec/mem/basic.md` and `TreeBorrowsMemory::{deallocate,
end_call, leak_check}` of `spec/mem/tree_borrows/memory.md`), and the pointer
comparison `Machine::compare_ptr` with `UnOp::GetThinPointer` of
`spec/lang/step/operators.md`, as `MiniRustSpec.Interp` interprets them on
`Machine<BasicMemory<x86_64>>` (`Mach`), on `Machine<TreeBorrowsMemory<x86_64>>`
(`MachTB`), and polymorphically (`evalIntrinsicM`, `evalUnOpM`, `evalBinOpM`).
Nothing here mentions Anneal's MIR semantics or Miri;
`MiniRustSpec.Correspondence.Pointers` is imported for its MiniRust-side facts
only (`MachTB.wfLive` and the Tree Borrows preservation lemmas).

* **§1** `evalIntrinsicM` has exactly one outcome; on `Allocate` and
  `Deallocate`, `evalIntrinsicM` at `BasicMemory` is `evalIntrinsic`
  (`evalIntrinsicM_bm_eq_heap`); both preserve `MachTB.wfLive`
  (`evalIntrinsicM_allocate_tb_wfLive`, `evalIntrinsicM_deallocate_tb_wfLive`).
* **§2** Complete bidirectional characterizations of `.ok` and `.error`, in
  exact upstream check order, for `Allocate` and `Deallocate` in every memory
  model (`allocate_{ok,error}_iff`, `deallocate_{ok,error}_iff`), and the
  individual guard laws.
* **§3** The memory-model laws: `BasicMemory::allocate`
  (`basicMemory_allocate_{ok,error}_iff`), `BasicMemory::deallocate` in exact
  upstream check order for every `ProvExtra`, `AllocExtra`, and `handle_extra`
  (`basicMemory_deallocate_{ok,error}_iff`), its `BasicMemory<x86_64>` and
  `TreeBorrowsMemory<x86_64>` instances, the Tree Borrows deallocation handler
  (`Node::access` with `AccessKind::Write`, then
  `Node::contains_strong_protector_preventing_deallocation`), the protector
  classification (`Protected::Weak` never prevents deallocation,
  `Protected::Strong` does exactly for `Unique`, `Reserved`/`Frozen` with a
  local read; `Cell` never does), and `leak_check` for `BasicMemory`,
  `TreeBorrowsMemory`, and `ConcurrentMemory` (`MemoryLeak` iff a live `Heap`
  allocation exists).
* **§4** `ptr::addr_eq` as `GetThinPointer` on both sides followed by
  `BinOp::Rel(Eq)` (`evalAddrEqM`): it compares addresses only, for every pair
  of pointers, whatever their metadata and provenance (`evalAddrEqM_ptr`),
  whereas `==` on wide pointers also compares metadata and panics on
  mismatched metadata kinds (`evalWideEqM_slice`, `evalWideEqM_vtable`,
  `evalWideEqM_mixed_specPanic`).
* **§5** Kernel-evaluated witnesses on `Mach` and `MachTB`: the 30 cases of
  `mrHeapWideObserve` with their exact `Stop`s, and the threaded traces
  `mrHeapLifecycleTrace` and `mrProtectorDeallocTrace`.
* **§6** Instances showing that the conditional laws are not vacuous, the
  Episode 1 capstone `ep1_minirust_heap_wide_capstone`, and the axiom and
  import audit.

## What the laws say about upstream MiniRust `d821c6e3`

1. **`Deallocate` checks in a fixed order, and the first failure wins**:
   provenance, liveness (`"double-free"`), offset, kind, size, alignment, and
   only then the memory model's `handle_extra` (`basicMemory_deallocate_error_iff`).
   Deallocating a dead allocation through a pointer into its middle is a
   double-free, not an offset error.
2. **`Allocate` accepts every power-of-two alignment**: `Align::from_bytes` has
   no upper bound, so `Allocate(0, 2^30)` succeeds (case 29), where rustc's
   `Align::MAX` is `2^29`.
3. **The explicit strong-protector check of `TreeBorrowsMemory::deallocate` is
   only reachable through the protected node or its descendants.** Upstream
   notes that `prevents_deallocation` is equivalent to
   `foreign_write().is_err()`; deallocating through a *foreign* tag therefore
   already fails in `Node::access` (case 19: `"Tree Borrows: foreign write of
   protected Frozen reference which had a local read"`), and the dedicated message `"Tree Borrows:
   deallocating strongly protected allocation"` appears when the allocation is
   deallocated through the strongly protected tag itself
   (`strongProtector_dealloc_through_protected_tag`).
4. **`leak_check` only looks at `AllocationKind::Heap`**: live `Global`,
   `Stack`, `Function`, and `VTable` allocations never leak
   (`basicMemory_leak_check_ok_of_no_heap`).
5. **`ptr::addr_eq` cannot panic, `==` can.** `GetThinPointer` erases the
   metadata, so `addr_eq` is defined on a slice pointer and a trait-object
   pointer, where `==` reaches `panic!("unmatching metadata in wide pointer
   comparasion")` (upstream's spelling).
-/

namespace MiniRustSpec.HeapAllocAndWidePtrMR

open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.LibSpecr MiniRustSpec.Interp

/-! ## §0. Proof infrastructure -/

/-- Close an equality goal with `Eq.refl`, leaving the definitional unfolding
to the kernel (no `Lean.ofReduceBool`, no compiler trust). -/
local elab "kernel_rfl" : tactic => do
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  let tgt ← Lean.MVarId.getType' mvarId
  let some (ty, lhs, _) := tgt.eq? | Lean.Meta.throwTacticEx `kernel_rfl mvarId "expected equality goal"
  let u ← Lean.Meta.getLevel ty
  mvarId.assign (Lean.mkApp2 (Lean.mkConst ``Eq.refl [u]) ty lhs)
  Lean.Elab.Tactic.replaceMainGoal []

/-- Inversion of a successful `?` chain. -/
theorem interp_bind_eq_ok {α β : Type} {x : Interp α} {f : α → Interp β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- Inversion of `ret(x)`. -/
theorem interp_pure_eq_ok {α : Type} {x y : α} (h : (pure x : Interp α) = .ok y) : x = y := by
  cases h
  rfl

/-- Inversion of a stopping `?` chain. -/
theorem interp_bind_eq_error {α β : Type} {x : Interp α} {f : α → Interp β} {e : Stop}
    (h : (x >>= f) = .error e) : x = .error e ∨ ∃ a, x = .ok a ∧ f a = .error e := by
  cases x with
  | error s =>
    cases h
    exact Or.inl rfl
  | ok a => exact Or.inr ⟨a, rfl, h⟩

/-- The two heap intrinsics of `spec/lang/step/intrinsics.md`. -/
def isHeapOp : IntrinsicOp → Bool
  | .Allocate | .Deallocate => true
  | _ => false

/-- `Size::from_bytes` of a negative integer is `None`. -/
theorem sizeFromBytes_neg {n : Int} (h : n < 0) : sizeFromBytes n = none := by
  simp only [sizeFromBytes, h, ↓reduceIte]

/-- `Size::from_bytes` of a non-negative integer is that many bytes. -/
theorem sizeFromBytes_nonneg {n : Int} (h : 0 ≤ n) : sizeFromBytes n = some ⟨n.toNat⟩ := by
  simp only [sizeFromBytes, Int.not_lt.mpr h, ↓reduceIte]

/-- `Size::from_bytes` succeeds exactly on non-negative integers. -/
theorem sizeFromBytes_eq_some_iff {n : Int} {sz : Size} :
    sizeFromBytes n = some sz ↔ 0 ≤ n ∧ sz = ⟨n.toNat⟩ := by
  constructor
  · intro h
    by_cases hn : n < 0
    · rw [sizeFromBytes_neg hn] at h; cases h
    · have hn' : 0 ≤ n := Int.not_lt.mp hn
      rw [sizeFromBytes_nonneg hn'] at h
      exact ⟨hn', (Option.some.inj h).symm⟩
  · rintro ⟨hn, rfl⟩
    exact sizeFromBytes_nonneg hn

/-- `Align::from_bytes(0)` is `None`: alignment must be a positive power of two. -/
theorem alignFromBytesInt_zero : alignFromBytesInt 0 = none := rfl

/-- `Align::from_bytes` of any negative integer is `None`. -/
theorem alignFromBytesInt_neg {n : Int} (h : n < 0) : alignFromBytesInt n = none := by
  simp only [alignFromBytesInt, h, ↓reduceIte]

/-- Bitwise helper: `2^k &&& (2^k - 1) = 0` for every natural exponent `k`. -/
theorem nat_pow2_land_pred (k : Nat) : (2 ^ k) &&& (2 ^ k - 1) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_two_pow]
  by_cases hik : k = i
  · subst hik
    have hlt : 2 ^ k - 1 < 2 ^ k := Nat.sub_lt (Nat.two_pow_pos k) (Nat.zero_lt_one)
    have hbit : (2 ^ k - 1).testBit k = false := by
      unfold Nat.testBit
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt]
      rfl
    rw [hbit, Bool.and_false]
  · simp [hik]

/-- `Align::from_bytes` accepts *every* power of two `2^k`, with no upper bound
(unlike `rustc_abi::Align::MAX = 2^29`, explaining case 29 universally). -/
theorem alignFromBytesInt_pow2 (k : Nat) :
    alignFromBytesInt ((2 : Int) ^ k) = some ⟨2 ^ k⟩ := by
  have hpos : (0 : Int) ≤ (2 : Int) ^ k := Int.pow_nonneg (by decide)
  have hnotlt : ¬ ((2 : Int) ^ k < 0) := Int.not_lt.mpr hpos
  have htoNat : ((2 : Int) ^ k).toNat = 2 ^ k := by
    change ((2 ^ k : Nat) : Int).toNat = 2 ^ k
    exact Int.toNat_natCast (2 ^ k)
  unfold alignFromBytesInt alignFromBytes
  rw [ite_eq_right hnotlt, htoNat]
  exact ite_eq_left ⟨Nat.ne_of_gt (Nat.two_pow_pos k), nat_pow2_land_pred k⟩

/-- `Align::from_bytes` succeeds exactly on positive powers of two. -/
theorem alignFromBytesInt_eq_some_iff {n : Int} {al : Align} :
    alignFromBytesInt n = some al ↔
      0 < n ∧ n.toNat &&& (n.toNat - 1) = 0 ∧ al = ⟨n.toNat⟩ := by
  unfold alignFromBytesInt alignFromBytes
  by_cases hn : n < 0
  · rw [ite_eq_left hn]
    constructor
    · intro h; cases h
    · rintro ⟨hpos, _⟩; omega
  · rw [ite_eq_right hn]
    by_cases hcond : n.toNat ≠ 0 ∧ n.toNat &&& (n.toNat - 1) = 0
    · rw [ite_eq_left hcond]
      constructor
      · intro h
        have hpos : 0 < n := by omega
        exact ⟨hpos, hcond.2, (Option.some.inj h).symm⟩
      · rintro ⟨_, _, rfl⟩; rfl
    · rw [ite_eq_right hcond]
      constructor
      · intro h; cases h
      · rintro ⟨hpos, hbit, _⟩
        exact absurd ⟨by omega, hbit⟩ hcond

/-- `x86_64::valid_size` holds iff the byte size is strictly below `2^63`
(`isize::MAX = 2^63 - 1`). -/
theorem x86_64_valid_size_iff (sz : Size) :
    x86_64.valid_size sz = true ↔ sz.bytes < 2 ^ 63 := by
  unfold x86_64.valid_size inBounds Size.bits x86_64.PTR_SIZE
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- `x86_64::valid_size` is false iff the byte size is at least `2^63`. -/
theorem x86_64_valid_size_false_iff (sz : Size) :
    x86_64.valid_size sz = false ↔ 2 ^ 63 ≤ sz.bytes := by
  by_cases hlt : sz.bytes < 2 ^ 63
  · have ht : x86_64.valid_size sz = true := (x86_64_valid_size_iff sz).mpr hlt
    rw [ht]
    constructor
    · intro h; cases h
    · intro h; omega
  · have hge : 2 ^ 63 ≤ sz.bytes := Nat.le_of_not_lt hlt
    have hf : x86_64.valid_size sz = false := by
      cases h : x86_64.valid_size sz with
      | false => rfl
      | true => exact absurd ((x86_64_valid_size_iff sz).mp h) hlt
    rw [hf]
    exact ⟨fun _ => hge, fun _ => rfl⟩

/-! ## §1. Determinism, `BasicMemory` equivalence, and `MachTB.wfLive` -/

section Determinism

variable {M : Type} [Memory M] [MemoryOps M]

/-- `Machine::eval_intrinsic` is a function into `Result`: an intrinsic has
exactly one outcome. For `Allocate`, whose upstream address choice is
daemonic (`pick`), this is the outcome under the interpretation's first-fit
resolution of that choice (`BasicMemory.pickAddr`). -/
theorem evalIntrinsicM_outcome_unique (m : Machine M) (op : IntrinsicOp)
    (args : List (Value M × «Type»)) (retTy : «Type») :
    ∃ r : Interp (Value M × Machine M), evalIntrinsicM m op args retTy = r ∧
      ∀ r', evalIntrinsicM m op args retTy = r' → r' = r :=
  ⟨_, rfl, fun _ h => h.symm⟩

/-- Two successful evaluations of the same intrinsic agree on the returned
value and on the resulting machine. -/
theorem evalIntrinsicM_ok_unique {m : Machine M} {op : IntrinsicOp}
    {args : List (Value M × «Type»)} {retTy : «Type»} {v1 v2 : Value M} {m1 m2 : Machine M}
    (h1 : evalIntrinsicM m op args retTy = .ok (v1, m1))
    (h2 : evalIntrinsicM m op args retTy = .ok (v2, m2)) : v1 = v2 ∧ m1 = m2 := by
  rw [h1] at h2
  cases h2
  exact ⟨rfl, rfl⟩

/-- Two stopping evaluations of the same intrinsic stop for the same reason. -/
theorem evalIntrinsicM_error_unique {m : Machine M} {op : IntrinsicOp}
    {args : List (Value M × «Type»)} {retTy : «Type»} {s1 s2 : Stop}
    (h1 : evalIntrinsicM m op args retTy = .error s1)
    (h2 : evalIntrinsicM m op args retTy = .error s2) : s1 = s2 := by
  rw [h1] at h2
  cases h2
  rfl

/-- An intrinsic that returns does not also stop. -/
theorem evalIntrinsicM_ok_not_error {m : Machine M} {op : IntrinsicOp}
    {args : List (Value M × «Type»)} {retTy : «Type»} {r : Value M × Machine M}
    (h : evalIntrinsicM m op args retTy = .ok r) (s : Stop) :
    evalIntrinsicM m op args retTy ≠ .error s := by
  rw [h]
  intro hc
  cases hc

end Determinism

/-! ### `BasicMemory` equivalence of the heap intrinsics -/

/-- `ConcurrentMemory::allocate` at `M = BasicMemory<x86_64>` is `CM.allocate`. -/
theorem cm_allocate_bm_eq (cm : ConcurrentMemory BM) (kind : AllocationKind) (size : Size)
    (align : Align) :
    ConcurrentMemory.allocate (M := BM) cm kind size align = CM.allocate cm kind size align := by
  unfold ConcurrentMemory.allocate CM.allocate MemoryOps.allocate instMemoryOpsBM
  rfl

/-- `ConcurrentMemory::deallocate` at `M = BasicMemory<x86_64>` is `CM.deallocate`. -/
theorem cm_deallocate_bm_eq (cm : ConcurrentMemory BM) (ptr : Ptr) (kind : AllocationKind)
    (size : Size) (align : Align) :
    ConcurrentMemory.deallocate (M := BM) cm ptr kind size align =
      CM.deallocate cm ptr kind size align := rfl

/-- `ConcurrentMemory::leak_check` at `M = BasicMemory<x86_64>` is `CM.leak_check`. -/
theorem cm_leak_check_bm_eq (cm : ConcurrentMemory BM) :
    ConcurrentMemory.leak_check (M := BM) cm = CM.leak_check cm := rfl

/-- On `Allocate`, the polymorphic `evalIntrinsicM` at `M = BasicMemory<x86_64>`
is the `BasicMemory` transcription `evalIntrinsic`. -/
theorem evalIntrinsicM_bm_eq_allocate (m : Mach) (args : List (Val × «Type»)) (retTy : «Type») :
    evalIntrinsicM (M := BM) m .Allocate args retTy = evalIntrinsic m .Allocate args retTy := by
  have hfun : @ConcurrentMemory.allocate BM _ _ = CM.allocate := by
    funext cm kind size align
    exact cm_allocate_bm_eq cm kind size align
  simp only [evalIntrinsicM, evalIntrinsic, hfun]
  rcases args with _ | ⟨⟨sizeV, sT⟩, _ | ⟨⟨alignV, aT⟩, _ | ⟨_, _⟩⟩⟩ <;> try rfl
  cases sizeV with
  | Int size =>
    rcases hs : sizeFromBytes size with _ | sz <;> simp only [hs]
    cases alignV with
    | Int align =>
      rcases ha : alignFromBytesInt align with _ | al <;> simp only [ha]
      cases retTy with
      | Ptr retPtrTy => by_cases hk : PtrType.meta_kind retPtrTy = .None <;> simp [hk] <;> rfl
      | _ => rfl
    | _ => rfl
  | _ => rfl

/-- On `Deallocate`, the polymorphic `evalIntrinsicM` at `M = BasicMemory<x86_64>`
is the `BasicMemory` transcription `evalIntrinsic`. -/
theorem evalIntrinsicM_bm_eq_deallocate (m : Mach) (args : List (Val × «Type»))
    (retTy : «Type») :
    evalIntrinsicM (M := BM) m .Deallocate args retTy = evalIntrinsic m .Deallocate args retTy := by
  have hfun : @ConcurrentMemory.deallocate BM _ _ = CM.deallocate := by
    funext cm ptr kind size align
    exact cm_deallocate_bm_eq cm ptr kind size align
  simp only [evalIntrinsicM, evalIntrinsic, hfun]
  rcases args with _ | ⟨⟨ptrV, pT⟩, _ | ⟨⟨sizeV, sT⟩, _ | ⟨⟨alignV, aT⟩, _ | ⟨_, _⟩⟩⟩⟩ <;>
    try rfl
  rcases ptrV with _ | _ | ⟨ptr, _ | _⟩ | _ | _ <;> try rfl
  cases sizeV with
  | Int size =>
    rcases hs : sizeFromBytes size with _ | sz <;> simp only [hs]
    cases alignV with
    | Int align =>
      rcases ha : alignFromBytesInt align with _ | al <;> simp only [ha]
      split <;> rfl
    | _ => rfl
  | _ => rfl

/-- On the heap intrinsics, `evalIntrinsicM (M := BM) = evalIntrinsic`. Every
law of §2, stated for `evalIntrinsicM` in every memory model, therefore holds
of `evalIntrinsic` on `Mach`. -/
theorem evalIntrinsicM_bm_eq_heap (m : Mach) (op : IntrinsicOp) (args : List (Val × «Type»))
    (retTy : «Type») (hop : isHeapOp op = true) :
    evalIntrinsicM (M := BM) m op args retTy = evalIntrinsic m op args retTy := by
  cases op with
  | Allocate => exact evalIntrinsicM_bm_eq_allocate m args retTy
  | Deallocate => exact evalIntrinsicM_bm_eq_deallocate m args retTy
  | _ => exact Bool.noConfusion hop

/-! ## §2. `Allocate` and `Deallocate`: guards and complete characterizations

`Machine::eval_intrinsic` checks the arguments and the return type of the
heap intrinsics in a fixed order and only then calls into the memory model.
Every law holds in every memory model `M`. -/

section Guards

variable {M : Type} [Memory M] [MemoryOps M]

/-! ### `Allocate` -/

/-- `Allocate` on two integer arguments, after the arity and integer checks:
size, alignment, return type, pointee, and then `ConcurrentMemory::allocate`
with `AllocationKind::Heap`. -/
theorem allocate_eq (m : Machine M) (size : Int) (sTy : «Type») (align : Int) (aTy : «Type»)
    (retTy : «Type») :
    evalIntrinsicM m .Allocate [(.Int size, sTy), (.Int align, aTy)] retTy =
      match sizeFromBytes size with
      | some size =>
        match alignFromBytesInt align with
        | some align =>
          match retTy with
          | .Ptr retPtrTy =>
            if PtrType.meta_kind retPtrTy = .None then do
              let (alloc, cm) ← ConcurrentMemory.allocate m.mem .Heap size align
              pure (.Ptr (ThinPointer.widen alloc none), { m with mem := cm })
            else
              ub "unsized pointee requested for `Allocate` intrinsic"
          | _ => ub "invalid return type for `Allocate` intrinsic"
        | none => ub "invalid alignment for `Allocate` intrinsic: not a power of 2"
      | none => ub "invalid size for `Allocate` intrinsic: negative size" := rfl

/-- `Allocate` with the wrong number of arguments is UB. -/
theorem allocate_arity_ub (m : Machine M) (args : List (Value M × «Type»)) (retTy : «Type»)
    (h : args.length ≠ 2) :
    evalIntrinsicM m .Allocate args retTy =
      .error (.ub "invalid number of arguments for `Allocate` intrinsic") := by
  rcases args with _ | ⟨⟨_, _⟩, _ | ⟨⟨_, _⟩, _ | ⟨_, _⟩⟩⟩
  · rfl
  · rfl
  · exact absurd rfl h
  · rfl

/-- `Allocate` whose first argument is not an integer is UB. -/
theorem allocate_size_not_int_ub (m : Machine M) (sizeV : Value M) (sTy : «Type»)
    (alignV : Value M) (aTy retTy : «Type») (h : ∀ i, sizeV ≠ .Int i) :
    evalIntrinsicM m .Allocate [(sizeV, sTy), (alignV, aTy)] retTy =
      .error (.ub "invalid first argument to `Allocate` intrinsic: not an integer") := by
  cases sizeV with
  | Int i => exact absurd rfl (h i)
  | _ => rfl

/-- `Allocate` with a negative size is UB. -/
theorem allocate_negative_size_ub (m : Machine M) (size : Int) (sTy : «Type»)
    (alignV : Value M) (aTy retTy : «Type») (h : size < 0) :
    evalIntrinsicM m .Allocate [(.Int size, sTy), (alignV, aTy)] retTy =
      .error (.ub "invalid size for `Allocate` intrinsic: negative size") := by
  simp only [evalIntrinsicM, sizeFromBytes_neg h]
  rfl

/-- `Allocate` whose second argument is not an integer is UB (after the size
checks). -/
theorem allocate_align_not_int_ub (m : Machine M) (size : Int) (sTy : «Type»)
    (alignV : Value M) (aTy retTy : «Type») (hs : 0 ≤ size) (h : ∀ i, alignV ≠ .Int i) :
    evalIntrinsicM m .Allocate [(.Int size, sTy), (alignV, aTy)] retTy =
      .error (.ub "invalid second argument to `Allocate` intrinsic: not an integer") := by
  simp only [evalIntrinsicM, sizeFromBytes_nonneg hs]
  cases alignV with
  | Int i => exact absurd rfl (h i)
  | _ => rfl

/-- `Allocate` with an alignment that is not a power of two is UB. This
covers `align = 0`, negative alignments, and e.g. `align = 3`. -/
theorem allocate_align_not_pow2_ub (m : Machine M) (size : Int) (sTy : «Type») (align : Int)
    (aTy retTy : «Type») (hs : 0 ≤ size) (h : alignFromBytesInt align = none) :
    evalIntrinsicM m .Allocate [(.Int size, sTy), (.Int align, aTy)] retTy =
      .error (.ub "invalid alignment for `Allocate` intrinsic: not a power of 2") := by
  rw [allocate_eq, sizeFromBytes_nonneg hs, h]
  rfl

/-- `Allocate` with `align = 0` is UB across every memory model `M`. -/
theorem allocate_align_zero_ub (m : Machine M) (size : Int) (sTy aTy retTy : «Type»)
    (hs : 0 ≤ size) :
    evalIntrinsicM m .Allocate [(.Int size, sTy), (.Int 0, aTy)] retTy =
      .error (.ub "invalid alignment for `Allocate` intrinsic: not a power of 2") :=
  allocate_align_not_pow2_ub m size sTy 0 aTy retTy hs alignFromBytesInt_zero

/-- `Allocate` at a return type that is not a pointer is UB. -/
theorem allocate_ret_not_ptr_ub (m : Machine M) (size : Int) (sTy : «Type») (align : Int)
    (aTy retTy : «Type») (al : Align) (hs : 0 ≤ size) (ha : alignFromBytesInt align = some al)
    (h : ∀ p, retTy ≠ .Ptr p) :
    evalIntrinsicM m .Allocate [(.Int size, sTy), (.Int align, aTy)] retTy =
      .error (.ub "invalid return type for `Allocate` intrinsic") := by
  rw [allocate_eq, sizeFromBytes_nonneg hs, ha]
  cases retTy with
  | Ptr p => exact absurd rfl (h p)
  | _ => rfl

/-- `Allocate` at a wide pointer return type (unsized pointee) is UB. -/
theorem allocate_unsized_pointee_ub (m : Machine M) (size : Int) (sTy : «Type») (align : Int)
    (aTy : «Type») (p : PtrType) (al : Align) (hs : 0 ≤ size)
    (ha : alignFromBytesInt align = some al) (h : PtrType.meta_kind p ≠ .None) :
    evalIntrinsicM m .Allocate [(.Int size, sTy), (.Int align, aTy)] (.Ptr p) =
      .error (.ub "unsized pointee requested for `Allocate` intrinsic") := by
  rw [allocate_eq, sizeFromBytes_nonneg hs, ha]
  simp only [h, ↓reduceIte]
  rfl

/-- `Allocate` past its checks is `ConcurrentMemory::allocate` with
`AllocationKind::Heap`, returning the thin pointer. -/
theorem allocate_eq_memory (m : Machine M) (size : Int) (sTy : «Type») (align : Int)
    (aTy : «Type») (p : PtrType) (al : Align) (hs : 0 ≤ size)
    (ha : alignFromBytesInt align = some al) (h : PtrType.meta_kind p = .None) :
    evalIntrinsicM m .Allocate [(.Int size, sTy), (.Int align, aTy)] (.Ptr p) =
      (do
        let (alloc, cm) ← ConcurrentMemory.allocate m.mem .Heap ⟨size.toNat⟩ al
        pure (.Ptr (ThinPointer.widen alloc none), { m with mem := cm })) := by
  rw [allocate_eq, sizeFromBytes_nonneg hs, ha]
  simp only [h, ↓reduceIte]

/-- Complete characterization of a successful `Allocate` in every memory
model. -/
theorem allocate_ok_iff {m m' : Machine M} {args : List (Value M × «Type»)} {retTy : «Type»}
    {val : Value M} :
    evalIntrinsicM m .Allocate args retTy = .ok (val, m') ↔
      ∃ size sTy align aTy al p ptr cm,
        args = [(.Int size, sTy), (.Int align, aTy)] ∧ 0 ≤ size ∧
        alignFromBytesInt align = some al ∧
        retTy = .Ptr p ∧ PtrType.meta_kind p = .None ∧
        ConcurrentMemory.allocate m.mem .Heap ⟨size.toNat⟩ al = .ok (ptr, cm) ∧
        val = .Ptr (ThinPointer.widen ptr none) ∧
        m' = { m with mem := cm } := by
  constructor
  · intro h
    rcases args with _ | ⟨⟨sizeV, sTy⟩, _ | ⟨⟨alignV, aTy⟩, _ | ⟨_, _⟩⟩⟩
    · dsimp only [evalIntrinsicM, ub] at h; cases h
    · dsimp only [evalIntrinsicM, ub] at h; cases h
    · cases sizeV with
      | Int size =>
        by_cases hs : size < 0
        · rw [allocate_negative_size_ub m size sTy alignV aTy retTy hs] at h; cases h
        · have hs' : 0 ≤ size := Int.not_lt.mp hs
          cases alignV with
          | Int align =>
            cases ha : alignFromBytesInt align with
            | none => rw [allocate_align_not_pow2_ub m size sTy align aTy retTy hs' ha] at h; cases h
            | some al =>
              by_cases hp : ∃ p, retTy = .Ptr p
              · obtain ⟨p, rfl⟩ := hp
                by_cases hk : PtrType.meta_kind p = .None
                · rw [allocate_eq_memory m size sTy align aTy p al hs' ha hk] at h
                  obtain ⟨⟨ptr, cm⟩, hal, h⟩ := interp_bind_eq_ok h
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok h)
                  exact ⟨size, sTy, align, aTy, al, p, ptr, cm, rfl, hs', ha, rfl, hk, hal, rfl, rfl⟩
                · rw [allocate_unsized_pointee_ub m size sTy align aTy p al hs' ha hk] at h
                  cases h
              · rw [allocate_ret_not_ptr_ub m size sTy align aTy retTy al hs' ha
                  (fun p hc => hp ⟨p, hc⟩)] at h
                cases h
          | _ =>
            rw [allocate_align_not_int_ub m size sTy _ aTy retTy hs' (fun _ hc => by cases hc)] at h
            cases h
      | _ =>
        rw [allocate_size_not_int_ub m _ sTy alignV aTy retTy (fun _ hc => by cases hc)] at h
        cases h
    · dsimp only [evalIntrinsicM, ub] at h; cases h
  · rintro ⟨size, sTy, align, aTy, al, p, ptr, cm, rfl, hs, ha, rfl, hk, hal, rfl, rfl⟩
    rw [allocate_eq_memory m size sTy align aTy p al hs ha hk, hal]
    rfl

/-- Complete characterization of every stopping outcome of `Allocate`, in
exact upstream check order, in every memory model. -/
theorem allocate_error_iff {m : Machine M} {args : List (Value M × «Type»)} {retTy : «Type»}
    {e : Stop} :
    evalIntrinsicM m .Allocate args retTy = .error e ↔
      (args.length ≠ 2 ∧ e = .ub "invalid number of arguments for `Allocate` intrinsic") ∨
      (∃ sizeV sTy alignV aTy, args = [(sizeV, sTy), (alignV, aTy)] ∧ (∀ i, sizeV ≠ .Int i) ∧
        e = .ub "invalid first argument to `Allocate` intrinsic: not an integer") ∨
      (∃ size sTy alignV aTy, args = [(.Int size, sTy), (alignV, aTy)] ∧ size < 0 ∧
        e = .ub "invalid size for `Allocate` intrinsic: negative size") ∨
      (∃ size sTy alignV aTy, args = [(.Int size, sTy), (alignV, aTy)] ∧ 0 ≤ size ∧
        (∀ i, alignV ≠ .Int i) ∧
        e = .ub "invalid second argument to `Allocate` intrinsic: not an integer") ∨
      (∃ size sTy align aTy, args = [(.Int size, sTy), (.Int align, aTy)] ∧ 0 ≤ size ∧
        alignFromBytesInt align = none ∧
        e = .ub "invalid alignment for `Allocate` intrinsic: not a power of 2") ∨
      (∃ size sTy align aTy al, args = [(.Int size, sTy), (.Int align, aTy)] ∧ 0 ≤ size ∧
        alignFromBytesInt align = some al ∧ (∀ p, retTy ≠ .Ptr p) ∧
        e = .ub "invalid return type for `Allocate` intrinsic") ∨
      (∃ size sTy align aTy al p, args = [(.Int size, sTy), (.Int align, aTy)] ∧ 0 ≤ size ∧
        alignFromBytesInt align = some al ∧ retTy = .Ptr p ∧ PtrType.meta_kind p ≠ .None ∧
        e = .ub "unsized pointee requested for `Allocate` intrinsic") ∨
      (∃ size sTy align aTy al p, args = [(.Int size, sTy), (.Int align, aTy)] ∧ 0 ≤ size ∧
        alignFromBytesInt align = some al ∧ retTy = .Ptr p ∧ PtrType.meta_kind p = .None ∧
        ConcurrentMemory.allocate m.mem .Heap ⟨size.toNat⟩ al = .error e) := by
  constructor
  · intro h
    rcases args with _ | ⟨⟨sizeV, sTy⟩, _ | ⟨⟨alignV, aTy⟩, _ | ⟨_, _⟩⟩⟩
    · dsimp only [evalIntrinsicM, ub] at h; cases h; exact Or.inl ⟨by show 0 ≠ 2; decide, rfl⟩
    · dsimp only [evalIntrinsicM, ub] at h; cases h; exact Or.inl ⟨by show 1 ≠ 2; decide, rfl⟩
    · refine Or.inr ?_
      cases sizeV with
      | Int size =>
        refine Or.inr ?_
        by_cases hs : size < 0
        · rw [allocate_negative_size_ub m size sTy alignV aTy retTy hs] at h; cases h
          exact Or.inl ⟨size, sTy, alignV, aTy, rfl, hs, rfl⟩
        · have hs' : 0 ≤ size := Int.not_lt.mp hs
          refine Or.inr ?_
          cases alignV with
          | Int align =>
            refine Or.inr ?_
            cases ha : alignFromBytesInt align with
            | none =>
              rw [allocate_align_not_pow2_ub m size sTy align aTy retTy hs' ha] at h; cases h
              exact Or.inl ⟨size, sTy, align, aTy, rfl, hs', ha, rfl⟩
            | some al =>
              refine Or.inr ?_
              by_cases hp : ∃ p, retTy = .Ptr p
              · obtain ⟨p, rfl⟩ := hp
                refine Or.inr ?_
                by_cases hk : PtrType.meta_kind p = .None
                · rw [allocate_eq_memory m size sTy align aTy p al hs' ha hk] at h
                  rcases interp_bind_eq_error h with hal | ⟨_, _, hc⟩
                  · exact Or.inr ⟨size, sTy, align, aTy, al, p, rfl, hs', ha, rfl, hk, hal⟩
                  · cases hc
                · rw [allocate_unsized_pointee_ub m size sTy align aTy p al hs' ha hk] at h
                  cases h
                  exact Or.inl ⟨size, sTy, align, aTy, al, p, rfl, hs', ha, rfl, hk, rfl⟩
              · have hp' : ∀ p, retTy ≠ .Ptr p := fun p hc => hp ⟨p, hc⟩
                rw [allocate_ret_not_ptr_ub m size sTy align aTy retTy al hs' ha hp'] at h
                cases h
                exact Or.inl ⟨size, sTy, align, aTy, al, rfl, hs', ha, hp', rfl⟩
          | _ =>
            rw [allocate_align_not_int_ub m size sTy _ aTy retTy hs' (fun _ hc => by cases hc)] at h
            cases h
            exact Or.inl ⟨size, sTy, _, aTy, rfl, hs', (fun _ hc => by cases hc), rfl⟩
      | _ =>
        rw [allocate_size_not_int_ub m _ sTy alignV aTy retTy (fun _ hc => by cases hc)] at h
        cases h
        exact Or.inl ⟨_, sTy, alignV, aTy, rfl, (fun _ hc => by cases hc), rfl⟩
    · dsimp only [evalIntrinsicM, ub] at h; cases h
      exact Or.inl ⟨by simp only [List.length_cons]; omega, rfl⟩
  · rintro (⟨hlen, rfl⟩ | ⟨sizeV, sTy, alignV, aTy, rfl, hni, rfl⟩ |
      ⟨size, sTy, alignV, aTy, rfl, hs, rfl⟩ | ⟨size, sTy, alignV, aTy, rfl, hs, hni, rfl⟩ |
      ⟨size, sTy, align, aTy, rfl, hs, ha, rfl⟩ | ⟨size, sTy, align, aTy, al, rfl, hs, ha, hp, rfl⟩ |
      ⟨size, sTy, align, aTy, al, p, rfl, hs, ha, rfl, hk, rfl⟩ |
      ⟨size, sTy, align, aTy, al, p, rfl, hs, ha, rfl, hk, hal⟩)
    · exact allocate_arity_ub m args retTy hlen
    · exact allocate_size_not_int_ub m sizeV sTy alignV aTy retTy hni
    · exact allocate_negative_size_ub m size sTy alignV aTy retTy hs
    · exact allocate_align_not_int_ub m size sTy alignV aTy retTy hs hni
    · exact allocate_align_not_pow2_ub m size sTy align aTy retTy hs ha
    · exact allocate_ret_not_ptr_ub m size sTy align aTy retTy al hs ha hp
    · exact allocate_unsized_pointee_ub m size sTy align aTy p al hs ha hk
    · rw [allocate_eq_memory m size sTy align aTy p al hs ha hk, hal]
      rfl

/-! ### `Deallocate` -/

/-- `Deallocate` on a thin pointer and two integers, after the arity, pointer,
and integer checks: size, alignment, return type, and then
`ConcurrentMemory::deallocate` with `AllocationKind::Heap`. -/
theorem deallocate_eq (m : Machine M) (ptr : ThinPointer (Memory.Provenance M)) (pTy : «Type»)
    (size : Int) (sTy : «Type») (align : Int) (aTy retTy : «Type») :
    evalIntrinsicM m .Deallocate
        [(.Ptr ⟨ptr, none⟩, pTy), (.Int size, sTy), (.Int align, aTy)] retTy =
      match sizeFromBytes size with
      | some size =>
        match alignFromBytesInt align with
        | some align =>
          match retTy with
          | .Tuple [] ⟨⟨0⟩, ⟨1⟩, none⟩ none => do
            let cm ← ConcurrentMemory.deallocate m.mem ptr .Heap size align
            pure (unitValueM, { m with mem := cm })
          | _ => ub "invalid return type for `Deallocate` intrinsic"
        | none => ub "invalid alignment for `Deallocate` intrinsic: not a power of 2"
      | none => ub "invalid size for `Deallocate` intrinsic: negative size" := rfl

/-- `Deallocate` with the wrong number of arguments is UB. -/
theorem deallocate_arity_ub (m : Machine M) (args : List (Value M × «Type»)) (retTy : «Type»)
    (h : args.length ≠ 3) :
    evalIntrinsicM m .Deallocate args retTy =
      .error (.ub "invalid number of arguments for `Deallocate` intrinsic") := by
  rcases args with _ | ⟨⟨_, _⟩, _ | ⟨⟨_, _⟩, _ | ⟨⟨_, _⟩, _ | ⟨_, _⟩⟩⟩⟩
  · rfl
  · rfl
  · rfl
  · exact absurd rfl h
  · rfl

/-- `Deallocate` whose first argument is not a thin pointer is UB. In
particular a wide pointer (slice or trait object) is rejected, whatever its
address. -/
theorem deallocate_not_thin_ptr_ub (m : Machine M) (ptrV : Value M) (pTy : «Type»)
    (sizeV : Value M) (sTy : «Type») (alignV : Value M) (aTy retTy : «Type»)
    (h : ∀ p, ptrV ≠ .Ptr ⟨p, none⟩) :
    evalIntrinsicM m .Deallocate [(ptrV, pTy), (sizeV, sTy), (alignV, aTy)] retTy =
      .error (.ub "invalid first argument to `Deallocate` intrinsic: not a thin pointer") := by
  rcases ptrV with _ | _ | ⟨ptr, _ | _⟩ | _ | _ | _
  · rfl
  · rfl
  · exact absurd rfl (h ptr)
  · rfl
  · rfl
  · rfl
  · rfl

/-- `Deallocate` of a wide pointer is UB: `Deallocate` takes the thin pointer
that `Allocate` returned. -/
theorem deallocate_wide_ptr_ub (m : Machine M) (ptr : ThinPointer (Memory.Provenance M))
    (ptrMeta : PointerMeta (Memory.Provenance M)) (pTy : «Type») (sizeV : Value M) (sTy : «Type»)
    (alignV : Value M) (aTy retTy : «Type») :
    evalIntrinsicM m .Deallocate [(.Ptr ⟨ptr, some ptrMeta⟩, pTy), (sizeV, sTy), (alignV, aTy)]
        retTy =
      .error (.ub "invalid first argument to `Deallocate` intrinsic: not a thin pointer") :=
  deallocate_not_thin_ptr_ub m _ pTy sizeV sTy alignV aTy retTy
    (fun _ hc => by cases (Pointer.mk.inj (Value.Ptr.inj hc)).2)

/-- `Deallocate` whose second argument is not an integer is UB. -/
theorem deallocate_size_not_int_ub (m : Machine M) (ptr : ThinPointer (Memory.Provenance M))
    (pTy : «Type») (sizeV : Value M) (sTy : «Type») (alignV : Value M) (aTy retTy : «Type»)
    (h : ∀ i, sizeV ≠ .Int i) :
    evalIntrinsicM m .Deallocate [(.Ptr ⟨ptr, none⟩, pTy), (sizeV, sTy), (alignV, aTy)] retTy =
      .error (.ub "invalid second argument to `Deallocate` intrinsic: not an integer") := by
  cases sizeV with
  | Int i => exact absurd rfl (h i)
  | _ => rfl

/-- `Deallocate` with a negative size is UB. -/
theorem deallocate_negative_size_ub (m : Machine M) (ptr : ThinPointer (Memory.Provenance M))
    (pTy : «Type») (size : Int) (sTy : «Type») (alignV : Value M) (aTy retTy : «Type»)
    (h : size < 0) :
    evalIntrinsicM m .Deallocate [(.Ptr ⟨ptr, none⟩, pTy), (.Int size, sTy), (alignV, aTy)]
        retTy =
      .error (.ub "invalid size for `Deallocate` intrinsic: negative size") := by
  simp only [evalIntrinsicM, sizeFromBytes_neg h]
  rfl

/-- `Deallocate` whose third argument is not an integer is UB. -/
theorem deallocate_align_not_int_ub (m : Machine M) (ptr : ThinPointer (Memory.Provenance M))
    (pTy : «Type») (size : Int) (sTy : «Type») (alignV : Value M) (aTy retTy : «Type»)
    (hs : 0 ≤ size) (h : ∀ i, alignV ≠ .Int i) :
    evalIntrinsicM m .Deallocate [(.Ptr ⟨ptr, none⟩, pTy), (.Int size, sTy), (alignV, aTy)]
        retTy =
      .error (.ub "invalid third argument to `Deallocate` intrinsic: not an integer") := by
  simp only [evalIntrinsicM, sizeFromBytes_nonneg hs]
  cases alignV with
  | Int i => exact absurd rfl (h i)
  | _ => rfl

/-- `Deallocate` with an alignment that is not a power of two is UB. -/
theorem deallocate_align_not_pow2_ub (m : Machine M) (ptr : ThinPointer (Memory.Provenance M))
    (pTy : «Type») (size : Int) (sTy : «Type») (align : Int) (aTy retTy : «Type»)
    (hs : 0 ≤ size) (h : alignFromBytesInt align = none) :
    evalIntrinsicM m .Deallocate [(.Ptr ⟨ptr, none⟩, pTy), (.Int size, sTy), (.Int align, aTy)]
        retTy =
      .error (.ub "invalid alignment for `Deallocate` intrinsic: not a power of 2") := by
  rw [deallocate_eq, sizeFromBytes_nonneg hs, h]
  rfl

/-- `Deallocate` with `align = 0` is UB across every memory model `M`. -/
theorem deallocate_align_zero_ub (m : Machine M) (ptr : ThinPointer (Memory.Provenance M))
    (pTy : «Type») (size : Int) (sTy aTy retTy : «Type») (hs : 0 ≤ size) :
    evalIntrinsicM m .Deallocate [(.Ptr ⟨ptr, none⟩, pTy), (.Int size, sTy), (.Int 0, aTy)]
        retTy =
      .error (.ub "invalid alignment for `Deallocate` intrinsic: not a power of 2") :=
  deallocate_align_not_pow2_ub m ptr pTy size sTy 0 aTy retTy hs alignFromBytesInt_zero

/-- `Deallocate` at a return type other than `()` is UB. -/
theorem deallocate_ret_not_unit_ub (m : Machine M) (ptr : ThinPointer (Memory.Provenance M))
    (pTy : «Type») (size : Int) (sTy : «Type») (align : Int) (aTy retTy : «Type») (al : Align)
    (hs : 0 ≤ size) (ha : alignFromBytesInt align = some al) (h : retTy ≠ unitType) :
    evalIntrinsicM m .Deallocate [(.Ptr ⟨ptr, none⟩, pTy), (.Int size, sTy), (.Int align, aTy)]
        retTy =
      .error (.ub "invalid return type for `Deallocate` intrinsic") := by
  rw [deallocate_eq, sizeFromBytes_nonneg hs, ha]
  dsimp only
  split
  · exact absurd rfl h
  · rfl

/-- `Deallocate` past its checks is `ConcurrentMemory::deallocate` with
`AllocationKind::Heap`, returning `()`. -/
theorem deallocate_eq_memory (m : Machine M) (ptr : ThinPointer (Memory.Provenance M))
    (pTy : «Type») (size : Int) (sTy : «Type») (align : Int) (aTy : «Type») (al : Align)
    (hs : 0 ≤ size) (ha : alignFromBytesInt align = some al) :
    evalIntrinsicM m .Deallocate [(.Ptr ⟨ptr, none⟩, pTy), (.Int size, sTy), (.Int align, aTy)]
        unitType =
      (do
        let cm ← ConcurrentMemory.deallocate m.mem ptr .Heap ⟨size.toNat⟩ al
        pure (unitValueM, { m with mem := cm })) := by
  rw [deallocate_eq, sizeFromBytes_nonneg hs, ha]
  rfl

/-- Complete characterization of a successful `Deallocate` in every memory
model. -/
theorem deallocate_ok_iff {m m' : Machine M} {args : List (Value M × «Type»)} {retTy : «Type»}
    {val : Value M} :
    evalIntrinsicM m .Deallocate args retTy = .ok (val, m') ↔
      ∃ ptr pTy size sTy align aTy al cm,
        args = [(.Ptr ⟨ptr, none⟩, pTy), (.Int size, sTy), (.Int align, aTy)] ∧ 0 ≤ size ∧
        alignFromBytesInt align = some al ∧ retTy = unitType ∧
        ConcurrentMemory.deallocate m.mem ptr .Heap ⟨size.toNat⟩ al = .ok cm ∧
        val = unitValueM ∧ m' = { m with mem := cm } := by
  constructor
  · intro h
    rcases args with _ | ⟨⟨ptrV, pTy⟩, _ | ⟨⟨sizeV, sTy⟩, _ | ⟨⟨alignV, aTy⟩, _ | ⟨_, _⟩⟩⟩⟩
    · dsimp only [evalIntrinsicM, ub] at h; cases h
    · dsimp only [evalIntrinsicM, ub] at h; cases h
    · dsimp only [evalIntrinsicM, ub] at h; cases h
    · by_cases hthin : ∃ p, ptrV = .Ptr ⟨p, none⟩
      · obtain ⟨ptr, rfl⟩ := hthin
        cases sizeV with
        | Int size =>
          by_cases hs : size < 0
          · rw [deallocate_negative_size_ub m ptr pTy size sTy alignV aTy retTy hs] at h; cases h
          · have hs' : 0 ≤ size := Int.not_lt.mp hs
            cases alignV with
            | Int align =>
              cases ha : alignFromBytesInt align with
              | none =>
                rw [deallocate_align_not_pow2_ub m ptr pTy size sTy align aTy retTy hs' ha] at h
                cases h
              | some al =>
                by_cases hret : retTy = unitType
                · subst hret
                  rw [deallocate_eq_memory m ptr pTy size sTy align aTy al hs' ha] at h
                  obtain ⟨cm, hd, h⟩ := interp_bind_eq_ok h
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok h)
                  exact ⟨ptr, pTy, size, sTy, align, aTy, al, cm, rfl, hs', ha, rfl, hd, rfl, rfl⟩
                · rw [deallocate_ret_not_unit_ub m ptr pTy size sTy align aTy retTy al hs' ha
                    hret] at h
                  cases h
            | _ =>
              rw [deallocate_align_not_int_ub m ptr pTy size sTy _ aTy retTy hs'
                (fun _ hc => by cases hc)] at h
              cases h
        | _ =>
          rw [deallocate_size_not_int_ub m ptr pTy _ sTy alignV aTy retTy
            (fun _ hc => by cases hc)] at h
          cases h
      · rw [deallocate_not_thin_ptr_ub m ptrV pTy sizeV sTy alignV aTy retTy
          (fun p hc => hthin ⟨p, hc⟩)] at h
        cases h
    · dsimp only [evalIntrinsicM, ub] at h; cases h
  · rintro ⟨ptr, pTy, size, sTy, align, aTy, al, cm, rfl, hs, ha, rfl, hd, rfl, rfl⟩
    rw [deallocate_eq_memory m ptr pTy size sTy align aTy al hs ha, hd]
    rfl

/-- Complete characterization of every stopping outcome of `Deallocate`, in
exact upstream check order, in every memory model. -/
theorem deallocate_error_iff {m : Machine M} {args : List (Value M × «Type»)} {retTy : «Type»}
    {e : Stop} :
    evalIntrinsicM m .Deallocate args retTy = .error e ↔
      (args.length ≠ 3 ∧ e = .ub "invalid number of arguments for `Deallocate` intrinsic") ∨
      (∃ ptrV pTy sizeV sTy alignV aTy, args = [(ptrV, pTy), (sizeV, sTy), (alignV, aTy)] ∧
        (∀ p, ptrV ≠ .Ptr ⟨p, none⟩) ∧
        e = .ub "invalid first argument to `Deallocate` intrinsic: not a thin pointer") ∨
      (∃ ptr pTy sizeV sTy alignV aTy,
        args = [(.Ptr ⟨ptr, none⟩, pTy), (sizeV, sTy), (alignV, aTy)] ∧ (∀ i, sizeV ≠ .Int i) ∧
        e = .ub "invalid second argument to `Deallocate` intrinsic: not an integer") ∨
      (∃ ptr pTy size sTy alignV aTy,
        args = [(.Ptr ⟨ptr, none⟩, pTy), (.Int size, sTy), (alignV, aTy)] ∧ size < 0 ∧
        e = .ub "invalid size for `Deallocate` intrinsic: negative size") ∨
      (∃ ptr pTy size sTy alignV aTy,
        args = [(.Ptr ⟨ptr, none⟩, pTy), (.Int size, sTy), (alignV, aTy)] ∧ 0 ≤ size ∧
        (∀ i, alignV ≠ .Int i) ∧
        e = .ub "invalid third argument to `Deallocate` intrinsic: not an integer") ∨
      (∃ ptr pTy size sTy align aTy,
        args = [(.Ptr ⟨ptr, none⟩, pTy), (.Int size, sTy), (.Int align, aTy)] ∧ 0 ≤ size ∧
        alignFromBytesInt align = none ∧
        e = .ub "invalid alignment for `Deallocate` intrinsic: not a power of 2") ∨
      (∃ ptr pTy size sTy align aTy al,
        args = [(.Ptr ⟨ptr, none⟩, pTy), (.Int size, sTy), (.Int align, aTy)] ∧ 0 ≤ size ∧
        alignFromBytesInt align = some al ∧ retTy ≠ unitType ∧
        e = .ub "invalid return type for `Deallocate` intrinsic") ∨
      (∃ ptr pTy size sTy align aTy al,
        args = [(.Ptr ⟨ptr, none⟩, pTy), (.Int size, sTy), (.Int align, aTy)] ∧ 0 ≤ size ∧
        alignFromBytesInt align = some al ∧ retTy = unitType ∧
        ConcurrentMemory.deallocate m.mem ptr .Heap ⟨size.toNat⟩ al = .error e) := by
  constructor
  · intro h
    rcases args with _ | ⟨⟨ptrV, pTy⟩, _ | ⟨⟨sizeV, sTy⟩, _ | ⟨⟨alignV, aTy⟩, _ | ⟨_, _⟩⟩⟩⟩
    · dsimp only [evalIntrinsicM, ub] at h; cases h; exact Or.inl ⟨by show 0 ≠ 3; decide, rfl⟩
    · dsimp only [evalIntrinsicM, ub] at h; cases h; exact Or.inl ⟨by show 1 ≠ 3; decide, rfl⟩
    · dsimp only [evalIntrinsicM, ub] at h; cases h; exact Or.inl ⟨by show 2 ≠ 3; decide, rfl⟩
    · refine Or.inr ?_
      by_cases hthin : ∃ p, ptrV = .Ptr ⟨p, none⟩
      · obtain ⟨ptr, rfl⟩ := hthin
        refine Or.inr ?_
        cases sizeV with
        | Int size =>
          refine Or.inr ?_
          by_cases hs : size < 0
          · rw [deallocate_negative_size_ub m ptr pTy size sTy alignV aTy retTy hs] at h; cases h
            exact Or.inl ⟨ptr, pTy, size, sTy, alignV, aTy, rfl, hs, rfl⟩
          · have hs' : 0 ≤ size := Int.not_lt.mp hs
            refine Or.inr ?_
            cases alignV with
            | Int align =>
              refine Or.inr ?_
              cases ha : alignFromBytesInt align with
              | none =>
                rw [deallocate_align_not_pow2_ub m ptr pTy size sTy align aTy retTy hs' ha] at h
                cases h
                exact Or.inl ⟨ptr, pTy, size, sTy, align, aTy, rfl, hs', ha, rfl⟩
              | some al =>
                refine Or.inr ?_
                by_cases hret : retTy = unitType
                · subst hret
                  rw [deallocate_eq_memory m ptr pTy size sTy align aTy al hs' ha] at h
                  rcases interp_bind_eq_error h with hd | ⟨_, _, hc⟩
                  · exact Or.inr ⟨ptr, pTy, size, sTy, align, aTy, al, rfl, hs', ha, rfl, hd⟩
                  · cases hc
                · rw [deallocate_ret_not_unit_ub m ptr pTy size sTy align aTy retTy al hs' ha
                    hret] at h
                  cases h
                  exact Or.inl ⟨ptr, pTy, size, sTy, align, aTy, al, rfl, hs', ha, hret, rfl⟩
            | _ =>
              rw [deallocate_align_not_int_ub m ptr pTy size sTy _ aTy retTy hs'
                (fun _ hc => by cases hc)] at h
              cases h
              exact Or.inl ⟨ptr, pTy, size, sTy, _, aTy, rfl, hs', (fun _ hc => by cases hc), rfl⟩
        | _ =>
          rw [deallocate_size_not_int_ub m ptr pTy _ sTy alignV aTy retTy
            (fun _ hc => by cases hc)] at h
          cases h
          exact Or.inl ⟨ptr, pTy, _, sTy, alignV, aTy, rfl, (fun _ hc => by cases hc), rfl⟩
      · have hthin' : ∀ p, ptrV ≠ .Ptr ⟨p, none⟩ := fun p hc => hthin ⟨p, hc⟩
        rw [deallocate_not_thin_ptr_ub m ptrV pTy sizeV sTy alignV aTy retTy hthin'] at h
        cases h
        exact Or.inl ⟨ptrV, pTy, sizeV, sTy, alignV, aTy, rfl, hthin', rfl⟩
    · dsimp only [evalIntrinsicM, ub] at h; cases h
      exact Or.inl ⟨by simp only [List.length_cons]; omega, rfl⟩
  · rintro (⟨hlen, rfl⟩ | ⟨ptrV, pTy, sizeV, sTy, alignV, aTy, rfl, hthin, rfl⟩ |
      ⟨ptr, pTy, sizeV, sTy, alignV, aTy, rfl, hni, rfl⟩ |
      ⟨ptr, pTy, size, sTy, alignV, aTy, rfl, hs, rfl⟩ |
      ⟨ptr, pTy, size, sTy, alignV, aTy, rfl, hs, hni, rfl⟩ |
      ⟨ptr, pTy, size, sTy, align, aTy, rfl, hs, ha, rfl⟩ |
      ⟨ptr, pTy, size, sTy, align, aTy, al, rfl, hs, ha, hret, rfl⟩ |
      ⟨ptr, pTy, size, sTy, align, aTy, al, rfl, hs, ha, rfl, hd⟩)
    · exact deallocate_arity_ub m args retTy hlen
    · exact deallocate_not_thin_ptr_ub m ptrV pTy sizeV sTy alignV aTy retTy hthin
    · exact deallocate_size_not_int_ub m ptr pTy sizeV sTy alignV aTy retTy hni
    · exact deallocate_negative_size_ub m ptr pTy size sTy alignV aTy retTy hs
    · exact deallocate_align_not_int_ub m ptr pTy size sTy alignV aTy retTy hs hni
    · exact deallocate_align_not_pow2_ub m ptr pTy size sTy align aTy retTy hs ha
    · exact deallocate_ret_not_unit_ub m ptr pTy size sTy align aTy retTy al hs ha hret
    · rw [deallocate_eq_memory m ptr pTy size sTy align aTy al hs ha, hd]
      rfl

end Guards

/-! ### `MachTB.wfLive` preservation

`TreeBorrowsMemory::allocate` adds a live allocation with a fresh, well-formed
root node; `TreeBorrowsMemory::deallocate` marks one allocation dead. Both
keep every *live* allocation's borrow tree well-formed. -/

/-- `ConcurrentMemory::allocate` at `M = TreeBorrowsMemory<x86_64>` is
`TreeBorrowsMemory::allocate` on the wrapped memory. -/
theorem cm_allocate_tb_eq (cm : ConcurrentMemory TBM) (kind : AllocationKind) (size : Size)
    (align : Align) :
    ConcurrentMemory.allocate cm kind size align =
      (do
        let (ptr, mem) ← TreeBorrowsMemory.allocate cm.memory kind size align
        pure (ptr, { cm with memory := mem })) := rfl

/-- `ConcurrentMemory::deallocate` at `M = TreeBorrowsMemory<x86_64>` is
`TreeBorrowsMemory::deallocate` on the wrapped memory. -/
theorem cm_deallocate_tb_eq (cm : ConcurrentMemory TBM)
    (ptr : ThinPointer TreeBorrowsProvenance) (kind : AllocationKind) (size : Size)
    (align : Align) :
    ConcurrentMemory.deallocate cm ptr kind size align =
      (do
        let mem ← TreeBorrowsMemory.deallocate cm.memory ptr kind size align
        pure { cm with memory := mem }) := rfl

/-- A successful `Allocate` preserves the Tree Borrows invariant
`MachTB.wfLive` on `Machine<TreeBorrowsMemory<x86_64>>`. -/
theorem evalIntrinsicM_allocate_tb_wfLive {m m' : MachTB} {args : List (Value TBM × «Type»)}
    {retTy : «Type»} {val : Value TBM}
    (hwf : MiniRustSpec.Correspondence.MachTB.wfLive m)
    (h : evalIntrinsicM m .Allocate args retTy = .ok (val, m')) :
    MiniRustSpec.Correspondence.MachTB.wfLive m' := by
  obtain ⟨size, sTy, align, aTy, al, p, ptr, cm, rfl, hs, ha, rfl, hk, hal, rfl, rfl⟩ :=
    allocate_ok_iff.mp h
  rw [cm_allocate_tb_eq] at hal
  obtain ⟨⟨ptr', mem⟩, halloc, hal⟩ := interp_bind_eq_ok hal
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok hal)
  exact MiniRustSpec.Correspondence.TreeBorrowsMemory.allocate_wfLive hwf halloc

/-- A successful `Deallocate` preserves the Tree Borrows invariant
`MachTB.wfLive` on `Machine<TreeBorrowsMemory<x86_64>>`. -/
theorem evalIntrinsicM_deallocate_tb_wfLive {m m' : MachTB} {args : List (Value TBM × «Type»)}
    {retTy : «Type»} {val : Value TBM}
    (hwf : MiniRustSpec.Correspondence.MachTB.wfLive m)
    (h : evalIntrinsicM m .Deallocate args retTy = .ok (val, m')) :
    MiniRustSpec.Correspondence.MachTB.wfLive m' := by
  obtain ⟨ptr, pTy, size, sTy, align, aTy, al, cm, rfl, hs, ha, rfl, hd, rfl, rfl⟩ :=
    deallocate_ok_iff.mp h
  rw [cm_deallocate_tb_eq] at hd
  obtain ⟨mem, hdealloc, hd⟩ := interp_bind_eq_ok hd
  obtain rfl := interp_pure_eq_ok hd
  exact MiniRustSpec.Correspondence.TreeBorrowsMemory.deallocate_wfLive hwf hdealloc

/-- Both heap intrinsics preserve `MachTB.wfLive`. -/
theorem evalIntrinsicM_heap_tb_wfLive {m m' : MachTB} {op : IntrinsicOp}
    {args : List (Value TBM × «Type»)} {retTy : «Type»} {val : Value TBM}
    (hop : isHeapOp op = true) (hwf : MiniRustSpec.Correspondence.MachTB.wfLive m)
    (h : evalIntrinsicM m op args retTy = .ok (val, m')) :
    MiniRustSpec.Correspondence.MachTB.wfLive m' := by
  cases op with
  | Allocate => exact evalIntrinsicM_allocate_tb_wfLive hwf h
  | Deallocate => exact evalIntrinsicM_deallocate_tb_wfLive hwf h
  | _ => exact Bool.noConfusion hop

/-! ## §3. Memory-model laws: `allocate`, `deallocate`, protectors, and `leak_check` -/

/-- A successful `list[i]` is the element at a non-negative, in-range index. -/
theorem listIndex_eq_ok_iff {T : Type} {xs : List T} {i : Int} {what : String} {x : T} :
    listIndex xs i what = .ok x ↔ 0 ≤ i ∧ xs[i.toNat]? = some x := by
  unfold listIndex
  by_cases hi : 0 ≤ i
  · simp only [hi, ↓reduceIte, true_and]
    cases xs[i.toNat]? with
    | none =>
      constructor
      · intro h; cases h
      · intro h; cases h
    | some y =>
      constructor
      · intro h; exact congrArg some (interp_pure_eq_ok h)
      · intro h; cases h; rfl
  · simp only [hi, ↓reduceIte, false_and]
    constructor
    · intro h; cases h
    · intro h; exact h.elim

/-- `list[i]` stops only with a specification panic (an invalid index). -/
theorem listIndex_error_specPanic {T : Type} {xs : List T} {i : Int} {what : String} {e : Stop}
    (h : listIndex xs i what = .error e) : ∃ msg, e = .specPanic msg := by
  unfold listIndex at h
  split at h
  · split at h
    · cases h
    · cases h; exact ⟨_, rfl⟩
  · cases h; exact ⟨_, rfl⟩

/-- `List::set` at an index that `list[i]` accepts succeeds. -/
theorem listSet_of_getElem? {T : Type} {xs : List T} {i : Int} {a x : T} {what : String}
    (hi : 0 ≤ i) (ha : xs[i.toNat]? = some a) :
    listSet xs i x what = .ok (xs.set i.toNat x) := by
  have hlt : i.toNat < xs.length := (List.getElem?_eq_some_iff.mp ha).1
  unfold listSet
  rw [ite_eq_left ⟨hi, hlt⟩]
  rfl

section BasicMemoryLaws

variable {ProvExtra AllocExtra : Type}

/-! ### `BasicMemory::allocate` -/

/-- `BasicMemory::allocate` of more than `isize::MAX` bytes is UB, before any
address is picked and before any byte is materialized. -/
theorem basicMemory_allocate_too_large_ub (mem : BasicMemory x86_64 ProvExtra AllocExtra)
    (kind : AllocationKind) (size : Size) (align : Align) (provExtra : ProvExtra)
    (allocExtra : AllocExtra) (h : x86_64.valid_size size = false) :
    BasicMemory.allocate mem kind size align provExtra allocExtra =
      .error (.ub "asking for a too large allocation") := by
  unfold BasicMemory.allocate
  simp only [h, Bool.not_false, ↓reduceIte]
  rfl

/-- Complete characterization of a successful `BasicMemory::allocate`: the
size is valid, the first-fit resolution found an address, the new allocation
is live, uninitialized, of the requested kind, size, and alignment, and the
returned pointer carries the new `AllocId`. -/
theorem basicMemory_allocate_ok_iff (mem mem' : BasicMemory x86_64 ProvExtra AllocExtra)
    (kind : AllocationKind) (size : Size) (align : Align) (provExtra : ProvExtra)
    (allocExtra : AllocExtra) (ptr : ThinPointer (Provenance ProvExtra)) :
    BasicMemory.allocate mem kind size align provExtra allocExtra = .ok (ptr, mem') ↔
      x86_64.valid_size size = true ∧
      ∃ addr, BasicMemory.pickAddr mem size align = some addr ∧
        ptr = { addr := addr, provenance := some (⟨mem.allocations.length⟩, provExtra) } ∧
        mem' = { mem with allocations := mem.allocations ++
          [{ addr := addr, align := align, kind := kind, live := true,
             data := List.replicate size.bytes .Uninit, extra := allocExtra }] } := by
  unfold BasicMemory.allocate
  cases hv : x86_64.valid_size size with
  | false =>
    simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true, false_and, iff_false]
    intro h; cases h
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, true_and]
    cases hpick : BasicMemory.pickAddr mem size align with
    | none =>
      constructor
      · intro h; cases h
      · rintro ⟨addr, hc, _⟩; cases hc
    | some addr =>
      constructor
      · intro h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok h)
        exact ⟨addr, rfl, rfl, rfl⟩
      · rintro ⟨addr', hc, rfl, rfl⟩
        cases hc
        rfl

/-- Complete characterization of every stopping outcome of
`BasicMemory::allocate`: an invalid size is UB; an exhausted first-fit
resolution is reported as `unsupported` (upstream's daemonic `pick` has "no
behavior" there). -/
theorem basicMemory_allocate_error_iff (mem : BasicMemory x86_64 ProvExtra AllocExtra)
    (kind : AllocationKind) (size : Size) (align : Align) (provExtra : ProvExtra)
    (allocExtra : AllocExtra) (e : Stop) :
    BasicMemory.allocate mem kind size align provExtra allocExtra = .error e ↔
      (x86_64.valid_size size = false ∧ e = .ub "asking for a too large allocation") ∨
      (x86_64.valid_size size = true ∧ BasicMemory.pickAddr mem size align = none ∧
        e = .unsupported "allocate: no candidate address of the first-fit resolution is free") := by
  unfold BasicMemory.allocate
  cases hv : x86_64.valid_size size with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    constructor
    · intro h; cases h; exact Or.inl ⟨by trivial, rfl⟩
    · rintro (⟨_, rfl⟩ | ⟨hc, _⟩)
      · rfl
      · cases hc
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases hpick : BasicMemory.pickAddr mem size align with
    | none =>
      constructor
      · intro h; cases h; exact Or.inr ⟨by trivial, by trivial, rfl⟩
      · rintro (⟨hc, _⟩ | ⟨_, _, rfl⟩)
        · cases hc
        · rfl
    | some addr =>
      constructor
      · intro h; cases h
      · rintro (⟨hc, _⟩ | ⟨_, hc, _⟩) <;> cases hc

/-- An address found by the first-fit search satisfies the `pick` predicate of
`BasicMemory::allocate`. -/
theorem basicMemory_firstFitAddr_ok (mem : BasicMemory x86_64 ProvExtra AllocExtra) (size : Size)
    (align : Align) :
    ∀ (fuel k : Nat) (addr : Int), BasicMemory.firstFitAddr mem size align fuel k = some addr →
      BasicMemory.allocAddrOk mem size align addr = true
  | 0, _, _, h => by cases h
  | fuel + 1, k, addr, h => by
    unfold BasicMemory.firstFitAddr at h
    split at h
    · rename_i hok
      cases h
      exact hok
    · exact basicMemory_firstFitAddr_ok mem size align fuel (k + 1) addr h

/-- The pointer of a successful `BasicMemory::allocate` is strictly positive
and aligned as requested. -/
theorem basicMemory_allocate_aligned {mem mem' : BasicMemory x86_64 ProvExtra AllocExtra}
    {kind : AllocationKind} {size : Size} {align : Align} {provExtra : ProvExtra}
    {allocExtra : AllocExtra} {ptr : ThinPointer (Provenance ProvExtra)}
    (h : BasicMemory.allocate mem kind size align provExtra allocExtra = .ok (ptr, mem')) :
    0 < ptr.addr ∧ Align.is_aligned align ptr.addr = true := by
  obtain ⟨_, addr, hpick, rfl, rfl⟩ :=
    (basicMemory_allocate_ok_iff mem mem' kind size align provExtra allocExtra ptr).mp h
  have hok := basicMemory_firstFitAddr_ok mem size align _ _ addr hpick
  unfold BasicMemory.allocAddrOk at hok
  split at hok
  · cases hok
  · rename_i hpos
    split at hok
    · cases hok
    · rename_i hal
      refine ⟨Int.not_le.mp hpos, ?_⟩
      cases hb : Align.is_aligned align addr with
      | true => rfl
      | false => rw [hb] at hal; exact absurd rfl hal

/-! ### `BasicMemory::deallocate` -/

/-- The name `{:?}` prints for an `AllocationKind`. -/
def allocKindName : AllocationKind → String
  | .Stack => "Stack" | .Heap => "Heap" | .Global => "Global"
  | .Function => "Function" | .VTable => "VTable"

/-- The UB message of `BasicMemory::deallocate` for a kind mismatch:
> "deallocating {:?} memory with {:?} deallocation operation" -/
def deallocKindMismatchMsg (actual requested : AllocationKind) : String :=
  s!"deallocating {allocKindName actual} memory with {allocKindName requested} deallocation operation"

/-- `BasicMemory::deallocate` through a pointer without provenance is UB. -/
theorem basicMemory_deallocate_no_provenance_ub (mem : BasicMemory x86_64 ProvExtra AllocExtra)
    (ptr : ThinPointer (Provenance ProvExtra)) (kind : AllocationKind) (size : Size)
    (align : Align) (handleExtra : AllocExtra → ProvExtra → Interp AllocExtra)
    (h : ptr.provenance = none) :
    BasicMemory.deallocate mem ptr kind size align handleExtra =
      .error (.ub "deallocating invalid pointer") := by
  unfold BasicMemory.deallocate
  rw [h]
  rfl

/-- `BasicMemory::deallocate` through a pointer with provenance `(id, extra)`
on the allocation `a` that `id` names: the checks, in upstream order. -/
theorem basicMemory_deallocate_steps (mem : BasicMemory x86_64 ProvExtra AllocExtra)
    (ptr : ThinPointer (Provenance ProvExtra)) (kind : AllocationKind) (size : Size)
    (align : Align) (handleExtra : AllocExtra → ProvExtra → Interp AllocExtra)
    (id : AllocId) (provExtra : ProvExtra) (a : Allocation ProvExtra AllocExtra)
    (hp : ptr.provenance = some (id, provExtra))
    (ha : listIndex mem.allocations id._0 "self.allocations[id.0]" = .ok a) :
    BasicMemory.deallocate mem ptr kind size align handleExtra =
      (if !a.live then ub "double-free"
      else if ptr.addr ≠ a.addr then
        ub "deallocating with pointer not to the beginning of its allocation"
      else if kind ≠ a.kind then ub (deallocKindMismatchMsg a.kind kind)
      else if size ≠ Allocation.size a then ub "deallocating with incorrect size information"
      else if align ≠ a.align then ub "deallocating with incorrect alignment information"
      else do
        let extra' ← handleExtra a.extra provExtra
        let allocations ←
          listSet mem.allocations id._0 { a with live := false, extra := extra' } "set"
        pure { mem with allocations := allocations }) := by
  unfold BasicMemory.deallocate
  rw [hp]
  dsimp only
  rw [ha]
  rfl

/-- `BasicMemory::deallocate` through a pointer whose `AllocId` names no
allocation stops as `self.allocations[id.0]` does (a specification panic:
upstream's "This lookup will definitely work, since AllocId cannot be faked"). -/
theorem basicMemory_deallocate_bad_id (mem : BasicMemory x86_64 ProvExtra AllocExtra)
    (ptr : ThinPointer (Provenance ProvExtra)) (kind : AllocationKind) (size : Size)
    (align : Align) (handleExtra : AllocExtra → ProvExtra → Interp AllocExtra)
    (id : AllocId) (provExtra : ProvExtra) (e : Stop)
    (hp : ptr.provenance = some (id, provExtra))
    (ha : listIndex mem.allocations id._0 "self.allocations[id.0]" = .error e) :
    BasicMemory.deallocate mem ptr kind size align handleExtra = .error e := by
  unfold BasicMemory.deallocate
  rw [hp]
  dsimp only
  rw [ha]
  rfl

/-- Deallocating a dead allocation is UB `"double-free"`, whatever the
pointer's offset and the claimed kind, size, and alignment. -/
theorem basicMemory_deallocate_double_free_ub (mem : BasicMemory x86_64 ProvExtra AllocExtra)
    (ptr : ThinPointer (Provenance ProvExtra)) (kind : AllocationKind) (size : Size)
    (align : Align) (handleExtra : AllocExtra → ProvExtra → Interp AllocExtra)
    (id : AllocId) (provExtra : ProvExtra) (a : Allocation ProvExtra AllocExtra)
    (hp : ptr.provenance = some (id, provExtra))
    (ha : listIndex mem.allocations id._0 "self.allocations[id.0]" = .ok a)
    (hlive : a.live = false) :
    BasicMemory.deallocate mem ptr kind size align handleExtra = .error (.ub "double-free") := by
  rw [basicMemory_deallocate_steps mem ptr kind size align handleExtra id provExtra a hp ha]
  simp only [hlive, Bool.not_false, ↓reduceIte]
  rfl

/-- Deallocating through a pointer that is not to the beginning of its (live)
allocation is UB. -/
theorem basicMemory_deallocate_not_beginning_ub (mem : BasicMemory x86_64 ProvExtra AllocExtra)
    (ptr : ThinPointer (Provenance ProvExtra)) (kind : AllocationKind) (size : Size)
    (align : Align) (handleExtra : AllocExtra → ProvExtra → Interp AllocExtra)
    (id : AllocId) (provExtra : ProvExtra) (a : Allocation ProvExtra AllocExtra)
    (hp : ptr.provenance = some (id, provExtra))
    (ha : listIndex mem.allocations id._0 "self.allocations[id.0]" = .ok a)
    (hlive : a.live = true) (haddr : ptr.addr ≠ a.addr) :
    BasicMemory.deallocate mem ptr kind size align handleExtra =
      .error (.ub "deallocating with pointer not to the beginning of its allocation") := by
  rw [basicMemory_deallocate_steps mem ptr kind size align handleExtra id provExtra a hp ha]
  simp only [hlive, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ne_eq, haddr, not_false_eq_true]
  rfl

/-- Deallocating memory of one `AllocationKind` with the deallocation
operation of another is UB. For `kind = Heap` (the `Deallocate` intrinsic)
this covers `Global`, `Stack`, `Function`, and `VTable` memory. -/
theorem basicMemory_deallocate_kind_mismatch_ub (mem : BasicMemory x86_64 ProvExtra AllocExtra)
    (ptr : ThinPointer (Provenance ProvExtra)) (kind : AllocationKind) (size : Size)
    (align : Align) (handleExtra : AllocExtra → ProvExtra → Interp AllocExtra)
    (id : AllocId) (provExtra : ProvExtra) (a : Allocation ProvExtra AllocExtra)
    (hp : ptr.provenance = some (id, provExtra))
    (ha : listIndex mem.allocations id._0 "self.allocations[id.0]" = .ok a)
    (hlive : a.live = true) (haddr : ptr.addr = a.addr) (hkind : kind ≠ a.kind) :
    BasicMemory.deallocate mem ptr kind size align handleExtra =
      .error (.ub (deallocKindMismatchMsg a.kind kind)) := by
  rw [basicMemory_deallocate_steps mem ptr kind size align handleExtra id provExtra a hp ha]
  simp only [hlive, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ne_eq, haddr, not_true_eq_false,
    hkind, not_false_eq_true]
  rfl

/-- Deallocating with a size other than the allocation's is UB. -/
theorem basicMemory_deallocate_size_mismatch_ub (mem : BasicMemory x86_64 ProvExtra AllocExtra)
    (ptr : ThinPointer (Provenance ProvExtra)) (kind : AllocationKind) (size : Size)
    (align : Align) (handleExtra : AllocExtra → ProvExtra → Interp AllocExtra)
    (id : AllocId) (provExtra : ProvExtra) (a : Allocation ProvExtra AllocExtra)
    (hp : ptr.provenance = some (id, provExtra))
    (ha : listIndex mem.allocations id._0 "self.allocations[id.0]" = .ok a)
    (hlive : a.live = true) (haddr : ptr.addr = a.addr) (hkind : kind = a.kind)
    (hsize : size ≠ Allocation.size a) :
    BasicMemory.deallocate mem ptr kind size align handleExtra =
      .error (.ub "deallocating with incorrect size information") := by
  rw [basicMemory_deallocate_steps mem ptr kind size align handleExtra id provExtra a hp ha]
  simp only [hlive, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ne_eq, haddr, not_true_eq_false,
    hkind, hsize, not_false_eq_true]
  rfl

/-- Deallocating with an alignment other than the allocation's is UB. -/
theorem basicMemory_deallocate_align_mismatch_ub (mem : BasicMemory x86_64 ProvExtra AllocExtra)
    (ptr : ThinPointer (Provenance ProvExtra)) (kind : AllocationKind) (size : Size)
    (align : Align) (handleExtra : AllocExtra → ProvExtra → Interp AllocExtra)
    (id : AllocId) (provExtra : ProvExtra) (a : Allocation ProvExtra AllocExtra)
    (hp : ptr.provenance = some (id, provExtra))
    (ha : listIndex mem.allocations id._0 "self.allocations[id.0]" = .ok a)
    (hlive : a.live = true) (haddr : ptr.addr = a.addr) (hkind : kind = a.kind)
    (hsize : size = Allocation.size a) (halign : align ≠ a.align) :
    BasicMemory.deallocate mem ptr kind size align handleExtra =
      .error (.ub "deallocating with incorrect alignment information") := by
  rw [basicMemory_deallocate_steps mem ptr kind size align handleExtra id provExtra a hp ha]
  simp only [hlive, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ne_eq, haddr, not_true_eq_false,
    hkind, hsize, halign, not_false_eq_true]
  rfl

/-- Past its own checks, `BasicMemory::deallocate` runs the memory model's
`handle_extra` and marks the allocation dead. -/
theorem basicMemory_deallocate_checked (mem : BasicMemory x86_64 ProvExtra AllocExtra)
    (ptr : ThinPointer (Provenance ProvExtra)) (kind : AllocationKind) (size : Size)
    (align : Align) (handleExtra : AllocExtra → ProvExtra → Interp AllocExtra)
    (id : AllocId) (provExtra : ProvExtra) (a : Allocation ProvExtra AllocExtra)
    (hp : ptr.provenance = some (id, provExtra))
    (ha : listIndex mem.allocations id._0 "self.allocations[id.0]" = .ok a)
    (hlive : a.live = true) (haddr : ptr.addr = a.addr) (hkind : kind = a.kind)
    (hsize : size = Allocation.size a) (halign : align = a.align) :
    BasicMemory.deallocate mem ptr kind size align handleExtra =
      (do
        let extra' ← handleExtra a.extra provExtra
        pure { mem with allocations :=
          mem.allocations.set id._0.toNat { a with live := false, extra := extra' } }) := by
  rw [basicMemory_deallocate_steps mem ptr kind size align handleExtra id provExtra a hp ha]
  simp only [hlive, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ne_eq, haddr, not_true_eq_false,
    hkind, hsize, halign]
  obtain ⟨hi, hget⟩ := listIndex_eq_ok_iff.mp ha
  cases handleExtra a.extra provExtra with
  | error s => rfl
  | ok extra' =>
    show (listSet mem.allocations id._0 _ "set" >>= fun allocations =>
      pure { mem with allocations := allocations }) = _
    rw [listSet_of_getElem? hi hget]
    rfl

/-- Complete characterization of a successful `BasicMemory::deallocate`, for
every `ProvExtra`, `AllocExtra`, and `handle_extra`. -/
theorem basicMemory_deallocate_ok_iff (mem mem' : BasicMemory x86_64 ProvExtra AllocExtra)
    (ptr : ThinPointer (Provenance ProvExtra)) (kind : AllocationKind) (size : Size)
    (align : Align) (handleExtra : AllocExtra → ProvExtra → Interp AllocExtra) :
    BasicMemory.deallocate mem ptr kind size align handleExtra = .ok mem' ↔
      ∃ id provExtra a extra',
        ptr.provenance = some (id, provExtra) ∧ 0 ≤ id._0 ∧
        mem.allocations[id._0.toNat]? = some a ∧
        a.live = true ∧ ptr.addr = a.addr ∧ kind = a.kind ∧ size = Allocation.size a ∧
        align = a.align ∧ handleExtra a.extra provExtra = .ok extra' ∧
        mem' = { mem with allocations :=
          mem.allocations.set id._0.toNat { a with live := false, extra := extra' } } := by
  constructor
  · intro h
    cases hp : ptr.provenance with
    | none =>
      rw [basicMemory_deallocate_no_provenance_ub mem ptr kind size align handleExtra hp] at h
      cases h
    | some pr =>
      obtain ⟨id, provExtra⟩ := pr
      cases ha : listIndex mem.allocations id._0 "self.allocations[id.0]" with
      | error s =>
        rw [basicMemory_deallocate_bad_id mem ptr kind size align handleExtra id provExtra s hp ha]
          at h
        cases h
      | ok a =>
        obtain ⟨hi, hget⟩ := listIndex_eq_ok_iff.mp ha
        cases hlive : a.live with
        | false =>
          rw [basicMemory_deallocate_double_free_ub mem ptr kind size align handleExtra id
            provExtra a hp ha hlive] at h
          cases h
        | true =>
          by_cases haddr : ptr.addr = a.addr
          · by_cases hkind : kind = a.kind
            · by_cases hsize : size = Allocation.size a
              · by_cases halign : align = a.align
                · rw [basicMemory_deallocate_checked mem ptr kind size align handleExtra id
                    provExtra a hp ha hlive haddr hkind hsize halign] at h
                  obtain ⟨extra', hh, h⟩ := interp_bind_eq_ok h
                  exact ⟨id, provExtra, a, extra', rfl, hi, hget, hlive, haddr, hkind, hsize,
                    halign, hh, (interp_pure_eq_ok h).symm⟩
                · rw [basicMemory_deallocate_align_mismatch_ub mem ptr kind size align handleExtra
                    id provExtra a hp ha hlive haddr hkind hsize halign] at h
                  cases h
              · rw [basicMemory_deallocate_size_mismatch_ub mem ptr kind size align handleExtra
                  id provExtra a hp ha hlive haddr hkind hsize] at h
                cases h
            · rw [basicMemory_deallocate_kind_mismatch_ub mem ptr kind size align handleExtra
                id provExtra a hp ha hlive haddr hkind] at h
              cases h
          · rw [basicMemory_deallocate_not_beginning_ub mem ptr kind size align handleExtra
              id provExtra a hp ha hlive haddr] at h
            cases h
  · rintro ⟨id, provExtra, a, extra', hp, hi, hget, hlive, haddr, hkind, hsize, halign, hh, rfl⟩
    rw [basicMemory_deallocate_checked mem ptr kind size align handleExtra id provExtra a hp
      (listIndex_eq_ok_iff.mpr ⟨hi, hget⟩) hlive haddr hkind hsize halign, hh]
    rfl

/-- Complete characterization of every stopping outcome of
`BasicMemory::deallocate`, in exact upstream check order, for every
`ProvExtra`, `AllocExtra`, and `handle_extra`: provenance, the allocation
lookup, liveness, offset, kind, size, alignment, and `handle_extra`. -/
theorem basicMemory_deallocate_error_iff (mem : BasicMemory x86_64 ProvExtra AllocExtra)
    (ptr : ThinPointer (Provenance ProvExtra)) (kind : AllocationKind) (size : Size)
    (align : Align) (handleExtra : AllocExtra → ProvExtra → Interp AllocExtra) (e : Stop) :
    BasicMemory.deallocate mem ptr kind size align handleExtra = .error e ↔
      (ptr.provenance = none ∧ e = .ub "deallocating invalid pointer") ∨
      ∃ id provExtra, ptr.provenance = some (id, provExtra) ∧
        (listIndex mem.allocations id._0 "self.allocations[id.0]" = .error e ∨
         ∃ a, listIndex mem.allocations id._0 "self.allocations[id.0]" = .ok a ∧
          ((a.live = false ∧ e = .ub "double-free") ∨
           (a.live = true ∧ ptr.addr ≠ a.addr ∧
             e = .ub "deallocating with pointer not to the beginning of its allocation") ∨
           (a.live = true ∧ ptr.addr = a.addr ∧ kind ≠ a.kind ∧
             e = .ub (deallocKindMismatchMsg a.kind kind)) ∨
           (a.live = true ∧ ptr.addr = a.addr ∧ kind = a.kind ∧ size ≠ Allocation.size a ∧
             e = .ub "deallocating with incorrect size information") ∨
           (a.live = true ∧ ptr.addr = a.addr ∧ kind = a.kind ∧ size = Allocation.size a ∧
             align ≠ a.align ∧ e = .ub "deallocating with incorrect alignment information") ∨
           (a.live = true ∧ ptr.addr = a.addr ∧ kind = a.kind ∧ size = Allocation.size a ∧
             align = a.align ∧ handleExtra a.extra provExtra = .error e))) := by
  constructor
  · intro h
    cases hp : ptr.provenance with
    | none =>
      rw [basicMemory_deallocate_no_provenance_ub mem ptr kind size align handleExtra hp] at h
      cases h
      exact Or.inl ⟨rfl, rfl⟩
    | some pr =>
      obtain ⟨id, provExtra⟩ := pr
      refine Or.inr ⟨id, provExtra, rfl, ?_⟩
      cases ha : listIndex mem.allocations id._0 "self.allocations[id.0]" with
      | error s =>
        rw [basicMemory_deallocate_bad_id mem ptr kind size align handleExtra id provExtra s hp ha]
          at h
        cases h
        exact Or.inl rfl
      | ok a =>
        refine Or.inr ⟨a, rfl, ?_⟩
        cases hlive : a.live with
        | false =>
          rw [basicMemory_deallocate_double_free_ub mem ptr kind size align handleExtra id
            provExtra a hp ha hlive] at h
          cases h
          exact Or.inl ⟨rfl, rfl⟩
        | true =>
          refine Or.inr ?_
          by_cases haddr : ptr.addr = a.addr
          · refine Or.inr ?_
            by_cases hkind : kind = a.kind
            · refine Or.inr ?_
              by_cases hsize : size = Allocation.size a
              · refine Or.inr ?_
                by_cases halign : align = a.align
                · rw [basicMemory_deallocate_checked mem ptr kind size align handleExtra id
                    provExtra a hp ha hlive haddr hkind hsize halign] at h
                  rcases interp_bind_eq_error h with hh | ⟨_, _, hc⟩
                  · exact Or.inr ⟨rfl, haddr, hkind, hsize, halign, hh⟩
                  · cases hc
                · rw [basicMemory_deallocate_align_mismatch_ub mem ptr kind size align handleExtra
                    id provExtra a hp ha hlive haddr hkind hsize halign] at h
                  cases h
                  exact Or.inl ⟨rfl, haddr, hkind, hsize, halign, rfl⟩
              · rw [basicMemory_deallocate_size_mismatch_ub mem ptr kind size align handleExtra
                  id provExtra a hp ha hlive haddr hkind hsize] at h
                cases h
                exact Or.inl ⟨rfl, haddr, hkind, hsize, rfl⟩
            · rw [basicMemory_deallocate_kind_mismatch_ub mem ptr kind size align handleExtra
                id provExtra a hp ha hlive haddr hkind] at h
              cases h
              exact Or.inl ⟨rfl, haddr, hkind, rfl⟩
          · rw [basicMemory_deallocate_not_beginning_ub mem ptr kind size align handleExtra
              id provExtra a hp ha hlive haddr] at h
            cases h
            exact Or.inl ⟨rfl, haddr, rfl⟩
  · rintro (⟨hp, rfl⟩ | ⟨id, provExtra, hp, hbad | ⟨a, ha, hcase⟩⟩)
    · exact basicMemory_deallocate_no_provenance_ub mem ptr kind size align handleExtra hp
    · exact basicMemory_deallocate_bad_id mem ptr kind size align handleExtra id provExtra e hp hbad
    · rcases hcase with ⟨hlive, rfl⟩ | ⟨hlive, haddr, rfl⟩ | ⟨hlive, haddr, hkind, rfl⟩ |
        ⟨hlive, haddr, hkind, hsize, rfl⟩ | ⟨hlive, haddr, hkind, hsize, halign, rfl⟩ |
        ⟨hlive, haddr, hkind, hsize, halign, hh⟩
      · exact basicMemory_deallocate_double_free_ub mem ptr kind size align handleExtra id
          provExtra a hp ha hlive
      · exact basicMemory_deallocate_not_beginning_ub mem ptr kind size align handleExtra id
          provExtra a hp ha hlive haddr
      · exact basicMemory_deallocate_kind_mismatch_ub mem ptr kind size align handleExtra id
          provExtra a hp ha hlive haddr hkind
      · exact basicMemory_deallocate_size_mismatch_ub mem ptr kind size align handleExtra id
          provExtra a hp ha hlive haddr hkind hsize
      · exact basicMemory_deallocate_align_mismatch_ub mem ptr kind size align handleExtra id
          provExtra a hp ha hlive haddr hkind hsize halign
      · rw [basicMemory_deallocate_checked mem ptr kind size align handleExtra id provExtra a hp
          ha hlive haddr hkind hsize halign, hh]
        rfl

/-! ### `BasicMemory::leak_check` -/

/-- `BasicMemory::leak_check` reports `MemoryLeak` exactly when a live `Heap`
allocation exists; it never stops for any other reason. -/
theorem basicMemory_leak_check_error_iff (mem : BasicMemory x86_64 ProvExtra AllocExtra)
    (e : Stop) :
    BasicMemory.leak_check mem = .error e ↔
      e = .memoryLeak ∧ ∃ a ∈ mem.allocations, a.live = true ∧ a.kind = .Heap := by
  unfold BasicMemory.leak_check
  by_cases h : mem.allocations.any (fun a => a.live && decide (a.kind = .Heap)) = true
  · rw [ite_eq_left h]
    have hex : ∃ a ∈ mem.allocations, a.live = true ∧ a.kind = .Heap := by
      obtain ⟨a, hm, ha⟩ := List.any_eq_true.mp h
      rw [Bool.and_eq_true, decide_eq_true_eq] at ha
      exact ⟨a, hm, ha⟩
    constructor
    · intro he; cases he; exact ⟨rfl, hex⟩
    · rintro ⟨rfl, _⟩; rfl
  · rw [ite_eq_right h]
    constructor
    · intro he; cases he
    · rintro ⟨_, a, hm, hl, hk⟩
      exact absurd (List.any_eq_true.mpr ⟨a, hm, by rw [hl, hk]; rfl⟩) h

/-- `BasicMemory::leak_check` passes exactly when no live allocation is a
`Heap` allocation. -/
theorem basicMemory_leak_check_ok_iff (mem : BasicMemory x86_64 ProvExtra AllocExtra) :
    BasicMemory.leak_check mem = .ok () ↔
      ∀ a ∈ mem.allocations, a.live = true → a.kind ≠ .Heap := by
  unfold BasicMemory.leak_check
  by_cases h : mem.allocations.any (fun a => a.live && decide (a.kind = .Heap)) = true
  · rw [ite_eq_left h]
    constructor
    · intro he; cases he
    · intro hall
      obtain ⟨a, hm, ha⟩ := List.any_eq_true.mp h
      rw [Bool.and_eq_true, decide_eq_true_eq] at ha
      exact absurd ha.2 (hall a hm ha.1)
  · rw [ite_eq_right h]
    constructor
    · intro _ a hm hl hk
      exact h (List.any_eq_true.mpr ⟨a, hm, by rw [hl, hk]; rfl⟩)
    · intro _; rfl

/-- `leak_check` exempts every kind but `Heap`: a memory whose live
allocations are all `Global`, `Stack`, `Function`, or `VTable` allocations
passes. In particular memory handed out by a `Global`-backed (static)
allocator is never reported as leaked. -/
theorem basicMemory_leak_check_ok_of_no_heap (mem : BasicMemory x86_64 ProvExtra AllocExtra)
    (h : ∀ a ∈ mem.allocations, a.live = true →
      a.kind = .Global ∨ a.kind = .Stack ∨ a.kind = .Function ∨ a.kind = .VTable) :
    BasicMemory.leak_check mem = .ok () := by
  rw [basicMemory_leak_check_ok_iff]
  intro a hm hl hk
  rcases h a hm hl with h' | h' | h' | h' <;> rw [hk] at h' <;> cases h'

end BasicMemoryLaws

/-! ### The `BasicMemory<x86_64>` instance (`Mach`) -/

/-- The `pick` predicate of `BM.allocate` is the polymorphic one. -/
theorem bm_allocAddrOk_eq (mem : BM) (size : Size) (align : Align) (addr : Int) :
    BM.allocAddrOk mem size align addr = BasicMemory.allocAddrOk mem size align addr := rfl

/-- The first-fit search of `BM.allocate` is the polymorphic one. -/
theorem bm_firstFitAddr_eq (mem : BM) (size : Size) (align : Align) :
    ∀ (fuel k : Nat), firstFitAddr mem size align fuel k =
      BasicMemory.firstFitAddr mem size align fuel k
  | 0, _ => rfl
  | fuel + 1, k => by
    unfold firstFitAddr BasicMemory.firstFitAddr
    rw [bm_allocAddrOk_eq, bm_firstFitAddr_eq mem size align fuel (k + 1)]

/-- `BM.allocate`, the `BasicMemory<x86_64>` transcription, is the polymorphic
`BasicMemory::allocate` at `ProvExtra = AllocExtra = ()`; the laws above hold
of it. -/
theorem bm_allocate_eq_basic (mem : BM) (kind : AllocationKind) (size : Size) (align : Align) :
    BM.allocate mem kind size align = BasicMemory.allocate mem kind size align () () := by
  unfold BM.allocate BasicMemory.allocate BM.pickAddr BasicMemory.pickAddr
  rw [bm_firstFitAddr_eq]

/-- `BM.deallocate`, the `BasicMemory<x86_64>` transcription, is the polymorphic
`BasicMemory::deallocate` with the trivial `handle_extra`; the laws above hold
of it. -/
theorem bm_deallocate_eq_basic (mem : BM) (ptr : Ptr) (kind : AllocationKind) (size : Size)
    (align : Align) :
    BM.deallocate mem ptr kind size align =
      BasicMemory.deallocate mem ptr kind size align (fun extra _ => pure extra) := by
  unfold BM.deallocate BasicMemory.deallocate
  cases ptr.provenance with
  | none => rfl
  | some pr =>
    dsimp only
    cases listIndex mem.allocations pr.1._0 "self.allocations[id.0]" with
    | error e => rfl
    | ok a => rfl

/-- Complete characterization of a successful `Deallocate`-side
`BasicMemory<x86_64>::deallocate`: the allocation is live, the pointer is to
its beginning, kind, size, and alignment match, and it is marked dead. -/
theorem bm_deallocate_ok_iff (mem mem' : BM) (ptr : Ptr) (kind : AllocationKind) (size : Size)
    (align : Align) :
    BM.deallocate mem ptr kind size align = .ok mem' ↔
      ∃ id a,
        ptr.provenance = some (id, ()) ∧ 0 ≤ id._0 ∧ mem.allocations[id._0.toNat]? = some a ∧
        a.live = true ∧ ptr.addr = a.addr ∧ kind = a.kind ∧ size = Allocation.size a ∧
        align = a.align ∧
        mem' = { mem with allocations :=
          mem.allocations.set id._0.toNat { a with live := false } } := by
  rw [bm_deallocate_eq_basic, basicMemory_deallocate_ok_iff]
  constructor
  · rintro ⟨id, _, a, extra', hp, hi, hget, hlive, haddr, hkind, hsize, halign, hh, rfl⟩
    cases interp_pure_eq_ok hh
    exact ⟨id, a, hp, hi, hget, hlive, haddr, hkind, hsize, halign, rfl⟩
  · rintro ⟨id, a, hp, hi, hget, hlive, haddr, hkind, hsize, halign, rfl⟩
    exact ⟨id, (), a, a.extra, hp, hi, hget, hlive, haddr, hkind, hsize, halign, rfl, rfl⟩

/-- Complete bidirectional error characterization of `BM.deallocate`, in exact
upstream check order (since `BM`'s trivial `handle_extra` never fails). -/
theorem bm_deallocate_error_iff (mem : BM) (ptr : Ptr) (kind : AllocationKind) (size : Size)
    (align : Align) (e : Stop) :
    BM.deallocate mem ptr kind size align = .error e ↔
      (ptr.provenance = none ∧ e = .ub "deallocating invalid pointer") ∨
      ∃ id, ptr.provenance = some (id, ()) ∧
        (listIndex mem.allocations id._0 "self.allocations[id.0]" = .error e ∨
         ∃ a, listIndex mem.allocations id._0 "self.allocations[id.0]" = .ok a ∧
          ((a.live = false ∧ e = .ub "double-free") ∨
           (a.live = true ∧ ptr.addr ≠ a.addr ∧
             e = .ub "deallocating with pointer not to the beginning of its allocation") ∨
           (a.live = true ∧ ptr.addr = a.addr ∧ kind ≠ a.kind ∧
             e = .ub (deallocKindMismatchMsg a.kind kind)) ∨
           (a.live = true ∧ ptr.addr = a.addr ∧ kind = a.kind ∧ size ≠ Allocation.size a ∧
             e = .ub "deallocating with incorrect size information") ∨
           (a.live = true ∧ ptr.addr = a.addr ∧ kind = a.kind ∧ size = Allocation.size a ∧
             align ≠ a.align ∧ e = .ub "deallocating with incorrect alignment information"))) := by
  rw [bm_deallocate_eq_basic, basicMemory_deallocate_error_iff]
  constructor
  · rintro (h | ⟨id, ⟨⟩, hp, hbad | ⟨a, ha, hc⟩⟩)
    · exact Or.inl h
    · exact Or.inr ⟨id, hp, Or.inl hbad⟩
    · refine Or.inr ⟨id, hp, Or.inr ⟨a, ha, ?_⟩⟩
      rcases hc with h1 | h2 | h3 | h4 | h5 | ⟨_, _, _, _, _, hpure⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inl h3))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h5)))
      · cases hpure
  · rintro (h | ⟨id, hp, hbad | ⟨a, ha, hc⟩⟩)
    · exact Or.inl h
    · exact Or.inr ⟨id, (), hp, Or.inl hbad⟩
    · refine Or.inr ⟨id, (), hp, Or.inr ⟨a, ha, ?_⟩⟩
      rcases hc with h1 | h2 | h3 | h4 | h5
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inl h3))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))

/-- `evalIntrinsicM .Allocate` on `Mach` with `size ≥ 2^63` (`!x86_64.valid_size`)
is UB `"asking for a too large allocation"`. -/
theorem allocate_oversized_bm_ub (m : Mach) (size : Int) (sTy : «Type») (align : Int)
    (aTy : «Type») (p : PtrType) (al : Align) (hs : (2 : Int) ^ 63 ≤ size)
    (ha : alignFromBytesInt align = some al) (hk : PtrType.meta_kind p = .None) :
    evalIntrinsicM (M := BM) m .Allocate [(.Int size, sTy), (.Int align, aTy)] (.Ptr p) =
      .error (.ub "asking for a too large allocation") := by
  have hs0 : 0 ≤ size := by omega
  rw [allocate_eq_memory m size sTy align aTy p al hs0 ha hk, cm_allocate_bm_eq]
  unfold CM.allocate
  have hal : BM.allocate m.mem.memory .Heap ⟨size.toNat⟩ al =
      .error (.ub "asking for a too large allocation") := by
    rw [bm_allocate_eq_basic, basicMemory_allocate_too_large_ub]
    exact (x86_64_valid_size_false_iff ⟨size.toNat⟩).mpr (by show 2 ^ 63 ≤ size.toNat; omega)
  rw [hal]
  rfl

/-- `evalIntrinsicM .Deallocate` on `Mach` of a live non-`Heap` allocation
(`Global` `StaticAllocator` `rust#166221`, `Stack`, `Function`, `VTable`) is UB. -/
theorem evalIntrinsicM_deallocate_kind_mismatch_bm_ub (m : Mach) (ptr : Ptr) (pTy : «Type»)
    (size : Int) (sTy : «Type») (align : Int) (aTy : «Type») (al : Align)
    (id : AllocId) (a : Allocation Unit Unit)
    (hs : 0 ≤ size) (ha : alignFromBytesInt align = some al)
    (hp : ptr.provenance = some (id, ())) (hi : 0 ≤ id._0)
    (hget : m.mem.memory.allocations[id._0.toNat]? = some a)
    (hlive : a.live = true) (haddr : ptr.addr = a.addr) (hkind : AllocationKind.Heap ≠ a.kind) :
    evalIntrinsicM (M := BM) m .Deallocate
        [(.Ptr ⟨ptr, none⟩, pTy), (.Int size, sTy), (.Int align, aTy)] unitType =
      .error (.ub (deallocKindMismatchMsg a.kind .Heap)) := by
  rw [deallocate_eq_memory m ptr pTy size sTy align aTy al hs ha, cm_deallocate_bm_eq]
  unfold CM.deallocate
  have hd : BM.deallocate m.mem.memory ptr .Heap ⟨size.toNat⟩ al =
      .error (.ub (deallocKindMismatchMsg a.kind .Heap)) := by
    rw [bm_deallocate_eq_basic,
      basicMemory_deallocate_kind_mismatch_ub m.mem.memory ptr .Heap ⟨size.toNat⟩ al _ id () a hp
        (listIndex_eq_ok_iff.mpr ⟨hi, hget⟩) hlive haddr hkind]
  rw [hd]
  rfl

/-! ### The `TreeBorrowsMemory<x86_64>` instance (`MachTB`): protectors -/

/-- The `handle_extra` closure of `TreeBorrowsMemory::deallocate`
(`spec/mem/tree_borrows/memory.md`): a write access through the pointer's
node over the whole allocation, then the strong-protector check. -/
def tbDeallocHandler (size : Size) (extra : TreeBorrowsAllocationExtra) (path : Path) :
    Interp TreeBorrowsAllocationExtra := do
  let root' ← Node.access extra.root (some path) .Write ⟨0⟩ size
  if Node.contains_strong_protector_preventing_deallocation root' then
    ub "Tree Borrows: deallocating strongly protected allocation"
  else
    pure { root := root' }

/-- `TreeBorrowsMemory::deallocate` is `BasicMemory::deallocate` with
`tbDeallocHandler` as its `handle_extra`. -/
theorem tb_deallocate_eq_basic (tbm : TBM) (ptr : ThinPointer TreeBorrowsProvenance)
    (kind : AllocationKind) (size : Size) (align : Align) :
    TreeBorrowsMemory.deallocate tbm ptr kind size align =
      (do
        let mem' ← BasicMemory.deallocate tbm.mem ptr kind size align (tbDeallocHandler size)
        pure { tbm with mem := mem' }) := rfl

/-- The Tree Borrows deallocation handler after a successful write access:
the strong-protector check. -/
theorem tbDeallocHandler_of_access (size : Size) (extra : TreeBorrowsAllocationExtra)
    (path : Path) (root' : Node)
    (hacc : Node.access extra.root (some path) .Write ⟨0⟩ size = .ok root') :
    tbDeallocHandler size extra path =
      (if Node.contains_strong_protector_preventing_deallocation root' = true then
        ub "Tree Borrows: deallocating strongly protected allocation"
      else pure { root := root' }) := by
  unfold tbDeallocHandler
  rw [hacc]
  rfl

/-- The Tree Borrows deallocation handler propagates a failing write access. -/
theorem tbDeallocHandler_of_access_error (size : Size) (extra : TreeBorrowsAllocationExtra)
    (path : Path) (e : Stop)
    (hacc : Node.access extra.root (some path) .Write ⟨0⟩ size = .error e) :
    tbDeallocHandler size extra path = .error e := by
  unfold tbDeallocHandler
  rw [hacc]
  rfl

/-- The Tree Borrows deallocation handler succeeds exactly when the write
access succeeds and leaves no strong protector that prevents deallocation. -/
theorem tbDeallocHandler_ok_iff (size : Size) (extra extra' : TreeBorrowsAllocationExtra)
    (path : Path) :
    tbDeallocHandler size extra path = .ok extra' ↔
      ∃ root', Node.access extra.root (some path) .Write ⟨0⟩ size = .ok root' ∧
        Node.contains_strong_protector_preventing_deallocation root' = false ∧
        extra' = { root := root' } := by
  cases hacc : Node.access extra.root (some path) .Write ⟨0⟩ size with
  | error s =>
    rw [tbDeallocHandler_of_access_error size extra path s hacc]
    constructor
    · intro h; cases h
    · rintro ⟨_, hc, _⟩; cases hc
  | ok root' =>
    rw [tbDeallocHandler_of_access size extra path root' hacc]
    cases hprot : Node.contains_strong_protector_preventing_deallocation root' with
    | true =>
      simp only [↓reduceIte]
      constructor
      · intro h; cases h
      · rintro ⟨r, hr, hc, _⟩
        cases hr
        rw [hprot] at hc
        cases hc
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro h
        exact ⟨root', rfl, hprot, (interp_pure_eq_ok h).symm⟩
      · rintro ⟨r, hr, _, rfl⟩
        cases hr
        rfl

/-- The Tree Borrows deallocation handler stops exactly when the write access
is UB (for instance a write through a `Frozen` tag, or a foreign write to a
protected `Frozen` or `Unique` tag), or when the access succeeds and a strong
protector prevents deallocation. -/
theorem tbDeallocHandler_error_iff (size : Size) (extra : TreeBorrowsAllocationExtra)
    (path : Path) (e : Stop) :
    tbDeallocHandler size extra path = .error e ↔
      Node.access extra.root (some path) .Write ⟨0⟩ size = .error e ∨
      ∃ root', Node.access extra.root (some path) .Write ⟨0⟩ size = .ok root' ∧
        Node.contains_strong_protector_preventing_deallocation root' = true ∧
        e = .ub "Tree Borrows: deallocating strongly protected allocation" := by
  cases hacc : Node.access extra.root (some path) .Write ⟨0⟩ size with
  | error s =>
    rw [tbDeallocHandler_of_access_error size extra path s hacc]
    constructor
    · intro h; cases h; exact Or.inl rfl
    · rintro (hc | ⟨_, hc, _⟩)
      · cases hc; rfl
      · cases hc
  | ok root' =>
    rw [tbDeallocHandler_of_access size extra path root' hacc]
    cases hprot : Node.contains_strong_protector_preventing_deallocation root' with
    | true =>
      simp only [↓reduceIte]
      constructor
      · intro h
        cases h
        exact Or.inr ⟨root', rfl, hprot, rfl⟩
      · rintro (hc | ⟨r, hr, _, rfl⟩)
        · cases hc
        · rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro h; cases h
      · rintro (hc | ⟨r, hr, hc, _⟩)
        · cases hc
        · cases hr
          rw [hprot] at hc
          cases hc

/-- Complete characterization of a successful `TreeBorrowsMemory::deallocate`:
the `BasicMemory` checks, the write access through the pointer's node, and no
strong protector preventing deallocation. -/
theorem tb_deallocate_ok_iff (tbm tbm' : TBM) (ptr : ThinPointer TreeBorrowsProvenance)
    (kind : AllocationKind) (size : Size) (align : Align) :
    TreeBorrowsMemory.deallocate tbm ptr kind size align = .ok tbm' ↔
      ∃ id path a root',
        ptr.provenance = some (id, path) ∧ 0 ≤ id._0 ∧
        tbm.mem.allocations[id._0.toNat]? = some a ∧
        a.live = true ∧ ptr.addr = a.addr ∧ kind = a.kind ∧ size = Allocation.size a ∧
        align = a.align ∧
        Node.access a.extra.root (some path) .Write ⟨0⟩ size = .ok root' ∧
        Node.contains_strong_protector_preventing_deallocation root' = false ∧
        tbm' = { tbm with mem := { tbm.mem with allocations :=
          (tbm.mem.allocations.set id._0.toNat
            { a with live := false, extra := { root := root' } }) } } := by
  rw [tb_deallocate_eq_basic]
  constructor
  · intro h
    obtain ⟨mem', hd, h⟩ := interp_bind_eq_ok h
    obtain rfl := interp_pure_eq_ok h
    obtain ⟨id, path, a, extra', hp, hi, hget, hlive, haddr, hkind, hsize, halign, hh, rfl⟩ :=
      (basicMemory_deallocate_ok_iff tbm.mem mem' ptr kind size align (tbDeallocHandler size)).mp hd
    obtain ⟨root', hacc, hprot, rfl⟩ := (tbDeallocHandler_ok_iff size a.extra extra' path).mp hh
    exact ⟨id, path, a, root', hp, hi, hget, hlive, haddr, hkind, hsize, halign, hacc, hprot, rfl⟩
  · rintro ⟨id, path, a, root', hp, hi, hget, hlive, haddr, hkind, hsize, halign, hacc, hprot, rfl⟩
    have hh : tbDeallocHandler size a.extra path = .ok { root := root' } :=
      (tbDeallocHandler_ok_iff size a.extra _ path).mpr ⟨root', hacc, hprot, rfl⟩
    rw [(basicMemory_deallocate_ok_iff tbm.mem _ ptr kind size align (tbDeallocHandler size)).mpr
      ⟨id, path, a, _, hp, hi, hget, hlive, haddr, hkind, hsize, halign, hh, rfl⟩]
    rfl

/-- `TreeBorrowsMemory::deallocate` of an allocation that passes the
`BasicMemory` checks but whose borrow tree, after the write access, still
contains a strong protector preventing deallocation is UB. -/
theorem tb_deallocate_strong_protector_ub (tbm : TBM) (ptr : ThinPointer TreeBorrowsProvenance)
    (kind : AllocationKind) (size : Size) (align : Align) (id : AllocId) (path : Path)
    (a : Allocation Path TreeBorrowsAllocationExtra) (root' : Node)
    (hp : ptr.provenance = some (id, path)) (hi : 0 ≤ id._0)
    (hget : tbm.mem.allocations[id._0.toNat]? = some a) (hlive : a.live = true)
    (haddr : ptr.addr = a.addr) (hkind : kind = a.kind) (hsize : size = Allocation.size a)
    (halign : align = a.align)
    (hacc : Node.access a.extra.root (some path) .Write ⟨0⟩ size = .ok root')
    (hprot : Node.contains_strong_protector_preventing_deallocation root' = true) :
    TreeBorrowsMemory.deallocate tbm ptr kind size align =
      .error (.ub "Tree Borrows: deallocating strongly protected allocation") := by
  have hh : tbDeallocHandler size a.extra path =
      .error (.ub "Tree Borrows: deallocating strongly protected allocation") :=
    (tbDeallocHandler_error_iff size a.extra path _).mpr (Or.inr ⟨root', hacc, hprot, rfl⟩)
  rw [tb_deallocate_eq_basic,
    (basicMemory_deallocate_error_iff tbm.mem ptr kind size align (tbDeallocHandler size) _).mpr
      (Or.inr ⟨id, path, hp, Or.inr ⟨a, listIndex_eq_ok_iff.mpr ⟨hi, hget⟩,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨hlive, haddr, hkind, hsize, halign, hh⟩))))⟩⟩)]
  rfl

/-- `TreeBorrowsMemory::deallocate` whose write access is UB (a `Frozen` or
`Disabled` tag, or a protected foreign tag) is UB with the access's message. -/
theorem tb_deallocate_access_ub (tbm : TBM) (ptr : ThinPointer TreeBorrowsProvenance)
    (kind : AllocationKind) (size : Size) (align : Align) (id : AllocId) (path : Path)
    (a : Allocation Path TreeBorrowsAllocationExtra) (e : Stop)
    (hp : ptr.provenance = some (id, path)) (hi : 0 ≤ id._0)
    (hget : tbm.mem.allocations[id._0.toNat]? = some a) (hlive : a.live = true)
    (haddr : ptr.addr = a.addr) (hkind : kind = a.kind) (hsize : size = Allocation.size a)
    (halign : align = a.align)
    (hacc : Node.access a.extra.root (some path) .Write ⟨0⟩ size = .error e) :
    TreeBorrowsMemory.deallocate tbm ptr kind size align = .error e := by
  have hh : tbDeallocHandler size a.extra path = .error e :=
    (tbDeallocHandler_error_iff size a.extra path e).mpr (Or.inl hacc)
  rw [tb_deallocate_eq_basic,
    (basicMemory_deallocate_error_iff tbm.mem ptr kind size align (tbDeallocHandler size) e).mpr
      (Or.inr ⟨id, path, hp, Or.inr ⟨a, listIndex_eq_ok_iff.mpr ⟨hi, hget⟩,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨hlive, haddr, hkind, hsize, halign, hh⟩))))⟩⟩)]
  rfl

/-- Complete bidirectional error characterization of `TreeBorrowsMemory::deallocate`,
combining `BasicMemory`'s upstream check order with `tbDeallocHandler`'s write
access and strong-protector checks. -/
theorem tb_deallocate_error_iff (tbm : TBM) (ptr : ThinPointer TreeBorrowsProvenance)
    (kind : AllocationKind) (size : Size) (align : Align) (e : Stop) :
    TreeBorrowsMemory.deallocate tbm ptr kind size align = .error e ↔
      (ptr.provenance = none ∧ e = .ub "deallocating invalid pointer") ∨
      ∃ id path, ptr.provenance = some (id, path) ∧
        (listIndex tbm.mem.allocations id._0 "self.allocations[id.0]" = .error e ∨
         ∃ a, listIndex tbm.mem.allocations id._0 "self.allocations[id.0]" = .ok a ∧
          ((a.live = false ∧ e = .ub "double-free") ∨
           (a.live = true ∧ ptr.addr ≠ a.addr ∧
             e = .ub "deallocating with pointer not to the beginning of its allocation") ∨
           (a.live = true ∧ ptr.addr = a.addr ∧ kind ≠ a.kind ∧
             e = .ub (deallocKindMismatchMsg a.kind kind)) ∨
           (a.live = true ∧ ptr.addr = a.addr ∧ kind = a.kind ∧ size ≠ Allocation.size a ∧
             e = .ub "deallocating with incorrect size information") ∨
           (a.live = true ∧ ptr.addr = a.addr ∧ kind = a.kind ∧ size = Allocation.size a ∧
             align ≠ a.align ∧ e = .ub "deallocating with incorrect alignment information") ∨
           (a.live = true ∧ ptr.addr = a.addr ∧ kind = a.kind ∧ size = Allocation.size a ∧
             align = a.align ∧
             (Node.access a.extra.root (some path) .Write ⟨0⟩ size = .error e ∨
              ∃ root', Node.access a.extra.root (some path) .Write ⟨0⟩ size = .ok root' ∧
                Node.contains_strong_protector_preventing_deallocation root' = true ∧
                e = .ub "Tree Borrows: deallocating strongly protected allocation")))) := by
  rw [tb_deallocate_eq_basic]
  constructor
  · intro h
    rcases interp_bind_eq_error h with hd | ⟨_, _, hc⟩
    · have hbm := (basicMemory_deallocate_error_iff tbm.mem ptr kind size align
        (tbDeallocHandler size) e).mp hd
      rcases hbm with h0 | ⟨id, path, hp, hbad | ⟨a, ha, hc⟩⟩
      · exact Or.inl h0
      · exact Or.inr ⟨id, path, hp, Or.inl hbad⟩
      · refine Or.inr ⟨id, path, hp, Or.inr ⟨a, ha, ?_⟩⟩
        rcases hc with h1 | h2 | h3 | h4 | h5 | ⟨hlive, haddr, hkind, hsize, halign, hh⟩
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr (Or.inl h3))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨hlive, haddr, hkind, hsize, halign, (tbDeallocHandler_error_iff size a.extra path e).mp hh⟩))))
    · cases hc
  · intro h
    have hbm : BasicMemory.deallocate tbm.mem ptr kind size align (tbDeallocHandler size) = .error e := by
      rw [basicMemory_deallocate_error_iff]
      rcases h with h0 | ⟨id, path, hp, hbad | ⟨a, ha, hc⟩⟩
      · exact Or.inl h0
      · exact Or.inr ⟨id, path, hp, Or.inl hbad⟩
      · refine Or.inr ⟨id, path, hp, Or.inr ⟨a, ha, ?_⟩⟩
        rcases hc with h1 | h2 | h3 | h4 | h5 | ⟨hlive, haddr, hkind, hsize, halign, htb⟩
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr (Or.inl h3))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨hlive, haddr, hkind, hsize, halign, (tbDeallocHandler_error_iff size a.extra path e).mpr htb⟩))))
    rw [hbm]
    rfl

/-- `evalIntrinsicM .Allocate` on `MachTB` with `size ≥ 2^63` (`!x86_64.valid_size`)
is UB `"asking for a too large allocation"`. -/
theorem allocate_oversized_tb_ub (m : MachTB) (size : Int) (sTy : «Type») (align : Int)
    (aTy : «Type») (p : PtrType) (al : Align) (hs : (2 : Int) ^ 63 ≤ size)
    (ha : alignFromBytesInt align = some al) (hk : PtrType.meta_kind p = .None) :
    evalIntrinsicM (M := TBM) m .Allocate [(.Int size, sTy), (.Int align, aTy)] (.Ptr p) =
      .error (.ub "asking for a too large allocation") := by
  have hs0 : 0 ≤ size := by omega
  rw [allocate_eq_memory m size sTy align aTy p al hs0 ha hk, cm_allocate_tb_eq]
  have hal : TreeBorrowsMemory.allocate m.mem.memory .Heap ⟨size.toNat⟩ al =
      .error (.ub "asking for a too large allocation") := by
    unfold TreeBorrowsMemory.allocate
    dsimp only
    rw [basicMemory_allocate_too_large_ub]
    · rfl
    · exact (x86_64_valid_size_false_iff ⟨size.toNat⟩).mpr (by show 2 ^ 63 ≤ size.toNat; omega)
  rw [hal]
  rfl

/-- `evalIntrinsicM .Deallocate` on `MachTB` of a live non-`Heap` allocation
(`Global` `StaticAllocator` `rust#166221`, `Stack`, `Function`, `VTable`) is UB. -/
theorem evalIntrinsicM_deallocate_kind_mismatch_tb_ub (m : MachTB)
    (ptr : ThinPointer TreeBorrowsProvenance) (pTy : «Type»)
    (size : Int) (sTy : «Type») (align : Int) (aTy : «Type») (al : Align)
    (id : AllocId) (path : Path) (a : Allocation Path TreeBorrowsAllocationExtra)
    (hs : 0 ≤ size) (ha : alignFromBytesInt align = some al)
    (hp : ptr.provenance = some (id, path)) (hi : 0 ≤ id._0)
    (hget : m.mem.memory.mem.allocations[id._0.toNat]? = some a)
    (hlive : a.live = true) (haddr : ptr.addr = a.addr) (hkind : AllocationKind.Heap ≠ a.kind) :
    evalIntrinsicM (M := TBM) m .Deallocate
        [(.Ptr ⟨ptr, none⟩, pTy), (.Int size, sTy), (.Int align, aTy)] unitType =
      .error (.ub (deallocKindMismatchMsg a.kind .Heap)) := by
  rw [deallocate_eq_memory m ptr pTy size sTy align aTy al hs ha, cm_deallocate_tb_eq]
  have hd : TreeBorrowsMemory.deallocate m.mem.memory ptr .Heap ⟨size.toNat⟩ al =
      .error (.ub (deallocKindMismatchMsg a.kind .Heap)) := by
    rw [tb_deallocate_error_iff]
    exact Or.inr ⟨id, path, hp, Or.inr ⟨a, listIndex_eq_ok_iff.mpr ⟨hi, hget⟩,
      Or.inr (Or.inr (Or.inl ⟨hlive, haddr, hkind, rfl⟩))⟩⟩
  rw [hd]
  rfl

/-- `Permission::prevents_deallocation`, classified: exactly the protected
`Unique`, and the protected `Reserved` and `Frozen` that had a local read.
Unprotected permissions, protected `Disabled`, and `Cell` never prevent
deallocation. -/
theorem permission_prevents_deallocation_iff (p : Permission) :
    Permission.prevents_deallocation p = true ↔
      p = .Prot .Unique ∨ (∃ b, p = .Prot (.Reserved true b)) ∨ p = .Prot (.Frozen true) := by
  rcases p with u | pp
  · constructor
    · intro h; cases h
    · rintro (h | ⟨_, h⟩ | h) <;> cases h
  · rcases pp with _ | ⟨r, f⟩ | _ | r | _
    · constructor
      · intro h; cases h
      · rintro (h | ⟨_, h⟩ | h) <;> cases h
    · constructor
      · intro h
        have hr : r = true := h
        subst hr
        exact Or.inr (Or.inl ⟨f, rfl⟩)
      · rintro (h | ⟨_, h⟩ | h)
        · cases h
        · cases h; rfl
        · cases h
    · exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
    · constructor
      · intro h
        have hr : r = true := h
        subst hr
        exact Or.inr (Or.inr rfl)
      · rintro (h | ⟨_, h⟩ | h)
        · cases h
        · cases h
        · cases h; rfl
    · constructor
      · intro h; cases h
      · rintro (h | ⟨_, h⟩ | h) <;> cases h

/-- `Cell` (interior mutability) never prevents deallocation, protected or
not. -/
theorem cell_never_prevents_deallocation :
    Permission.prevents_deallocation (.Prot .Cell) = false ∧
    Permission.prevents_deallocation (.Unprot .Cell) = false := ⟨rfl, rfl⟩

/-- `Node::contains_strong_protector_preventing_deallocation`, unfolded once:
the node itself is `Protected::Strong` and one of its permissions prevents
deallocation, or one of its children contains such a protector. -/
theorem node_contains_strong_protector_eq (children : List Node) (perms : List Permission)
    (prot : Protected) :
    Node.contains_strong_protector_preventing_deallocation ⟨children, perms, prot⟩ =
      ((decide (prot = .Strong) && perms.any Permission.prevents_deallocation) ||
        Node.anyChildPreventsDeallocation children) := by
  rw [Node.contains_strong_protector_preventing_deallocation]

/-- A leaf node prevents deallocation exactly when it is `Protected::Strong`
and one of its permissions prevents deallocation. -/
theorem leaf_contains_strong_protector_iff (perms : List Permission) (prot : Protected) :
    Node.contains_strong_protector_preventing_deallocation ⟨[], perms, prot⟩ = true ↔
      prot = .Strong ∧ ∃ p ∈ perms, Permission.prevents_deallocation p = true := by
  rw [node_contains_strong_protector_eq, Node.anyChildPreventsDeallocation, Bool.or_false,
    Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]

/-- A `Protected::Weak` leaf (a `Box` argument) never prevents deallocation,
whatever its permissions. -/
theorem weak_protector_never_prevents_deallocation (perms : List Permission) :
    Node.contains_strong_protector_preventing_deallocation ⟨[], perms, .Weak⟩ = false := by
  cases h : Node.contains_strong_protector_preventing_deallocation ⟨[], perms, .Weak⟩ with
  | false => rfl
  | true => exact absurd ((leaf_contains_strong_protector_iff perms .Weak).mp h).1 (by decide)

/-- An unprotected leaf never prevents deallocation. -/
theorem unprotected_never_prevents_deallocation (perms : List Permission) :
    Node.contains_strong_protector_preventing_deallocation ⟨[], perms, .No⟩ = false := by
  cases h : Node.contains_strong_protector_preventing_deallocation ⟨[], perms, .No⟩ with
  | false => rfl
  | true => exact absurd ((leaf_contains_strong_protector_iff perms .No).mp h).1 (by decide)

/-- A `Protected::Strong` leaf all of whose permissions are `Cell` never
prevents deallocation: the interior-mutability exemption. -/
theorem strong_cell_never_prevents_deallocation (perms : List Permission)
    (hcell : ∀ p ∈ perms, p = .Prot .Cell) :
    Node.contains_strong_protector_preventing_deallocation ⟨[], perms, .Strong⟩ = false := by
  cases h : Node.contains_strong_protector_preventing_deallocation ⟨[], perms, .Strong⟩ with
  | false => rfl
  | true =>
    obtain ⟨_, p, hm, hp⟩ := (leaf_contains_strong_protector_iff perms .Strong).mp h
    rw [hcell p hm] at hp
    cases hp

/-- A `Protected::Strong` leaf with a `Frozen` permission that had a local
read, or a `Unique` one, prevents deallocation. -/
theorem strong_accessed_prevents_deallocation (perms : List Permission) (p : Permission)
    (hm : p ∈ perms) (hp : p = .Prot (.Frozen true) ∨ p = .Prot .Unique) :
    Node.contains_strong_protector_preventing_deallocation ⟨[], perms, .Strong⟩ = true := by
  refine (leaf_contains_strong_protector_iff perms .Strong).mpr ⟨rfl, p, hm, ?_⟩
  rcases hp with rfl | rfl <;> rfl

/-- Releasing no protectors (`end_call` of a frame without protected
references) leaves the memory unchanged. -/
theorem tb_end_call_no_protectors (tbm : TBM) :
    TreeBorrowsMemory.end_call tbm { protectors := [] } = .ok tbm := rfl

/-- `TreeBorrowsMemory::end_call` releases protectors in frame order: the head
protector via `release_protector`, then the tail. -/
theorem tb_end_call_cons (tbm : TBM) (p : TreeBorrowsProvenance)
    (ps : List TreeBorrowsProvenance) :
    TreeBorrowsMemory.end_call tbm { protectors := p :: ps } =
      (do
        let tbm' ← TreeBorrowsMemory.release_protector tbm p
        TreeBorrowsMemory.end_call tbm' { protectors := ps }) := rfl

/-- `Node::release_protector` at the protected node itself (`path = some []`)
clears its protector to `Protected::No` and preserves its children and
permissions. -/
theorem node_release_protector_here (children : List Node) (perms : List Permission)
    (prot : Protected) (accesses : List (Option AccessKind)) :
    Node.release_protector ⟨children, perms, prot⟩ (some []) accesses =
      .ok ⟨children, perms, .No⟩ := rfl

mutual

/-- `nd` occurs somewhere in the borrow tree rooted at `root` (either `root`
itself or a descendant at arbitrary depth). -/
def Node.InTree (nd : Node) : Node → Prop
  | n@⟨children, _, _⟩ => nd = n ∨ Node.InForest nd children

/-- `nd` occurs somewhere in one of the borrow trees of `forest`. -/
def Node.InForest (nd : Node) : List Node → Prop
  | [] => False
  | c :: rest => Node.InTree nd c ∨ Node.InForest nd rest

end

mutual

/-- **Arbitrary-tree characterization of `Node::contains_strong_protector_preventing_deallocation`**:
a borrow tree of any depth prevents deallocation iff *some* node anywhere in the
tree is `Protected::Strong` and carries a permission that prevents deallocation. -/
theorem node_contains_strong_protector_iff : ∀ (n : Node),
    Node.contains_strong_protector_preventing_deallocation n = true ↔
      ∃ nd, Node.InTree nd n ∧ nd.«protected» = .Strong ∧
        ∃ p ∈ nd.permissions, Permission.prevents_deallocation p = true
  | ⟨children, perms, prot⟩ => by
    rw [node_contains_strong_protector_eq, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, List.any_eq_true, anyChildPreventsDeallocation_iff children]
    constructor
    · rintro (⟨hprot, hp⟩ | ⟨nd, hfor, hstrong, hp⟩)
      · exact ⟨⟨children, perms, prot⟩, Or.inl rfl, hprot, hp⟩
      · exact ⟨nd, Or.inr hfor, hstrong, hp⟩
    · rintro ⟨nd, (rfl | hfor), hstrong, hp⟩
      · exact Or.inl ⟨hstrong, hp⟩
      · exact Or.inr ⟨nd, hfor, hstrong, hp⟩

/-- Forest counterpart of `node_contains_strong_protector_iff`. -/
theorem anyChildPreventsDeallocation_iff : ∀ (children : List Node),
    Node.anyChildPreventsDeallocation children = true ↔
      ∃ nd, Node.InForest nd children ∧ nd.«protected» = .Strong ∧
        ∃ p ∈ nd.permissions, Permission.prevents_deallocation p = true
  | [] => by
    simp only [Node.anyChildPreventsDeallocation, Node.InForest, Bool.false_eq_true, false_and,
      exists_false]
  | c :: rest => by
    rw [Node.anyChildPreventsDeallocation, Bool.or_eq_true,
      node_contains_strong_protector_iff c, anyChildPreventsDeallocation_iff rest]
    constructor
    · rintro (⟨nd, hin, hstrong, hp⟩ | ⟨nd, hin, hstrong, hp⟩)
      · exact ⟨nd, Or.inl hin, hstrong, hp⟩
      · exact ⟨nd, Or.inr hin, hstrong, hp⟩
    · rintro ⟨nd, (hin | hin), hstrong, hp⟩
      · exact Or.inl ⟨nd, hin, hstrong, hp⟩
      · exact Or.inr ⟨nd, hin, hstrong, hp⟩

end

/-- **Arbitrary-tree Weak/Unprotected exemption (`rust#165833`)**: a borrow tree
of any depth containing only `Protected::No` and `Protected::Weak` nodes never
prevents deallocation. -/
theorem tree_no_strong_never_prevents_deallocation (n : Node)
    (h : ∀ nd, Node.InTree nd n → nd.«protected» ≠ .Strong) :
    Node.contains_strong_protector_preventing_deallocation n = false := by
  cases hc : Node.contains_strong_protector_preventing_deallocation n with
  | false => rfl
  | true =>
    obtain ⟨nd, hin, hstrong, _⟩ := (node_contains_strong_protector_iff n).mp hc
    exact absurd hstrong (h nd hin)

/-- **Arbitrary-tree `Cell` exemption (`rust#165833`)**: a borrow tree of any
depth in which every `Protected::Strong` node holds only `Cell` permissions
never prevents deallocation. -/
theorem tree_strong_cell_never_prevents_deallocation (n : Node)
    (h : ∀ nd, Node.InTree nd n → nd.«protected» = .Strong →
      ∀ p ∈ nd.permissions, p = .Prot .Cell) :
    Node.contains_strong_protector_preventing_deallocation n = false := by
  cases hc : Node.contains_strong_protector_preventing_deallocation n with
  | false => rfl
  | true =>
    obtain ⟨nd, hin, hstrong, p, hmem, hp⟩ := (node_contains_strong_protector_iff n).mp hc
    rw [h nd hin hstrong p hmem] at hp
    cases hp

/-- **Arbitrary-tree active strong protector (`rust#165833`)**: if *any* node at
any depth in a borrow tree is `Protected::Strong` with `Unique`, `Frozen(true)`,
or `Reserved(true, _)`, the whole tree prevents deallocation. -/
theorem tree_descendant_strong_prevents_deallocation (n nd : Node) (hin : Node.InTree nd n)
    (hstrong : nd.«protected» = .Strong) (p : Permission) (hm : p ∈ nd.permissions)
    (hp : p = .Prot .Unique ∨ (∃ b, p = .Prot (.Reserved true b)) ∨ p = .Prot (.Frozen true)) :
    Node.contains_strong_protector_preventing_deallocation n = true :=
  (node_contains_strong_protector_iff n).mpr
    ⟨nd, hin, hstrong, p, hm, (permission_prevents_deallocation_iff p).mpr hp⟩

/-! ### `leak_check` for `TreeBorrowsMemory` and `ConcurrentMemory` -/

/-- `TreeBorrowsMemory::leak_check` is `BasicMemory::leak_check` of the
wrapped memory: borrow trees and protectors play no role. -/
theorem tb_leak_check_eq (tbm : TBM) :
    TreeBorrowsMemory.leak_check tbm = BasicMemory.leak_check tbm.mem := rfl

/-- `TreeBorrowsMemory::leak_check` reports `MemoryLeak` exactly when a live
`Heap` allocation exists. -/
theorem tb_leak_check_error_iff (tbm : TBM) (e : Stop) :
    TreeBorrowsMemory.leak_check tbm = .error e ↔
      e = .memoryLeak ∧ ∃ a ∈ tbm.mem.allocations, a.live = true ∧ a.kind = .Heap :=
  basicMemory_leak_check_error_iff tbm.mem e

/-- `TreeBorrowsMemory::leak_check` passes exactly when no live allocation is
a `Heap` allocation. -/
theorem tb_leak_check_ok_iff (tbm : TBM) :
    TreeBorrowsMemory.leak_check tbm = .ok () ↔
      ∀ a ∈ tbm.mem.allocations, a.live = true → a.kind ≠ .Heap :=
  basicMemory_leak_check_ok_iff tbm.mem

/-- `ConcurrentMemory::leak_check` over `BasicMemory<x86_64>` reports
`MemoryLeak` exactly when a live `Heap` allocation exists. -/
theorem cm_leak_check_bm_error_iff (cm : ConcurrentMemory BM) (e : Stop) :
    ConcurrentMemory.leak_check cm = .error e ↔
      e = .memoryLeak ∧ ∃ a ∈ cm.memory.allocations, a.live = true ∧ a.kind = .Heap :=
  basicMemory_leak_check_error_iff cm.memory e

/-- `ConcurrentMemory::leak_check` over `BasicMemory<x86_64>` passes exactly
when no live allocation is a `Heap` allocation. -/
theorem cm_leak_check_bm_ok_iff (cm : ConcurrentMemory BM) :
    ConcurrentMemory.leak_check cm = .ok () ↔
      ∀ a ∈ cm.memory.allocations, a.live = true → a.kind ≠ .Heap :=
  basicMemory_leak_check_ok_iff cm.memory

/-- `ConcurrentMemory::leak_check` over `TreeBorrowsMemory<x86_64>` reports
`MemoryLeak` exactly when a live `Heap` allocation exists. -/
theorem cm_leak_check_tb_error_iff (cm : ConcurrentMemory TBM) (e : Stop) :
    ConcurrentMemory.leak_check cm = .error e ↔
      e = .memoryLeak ∧ ∃ a ∈ cm.memory.mem.allocations, a.live = true ∧ a.kind = .Heap :=
  basicMemory_leak_check_error_iff cm.memory.mem e

/-- `ConcurrentMemory::leak_check` over `TreeBorrowsMemory<x86_64>` passes
exactly when no live allocation is a `Heap` allocation. -/
theorem cm_leak_check_tb_ok_iff (cm : ConcurrentMemory TBM) :
    ConcurrentMemory.leak_check cm = .ok () ↔
      ∀ a ∈ cm.memory.mem.allocations, a.live = true → a.kind ≠ .Heap :=
  basicMemory_leak_check_ok_iff cm.memory.mem

/-- The `BasicMemory<x86_64>` transcription `CM.leak_check` agrees. -/
theorem cm_leak_check_error_iff (cm : ConcurrentMemory BM) (e : Stop) :
    CM.leak_check cm = .error e ↔
      e = .memoryLeak ∧ ∃ a ∈ cm.memory.allocations, a.live = true ∧ a.kind = .Heap := by
  rw [← cm_leak_check_bm_eq]
  exact cm_leak_check_bm_error_iff cm e


/-! ### The heap lifecycle, universally

What the threaded trace `mrHeapLifecycleTrace` shows on one machine holds on
every `BasicMemory`: a fresh `Heap` allocation is live, so `leak_check`
reports it; deallocating it with the size, alignment, and kind it was
allocated with passes every check of `BasicMemory::deallocate`; afterwards
`leak_check` is back to what it was before the allocation; and a second
deallocation is a double-free. -/

section HeapLifecycle

variable {ProvExtra AllocExtra : Type}

/-- The allocation record `BasicMemory::allocate` appends. -/
def freshAllocation (addr : Int) (kind : AllocationKind) (size : Size) (align : Align)
    (live : Bool) (extra : AllocExtra) : Allocation ProvExtra AllocExtra :=
  { addr := addr, align := align, kind := kind, live := live,
    data := List.replicate size.bytes .Uninit, extra := extra }

/-- `Allocation::size` of a fresh allocation is the requested size. -/
theorem freshAllocation_size (addr : Int) (kind : AllocationKind) (size : Size) (align : Align)
    (live : Bool) (extra : AllocExtra) :
    Allocation.size (freshAllocation (ProvExtra := ProvExtra) addr kind size align live extra) =
      size := by
  cases size
  simp only [Allocation.size, freshAllocation, List.length_replicate]

/-- **Deallocating what was just allocated succeeds**, for every memory, kind,
size, alignment, and every `handle_extra` that accepts the fresh extra: the
pointer `BasicMemory::allocate` returned passes every check of
`BasicMemory::deallocate` with the same kind, size, and alignment, and the
allocation is marked dead in place. -/
theorem basicMemory_allocate_then_deallocate
    {mem mem' : BasicMemory x86_64 ProvExtra AllocExtra} {kind : AllocationKind} {size : Size}
    {align : Align} {provExtra : ProvExtra} {allocExtra extra' : AllocExtra}
    {ptr : ThinPointer (Provenance ProvExtra)}
    (handleExtra : AllocExtra → ProvExtra → Interp AllocExtra)
    (h : BasicMemory.allocate mem kind size align provExtra allocExtra = .ok (ptr, mem'))
    (hh : handleExtra allocExtra provExtra = .ok extra') :
    ∃ addr, ptr.addr = addr ∧
      mem' = { mem with allocations :=
        mem.allocations ++ [freshAllocation addr kind size align true allocExtra] } ∧
      BasicMemory.deallocate mem' ptr kind size align handleExtra =
        .ok { mem with allocations :=
          mem.allocations ++ [freshAllocation addr kind size align false extra'] } := by
  obtain ⟨_, addr, _, rfl, rfl⟩ :=
    (basicMemory_allocate_ok_iff mem mem' kind size align provExtra allocExtra ptr).mp h
  refine ⟨addr, rfl, rfl, ?_⟩
  rw [(basicMemory_deallocate_ok_iff _ _ _ kind size align handleExtra).mpr
    ⟨⟨mem.allocations.length⟩, provExtra, freshAllocation addr kind size align true allocExtra,
      extra', rfl, Int.natCast_nonneg _, ?_, rfl, rfl, rfl,
      (freshAllocation_size addr kind size align true allocExtra).symm, rfl, hh, rfl⟩]
  · simp only [Int.toNat_natCast, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self,
      List.set_cons_zero]
    rfl
  · simp only [Int.toNat_natCast, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero]
    rfl

/-- A second deallocation of the same pointer is a double-free. -/
theorem basicMemory_deallocate_twice_double_free
    {mem mem' : BasicMemory x86_64 ProvExtra AllocExtra} {kind : AllocationKind} {size : Size}
    {align : Align} {provExtra : ProvExtra} {allocExtra extra' : AllocExtra}
    {ptr : ThinPointer (Provenance ProvExtra)}
    (handleExtra : AllocExtra → ProvExtra → Interp AllocExtra)
    (h : BasicMemory.allocate mem kind size align provExtra allocExtra = .ok (ptr, mem'))
    (hh : handleExtra allocExtra provExtra = .ok extra')
    (kind' : AllocationKind) (size' : Size) (align' : Align) :
    ∃ mem'', BasicMemory.deallocate mem' ptr kind size align handleExtra = .ok mem'' ∧
      BasicMemory.deallocate mem'' ptr kind' size' align' handleExtra = .error (.ub "double-free") := by
  obtain ⟨addr, haddr, rfl, hd⟩ := basicMemory_allocate_then_deallocate handleExtra h hh
  obtain ⟨_, _, _, hp, _⟩ :=
    (basicMemory_allocate_ok_iff mem _ kind size align provExtra allocExtra ptr).mp h
  refine ⟨_, hd, ?_⟩
  refine basicMemory_deallocate_double_free_ub _ ptr kind' size' align' handleExtra
    ⟨mem.allocations.length⟩ provExtra (freshAllocation addr kind size align false extra')
    (by rw [hp]) ?_ rfl
  rw [listIndex_eq_ok_iff]
  refine ⟨Int.natCast_nonneg _, ?_⟩
  simp only [Int.toNat_natCast, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem?_cons_zero]

/-- A fresh `Heap` allocation makes `leak_check` report `MemoryLeak`, whatever
memory it was allocated in. -/
theorem basicMemory_allocate_heap_leaks
    {mem mem' : BasicMemory x86_64 ProvExtra AllocExtra} {size : Size} {align : Align}
    {provExtra : ProvExtra} {allocExtra : AllocExtra} {ptr : ThinPointer (Provenance ProvExtra)}
    (h : BasicMemory.allocate mem .Heap size align provExtra allocExtra = .ok (ptr, mem')) :
    BasicMemory.leak_check mem' = .error .memoryLeak := by
  obtain ⟨_, addr, _, _, rfl⟩ :=
    (basicMemory_allocate_ok_iff mem mem' .Heap size align provExtra allocExtra ptr).mp h
  rw [basicMemory_leak_check_error_iff]
  exact ⟨rfl, freshAllocation addr .Heap size align true allocExtra,
    List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl⟩

/-- After allocating and deallocating a block, `leak_check` gives exactly
what it gave before the allocation: the dead record is ignored. -/
theorem basicMemory_allocate_deallocate_leak_check
    {mem mem' : BasicMemory x86_64 ProvExtra AllocExtra} {kind : AllocationKind} {size : Size}
    {align : Align} {provExtra : ProvExtra} {allocExtra extra' : AllocExtra}
    {ptr : ThinPointer (Provenance ProvExtra)}
    (handleExtra : AllocExtra → ProvExtra → Interp AllocExtra)
    (h : BasicMemory.allocate mem kind size align provExtra allocExtra = .ok (ptr, mem'))
    (hh : handleExtra allocExtra provExtra = .ok extra') :
    ∃ mem'', BasicMemory.deallocate mem' ptr kind size align handleExtra = .ok mem'' ∧
      BasicMemory.leak_check mem'' = BasicMemory.leak_check mem := by
  obtain ⟨addr, _, rfl, hd⟩ := basicMemory_allocate_then_deallocate handleExtra h hh
  refine ⟨_, hd, ?_⟩
  unfold BasicMemory.leak_check
  simp only [List.any_append, List.any_cons, List.any_nil, freshAllocation, Bool.false_and,
    Bool.or_false]

end HeapLifecycle

/-- `ConcurrentMemory::allocate` over `BasicMemory<x86_64>` is the polymorphic
`BasicMemory::allocate` on the wrapped memory. -/
theorem cm_allocate_bm_basic (cm : ConcurrentMemory BM) (kind : AllocationKind) (size : Size)
    (align : Align) :
    ConcurrentMemory.allocate (M := BM) cm kind size align =
      (do
        let (ptr, mem) ← BasicMemory.allocate cm.memory kind size align () ()
        pure (ptr, { cm with memory := mem })) := by
  rw [cm_allocate_bm_eq]
  unfold CM.allocate
  rw [bm_allocate_eq_basic]

/-- `ConcurrentMemory::deallocate` over `BasicMemory<x86_64>` is the
polymorphic `BasicMemory::deallocate` with the trivial `handle_extra`. -/
theorem cm_deallocate_bm_basic (cm : ConcurrentMemory BM) (ptr : Ptr) (kind : AllocationKind)
    (size : Size) (align : Align) :
    ConcurrentMemory.deallocate (M := BM) cm ptr kind size align =
      (do
        let mem ← BasicMemory.deallocate cm.memory ptr kind size align (fun extra _ => pure extra)
        pure { cm with memory := mem }) := by
  rw [cm_deallocate_bm_eq]
  unfold CM.deallocate
  rw [bm_deallocate_eq_basic]

/-- **The heap lifecycle on every `Mach`.** Whenever `Allocate(size, align)`
succeeds at a thin pointer type on a `Machine<BasicMemory<x86_64>>`, the new
machine reports a leak; `Deallocate(ptr, size, align)` of the returned
pointer succeeds; the machine after it passes `leak_check` exactly when the
machine before the allocation did; and a second `Deallocate` of the same
pointer is UB `"double-free"`. -/
theorem heap_lifecycle_bm (m m1 : Mach) (size align : Int) (sTy aTy : «Type») (p : PtrType)
    (val : Val) (pTy : «Type»)
    (h : evalIntrinsicM m .Allocate [(.Int size, sTy), (.Int align, aTy)] (.Ptr p) =
      .ok (val, m1)) :
    ∃ ptr m2, val = .Ptr ⟨ptr, none⟩ ∧
      ConcurrentMemory.leak_check m1.mem = .error .memoryLeak ∧
      evalIntrinsicM m1 .Deallocate [(.Ptr ⟨ptr, none⟩, pTy), (.Int size, sTy), (.Int align, aTy)]
        unitType = .ok (unitValueM, m2) ∧
      ConcurrentMemory.leak_check m2.mem = ConcurrentMemory.leak_check m.mem ∧
      evalIntrinsicM m2 .Deallocate [(.Ptr ⟨ptr, none⟩, pTy), (.Int size, sTy), (.Int align, aTy)]
        unitType = .error (.ub "double-free") := by
  obtain ⟨size', sTy', align', aTy', al, p', ptr, cm, hargs, hs, ha, hret, hk, hal, hval, hm1⟩ :=
    allocate_ok_iff.mp h
  have hsz : size' = size := by cases hargs; rfl
  have hag : align' = align := by cases hargs; rfl
  subst hsz hag hval hm1
  rw [cm_allocate_bm_basic] at hal
  obtain ⟨⟨ptr', mem1⟩, halloc, hp'⟩ := interp_bind_eq_ok hal
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok hp')
  obtain ⟨mem2, hd, hd2⟩ := basicMemory_deallocate_twice_double_free (fun extra _ => pure extra)
    halloc rfl .Heap ⟨size'.toNat⟩ al
  obtain ⟨mem2', hd', hleak⟩ := basicMemory_allocate_deallocate_leak_check
    (fun extra _ => pure extra) halloc rfl
  rw [hd] at hd'
  cases hd'
  refine ⟨ptr', { m with mem := { m.mem with memory := mem2 } }, rfl, ?_, ?_, ?_, ?_⟩
  · exact basicMemory_allocate_heap_leaks halloc
  · rw [deallocate_eq_memory (M := BM) _ ptr' pTy size' sTy align' aTy al hs ha,
      cm_deallocate_bm_basic]
    simp only [hd]
    rfl
  · exact hleak
  · rw [deallocate_eq_memory (M := BM) _ ptr' pTy size' sTy align' aTy al hs ha,
      cm_deallocate_bm_basic]
    simp only [hd2]
    rfl

/-! ### The heap lifecycle on `TreeBorrowsMemory` / `MachTB`, universally -/

/-- Setting an element of `List.replicate n x` to `x` leaves the list unchanged. -/
theorem list_set_replicate_same {α : Type} :
    ∀ (n : Nat) (x : α) (i : Nat), (List.replicate n x).set i x = List.replicate n x
  | 0, _, _ => rfl
  | _ + 1, _, 0 => rfl
  | n + 1, x, i + 1 => congrArg (x :: ·) (list_set_replicate_same n x i)

/-- A local write over any valid subrange of a freshly allocated all-`Unique`
unprotected permission vector leaves every byte `.Unprot .Unique`. -/
theorem node_transitionRange_local_write_unique (total : Nat) :
    ∀ (rem offset : Nat), offset + rem ≤ total →
      Node.transitionRange .Local .Write offset rem
          (List.replicate total (.Unprot .Unique)) =
        .ok (List.replicate total (.Unprot .Unique))
  | 0, _, _ => rfl
  | rem + 1, offset, hle => by
    have hlt : offset < total := by omega
    have hidx : listIndex (List.replicate total (Permission.Unprot .Unique)) (Int.ofNat offset)
        "Node::transition" = .ok (Permission.Unprot .Unique) := by
      rw [listIndex_eq_ok_iff]
      refine ⟨Int.natCast_nonneg _, ?_⟩
      simp only [Int.ofNat_eq_natCast, Int.toNat_natCast, List.getElem?_replicate, hlt, ↓reduceIte]
    have hset : listSet (List.replicate total (Permission.Unprot .Unique)) (Int.ofNat offset)
        (Permission.Unprot .Unique) "Node::transition" =
        .ok (List.replicate total (Permission.Unprot .Unique)) := by
      unfold listSet
      simp only [Int.ofNat_eq_natCast, Int.toNat_natCast, List.length_replicate,
        Int.natCast_nonneg, hlt, and_self, ↓reduceIte, list_set_replicate_same]
      rfl
    have htr : Permission.transition (.Unprot .Unique) .Write .Local = .ok (.Unprot .Unique) := rfl
    unfold Node.transitionRange listMutateAt
    simp only [hidx, htr, hset, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
    exact node_transitionRange_local_write_unique total rem (offset + 1) (by omega)

/-- `Node::access` with a local write on the fresh unprotected all-`Unique` root
tree created by `TreeBorrowsMemory::allocate` succeeds for **every** `size : Size`
and preserves the root node. -/
theorem node_access_write_fresh_root (size : Size) :
    Node.access ⟨[], List.replicate size.bytes (.Unprot .Unique), .No⟩ (some []) .Write ⟨0⟩ size =
      .ok ⟨[], List.replicate size.bytes (.Unprot .Unique), .No⟩ := by
  simp only [Node.access, Node.transition, Option.isSome, ↓reduceIte,
    node_transitionRange_local_write_unique size.bytes size.bytes 0
      (Nat.le_of_eq (Nat.zero_add _))]
  rfl

/-- `tbDeallocHandler` succeeds on a freshly allocated root tree for every
`size : Size`, because the local write passes and the unprotected leaf has no
strong protector. -/
theorem tbDeallocHandler_fresh_root (size : Size) :
    tbDeallocHandler size ⟨⟨[], List.replicate size.bytes (.Unprot .Unique), .No⟩⟩ [] =
      .ok ⟨⟨[], List.replicate size.bytes (.Unprot .Unique), .No⟩⟩ := by
  unfold tbDeallocHandler
  rw [node_access_write_fresh_root size]
  rfl

/-- **Deallocating what was just allocated succeeds on `TreeBorrowsMemory`**, for
every `tbm : TBM`, every `kind`, `size`, and `align`. -/
theorem tb_allocate_then_deallocate {tbm tbm' : TBM} {kind : AllocationKind} {size : Size}
    {align : Align} {ptr : ThinPointer TreeBorrowsProvenance}
    (h : TreeBorrowsMemory.allocate tbm kind size align = .ok (ptr, tbm')) :
    ∃ addr, ptr.addr = addr ∧
      tbm' = { tbm with mem := { tbm.mem with allocations :=
        tbm.mem.allocations ++ [freshAllocation addr kind size align true
          ⟨⟨[], List.replicate size.bytes (.Unprot .Unique), .No⟩⟩] } } ∧
      TreeBorrowsMemory.deallocate tbm' ptr kind size align =
        .ok { tbm with mem := { tbm.mem with allocations :=
          tbm.mem.allocations ++ [freshAllocation addr kind size align false
            ⟨⟨[], List.replicate size.bytes (.Unprot .Unique), .No⟩⟩] } } := by
  unfold TreeBorrowsMemory.allocate at h
  obtain ⟨⟨ptr', mem'⟩, halloc, hp⟩ := interp_bind_eq_ok h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok hp)
  obtain ⟨addr, haddr, hmem', hd⟩ :=
    basicMemory_allocate_then_deallocate (tbDeallocHandler size) halloc (tbDeallocHandler_fresh_root size)
  refine ⟨addr, haddr, by rw [hmem'], ?_⟩
  rw [tb_deallocate_eq_basic]
  simp only [hd]
  rfl

/-- A second `TreeBorrowsMemory::deallocate` of the same pointer is `"double-free"`. -/
theorem tb_deallocate_twice_double_free {tbm tbm' : TBM} {kind : AllocationKind} {size : Size}
    {align : Align} {ptr : ThinPointer TreeBorrowsProvenance}
    (h : TreeBorrowsMemory.allocate tbm kind size align = .ok (ptr, tbm'))
    (kind' : AllocationKind) (size' : Size) (align' : Align) :
    ∃ tbm'', TreeBorrowsMemory.deallocate tbm' ptr kind size align = .ok tbm'' ∧
      TreeBorrowsMemory.deallocate tbm'' ptr kind' size' align' = .error (.ub "double-free") := by
  unfold TreeBorrowsMemory.allocate at h
  obtain ⟨⟨ptr', mem'⟩, halloc, hp⟩ := interp_bind_eq_ok h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok hp)
  obtain ⟨mem'', hd, hd2⟩ :=
    basicMemory_deallocate_twice_double_free (tbDeallocHandler size) halloc
      (tbDeallocHandler_fresh_root size) kind' size' align'
  refine ⟨{ tbm with mem := mem'' }, ?_, ?_⟩
  · rw [tb_deallocate_eq_basic]; simp only [hd]; rfl
  · rw [tb_deallocate_eq_basic]
    have hd2' : BasicMemory.deallocate mem'' ptr' kind' size' align' (tbDeallocHandler size') =
        .error (.ub "double-free") := by
      obtain ⟨addr, _, rfl, hd'⟩ :=
        basicMemory_allocate_then_deallocate (tbDeallocHandler size) halloc
          (tbDeallocHandler_fresh_root size)
      rw [hd'] at hd
      cases hd
      obtain ⟨_, _, _, hptr, _⟩ :=
        (basicMemory_allocate_ok_iff tbm.mem _ kind size align [] _ ptr').mp halloc
      refine basicMemory_deallocate_double_free_ub _ ptr' kind' size' align' (tbDeallocHandler size')
        ⟨tbm.mem.allocations.length⟩ []
        (freshAllocation addr kind size align false
          ⟨⟨[], List.replicate size.bytes (.Unprot .Unique), .No⟩⟩) (by rw [hptr]) ?_ rfl
      rw [listIndex_eq_ok_iff]
      refine ⟨Int.natCast_nonneg _, ?_⟩
      simp only [Int.toNat_natCast, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_cons_zero]
    simp only [hd2']
    rfl

/-- A fresh `Heap` allocation on `TreeBorrowsMemory` makes `leak_check` report
`MemoryLeak`, whatever memory it was allocated in. -/
theorem tb_allocate_heap_leaks {tbm tbm' : TBM} {size : Size} {align : Align}
    {ptr : ThinPointer TreeBorrowsProvenance}
    (h : TreeBorrowsMemory.allocate tbm .Heap size align = .ok (ptr, tbm')) :
    TreeBorrowsMemory.leak_check tbm' = .error .memoryLeak := by
  unfold TreeBorrowsMemory.allocate at h
  obtain ⟨⟨_, mem'⟩, halloc, hp⟩ := interp_bind_eq_ok h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok hp)
  exact basicMemory_allocate_heap_leaks halloc

/-- After allocating and deallocating a block on `TreeBorrowsMemory`,
`leak_check` returns to its pre-allocation result. -/
theorem tb_allocate_deallocate_leak_check {tbm tbm' : TBM} {kind : AllocationKind} {size : Size}
    {align : Align} {ptr : ThinPointer TreeBorrowsProvenance}
    (h : TreeBorrowsMemory.allocate tbm kind size align = .ok (ptr, tbm')) :
    ∃ tbm'', TreeBorrowsMemory.deallocate tbm' ptr kind size align = .ok tbm'' ∧
      TreeBorrowsMemory.leak_check tbm'' = TreeBorrowsMemory.leak_check tbm := by
  unfold TreeBorrowsMemory.allocate at h
  obtain ⟨⟨_, mem'⟩, halloc, hp⟩ := interp_bind_eq_ok h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok hp)
  obtain ⟨mem'', hd, hleak⟩ :=
    basicMemory_allocate_deallocate_leak_check (tbDeallocHandler size) halloc
      (tbDeallocHandler_fresh_root size)
  refine ⟨{ tbm with mem := mem'' }, ?_, hleak⟩
  rw [tb_deallocate_eq_basic]; simp only [hd]; rfl

/-- **The heap lifecycle on every `MachTB` (`TreeBorrowsMemory<x86_64>`).**
Whenever `Allocate(size, align)` succeeds at a thin pointer type on any `MachTB`,
the new machine reports a leak; `Deallocate(ptr, size, align)` succeeds (passing
`Node.access .Write` and the strong-protector check on the fresh root tree);
`leak_check` returns to its pre-allocation result; a second `Deallocate` is UB
`"double-free"`; and `MachTB.wfLive` is preserved across both transitions. -/
theorem heap_lifecycle_tb (m m1 : MachTB) (size align : Int) (sTy aTy : «Type») (p : PtrType)
    (val : Value TBM) (pTy : «Type»)
    (h : evalIntrinsicM m .Allocate [(.Int size, sTy), (.Int align, aTy)] (.Ptr p) =
      .ok (val, m1)) :
    ∃ ptr m2, val = .Ptr ⟨ptr, none⟩ ∧
      ConcurrentMemory.leak_check m1.mem = .error .memoryLeak ∧
      evalIntrinsicM m1 .Deallocate [(.Ptr ⟨ptr, none⟩, pTy), (.Int size, sTy), (.Int align, aTy)]
        unitType = .ok (unitValueM, m2) ∧
      ConcurrentMemory.leak_check m2.mem = ConcurrentMemory.leak_check m.mem ∧
      evalIntrinsicM m2 .Deallocate [(.Ptr ⟨ptr, none⟩, pTy), (.Int size, sTy), (.Int align, aTy)]
        unitType = .error (.ub "double-free") ∧
      (MiniRustSpec.Correspondence.MachTB.wfLive m →
        MiniRustSpec.Correspondence.MachTB.wfLive m1 ∧
        MiniRustSpec.Correspondence.MachTB.wfLive m2) := by
  obtain ⟨size', sTy', align', aTy', al, p', ptr, cm, hargs, hs, ha, hret, hk, hal, hval, hm1⟩ :=
    allocate_ok_iff.mp h
  have hsz : size' = size := by cases hargs; rfl
  have hag : align' = align := by cases hargs; rfl
  subst hsz hag hval hm1
  rw [cm_allocate_tb_eq] at hal
  obtain ⟨⟨ptr', tbm1⟩, halloc, hp'⟩ := interp_bind_eq_ok hal
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok hp')
  obtain ⟨tbm2, hd, hd2⟩ := tb_deallocate_twice_double_free halloc .Heap ⟨size'.toNat⟩ al
  obtain ⟨tbm2', hd', hleak⟩ := tb_allocate_deallocate_leak_check halloc
  rw [hd] at hd'
  cases hd'
  have hdealloc : evalIntrinsicM { m with mem := { m.mem with memory := tbm1 } } .Deallocate
      [(.Ptr ⟨ptr', none⟩, pTy), (.Int size', sTy), (.Int align', aTy)] unitType =
      .ok (unitValueM, { m with mem := { m.mem with memory := tbm2 } }) := by
    rw [deallocate_eq_memory (M := TBM) _ ptr' pTy size' sTy align' aTy al hs ha, cm_deallocate_tb_eq]
    simp only [hd]
    rfl
  refine ⟨ptr', { m with mem := { m.mem with memory := tbm2 } }, rfl, ?_, hdealloc, ?_, ?_, ?_⟩
  · exact tb_allocate_heap_leaks halloc
  · exact hleak
  · rw [deallocate_eq_memory (M := TBM) _ ptr' pTy size' sTy align' aTy al hs ha, cm_deallocate_tb_eq]
    simp only [hd2]
    rfl
  · intro hwf
    have hwf1 := evalIntrinsicM_allocate_tb_wfLive hwf h
    exact ⟨hwf1, evalIntrinsicM_deallocate_tb_wfLive hwf1 hdealloc⟩

/-! ## §4. `ptr::addr_eq` against `==` on wide pointers

`core::ptr::addr_eq(p, q)` is `p.cast::<()>() == q.cast::<()>()`: both
pointers are made thin (`UnOp::GetThinPointer`) and then compared
(`BinOp::Rel(Eq)`, `Machine::compare_ptr`). `p == q` compares the wide
pointers as they are. -/

section WidePointers

variable {M : Type} [Memory M] [MemoryOps M]

/-- `ptr::addr_eq`: `GetThinPointer` on both operands, then `BinOp::Rel(Eq)`. -/
def evalAddrEqM (l r : Value M × «Type») : Interp (Value M × «Type») := do
  let l' ← evalUnOpM .GetThinPointer l
  let r' ← evalUnOpM .GetThinPointer r
  evalBinOpM (.Rel .Eq) l' r'

/-- `==` on the operands as they are: `BinOp::Rel(Eq)`. -/
def evalWideEqM (l r : Value M × «Type») : Interp (Value M × «Type») :=
  evalBinOpM (.Rel .Eq) l r

/-- `Ordering::then(Equal)` after an integer comparison is equality. -/
theorem intCmp_then_eq_isEq (a b : Int) : ((intCmp a b).then .eq).isEq = decide (a = b) := by
  unfold intCmp
  by_cases hlt : a < b
  · have hne : a ≠ b := Int.ne_of_lt hlt
    simp only [hlt, ↓reduceIte, hne, decide_false]
    rfl
  · by_cases heq : a = b
    · subst heq
      simp only [Int.lt_irrefl, ↓reduceIte, decide_true]
      rfl
    · simp only [hlt, ↓reduceIte, heq, decide_false]
      rfl

/-- Lexicographic comparison of two integer pairs is equality of both. -/
theorem intCmp_then_isEq (a b c d : Int) :
    ((intCmp a b).then (intCmp c d)).isEq = decide (a = b ∧ c = d) := by
  unfold intCmp
  by_cases hlt : a < b
  · have hne : a ≠ b := Int.ne_of_lt hlt
    simp only [hlt, ↓reduceIte, hne, false_and, decide_false]
    rfl
  · by_cases heq : a = b
    · subst heq
      simp only [Int.lt_irrefl, ↓reduceIte, true_and]
      by_cases hlt' : c < d
      · have hne' : c ≠ d := Int.ne_of_lt hlt'
        simp only [hlt', ↓reduceIte, hne', decide_false]
        rfl
      · by_cases heq' : c = d
        · subst heq'
          simp only [Int.lt_irrefl, ↓reduceIte, decide_true]
          rfl
        · simp only [hlt', ↓reduceIte, heq', decide_false]
          rfl
    · simp only [hlt, ↓reduceIte, heq, false_and, decide_false]
      rfl

/-- `GetThinPointer` erases the metadata of a pointer and keeps its thin
pointer, address and provenance. -/
theorem getThinPointer_ptr (p : Pointer (Memory.Provenance M)) (ty : «Type») :
    evalUnOpM (M := M) .GetThinPointer (.Ptr p, ty) =
      .ok (.Ptr { p with metadata := none }, .Ptr (.Raw .None)) := rfl

/-- `GetThinPointer` of anything but a pointer is a specification panic. -/
theorem getThinPointer_non_ptr (v : Value M) (ty : «Type») (h : ∀ p, v ≠ .Ptr p) :
    evalUnOpM (M := M) .GetThinPointer (v, ty) = .error (.specPanic "non-pointer GetThinPointer") := by
  cases v with
  | Ptr p => exact absurd rfl (h p)
  | _ => rfl

/-- **`ptr::addr_eq` compares addresses only.** For every pair of pointers,
whatever their metadata (none, slice length, vtable) and whatever their
provenance, `addr_eq` succeeds and returns whether the addresses are equal. -/
theorem evalAddrEqM_ptr (pl pr : Pointer (Memory.Provenance M)) (tl tr : «Type») :
    evalAddrEqM (M := M) (.Ptr pl, tl) (.Ptr pr, tr) =
      .ok (.Bool (decide (pl.thin_pointer.addr = pr.thin_pointer.addr)), .Bool) := by
  have h : evalAddrEqM (M := M) (.Ptr pl, tl) (.Ptr pr, tr) =
      .ok (.Bool ((intCmp pl.thin_pointer.addr pr.thin_pointer.addr).then .eq).isEq, .Bool) := rfl
  rw [h, intCmp_then_eq_isEq]

/-- `addr_eq` does not depend on metadata: replacing the metadata of either
pointer changes nothing. -/
theorem evalAddrEqM_metadata_irrelevant (tl tr : ThinPointer (Memory.Provenance M))
    (ml ml' mr mr' : Option (PointerMeta (Memory.Provenance M))) (tyl tyr tyl' tyr' : «Type») :
    evalAddrEqM (M := M) (.Ptr ⟨tl, ml⟩, tyl) (.Ptr ⟨tr, mr⟩, tyr) =
      evalAddrEqM (M := M) (.Ptr ⟨tl, ml'⟩, tyl') (.Ptr ⟨tr, mr'⟩, tyr') := by
  rw [evalAddrEqM_ptr, evalAddrEqM_ptr]

/-- `addr_eq` does not depend on provenance: pointers at the same address
compare equal even with different (or no) provenance. -/
theorem evalAddrEqM_same_addr (addr : Int) (provL provR : Option (Memory.Provenance M))
    (ml mr : Option (PointerMeta (Memory.Provenance M))) (tyl tyr : «Type») :
    evalAddrEqM (M := M) (.Ptr ⟨⟨addr, provL⟩, ml⟩, tyl) (.Ptr ⟨⟨addr, provR⟩, mr⟩, tyr) =
      .ok (.Bool true, .Bool) := by
  rw [evalAddrEqM_ptr]
  simp only [decide_true]

omit [MemoryOps M] in
/-- `==` on thin pointers compares addresses, ignoring provenance. -/
theorem evalWideEqM_thin (tl tr : ThinPointer (Memory.Provenance M)) (pty : PtrType)
    (tyr : «Type») :
    evalWideEqM (M := M) (.Ptr ⟨tl, none⟩, .Ptr pty) (.Ptr ⟨tr, none⟩, tyr) =
      .ok (.Bool (decide (tl.addr = tr.addr)), .Bool) := by
  have h : evalWideEqM (M := M) (.Ptr ⟨tl, none⟩, .Ptr pty) (.Ptr ⟨tr, none⟩, tyr) =
      .ok (.Bool ((intCmp tl.addr tr.addr).then .eq).isEq, .Bool) := rfl
  rw [h, intCmp_then_eq_isEq]

omit [MemoryOps M] in
/-- `==` on slice pointers compares the address *and* the element count. -/
theorem evalWideEqM_slice (tl tr : ThinPointer (Memory.Provenance M)) (l r : Int)
    (pty : PtrType) (tyr : «Type») :
    evalWideEqM (M := M) (.Ptr ⟨tl, some (.ElementCount l)⟩, .Ptr pty)
        (.Ptr ⟨tr, some (.ElementCount r)⟩, tyr) =
      .ok (.Bool (decide (tl.addr = tr.addr ∧ l = r)), .Bool) := by
  have h : evalWideEqM (M := M) (.Ptr ⟨tl, some (.ElementCount l)⟩, .Ptr pty)
      (.Ptr ⟨tr, some (.ElementCount r)⟩, tyr) =
      .ok (.Bool ((intCmp tl.addr tr.addr).then (intCmp l r)).isEq, .Bool) := rfl
  rw [h, intCmp_then_isEq]

omit [MemoryOps M] in
/-- `==` on trait-object pointers compares the address *and* the vtable
address (ignoring both provenances). -/
theorem evalWideEqM_vtable (tl tr vl vr : ThinPointer (Memory.Provenance M))
    (pty : PtrType) (tyr : «Type») :
    evalWideEqM (M := M) (.Ptr ⟨tl, some (.VTablePointer vl)⟩, .Ptr pty)
        (.Ptr ⟨tr, some (.VTablePointer vr)⟩, tyr) =
      .ok (.Bool (decide (tl.addr = tr.addr ∧ vl.addr = vr.addr)), .Bool) := by
  have h : evalWideEqM (M := M) (.Ptr ⟨tl, some (.VTablePointer vl)⟩, .Ptr pty)
      (.Ptr ⟨tr, some (.VTablePointer vr)⟩, tyr) =
      .ok (.Bool ((intCmp tl.addr tr.addr).then (intCmp vl.addr vr.addr)).isEq, .Bool) := rfl
  rw [h, intCmp_then_isEq]

omit [MemoryOps M] in
/-- `==` on a slice pointer and a trait-object pointer is a specification
panic: `compare_ptr` has no case for mismatched metadata kinds. `addr_eq` on
the same operands is defined (`evalAddrEqM_ptr`). -/
theorem evalWideEqM_mixed_specPanic (tl tr v : ThinPointer (Memory.Provenance M)) (n : Int)
    (pty : PtrType) (tyr : «Type») :
    evalWideEqM (M := M) (.Ptr ⟨tl, some (.ElementCount n)⟩, .Ptr pty)
        (.Ptr ⟨tr, some (.VTablePointer v)⟩, tyr) =
      .error (.specPanic "unmatching metadata in wide pointer comparasion") ∧
    evalWideEqM (M := M) (.Ptr ⟨tr, some (.VTablePointer v)⟩, .Ptr pty)
        (.Ptr ⟨tl, some (.ElementCount n)⟩, tyr) =
      .error (.specPanic "unmatching metadata in wide pointer comparasion") := ⟨rfl, rfl⟩

omit [MemoryOps M] in
/-- `==` on a thin pointer and a wide pointer is a specification panic too. -/
theorem evalWideEqM_thin_wide_specPanic (tl tr : ThinPointer (Memory.Provenance M))
    (ptrMeta : PointerMeta (Memory.Provenance M)) (pty : PtrType) (tyr : «Type») :
    evalWideEqM (M := M) (.Ptr ⟨tl, none⟩, .Ptr pty) (.Ptr ⟨tr, some ptrMeta⟩, tyr) =
      .error (.specPanic "unmatching metadata in wide pointer comparasion") ∧
    evalWideEqM (M := M) (.Ptr ⟨tr, some ptrMeta⟩, .Ptr pty) (.Ptr ⟨tl, none⟩, tyr) =
      .error (.specPanic "unmatching metadata in wide pointer comparasion") := by
  cases ptrMeta <;> exact ⟨rfl, rfl⟩

/-- `addr_eq` and `==` separated on slices: two slice pointers at the same
address with different lengths are `addr_eq` and not `==`. -/
theorem addrEq_true_wideEq_false_slice (t : ThinPointer (Memory.Provenance M)) (l r : Int)
    (hne : l ≠ r) (pty : PtrType) (tyr : «Type») :
    evalAddrEqM (M := M) (.Ptr ⟨t, some (.ElementCount l)⟩, .Ptr pty)
        (.Ptr ⟨t, some (.ElementCount r)⟩, tyr) = .ok (.Bool true, .Bool) ∧
    evalWideEqM (M := M) (.Ptr ⟨t, some (.ElementCount l)⟩, .Ptr pty)
        (.Ptr ⟨t, some (.ElementCount r)⟩, tyr) = .ok (.Bool false, .Bool) := by
  refine ⟨?_, ?_⟩
  · rw [evalAddrEqM_ptr]
    simp only [decide_true]
  · rw [evalWideEqM_slice]
    simp only [hne, and_false, decide_false]

/-- `addr_eq` and `==` separated on trait-object pointers: two `dyn Trait`
pointers at the same address with distinct vtable addresses are `addr_eq` and
not `==`. -/
theorem addrEq_true_wideEq_false_vtable (t vl vr : ThinPointer (Memory.Provenance M))
    (hne : vl.addr ≠ vr.addr) (pty : PtrType) (tyr : «Type») :
    evalAddrEqM (M := M) (.Ptr ⟨t, some (.VTablePointer vl)⟩, .Ptr pty)
        (.Ptr ⟨t, some (.VTablePointer vr)⟩, tyr) = .ok (.Bool true, .Bool) ∧
    evalWideEqM (M := M) (.Ptr ⟨t, some (.VTablePointer vl)⟩, .Ptr pty)
        (.Ptr ⟨t, some (.VTablePointer vr)⟩, tyr) = .ok (.Bool false, .Bool) := by
  refine ⟨?_, ?_⟩
  · rw [evalAddrEqM_ptr]
    simp only [decide_true]
  · rw [evalWideEqM_vtable]
    simp only [hne, and_false, decide_false]

omit [MemoryOps M] in
/-- `encodePtrBytesM` preserves list length. -/
theorem encodePtrBytesM_length (prov : Option (Memory.Provenance M)) :
    ∀ (idx : Nat) (bs : List UInt8), (encodePtrBytesM (M := M) prov idx bs).length = bs.length
  | _, [] => rfl
  | idx, _ :: rest => by
    simp only [encodePtrBytesM, List.length_cons, encodePtrBytesM_length prov (idx + 1) rest]

omit [MemoryOps M] in
/-- `leBytes u n` has exact length `n`. -/
theorem leBytes_length (u : Nat) : ∀ n : Nat, (leBytes u n).length = n
  | 0 => rfl
  | n + 1 => by simp only [leBytes, List.length_cons, leBytes_length (u / 256) n]

omit [MemoryOps M] in
/-- A successful `encodePtrM` always emits `x86_64.PTR_SIZE.bytes = 8` bytes. -/
theorem encodePtrM_length (thin : ThinPointer (Memory.Provenance M))
    (bs : List (AbstractByte (Memory.Provenance M)))
    (h : encodePtrM (M := M) thin = .ok bs) : bs.length = 8 := by
  unfold encodePtrM at h
  cases henc : Endianness.encode x86_64.ENDIANNESS .Unsigned x86_64.PTR_SIZE thin.addr with
  | none => rw [henc] at h; cases h
  | some data =>
    rw [henc] at h
    cases h
    rw [encodePtrBytesM_length]
    unfold Endianness.encode at henc
    by_cases hin : inBounds thin.addr .Unsigned x86_64.PTR_SIZE = true
    · rw [ite_eq_left hin] at henc
      cases henc
      exact leBytes_length _ 8
    · rw [ite_eq_right hin] at henc
      cases henc

omit [MemoryOps M] in
/-- The encoding of a slice pointer is the encoding of its thin pointer
followed by the encoding of its length: the first `PTR_SIZE` bytes, the ones
`addr_eq` compares after `GetThinPointer`, do not depend on the metadata. -/
theorem encodeWidePtrM_slice (thin : ThinPointer (Memory.Provenance M)) (n : Int) :
    encodeWidePtrM (M := M) .ElementCount ⟨thin, some (.ElementCount n)⟩ =
      (do
        let thinBytes ← encodePtrM (M := M) thin
        let metaBytes ← Type.encodeIntM (M := M) IntType.usize_ty (.Int n)
        pure (thinBytes ++ metaBytes)) := rfl

omit [MemoryOps M] in
/-- Universal metadata-prefix independence for slice pointers: whenever
`encodeWidePtrM` succeeds on a slice pointer, its first 8 bytes equal the
thin-pointer encoding `encodePtrM thin`, independent of the slice length `n`. -/
theorem encodeWidePtrM_slice_thin_prefix (thin : ThinPointer (Memory.Provenance M)) (n : Int)
    (bs : List (AbstractByte (Memory.Provenance M)))
    (h : encodeWidePtrM (M := M) .ElementCount ⟨thin, some (.ElementCount n)⟩ = .ok bs) :
    ∃ thinBytes, encodePtrM (M := M) thin = .ok thinBytes ∧ bs.take 8 = thinBytes := by
  rw [encodeWidePtrM_slice] at h
  obtain ⟨thinBytes, hthin, h⟩ := interp_bind_eq_ok h
  obtain ⟨metaBytes, _, h⟩ := interp_bind_eq_ok h
  obtain rfl := interp_pure_eq_ok h
  have hlen : thinBytes.length = 8 := encodePtrM_length thin thinBytes hthin
  refine ⟨thinBytes, hthin, ?_⟩
  rw [← hlen, List.take_left]

omit [MemoryOps M] in
/-- The encoding of a trait-object pointer is the encoding of its thin pointer
followed by the encoding of its vtable pointer. -/
theorem encodeWidePtrM_vtable (thin vtable : ThinPointer (Memory.Provenance M))
    (trait : TraitName) :
    encodeWidePtrM (M := M) (.VTablePointer trait) ⟨thin, some (.VTablePointer vtable)⟩ =
      (do
        let thinBytes ← encodePtrM (M := M) thin
        let metaBytes ← encodePtrM (M := M) vtable
        pure (thinBytes ++ metaBytes)) := rfl

omit [MemoryOps M] in
/-- Universal metadata-prefix independence for trait-object pointers: whenever
`encodeWidePtrM` succeeds on a `dyn Trait` pointer, its first 8 bytes equal the
thin-pointer encoding `encodePtrM thin`, independent of the vtable pointer. -/
theorem encodeWidePtrM_vtable_thin_prefix (thin vtable : ThinPointer (Memory.Provenance M))
    (trait : TraitName) (bs : List (AbstractByte (Memory.Provenance M)))
    (h : encodeWidePtrM (M := M) (.VTablePointer trait) ⟨thin, some (.VTablePointer vtable)⟩ =
      .ok bs) :
    ∃ thinBytes, encodePtrM (M := M) thin = .ok thinBytes ∧ bs.take 8 = thinBytes := by
  rw [encodeWidePtrM_vtable] at h
  obtain ⟨thinBytes, hthin, h⟩ := interp_bind_eq_ok h
  obtain ⟨metaBytes, _, h⟩ := interp_bind_eq_ok h
  obtain rfl := interp_pure_eq_ok h
  have hlen : thinBytes.length = 8 := encodePtrM_length thin thinBytes hthin
  refine ⟨thinBytes, hthin, ?_⟩
  rw [← hlen, List.take_left]

end WidePointers

/-- On `Mach`, the `BasicMemory` transcription `evalBinOp (.Rel .Eq)` agrees
with `evalWideEqM (M := BM)` on every pair of pointer operands. -/
theorem evalWideEq_bm (pl pr : Pointer Prov) (pty : PtrType) (tr : «Type») :
    evalBinOp (.Rel .Eq) (.Ptr pl, .Ptr pty) (.Ptr pr, tr) =
      evalWideEqM (M := BM) (.Ptr pl, .Ptr pty) (.Ptr pr, tr) := by
  rcases pl with ⟨tl, ml⟩
  rcases pr with ⟨trp, mr⟩
  rcases ml with _ | (l | vl) <;> rcases mr with _ | (r | vr) <;> rfl

/-- On `Mach`, the `BasicMemory` transcriptions `evalUnOp` and `evalBinOp`
compute the same `addr_eq`: addresses only. -/
theorem evalAddrEq_bm (pl pr : Pointer Prov) (tl tr : «Type») :
    (do
      let l' ← evalUnOp .GetThinPointer (.Ptr pl, tl)
      let r' ← evalUnOp .GetThinPointer (.Ptr pr, tr)
      evalBinOp (.Rel .Eq) l' r') =
      evalAddrEqM (M := BM) (.Ptr pl, tl) (.Ptr pr, tr) := by
  rw [evalAddrEqM_ptr]
  have h : (do
      let l' ← evalUnOp .GetThinPointer (.Ptr pl, tl)
      let r' ← evalUnOp .GetThinPointer (.Ptr pr, tr)
      evalBinOp (.Rel .Eq) l' r') =
      .ok (.Bool ((intCmp pl.thin_pointer.addr pr.thin_pointer.addr).then .eq).isEq, .Bool) := rfl
  rw [h, intCmp_then_eq_isEq]

/-! ## §5. Concrete machines: the 30-case observer and the threaded traces

Every statement of this section is a closed computation that the kernel
evaluates (`decide +kernel`, or `Eq.refl` through `kernel_rfl`). The scenarios
are written once, for every memory model, against `evalIntrinsicM`,
`typedStoreM`, `typedLoadM`, `ConcurrentMemory.{allocate, retag_ptr, end_call,
leak_check}`, `evalUnOpM`, and `evalBinOpM`; they are run on
`Machine<BasicMemory<x86_64>>` (`Mach`, `tb = false`) and on
`Machine<TreeBorrowsMemory<x86_64>>` (`MachTB`, `tb = true`). No scenario
inspects or builds a machine by hand: every machine below is reached from
`ConcurrentMemory::new` by the interpreted operations. -/

/-- What a scenario shows. -/
inductive MrHeapWideObs : Type where
  | okAlloc (sizeBytes : Nat) (alignBytes : Nat)
  | okRoundTrip (readBits : Nat)
  | okDealloc
  | okBool (val : Bool)
  | memoryLeak
  | ub
  | specPanic
  | invalidOrUnsupported
  deriving DecidableEq, Repr

/-- The `Stop` of an interpretation, if it stopped. -/
def stopOf {α : Type} : Interp α → Option Stop
  | .error s => some s
  | .ok _ => none

/-- The observation class of a `Stop`: UB, a specification panic, a memory
leak, or (for `abort`, `deadlock`, `unsupported`, and `machineStop`, none of
which a heap or comparison scenario is expected to reach) invalid or
unsupported. -/
def obsOfStop : Stop → MrHeapWideObs
  | .ub _ => .ub
  | .specPanic _ => .specPanic
  | .memoryLeak => .memoryLeak
  | .abort => .invalidOrUnsupported
  | .deadlock => .invalidOrUnsupported
  | .unsupported _ => .invalidOrUnsupported
  | .machineStop => .invalidOrUnsupported

/-- The observation of a scenario: its result, or the class of its `Stop`. -/
def observe (r : Interp MrHeapWideObs) : MrHeapWideObs :=
  match r with
  | .ok o => o
  | .error s => obsOfStop s

/-- A read-only view of one allocation record, for observing what `Allocate`
created. -/
structure AllocView where
  /-- `Allocation::size` in bytes. -/
  size : Nat
  /-- The alignment the allocation was requested with, in bytes. -/
  align : Nat
  /-- Whether the allocation is live. -/
  live : Bool
  /-- The allocation's kind. -/
  kind : AllocationKind
  /-- The allocation's base address. -/
  addr : Int

section Machines

variable {M : Type} [Memory M] [MemoryOps M]

/-- What the scenarios need from a memory model beyond `MemoryOps`. -/
structure Harness (M : Type) [Memory M] [MemoryOps M] where
  /-- The parameters `M::new` is called with. -/
  params : Memory.Params M
  /-- The allocation records of a memory, oldest first. -/
  view : M → List AllocView
  /-- A provenance for pointers that are compared, never dereferenced. -/
  provA : Memory.Provenance M
  /-- A second, different provenance. -/
  provB : Memory.Provenance M

/-- A program without functions. No heap intrinsic reads the program. -/
def emptyProg : Program :=
  { functions := ⟨[]⟩, start := ⟨⟨0⟩⟩, globals := ⟨[]⟩, traits := ⟨[]⟩, vtables := ⟨[]⟩ }

/-- The initial machine: `ConcurrentMemory::new`, no threads. -/
def initMach (H : Harness M) : Machine M :=
  { prog := emptyProg
    mem := ConcurrentMemory.new H.params
    intptrcast := ⟨⟨[]⟩⟩
    threads := []
    active_thread := 0
    synchronized_threads := ⟨[]⟩
    locks := []
    global_ptrs := ⟨[]⟩
    fn_ptrs := ⟨[]⟩
    vtable_ptrs := ⟨[]⟩
    stdout := ⟨[]⟩
    stderr := ⟨[]⟩ }

/-- `usize`. -/
@[reducible] def tyUsize : «Type» := .Int ⟨.Unsigned, ⟨8⟩⟩

/-- `u32`. -/
@[reducible] def itU32 : IntType := ⟨.Unsigned, ⟨4⟩⟩

/-- `u64`. -/
@[reducible] def itU64 : IntType := ⟨.Unsigned, ⟨8⟩⟩

/-- A thin raw pointer type. -/
@[reducible] def tyRawPtr : «Type» := .Ptr (.Raw .None)

/-- `Allocate(size, align)` at a thin raw pointer return type. -/
def allocM (m : Machine M) (size align : Int) :
    Interp (ThinPointer (Memory.Provenance M) × Machine M) := do
  let (v, m') ← evalIntrinsicM m .Allocate [(.Int size, tyUsize), (.Int align, tyUsize)] tyRawPtr
  match v with
  | .Ptr ⟨ptr, none⟩ => pure (ptr, m')
  | _ => unsupported "harness: `Allocate` returned something other than a thin pointer"

/-- `Deallocate(ptr, size, align)`. -/
def deallocM (m : Machine M) (ptr : ThinPointer (Memory.Provenance M)) (size align : Int) :
    Interp (Machine M) := do
  let (_, m') ← evalIntrinsicM m .Deallocate
    [(.Ptr ⟨ptr, none⟩, tyRawPtr), (.Int size, tyUsize), (.Int align, tyUsize)] unitType
  pure m'

/-- A non-atomic `typed_store` of an integer at its natural alignment. -/
def storeM (m : Machine M) (ptr : ThinPointer (Memory.Provenance M)) (v : Int) (ty : IntType) :
    Interp (Machine M) :=
  typedStoreM m ptr (.Int v) (.Int ty) ⟨ty.size.bytes⟩ .None

/-- A non-atomic `typed_load` of an integer at its natural alignment. -/
def loadM (m : Machine M) (ptr : ThinPointer (Memory.Provenance M)) (ty : IntType) :
    Interp (Int × Machine M) := do
  let (v, m') ← typedLoadM m ptr (.Int ty) ⟨ty.size.bytes⟩ .None
  match v with
  | .Int i => pure (i, m')
  | _ => unsupported "harness: `typed_load` at an integer type returned a non-integer"

/-- `ConcurrentMemory::allocate` with an explicit `AllocationKind` (how the
machine allocates `Global` and `Stack` memory). -/
def allocKindM (m : Machine M) (kind : AllocationKind) (size align : Nat) :
    Interp (ThinPointer (Memory.Provenance M) × Machine M) := do
  let (ptr, cm) ← ConcurrentMemory.allocate m.mem kind ⟨size⟩ ⟨align⟩
  pure (ptr, { m with mem := cm })

/-- `ConcurrentMemory::leak_check` of the machine's memory. -/
def leakM (m : Machine M) : Interp Unit :=
  ConcurrentMemory.leak_check m.mem

/-- `ConcurrentMemory::retag_ptr` of a thin pointer at a pointer type, in a
frame with extra `fe`; `fnEntry` requests a protector. -/
def retagM (m : Machine M) (fe : Memory.FrameExtra M) (ptr : ThinPointer (Memory.Provenance M))
    (pty : PtrType) (fnEntry : Bool) :
    Interp (ThinPointer (Memory.Provenance M) × Machine M × Memory.FrameExtra M) := do
  let (p, cm, fe') ←
    ConcurrentMemory.retag_ptr m.mem fe ⟨ptr, none⟩ pty fnEntry true
      (fun _ => specPanic "harness: no vtables")
  pure (p.thin_pointer, { m with mem := cm }, fe')

/-- `ConcurrentMemory::end_call`: release the protectors of a frame. -/
def endCallM (m : Machine M) (fe : Memory.FrameExtra M) : Interp (Machine M) := do
  let cm ← ConcurrentMemory.end_call m.mem fe
  pure { m with mem := cm }

/-- The pointee of a reference or `Box` to a 32-byte, 32-aligned block whose
`UnsafeCell`s are `cells`. -/
def blockPointee (cells : List (Offset × Size)) (freeze : Bool) : PointeeInfo :=
  { layout := .Sized ⟨32⟩ ⟨32⟩, inhabited := true, unsafe_cells := .Sized cells, freeze := freeze
    unpin := true }

/-- A 32-byte pointee without interior mutability. -/
def frozenPointee : PointeeInfo := blockPointee [] true

/-- A 32-byte pointee that is one `UnsafeCell` (a `Cell`). -/
def cellPointee : PointeeInfo := blockPointee [(⟨0⟩, ⟨32⟩)] false

/-- A slice pointer `*const [u8]`. -/
def slicePtr (thin : ThinPointer (Memory.Provenance M)) (len : Int) : Value M × «Type» :=
  (.Ptr ⟨thin, some (.ElementCount len)⟩, .Ptr (.Raw .ElementCount))

/-- The trait of the trait-object pointers below. -/
def dynTrait : TraitName := ⟨⟨0⟩⟩

/-- A trait-object pointer `*const dyn Trait` whose vtable is at `vtableAddr`. -/
def dynPtr (thin : ThinPointer (Memory.Provenance M)) (vtableAddr : Int) : Value M × «Type» :=
  (.Ptr ⟨thin, some (.VTablePointer ⟨vtableAddr, none⟩)⟩, .Ptr (.Raw (.VTablePointer dynTrait)))

/-- Observe a Boolean result. -/
def boolObs (r : Interp (Value M × «Type»)) : Interp MrHeapWideObs := do
  let (v, _) ← r
  match v with
  | .Bool b => pure (.okBool b)
  | _ => unsupported "harness: a comparison returned a non-Boolean"

/-- Observe what `Allocate` created: the newest allocation record must be
live, a `Heap` allocation, at the returned address, and the returned address
must be aligned to the record's alignment; the observation reports the
record's size and alignment. -/
def allocObs (H : Harness M) (ptr : ThinPointer (Memory.Provenance M)) (m : Machine M) :
    Interp MrHeapWideObs :=
  match (H.view m.mem.memory).getLast? with
  | some a =>
    if a.live && decide (a.kind = .Heap) && decide (a.addr = ptr.addr) &&
        Align.is_aligned ⟨a.align⟩ ptr.addr then
      pure (.okAlloc a.size a.align)
    else
      unsupported "harness: the newest allocation is not the live aligned heap block returned"
  | none => unsupported "harness: no allocation after `Allocate`"

/-- `Allocate(size, align)` on the initial machine, observed. -/
def obsAlloc (H : Harness M) (size align : Int) : Interp MrHeapWideObs := do
  let (ptr, m) ← allocM (initMach H) size align
  allocObs H ptr m

/-- `Allocate`, store, load, `Deallocate`, `leak_check`. -/
def roundTrip (H : Harness M) (size align : Int) (ty : IntType) (v : Int) :
    Interp MrHeapWideObs := do
  let (ptr, m) ← allocM (initMach H) size align
  let m ← storeM m ptr v ty
  let (r, m) ← loadM m ptr ty
  let m ← deallocM m ptr size align
  leakM m
  pure (.okRoundTrip r.toNat)

/-- The over-aligned `Box` of the protector scenarios: `Allocate(32, 32)`,
`42u32` stored at offset 0, and a child reference of type `pty` retagged from
the allocation's pointer (`fnEntry` requests a protector), then read once
through the child when `readChild`. Returns the parent pointer, the child
pointer, the machine, and the frame's extra. -/
def boxWithChild (H : Harness M) (pty : PtrType) (fnEntry readChild : Bool) :
    Interp (ThinPointer (Memory.Provenance M) × ThinPointer (Memory.Provenance M) ×
      Machine M × Memory.FrameExtra M) := do
  let (parent, m) ← allocM (initMach H) 32 32
  let m ← storeM m parent 42 itU32
  let (child, m, fe) ← retagM m MemoryOps.new_call parent pty fnEntry
  if readChild then
    let (_, m) ← loadM m child itU32
    pure (parent, child, m, fe)
  else
    pure (parent, child, m, fe)

/-- The 30 scenarios (`0..29`). An index out of range is `unsupported`. -/
def mrCase (H : Harness M) : Nat → Interp MrHeapWideObs
  | 0 => obsAlloc H 0 1
  | 1 => obsAlloc H 0 32
  | 2 => roundTrip H 4 4 itU32 3735928559
  | 3 => roundTrip H 32 32 itU64 81985529216486895
  | 4 => do
    let (ptr, m) ← allocM (initMach H) 4 4
    let (r, _) ← loadM m ptr itU32
    pure (.okRoundTrip r.toNat)
  | 5 => obsAlloc H 8 3
  | 6 => obsAlloc H 9223372036854775808 8
  | 7 => do
    let (ptr, m) ← allocM (initMach H) 8 8
    let m ← deallocM m ptr 8 8
    let _ ← deallocM m ptr 8 8
    pure .okDealloc
  | 8 => do
    let (ptr, m) ← allocM (initMach H) 4 4
    let m ← storeM m ptr 7 itU32
    let m ← deallocM m ptr 4 4
    let (r, _) ← loadM m ptr itU32
    pure (.okRoundTrip r.toNat)
  | 9 => do
    let (ptr, m) ← allocM (initMach H) 8 8
    let _ ← deallocM m { ptr with addr := ptr.addr + 4 } 8 8
    pure .okDealloc
  | 10 => do
    let (ptr, m) ← allocM (initMach H) 8 8
    let _ ← deallocM m ptr 4 8
    pure .okDealloc
  | 11 => do
    let (ptr, m) ← allocM (initMach H) 8 8
    let _ ← deallocM m ptr 8 16
    pure .okDealloc
  | 12 => do
    let _ ← deallocM (initMach H) ⟨4096, none⟩ 8 8
    pure .okDealloc
  | 13 => do
    let (ptr, m) ← allocKindM (initMach H) .Global 4 4
    let _ ← deallocM m ptr 4 4
    pure .okDealloc
  | 14 => do
    let (ptr, m) ← allocKindM (initMach H) .Stack 4 4
    let _ ← deallocM m ptr 4 4
    pure .okDealloc
  | 15 => do
    let (_, m) ← allocM (initMach H) 8 8
    leakM m
    pure .okDealloc
  | 16 => do
    let (ptr, m) ← allocM (initMach H) 8 8
    let m ← deallocM m ptr 8 8
    leakM m
    pure .okDealloc
  | 17 => do
    let (_, m) ← allocKindM (initMach H) .Global 8 8
    leakM m
    pure .okDealloc
  | 18 => do
    let (_, box, m, _) ← boxWithChild H (.Box frozenPointee) true false
    let _ ← deallocM m box 32 32
    pure .okDealloc
  | 19 => do
    let (parent, _, m, _) ← boxWithChild H (.Ref .Immutable frozenPointee) true true
    let _ ← deallocM m parent 32 32
    pure .okDealloc
  | 20 => do
    let (parent, _, m, fe) ← boxWithChild H (.Ref .Immutable frozenPointee) true true
    let m ← endCallM m fe
    let _ ← deallocM m parent 32 32
    pure .okDealloc
  | 21 => do
    let (_, child, m, _) ← boxWithChild H (.Ref .Immutable frozenPointee) false false
    let _ ← deallocM m child 32 32
    pure .okDealloc
  | 22 => do
    let (parent, _, m, _) ← boxWithChild H (.Ref .Immutable cellPointee) true false
    let _ ← deallocM m parent 32 32
    pure .okDealloc
  | 23 => boolObs (evalAddrEqM (M := M) (slicePtr ⟨8192, none⟩ 3) (slicePtr ⟨8192, none⟩ 7))
  | 24 => boolObs (evalWideEqM (M := M) (slicePtr ⟨8192, none⟩ 3) (slicePtr ⟨8192, none⟩ 7))
  | 25 => boolObs (evalAddrEqM (M := M) (dynPtr ⟨8192, none⟩ 36864) (dynPtr ⟨8192, none⟩ 40960))
  | 26 => boolObs (evalWideEqM (M := M) (dynPtr ⟨8192, none⟩ 36864) (dynPtr ⟨8192, none⟩ 40960))
  | 27 => boolObs (evalAddrEqM (M := M) (slicePtr ⟨8192, some H.provA⟩ 5)
      (dynPtr ⟨8192, some H.provB⟩ 36864))
  | 28 => boolObs (evalWideEqM (M := M) (slicePtr ⟨8192, some H.provA⟩ 5)
      (dynPtr ⟨8192, some H.provB⟩ 36864))
  | 29 => obsAlloc H 0 1073741824
  | _ => unsupported "harness: no such case"

/-- One step of a threaded trace: on success record the observation and
continue with the new state; on a `Stop` record its class and halt. -/
def traceStep {α : Type} (r : Interp (MrHeapWideObs × α)) (k : α → List MrHeapWideObs) :
    List MrHeapWideObs :=
  match r with
  | .ok (o, a) => o :: k a
  | .error s => [obsOfStop s]

/-- The heap lifecycle on one machine: `Allocate(32, 32)`; store and load a
`u64`; `leak_check` before deallocation (which reports the leak and changes
nothing); `addr_eq` of two slice pointers to the block; `Deallocate`; and a
second `Deallocate`, which halts the trace. -/
def lifecycleTraceM (H : Harness M) : List MrHeapWideObs :=
  traceStep (do
      let (ptr, m) ← allocM (initMach H) 32 32
      let o ← allocObs H ptr m
      pure (o, (ptr, m))) fun (ptr, m) =>
  traceStep (do
      let m ← storeM m ptr 14627333968688404088 itU64
      let (r, m) ← loadM m ptr itU64
      pure (.okRoundTrip r.toNat, m)) fun m =>
  observe (do leakM m; pure .okDealloc) ::
  traceStep (do
      let o ← boolObs (evalAddrEqM (slicePtr ptr 2) (slicePtr ptr 4))
      pure (o, ())) fun _ =>
  traceStep (do
      let m ← deallocM m ptr 32 32
      pure (.okDealloc, m)) fun m =>
  traceStep (do
      let m ← deallocM m ptr 32 32
      pure (.okDealloc, m)) fun _ => []

/-- The protector trace on one over-aligned block with a strongly protected
`Frozen` child (`boxWithChild`, before any read through the child): read
`42u32` through the child; `addr_eq` of a slice pointer through the parent
and one through the child; `Deallocate` through the parent while the child's
protector is active; and, if that succeeded, the exit `leak_check`. -/
def protectorTraceM (H : Harness M) : List MrHeapWideObs :=
  match boxWithChild H (.Ref .Immutable frozenPointee) true false with
  | .error s => [obsOfStop s]
  | .ok (parent, child, m, _) =>
    traceStep (do
        let (r, m) ← loadM m child itU32
        pure (.okRoundTrip r.toNat, m)) fun m =>
    traceStep (do
        let o ← boolObs (evalAddrEqM (slicePtr parent 1) (slicePtr child 8))
        pure (o, ())) fun _ =>
    traceStep (do
        let m ← deallocM m parent 32 32
        pure (.okDealloc, m)) fun m =>
    traceStep (do
        leakM m
        pure (.okDealloc, ())) fun _ => []

end Machines

/-- `Machine<BasicMemory<x86_64>>`. -/
def bmHarness : Harness BM where
  params := ()
  view := fun mem =>
    mem.allocations.map fun a => ⟨a.data.length, a.align.bytes, a.live, a.kind, a.addr⟩
  provA := (⟨7⟩, ())
  provB := (⟨8⟩, ())

/-- `Machine<TreeBorrowsMemory<x86_64>>` (implicit writes enabled). -/
def tbHarness : Harness TBM where
  params := ⟨true⟩
  view := fun tbm =>
    tbm.mem.allocations.map fun a => ⟨a.data.length, a.align.bytes, a.live, a.kind, a.addr⟩
  provA := (⟨7⟩, [])
  provB := (⟨7⟩, [0])

/-- The 30-case observer: `tb = false` runs on `Mach`, `tb = true` on
`MachTB`. For `caseIdx ≥ 30` it is `.invalidOrUnsupported`. -/
def mrHeapWideObserve (tb : Bool) (caseIdx : Nat) : MrHeapWideObs :=
  if tb then observe (mrCase tbHarness caseIdx) else observe (mrCase bmHarness caseIdx)

/-- The exact `Stop` of a case, if it stopped. -/
def mrCaseStop (tb : Bool) (caseIdx : Nat) : Option Stop :=
  if tb then stopOf (mrCase tbHarness caseIdx) else stopOf (mrCase bmHarness caseIdx)

/-- The heap lifecycle trace on `Mach` (`tb = false`) or `MachTB`. -/
def mrHeapLifecycleTrace (tb : Bool) : List MrHeapWideObs :=
  if tb then lifecycleTraceM tbHarness else lifecycleTraceM bmHarness

/-- The protector trace on `Mach` (`tb = false`) or `MachTB`. -/
def mrProtectorDeallocTrace (tb : Bool) : List MrHeapWideObs :=
  if tb then protectorTraceM tbHarness else protectorTraceM bmHarness

/-- **The 30-case table.** Cases `0..27` and `29` succeed or are UB; case
`28` (`==` on a slice pointer and a trait-object pointer) is a specification
panic. Cases `19` and `21` are mode-sensitive: `okDealloc` on `Mach`, UB on
`MachTB`. -/
theorem mrHeapWideObserve_table :
    (List.range 30).map (mrHeapWideObserve false) =
      [.okAlloc 0 1, .okAlloc 0 32, .okRoundTrip 3735928559, .okRoundTrip 81985529216486895,
       .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub,
       .memoryLeak, .okDealloc, .okDealloc,
       .okDealloc, .okDealloc, .okDealloc, .okDealloc, .okDealloc,
       .okBool true, .okBool false, .okBool true, .okBool false, .okBool true,
       .specPanic, .okAlloc 0 1073741824] ∧
    (List.range 30).map (mrHeapWideObserve true) =
      [.okAlloc 0 1, .okAlloc 0 32, .okRoundTrip 3735928559, .okRoundTrip 81985529216486895,
       .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub,
       .memoryLeak, .okDealloc, .okDealloc,
       .okDealloc, .ub, .okDealloc, .ub, .okDealloc,
       .okBool true, .okBool false, .okBool true, .okBool false, .okBool true,
       .specPanic, .okAlloc 0 1073741824] := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- Out of range, the observer is `.invalidOrUnsupported` on both machines. -/
theorem mrHeapWideObserve_out_of_range (tb : Bool) (caseIdx : Nat) (h : 30 ≤ caseIdx) :
    mrHeapWideObserve tb caseIdx = .invalidOrUnsupported := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm]
  cases tb <;> rfl

/-- The exact `Stop` of every case on `Mach` (`none`: the case succeeded). -/
theorem mrCaseStop_table_bm :
    (List.range 30).map (mrCaseStop false) =
      [none, none, none, none,
       some (.ub "load at type but the data in memory violates the language invariant"),
       some (.ub "invalid alignment for `Allocate` intrinsic: not a power of 2"),
       some (.ub "asking for a too large allocation"),
       some (.ub "double-free"),
       some (.ub "dereferencing pointer to dead allocation"),
       some (.ub "deallocating with pointer not to the beginning of its allocation"),
       some (.ub "deallocating with incorrect size information"),
       some (.ub "deallocating with incorrect alignment information"),
       some (.ub "deallocating invalid pointer"),
       some (.ub "deallocating Global memory with Heap deallocation operation"),
       some (.ub "deallocating Stack memory with Heap deallocation operation"),
       some .memoryLeak,
       none, none, none, none, none, none, none, none, none, none, none, none,
       some (.specPanic "unmatching metadata in wide pointer comparasion"),
       none] := by
  decide +kernel

/-- The exact `Stop` of every case on `MachTB`: as on `Mach`, except for the
two Tree Borrows cases `19` (a foreign write, the deallocation through the
parent, to a strongly protected `Frozen` child that was read) and `21` (a
write, the deallocation, through an unprotected `Frozen` child). -/
theorem mrCaseStop_table_tb :
    (List.range 30).map (mrCaseStop true) =
      [none, none, none, none,
       some (.ub "load at type but the data in memory violates the language invariant"),
       some (.ub "invalid alignment for `Allocate` intrinsic: not a power of 2"),
       some (.ub "asking for a too large allocation"),
       some (.ub "double-free"),
       some (.ub "dereferencing pointer to dead allocation"),
       some (.ub "deallocating with pointer not to the beginning of its allocation"),
       some (.ub "deallocating with incorrect size information"),
       some (.ub "deallocating with incorrect alignment information"),
       some (.ub "deallocating invalid pointer"),
       some (.ub "deallocating Global memory with Heap deallocation operation"),
       some (.ub "deallocating Stack memory with Heap deallocation operation"),
       some .memoryLeak,
       none, none, none,
       some (.ub "Tree Borrows: foreign write of protected Frozen reference which had a local read"),
       none,
       some (.ub "Tree Borrows: local write of Frozen reference"),
       none, none, none, none, none, none,
       some (.specPanic "unmatching metadata in wide pointer comparasion"),
       none] := by
  decide +kernel

/-- The two machines disagree on exactly the Tree Borrows cases `19` and `21`. -/
theorem mrHeapWideObserve_mode_sensitive :
    (List.range 30).filter (fun i => mrHeapWideObserve false i != mrHeapWideObserve true i) =
      [19, 21] := by
  decide +kernel

/-- **The heap lifecycle trace**, the same on both machines: the block is
allocated, round-trips a `u64`, is reported by `leak_check` while live,
`addr_eq`s with itself under different slice lengths, is deallocated, and
cannot be deallocated twice. -/
theorem mrHeapLifecycleTrace_table :
    mrHeapLifecycleTrace false =
      [.okAlloc 32 32, .okRoundTrip 14627333968688404088, .memoryLeak, .okBool true,
       .okDealloc, .ub] ∧
    mrHeapLifecycleTrace true =
      [.okAlloc 32 32, .okRoundTrip 14627333968688404088, .memoryLeak, .okBool true,
       .okDealloc, .ub] := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- **The protector trace.** On `Mach` the block is deallocated and nothing
leaks; on `MachTB` deallocating through the parent while the child's strong
protector is active is UB, and the trace halts there. -/
theorem mrProtectorDeallocTrace_table :
    mrProtectorDeallocTrace false = [.okRoundTrip 42, .okBool true, .okDealloc, .okDealloc] ∧
    mrProtectorDeallocTrace true = [.okRoundTrip 42, .okBool true, .ub] := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-! ### Further Tree Borrows witnesses (`rust#165833`) -/

/-- Deallocate the block through a child reference of type `pty` retagged on
function entry (so protected), optionally after releasing the frame's
protectors with `end_call`. -/
def deallocThroughChild {M : Type} [Memory M] [MemoryOps M] (H : Harness M) (pty : PtrType)
    (release : Bool) : Interp MrHeapWideObs := do
  let (_, child, m, fe) ← boxWithChild H pty true false
  let m ← if release then endCallM m fe else pure m
  let _ ← deallocM m child 32 32
  pure .okDealloc

/-- The explicit strong-protector check of `TreeBorrowsMemory::deallocate`:
deallocating through a strongly protected `&mut` itself passes the write
access (a local write) and is then rejected with the dedicated message; after
`end_call` released the protector the same deallocation succeeds; through a
weakly protected `Box` it succeeds while the protector is active. `Mach` has
no protectors. -/
theorem strongProtector_dealloc_through_protected_tag :
    stopOf (deallocThroughChild tbHarness (.Ref .Mutable frozenPointee) false) =
      some (.ub "Tree Borrows: deallocating strongly protected allocation") ∧
    stopOf (deallocThroughChild tbHarness (.Ref .Mutable frozenPointee) true) = none ∧
    stopOf (deallocThroughChild tbHarness (.Box frozenPointee) false) = none ∧
    stopOf (deallocThroughChild bmHarness (.Ref .Mutable frozenPointee) false) = none := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The memory and child pointer of the strongly protected `&mut` scenario, as
`TreeBorrowsMemory` itself produced them. -/
def tbStrongMut : Option (TBM × ThinPointer TreeBorrowsProvenance) :=
  match boxWithChild tbHarness (.Ref .Mutable frozenPointee) true false with
  | .ok (_, child, m, _) => some (m.mem.memory, child)
  | .error _ => none

/-- On that reachable memory, `TreeBorrowsMemory::deallocate` through the
child is UB with the strong-protector message. -/
theorem tbStrongMut_dealloc :
    tbStrongMut.map (fun x => stopOf (TreeBorrowsMemory.deallocate x.1 x.2 .Heap ⟨32⟩ ⟨32⟩)) =
      some (some (.ub "Tree Borrows: deallocating strongly protected allocation")) := by
  decide +kernel

/-- Even after both a read AND a write through a strongly protected `Cell`
(`UnsafeCell`) child reference, deallocating through the parent `Unique` tag
still succeeds on `MachTB` (interior mutability exemption holds after access,
not only when unaccessed). -/
def strongProtectedCellAccessedDealloc : Interp MrHeapWideObs := do
  let (parent, child, m, _) ← boxWithChild tbHarness (.Ref .Immutable cellPointee) true true
  let m ← storeM m child 99 itU32
  let (v, m) ← loadM m child itU32
  let _ ← deallocM m parent 32 32
  pure (.okRoundTrip v.toNat)

/-- Witness that accessing (reading + mutating) a strongly protected `Cell`
child still allows parent deallocation on `MachTB`. -/
theorem strongProtected_cell_accessed_dealloc_ok :
    strongProtectedCellAccessedDealloc = .ok (.okRoundTrip 99) := by
  kernel_rfl

/-! ### Wide-pointer encoding witnesses (`rust#166144`) -/

/-- Encode a wide pointer and decode it again. -/
def widePtrCodec (M : Type) [Memory M] [MemoryOps M] (metaKind : PointerMetaKind)
    (ptr : Pointer (Memory.Provenance M)) : Interp (Option (Value M)) := do
  let bytes ← encodeWidePtrM (M := M) metaKind ptr
  decodeWidePtrM (M := M) metaKind bytes

/-- The first `PTR_SIZE` bytes of the encoding of a wide pointer. -/
def widePtrThinBytes (M : Type) [Memory M] (metaKind : PointerMetaKind)
    (ptr : Pointer (Memory.Provenance M)) :
    Interp (List (AbstractByte (Memory.Provenance M))) := do
  let bytes ← encodeWidePtrM (M := M) metaKind ptr
  pure (bytes.take 8)

/-- On both machines, slice and trait-object pointers with provenance survive
`encode` then `decode` (`encodeWidePtrM`, `decodeWidePtrM`), and the thin
prefix of the encoding does not depend on the slice length: the bytes
`addr_eq` compares are the same for `len = 3` and `len = 7`. -/
theorem widePtr_codec_roundtrip :
    widePtrCodec BM .ElementCount ⟨⟨8192, some bmHarness.provA⟩, some (.ElementCount 3)⟩ =
      .ok (some (.Ptr ⟨⟨8192, some bmHarness.provA⟩, some (.ElementCount 3)⟩)) ∧
    widePtrCodec TBM .ElementCount ⟨⟨8192, some tbHarness.provB⟩, some (.ElementCount 3)⟩ =
      .ok (some (.Ptr ⟨⟨8192, some tbHarness.provB⟩, some (.ElementCount 3)⟩)) ∧
    widePtrCodec BM (.VTablePointer dynTrait)
        ⟨⟨8192, some bmHarness.provA⟩, some (.VTablePointer ⟨36864, none⟩)⟩ =
      .ok (some (.Ptr ⟨⟨8192, some bmHarness.provA⟩, some (.VTablePointer ⟨36864, none⟩)⟩)) ∧
    widePtrCodec TBM (.VTablePointer dynTrait)
        ⟨⟨8192, some tbHarness.provB⟩, some (.VTablePointer ⟨36864, none⟩)⟩ =
      .ok (some (.Ptr ⟨⟨8192, some tbHarness.provB⟩, some (.VTablePointer ⟨36864, none⟩)⟩)) ∧
    widePtrThinBytes BM .ElementCount ⟨⟨8192, some bmHarness.provA⟩, some (.ElementCount 3)⟩ =
      widePtrThinBytes BM .ElementCount ⟨⟨8192, some bmHarness.provA⟩, some (.ElementCount 7)⟩ ∧
    widePtrThinBytes TBM .ElementCount ⟨⟨8192, some tbHarness.provB⟩, some (.ElementCount 3)⟩ =
      widePtrThinBytes TBM .ElementCount ⟨⟨8192, some tbHarness.provB⟩, some (.ElementCount 7)⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> kernel_rfl

/-! ## §6. Vacuity, capstone, and axiom audit -/

/-- The initial `MachTB` satisfies `MachTB.wfLive`: its memory is
`TreeBorrowsMemory::new`. -/
theorem tbInit_wfLive : MiniRustSpec.Correspondence.MachTB.wfLive (initMach tbHarness) :=
  MiniRustSpec.Correspondence.TreeBorrowsMemory.new_wfLive ⟨true⟩

/-- `Allocate(32, 32)` and then `Deallocate` on the initial `MachTB`, keeping
both machines. -/
def tbAllocDealloc : Interp (MachTB × MachTB) := do
  let (ptr, m) ← allocM (initMach tbHarness) 32 32
  let m' ← deallocM m ptr 32 32
  pure (m, m')

/-- `tbAllocDealloc` succeeds. -/
theorem tbAllocDealloc_ok : stopOf tbAllocDealloc = none := by
  decide +kernel

/-- `evalIntrinsicM_allocate_tb_wfLive` and `evalIntrinsicM_deallocate_tb_wfLive`
are not vacuous: on the `wfLive` initial machine, `Allocate` and then
`Deallocate` succeed, and both resulting machines are `wfLive`. -/
theorem heap_tb_wfLive_witness :
    ∃ m m', tbAllocDealloc = .ok (m, m') ∧
      MiniRustSpec.Correspondence.MachTB.wfLive m ∧
      MiniRustSpec.Correspondence.MachTB.wfLive m' := by
  have hok := tbAllocDealloc_ok
  cases h : tbAllocDealloc with
  | error e => rw [h] at hok; cases hok
  | ok r =>
    obtain ⟨m, m'⟩ := r
    refine ⟨m, m', rfl, ?_⟩
    unfold tbAllocDealloc at h
    obtain ⟨⟨ptr, m1⟩, halloc, h⟩ := interp_bind_eq_ok h
    obtain ⟨m2, hdealloc, h⟩ := interp_bind_eq_ok h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok h)
    unfold allocM at halloc
    obtain ⟨⟨v, m0⟩, hA, halloc⟩ := interp_bind_eq_ok halloc
    have hwf0 : MiniRustSpec.Correspondence.MachTB.wfLive m0 :=
      evalIntrinsicM_allocate_tb_wfLive tbInit_wfLive hA
    have hm : m0 = m1 := by
      rcases v with _ | _ | ⟨p, _ | _⟩ | _ | _ | _ <;>
        first
        | (cases halloc; done)
        | exact (Prod.mk.inj (interp_pure_eq_ok halloc)).2
    subst hm
    unfold deallocM at hdealloc
    obtain ⟨⟨v', m3⟩, hD, hdealloc⟩ := interp_bind_eq_ok hdealloc
    obtain rfl := interp_pure_eq_ok hdealloc
    exact ⟨hwf0, evalIntrinsicM_deallocate_tb_wfLive hwf0 hD⟩

/-- Whether every hypothesis of `tb_deallocate_strong_protector_ub` holds on
the reachable memory `tbStrongMut` for the child pointer (`none` if a lookup
or the write access fails). -/
def tbStrongMutCheck : Option Bool :=
  tbStrongMut.bind fun x =>
    match x.2.provenance with
    | none => none
    | some (id, path) =>
      match x.1.mem.allocations[id._0.toNat]? with
      | none => none
      | some a =>
        match Node.access a.extra.root (some path) .Write ⟨0⟩ ⟨32⟩ with
        | .error _ => none
        | .ok root' =>
          some (decide (0 ≤ id._0) && a.live && decide (x.2.addr = a.addr) &&
            decide (AllocationKind.Heap = a.kind) && decide ((⟨32⟩ : Size) = Allocation.size a) &&
            decide ((⟨32⟩ : Align) = a.align) &&
            Node.contains_strong_protector_preventing_deallocation root')

/-- The check succeeds. -/
theorem tbStrongMutCheck_true : tbStrongMutCheck = some true := by
  decide +kernel

/-- `tb_deallocate_strong_protector_ub` is not vacuous: on the memory that
`TreeBorrowsMemory` itself produced for a strongly protected `&mut` to the
block (`tbStrongMut`), every hypothesis of the law holds for the child
pointer: the allocation is live, the pointer is to its beginning, kind, size,
and alignment match, the write access through the child succeeds, and the
resulting tree contains a strong protector preventing deallocation. -/
theorem tb_deallocate_strong_protector_witness :
    ∃ tbm ptr id path a root',
      tbStrongMut = some (tbm, ptr) ∧
      ptr.provenance = some (id, path) ∧ 0 ≤ id._0 ∧
      tbm.mem.allocations[id._0.toNat]? = some a ∧ a.live = true ∧ ptr.addr = a.addr ∧
      AllocationKind.Heap = a.kind ∧ (⟨32⟩ : Size) = Allocation.size a ∧
      (⟨32⟩ : Align) = a.align ∧
      Node.access a.extra.root (some path) .Write ⟨0⟩ ⟨32⟩ = .ok root' ∧
      Node.contains_strong_protector_preventing_deallocation root' = true := by
  have hk := tbStrongMutCheck_true
  unfold tbStrongMutCheck at hk
  cases hs : tbStrongMut with
  | none => rw [hs] at hk; cases hk
  | some x =>
    obtain ⟨tbm, ptr⟩ := x
    rw [hs] at hk
    dsimp only [Option.bind] at hk
    cases hp : ptr.provenance with
    | none => rw [hp] at hk; cases hk
    | some pr =>
      obtain ⟨id, path⟩ := pr
      rw [hp] at hk
      dsimp only at hk
      cases hget : tbm.mem.allocations[id._0.toNat]? with
      | none => rw [hget] at hk; cases hk
      | some a =>
        rw [hget] at hk
        dsimp only at hk
        cases hacc : Node.access a.extra.root (some path) .Write ⟨0⟩ ⟨32⟩ with
        | error e => rw [hacc] at hk; cases hk
        | ok root' =>
          rw [hacc] at hk
          dsimp only at hk
          have hb := Option.some.inj hk
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
          obtain ⟨⟨⟨⟨⟨⟨hi, hlive⟩, haddr⟩, hkind⟩, hsize⟩, halign⟩, hprot⟩ := hb
          exact ⟨tbm, ptr, id, path, a, root', rfl, hp, hi, hget, hlive, haddr, hkind, hsize,
            halign, hacc, hprot⟩

/-! ### Episode 1 capstone -/

/-- **Episode 1 capstone**: the headline guarantees of this module in one
statement.
1. On `Allocate` and `Deallocate`, the polymorphic `evalIntrinsicM` at
   `BasicMemory` is exactly `evalIntrinsic` on `Mach`; and on every `Mach`, a
   successful `Allocate` leaks until its pointer is passed to `Deallocate`
   with the same size and alignment, which succeeds, restores `leak_check`,
   and makes a second `Deallocate` a double-free (`heap_lifecycle_bm`).
2. On `MachTB`, both preserve the Tree Borrows invariant `MachTB.wfLive` (which
   the initial machine satisfies), and the full universal heap lifecycle
   (`Allocate` -> leak -> `Deallocate` passing `Node.access .Write` +
   protector check -> `leak_check` restored -> double-free UB + `wfLive`) holds
   on every `MachTB` (`heap_lifecycle_tb`).
3. `leak_check` reports `MemoryLeak` exactly when a live `Heap` allocation
   exists, on both memory models (so `Global`, `Stack`, `Function`, and
   `VTable` memory never leaks: `rust#166221`).
4. `ptr::addr_eq` compares addresses only, on both memory models, whatever
   the metadata and provenance of its operands, whereas `==` on a slice
   pointer and a trait-object pointer is a specification panic (`rust#166144`).
5. Protectors (`rust#165833`): a `Protected::Weak` node and a `Cell`-only
   strongly protected node never prevent deallocation; a strongly protected
   node with a `Frozen` permission that had a local read does.
6. The kernel-evaluated 30-case table on both machines, and both threaded
   traces. -/
theorem ep1_minirust_heap_wide_capstone :
    (∀ (m : Mach) (op : IntrinsicOp) (args : List (Val × «Type»)) (retTy : «Type»),
      isHeapOp op = true →
        evalIntrinsicM (M := BM) m op args retTy = evalIntrinsic m op args retTy) ∧
    (∀ (m m1 : Mach) (size align : Int) (sTy aTy : «Type») (p : PtrType) (val : Val)
        (pTy : «Type»),
      evalIntrinsicM m .Allocate [(.Int size, sTy), (.Int align, aTy)] (.Ptr p) = .ok (val, m1) →
      ∃ ptr m2, val = .Ptr ⟨ptr, none⟩ ∧
        ConcurrentMemory.leak_check m1.mem = .error .memoryLeak ∧
        evalIntrinsicM m1 .Deallocate
            [(.Ptr ⟨ptr, none⟩, pTy), (.Int size, sTy), (.Int align, aTy)] unitType =
          .ok (unitValueM, m2) ∧
        ConcurrentMemory.leak_check m2.mem = ConcurrentMemory.leak_check m.mem ∧
        evalIntrinsicM m2 .Deallocate
            [(.Ptr ⟨ptr, none⟩, pTy), (.Int size, sTy), (.Int align, aTy)] unitType =
          .error (.ub "double-free")) ∧
    ((∀ (m m' : MachTB) (op : IntrinsicOp) (args : List (Value TBM × «Type»)) (retTy : «Type»)
        (val : Value TBM), isHeapOp op = true →
        MiniRustSpec.Correspondence.MachTB.wfLive m →
        evalIntrinsicM m op args retTy = .ok (val, m') →
        MiniRustSpec.Correspondence.MachTB.wfLive m') ∧
      MiniRustSpec.Correspondence.MachTB.wfLive (initMach tbHarness) ∧
      (∀ (m m1 : MachTB) (size align : Int) (sTy aTy : «Type») (p : PtrType) (val : Value TBM)
          (pTy : «Type»),
        evalIntrinsicM m .Allocate [(.Int size, sTy), (.Int align, aTy)] (.Ptr p) = .ok (val, m1) →
        ∃ ptr m2, val = .Ptr ⟨ptr, none⟩ ∧
          ConcurrentMemory.leak_check m1.mem = .error .memoryLeak ∧
          evalIntrinsicM m1 .Deallocate
              [(.Ptr ⟨ptr, none⟩, pTy), (.Int size, sTy), (.Int align, aTy)] unitType =
            .ok (unitValueM, m2) ∧
          ConcurrentMemory.leak_check m2.mem = ConcurrentMemory.leak_check m.mem ∧
          evalIntrinsicM m2 .Deallocate
              [(.Ptr ⟨ptr, none⟩, pTy), (.Int size, sTy), (.Int align, aTy)] unitType =
            .error (.ub "double-free") ∧
          (MiniRustSpec.Correspondence.MachTB.wfLive m →
            MiniRustSpec.Correspondence.MachTB.wfLive m1 ∧
            MiniRustSpec.Correspondence.MachTB.wfLive m2))) ∧
    ((∀ cm : ConcurrentMemory BM, ConcurrentMemory.leak_check cm = .error .memoryLeak ↔
        ∃ a ∈ cm.memory.allocations, a.live = true ∧ a.kind = .Heap) ∧
      (∀ cm : ConcurrentMemory TBM, ConcurrentMemory.leak_check cm = .error .memoryLeak ↔
        ∃ a ∈ cm.memory.mem.allocations, a.live = true ∧ a.kind = .Heap)) ∧
    ((∀ (pl pr : Pointer Prov) (tl tr : «Type»),
        evalAddrEqM (M := BM) (.Ptr pl, tl) (.Ptr pr, tr) =
          .ok (.Bool (decide (pl.thin_pointer.addr = pr.thin_pointer.addr)), .Bool)) ∧
      (∀ (pl pr : Pointer TreeBorrowsProvenance) (tl tr : «Type»),
        evalAddrEqM (M := TBM) (.Ptr pl, tl) (.Ptr pr, tr) =
          .ok (.Bool (decide (pl.thin_pointer.addr = pr.thin_pointer.addr)), .Bool)) ∧
      (∀ (tl tr v : ThinPointer TreeBorrowsProvenance) (n : Int) (pty : PtrType) (tyr : «Type»),
        evalWideEqM (M := TBM) (.Ptr ⟨tl, some (.ElementCount n)⟩, .Ptr pty)
            (.Ptr ⟨tr, some (.VTablePointer v)⟩, tyr) =
          .error (.specPanic "unmatching metadata in wide pointer comparasion"))) ∧
    ((∀ n : Node,
        Node.contains_strong_protector_preventing_deallocation n = true ↔
          ∃ nd, Node.InTree nd n ∧ nd.«protected» = .Strong ∧
            ∃ p ∈ nd.permissions, Permission.prevents_deallocation p = true) ∧
      (∀ perms : List Permission,
        Node.contains_strong_protector_preventing_deallocation ⟨[], perms, .Weak⟩ = false) ∧
      (∀ perms : List Permission, (∀ p ∈ perms, p = .Prot .Cell) →
        Node.contains_strong_protector_preventing_deallocation ⟨[], perms, .Strong⟩ = false) ∧
      (∀ (perms : List Permission), Permission.Prot (.Frozen true) ∈ perms →
        Node.contains_strong_protector_preventing_deallocation ⟨[], perms, .Strong⟩ = true) ∧
      (∀ k : Nat, alignFromBytesInt ((2 : Int) ^ k) = some ⟨2 ^ k⟩) ∧
      (∀ sz : Size, x86_64.valid_size sz = true ↔ sz.bytes < 2 ^ 63)) ∧
    ((List.range 30).map (mrHeapWideObserve false) =
        [.okAlloc 0 1, .okAlloc 0 32, .okRoundTrip 3735928559, .okRoundTrip 81985529216486895,
         .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub,
         .memoryLeak, .okDealloc, .okDealloc,
         .okDealloc, .okDealloc, .okDealloc, .okDealloc, .okDealloc,
         .okBool true, .okBool false, .okBool true, .okBool false, .okBool true,
         .specPanic, .okAlloc 0 1073741824] ∧
      (List.range 30).map (mrHeapWideObserve true) =
        [.okAlloc 0 1, .okAlloc 0 32, .okRoundTrip 3735928559, .okRoundTrip 81985529216486895,
         .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub, .ub,
         .memoryLeak, .okDealloc, .okDealloc,
         .okDealloc, .ub, .okDealloc, .ub, .okDealloc,
         .okBool true, .okBool false, .okBool true, .okBool false, .okBool true,
         .specPanic, .okAlloc 0 1073741824]) ∧
    (mrHeapLifecycleTrace false =
        [.okAlloc 32 32, .okRoundTrip 14627333968688404088, .memoryLeak, .okBool true,
         .okDealloc, .ub] ∧
      mrHeapLifecycleTrace true =
        [.okAlloc 32 32, .okRoundTrip 14627333968688404088, .memoryLeak, .okBool true,
         .okDealloc, .ub]) ∧
    (mrProtectorDeallocTrace false = [.okRoundTrip 42, .okBool true, .okDealloc, .okDealloc] ∧
      mrProtectorDeallocTrace true = [.okRoundTrip 42, .okBool true, .ub]) :=
  by
  refine ⟨?_, heap_lifecycle_bm, ⟨?_, ?_, heap_lifecycle_tb⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact fun m op args retTy hop => evalIntrinsicM_bm_eq_heap m op args retTy hop
  · exact fun _ _ _ _ _ _ hop hwf h => evalIntrinsicM_heap_tb_wfLive hop hwf h
  · exact tbInit_wfLive
  · exact fun cm => (cm_leak_check_bm_error_iff cm .memoryLeak).trans
      ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩
  · exact fun cm => (cm_leak_check_tb_error_iff cm .memoryLeak).trans
      ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩
  · exact fun pl pr tl tr => evalAddrEqM_ptr (M := BM) pl pr tl tr
  · exact fun pl pr tl tr => evalAddrEqM_ptr (M := TBM) pl pr tl tr
  · exact fun tl tr v n pty tyr => (evalWideEqM_mixed_specPanic (M := TBM) tl tr v n pty tyr).1
  · exact node_contains_strong_protector_iff
  · exact weak_protector_never_prevents_deallocation
  · exact strong_cell_never_prevents_deallocation
  · exact fun perms hm => strong_accessed_prevents_deallocation perms _ hm (Or.inl rfl)
  · exact alignFromBytesInt_pow2
  · exact x86_64_valid_size_iff
  · exact mrHeapWideObserve_table
  · exact mrHeapLifecycleTrace_table
  · exact mrProtectorDeallocTrace_table

/-! ### Axiom and import audit -/

section AxiomAudit

open Lean Elab Command

/-! Fail the build unless
1. this module's *direct* imports are exactly `Lean`, `MiniRustSpec.Interp`,
   and `MiniRustSpec.Correspondence.Pointers` (plus the implicit `Init`);
2. no `Anneal.*`, `Miri.*`, or `LeanMiriSpec.*` module is imported, even
   transitively;
3. no declaration of this module refers to a constant declared in a
   `Trusted.*`, `Anneal.*`, `Miri.*`, or `LeanMiriSpec.*` module
   (`MiniRustSpec.Correspondence.Pointers` transitively imports
   `Trusted.Rustc.V2026_06_01.MirSemantics.Machine` through
   `MiniRustSpec.Correspondence.Translate`, so `Trusted.*` cannot be excluded
   from the transitive import closure; it is excluded from what this module
   uses);
4. every declaration of this module (`env.constants.map₂`: theorems,
   definitions, instances, and their auxiliary constants) depends only on
   Lean's standard axioms `propext`, `Quot.sound`, and `Classical.choice`: no
   `sorryAx`, no `Lean.ofReduceBool`, and no `Lean.trustCompiler`. -/

run_cmd do
  let env ← getEnv
  let allowed : List Lean.Name :=
    [`Init, `Lean, `MiniRustSpec.Interp, `MiniRustSpec.Correspondence.Pointers]
  for imp in env.header.imports do
    unless allowed.contains imp.module do
      throwError "import-isolation violation: direct import of {imp.module}"
  for modName in env.header.moduleNames do
    if (`Anneal).isPrefixOf modName || (`Miri).isPrefixOf modName ||
        (`LeanMiriSpec).isPrefixOf modName then
      throwError "import-isolation violation: {modName} must not be imported"
  let forbidden (modName : Lean.Name) : Bool :=
    (`Trusted).isPrefixOf modName || (`Anneal).isPrefixOf modName ||
      (`Miri).isPrefixOf modName || (`LeanMiriSpec).isPrefixOf modName
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  for (c, info) in env.constants.map₂.toList do
    let used := info.type.getUsedConstants ++
      (match info.value? (allowOpaque := true) with
        | some v => v.getUsedConstants
        | none => #[])
    for u in used do
      if let some idx := env.getModuleIdxFor? u then
        let modName := env.header.moduleNames[idx.toNat]!
        if forbidden modName then
          throwError "dependency-isolation violation: {c} refers to {u} of {modName}"
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      if a == ``sorryAx then throwError "{c} depends on sorryAx"
      if a == ``Lean.ofReduceBool || a == ``Lean.trustCompiler then
        throwError "{c} depends on {a} (compiler-trusting evaluation)"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} depends on non-standard axiom {a}"
    checked := checked + 1
    if (`MiniRustSpec.HeapAllocAndWidePtrMR).isPrefixOf c then
      if let .thmInfo _ := info then theorems := theorems + 1
  -- This module states 175 `theorem` declarations; auxiliary theorem constants only add to it.
  if theorems < 175 then
    throwError "axiom audit is vacuous: only {theorems} theorems of MiniRustSpec.HeapAllocAndWidePtrMR seen"
  logInfo m!"MiniRustSpec.HeapAllocAndWidePtrMR: {checked} declarations ({theorems} theorems) depend only on propext, Quot.sound, Classical.choice (sorry_free=true, ofReduceBool_free=true, import_isolated=true)"

end AxiomAudit

end MiniRustSpec.HeapAllocAndWidePtrMR
