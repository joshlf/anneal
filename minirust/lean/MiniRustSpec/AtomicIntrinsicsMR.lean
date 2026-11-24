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
# MiniRust atomic intrinsics: laws, UB characterization, and witnesses

This module is about MiniRust `d821c6e3` only. It studies the four atomic
memory intrinsics of `spec/lang/step/intrinsics.md`,
`IntrinsicOp::{AtomicStore, AtomicLoad, AtomicCompareExchange,
AtomicFetchAndOp}`, as `MiniRustSpec.Interp` interprets them: `evalIntrinsic`
on `Machine<BasicMemory<x86_64>>` (`Mach`) and the polymorphic
`evalIntrinsicM` on every memory model, in particular
`Machine<TreeBorrowsMemory<x86_64>>` (`MachTB`). Nothing here mentions Anneal's
MIR semantics; `MiniRustSpec.Correspondence.Pointers` is imported for its
MiniRust-side facts only (the `BasicMemory` codec equivalences and
`MachTB.wfLive`).

* **§1** `valueEqM` / `valueEq` (upstream's `current == before`) decide
  equality of `Value<M>` (`valueEqM_refl`, `valueEqM_eq_true_iff`,
  `valueEq_eq_true_iff`); `evalIntrinsicM` has exactly one outcome
  (`evalIntrinsicM_outcome_unique`); and on the atomic intrinsics
  `evalIntrinsicM` at `BasicMemory` is `evalIntrinsic`
  (`evalIntrinsicM_bm_eq_atomic`).
* **§2** A successful atomic intrinsic is one atomic `typed_load`, one atomic
  `typed_store`, or a load followed by a store (`AtomicEffect`,
  `evalIntrinsicM_atomic_ok_inv`), so it preserves every invariant those
  preserve (`evalIntrinsicM_atomic_preserves`), in particular `MachTB.wfLive`
  (`evalIntrinsicM_atomic_tb_wfLive`), and records only atomic accesses
  (`evalIntrinsicM_atomic_accesses`). `typed_load` and `typed_store` change
  memory only through the memory model's `load` and `store`
  (`typedLoadM_ok_memory`, `typedStoreM_ok_memory`).
* **§3** Complete bidirectional (`iff`) characterizations of both `.ok` and
  `.error` (UB and specification panic, in exact upstream check order) for all
  four atomic intrinsics in every memory model (`atomicStore_{ok,error}_iff`,
  `atomicLoad_{ok,error}_iff`, `atomicCompareExchange_{ok,error}_iff`,
  `atomicFetchAndOp_{ok,error}_iff`), individual guard/UB/panic laws (arity,
  non-thin first argument, unsized, zero-sized, non-power-of-two, wide-pointer
  and oversized types, type mismatches, non-integer types, ill-typed operands,
  misalignment, complete `eval_int_bin_op` UB and overflow coverage), the
  `ConcurrentMemory` data-race interaction laws (`Access::races`,
  `ConcurrentMemory::check_data_races` with `check_data_races_error_iff`,
  `atomic_atomic_no_data_race`, `atomicStore_nonAtomicLoad_data_race` and its
  generalization to every type `atomicStore_any_type_nonAtomicLoad_data_race`,
  `atomicCompareExchange_failure_nonAtomicLoad_no_data_race`,
  `atomicCompareExchange_success_nonAtomicLoad_data_race`,
  `atomicFetchAndOp_nonAtomicLoad_data_race`, and the races of atomic *reads*
  with non-atomic stores `atomicLoad_nonAtomicStore_data_race` and
  `atomicCompareExchange_nonAtomicStore_data_race`), and the provenance laws of
  integer atomics (`encodeM_int_no_provenance`,
  `atomicCompareExchange_success_stores_no_provenance`,
  `atomicFetchAndOp_stores_no_provenance`,
  `atomicCompareExchange_failure_memory_bm`).
* **§4** Kernel-evaluated witnesses on concrete `Mach` and `MachTB` machines:
  round trips across integer widths, `bool`, and thin raw pointers;
  compare-exchange success and failure with their access logs; fetch-and-op
  (including `AddUnchecked`/`SubUnchecked`/`DivExact`/`Shl` vs `Add` overflow);
  dangling, out-of-bounds, misaligned, and uninitialized accesses; ill-typed
  operands; `CM` and `ConcurrentMemory` data-race witnesses (atomic vs atomic,
  atomic write vs non-atomic load, atomic read vs non-atomic store,
  synchronized threads, disjoint byte ranges, and failing vs succeeding
  compare-exchange against a non-atomic load); provenance of pointer bytes
  under integer atomics; the Tree Borrows `Frozen` and `Reserved` witnesses; and
  `Terminator::Intrinsic` end to end through `step` / `steps` and `stepTB` /
  `stepsTB`.
* **§5** Instances showing that the conditional laws (including the data-race
  laws) are not vacuous, and the axiom and import audit.

## What the laws say about upstream MiniRust `d821c6e3`

1. **`AtomicFetchAndOp` does not bring its result in bounds.** It stores the
   result of `eval_int_bin_op` as is, whereas `eval_bin_op` for `BinOp::Int`
   applies `int_ty.bring_in_bounds`. A result outside the integer type
   (`255u8 + 1` or `128u8 << 1`) fails the `assert!` of `Machine::typed_store`,
   a specification panic, where Rust's `fetch_add` wraps — in contrast to
   `AddUnchecked`, which throws UB `"overflow in unchecked add"`
   (`atomicFetchAndOp_out_of_range_specPanic`,
   `atomicFetchAndOp_addUnchecked_overflow_ub`,
   `atomicFetchAndOp_add_u8_overflow_bm`,
   `atomicFetchAndOp_unchecked_and_shift_bm`).
2. **A failing `AtomicCompareExchange` is a read.** It performs no store, so
   it logs only an atomic `Load` (`atomicCompareExchange_failure_accesses`,
   `atomicCompareExchange_accesses`), never races with a non-atomic load on an
   unsynchronized thread
   (`atomicCompareExchange_failure_nonAtomicLoad_no_data_race`, contrasting
   with `atomicCompareExchange_success_nonAtomicLoad_data_race`), and, under
   Tree Borrows, succeeds through a `Frozen` shared reference through which a
   succeeding one is UB (`atomic_frozen_tb`). It is a read, not a no-op: like
   `AtomicLoad`, it *does* race with a non-atomic store
   (`atomicCompareExchange_nonAtomicStore_data_race`,
   `atomicLoad_nonAtomicStore_data_race`).
3. **Unsized types: UB for `AtomicStore`, a specification panic for
   `AtomicLoad`.** `AtomicStore` matches on `LayoutStrategy::Sized` and throws
   UB otherwise; `AtomicLoad` calls `expect_size` (`atomic_slice_u8_unsized`).
4. **The `Align::from_bytes(size.bytes()).unwrap()` of `AtomicCompareExchange`
   and `AtomicFetchAndOp`, and the `previous` `unreachable!()` of
   `AtomicFetchAndOp`, cannot be what panics**: for an integer type whose size
   is not a power of two, `Type::layout` (`IntType::align`) panics first
   (`atomicCompareExchange_ill_formed_int_specPanic`,
   `atomicFetchAndOp_ill_formed_int_specPanic`), and `typed_load` at
   `Type::Int` only ever returns `Value::Int` (`typedLoadM_int_returns_int`),
   so neither dead branch appears in `atomicCompareExchange_error_iff` or
   `atomicFetchAndOp_error_iff`.
5. The UB message of `AtomicCompareExchange` at a non-integer type reads
   `Intrinis::AtomicCompareExchange` upstream; the interpretation and
   `atomicCompareExchange_non_int_ub` keep the typo.
6. **Integer atomics erase provenance exactly when they store.** `Type::decode`
   at `Type::Int` ignores the provenance of the bytes it reads and
   `Type::encode` at `Type::Int` writes bytes without provenance. On the bytes
   of a pointer, `AtomicLoad` and a *failing* `AtomicCompareExchange` at `usize`
   return the bare address and leave every provenance fragment in memory
   (`atomicLoad_memory_bm`, `atomicCompareExchange_failure_memory_bm`), whereas
   a *succeeding* `AtomicCompareExchange` and `AtomicFetchAndOp` erase it, even
   when they store the integer that was there
   (`atomicCompareExchange_success_stores_no_provenance`,
   `atomicFetchAndOp_stores_no_provenance`, `atomic_int_provenance_bm`,
   `atomic_int_provenance_tb`). Whether a pointer survives a compare-exchange
   on its bytes therefore depends on whether the comparison succeeds.
7. **Under Tree Borrows, only an atomic store activates a `Reserved`
   reference.** Through an unprotected mutable reference that has not been
   written to, `AtomicLoad` and a failing `AtomicCompareExchange` keep the
   borrow-tree node `Reserved`, so foreign reads stay harmless; `AtomicStore`,
   `AtomicFetchAndOp`, and a succeeding `AtomicCompareExchange` make it
   `Unique`, disable `Frozen` siblings, and expose it to being frozen by the
   next foreign read (`atomic_reserved_reads_tb`,
   `atomic_reserved_writes_activate_tb`,
   `atomic_reserved_foreign_read_asymmetry_tb`).
8. **`AtomicCompareExchange` checks `next` only when it stores it, and never
   checks `current`.** An ill-typed `current` makes it fail silently
   (`atomicCompareExchange_current_not_int`); an ill-formed `next` is a
   specification panic on success and unnoticed on failure
   (`atomicCompareExchange_next_out_of_range_specPanic`,
   `atomic_ill_typed_operands_bm`). An ill-typed operand of `AtomicFetchAndOp`
   reaches `unreachable!()` (`atomicFetchAndOp_other_not_int_specPanic`).
-/

namespace MiniRustSpec.AtomicIntrinsicsMR

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

/-- `Result::Ok(a)?` continues with `a`. -/
theorem interp_ok_bind {α β : Type} (a : α) (f : α → Interp β) :
    ((Except.ok a : Interp α) >>= f) = f a := rfl

/-- `ret(a)?` continues with `a`. -/
theorem interp_pure_bind {α β : Type} (a : α) (f : α → Interp β) :
    ((pure a : Interp α) >>= f) = f a := rfl

/-- A `Stop` propagates through `?`. -/
theorem interp_error_bind {α β : Type} (e : Stop) (f : α → Interp β) :
    ((Except.error e : Interp α) >>= f) = .error e := rfl

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

/-- Congruence of `?` chains in both the scrutinee and the continuation. -/
theorem interp_bind_congr {α β : Type} {x y : Interp α} {f g : α → Interp β}
    (hxy : x = y) (hfg : ∀ a, f a = g a) : (x >>= f) = (y >>= g) := by
  subst hxy
  cases x with
  | error _ => rfl
  | ok a => exact hfg a

/-- Inversion of a stopping `?` chain. -/
theorem interp_bind_eq_error {α β : Type} {x : Interp α} {f : α → Interp β} {e : Stop}
    (h : (x >>= f) = .error e) : x = .error e ∨ ∃ a, x = .ok a ∧ f a = .error e := by
  cases x with
  | error s =>
    cases h
    exact Or.inl rfl
  | ok a => exact Or.inr ⟨a, rfl, h⟩

/-- `List.any` is `false` iff every element satisfies `p x = false`. -/
theorem list_any_eq_false_iff {α : Type} {l : List α} {p : α → Bool} :
    l.any p = false ↔ ∀ x ∈ l, p x = false := by
  rw [List.any_eq_false]
  constructor
  · intro h x hx
    cases hpx : p x with
    | false => rfl
    | true => exact absurd hpx (h x hx)
  · intro h x hx hpx
    rw [h x hx] at hpx
    cases hpx

/-- A successful `list[i]` (`listIndex`) found its result at position `i.toNat`. -/
theorem listIndex_eq_ok {T : Type} {xs : List T} {i : Int} {what : String} {x : T}
    (h : listIndex xs i what = .ok x) : xs[i.toNat]? = some x := by
  unfold listIndex at h
  split at h
  · generalize xs[i.toNat]? = opt at h
    cases opt with
    | none => cases h
    | some elem =>
      dsimp only at h
      obtain rfl := interp_pure_eq_ok h
      rfl
  · cases h

/-- A successful `List::set(i, x)` (`listSet`) is `List.set` at position `i.toNat`. -/
theorem listSet_eq_ok {T : Type} {xs ys : List T} {i : Int} {x : T} {what : String}
    (h : listSet xs i x what = .ok ys) : ys = xs.set i.toNat x := by
  unfold listSet at h
  split at h
  · exact (interp_pure_eq_ok h).symm
  · cases h

/-- The four atomic memory intrinsics of `spec/lang/step/intrinsics.md`. -/
def isAtomicOp : IntrinsicOp → Bool
  | .AtomicStore | .AtomicLoad | .AtomicCompareExchange | .AtomicFetchAndOp _ => true
  | _ => false

/-! ## §1. Structural `Value` equality, determinism, and `BasicMemory` equivalence -/

section ValueEq

variable {M : Type} [Memory M] (decEq : DecidableEq (Memory.Provenance M))

mutual

/-- `valueEqWith` is reflexive. -/
theorem valueEqWith_refl : ∀ (v : Value M), valueEqWith decEq v v = true
  | .Int i => by simp only [valueEqWith, beq_self_eq_true]
  | .Bool b => by simp only [valueEqWith, beq_self_eq_true]
  | .Ptr p => by simp only [valueEqWith, decide_true]
  | .Tuple vs => by simp only [valueEqWith, valueListEqWith_refl vs]
  | .Variant d v => by
    simp only [valueEqWith, beq_self_eq_true, valueEqWith_refl v, Bool.and_self]
  | .Union c => by simp only [valueEqWith, decide_true]

/-- `valueListEqWith` is reflexive. -/
theorem valueListEqWith_refl : ∀ (l : List (Value M)), valueListEqWith decEq l l = true
  | [] => by simp only [valueListEqWith]
  | v :: r => by
    simp only [valueListEqWith, valueEqWith_refl v, valueListEqWith_refl r, Bool.and_self]

end

mutual

/-- `valueEqWith` only identifies equal values. -/
theorem valueEqWith_sound :
    ∀ (v1 v2 : Value M), valueEqWith decEq v1 v2 = true → v1 = v2
  | .Int i1, v2 => by
    cases v2 <;>
      simp only [valueEqWith, Bool.false_eq_true, reduceCtorEq, imp_self, beq_iff_eq,
        Value.Int.injEq]
  | .Bool b1, v2 => by
    cases v2 <;>
      simp only [valueEqWith, Bool.false_eq_true, reduceCtorEq, imp_self, beq_iff_eq,
        Value.Bool.injEq]
  | .Ptr p1, v2 => by
    cases v2 <;>
      simp only [valueEqWith, Bool.false_eq_true, reduceCtorEq, imp_self, decide_eq_true_eq,
        Value.Ptr.injEq]
  | .Tuple vs1, v2 => by
    cases v2 <;>
      simp only [valueEqWith, Bool.false_eq_true, reduceCtorEq, imp_self, Value.Tuple.injEq]
    exact valueListEqWith_sound vs1 _
  | .Variant d1 w1, v2 => by
    cases v2 <;>
      simp only [valueEqWith, Bool.false_eq_true, reduceCtorEq, imp_self, Bool.and_eq_true,
        beq_iff_eq, Value.Variant.injEq, and_imp]
    intro hd h
    exact ⟨hd, valueEqWith_sound w1 _ h⟩
  | .Union c1, v2 => by
    cases v2 <;>
      simp only [valueEqWith, Bool.false_eq_true, reduceCtorEq, imp_self, decide_eq_true_eq,
        Value.Union.injEq]

/-- `valueListEqWith` only identifies equal value lists. -/
theorem valueListEqWith_sound :
    ∀ (l1 l2 : List (Value M)), valueListEqWith decEq l1 l2 = true → l1 = l2
  | [], l2 => by
    cases l2 <;> simp only [valueListEqWith, Bool.false_eq_true, reduceCtorEq, imp_self]
  | v1 :: r1, l2 => by
    cases l2 with
    | nil => simp only [valueListEqWith, Bool.false_eq_true, reduceCtorEq, imp_self]
    | cons v2 r2 =>
      simp only [valueListEqWith, Bool.and_eq_true]
      intro h
      rw [valueEqWith_sound v1 v2 h.1, valueListEqWith_sound r1 r2 h.2]

end

/-- `valueEqWith` decides equality of `Value<M>`, whatever decision procedure
for `M::Provenance` it is given. -/
theorem valueEqWith_eq_true_iff (v1 v2 : Value M) :
    valueEqWith decEq v1 v2 = true ↔ v1 = v2 :=
  ⟨valueEqWith_sound decEq v1 v2, fun h => h ▸ valueEqWith_refl decEq v1⟩

end ValueEq

section ValueEqM

variable {M : Type} [Memory M] [MemoryOps M]

/-- `current == before` holds of a value and itself. -/
theorem valueEqM_refl (v : Value M) : valueEqM v v = true :=
  valueEqWith_refl MemoryOps.decEqProv v

/-- `current == before` (`valueEqM`) is exactly equality of `Value<M>`. -/
theorem valueEqM_eq_true_iff (v1 v2 : Value M) : valueEqM v1 v2 = true ↔ v1 = v2 :=
  valueEqWith_eq_true_iff MemoryOps.decEqProv v1 v2

/-- `current != before` (`valueEqM` is `false`) is exactly disequality. -/
theorem valueEqM_eq_false_iff (v1 v2 : Value M) : valueEqM v1 v2 = false ↔ v1 ≠ v2 := by
  constructor
  · intro h heq
    rw [(valueEqM_eq_true_iff v1 v2).mpr heq] at h
    cases h
  · intro hne
    cases hb : valueEqM v1 v2 with
    | false => rfl
    | true => exact absurd ((valueEqM_eq_true_iff v1 v2).mp hb) hne

/-- Decidable equality of `Value<M>`, by `valueEqM`. The generated `Value` has
no derived instance because it is nested through `List (Value M)`. -/
instance instDecidableEqValue : DecidableEq (Value M) := fun v1 v2 =>
  decidable_of_iff _ (valueEqM_eq_true_iff v1 v2)

end ValueEqM

/-- `current == before` holds of a `Value<BasicMemory<x86_64>>` and itself. -/
theorem valueEq_refl (v : Val) : valueEq v v = true :=
  valueEqWith_refl _ v

/-- `current == before` (`valueEq`) is exactly equality of `Val`. -/
theorem valueEq_eq_true_iff (v1 v2 : Val) : valueEq v1 v2 = true ↔ v1 = v2 :=
  valueEqWith_eq_true_iff _ v1 v2

/-- `current != before` (`valueEq` is `false`) is exactly disequality of `Val`. -/
theorem valueEq_eq_false_iff (v1 v2 : Val) : valueEq v1 v2 = false ↔ v1 ≠ v2 :=
  valueEqM_eq_false_iff (M := BM) v1 v2

/-- At `M = BasicMemory<x86_64>` the polymorphic comparison is `valueEq`. -/
theorem valueEqM_bm_eq (v1 v2 : Val) : valueEqM (M := BM) v1 v2 = valueEq v1 v2 := rfl

section Determinism

variable {M : Type} [Memory M] [MemoryOps M]

/-- `Machine::eval_intrinsic` is a function into `Result`: an intrinsic has
exactly one outcome, either one `(value, machine)` pair or one `Stop`. The
only non-determinism of upstream's `NdResult` reachable from the atomic
intrinsics is none at all: they `pick` nothing. -/
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

/-! ### `BasicMemory` equivalence of the atomic intrinsics

`evalIntrinsic` transcribes `Machine::eval_intrinsic` at `M =
BasicMemory<x86_64>`, and `evalIntrinsicM` transcribes it for every `M`. On the
four atomic intrinsics the two agree as soon as `Machine::typed_load` and
`Machine::typed_store` do, and those agree as soon as the representation
relation and `check_value` do. -/

section BmEq

/-- `Machine::typed_load` at `M = BasicMemory<x86_64>` is `typedLoad`, given
that the polymorphic `Type::decode` and `check_value` agree with the
`BasicMemory` ones. -/
theorem typedLoadM_bm_eq_of_codec
    (hdec : ∀ (ty : «Type») (bs : List Byte), Type.decodeM (M := BM) ty bs = Type.decode ty bs)
    (hchk : ∀ (val : Val) (ty : «Type») (m : Option Mach),
      checkValueM (M := BM) val ty m = checkValue val ty m)
    (m : Mach) (ptr : Ptr) (ty : «Type») (align : Align) (atomicity : Atomicity) :
    typedLoadM (M := BM) m ptr ty align atomicity = typedLoad m ptr ty align atomicity := by
  unfold typedLoadM typedLoad
  refine interp_bind_congr rfl (fun _ => ?_)
  refine interp_bind_congr rfl (fun sz => ?_)
  refine interp_bind_congr (y := CM.load m.mem ptr sz align atomicity) rfl (fun ⟨bs, cm⟩ => ?_)
  dsimp only
  refine interp_bind_congr (hdec ty bs) (fun optVal => ?_)
  cases optVal with
  | none => rfl
  | some val =>
    dsimp only
    exact interp_bind_congr (hchk val ty (some { m with mem := cm })) (fun _ => rfl)

/-- `Machine::typed_store` at `M = BasicMemory<x86_64>` is `typedStore`, given
that the polymorphic `Type::encode` and `check_value` agree with the
`BasicMemory` ones. -/
theorem typedStoreM_bm_eq_of_codec
    (henc : ∀ (ty : «Type») (val : Val), Type.encodeM (M := BM) ty val = Type.encode ty val)
    (hchk : ∀ (val : Val) (ty : «Type») (m : Option Mach),
      checkValueM (M := BM) val ty m = checkValue val ty m)
    (m : Mach) (ptr : Ptr) (val : Val) (ty : «Type») (align : Align) (atomicity : Atomicity) :
    typedStoreM (M := BM) m ptr val ty align atomicity =
      typedStore m ptr val ty align atomicity := by
  unfold typedStoreM typedStore
  dsimp only
  rw [hchk]
  cases checkValue val ty (some m) with
  | error _ => rfl
  | ok _ =>
    dsimp only
    refine interp_bind_congr (henc ty val) (fun bs => ?_)
    exact interp_bind_congr (y := CM.store m.mem ptr bs align atomicity) rfl (fun _ => rfl)

/-- On the four atomic intrinsics, `evalIntrinsicM` at `M = BasicMemory<x86_64>`
is `evalIntrinsic`, given that `typed_load` and `typed_store` agree there. -/
theorem evalIntrinsicM_bm_eq_atomic_of_typed
    (hL : ∀ (m : Mach) (ptr : Ptr) (ty : «Type») (align : Align) (atomicity : Atomicity),
      typedLoadM (M := BM) m ptr ty align atomicity = typedLoad m ptr ty align atomicity)
    (hS : ∀ (m : Mach) (ptr : Ptr) (val : Val) (ty : «Type») (align : Align)
      (atomicity : Atomicity),
      typedStoreM (M := BM) m ptr val ty align atomicity =
        typedStore m ptr val ty align atomicity)
    (m : Mach) (op : IntrinsicOp) (args : List (Val × «Type»)) (retTy : «Type»)
    (hop : isAtomicOp op = true) :
    evalIntrinsicM (M := BM) m op args retTy = evalIntrinsic m op args retTy := by
  have hL' : @typedLoadM BM _ _ = typedLoad := by
    funext m ptr ty align atomicity
    exact hL m ptr ty align atomicity
  have hS' : @typedStoreM BM _ _ = typedStore := by
    funext m ptr val ty align atomicity
    exact hS m ptr val ty align atomicity
  unfold evalIntrinsicM evalIntrinsic
  cases op with
  | AtomicStore =>
    simp only [hS']
    rcases args with _ | ⟨⟨ptrV, _⟩, _ | ⟨⟨val, ty⟩, _ | ⟨_, _⟩⟩⟩ <;> try rfl
    rcases ptrV with _ | _ | ⟨ptr, _ | _⟩ | _ | _ <;> rfl
  | AtomicLoad =>
    simp only [hL']
    rcases args with _ | ⟨⟨ptrV, _⟩, _ | ⟨_, _⟩⟩ <;> try rfl
    rcases ptrV with _ | _ | ⟨ptr, _ | _⟩ | _ | _ <;> rfl
  | AtomicCompareExchange =>
    simp only [hL', hS']
    rcases args with
      _ | ⟨⟨ptrV, _⟩, _ | ⟨⟨current, currTy⟩, _ | ⟨⟨next, nextTy⟩, _ | ⟨_, _⟩⟩⟩⟩ <;> try rfl
    rcases ptrV with _ | _ | ⟨ptr, _ | _⟩ | _ | _ <;> rfl
  | AtomicFetchAndOp binOp =>
    simp only [hL', hS']
    rcases args with _ | ⟨⟨ptrV, _⟩, _ | ⟨⟨other, otherTy⟩, _ | ⟨_, _⟩⟩⟩ <;> try rfl
    rcases ptrV with _ | _ | ⟨ptr, _ | _⟩ | _ | _ <;> try rfl
    rcases other with _ | _ | _ | _ | _ | _ <;> try rfl
    dsimp only
    split
    · rfl
    · cases retTy <;> try rfl
      refine interp_bind_congr rfl (fun _ => ?_)
      refine interp_bind_congr rfl (fun _ => ?_)
      split <;> try rfl
      split <;> try rfl
      refine interp_bind_congr rfl (fun x => ?_)
      rcases x with ⟨previous, m1⟩
      cases previous <;> rfl
  | _ => exact Bool.noConfusion hop

end BmEq

/-! `MiniRustSpec.Correspondence.Pointers` proves these hypotheses for every
type and value (`Type.decodeM_bm_eq`, `Type.encodeM_bm_eq`,
`checkValueM_bm_eq`), so the equivalence holds unconditionally. -/

/-- `Machine::typed_load` at `M = BasicMemory<x86_64>` is `typedLoad`. -/
theorem typedLoadM_bm_eq_typedLoad (m : Mach) (ptr : Ptr) (ty : «Type») (align : Align)
    (atomicity : Atomicity) :
    typedLoadM (M := BM) m ptr ty align atomicity = typedLoad m ptr ty align atomicity :=
  typedLoadM_bm_eq_of_codec MiniRustSpec.Correspondence.Type.decodeM_bm_eq
    MiniRustSpec.Correspondence.checkValueM_bm_eq m ptr ty align atomicity

/-- `Machine::typed_store` at `M = BasicMemory<x86_64>` is `typedStore`. -/
theorem typedStoreM_bm_eq_typedStore (m : Mach) (ptr : Ptr) (val : Val) (ty : «Type»)
    (align : Align) (atomicity : Atomicity) :
    typedStoreM (M := BM) m ptr val ty align atomicity =
      typedStore m ptr val ty align atomicity :=
  typedStoreM_bm_eq_of_codec MiniRustSpec.Correspondence.Type.encodeM_bm_eq
    MiniRustSpec.Correspondence.checkValueM_bm_eq m ptr val ty align atomicity

/-- On the four atomic intrinsics, the polymorphic `evalIntrinsicM` at
`M = BasicMemory<x86_64>` is the `BasicMemory` transcription `evalIntrinsic`.
Every law of §2 and §3, stated for `evalIntrinsicM` in every memory model,
therefore holds of `evalIntrinsic` on `Mach`. -/
theorem evalIntrinsicM_bm_eq_atomic (m : Mach) (op : IntrinsicOp)
    (args : List (Val × «Type»)) (retTy : «Type») (hop : isAtomicOp op = true) :
    evalIntrinsicM (M := BM) m op args retTy = evalIntrinsic m op args retTy :=
  evalIntrinsicM_bm_eq_atomic_of_typed typedLoadM_bm_eq_typedLoad typedStoreM_bm_eq_typedStore
    m op args retTy hop

/-- `evalIntrinsicM_bm_eq_atomic`, spelled out for each of the four atomic
intrinsics. -/
theorem evalIntrinsicM_bm_eq_atomic_each (m : Mach) (args : List (Val × «Type»))
    (retTy : «Type») (binOp : IntBinOp) :
    evalIntrinsicM (M := BM) m .AtomicStore args retTy =
      evalIntrinsic m .AtomicStore args retTy ∧
    evalIntrinsicM (M := BM) m .AtomicLoad args retTy =
      evalIntrinsic m .AtomicLoad args retTy ∧
    evalIntrinsicM (M := BM) m .AtomicCompareExchange args retTy =
      evalIntrinsic m .AtomicCompareExchange args retTy ∧
    evalIntrinsicM (M := BM) m (.AtomicFetchAndOp binOp) args retTy =
      evalIntrinsic m (.AtomicFetchAndOp binOp) args retTy :=
  ⟨evalIntrinsicM_bm_eq_atomic m .AtomicStore args retTy rfl,
   evalIntrinsicM_bm_eq_atomic m .AtomicLoad args retTy rfl,
   evalIntrinsicM_bm_eq_atomic m .AtomicCompareExchange args retTy rfl,
   evalIntrinsicM_bm_eq_atomic m (.AtomicFetchAndOp binOp) args retTy rfl⟩

/-! ## §2. What an atomic intrinsic does to the machine

A successful atomic intrinsic changes the machine only through
`Machine::typed_load` and `Machine::typed_store` at `Atomicity::Atomic`: one
store (`AtomicStore`), one load (`AtomicLoad`, a failing
`AtomicCompareExchange`), or a load followed by a store (a succeeding
`AtomicCompareExchange`, `AtomicFetchAndOp`). Every invariant those two
preserve is therefore preserved by all four intrinsics, in every memory model. -/

section Effect

variable {M : Type} [Memory M] [MemoryOps M]

/-- The three ways a successful atomic intrinsic that returned `val` can have
taken the machine from `m` to `m'`. -/
inductive AtomicEffect (m : Machine M) (val : Value M) (m' : Machine M) : Prop where
  /-- `AtomicStore`: one atomic typed store, returning `()`. -/
  | store (ptr : ThinPointer (Memory.Provenance M)) (v : Value M) (ty : «Type») (align : Align)
      (hs : typedStoreM m ptr v ty align .Atomic = .ok m') (hv : val = unitValueM)
  /-- `AtomicLoad` and a failing `AtomicCompareExchange`: one atomic typed
  load, returning the loaded value. -/
  | load (ptr : ThinPointer (Memory.Provenance M)) (ty : «Type») (align : Align)
      (hl : typedLoadM m ptr ty align .Atomic = .ok (val, m'))
  /-- A succeeding `AtomicCompareExchange` and `AtomicFetchAndOp`: one atomic
  typed load, returning the loaded value, then one atomic typed store through
  the same pointer at the same type. -/
  | loadStore (ptr : ThinPointer (Memory.Provenance M)) (ty : «Type») (align : Align)
      (v : Value M) (m1 : Machine M)
      (hl : typedLoadM m ptr ty align .Atomic = .ok (val, m1))
      (hs : typedStoreM m1 ptr v ty align .Atomic = .ok m')

/-- Inversion of a successful atomic intrinsic into its `AtomicEffect`. -/
theorem evalIntrinsicM_atomic_ok_inv {m m' : Machine M} {op : IntrinsicOp}
    {args : List (Value M × «Type»)} {retTy : «Type»} {val : Value M}
    (hop : isAtomicOp op = true)
    (h : evalIntrinsicM m op args retTy = .ok (val, m')) : AtomicEffect m val m' := by
  cases op with
  | AtomicStore =>
    dsimp only [evalIntrinsicM] at h
    repeat' split at h
    all_goals first
      | (dsimp only [ub] at h; cases h)
      | (obtain ⟨_, _, h⟩ := interp_bind_eq_ok h
         repeat' split at h
         all_goals first
           | (dsimp only [ub] at h; cases h)
           | (obtain ⟨_, hs, h⟩ := interp_bind_eq_ok h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok h)
              exact .store _ _ _ _ hs rfl))
  | AtomicLoad =>
    dsimp only [evalIntrinsicM] at h
    repeat' split at h
    all_goals first
      | (dsimp only [ub] at h; cases h)
      | (obtain ⟨_, _, h⟩ := interp_bind_eq_ok h
         obtain ⟨_, _, h⟩ := interp_bind_eq_ok h
         repeat' split at h
         all_goals first
           | (dsimp only [ub] at h; cases h)
           | exact .load _ _ _ h)
  | AtomicCompareExchange =>
    dsimp only [evalIntrinsicM] at h
    repeat' split at h
    all_goals first
      | (dsimp only [ub] at h; cases h)
      | (obtain ⟨_, _, h⟩ := interp_bind_eq_ok h
         obtain ⟨_, _, h⟩ := interp_bind_eq_ok h
         repeat' split at h
         all_goals first
           | (dsimp only [ub, specPanic] at h; cases h)
           | (obtain ⟨⟨_, m1⟩, hl, h⟩ := interp_bind_eq_ok h
              try dsimp only at h
              split at h
              · obtain ⟨_, hs, h⟩ := interp_bind_eq_ok h
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok h)
                exact .loadStore _ _ _ _ _ hl hs
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok h)
                exact .load _ _ _ hl))
  | AtomicFetchAndOp binOp =>
    dsimp only [evalIntrinsicM] at h
    repeat' split at h
    all_goals first
      | (dsimp only [ub] at h; cases h)
      | (obtain ⟨_, _, h⟩ := interp_bind_eq_ok h
         obtain ⟨_, _, h⟩ := interp_bind_eq_ok h
         repeat' split at h
         all_goals first
           | (dsimp only [ub, specPanic] at h; cases h)
           | (obtain ⟨⟨_, m1⟩, hl, h⟩ := interp_bind_eq_ok h
              try dsimp only at h
              repeat' split at h
              all_goals first
                | (dsimp only [specPanic] at h; cases h)
                | (obtain ⟨_, _, h⟩ := interp_bind_eq_ok h
                   obtain ⟨_, hs, h⟩ := interp_bind_eq_ok h
                   obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok h)
                   exact .loadStore _ _ _ _ _ hl hs)))
  | _ => exact Bool.noConfusion hop

/-- Every machine invariant preserved by atomic `typed_load` and `typed_store`
is preserved by all four atomic intrinsics. -/
theorem evalIntrinsicM_atomic_preserves {P : Machine M → Prop}
    (hL : ∀ {m m' : Machine M} {ptr : ThinPointer (Memory.Provenance M)} {ty : «Type»}
      {align : Align} {val : Value M},
      P m → typedLoadM m ptr ty align .Atomic = .ok (val, m') → P m')
    (hS : ∀ {m m' : Machine M} {ptr : ThinPointer (Memory.Provenance M)} {val : Value M}
      {ty : «Type»} {align : Align},
      P m → typedStoreM m ptr val ty align .Atomic = .ok m' → P m')
    {m m' : Machine M} {op : IntrinsicOp} {args : List (Value M × «Type»)} {retTy : «Type»}
    {val : Value M} (hop : isAtomicOp op = true) (hP : P m)
    (h : evalIntrinsicM m op args retTy = .ok (val, m')) : P m' := by
  cases evalIntrinsicM_atomic_ok_inv hop h with
  | store ptr v ty align hs _ => exact hS hP hs
  | load ptr ty align hl => exact hL hP hl
  | loadStore ptr ty align v m1 hl hs => exact hS (hL hP hl) hs

/-- A successful `typed_load` appends exactly one `Load` access of the type's
size at the pointer's address, with the requested atomicity. -/
theorem typedLoadM_ok_accesses {m m' : Machine M} {ptr : ThinPointer (Memory.Provenance M)}
    {ty : «Type»} {align : Align} {atomicity : Atomicity} {val : Value M}
    (h : typedLoadM m ptr ty align atomicity = .ok (val, m')) :
    ∃ size a, Type.layout ty = .ok (.Sized size a) ∧
      m'.mem.accesses = m.mem.accesses ++ [⟨.Load, atomicity, ptr.addr, size⟩] := by
  unfold typedLoadM at h
  obtain ⟨l, hl, h⟩ := interp_bind_eq_ok h
  obtain ⟨size, hsz, h⟩ := interp_bind_eq_ok h
  obtain ⟨⟨bytes, cm⟩, hload, h⟩ := interp_bind_eq_ok h
  dsimp only at h
  unfold ConcurrentMemory.load at hload
  obtain ⟨⟨bytes', mem'⟩, _, hload⟩ := interp_bind_eq_ok hload
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok hload)
  obtain ⟨opt, _, h⟩ := interp_bind_eq_ok h
  cases opt with
  | none => cases h
  | some v =>
    obtain ⟨_, _, h⟩ := interp_bind_eq_ok h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok h)
    cases l with
    | Sized s a =>
      obtain rfl := interp_pure_eq_ok hsz
      exact ⟨s, a, hl, rfl⟩
    | _ => cases hsz

/-- A successful `typed_store` appends exactly one `Store` access of the
encoded length at the pointer's address, with the requested atomicity. -/
theorem typedStoreM_ok_accesses {m m' : Machine M} {ptr : ThinPointer (Memory.Provenance M)}
    {val : Value M} {ty : «Type»} {align : Align} {atomicity : Atomicity}
    (h : typedStoreM m ptr val ty align atomicity = .ok m') :
    ∃ bytes, Type.encodeM ty val = .ok bytes ∧
      m'.mem.accesses = m.mem.accesses ++ [⟨.Store, atomicity, ptr.addr, ⟨bytes.length⟩⟩] := by
  unfold typedStoreM at h
  dsimp only at h
  rcases hcv : checkValueM val ty (some m) with _ | ⟨⟩
  · simp only [hcv] at h
    cases h
  · simp only [hcv] at h
    obtain ⟨bytes, henc, h⟩ := interp_bind_eq_ok h
    obtain ⟨cm, hstore, h⟩ := interp_bind_eq_ok h
    obtain rfl := interp_pure_eq_ok h
    unfold ConcurrentMemory.store at hstore
    obtain ⟨mem', _, hstore⟩ := interp_bind_eq_ok hstore
    obtain rfl := interp_pure_eq_ok hstore
    exact ⟨bytes, henc, rfl⟩

/-- What a successful `typed_load` does to memory and where its value comes
from: the memory of the resulting machine is the one that the memory model's
`load` returned, and the value is the decoding of exactly the bytes that this
`load` read. `typed_load` itself never writes a byte. -/
theorem typedLoadM_ok_memory {m m' : Machine M} {ptr : ThinPointer (Memory.Provenance M)}
    {ty : «Type»} {align : Align} {atomicity : Atomicity} {val : Value M}
    (h : typedLoadM m ptr ty align atomicity = .ok (val, m')) :
    ∃ size a bytes, Type.layout ty = .ok (.Sized size a) ∧
      MemoryOps.load m.mem.memory ptr size align = .ok (bytes, m'.mem.memory) ∧
      Type.decodeM (M := M) ty bytes = .ok (some val) := by
  unfold typedLoadM at h
  obtain ⟨l, hl, h⟩ := interp_bind_eq_ok h
  obtain ⟨size, hsz, h⟩ := interp_bind_eq_ok h
  obtain ⟨⟨bytes, cm⟩, hload, h⟩ := interp_bind_eq_ok h
  dsimp only at h
  unfold ConcurrentMemory.load at hload
  obtain ⟨⟨bytes', mem'⟩, hmem, hload⟩ := interp_bind_eq_ok hload
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok hload)
  obtain ⟨opt, hdec, h⟩ := interp_bind_eq_ok h
  cases opt with
  | none => cases h
  | some v =>
    obtain ⟨_, _, h⟩ := interp_bind_eq_ok h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok h)
    cases l with
    | Sized s a =>
      obtain rfl := interp_pure_eq_ok hsz
      exact ⟨s, a, _, hl, hmem, hdec⟩
    | _ => cases hsz

/-- What a successful `typed_store` does to memory: the memory of the resulting
machine is what the memory model's `store` made of the encoding of the stored
value. Nothing else of the value reaches memory; in particular, provenance
reaches memory only if `Type::encode` puts it into the bytes. -/
theorem typedStoreM_ok_memory {m m' : Machine M} {ptr : ThinPointer (Memory.Provenance M)}
    {val : Value M} {ty : «Type»} {align : Align} {atomicity : Atomicity}
    (h : typedStoreM m ptr val ty align atomicity = .ok m') :
    ∃ bytes, Type.encodeM (M := M) ty val = .ok bytes ∧
      MemoryOps.store m.mem.memory ptr bytes align = .ok m'.mem.memory := by
  unfold typedStoreM at h
  dsimp only at h
  rcases hcv : checkValueM val ty (some m) with _ | ⟨⟩
  · simp only [hcv] at h
    cases h
  · simp only [hcv] at h
    obtain ⟨bytes, henc, h⟩ := interp_bind_eq_ok h
    obtain ⟨cm, hstore, h⟩ := interp_bind_eq_ok h
    obtain rfl := interp_pure_eq_ok h
    unfold ConcurrentMemory.store at hstore
    obtain ⟨mem', hmem, hstore⟩ := interp_bind_eq_ok hstore
    obtain rfl := interp_pure_eq_ok hstore
    exact ⟨bytes, henc, hmem⟩

/-- Every access that a successful atomic intrinsic records is
`Atomicity::Atomic` and is at one address: the access log grows by one or two
entries, all atomic. In particular no atomic intrinsic records a non-atomic
access, which is what `Access::races` needs to exempt atomic-atomic pairs. -/
theorem evalIntrinsicM_atomic_accesses {m m' : Machine M} {op : IntrinsicOp}
    {args : List (Value M × «Type»)} {retTy : «Type»} {val : Value M}
    (hop : isAtomicOp op = true)
    (h : evalIntrinsicM m op args retTy = .ok (val, m')) :
    ∃ (addr : Address) (log : List Access),
      m'.mem.accesses = m.mem.accesses ++ log ∧ 1 ≤ log.length ∧ log.length ≤ 2 ∧
      ∀ a ∈ log, a.atomicity = .Atomic ∧ a.addr = addr := by
  cases evalIntrinsicM_atomic_ok_inv hop h with
  | store ptr v ty align hs _ =>
    obtain ⟨bytes, _, hacc⟩ := typedStoreM_ok_accesses hs
    refine ⟨ptr.addr, _, hacc, Nat.le_refl 1, Nat.le_succ 1, ?_⟩
    intro a ha
    cases ha with
    | head => exact ⟨rfl, rfl⟩
    | tail _ ha => cases ha
  | load ptr ty align hl =>
    obtain ⟨size, _, _, hacc⟩ := typedLoadM_ok_accesses hl
    refine ⟨ptr.addr, _, hacc, Nat.le_refl 1, Nat.le_succ 1, ?_⟩
    intro a ha
    cases ha with
    | head => exact ⟨rfl, rfl⟩
    | tail _ ha => cases ha
  | loadStore ptr ty align v m1 hl hs =>
    obtain ⟨size, _, _, hacc1⟩ := typedLoadM_ok_accesses hl
    obtain ⟨bytes, _, hacc2⟩ := typedStoreM_ok_accesses hs
    refine ⟨ptr.addr, [⟨.Load, .Atomic, ptr.addr, size⟩, ⟨.Store, .Atomic, ptr.addr, ⟨bytes.length⟩⟩],
      ?_, Nat.le_succ 1, Nat.le_refl 2, ?_⟩
    · rw [hacc2, hacc1, List.append_assoc]
      rfl
    · intro a ha
      cases ha with
      | head => exact ⟨rfl, rfl⟩
      | tail _ ha =>
        cases ha with
        | head => exact ⟨rfl, rfl⟩
        | tail _ ha => cases ha

end Effect

/-! ### `MachTB.wfLive` preservation

`MiniRustSpec.Correspondence.Pointers` proves that `typed_load` and
`typed_store` preserve the Tree Borrows live-allocation invariant
`MachTB.wfLive` (every live allocation has a well-formed borrow tree), so all
four atomic intrinsics do. `atomicStore_tb_wfLive_witness` in §5 shows that the
statement is not vacuous. -/

/-- All four atomic intrinsics preserve the Tree Borrows live-allocation
invariant `MachTB.wfLive` on `Machine<TreeBorrowsMemory<x86_64>>`: every live
allocation keeps a well-formed borrow tree. -/
theorem evalIntrinsicM_atomic_tb_wfLive {m m' : MachTB} {op : IntrinsicOp}
    {args : List (Value TBM × «Type»)} {retTy : «Type»} {val : Value TBM}
    (hop : isAtomicOp op = true)
    (hwf : MiniRustSpec.Correspondence.MachTB.wfLive m)
    (h : evalIntrinsicM m op args retTy = .ok (val, m')) :
    MiniRustSpec.Correspondence.MachTB.wfLive m' :=
  evalIntrinsicM_atomic_preserves (P := MiniRustSpec.Correspondence.MachTB.wfLive)
    (fun hP hl => MiniRustSpec.Correspondence.typedLoadM_tb_wfLive hP hl)
    (fun hP hs => MiniRustSpec.Correspondence.typedStoreM_tb_wfLive hP hs) hop hwf h

/-- `evalIntrinsicM_atomic_tb_wfLive`, spelled out for each of the four atomic
intrinsics. -/
theorem evalIntrinsicM_atomic_tb_wfLive_each {m m' : MachTB}
    {args : List (Value TBM × «Type»)} {retTy : «Type»} {val : Value TBM} (binOp : IntBinOp)
    (hwf : MiniRustSpec.Correspondence.MachTB.wfLive m) :
    (evalIntrinsicM m .AtomicStore args retTy = .ok (val, m') →
      MiniRustSpec.Correspondence.MachTB.wfLive m') ∧
    (evalIntrinsicM m .AtomicLoad args retTy = .ok (val, m') →
      MiniRustSpec.Correspondence.MachTB.wfLive m') ∧
    (evalIntrinsicM m .AtomicCompareExchange args retTy = .ok (val, m') →
      MiniRustSpec.Correspondence.MachTB.wfLive m') ∧
    (evalIntrinsicM m (.AtomicFetchAndOp binOp) args retTy = .ok (val, m') →
      MiniRustSpec.Correspondence.MachTB.wfLive m') :=
  ⟨fun h => evalIntrinsicM_atomic_tb_wfLive (op := .AtomicStore) rfl hwf h,
   fun h => evalIntrinsicM_atomic_tb_wfLive (op := .AtomicLoad) rfl hwf h,
   fun h => evalIntrinsicM_atomic_tb_wfLive (op := .AtomicCompareExchange) rfl hwf h,
   fun h => evalIntrinsicM_atomic_tb_wfLive (op := .AtomicFetchAndOp binOp) rfl hwf h⟩

/-! ## §3. Undefined behavior and spec panics of the atomic intrinsics

The laws of this section hold in every memory model `M`: they are decided by
the shape of the arguments and of the types before any memory access. -/

/-- `IntType` of `u8`. -/
@[reducible] def itU8 : IntType := ⟨.Unsigned, ⟨1⟩⟩
/-- `IntType` of `u16`. -/
@[reducible] def itU16 : IntType := ⟨.Unsigned, ⟨2⟩⟩
/-- `IntType` of `u32`. -/
@[reducible] def itU32 : IntType := ⟨.Unsigned, ⟨4⟩⟩
/-- `IntType` of `u64`, which is also `usize` on `x86_64`. -/
@[reducible] def itU64 : IntType := ⟨.Unsigned, ⟨8⟩⟩
/-- `IntType` of `i32`. -/
@[reducible] def itI32 : IntType := ⟨.Signed, ⟨4⟩⟩
/-- `IntType` of `i64`. -/
@[reducible] def itI64 : IntType := ⟨.Signed, ⟨8⟩⟩
/-- `IntType` of `u128`, twice `x86_64::MAX_ATOMIC_SIZE`. -/
@[reducible] def itU128 : IntType := ⟨.Unsigned, ⟨16⟩⟩
/-- A thin raw pointer type such as `*const u32` (`PtrType::Raw` records only
the metadata kind). -/
@[reducible] def tyRawPtr : «Type» := .Ptr (.Raw .None)

section Guards

variable {M : Type} [Memory M] [MemoryOps M]

/-! ### Arity -/

/-- `AtomicStore` takes exactly two arguments. -/
theorem atomicStore_arity_ub (m : Machine M) (args : List (Value M × «Type»)) (retTy : «Type»)
    (h : args.length ≠ 2) :
    evalIntrinsicM m .AtomicStore args retTy =
      .error (.ub "invalid number of arguments for `AtomicStore` intrinsic") := by
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rfl
  · rfl
  · exact absurd rfl h
  · rfl

/-- `AtomicLoad` takes exactly one argument. -/
theorem atomicLoad_arity_ub (m : Machine M) (args : List (Value M × «Type»)) (retTy : «Type»)
    (h : args.length ≠ 1) :
    evalIntrinsicM m .AtomicLoad args retTy =
      .error (.ub "invalid number of arguments for `AtomicLoad` intrinsic") := by
  rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · rfl
  · exact absurd rfl h
  · rfl

/-- `AtomicCompareExchange` takes exactly three arguments. -/
theorem atomicCompareExchange_arity_ub (m : Machine M) (args : List (Value M × «Type»))
    (retTy : «Type») (h : args.length ≠ 3) :
    evalIntrinsicM m .AtomicCompareExchange args retTy =
      .error (.ub "invalid number of arguments for `AtomicCompareExchange` intrinsic") := by
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩
  · rfl
  · rfl
  · rfl
  · exact absurd rfl h
  · rfl

/-- `AtomicFetchAndOp` takes exactly two arguments, whatever its operator. -/
theorem atomicFetchAndOp_arity_ub (m : Machine M) (binOp : IntBinOp)
    (args : List (Value M × «Type»)) (retTy : «Type») (h : args.length ≠ 2) :
    evalIntrinsicM m (.AtomicFetchAndOp binOp) args retTy =
      .error (.ub "invalid number of arguments for `AtomicFetchAndOp` intrinsic") := by
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rfl
  · rfl
  · exact absurd rfl h
  · rfl

/-! ### The first argument must be a thin pointer -/

/-- `AtomicStore` through anything but a thin pointer is UB. -/
theorem atomicStore_not_thin_ptr_ub (m : Machine M) (ptrV : Value M) (pty : «Type»)
    (v : Value M) (ty retTy : «Type») (h : ∀ p, ptrV ≠ .Ptr ⟨p, none⟩) :
    evalIntrinsicM m .AtomicStore [(ptrV, pty), (v, ty)] retTy =
      .error (.ub "invalid first argument to `AtomicStore` intrinsic: not a thin pointer") := by
  rcases ptrV with _ | _ | ⟨p, _ | _⟩ | _ | _ | _
  all_goals first | rfl | exact absurd rfl (h _)

/-- `AtomicLoad` through anything but a thin pointer is UB. -/
theorem atomicLoad_not_thin_ptr_ub (m : Machine M) (ptrV : Value M) (pty retTy : «Type»)
    (h : ∀ p, ptrV ≠ .Ptr ⟨p, none⟩) :
    evalIntrinsicM m .AtomicLoad [(ptrV, pty)] retTy =
      .error (.ub "invalid first argument to `AtomicLoad` intrinsic: not a thin pointer") := by
  rcases ptrV with _ | _ | ⟨p, _ | _⟩ | _ | _ | _
  all_goals first | rfl | exact absurd rfl (h _)

/-- `AtomicCompareExchange` through anything but a thin pointer is UB. -/
theorem atomicCompareExchange_not_thin_ptr_ub (m : Machine M) (ptrV : Value M) (pty : «Type»)
    (cur next : Value M) (currTy nextTy retTy : «Type») (h : ∀ p, ptrV ≠ .Ptr ⟨p, none⟩) :
    evalIntrinsicM m .AtomicCompareExchange [(ptrV, pty), (cur, currTy), (next, nextTy)] retTy =
      .error (.ub
        "invalid first argument to `AtomicCompareExchange` intrinsic: not a thin pointer") := by
  rcases ptrV with _ | _ | ⟨p, _ | _⟩ | _ | _ | _
  all_goals first | rfl | exact absurd rfl (h _)

/-- `AtomicFetchAndOp` through anything but a thin pointer is UB. -/
theorem atomicFetchAndOp_not_thin_ptr_ub (m : Machine M) (binOp : IntBinOp) (ptrV : Value M)
    (pty : «Type») (other : Value M) (otherTy retTy : «Type»)
    (h : ∀ p, ptrV ≠ .Ptr ⟨p, none⟩) :
    evalIntrinsicM m (.AtomicFetchAndOp binOp) [(ptrV, pty), (other, otherTy)] retTy =
      .error (.ub
        "invalid first argument to `AtomicFetchAndOp` intrinsic: not a thin pointer") := by
  rcases ptrV with _ | _ | ⟨p, _ | _⟩ | _ | _ | _
  all_goals first | rfl | exact absurd rfl (h _)

/-- A `Value::Int` (an address without a pointer value around it) is not a
thin pointer: all four intrinsics are UB on it. -/
theorem atomic_int_first_arg_ub (m : Machine M) (a : Int) (pty : «Type») (v w : Value M)
    (ty ty' retTy : «Type») (binOp : IntBinOp) :
    evalIntrinsicM m .AtomicStore [(.Int a, pty), (v, ty)] retTy =
      .error (.ub "invalid first argument to `AtomicStore` intrinsic: not a thin pointer") ∧
    evalIntrinsicM m .AtomicLoad [(.Int a, pty)] retTy =
      .error (.ub "invalid first argument to `AtomicLoad` intrinsic: not a thin pointer") ∧
    evalIntrinsicM m .AtomicCompareExchange [(.Int a, pty), (v, ty), (w, ty')] retTy =
      .error (.ub
        "invalid first argument to `AtomicCompareExchange` intrinsic: not a thin pointer") ∧
    evalIntrinsicM m (.AtomicFetchAndOp binOp) [(.Int a, pty), (v, ty)] retTy =
      .error (.ub
        "invalid first argument to `AtomicFetchAndOp` intrinsic: not a thin pointer") :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A wide pointer (`metadata = Some(_)`, as for `*const [u32]`) is not a thin
pointer: all four intrinsics are UB on it. -/
theorem atomic_wide_ptr_first_arg_ub (m : Machine M) (p : ThinPointer (Memory.Provenance M))
    (md : PointerMeta (Memory.Provenance M)) (pty : «Type») (v w : Value M)
    (ty ty' retTy : «Type») (binOp : IntBinOp) :
    evalIntrinsicM m .AtomicStore [(.Ptr ⟨p, some md⟩, pty), (v, ty)] retTy =
      .error (.ub "invalid first argument to `AtomicStore` intrinsic: not a thin pointer") ∧
    evalIntrinsicM m .AtomicLoad [(.Ptr ⟨p, some md⟩, pty)] retTy =
      .error (.ub "invalid first argument to `AtomicLoad` intrinsic: not a thin pointer") ∧
    evalIntrinsicM m .AtomicCompareExchange [(.Ptr ⟨p, some md⟩, pty), (v, ty), (w, ty')] retTy =
      .error (.ub
        "invalid first argument to `AtomicCompareExchange` intrinsic: not a thin pointer") ∧
    evalIntrinsicM m (.AtomicFetchAndOp binOp) [(.Ptr ⟨p, some md⟩, pty), (v, ty)] retTy =
      .error (.ub
        "invalid first argument to `AtomicFetchAndOp` intrinsic: not a thin pointer") :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Layout facts used by the size checks -/

/-- `Align::from_bytes` on a byte count that came from a `Size`. -/
theorem alignFromBytesInt_natCast (n : Nat) : alignFromBytesInt (n : Int) = alignFromBytes n := by
  unfold alignFromBytesInt
  have h : ¬ ((n : Int) < 0) := by omega
  simp only [h, ↓reduceIte, Int.toNat_natCast]

/-- `Align::from_bytes(n)` is `n` itself when it is defined: an atomic access
is aligned to its own size. -/
theorem alignFromBytes_eq_some {n : Nat} {al : Align} (h : alignFromBytes n = some al) :
    al = ⟨n⟩ := by
  unfold alignFromBytes at h
  split at h
  · cases h
    rfl
  · cases h

/-- The layout of an integer type whose size is a power of two. -/
theorem layout_int {t : IntType} {al : Align} (h : alignFromBytes t.size.bytes = some al) :
    Type.layout (.Int t) =
      .ok (.Sized t.size ⟨min al.bytes x86_64.INT_MAX_ALIGN.bytes⟩) := by
  simp only [Type.layout, IntType.align, h]
  rfl

/-- An integer type whose size is not a power of two has no layout: computing
it is a spec panic (`IntType::align` unwraps `Align::from_bytes`). -/
theorem layout_int_ill_formed {t : IntType} (h : alignFromBytes t.size.bytes = none) :
    Type.layout (.Int t) = .error (.specPanic "Align::from_bytes(size).unwrap()") := by
  simp only [Type.layout, IntType.align, h]
  rfl

/-- Comparing any type against an integer type with `typeEq` is propositional
equality. -/
theorem typeEq_int_right_iff (ty : «Type») (t : IntType) :
    typeEq ty (.Int t) = true ↔ ty = .Int t := by
  cases ty with
  | Int t' =>
    constructor
    · intro h
      simp only [typeEq] at h
      have ht : t' = t := beq_iff_eq.mp h
      subst ht
      rfl
    · intro h
      cases h
      simp only [typeEq, beq_self_eq_true]
  | _ =>
    constructor
    · intro h
      simp only [typeEq] at h
      cases h
    · intro h
      cases h

/-- Mirror image of `typeEq_int_right_iff`: an integer type on the left of `typeEq`
forces propositional equality too, the exact complement of `typeEq_not_eq`. -/
theorem typeEq_int_left_iff (t : IntType) (ty : «Type») :
    typeEq (.Int t) ty = true ↔ ty = .Int t := by
  cases ty with
  | Int t' =>
    constructor
    · intro h
      simp only [typeEq] at h
      have ht : t = t' := beq_iff_eq.mp h
      subst ht
      rfl
    · intro h
      cases h
      simp only [typeEq, beq_self_eq_true]
  | _ =>
    constructor
    · intro h
      simp only [typeEq] at h
      cases h
    · intro h
      cases h

/-- Variant entries `[(0, bool), (1, bool)]` and their swapped-order counterpart. -/
def permEnumEntriesA : List (Int × Variant) := [(0, ⟨.Bool, ⟨[]⟩⟩), (1, ⟨.Bool, ⟨[]⟩⟩)]
/-- Swapped-order counterpart of `permEnumEntriesA`. -/
def permEnumEntriesB : List (Int × Variant) := [(1, ⟨.Bool, ⟨[]⟩⟩), (0, ⟨.Bool, ⟨[]⟩⟩)]
/-- Two extensionally identical `Type::Enum`s with opposite variant list order. -/
def permEnumA : «Type» := .Enum ⟨permEnumEntriesA⟩ itU8 .Invalid ⟨1⟩ ⟨1⟩
/-- Swapped-order counterpart of `permEnumA`. -/
def permEnumB : «Type» := .Enum ⟨permEnumEntriesB⟩ itU8 .Invalid ⟨1⟩ ⟨1⟩

/-- `permEnumA` and `permEnumB` satisfy `typeEq` yet are propositionally distinct. -/
theorem permEnum_typeEq_ne : typeEq permEnumA permEnumB = true ∧ permEnumA ≠ permEnumB := by
  refine ⟨?_, ?_⟩
  · have hml : (mapLen ⟨permEnumEntriesA⟩ == mapLen ⟨permEnumEntriesB⟩) = true := rfl
    have hget0 : mapGet ⟨permEnumEntriesB⟩ 0 = some ⟨.Bool, ⟨[]⟩⟩ := rfl
    have hget1 : mapGet ⟨permEnumEntriesB⟩ 1 = some ⟨.Bool, ⟨[]⟩⟩ := rfl
    have hc0 : (([] : List Int).contains 0) = false := rfl
    have hc1 : (([0] : List Int).contains 1) = false := rfl
    simp only [permEnumA, permEnumB, typeEq, discriminatorEq, hml, beq_self_eq_true,
      Bool.true_and, Bool.and_true]
    simp only [permEnumEntriesA, typeVariantsEq, typeEq, mapEq, List.all_nil, hget0, hget1,
      hc0, hc1, Bool.false_eq_true, ↓reduceIte, Bool.and_self]
  · intro h
    have hfst :=
      congrArg (fun t => match t with | .Enum ⟨(k, _) :: _⟩ _ _ _ _ => k | _ => (2 : Int)) h
    dsimp only [permEnumA, permEnumB, permEnumEntriesA, permEnumEntriesB] at hfst
    exact absurd hfst (by decide)

/-- Unlike on `Type::Int`, `typeEq` on all of `Type` is not propositional equality. -/
theorem typeEq_not_eq : ∃ t1 t2 : «Type», typeEq t1 t2 = true ∧ t1 ≠ t2 :=
  ⟨permEnumA, permEnumB, permEnum_typeEq_ne⟩

/-- `Align::from_bytes(n)` succeeds only for positive byte counts. -/
theorem alignFromBytes_pos {n : Nat} {al : Align} (h : alignFromBytes n = some al) :
    0 < n := by
  unfold alignFromBytes at h
  split at h
  · rename_i hc
    exact Nat.pos_of_ne_zero hc.1
  · cases h

/-- A successful `typed_load` at an integer type always yields a `Value::Int`,
in every memory model. In particular, the second `unreachable!()` of
`AtomicFetchAndOp` (`let Value::Int(previous_int) = previous else { unreachable!() }`)
cannot be reached. -/
theorem typedLoadM_int_returns_int {m m' : Machine M}
    {ptr : ThinPointer (Memory.Provenance M)} {t : IntType} {align : Align}
    {atomicity : Atomicity} {val : Value M}
    (h : typedLoadM m ptr (.Int t) align atomicity = .ok (val, m')) :
    ∃ i, val = .Int i := by
  unfold typedLoadM at h
  obtain ⟨_, _, h⟩ := interp_bind_eq_ok h
  obtain ⟨_, _, h⟩ := interp_bind_eq_ok h
  obtain ⟨⟨bytes, cm⟩, _, h⟩ := interp_bind_eq_ok h
  dsimp only at h
  obtain ⟨opt, hdec, h⟩ := interp_bind_eq_ok h
  cases opt with
  | none => cases h
  | some v =>
    obtain ⟨_, _, h⟩ := interp_bind_eq_ok h
    obtain ⟨rfl, _⟩ := Prod.mk.inj (interp_pure_eq_ok h)
    cases t with
    | mk signed size =>
      dsimp only [Type.decodeM, Type.decodeIntM] at hdec
      split at hdec
      · dsimp only [specPanic] at hdec; cases hdec
      · split at hdec
        · have hsome := interp_pure_eq_ok hdec
          cases hsome
          exact ⟨_, rfl⟩
        · have hnone := interp_pure_eq_ok hdec
          cases hnone

omit [MemoryOps M] in
/-- Encoding any value at an integer type produces exactly `t.size.bytes` bytes. -/
theorem encodeM_int_length {t : IntType} {val : Value M}
    {bytes : List (AbstractByte (Memory.Provenance M))}
    (h : Type.encodeM (M := M) (.Int t) val = .ok bytes) :
    bytes.length = t.size.bytes := by
  cases t with
  | mk signed size =>
    cases val with
    | Int i =>
      dsimp only [Type.encodeM, Type.encodeIntM, Endianness.encode, x86_64.ENDIANNESS] at h
      cases hin : inBounds i signed size with
      | true =>
        simp only [hin, ↓reduceIte] at h
        obtain rfl := interp_pure_eq_ok h
        rw [List.length_map, MiniRustSpec.Correspondence.leBytes_length]
      | false =>
        simp only [hin, Bool.false_eq_true, ↓reduceIte, specPanic] at h
        cases h
    | _ =>
      dsimp only [Type.encodeM, Type.encodeIntM, specPanic] at h
      cases h

omit [MemoryOps M] in
/-- Encoding any value at an integer type produces bytes without provenance:
every byte is `AbstractByte::Init(b, None)`. Whatever a `typed_store` at
`Type::Int` writes, it writes without provenance, in every memory model. -/
theorem encodeM_int_no_provenance {t : IntType} {val : Value M}
    {bytes : List (AbstractByte (Memory.Provenance M))}
    (h : Type.encodeM (M := M) (.Int t) val = .ok bytes) :
    ∀ b ∈ bytes, ∃ u, b = AbstractByte.Init u none := by
  cases t with
  | mk signed size =>
    cases val with
    | Int i =>
      dsimp only [Type.encodeM, Type.encodeIntM, Endianness.encode, x86_64.ENDIANNESS] at h
      cases hin : inBounds i signed size with
      | true =>
        simp only [hin, ↓reduceIte] at h
        obtain rfl := interp_pure_eq_ok h
        intro b hb
        obtain ⟨u, _, rfl⟩ := List.mem_map.mp hb
        exact ⟨u, rfl⟩
      | false =>
        simp only [hin, Bool.false_eq_true, ↓reduceIte, specPanic] at h
        cases h
    | _ =>
      dsimp only [Type.encodeM, Type.encodeIntM, specPanic] at h
      cases h

/-! ### `AtomicStore` -/

/-- `AtomicStore` at an unsized type is UB. -/
theorem atomicStore_unsized_ub (m : Machine M) (ptr : ThinPointer (Memory.Provenance M))
    (pty : «Type») (v : Value M) (ty retTy : «Type») {l : LayoutStrategy}
    (hl : Type.layout ty = .ok l) (hu : LayoutStrategy.is_sized l = false) :
    evalIntrinsicM m .AtomicStore [(.Ptr ⟨ptr, none⟩, pty), (v, ty)] retTy =
      .error (.ub "invalid second argument to `AtomicStore` intrinsic: unsized type") := by
  simp only [evalIntrinsicM, hl, interp_ok_bind]
  cases l with
  | Sized s a => exact Bool.noConfusion hu
  | _ => rfl

/-- `AtomicStore` at a type whose size is not a power of two is UB. -/
theorem atomicStore_size_not_pow2_ub (m : Machine M) (ptr : ThinPointer (Memory.Provenance M))
    (pty : «Type») (v : Value M) (ty retTy : «Type») {size : Size} {a : Align}
    (hl : Type.layout ty = .ok (.Sized size a))
    (ha : alignFromBytesInt size.bytes = none) :
    evalIntrinsicM m .AtomicStore [(.Ptr ⟨ptr, none⟩, pty), (v, ty)] retTy =
      .error (.ub
        "invalid second argument to `AtomicStore` intrinsic: size not power of two") := by
  simp only [evalIntrinsicM, hl, interp_ok_bind, ha]
  rfl

/-- `AtomicStore` at a type larger than `MAX_ATOMIC_SIZE` is UB, whatever the
return type. -/
theorem atomicStore_size_too_big_ub (m : Machine M) (ptr : ThinPointer (Memory.Provenance M))
    (pty : «Type») (v : Value M) (ty retTy : «Type») {size : Size} {a align : Align}
    (hl : Type.layout ty = .ok (.Sized size a))
    (ha : alignFromBytesInt size.bytes = some align)
    (hbig : size.bytes > x86_64.MAX_ATOMIC_SIZE.bytes) :
    evalIntrinsicM m .AtomicStore [(.Ptr ⟨ptr, none⟩, pty), (v, ty)] retTy =
      .error (.ub "invalid second argument to `AtomicStore` intrinsic: size too big") := by
  simp only [evalIntrinsicM, hl, interp_ok_bind, ha, hbig, ↓reduceIte]
  rfl

/-- `AtomicStore` returning anything but `()` is UB. -/
theorem atomicStore_ret_not_unit_ub (m : Machine M) (ptr : ThinPointer (Memory.Provenance M))
    (pty : «Type») (v : Value M) (ty retTy : «Type») {size : Size} {a align : Align}
    (hl : Type.layout ty = .ok (.Sized size a))
    (ha : alignFromBytesInt size.bytes = some align)
    (hsz : size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes) (hret : retTy ≠ unitType) :
    evalIntrinsicM m .AtomicStore [(.Ptr ⟨ptr, none⟩, pty), (v, ty)] retTy =
      .error (.ub "invalid return type for `AtomicStore` intrinsic") := by
  have hn : ¬ (size.bytes > x86_64.MAX_ATOMIC_SIZE.bytes) := Nat.not_lt.mpr hsz
  simp only [evalIntrinsicM, hl, interp_ok_bind, ha, hn, ↓reduceIte]
  split
  · exact absurd rfl hret
  · rfl

/-- A well-shaped `AtomicStore` is `Machine::typed_store` at
`Atomicity::Atomic`, aligned to the size of the stored type. -/
theorem atomicStore_eq_typedStoreM (m : Machine M) (ptr : ThinPointer (Memory.Provenance M))
    (pty : «Type») (v : Value M) (ty : «Type») {size : Size} {a align : Align}
    (hl : Type.layout ty = .ok (.Sized size a))
    (ha : alignFromBytesInt size.bytes = some align)
    (hsz : size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes) :
    evalIntrinsicM m .AtomicStore [(.Ptr ⟨ptr, none⟩, pty), (v, ty)] unitType =
      (typedStoreM m ptr v ty align .Atomic >>= fun m' => pure (unitValueM, m')) := by
  have hn : ¬ (size.bytes > x86_64.MAX_ATOMIC_SIZE.bytes) := Nat.not_lt.mpr hsz
  simp only [evalIntrinsicM, unitType, hl, interp_ok_bind, ha, hn, ↓reduceIte]

/-- Complete characterization of a successful `AtomicStore` in every memory model. -/
theorem atomicStore_ok_iff {m m' : Machine M} {args : List (Value M × «Type»)}
    {retTy : «Type»} {val : Value M} :
    evalIntrinsicM m .AtomicStore args retTy = .ok (val, m') ↔
      ∃ ptr pty v ty size a align,
        args = [(.Ptr ⟨ptr, none⟩, pty), (v, ty)] ∧
        Type.layout ty = .ok (.Sized size a) ∧
        alignFromBytes size.bytes = some align ∧
        size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes ∧
        retTy = unitType ∧
        val = unitValueM ∧
        typedStoreM m ptr v ty align .Atomic = .ok m' := by
  constructor
  · intro h
    rcases args with _ | ⟨⟨ptrV, pty⟩, _ | ⟨⟨v, ty⟩, _ | ⟨_, _⟩⟩⟩
    · dsimp only [evalIntrinsicM, ub] at h; cases h
    · dsimp only [evalIntrinsicM, ub] at h; cases h
    · rcases ptrV with _ | _ | ⟨ptr, _ | _⟩ | _ | _ | _
      all_goals try (dsimp only [evalIntrinsicM, ub] at h; cases h)
      dsimp only [evalIntrinsicM] at h
      obtain ⟨layout, hl, h⟩ := interp_bind_eq_ok h
      cases layout with
      | Sized size a =>
        dsimp only at h
        rw [alignFromBytesInt_natCast] at h
        cases ha : alignFromBytes size.bytes with
        | none =>
          simp only [ha, ub] at h; cases h
        | some align =>
          simp only [ha] at h
          by_cases hbig : size.bytes > x86_64.MAX_ATOMIC_SIZE.bytes
          · simp only [hbig, ↓reduceIte, ub] at h; cases h
          · simp only [hbig, ↓reduceIte] at h
            by_cases hret : retTy = unitType
            · subst hret
              dsimp only [unitType] at h
              obtain ⟨m1, hs, h⟩ := interp_bind_eq_ok h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok h)
              exact ⟨ptr, pty, v, ty, size, a, align, rfl, hl, ha,
                Nat.not_lt.mp hbig, rfl, rfl, hs⟩
            · split at h
              · exact absurd rfl hret
              · dsimp only [ub] at h; cases h
      | _ => dsimp only [ub] at h; cases h
    · dsimp only [evalIntrinsicM, ub] at h; cases h
  · rintro ⟨ptr, pty, v, ty, size, a, align, rfl, hl, ha, hsz, rfl, rfl, hs⟩
    have ha' : alignFromBytesInt size.bytes = some align := by
      rw [alignFromBytesInt_natCast]; exact ha
    rw [atomicStore_eq_typedStoreM m ptr pty v ty hl ha' hsz, hs]
    rfl

/-- Complete characterization of every stopping outcome (UB or spec panic, in
exact upstream check order) of `AtomicStore` in every memory model. -/
theorem atomicStore_error_iff {m : Machine M} {args : List (Value M × «Type»)}
    {retTy : «Type»} {e : Stop} :
    evalIntrinsicM m .AtomicStore args retTy = .error e ↔
      (args.length ≠ 2 ∧ e = .ub "invalid number of arguments for `AtomicStore` intrinsic") ∨
      (∃ ptrV pty v ty, args = [(ptrV, pty), (v, ty)] ∧
        (∀ p, ptrV ≠ .Ptr ⟨p, none⟩) ∧
        e = .ub "invalid first argument to `AtomicStore` intrinsic: not a thin pointer") ∨
      (∃ ptr pty v ty, args = [(.Ptr ⟨ptr, none⟩, pty), (v, ty)] ∧
        (Type.layout ty = .error e ∨
         (∃ l, Type.layout ty = .ok l ∧ LayoutStrategy.is_sized l = false ∧
           e = .ub "invalid second argument to `AtomicStore` intrinsic: unsized type") ∨
         (∃ size a, Type.layout ty = .ok (.Sized size a) ∧
           alignFromBytes size.bytes = none ∧
           e = .ub "invalid second argument to `AtomicStore` intrinsic: size not power of two") ∨
         (∃ size a align, Type.layout ty = .ok (.Sized size a) ∧
           alignFromBytes size.bytes = some align ∧
           size.bytes > x86_64.MAX_ATOMIC_SIZE.bytes ∧
           e = .ub "invalid second argument to `AtomicStore` intrinsic: size too big") ∨
         (∃ size a align, Type.layout ty = .ok (.Sized size a) ∧
           alignFromBytes size.bytes = some align ∧
           size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes ∧
           retTy ≠ unitType ∧
           e = .ub "invalid return type for `AtomicStore` intrinsic") ∨
         (∃ size a align, Type.layout ty = .ok (.Sized size a) ∧
           alignFromBytes size.bytes = some align ∧
           size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes ∧
           retTy = unitType ∧
           typedStoreM m ptr v ty align .Atomic = .error e))) := by
  constructor
  · intro h
    rcases args with _ | ⟨⟨ptrV, pty⟩, _ | ⟨⟨v, ty⟩, _ | ⟨_, _⟩⟩⟩
    · dsimp only [evalIntrinsicM, ub] at h; cases h; exact Or.inl ⟨by show 0 ≠ 2; decide, rfl⟩
    · dsimp only [evalIntrinsicM, ub] at h; cases h; exact Or.inl ⟨by show 1 ≠ 2; decide, rfl⟩
    · rcases ptrV with _ | _ | ⟨ptr, _ | _⟩ | _ | _ | _
      · dsimp only [evalIntrinsicM, ub] at h; cases h
        exact Or.inr (Or.inl ⟨_, pty, v, ty, rfl, (fun _ hc => by cases hc), rfl⟩)
      · dsimp only [evalIntrinsicM, ub] at h; cases h
        exact Or.inr (Or.inl ⟨_, pty, v, ty, rfl, (fun _ hc => by cases hc), rfl⟩)
      · dsimp only [evalIntrinsicM] at h
        refine Or.inr (Or.inr ⟨ptr, pty, v, ty, rfl, ?_⟩)
        rcases interp_bind_eq_error h with hlay | ⟨layout, hl, h⟩
        · exact Or.inl hlay
        · cases layout with
          | Sized size a =>
            dsimp only at h
            rw [alignFromBytesInt_natCast] at h
            cases ha : alignFromBytes size.bytes with
            | none =>
              simp only [ha, ub] at h; cases h
              exact Or.inr (Or.inr (Or.inl ⟨size, a, hl, ha, rfl⟩))
            | some align =>
              simp only [ha] at h
              by_cases hbig : size.bytes > x86_64.MAX_ATOMIC_SIZE.bytes
              · simp only [hbig, ↓reduceIte, ub] at h; cases h
                exact Or.inr (Or.inr (Or.inr (Or.inl ⟨size, a, align, hl, ha, hbig, rfl⟩)))
              · simp only [hbig, ↓reduceIte] at h
                by_cases hret : retTy = unitType
                · subst hret
                  dsimp only [unitType] at h
                  rcases interp_bind_eq_error h with hs | ⟨_, _, h⟩
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                      ⟨size, a, align, hl, ha, Nat.not_lt.mp hbig, rfl, hs⟩))))
                  · cases h
                · split at h
                  · exact absurd rfl hret
                  · dsimp only [ub] at h; cases h
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                      ⟨size, a, align, hl, ha, Nat.not_lt.mp hbig, hret, rfl⟩))))
          | Slice _ _ =>
            dsimp only [ub] at h; cases h
            exact Or.inr (Or.inl ⟨_, hl, rfl, rfl⟩)
          | TraitObject _ =>
            dsimp only [ub] at h; cases h
            exact Or.inr (Or.inl ⟨_, hl, rfl, rfl⟩)
          | Tuple _ _ =>
            dsimp only [ub] at h; cases h
            exact Or.inr (Or.inl ⟨_, hl, rfl, rfl⟩)
      · dsimp only [evalIntrinsicM, ub] at h; cases h
        exact Or.inr (Or.inl ⟨_, pty, v, ty, rfl,
          (fun _ hc => by cases (Pointer.mk.inj (Value.Ptr.inj hc)).2), rfl⟩)
      · dsimp only [evalIntrinsicM, ub] at h; cases h
        exact Or.inr (Or.inl ⟨_, pty, v, ty, rfl, (fun _ hc => by cases hc), rfl⟩)
      · dsimp only [evalIntrinsicM, ub] at h; cases h
        exact Or.inr (Or.inl ⟨_, pty, v, ty, rfl, (fun _ hc => by cases hc), rfl⟩)
      · dsimp only [evalIntrinsicM, ub] at h; cases h
        exact Or.inr (Or.inl ⟨_, pty, v, ty, rfl, (fun _ hc => by cases hc), rfl⟩)
    · dsimp only [evalIntrinsicM, ub] at h; cases h
      exact Or.inl ⟨by simp only [List.length_cons]; omega, rfl⟩
  · rintro (⟨hlen, rfl⟩ | ⟨ptrV, pty, v, ty, rfl, hnt, rfl⟩ | ⟨ptr, pty, v, ty, rfl, hcase⟩)
    · exact atomicStore_arity_ub m args retTy hlen
    · exact atomicStore_not_thin_ptr_ub m ptrV pty v ty retTy hnt
    · rcases hcase with hlay | ⟨l, hl, hu, rfl⟩ | ⟨size, a, hl, ha, rfl⟩ |
        ⟨size, a, align, hl, ha, hbig, rfl⟩ | ⟨size, a, align, hl, ha, hsz, hret, rfl⟩ |
        ⟨size, a, align, hl, ha, hsz, rfl, hs⟩
      · simp only [evalIntrinsicM, hlay, interp_error_bind]
      · exact atomicStore_unsized_ub m ptr pty v ty retTy hl hu
      · exact atomicStore_size_not_pow2_ub m ptr pty v ty retTy hl
          (by rw [alignFromBytesInt_natCast]; exact ha)
      · exact atomicStore_size_too_big_ub m ptr pty v ty retTy hl
          (by rw [alignFromBytesInt_natCast]; exact ha) hbig
      · exact atomicStore_ret_not_unit_ub m ptr pty v ty retTy hl
          (by rw [alignFromBytesInt_natCast]; exact ha) hsz hret
      · rw [atomicStore_eq_typedStoreM m ptr pty v ty hl
          (by rw [alignFromBytesInt_natCast]; exact ha) hsz, hs]
        rfl

/-! ### `AtomicLoad` -/

/-- `AtomicLoad` at an unsized return type is a spec panic, not UB: unlike
`AtomicStore`, upstream calls `expect_size`, which asserts well-formedness. -/
theorem atomicLoad_unsized_specPanic (m : Machine M) (ptr : ThinPointer (Memory.Provenance M))
    (pty retTy : «Type») {l : LayoutStrategy}
    (hl : Type.layout retTy = .ok l) (hu : LayoutStrategy.is_sized l = false) :
    evalIntrinsicM m .AtomicLoad [(.Ptr ⟨ptr, none⟩, pty)] retTy =
      .error (.specPanic
        "expect_size called on unsized type: WF ensures intrinsic return types are sized") := by
  simp only [evalIntrinsicM, hl, interp_ok_bind]
  cases l with
  | Sized s a => exact Bool.noConfusion hu
  | _ => rfl

/-- `AtomicLoad` at a type whose size is not a power of two is UB. -/
theorem atomicLoad_size_not_pow2_ub (m : Machine M) (ptr : ThinPointer (Memory.Provenance M))
    (pty retTy : «Type») {size : Size} {a : Align}
    (hl : Type.layout retTy = .ok (.Sized size a))
    (ha : alignFromBytesInt size.bytes = none) :
    evalIntrinsicM m .AtomicLoad [(.Ptr ⟨ptr, none⟩, pty)] retTy =
      .error (.ub "invalid return type for `AtomicLoad` intrinsic: size not power of two") := by
  simp only [evalIntrinsicM, hl, interp_ok_bind, LayoutStrategy.expect_size, interp_pure_bind, ha]
  rfl

/-- `AtomicLoad` at a type larger than `MAX_ATOMIC_SIZE` is UB. -/
theorem atomicLoad_size_too_big_ub (m : Machine M) (ptr : ThinPointer (Memory.Provenance M))
    (pty retTy : «Type») {size : Size} {a align : Align}
    (hl : Type.layout retTy = .ok (.Sized size a))
    (ha : alignFromBytesInt size.bytes = some align)
    (hbig : size.bytes > x86_64.MAX_ATOMIC_SIZE.bytes) :
    evalIntrinsicM m .AtomicLoad [(.Ptr ⟨ptr, none⟩, pty)] retTy =
      .error (.ub "invalid return type for `AtomicLoad` intrinsic: size too big") := by
  simp only [evalIntrinsicM, hl, interp_ok_bind, LayoutStrategy.expect_size, interp_pure_bind, ha,
    hbig, ↓reduceIte]
  rfl

/-- A well-shaped `AtomicLoad` is `Machine::typed_load` at `Atomicity::Atomic`,
aligned to the size of the loaded type. -/
theorem atomicLoad_eq_typedLoadM (m : Machine M) (ptr : ThinPointer (Memory.Provenance M))
    (pty retTy : «Type») {size : Size} {a align : Align}
    (hl : Type.layout retTy = .ok (.Sized size a))
    (ha : alignFromBytesInt size.bytes = some align)
    (hsz : size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes) :
    evalIntrinsicM m .AtomicLoad [(.Ptr ⟨ptr, none⟩, pty)] retTy =
      typedLoadM m ptr retTy align .Atomic := by
  have hn : ¬ (size.bytes > x86_64.MAX_ATOMIC_SIZE.bytes) := Nat.not_lt.mpr hsz
  simp only [evalIntrinsicM, hl, interp_ok_bind, LayoutStrategy.expect_size, interp_pure_bind, ha,
    hn, ↓reduceIte]

/-- Complete characterization of a successful `AtomicLoad` in every memory model. -/
theorem atomicLoad_ok_iff {m m' : Machine M} {args : List (Value M × «Type»)}
    {retTy : «Type»} {val : Value M} :
    evalIntrinsicM m .AtomicLoad args retTy = .ok (val, m') ↔
      ∃ ptr pty size a align,
        args = [(.Ptr ⟨ptr, none⟩, pty)] ∧
        Type.layout retTy = .ok (.Sized size a) ∧
        alignFromBytes size.bytes = some align ∧
        size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes ∧
        typedLoadM m ptr retTy align .Atomic = .ok (val, m') := by
  constructor
  · intro h
    rcases args with _ | ⟨⟨ptrV, pty⟩, _ | ⟨_, _⟩⟩
    · dsimp only [evalIntrinsicM, ub] at h; cases h
    · rcases ptrV with _ | _ | ⟨ptr, _ | _⟩ | _ | _ | _
      all_goals try (dsimp only [evalIntrinsicM, ub] at h; cases h)
      dsimp only [evalIntrinsicM] at h
      obtain ⟨layout, hl, h1⟩ := interp_bind_eq_ok h
      obtain ⟨size, hexp, h2⟩ := interp_bind_eq_ok h1
      cases layout with
      | Sized sz a =>
        have hszEq : sz = size := interp_pure_eq_ok hexp
        rw [← hszEq] at h2
        rw [alignFromBytesInt_natCast] at h2
        cases ha : alignFromBytes sz.bytes with
        | none =>
          simp only [ha, ub] at h2; cases h2
        | some align =>
          simp only [ha] at h2
          by_cases hbig : sz.bytes > x86_64.MAX_ATOMIC_SIZE.bytes
          · simp only [hbig, ↓reduceIte, ub] at h2; cases h2
          · simp only [hbig, ↓reduceIte] at h2
            exact ⟨ptr, pty, sz, a, align, rfl, hl, ha, Nat.not_lt.mp hbig, h2⟩
      | _ => dsimp only [LayoutStrategy.expect_size, specPanic] at hexp; cases hexp
    · dsimp only [evalIntrinsicM, ub] at h; cases h
  · rintro ⟨ptr, pty, size, a, align, rfl, hl, ha, hsz, hload⟩
    have ha' : alignFromBytesInt size.bytes = some align := by
      rw [alignFromBytesInt_natCast]; exact ha
    rw [atomicLoad_eq_typedLoadM m ptr pty retTy hl ha' hsz]
    exact hload

/-- Complete characterization of every stopping outcome (UB or spec panic, in
exact upstream check order) of `AtomicLoad` in every memory model. -/
theorem atomicLoad_error_iff {m : Machine M} {args : List (Value M × «Type»)}
    {retTy : «Type»} {e : Stop} :
    evalIntrinsicM m .AtomicLoad args retTy = .error e ↔
      (args.length ≠ 1 ∧ e = .ub "invalid number of arguments for `AtomicLoad` intrinsic") ∨
      (∃ ptrV pty, args = [(ptrV, pty)] ∧
        (∀ p, ptrV ≠ .Ptr ⟨p, none⟩) ∧
        e = .ub "invalid first argument to `AtomicLoad` intrinsic: not a thin pointer") ∨
      (∃ ptr pty, args = [(.Ptr ⟨ptr, none⟩, pty)] ∧
        (Type.layout retTy = .error e ∨
         (∃ l, Type.layout retTy = .ok l ∧ LayoutStrategy.is_sized l = false ∧
           e = .specPanic
             "expect_size called on unsized type: WF ensures intrinsic return types are sized") ∨
         (∃ size a, Type.layout retTy = .ok (.Sized size a) ∧
           alignFromBytes size.bytes = none ∧
           e = .ub "invalid return type for `AtomicLoad` intrinsic: size not power of two") ∨
         (∃ size a align, Type.layout retTy = .ok (.Sized size a) ∧
           alignFromBytes size.bytes = some align ∧
           size.bytes > x86_64.MAX_ATOMIC_SIZE.bytes ∧
           e = .ub "invalid return type for `AtomicLoad` intrinsic: size too big") ∨
         (∃ size a align, Type.layout retTy = .ok (.Sized size a) ∧
           alignFromBytes size.bytes = some align ∧
           size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes ∧
           typedLoadM m ptr retTy align .Atomic = .error e))) := by
  constructor
  · intro h
    rcases args with _ | ⟨⟨ptrV, pty⟩, _ | ⟨_, _⟩⟩
    · dsimp only [evalIntrinsicM, ub] at h; cases h; exact Or.inl ⟨by show 0 ≠ 1; decide, rfl⟩
    · rcases ptrV with _ | _ | ⟨ptr, _ | _⟩ | _ | _ | _
      · dsimp only [evalIntrinsicM, ub] at h; cases h
        exact Or.inr (Or.inl ⟨_, pty, rfl, (fun _ hc => by cases hc), rfl⟩)
      · dsimp only [evalIntrinsicM, ub] at h; cases h
        exact Or.inr (Or.inl ⟨_, pty, rfl, (fun _ hc => by cases hc), rfl⟩)
      · dsimp only [evalIntrinsicM] at h
        refine Or.inr (Or.inr ⟨ptr, pty, rfl, ?_⟩)
        rcases interp_bind_eq_error h with hlay | ⟨layout, hl, h1⟩
        · exact Or.inl hlay
        · rcases interp_bind_eq_error h1 with hexp | ⟨size, hexp, h2⟩
          · cases layout with
            | Sized _ _ => dsimp only [LayoutStrategy.expect_size] at hexp; cases hexp
            | Slice _ _ =>
              dsimp only [LayoutStrategy.expect_size, specPanic] at hexp; cases hexp
              exact Or.inr (Or.inl ⟨_, hl, rfl, rfl⟩)
            | TraitObject _ =>
              dsimp only [LayoutStrategy.expect_size, specPanic] at hexp; cases hexp
              exact Or.inr (Or.inl ⟨_, hl, rfl, rfl⟩)
            | Tuple _ _ =>
              dsimp only [LayoutStrategy.expect_size, specPanic] at hexp; cases hexp
              exact Or.inr (Or.inl ⟨_, hl, rfl, rfl⟩)
          · cases layout with
            | Sized sz a =>
              have hszEq : sz = size := interp_pure_eq_ok hexp
              rw [← hszEq] at h2
              rw [alignFromBytesInt_natCast] at h2
              cases ha : alignFromBytes sz.bytes with
              | none =>
                simp only [ha, ub] at h2; cases h2
                exact Or.inr (Or.inr (Or.inl ⟨sz, a, hl, ha, rfl⟩))
              | some align =>
                simp only [ha] at h2
                by_cases hbig : sz.bytes > x86_64.MAX_ATOMIC_SIZE.bytes
                · simp only [hbig, ↓reduceIte, ub] at h2; cases h2
                  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨sz, a, align, hl, ha, hbig, rfl⟩)))
                · simp only [hbig, ↓reduceIte] at h2
                  exact Or.inr (Or.inr (Or.inr (Or.inr
                    ⟨sz, a, align, hl, ha, Nat.not_lt.mp hbig, h2⟩)))
            | _ => dsimp only [LayoutStrategy.expect_size, specPanic] at hexp; cases hexp
      · dsimp only [evalIntrinsicM, ub] at h; cases h
        exact Or.inr (Or.inl ⟨_, pty, rfl,
          (fun _ hc => by cases (Pointer.mk.inj (Value.Ptr.inj hc)).2), rfl⟩)
      · dsimp only [evalIntrinsicM, ub] at h; cases h
        exact Or.inr (Or.inl ⟨_, pty, rfl, (fun _ hc => by cases hc), rfl⟩)
      · dsimp only [evalIntrinsicM, ub] at h; cases h
        exact Or.inr (Or.inl ⟨_, pty, rfl, (fun _ hc => by cases hc), rfl⟩)
      · dsimp only [evalIntrinsicM, ub] at h; cases h
        exact Or.inr (Or.inl ⟨_, pty, rfl, (fun _ hc => by cases hc), rfl⟩)
    · dsimp only [evalIntrinsicM, ub] at h; cases h
      exact Or.inl ⟨by simp only [List.length_cons]; omega, rfl⟩
  · rintro (⟨hlen, rfl⟩ | ⟨ptrV, pty, rfl, hnt, rfl⟩ | ⟨ptr, pty, rfl, hcase⟩)
    · exact atomicLoad_arity_ub m args retTy hlen
    · exact atomicLoad_not_thin_ptr_ub m ptrV pty retTy hnt
    · rcases hcase with hlay | ⟨l, hl, hu, rfl⟩ | ⟨size, a, hl, ha, rfl⟩ |
        ⟨size, a, align, hl, ha, hbig, rfl⟩ | ⟨size, a, align, hl, ha, hsz, hload⟩
      · simp only [evalIntrinsicM, hlay, interp_error_bind]
      · exact atomicLoad_unsized_specPanic m ptr pty retTy hl hu
      · exact atomicLoad_size_not_pow2_ub m ptr pty retTy hl
          (by rw [alignFromBytesInt_natCast]; exact ha)
      · exact atomicLoad_size_too_big_ub m ptr pty retTy hl
          (by rw [alignFromBytesInt_natCast]; exact ha) hbig
      · rw [atomicLoad_eq_typedLoadM m ptr pty retTy hl
          (by rw [alignFromBytesInt_natCast]; exact ha) hsz]
        exact hload

/-! ### `AtomicCompareExchange` -/

/-- `AtomicCompareExchange` whose `current` has another type than the return
type is UB. -/
theorem atomicCompareExchange_current_type_ub (m : Machine M)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (cur next : Value M)
    (currTy nextTy retTy : «Type») (h : typeEq currTy retTy = false) :
    evalIntrinsicM m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (cur, currTy), (next, nextTy)] retTy =
      .error (.ub "invalid second argument to `AtomicCompareExchange` intrinsic: not same type as return value") := by
  simp only [evalIntrinsicM, h, Bool.not_false, ↓reduceIte]
  rfl

/-- `AtomicCompareExchange` whose `next` has another type than the return type
is UB. -/
theorem atomicCompareExchange_next_type_ub (m : Machine M)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (cur next : Value M)
    (currTy nextTy retTy : «Type») (h1 : typeEq currTy retTy = true)
    (h2 : typeEq nextTy retTy = false) :
    evalIntrinsicM m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (cur, currTy), (next, nextTy)] retTy =
      .error (.ub "invalid third argument to `AtomicCompareExchange` intrinsic: not same type as return value") := by
  simp only [evalIntrinsicM, h1, h2, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- `AtomicCompareExchange` at a non-integer type is UB (the message keeps
upstream's `Intrinis` typo). -/
theorem atomicCompareExchange_non_int_ub (m : Machine M)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (cur next : Value M)
    (currTy nextTy retTy : «Type») (h1 : typeEq currTy retTy = true)
    (h2 : typeEq nextTy retTy = true) (hni : ∀ t, retTy ≠ .Int t) :
    evalIntrinsicM m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (cur, currTy), (next, nextTy)] retTy =
      .error (.ub "invalid return type for `Intrinis::AtomicCompareExchange`: only works with integers") := by
  simp only [evalIntrinsicM, h1, h2, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases retTy with
  | Int t => exact absurd rfl (hni t)
  | _ => rfl

/-- `AtomicCompareExchange` at an integer type larger than `MAX_ATOMIC_SIZE`
is UB. -/
theorem atomicCompareExchange_size_too_big_ub (m : Machine M)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (cur next : Value M)
    (t : IntType) {al : Align} (hal : alignFromBytes t.size.bytes = some al)
    (hbig : t.size.bytes > x86_64.MAX_ATOMIC_SIZE.bytes) :
    evalIntrinsicM m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (cur, .Int t), (next, .Int t)] (.Int t) =
      .error (.ub "invalid return type for `AtomicCompareExchange` intrinsic: size too big") := by
  have hte : typeEq (.Int t) (.Int t) = true := by simp only [typeEq, beq_self_eq_true]
  have ha : alignFromBytesInt (t.size.bytes : Int) = some al := by
    rw [alignFromBytesInt_natCast]
    exact hal
  simp only [evalIntrinsicM, hte, Bool.not_true, Bool.false_eq_true, ↓reduceIte, layout_int hal,
    interp_ok_bind, LayoutStrategy.expect_size, interp_pure_bind, ha, hbig]
  rfl

/-- `AtomicCompareExchange` at an integer type whose size is not a power of
two is a spec panic already in `Type::layout` (`IntType::align`), so the
`Align::from_bytes(size.bytes()).unwrap()` of the intrinsic itself is never the
one that panics. -/
theorem atomicCompareExchange_ill_formed_int_specPanic (m : Machine M)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (cur next : Value M)
    (t : IntType) (hal : alignFromBytes t.size.bytes = none) :
    evalIntrinsicM m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (cur, .Int t), (next, .Int t)] (.Int t) =
      .error (.specPanic "Align::from_bytes(size).unwrap()") := by
  have hte : typeEq (.Int t) (.Int t) = true := by simp only [typeEq, beq_self_eq_true]
  simp only [evalIntrinsicM, hte, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    layout_int_ill_formed hal, interp_error_bind]

/-- A well-shaped `AtomicCompareExchange` is an atomic `typed_load` followed,
only when `current == before`, by an atomic `typed_store` of `next`; either
way it returns the loaded value. -/
theorem atomicCompareExchange_eq (m : Machine M) (ptr : ThinPointer (Memory.Provenance M))
    (pty : «Type») (cur next : Value M) (t : IntType) {al : Align}
    (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes) :
    evalIntrinsicM m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (cur, .Int t), (next, .Int t)] (.Int t) =
      (typedLoadM m ptr (.Int t) al .Atomic >>= fun (before, m1) =>
        if valueEqM cur before then
          typedStoreM m1 ptr next (.Int t) al .Atomic >>= fun m2 => pure (before, m2)
        else pure (before, m1)) := by
  have hte : typeEq (.Int t) (.Int t) = true := by simp only [typeEq, beq_self_eq_true]
  have ha : alignFromBytesInt (t.size.bytes : Int) = some al := by
    rw [alignFromBytesInt_natCast]
    exact hal
  have hn : ¬ (t.size.bytes > x86_64.MAX_ATOMIC_SIZE.bytes) := Nat.not_lt.mpr hsz
  simp only [evalIntrinsicM, hte, Bool.not_true, Bool.false_eq_true, ↓reduceIte, layout_int hal,
    interp_ok_bind, LayoutStrategy.expect_size, interp_pure_bind, ha, hn]

/-- A failing `AtomicCompareExchange` (`current != before`) is exactly its
load: it returns `before` and the machine after the load. No store happens. -/
theorem atomicCompareExchange_failure {m m1 : Machine M}
    {ptr : ThinPointer (Memory.Provenance M)} (pty : «Type») {cur before : Value M}
    (next : Value M) {t : IntType} {al : Align}
    (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hload : typedLoadM m ptr (.Int t) al .Atomic = .ok (before, m1))
    (hne : cur ≠ before) :
    evalIntrinsicM m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (cur, .Int t), (next, .Int t)] (.Int t) =
      .ok (before, m1) := by
  have hv : valueEqM cur before = false := (valueEqM_eq_false_iff cur before).mpr hne
  rw [atomicCompareExchange_eq m ptr pty cur next t hal hsz, hload]
  simp only [interp_ok_bind, hv, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- A succeeding `AtomicCompareExchange` (memory holds `current`) stores `next`
and returns `current`. -/
theorem atomicCompareExchange_success {m m1 m2 : Machine M}
    {ptr : ThinPointer (Memory.Provenance M)} (pty : «Type») {cur next : Value M}
    {t : IntType} {al : Align}
    (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hload : typedLoadM m ptr (.Int t) al .Atomic = .ok (cur, m1))
    (hstore : typedStoreM m1 ptr next (.Int t) al .Atomic = .ok m2) :
    evalIntrinsicM m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (cur, .Int t), (next, .Int t)] (.Int t) =
      .ok (cur, m2) := by
  rw [atomicCompareExchange_eq m ptr pty cur next t hal hsz, hload]
  simp only [interp_ok_bind, valueEqM_refl, ↓reduceIte, hstore]
  rfl

/-- A succeeding comparison whose store stops makes the whole
`AtomicCompareExchange` stop the same way (for example with Tree Borrows UB on
a `Frozen` pointer, or with a spec panic when `next` is ill-formed). -/
theorem atomicCompareExchange_store_error {m m1 : Machine M}
    {ptr : ThinPointer (Memory.Provenance M)} (pty : «Type») {cur next : Value M}
    {t : IntType} {al : Align} {e : Stop}
    (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hload : typedLoadM m ptr (.Int t) al .Atomic = .ok (cur, m1))
    (hstore : typedStoreM m1 ptr next (.Int t) al .Atomic = .error e) :
    evalIntrinsicM m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (cur, .Int t), (next, .Int t)] (.Int t) =
      .error e := by
  rw [atomicCompareExchange_eq m ptr pty cur next t hal hsz, hload]
  simp only [interp_ok_bind, valueEqM_refl, ↓reduceIte, hstore, interp_error_bind]

/-- A stopping load makes the whole `AtomicCompareExchange` stop the same way. -/
theorem atomicCompareExchange_load_error {m : Machine M}
    {ptr : ThinPointer (Memory.Provenance M)} (pty : «Type») (cur next : Value M)
    {t : IntType} {al : Align} {e : Stop}
    (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hload : typedLoadM m ptr (.Int t) al .Atomic = .error e) :
    evalIntrinsicM m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (cur, .Int t), (next, .Int t)] (.Int t) =
      .error e := by
  rw [atomicCompareExchange_eq m ptr pty cur next t hal hsz, hload]
  rfl

/-- A successful `AtomicCompareExchange` at `Type::Int(t)` passed the size
checks: `t`'s size is a power of two no bigger than `MAX_ATOMIC_SIZE`. -/
theorem atomicCompareExchange_ok_size {m m' : Machine M}
    {ptr : ThinPointer (Memory.Provenance M)} {pty : «Type»} {cur next val : Value M} {t : IntType}
    (h : evalIntrinsicM m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (cur, .Int t), (next, .Int t)] (.Int t) = .ok (val, m')) :
    ∃ al, alignFromBytes t.size.bytes = some al ∧
      t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes := by
  have hte : typeEq (.Int t) (.Int t) = true := by simp only [typeEq, beq_self_eq_true]
  simp only [evalIntrinsicM, hte, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases hal : alignFromBytes t.size.bytes with
  | none => simp only [layout_int_ill_formed hal, interp_error_bind] at h; cases h
  | some al =>
    have ha : alignFromBytesInt (t.size.bytes : Int) = some al := by
      rw [alignFromBytesInt_natCast]; exact hal
    simp only [layout_int hal, interp_ok_bind, LayoutStrategy.expect_size,
      interp_pure_bind, ha] at h
    by_cases hbig : t.size.bytes > x86_64.MAX_ATOMIC_SIZE.bytes
    · simp only [hbig, ↓reduceIte, ub] at h; cases h
    · exact ⟨al, rfl, Nat.not_lt.mp hbig⟩

/-- Upstream: "We do *not* do a store on a failing AtomicCompareExchange. This
means that races between a non-atomic load and a failing AtomicCompareExchange
are not considered UB!" An `AtomicCompareExchange` that returns something other
than `current` appends exactly one access to the log, an atomic `Load`. -/
theorem atomicCompareExchange_failure_accesses {m m' : Machine M}
    {ptr : ThinPointer (Memory.Provenance M)} {pty : «Type»} {cur next before : Value M}
    {t : IntType}
    (h : evalIntrinsicM m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (cur, .Int t), (next, .Int t)] (.Int t) = .ok (before, m'))
    (hne : cur ≠ before) :
    m'.mem.accesses = m.mem.accesses ++ [⟨.Load, .Atomic, ptr.addr, t.size⟩] := by
  obtain ⟨_, hal, hsz⟩ := atomicCompareExchange_ok_size h
  rw [atomicCompareExchange_eq m ptr pty cur next t hal hsz] at h
  obtain ⟨⟨b, m1⟩, hload, h⟩ := interp_bind_eq_ok h
  dsimp only at h
  cases hv : valueEqM cur b with
  | true =>
    simp only [hv, ↓reduceIte] at h
    obtain ⟨m2, _, h⟩ := interp_bind_eq_ok h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok h)
    exact absurd ((valueEqM_eq_true_iff cur b).mp hv) hne
  | false =>
    simp only [hv, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok h)
    obtain ⟨size, a, hl, hacc⟩ := typedLoadM_ok_accesses hload
    rw [layout_int hal] at hl
    cases hl
    exact hacc

/-- An `AtomicCompareExchange` that returns `current` succeeded: it appends an
atomic `Load` and then an atomic `Store` of the encoding of `next`. -/
theorem atomicCompareExchange_success_accesses {m m' : Machine M}
    {ptr : ThinPointer (Memory.Provenance M)} {pty : «Type»} {cur next : Value M}
    {t : IntType}
    (h : evalIntrinsicM m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (cur, .Int t), (next, .Int t)] (.Int t) = .ok (cur, m')) :
    ∃ bytes, Type.encodeM (M := M) (.Int t) next = .ok bytes ∧
      m'.mem.accesses = m.mem.accesses ++
        [⟨.Load, .Atomic, ptr.addr, t.size⟩, ⟨.Store, .Atomic, ptr.addr, ⟨bytes.length⟩⟩] := by
  obtain ⟨_, hal, hsz⟩ := atomicCompareExchange_ok_size h
  rw [atomicCompareExchange_eq m ptr pty cur next t hal hsz] at h
  obtain ⟨⟨b, m1⟩, hload, h⟩ := interp_bind_eq_ok h
  dsimp only at h
  cases hv : valueEqM cur b with
  | true =>
    simp only [hv, ↓reduceIte] at h
    obtain ⟨m2, hstore, h⟩ := interp_bind_eq_ok h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok h)
    obtain ⟨size, a, hl, hacc1⟩ := typedLoadM_ok_accesses hload
    rw [layout_int hal] at hl
    cases hl
    obtain ⟨bytes, henc, hacc2⟩ := typedStoreM_ok_accesses hstore
    refine ⟨bytes, henc, ?_⟩
    rw [hacc2, hacc1, List.append_assoc]
    rfl
  | false =>
    simp only [hv, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok h)
    rw [valueEqM_refl] at hv
    cases hv

/-- Complete characterization of a successful `AtomicCompareExchange` in every
memory model: it returns the loaded value `before` and performs an atomic store
of `next` iff `current = before`. -/
theorem atomicCompareExchange_ok_iff {m m' : Machine M} {args : List (Value M × «Type»)}
    {retTy : «Type»} {val : Value M} :
    evalIntrinsicM m .AtomicCompareExchange args retTy = .ok (val, m') ↔
      ∃ ptr pty cur next t al m1,
        args = [(.Ptr ⟨ptr, none⟩, pty), (cur, .Int t), (next, .Int t)] ∧
        retTy = .Int t ∧
        alignFromBytes t.size.bytes = some al ∧
        t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes ∧
        typedLoadM m ptr (.Int t) al .Atomic = .ok (val, m1) ∧
        ((cur = val ∧ typedStoreM m1 ptr next (.Int t) al .Atomic = .ok m') ∨
         (cur ≠ val ∧ m' = m1)) := by
  constructor
  · intro h
    rcases args with _ | ⟨⟨ptrV, pty⟩, _ | ⟨⟨cur, currTy⟩, _ | ⟨⟨next, nextTy⟩, _ | ⟨_, _⟩⟩⟩⟩
    · dsimp only [evalIntrinsicM, ub] at h; cases h
    · dsimp only [evalIntrinsicM, ub] at h; cases h
    · dsimp only [evalIntrinsicM, ub] at h; cases h
    · rcases ptrV with _ | _ | ⟨ptr, _ | _⟩ | _ | _ | _
      all_goals try (dsimp only [evalIntrinsicM, ub] at h; cases h)
      dsimp only [evalIntrinsicM] at h
      cases hc1 : typeEq currTy retTy with
      | false => simp only [hc1, Bool.not_false, ↓reduceIte, ub] at h; cases h
      | true =>
        simp only [hc1, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        cases hc2 : typeEq nextTy retTy with
        | false => simp only [hc2, Bool.not_false, ↓reduceIte, ub] at h; cases h
        | true =>
          simp only [hc2, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          cases retTy with
          | Int t =>
            obtain rfl := (typeEq_int_right_iff currTy t).mp hc1
            obtain rfl := (typeEq_int_right_iff nextTy t).mp hc2
            cases hal : alignFromBytes t.size.bytes with
            | none =>
              simp only [layout_int_ill_formed hal, interp_error_bind] at h; cases h
            | some al =>
              have ha : alignFromBytesInt (t.size.bytes : Int) = some al := by
                rw [alignFromBytesInt_natCast]; exact hal
              simp only [layout_int hal, interp_ok_bind, LayoutStrategy.expect_size,
                interp_pure_bind, ha] at h
              by_cases hbig : t.size.bytes > x86_64.MAX_ATOMIC_SIZE.bytes
              · simp only [hbig, ↓reduceIte, ub] at h; cases h
              · simp only [hbig, ↓reduceIte] at h
                obtain ⟨⟨before, m1⟩, hload, h⟩ := interp_bind_eq_ok h
                dsimp only at h
                cases hv : valueEqM cur before with
                | true =>
                  simp only [hv, ↓reduceIte] at h
                  have hcb : cur = before := (valueEqM_eq_true_iff cur before).mp hv
                  obtain ⟨m2, hstore, h⟩ := interp_bind_eq_ok h
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok h)
                  exact ⟨ptr, pty, cur, next, t, al, m1, rfl, rfl, hal, Nat.not_lt.mp hbig,
                    hload, Or.inl ⟨hcb, hstore⟩⟩
                | false =>
                  simp only [hv, Bool.false_eq_true, ↓reduceIte] at h
                  have hne : cur ≠ before := (valueEqM_eq_false_iff cur before).mp hv
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok h)
                  exact ⟨ptr, pty, cur, next, t, al, m1, rfl, rfl, hal, Nat.not_lt.mp hbig,
                    hload, Or.inr ⟨hne, rfl⟩⟩
          | _ => dsimp only [ub] at h; cases h
    · dsimp only [evalIntrinsicM, ub] at h; cases h
  · rintro ⟨ptr, pty, cur, next, t, al, m1, rfl, rfl, hal, hsz, hload, ⟨rfl, hstore⟩ | ⟨hne, rfl⟩⟩
    · exact atomicCompareExchange_success pty hal hsz hload hstore
    · exact atomicCompareExchange_failure pty next hal hsz hload hne

/-- Complete characterization of every stopping outcome (UB or spec panic, in
exact upstream check order) of `AtomicCompareExchange` in every memory model.
Notice that the intrinsic's own `Align::from_bytes(size.bytes()).unwrap()`
panic does not appear: `Type::layout` (`IntType::align`) always panics first
when `t.size.bytes` is not a power of two. -/
theorem atomicCompareExchange_error_iff {m : Machine M} {args : List (Value M × «Type»)}
    {retTy : «Type»} {e : Stop} :
    evalIntrinsicM m .AtomicCompareExchange args retTy = .error e ↔
      (args.length ≠ 3 ∧
        e = .ub "invalid number of arguments for `AtomicCompareExchange` intrinsic") ∨
      (∃ ptrV pty cur currTy next nextTy,
        args = [(ptrV, pty), (cur, currTy), (next, nextTy)] ∧
        (∀ p, ptrV ≠ .Ptr ⟨p, none⟩) ∧
        e = .ub
          "invalid first argument to `AtomicCompareExchange` intrinsic: not a thin pointer") ∨
      (∃ ptr pty cur currTy next nextTy,
        args = [(.Ptr ⟨ptr, none⟩, pty), (cur, currTy), (next, nextTy)] ∧
        ((typeEq currTy retTy = false ∧
          e = .ub "invalid second argument to `AtomicCompareExchange` intrinsic: not same type as return value") ∨
         (typeEq currTy retTy = true ∧ typeEq nextTy retTy = false ∧
          e = .ub "invalid third argument to `AtomicCompareExchange` intrinsic: not same type as return value") ∨
         (typeEq currTy retTy = true ∧ typeEq nextTy retTy = true ∧ (∀ t, retTy ≠ .Int t) ∧
          e = .ub "invalid return type for `Intrinis::AtomicCompareExchange`: only works with integers") ∨
         (∃ t, currTy = .Int t ∧ nextTy = .Int t ∧ retTy = .Int t ∧
           ((alignFromBytes t.size.bytes = none ∧
             e = .specPanic "Align::from_bytes(size).unwrap()") ∨
            (∃ al, alignFromBytes t.size.bytes = some al ∧
              t.size.bytes > x86_64.MAX_ATOMIC_SIZE.bytes ∧
              e = .ub "invalid return type for `AtomicCompareExchange` intrinsic: size too big") ∨
            (∃ al, alignFromBytes t.size.bytes = some al ∧
              t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes ∧
              typedLoadM m ptr (.Int t) al .Atomic = .error e) ∨
            (∃ al m1, alignFromBytes t.size.bytes = some al ∧
              t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes ∧
              typedLoadM m ptr (.Int t) al .Atomic = .ok (cur, m1) ∧
              typedStoreM m1 ptr next (.Int t) al .Atomic = .error e))))) := by
  constructor
  · intro h
    rcases args with _ | ⟨⟨ptrV, pty⟩, _ | ⟨⟨cur, currTy⟩, _ | ⟨⟨next, nextTy⟩, _ | ⟨_, _⟩⟩⟩⟩
    · dsimp only [evalIntrinsicM, ub] at h; cases h; exact Or.inl ⟨by show 0 ≠ 3; decide, rfl⟩
    · dsimp only [evalIntrinsicM, ub] at h; cases h; exact Or.inl ⟨by show 1 ≠ 3; decide, rfl⟩
    · dsimp only [evalIntrinsicM, ub] at h; cases h; exact Or.inl ⟨by show 2 ≠ 3; decide, rfl⟩
    · rcases ptrV with _ | _ | ⟨ptr, _ | _⟩ | _ | _ | _
      · dsimp only [evalIntrinsicM, ub] at h; cases h
        exact Or.inr (Or.inl ⟨_, pty, cur, currTy, next, nextTy, rfl,
          (fun _ hc => by cases hc), rfl⟩)
      · dsimp only [evalIntrinsicM, ub] at h; cases h
        exact Or.inr (Or.inl ⟨_, pty, cur, currTy, next, nextTy, rfl,
          (fun _ hc => by cases hc), rfl⟩)
      · dsimp only [evalIntrinsicM] at h
        refine Or.inr (Or.inr ⟨ptr, pty, cur, currTy, next, nextTy, rfl, ?_⟩)
        cases hc1 : typeEq currTy retTy with
        | false =>
          simp only [hc1, Bool.not_false, ↓reduceIte, ub] at h; cases h
          exact Or.inl ⟨rfl, rfl⟩
        | true =>
          simp only [hc1, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          cases hc2 : typeEq nextTy retTy with
          | false =>
            simp only [hc2, Bool.not_false, ↓reduceIte, ub] at h; cases h
            exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
          | true =>
            simp only [hc2, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
            cases retTy with
            | Int t =>
              have hct := (typeEq_int_right_iff currTy t).mp hc1
              have hnt := (typeEq_int_right_iff nextTy t).mp hc2
              refine Or.inr (Or.inr (Or.inr ⟨t, hct, hnt, rfl, ?_⟩))
              cases hal : alignFromBytes t.size.bytes with
              | none =>
                simp only [layout_int_ill_formed hal, interp_error_bind] at h; cases h
                exact Or.inl ⟨rfl, rfl⟩
              | some al =>
                have ha : alignFromBytesInt (t.size.bytes : Int) = some al := by
                  rw [alignFromBytesInt_natCast]; exact hal
                simp only [layout_int hal, interp_ok_bind, LayoutStrategy.expect_size,
                  interp_pure_bind, ha] at h
                by_cases hbig : t.size.bytes > x86_64.MAX_ATOMIC_SIZE.bytes
                · simp only [hbig, ↓reduceIte, ub] at h; cases h
                  exact Or.inr (Or.inl ⟨al, rfl, hbig, rfl⟩)
                · simp only [hbig, ↓reduceIte] at h
                  rcases interp_bind_eq_error h with hload | ⟨⟨before, m1⟩, hload, h⟩
                  · exact Or.inr (Or.inr (Or.inl ⟨al, rfl, Nat.not_lt.mp hbig, hload⟩))
                  · dsimp only at h
                    cases hv : valueEqM cur before with
                    | false =>
                      simp only [hv, Bool.false_eq_true, ↓reduceIte] at h; cases h
                    | true =>
                      simp only [hv, ↓reduceIte] at h
                      rw [← (valueEqM_eq_true_iff cur before).mp hv] at hload
                      rcases interp_bind_eq_error h with hstore | ⟨_, _, h⟩
                      · exact Or.inr (Or.inr (Or.inr
                          ⟨al, m1, rfl, Nat.not_lt.mp hbig, hload, hstore⟩))
                      · cases h
            | _ =>
              dsimp only [ub] at h; cases h
              exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, (fun _ hc => by cases hc), rfl⟩))
      · dsimp only [evalIntrinsicM, ub] at h; cases h
        exact Or.inr (Or.inl ⟨_, pty, cur, currTy, next, nextTy, rfl,
          (fun _ hc => by cases (Pointer.mk.inj (Value.Ptr.inj hc)).2), rfl⟩)
      · dsimp only [evalIntrinsicM, ub] at h; cases h
        exact Or.inr (Or.inl ⟨_, pty, cur, currTy, next, nextTy, rfl,
          (fun _ hc => by cases hc), rfl⟩)
      · dsimp only [evalIntrinsicM, ub] at h; cases h
        exact Or.inr (Or.inl ⟨_, pty, cur, currTy, next, nextTy, rfl,
          (fun _ hc => by cases hc), rfl⟩)
      · dsimp only [evalIntrinsicM, ub] at h; cases h
        exact Or.inr (Or.inl ⟨_, pty, cur, currTy, next, nextTy, rfl,
          (fun _ hc => by cases hc), rfl⟩)
    · dsimp only [evalIntrinsicM, ub] at h; cases h
      exact Or.inl ⟨by simp only [List.length_cons]; omega, rfl⟩
  · rintro (⟨hlen, rfl⟩ | ⟨ptrV, pty, cur, currTy, next, nextTy, rfl, hnt, rfl⟩ |
      ⟨ptr, pty, cur, currTy, next, nextTy, rfl, hcase⟩)
    · exact atomicCompareExchange_arity_ub m args retTy hlen
    · exact atomicCompareExchange_not_thin_ptr_ub m ptrV pty cur next currTy nextTy retTy hnt
    · rcases hcase with ⟨hc1, rfl⟩ | ⟨hc1, hc2, rfl⟩ | ⟨hc1, hc2, hni, rfl⟩ |
        ⟨t, rfl, rfl, rfl, hinner⟩
      · exact atomicCompareExchange_current_type_ub m ptr pty cur next currTy nextTy retTy hc1
      · exact atomicCompareExchange_next_type_ub m ptr pty cur next currTy nextTy retTy hc1 hc2
      · exact atomicCompareExchange_non_int_ub m ptr pty cur next currTy nextTy retTy hc1 hc2 hni
      · rcases hinner with ⟨hal, rfl⟩ | ⟨al, hal, hbig, rfl⟩ | ⟨al, hal, hsz, hload⟩ |
          ⟨al, m1, hal, hsz, hload, hstore⟩
        · exact atomicCompareExchange_ill_formed_int_specPanic m ptr pty cur next t hal
        · exact atomicCompareExchange_size_too_big_ub m ptr pty cur next t hal hbig
        · exact atomicCompareExchange_load_error pty cur next hal hsz hload
        · exact atomicCompareExchange_store_error pty hal hsz hload hstore

/-- The complete access log of a successful `AtomicCompareExchange`, without
side hypotheses: it returned `current` and logged an atomic `Load` followed by
an atomic `Store`, or it returned something else and logged only the atomic
`Load`. Both accesses cover exactly the `t.size` bytes at the pointer. -/
theorem atomicCompareExchange_accesses {m m' : Machine M}
    {ptr : ThinPointer (Memory.Provenance M)} {pty : «Type»} {cur next val : Value M}
    {t : IntType}
    (h : evalIntrinsicM m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (cur, .Int t), (next, .Int t)] (.Int t) = .ok (val, m')) :
    (cur = val ∧ m'.mem.accesses = m.mem.accesses ++
        [⟨.Load, .Atomic, ptr.addr, t.size⟩, ⟨.Store, .Atomic, ptr.addr, t.size⟩]) ∨
    (cur ≠ val ∧
      m'.mem.accesses = m.mem.accesses ++ [⟨.Load, .Atomic, ptr.addr, t.size⟩]) := by
  by_cases hcv : cur = val
  · subst hcv
    obtain ⟨bytes, henc, hacc⟩ := atomicCompareExchange_success_accesses h
    rw [encodeM_int_length henc] at hacc
    exact Or.inl ⟨rfl, hacc⟩
  · exact Or.inr ⟨hcv, atomicCompareExchange_failure_accesses h hcv⟩

/-- `AtomicCompareExchange` never checks `current` against the type: upstream
compares it structurally with the loaded value and nothing else. A `current`
that is not a `Value::Int` (an ill-typed argument) therefore makes the
compare-exchange fail silently: it is exactly its load, and `next` is never
looked at. Contrast `atomicFetchAndOp_other_not_int_specPanic`, where an
ill-typed operand reaches `unreachable!()`. -/
theorem atomicCompareExchange_current_not_int {m m1 : Machine M}
    {ptr : ThinPointer (Memory.Provenance M)} (pty : «Type») {cur before : Value M}
    (next : Value M) {t : IntType} {al : Align}
    (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hload : typedLoadM m ptr (.Int t) al .Atomic = .ok (before, m1))
    (hcur : ∀ i, cur ≠ .Int i) :
    evalIntrinsicM m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (cur, .Int t), (next, .Int t)] (.Int t) =
      .ok (before, m1) := by
  obtain ⟨i, hi⟩ := typedLoadM_int_returns_int hload
  exact atomicCompareExchange_failure pty next hal hsz hload (fun hc => hcur i (hc.trans hi))

/-- A succeeding `AtomicCompareExchange` hands the memory model's `store` bytes
without provenance: the memory of the resulting machine is `M::store` of
`t.size` bytes that are all `AbstractByte::Init(b, None)`, applied to the memory
after the load. Whatever provenance the overwritten bytes carried is gone, even
when `next` is the integer that was there. -/
theorem atomicCompareExchange_success_stores_no_provenance {m m' : Machine M}
    {ptr : ThinPointer (Memory.Provenance M)} {pty : «Type»} {cur next : Value M}
    {t : IntType}
    (h : evalIntrinsicM m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (cur, .Int t), (next, .Int t)] (.Int t) = .ok (cur, m')) :
    ∃ (al : Align) (m1 : Machine M) (bytes : List (AbstractByte (Memory.Provenance M))),
      typedLoadM m ptr (.Int t) al .Atomic = .ok (cur, m1) ∧
      (∀ b ∈ bytes, ∃ u, b = AbstractByte.Init u none) ∧
      bytes.length = t.size.bytes ∧
      MemoryOps.store m1.mem.memory ptr bytes al = .ok m'.mem.memory := by
  obtain ⟨al, hal, hsz⟩ := atomicCompareExchange_ok_size h
  rw [atomicCompareExchange_eq m ptr pty cur next t hal hsz] at h
  obtain ⟨⟨b, m1⟩, hload, h⟩ := interp_bind_eq_ok h
  dsimp only at h
  cases hv : valueEqM cur b with
  | true =>
    simp only [hv, ↓reduceIte] at h
    obtain ⟨m2, hstore, h⟩ := interp_bind_eq_ok h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok h)
    obtain ⟨bytes, henc, hmem⟩ := typedStoreM_ok_memory hstore
    exact ⟨al, m1, bytes, hload, encodeM_int_no_provenance henc, encodeM_int_length henc, hmem⟩
  | false =>
    simp only [hv, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok h)
    rw [valueEqM_refl] at hv
    cases hv

/-! ### `AtomicFetchAndOp` -/

/-- `AtomicFetchAndOp` whose operand has another type than the return type is
UB. -/
theorem atomicFetchAndOp_other_type_ub (m : Machine M) (binOp : IntBinOp)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (other : Value M)
    (otherTy retTy : «Type») (h : typeEq otherTy retTy = false) :
    evalIntrinsicM m (.AtomicFetchAndOp binOp)
        [(.Ptr ⟨ptr, none⟩, pty), (other, otherTy)] retTy =
      .error (.ub "invalid second argument to `AtomicFetchAndOp` intrinsic: not same type as return value") := by
  simp only [evalIntrinsicM, h, Bool.not_false, ↓reduceIte]
  rfl

/-- `AtomicFetchAndOp` at a non-integer type is UB. -/
theorem atomicFetchAndOp_non_int_ub (m : Machine M) (binOp : IntBinOp)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (other : Value M)
    (otherTy retTy : «Type») (h : typeEq otherTy retTy = true) (hni : ∀ t, retTy ≠ .Int t) :
    evalIntrinsicM m (.AtomicFetchAndOp binOp)
        [(.Ptr ⟨ptr, none⟩, pty), (other, otherTy)] retTy =
      .error (.ub "invalid return type for `AtomicFetchAndOp` intrinsic: only works with integers") := by
  simp only [evalIntrinsicM, h, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases retTy with
  | Int t => exact absurd rfl (hni t)
  | _ => rfl

/-- `AtomicFetchAndOp` at an integer type larger than `MAX_ATOMIC_SIZE` is UB. -/
theorem atomicFetchAndOp_size_too_big_ub (m : Machine M) (binOp : IntBinOp)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (other : Value M)
    (t : IntType) {al : Align} (hal : alignFromBytes t.size.bytes = some al)
    (hbig : t.size.bytes > x86_64.MAX_ATOMIC_SIZE.bytes) :
    evalIntrinsicM m (.AtomicFetchAndOp binOp)
        [(.Ptr ⟨ptr, none⟩, pty), (other, .Int t)] (.Int t) =
      .error (.ub "invalid return type for `AtomicFetchAndOp` intrinsic: size too big") := by
  have hte : typeEq (.Int t) (.Int t) = true := by simp only [typeEq, beq_self_eq_true]
  have ha : alignFromBytesInt (t.size.bytes : Int) = some al := by
    rw [alignFromBytesInt_natCast]
    exact hal
  simp only [evalIntrinsicM, hte, Bool.not_true, Bool.false_eq_true, ↓reduceIte, layout_int hal,
    interp_ok_bind, LayoutStrategy.expect_size, interp_pure_bind, ha, hbig]
  rfl

/-- `AtomicFetchAndOp` at an integer type whose size is not a power of two is a
spec panic already in `Type::layout` (`IntType::align`), so the
`Align::from_bytes(size.bytes()).unwrap()` of the intrinsic itself is never the
one that panics. -/
theorem atomicFetchAndOp_ill_formed_int_specPanic (m : Machine M) (binOp : IntBinOp)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (other : Value M)
    (t : IntType) (hal : alignFromBytes t.size.bytes = none) :
    evalIntrinsicM m (.AtomicFetchAndOp binOp)
        [(.Ptr ⟨ptr, none⟩, pty), (other, .Int t)] (.Int t) =
      .error (.specPanic "Align::from_bytes(size).unwrap()") := by
  have hte : typeEq (.Int t) (.Int t) = true := by simp only [typeEq, beq_self_eq_true]
  simp only [evalIntrinsicM, hte, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    layout_int_ill_formed hal, interp_error_bind]

/-- A well-shaped `AtomicFetchAndOp` is an atomic `typed_load`, then
`eval_int_bin_op` on the loaded and the given integer, then an atomic
`typed_store` of the result *as is*; it returns the loaded value. -/
theorem atomicFetchAndOp_eq (m : Machine M) (binOp : IntBinOp)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (other : Value M) (t : IntType)
    {al : Align} (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes) :
    evalIntrinsicM m (.AtomicFetchAndOp binOp)
        [(.Ptr ⟨ptr, none⟩, pty), (other, .Int t)] (.Int t) =
      (typedLoadM m ptr (.Int t) al .Atomic >>= fun (previous, m1) =>
        match other with
        | .Int otherInt =>
          match previous with
          | .Int previousInt =>
            evalIntBinOp binOp previousInt otherInt t >>= fun nextInt =>
              typedStoreM m1 ptr (.Int nextInt) (.Int t) al .Atomic >>= fun m2 =>
                pure (previous, m2)
          | _ => specPanic "unreachable: AtomicFetchAndOp previous not Value::Int"
        | _ => specPanic "unreachable: AtomicFetchAndOp other not Value::Int") := by
  have hte : typeEq (.Int t) (.Int t) = true := by simp only [typeEq, beq_self_eq_true]
  have ha : alignFromBytesInt (t.size.bytes : Int) = some al := by
    rw [alignFromBytesInt_natCast]
    exact hal
  have hn : ¬ (t.size.bytes > x86_64.MAX_ATOMIC_SIZE.bytes) := Nat.not_lt.mpr hsz
  simp only [evalIntrinsicM, hte, Bool.not_true, Bool.false_eq_true, ↓reduceIte, layout_int hal,
    interp_ok_bind, LayoutStrategy.expect_size, interp_pure_bind, ha, hn]
  rfl

/-- `AtomicFetchAndOp` succeeds when its load, its operation, and its store
do, and returns the *previous* value. -/
theorem atomicFetchAndOp_ok {m m1 m2 : Machine M} (binOp : IntBinOp)
    {ptr : ThinPointer (Memory.Provenance M)} (pty : «Type») {p o n : Int} {t : IntType}
    {al : Align} (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hload : typedLoadM m ptr (.Int t) al .Atomic = .ok (.Int p, m1))
    (hop : evalIntBinOp binOp p o t = .ok n)
    (hstore : typedStoreM m1 ptr (.Int n) (.Int t) al .Atomic = .ok m2) :
    evalIntrinsicM m (.AtomicFetchAndOp binOp)
        [(.Ptr ⟨ptr, none⟩, pty), (.Int o, .Int t)] (.Int t) =
      .ok (.Int p, m2) := by
  rw [atomicFetchAndOp_eq m binOp ptr pty (.Int o) t hal hsz, hload]
  simp only [interp_ok_bind, hop, hstore]
  rfl

/-- UB (or any other `Stop`) of `eval_int_bin_op` is the outcome of the whole
`AtomicFetchAndOp`; nothing is stored. -/
theorem atomicFetchAndOp_binop_error {m m1 : Machine M} (binOp : IntBinOp)
    {ptr : ThinPointer (Memory.Provenance M)} (pty : «Type») {p o : Int} {t : IntType}
    {al : Align} {e : Stop} (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hload : typedLoadM m ptr (.Int t) al .Atomic = .ok (.Int p, m1))
    (hop : evalIntBinOp binOp p o t = .error e) :
    evalIntrinsicM m (.AtomicFetchAndOp binOp)
        [(.Ptr ⟨ptr, none⟩, pty), (.Int o, .Int t)] (.Int t) =
      .error e := by
  rw [atomicFetchAndOp_eq m binOp ptr pty (.Int o) t hal hsz, hload]
  simp only [interp_ok_bind, hop, interp_error_bind]

/-- A stopping store makes the whole `AtomicFetchAndOp` stop the same way. -/
theorem atomicFetchAndOp_store_error {m m1 : Machine M} (binOp : IntBinOp)
    {ptr : ThinPointer (Memory.Provenance M)} (pty : «Type») {p o n : Int} {t : IntType}
    {al : Align} {e : Stop} (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hload : typedLoadM m ptr (.Int t) al .Atomic = .ok (.Int p, m1))
    (hop : evalIntBinOp binOp p o t = .ok n)
    (hstore : typedStoreM m1 ptr (.Int n) (.Int t) al .Atomic = .error e) :
    evalIntrinsicM m (.AtomicFetchAndOp binOp)
        [(.Ptr ⟨ptr, none⟩, pty), (.Int o, .Int t)] (.Int t) =
      .error e := by
  rw [atomicFetchAndOp_eq m binOp ptr pty (.Int o) t hal hsz, hload]
  simp only [interp_ok_bind, hop, hstore, interp_error_bind]

/-- A stopping load makes the whole `AtomicFetchAndOp` stop the same way. -/
theorem atomicFetchAndOp_load_error {m : Machine M} (binOp : IntBinOp)
    {ptr : ThinPointer (Memory.Provenance M)} (pty : «Type») (other : Value M) {t : IntType}
    {al : Align} {e : Stop} (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hload : typedLoadM m ptr (.Int t) al .Atomic = .error e) :
    evalIntrinsicM m (.AtomicFetchAndOp binOp)
        [(.Ptr ⟨ptr, none⟩, pty), (other, .Int t)] (.Int t) =
      .error e := by
  rw [atomicFetchAndOp_eq m binOp ptr pty other t hal hsz, hload]
  rfl

/-- An operand that is not a `Value::Int` at an integer type reaches
upstream's `unreachable!()` after the load: a spec panic (the value is
ill-typed), not UB. -/
theorem atomicFetchAndOp_other_not_int_specPanic {m : Machine M} (binOp : IntBinOp)
    {ptr : ThinPointer (Memory.Provenance M)} (pty : «Type») {other : Value M} {t : IntType}
    {al : Align} {r : Value M × Machine M} (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hload : typedLoadM m ptr (.Int t) al .Atomic = .ok r)
    (hother : ∀ i, other ≠ .Int i) :
    evalIntrinsicM m (.AtomicFetchAndOp binOp)
        [(.Ptr ⟨ptr, none⟩, pty), (other, .Int t)] (.Int t) =
      .error (.specPanic "unreachable: AtomicFetchAndOp other not Value::Int") := by
  rw [atomicFetchAndOp_eq m binOp ptr pty other t hal hsz, hload]
  cases other with
  | Int i => exact absurd rfl (hother i)
  | _ => rfl

/-- Complete characterization of a successful `AtomicFetchAndOp` in every memory
model: it loads an integer `prevInt`, applies `eval_int_bin_op` to `prevInt`
and `otherInt`, stores `nextInt` *as is* with `Atomicity::Atomic`, and returns
`prevInt`. -/
theorem atomicFetchAndOp_ok_iff {m m' : Machine M} {binOp : IntBinOp}
    {args : List (Value M × «Type»)} {retTy : «Type»} {val : Value M} :
    evalIntrinsicM m (.AtomicFetchAndOp binOp) args retTy = .ok (val, m') ↔
      ∃ ptr pty prevInt otherInt nextInt t al m1,
        args = [(.Ptr ⟨ptr, none⟩, pty), (.Int otherInt, .Int t)] ∧
        retTy = .Int t ∧
        val = .Int prevInt ∧
        alignFromBytes t.size.bytes = some al ∧
        t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes ∧
        typedLoadM m ptr (.Int t) al .Atomic = .ok (.Int prevInt, m1) ∧
        evalIntBinOp binOp prevInt otherInt t = .ok nextInt ∧
        typedStoreM m1 ptr (.Int nextInt) (.Int t) al .Atomic = .ok m' := by
  constructor
  · intro h
    rcases args with _ | ⟨⟨ptrV, pty⟩, _ | ⟨⟨other, otherTy⟩, _ | ⟨_, _⟩⟩⟩
    · dsimp only [evalIntrinsicM, ub] at h; cases h
    · dsimp only [evalIntrinsicM, ub] at h; cases h
    · rcases ptrV with _ | _ | ⟨ptr, _ | _⟩ | _ | _ | _
      all_goals try (dsimp only [evalIntrinsicM, ub] at h; cases h)
      dsimp only [evalIntrinsicM] at h
      cases hc : typeEq otherTy retTy with
      | false => simp only [hc, Bool.not_false, ↓reduceIte, ub] at h; cases h
      | true =>
        simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        cases retTy with
        | Int t =>
          obtain rfl := (typeEq_int_right_iff otherTy t).mp hc
          cases hal : alignFromBytes t.size.bytes with
          | none =>
            simp only [layout_int_ill_formed hal, interp_error_bind] at h; cases h
          | some al =>
            have ha : alignFromBytesInt (t.size.bytes : Int) = some al := by
              rw [alignFromBytesInt_natCast]; exact hal
            simp only [layout_int hal, interp_ok_bind, LayoutStrategy.expect_size,
              interp_pure_bind, ha] at h
            by_cases hbig : t.size.bytes > x86_64.MAX_ATOMIC_SIZE.bytes
            · simp only [hbig, ↓reduceIte, ub] at h; cases h
            · simp only [hbig, ↓reduceIte] at h
              obtain ⟨⟨previous, m1⟩, hload, h⟩ := interp_bind_eq_ok h
              dsimp only at h
              cases other with
              | Int otherInt =>
                cases previous with
                | Int prevInt =>
                  obtain ⟨nextInt, hop, h⟩ := interp_bind_eq_ok h
                  obtain ⟨m2, hstore, h⟩ := interp_bind_eq_ok h
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok h)
                  exact ⟨ptr, pty, prevInt, otherInt, nextInt, t, al, m1, rfl, rfl, rfl, hal,
                    Nat.not_lt.mp hbig, hload, hop, hstore⟩
                | _ => dsimp only [specPanic] at h; cases h
              | _ => dsimp only [specPanic] at h; cases h
        | _ => dsimp only [ub] at h; cases h
    · dsimp only [evalIntrinsicM, ub] at h; cases h
  · rintro ⟨ptr, pty, prevInt, otherInt, nextInt, t, al, m1, rfl, rfl, rfl, hal, hsz, hload,
      hop, hstore⟩
    exact atomicFetchAndOp_ok binOp pty hal hsz hload hop hstore

/-- Complete characterization of every stopping outcome (UB or spec panic, in
exact upstream check order) of `AtomicFetchAndOp` in every memory model.
Neither the intrinsic's own `Align::from_bytes(size.bytes()).unwrap()` panic
nor the `unreachable!()` on `previous` can occur (`Type::layout` panics first
for non-power-of-two integer sizes, and `typed_load` at `Type::Int` only ever
returns `Value::Int`). -/
theorem atomicFetchAndOp_error_iff {m : Machine M} {binOp : IntBinOp}
    {args : List (Value M × «Type»)} {retTy : «Type»} {e : Stop} :
    evalIntrinsicM m (.AtomicFetchAndOp binOp) args retTy = .error e ↔
      (args.length ≠ 2 ∧
        e = .ub "invalid number of arguments for `AtomicFetchAndOp` intrinsic") ∨
      (∃ ptrV pty other otherTy, args = [(ptrV, pty), (other, otherTy)] ∧
        (∀ p, ptrV ≠ .Ptr ⟨p, none⟩) ∧
        e = .ub "invalid first argument to `AtomicFetchAndOp` intrinsic: not a thin pointer") ∨
      (∃ ptr pty other otherTy, args = [(.Ptr ⟨ptr, none⟩, pty), (other, otherTy)] ∧
        ((typeEq otherTy retTy = false ∧
          e = .ub "invalid second argument to `AtomicFetchAndOp` intrinsic: not same type as return value") ∨
         (typeEq otherTy retTy = true ∧ (∀ t, retTy ≠ .Int t) ∧
          e = .ub "invalid return type for `AtomicFetchAndOp` intrinsic: only works with integers") ∨
         (∃ t, otherTy = .Int t ∧ retTy = .Int t ∧
           ((alignFromBytes t.size.bytes = none ∧
             e = .specPanic "Align::from_bytes(size).unwrap()") ∨
            (∃ al, alignFromBytes t.size.bytes = some al ∧
              t.size.bytes > x86_64.MAX_ATOMIC_SIZE.bytes ∧
              e = .ub "invalid return type for `AtomicFetchAndOp` intrinsic: size too big") ∨
            (∃ al, alignFromBytes t.size.bytes = some al ∧
              t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes ∧
              typedLoadM m ptr (.Int t) al .Atomic = .error e) ∨
            (∃ al r, alignFromBytes t.size.bytes = some al ∧
              t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes ∧
              typedLoadM m ptr (.Int t) al .Atomic = .ok r ∧
              (∀ i, other ≠ .Int i) ∧
              e = .specPanic "unreachable: AtomicFetchAndOp other not Value::Int") ∨
            (∃ al prevInt otherInt m1, alignFromBytes t.size.bytes = some al ∧
              t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes ∧
              other = .Int otherInt ∧
              typedLoadM m ptr (.Int t) al .Atomic = .ok (.Int prevInt, m1) ∧
              evalIntBinOp binOp prevInt otherInt t = .error e) ∨
            (∃ al prevInt otherInt nextInt m1, alignFromBytes t.size.bytes = some al ∧
              t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes ∧
              other = .Int otherInt ∧
              typedLoadM m ptr (.Int t) al .Atomic = .ok (.Int prevInt, m1) ∧
              evalIntBinOp binOp prevInt otherInt t = .ok nextInt ∧
              typedStoreM m1 ptr (.Int nextInt) (.Int t) al .Atomic = .error e))))) := by
  constructor
  · intro h
    rcases args with _ | ⟨⟨ptrV, pty⟩, _ | ⟨⟨other, otherTy⟩, _ | ⟨_, _⟩⟩⟩
    · dsimp only [evalIntrinsicM, ub] at h; cases h; exact Or.inl ⟨by show 0 ≠ 2; decide, rfl⟩
    · dsimp only [evalIntrinsicM, ub] at h; cases h; exact Or.inl ⟨by show 1 ≠ 2; decide, rfl⟩
    · rcases ptrV with _ | _ | ⟨ptr, _ | _⟩ | _ | _ | _
      · dsimp only [evalIntrinsicM, ub] at h; cases h
        exact Or.inr (Or.inl ⟨_, pty, other, otherTy, rfl, (fun _ hc => by cases hc), rfl⟩)
      · dsimp only [evalIntrinsicM, ub] at h; cases h
        exact Or.inr (Or.inl ⟨_, pty, other, otherTy, rfl, (fun _ hc => by cases hc), rfl⟩)
      · dsimp only [evalIntrinsicM] at h
        refine Or.inr (Or.inr ⟨ptr, pty, other, otherTy, rfl, ?_⟩)
        cases hc : typeEq otherTy retTy with
        | false =>
          simp only [hc, Bool.not_false, ↓reduceIte, ub] at h; cases h
          exact Or.inl ⟨rfl, rfl⟩
        | true =>
          simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          cases retTy with
          | Int t =>
            have hot := (typeEq_int_right_iff otherTy t).mp hc
            refine Or.inr (Or.inr ⟨t, hot, rfl, ?_⟩)
            cases hal : alignFromBytes t.size.bytes with
            | none =>
              simp only [layout_int_ill_formed hal, interp_error_bind] at h; cases h
              exact Or.inl ⟨rfl, rfl⟩
            | some al =>
              have ha : alignFromBytesInt (t.size.bytes : Int) = some al := by
                rw [alignFromBytesInt_natCast]; exact hal
              simp only [layout_int hal, interp_ok_bind, LayoutStrategy.expect_size,
                interp_pure_bind, ha] at h
              by_cases hbig : t.size.bytes > x86_64.MAX_ATOMIC_SIZE.bytes
              · simp only [hbig, ↓reduceIte, ub] at h; cases h
                exact Or.inr (Or.inl ⟨al, rfl, hbig, rfl⟩)
              · simp only [hbig, ↓reduceIte] at h
                rcases interp_bind_eq_error h with hload | ⟨⟨previous, m1⟩, hload, h⟩
                · exact Or.inr (Or.inr (Or.inl ⟨al, rfl, Nat.not_lt.mp hbig, hload⟩))
                · obtain ⟨prevInt, rfl⟩ := typedLoadM_int_returns_int hload
                  dsimp only at h
                  cases other with
                  | Int otherInt =>
                    rcases interp_bind_eq_error h with hop | ⟨nextInt, hop, h⟩
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                        ⟨al, prevInt, otherInt, m1, rfl, Nat.not_lt.mp hbig, rfl, hload, hop⟩))))
                    · rcases interp_bind_eq_error h with hstore | ⟨_, _, h⟩
                      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                          ⟨al, prevInt, otherInt, nextInt, m1, rfl, Nat.not_lt.mp hbig, rfl,
                            hload, hop, hstore⟩))))
                      · cases h
                  | _ =>
                    dsimp only [specPanic] at h; cases h
                    exact Or.inr (Or.inr (Or.inr (Or.inl
                      ⟨al, (.Int prevInt, m1), rfl, Nat.not_lt.mp hbig, hload,
                        (fun _ hc => by cases hc), rfl⟩)))
          | _ =>
            dsimp only [ub] at h; cases h
            exact Or.inr (Or.inl ⟨rfl, (fun _ hc' => by cases hc'), rfl⟩)
      · dsimp only [evalIntrinsicM, ub] at h; cases h
        exact Or.inr (Or.inl ⟨_, pty, other, otherTy, rfl,
          (fun _ hc => by cases (Pointer.mk.inj (Value.Ptr.inj hc)).2), rfl⟩)
      · dsimp only [evalIntrinsicM, ub] at h; cases h
        exact Or.inr (Or.inl ⟨_, pty, other, otherTy, rfl, (fun _ hc => by cases hc), rfl⟩)
      · dsimp only [evalIntrinsicM, ub] at h; cases h
        exact Or.inr (Or.inl ⟨_, pty, other, otherTy, rfl, (fun _ hc => by cases hc), rfl⟩)
      · dsimp only [evalIntrinsicM, ub] at h; cases h
        exact Or.inr (Or.inl ⟨_, pty, other, otherTy, rfl, (fun _ hc => by cases hc), rfl⟩)
    · dsimp only [evalIntrinsicM, ub] at h; cases h
      exact Or.inl ⟨by simp only [List.length_cons]; omega, rfl⟩
  · rintro (⟨hlen, rfl⟩ | ⟨ptrV, pty, other, otherTy, rfl, hnt, rfl⟩ |
      ⟨ptr, pty, other, otherTy, rfl, hcase⟩)
    · exact atomicFetchAndOp_arity_ub m binOp args retTy hlen
    · exact atomicFetchAndOp_not_thin_ptr_ub m binOp ptrV pty other otherTy retTy hnt
    · rcases hcase with ⟨hc, rfl⟩ | ⟨hc, hni, rfl⟩ | ⟨t, rfl, rfl, hinner⟩
      · exact atomicFetchAndOp_other_type_ub m binOp ptr pty other otherTy retTy hc
      · exact atomicFetchAndOp_non_int_ub m binOp ptr pty other otherTy retTy hc hni
      · rcases hinner with ⟨hal, rfl⟩ | ⟨al, hal, hbig, rfl⟩ | ⟨al, hal, hsz, hload⟩ |
          ⟨al, r, hal, hsz, hload, hni, rfl⟩ |
          ⟨al, prevInt, otherInt, m1, hal, hsz, rfl, hload, hop⟩ |
          ⟨al, prevInt, otherInt, nextInt, m1, hal, hsz, rfl, hload, hop, hstore⟩
        · exact atomicFetchAndOp_ill_formed_int_specPanic m binOp ptr pty other t hal
        · exact atomicFetchAndOp_size_too_big_ub m binOp ptr pty other t hal hbig
        · exact atomicFetchAndOp_load_error binOp pty other hal hsz hload
        · exact atomicFetchAndOp_other_not_int_specPanic binOp pty hal hsz hload hni
        · exact atomicFetchAndOp_binop_error binOp pty hal hsz hload hop
        · exact atomicFetchAndOp_store_error binOp pty hal hsz hload hop hstore

/-- A successful `AtomicFetchAndOp` hands the memory model's `store` bytes
without provenance: the memory of the resulting machine is `M::store` of
`t.size` bytes that are all `AbstractByte::Init(b, None)`, applied to the memory
after the load. Whatever provenance the overwritten bytes carried is gone, even
when the operation leaves the integer unchanged (`fetch_add(0)`). -/
theorem atomicFetchAndOp_stores_no_provenance {m m' : Machine M} {binOp : IntBinOp}
    {ptr : ThinPointer (Memory.Provenance M)} {pty : «Type»} {other val : Value M}
    {t : IntType}
    (h : evalIntrinsicM m (.AtomicFetchAndOp binOp)
        [(.Ptr ⟨ptr, none⟩, pty), (other, .Int t)] (.Int t) = .ok (val, m')) :
    ∃ (al : Align) (m1 : Machine M) (bytes : List (AbstractByte (Memory.Provenance M))),
      typedLoadM m ptr (.Int t) al .Atomic = .ok (val, m1) ∧
      (∀ b ∈ bytes, ∃ u, b = AbstractByte.Init u none) ∧
      bytes.length = t.size.bytes ∧
      MemoryOps.store m1.mem.memory ptr bytes al = .ok m'.mem.memory := by
  obtain ⟨ptr', _, _, _, _, t', al, m1, hargs, hret, hval, _, _, hload, _, hstore⟩ :=
    atomicFetchAndOp_ok_iff.mp h
  have h1a := (List.cons.inj hargs).1
  have hptr : ptr = ptr' := (Pointer.mk.inj (Value.Ptr.inj (Prod.mk.inj h1a).1)).1
  have ht : t = t' := by
    cases hret
    rfl
  rw [← hptr, ← ht] at hload hstore
  rw [← hval] at hload
  obtain ⟨bytes, henc, hmem⟩ := typedStoreM_ok_memory hstore
  exact ⟨al, m1, bytes, hload, encodeM_int_no_provenance henc, encodeM_int_length henc, hmem⟩

/-- Passing `permEnumA` and `permEnumB` (`permEnumA ≠ permEnumB`) passes `typeEq`
and triggers the non-integer return type UB (not `"not same type as return value"`),
so `atomicCompareExchange_error_iff` and `atomicFetchAndOp_error_iff` cannot
replace `typeEq` by propositional `=`. -/
theorem atomic_enum_extensional_typeEq_ub (m : Machine M)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (v1 v2 : Value M) (binOp : IntBinOp) :
    permEnumA ≠ permEnumB ∧
    evalIntrinsicM m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (v1, permEnumA), (v2, permEnumA)] permEnumB =
      .error (.ub "invalid return type for `Intrinis::AtomicCompareExchange`: only works with integers") ∧
    evalIntrinsicM m (.AtomicFetchAndOp binOp)
        [(.Ptr ⟨ptr, none⟩, pty), (v1, permEnumA)] permEnumB =
      .error (.ub "invalid return type for `AtomicFetchAndOp` intrinsic: only works with integers") :=
  ⟨permEnum_typeEq_ne.2,
   atomicCompareExchange_non_int_ub m ptr pty v1 v2 permEnumA permEnumA permEnumB
     permEnum_typeEq_ne.1 permEnum_typeEq_ne.1 (fun _ h => by dsimp only [permEnumB] at h; cases h),
   atomicFetchAndOp_non_int_ub m binOp ptr pty v1 permEnumA permEnumB
     permEnum_typeEq_ne.1 (fun _ h => by dsimp only [permEnumB] at h; cases h)⟩

/-! ### `eval_int_bin_op` as used by `AtomicFetchAndOp` -/

/-- `Add`, `Sub`, `Mul`, `BitAnd`, `BitOr`, and `BitXor` never fail and never
wrap: they return the mathematical result, in or out of the integer type. -/
theorem evalIntBinOp_total_ops (l r : Int) (t : IntType) :
    evalIntBinOp .Add l r t = .ok (l + r) ∧
    evalIntBinOp .Sub l r t = .ok (l - r) ∧
    evalIntBinOp .Mul l r t = .ok (l * r) ∧
    evalIntBinOp .BitAnd l r t = .ok (intBitAnd l r) ∧
    evalIntBinOp .BitOr l r t = .ok (intBitOr l r) ∧
    evalIntBinOp .BitXor l r t = .ok (intBitXor l r) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Division by zero is UB. -/
theorem evalIntBinOp_div_zero (l : Int) (t : IntType) :
    evalIntBinOp .Div l 0 t = .error (.ub "division by zero") := rfl

/-- Remainder by zero is UB. -/
theorem evalIntBinOp_rem_zero (l : Int) (t : IntType) :
    evalIntBinOp .Rem l 0 t = .error (.ub "modulus of remainder is zero") := rfl

/-- A quotient outside the integer type (`INT_MIN / -1`) is UB. -/
theorem evalIntBinOp_div_overflow {l r : Int} {t : IntType} (hr : r ≠ 0)
    (hov : IntType.can_represent t (Int.tdiv l r) = false) :
    evalIntBinOp .Div l r t = .error (.ub "overflow in division") := by
  simp only [evalIntBinOp, hr, ↓reduceIte, hov, Bool.not_false]
  rfl

/-- A remainder whose quotient is outside the integer type (`INT_MIN % -1`) is UB. -/
theorem evalIntBinOp_rem_overflow {l r : Int} {t : IntType} (hr : r ≠ 0)
    (hov : IntType.can_represent t (Int.tdiv l r) = false) :
    evalIntBinOp .Rem l r t = .error (.ub "overflow in remainder") := by
  simp only [evalIntBinOp, hr, ↓reduceIte, hov, Bool.not_false]
  rfl

/-- An unchecked left shift by a negative amount or by at least the bit width
is UB. -/
theorem evalIntBinOp_shlUnchecked_oob (l : Int) {r : Int} {t : IntType}
    (h : r < 0 ∨ r ≥ (Size.bits t.size : Int)) :
    evalIntBinOp .ShlUnchecked l r t = .error (.ub "overflow in unchecked shift") := by
  simp only [evalIntBinOp, h, ↓reduceIte]
  rfl

/-- An unchecked right shift by a negative amount or by at least the bit width
is UB. -/
theorem evalIntBinOp_shrUnchecked_oob (l : Int) {r : Int} {t : IntType}
    (h : r < 0 ∨ r ≥ (Size.bits t.size : Int)) :
    evalIntBinOp .ShrUnchecked l r t = .error (.ub "overflow in unchecked shift") := by
  simp only [evalIntBinOp, h, ↓reduceIte]
  rfl

/-- `Shl` and `Shr` reduce the shift count modulo the bit width and never fail
in `eval_int_bin_op` (like `Add`/`Sub`/`Mul`, `Shl` does not bring its result
back in bounds). -/
theorem evalIntBinOp_shl_shr (l r : Int) (t : IntType) :
    evalIntBinOp .Shl l r t = .ok (l * (2 : Int) ^ (r % (Size.bits t.size : Int)).toNat) ∧
    evalIntBinOp .Shr l r t = .ok (l / (2 : Int) ^ (r % (Size.bits t.size : Int)).toNat) :=
  ⟨rfl, rfl⟩

/-- An unchecked addition whose sum is outside the integer type is UB. -/
theorem evalIntBinOp_addUnchecked_overflow {l r : Int} {t : IntType}
    (hov : IntType.can_represent t (l + r) = false) :
    evalIntBinOp .AddUnchecked l r t = .error (.ub "overflow in unchecked add") := by
  simp only [evalIntBinOp, hov, Bool.not_false, ↓reduceIte]
  rfl

/-- An unchecked subtraction whose difference is outside the integer type is UB. -/
theorem evalIntBinOp_subUnchecked_overflow {l r : Int} {t : IntType}
    (hov : IntType.can_represent t (l - r) = false) :
    evalIntBinOp .SubUnchecked l r t = .error (.ub "overflow in unchecked sub") := by
  simp only [evalIntBinOp, hov, Bool.not_false, ↓reduceIte]
  rfl

/-- An unchecked multiplication whose product is outside the integer type is UB. -/
theorem evalIntBinOp_mulUnchecked_overflow {l r : Int} {t : IntType}
    (hov : IntType.can_represent t (l * r) = false) :
    evalIntBinOp .MulUnchecked l r t = .error (.ub "overflow in unchecked mul") := by
  simp only [evalIntBinOp, hov, Bool.not_false, ↓reduceIte]
  rfl

/-- Exact division by zero is UB. -/
theorem evalIntBinOp_divExact_zero (l : Int) (t : IntType) :
    evalIntBinOp .DivExact l 0 t = .error (.ub "division by zero") := rfl

/-- Exact division whose quotient is outside the integer type (`INT_MIN / -1`) is UB. -/
theorem evalIntBinOp_divExact_overflow {l r : Int} {t : IntType} (hr : r ≠ 0)
    (hov : IntType.can_represent t (Int.tdiv l r) = false) :
    evalIntBinOp .DivExact l r t = .error (.ub "overflow in division") := by
  simp only [evalIntBinOp, hr, ↓reduceIte, hov, Bool.not_false]
  rfl

/-- Exact division with a non-zero remainder is UB. -/
theorem evalIntBinOp_divExact_rem_nonzero {l r : Int} {t : IntType} (hr : r ≠ 0)
    (hin : IntType.can_represent t (Int.tdiv l r) = true) (hrem : Int.tmod l r ≠ 0) :
    evalIntBinOp .DivExact l r t = .error (.ub "non-zero remainder in exact division") := by
  simp only [evalIntBinOp, hr, hin, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  split
  · rfl
  · rename_i hc
    first
      | exact absurd hrem hc
      | exact absurd hc hrem

/-- `i32::MIN / -1` and `i32::MIN % -1` are UB. -/
theorem evalIntBinOp_i32_min_neg_one :
    evalIntBinOp .Div (-2147483648) (-1) itI32 = .error (.ub "overflow in division") ∧
    evalIntBinOp .Rem (-2147483648) (-1) itI32 = .error (.ub "overflow in remainder") :=
  ⟨evalIntBinOp_div_overflow (by decide) (by decide),
   evalIntBinOp_rem_overflow (by decide) (by decide)⟩

/-- `255 + 1` at `u8` is `256`: `eval_int_bin_op` does not wrap, and `256` is
not a `u8`. -/
theorem evalIntBinOp_add_u8_255_1 :
    evalIntBinOp .Add 255 1 itU8 = .ok 256 ∧ IntType.can_represent itU8 256 = false :=
  ⟨rfl, by decide⟩

/-! ### `typed_store` of an out-of-range integer, and memory-model errors -/

/-- `Machine::typed_store` asserts `check_value`: storing an integer that its
type cannot represent is a spec panic, before any memory access. -/
theorem typedStoreM_int_out_of_range (m : Machine M) (ptr : ThinPointer (Memory.Provenance M))
    (n : Int) (t : IntType) (align : Align) (atomicity : Atomicity)
    (hn : IntType.can_represent t n = false) :
    typedStoreM m ptr (.Int n) (.Int t) align atomicity =
      .error (.specPanic "trying to store a value which is ill-formed for its type") := by
  simp only [typedStoreM, checkValueM, ensureElseUb, hn, Bool.not_false, ↓reduceIte, ub]
  rfl

/-- A `Stop` of the memory model's `load` is the outcome of `typed_load`. -/
theorem typedLoadM_load_error {m : Machine M} {ptr : ThinPointer (Memory.Provenance M)}
    {ty : «Type»} {size : Size} {a align : Align} (atomicity : Atomicity) {e : Stop}
    (hl : Type.layout ty = .ok (.Sized size a))
    (hload : MemoryOps.load m.mem.memory ptr size align = .error e) :
    typedLoadM m ptr ty align atomicity = .error e := by
  simp only [typedLoadM, hl, interp_ok_bind, LayoutStrategy.expect_size, interp_pure_bind,
    ConcurrentMemory.load, hload, interp_error_bind]

/-- A `Stop` of the memory model's `store` that does not depend on the bytes
(a misaligned or dangling pointer) is the outcome of `typed_store` of a
representable integer. -/
theorem typedStoreM_int_store_error {m : Machine M} {ptr : ThinPointer (Memory.Provenance M)}
    {i : Int} {t : IntType} {align : Align} (atomicity : Atomicity) {e : Stop}
    (hrep : IntType.can_represent t i = true)
    (hstore : ∀ bytes, MemoryOps.store m.mem.memory ptr bytes align = .error e) :
    typedStoreM m ptr (.Int i) (.Int t) align atomicity = .error e := by
  obtain ⟨signed, size⟩ := t
  have hin : inBounds i signed size = true := hrep
  simp only [typedStoreM, checkValueM, ensureElseUb, hrep, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, Type.encodeM, Type.encodeIntM, Endianness.encode, hin, interp_pure_bind,
    ConcurrentMemory.store, hstore, interp_error_bind]
  rfl

/-! ### Arithmetic UB of `AtomicFetchAndOp`, and the missing `bring_in_bounds`

Upstream MiniRust `d821c6e3` (`spec/lang/step/intrinsics.md`):
> "let next_int = Self::eval_int_bin_op(op, previous_int, other_int, int_ty)?;
>  let next = Value::Int(next_int);
>  self.typed_store(ptr, next, ret_ty, align, Atomicity::Atomic)?;"
`eval_bin_op` for `BinOp::Int` brings the result of `eval_int_bin_op` in bounds
(`int_ty.bring_in_bounds(result)`) before it builds the `Value::Int`;
`AtomicFetchAndOp` does not. A result outside the integer type therefore
reaches the `assert!` of `Machine::typed_store`, a specification panic, where
Rust's `fetch_add` wraps. -/

/-- `AtomicFetchAndOp(Div)` by zero is UB. -/
theorem atomicFetchAndOp_div_zero_ub {m m1 : Machine M}
    {ptr : ThinPointer (Memory.Provenance M)} (pty : «Type») {p : Int} {t : IntType}
    {al : Align} (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hload : typedLoadM m ptr (.Int t) al .Atomic = .ok (.Int p, m1)) :
    evalIntrinsicM m (.AtomicFetchAndOp .Div)
        [(.Ptr ⟨ptr, none⟩, pty), (.Int 0, .Int t)] (.Int t) =
      .error (.ub "division by zero") :=
  atomicFetchAndOp_binop_error .Div pty hal hsz hload (evalIntBinOp_div_zero p t)

/-- `AtomicFetchAndOp(Rem)` by zero is UB. -/
theorem atomicFetchAndOp_rem_zero_ub {m m1 : Machine M}
    {ptr : ThinPointer (Memory.Provenance M)} (pty : «Type») {p : Int} {t : IntType}
    {al : Align} (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hload : typedLoadM m ptr (.Int t) al .Atomic = .ok (.Int p, m1)) :
    evalIntrinsicM m (.AtomicFetchAndOp .Rem)
        [(.Ptr ⟨ptr, none⟩, pty), (.Int 0, .Int t)] (.Int t) =
      .error (.ub "modulus of remainder is zero") :=
  atomicFetchAndOp_binop_error .Rem pty hal hsz hload (evalIntBinOp_rem_zero p t)

/-- `AtomicFetchAndOp(Div)` whose quotient leaves the integer type
(`INT_MIN / -1`) is UB. -/
theorem atomicFetchAndOp_div_overflow_ub {m m1 : Machine M}
    {ptr : ThinPointer (Memory.Provenance M)} (pty : «Type») {p o : Int} {t : IntType}
    {al : Align} (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hload : typedLoadM m ptr (.Int t) al .Atomic = .ok (.Int p, m1))
    (ho : o ≠ 0) (hov : IntType.can_represent t (Int.tdiv p o) = false) :
    evalIntrinsicM m (.AtomicFetchAndOp .Div)
        [(.Ptr ⟨ptr, none⟩, pty), (.Int o, .Int t)] (.Int t) =
      .error (.ub "overflow in division") :=
  atomicFetchAndOp_binop_error .Div pty hal hsz hload (evalIntBinOp_div_overflow ho hov)

/-- `AtomicFetchAndOp(ShlUnchecked)` by an out-of-range amount is UB. -/
theorem atomicFetchAndOp_shlUnchecked_oob_ub {m m1 : Machine M}
    {ptr : ThinPointer (Memory.Provenance M)} (pty : «Type») {p o : Int} {t : IntType}
    {al : Align} (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hload : typedLoadM m ptr (.Int t) al .Atomic = .ok (.Int p, m1))
    (ho : o < 0 ∨ o ≥ (Size.bits t.size : Int)) :
    evalIntrinsicM m (.AtomicFetchAndOp .ShlUnchecked)
        [(.Ptr ⟨ptr, none⟩, pty), (.Int o, .Int t)] (.Int t) =
      .error (.ub "overflow in unchecked shift") :=
  atomicFetchAndOp_binop_error .ShlUnchecked pty hal hsz hload (evalIntBinOp_shlUnchecked_oob p ho)

/-- `AtomicFetchAndOp(ShrUnchecked)` by an out-of-range amount is UB. -/
theorem atomicFetchAndOp_shrUnchecked_oob_ub {m m1 : Machine M}
    {ptr : ThinPointer (Memory.Provenance M)} (pty : «Type») {p o : Int} {t : IntType}
    {al : Align} (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hload : typedLoadM m ptr (.Int t) al .Atomic = .ok (.Int p, m1))
    (ho : o < 0 ∨ o ≥ (Size.bits t.size : Int)) :
    evalIntrinsicM m (.AtomicFetchAndOp .ShrUnchecked)
        [(.Ptr ⟨ptr, none⟩, pty), (.Int o, .Int t)] (.Int t) =
      .error (.ub "overflow in unchecked shift") :=
  atomicFetchAndOp_binop_error .ShrUnchecked pty hal hsz hload (evalIntBinOp_shrUnchecked_oob p ho)

/-- The missing `bring_in_bounds`: when `eval_int_bin_op` returns a result
that the integer type cannot represent, `AtomicFetchAndOp` is a specification
panic of `typed_store`, in every memory model. -/
theorem atomicFetchAndOp_out_of_range_specPanic {m m1 : Machine M} (binOp : IntBinOp)
    {ptr : ThinPointer (Memory.Provenance M)} (pty : «Type») {p o n : Int} {t : IntType}
    {al : Align} (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hload : typedLoadM m ptr (.Int t) al .Atomic = .ok (.Int p, m1))
    (hop : evalIntBinOp binOp p o t = .ok n) (hn : IntType.can_represent t n = false) :
    evalIntrinsicM m (.AtomicFetchAndOp binOp)
        [(.Ptr ⟨ptr, none⟩, pty), (.Int o, .Int t)] (.Int t) =
      .error (.specPanic "trying to store a value which is ill-formed for its type") :=
  atomicFetchAndOp_store_error binOp pty hal hsz hload hop
    (typedStoreM_int_out_of_range m1 ptr n t al .Atomic hn)

/-- `AtomicFetchAndOp(Add)` whose sum overflows the integer type is a
specification panic, not a wrapping addition. -/
theorem atomicFetchAndOp_add_overflow_specPanic {m m1 : Machine M}
    {ptr : ThinPointer (Memory.Provenance M)} (pty : «Type») {p o : Int} {t : IntType}
    {al : Align} (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hload : typedLoadM m ptr (.Int t) al .Atomic = .ok (.Int p, m1))
    (hov : IntType.can_represent t (p + o) = false) :
    evalIntrinsicM m (.AtomicFetchAndOp .Add)
        [(.Ptr ⟨ptr, none⟩, pty), (.Int o, .Int t)] (.Int t) =
      .error (.specPanic "trying to store a value which is ill-formed for its type") :=
  atomicFetchAndOp_out_of_range_specPanic .Add pty hal hsz hload rfl hov

/-- `AtomicFetchAndOp(Add)` in bounds: it stores `previous + other` and returns
`previous`. -/
theorem atomicFetchAndOp_add_ok {m m1 m2 : Machine M}
    {ptr : ThinPointer (Memory.Provenance M)} (pty : «Type») {p o : Int} {t : IntType}
    {al : Align} (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hload : typedLoadM m ptr (.Int t) al .Atomic = .ok (.Int p, m1))
    (hstore : typedStoreM m1 ptr (.Int (p + o)) (.Int t) al .Atomic = .ok m2) :
    evalIntrinsicM m (.AtomicFetchAndOp .Add)
        [(.Ptr ⟨ptr, none⟩, pty), (.Int o, .Int t)] (.Int t) =
      .ok (.Int p, m2) :=
  atomicFetchAndOp_ok .Add pty hal hsz hload rfl hstore

/-- `AtomicFetchAndOp(Rem)` whose quotient leaves the integer type
(`INT_MIN % -1`) is UB. -/
theorem atomicFetchAndOp_rem_overflow_ub {m m1 : Machine M}
    {ptr : ThinPointer (Memory.Provenance M)} (pty : «Type») {p o : Int} {t : IntType}
    {al : Align} (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hload : typedLoadM m ptr (.Int t) al .Atomic = .ok (.Int p, m1))
    (ho : o ≠ 0) (hov : IntType.can_represent t (Int.tdiv p o) = false) :
    evalIntrinsicM m (.AtomicFetchAndOp .Rem)
        [(.Ptr ⟨ptr, none⟩, pty), (.Int o, .Int t)] (.Int t) =
      .error (.ub "overflow in remainder") :=
  atomicFetchAndOp_binop_error .Rem pty hal hsz hload (evalIntBinOp_rem_overflow ho hov)

/-- `AtomicFetchAndOp(AddUnchecked)` whose sum overflows the integer type is
UB (in contrast to `AtomicFetchAndOp(Add)`, which is a spec panic in
`typed_store`). -/
theorem atomicFetchAndOp_addUnchecked_overflow_ub {m m1 : Machine M}
    {ptr : ThinPointer (Memory.Provenance M)} (pty : «Type») {p o : Int} {t : IntType}
    {al : Align} (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hload : typedLoadM m ptr (.Int t) al .Atomic = .ok (.Int p, m1))
    (hov : IntType.can_represent t (p + o) = false) :
    evalIntrinsicM m (.AtomicFetchAndOp .AddUnchecked)
        [(.Ptr ⟨ptr, none⟩, pty), (.Int o, .Int t)] (.Int t) =
      .error (.ub "overflow in unchecked add") :=
  atomicFetchAndOp_binop_error .AddUnchecked pty hal hsz hload
    (evalIntBinOp_addUnchecked_overflow hov)

/-- `AtomicFetchAndOp(SubUnchecked)` whose difference overflows the integer
type is UB. -/
theorem atomicFetchAndOp_subUnchecked_overflow_ub {m m1 : Machine M}
    {ptr : ThinPointer (Memory.Provenance M)} (pty : «Type») {p o : Int} {t : IntType}
    {al : Align} (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hload : typedLoadM m ptr (.Int t) al .Atomic = .ok (.Int p, m1))
    (hov : IntType.can_represent t (p - o) = false) :
    evalIntrinsicM m (.AtomicFetchAndOp .SubUnchecked)
        [(.Ptr ⟨ptr, none⟩, pty), (.Int o, .Int t)] (.Int t) =
      .error (.ub "overflow in unchecked sub") :=
  atomicFetchAndOp_binop_error .SubUnchecked pty hal hsz hload
    (evalIntBinOp_subUnchecked_overflow hov)

/-- `AtomicFetchAndOp(MulUnchecked)` whose product overflows the integer type
is UB. -/
theorem atomicFetchAndOp_mulUnchecked_overflow_ub {m m1 : Machine M}
    {ptr : ThinPointer (Memory.Provenance M)} (pty : «Type») {p o : Int} {t : IntType}
    {al : Align} (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hload : typedLoadM m ptr (.Int t) al .Atomic = .ok (.Int p, m1))
    (hov : IntType.can_represent t (p * o) = false) :
    evalIntrinsicM m (.AtomicFetchAndOp .MulUnchecked)
        [(.Ptr ⟨ptr, none⟩, pty), (.Int o, .Int t)] (.Int t) =
      .error (.ub "overflow in unchecked mul") :=
  atomicFetchAndOp_binop_error .MulUnchecked pty hal hsz hload
    (evalIntBinOp_mulUnchecked_overflow hov)

/-- `AtomicFetchAndOp(DivExact)` with a non-zero remainder is UB. -/
theorem atomicFetchAndOp_divExact_rem_nonzero_ub {m m1 : Machine M}
    {ptr : ThinPointer (Memory.Provenance M)} (pty : «Type») {p o : Int} {t : IntType}
    {al : Align} (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hload : typedLoadM m ptr (.Int t) al .Atomic = .ok (.Int p, m1))
    (ho : o ≠ 0) (hin : IntType.can_represent t (Int.tdiv p o) = true)
    (hrem : Int.tmod p o ≠ 0) :
    evalIntrinsicM m (.AtomicFetchAndOp .DivExact)
        [(.Ptr ⟨ptr, none⟩, pty), (.Int o, .Int t)] (.Int t) =
      .error (.ub "non-zero remainder in exact division") :=
  atomicFetchAndOp_binop_error .DivExact pty hal hsz hload
    (evalIntBinOp_divExact_rem_nonzero ho hin hrem)

/-- `AtomicStore` of an out-of-range integer is a specification panic of
`typed_store` (before any memory access or alignment check). -/
theorem atomicStore_int_out_of_range_specPanic (m : Machine M)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (n : Int) (t : IntType)
    {al : Align} (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hn : IntType.can_represent t n = false) :
    evalIntrinsicM m .AtomicStore [(.Ptr ⟨ptr, none⟩, pty), (.Int n, .Int t)] unitType =
      .error (.specPanic "trying to store a value which is ill-formed for its type") := by
  have ha : alignFromBytesInt (t.size.bytes : Int) = some al := by
    rw [alignFromBytesInt_natCast]; exact hal
  rw [atomicStore_eq_typedStoreM m ptr pty (.Int n) (.Int t) (layout_int hal) ha hsz,
    typedStoreM_int_out_of_range m ptr n t al .Atomic hn]
  rfl

/-- `AtomicCompareExchange` checks `next` only when it stores it: a succeeding
compare-exchange whose `next` the integer type cannot represent is a
specification panic of `typed_store`. A *failing* one with the same `next`
returns normally (`atomicCompareExchange_failure` holds for every `next`), so
whether an ill-formed `next` is noticed depends on the value in memory. -/
theorem atomicCompareExchange_next_out_of_range_specPanic {m m1 : Machine M}
    {ptr : ThinPointer (Memory.Provenance M)} (pty : «Type») {cur : Value M} {n : Int}
    {t : IntType} {al : Align}
    (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hload : typedLoadM m ptr (.Int t) al .Atomic = .ok (cur, m1))
    (hn : IntType.can_represent t n = false) :
    evalIntrinsicM m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (cur, .Int t), (.Int n, .Int t)] (.Int t) =
      .error (.specPanic "trying to store a value which is ill-formed for its type") :=
  atomicCompareExchange_store_error pty hal hsz hload
    (typedStoreM_int_out_of_range m1 ptr n t al .Atomic hn)

/-! ### Alignment: an atomic access must be aligned to its own size -/

/-- The memory model's `load` rejects a pointer that is not aligned as
requested. `BasicMemory` and `TreeBorrowsMemory` both do. -/
def LoadChecksAlign (M : Type) [Memory M] [MemoryOps M] : Prop :=
  ∀ (mem : M) (ptr : ThinPointer (Memory.Provenance M)) (len : Size) (align : Align),
    ptr.addr % (align.bytes : Int) ≠ 0 →
    MemoryOps.load mem ptr len align = .error (.ub "load from a misaligned pointer")

/-- The memory model's `store` rejects a pointer that is not aligned as
requested. `BasicMemory` and `TreeBorrowsMemory` both do. -/
def StoreChecksAlign (M : Type) [Memory M] [MemoryOps M] : Prop :=
  ∀ (mem : M) (ptr : ThinPointer (Memory.Provenance M))
    (bytes : List (AbstractByte (Memory.Provenance M))) (align : Align),
    ptr.addr % (align.bytes : Int) ≠ 0 →
    MemoryOps.store mem ptr bytes align = .error (.ub "store to a misaligned pointer")

/-- `Align::is_aligned` fails on an address that is not a multiple. -/
theorem is_aligned_eq_false {align : Align} {addr : Int}
    (h : addr % (align.bytes : Int) ≠ 0) : Align.is_aligned align addr = false := by
  unfold Align.is_aligned
  exact beq_false_of_ne h

/-- `Machine::typed_load` at an integer type through a pointer that is not
aligned to the type's size is UB. -/
theorem typedLoadM_int_misaligned_ub (hM : LoadChecksAlign M) (m : Machine M)
    (ptr : ThinPointer (Memory.Provenance M)) (t : IntType) {al : Align}
    (atomicity : Atomicity) (hal : alignFromBytes t.size.bytes = some al)
    (hmis : ptr.addr % (t.size.bytes : Int) ≠ 0) :
    typedLoadM m ptr (.Int t) al atomicity = .error (.ub "load from a misaligned pointer") := by
  have hl := layout_int hal
  obtain rfl := alignFromBytes_eq_some hal
  exact typedLoadM_load_error atomicity hl (hM _ _ _ _ hmis)

/-- `AtomicLoad` through a pointer that is not aligned to the size of the
loaded integer is UB. -/
theorem atomicLoad_misaligned_ub (hM : LoadChecksAlign M) (m : Machine M)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (t : IntType) {al : Align}
    (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hmis : ptr.addr % (t.size.bytes : Int) ≠ 0) :
    evalIntrinsicM m .AtomicLoad [(.Ptr ⟨ptr, none⟩, pty)] (.Int t) =
      .error (.ub "load from a misaligned pointer") := by
  have ha : alignFromBytesInt (t.size.bytes : Int) = some al := by
    rw [alignFromBytesInt_natCast]
    exact hal
  rw [atomicLoad_eq_typedLoadM m ptr pty (.Int t) (layout_int hal) ha hsz]
  exact typedLoadM_int_misaligned_ub hM m ptr t .Atomic hal hmis

/-- `AtomicCompareExchange` through a misaligned pointer is UB already at its
load. -/
theorem atomicCompareExchange_misaligned_ub (hM : LoadChecksAlign M) (m : Machine M)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (cur next : Value M)
    (t : IntType) {al : Align} (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hmis : ptr.addr % (t.size.bytes : Int) ≠ 0) :
    evalIntrinsicM m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (cur, .Int t), (next, .Int t)] (.Int t) =
      .error (.ub "load from a misaligned pointer") :=
  atomicCompareExchange_load_error pty cur next hal hsz
    (typedLoadM_int_misaligned_ub hM m ptr t .Atomic hal hmis)

/-- `AtomicFetchAndOp` through a misaligned pointer is UB already at its load. -/
theorem atomicFetchAndOp_misaligned_ub (hM : LoadChecksAlign M) (m : Machine M)
    (binOp : IntBinOp) (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type»)
    (other : Value M) (t : IntType) {al : Align}
    (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hmis : ptr.addr % (t.size.bytes : Int) ≠ 0) :
    evalIntrinsicM m (.AtomicFetchAndOp binOp)
        [(.Ptr ⟨ptr, none⟩, pty), (other, .Int t)] (.Int t) =
      .error (.ub "load from a misaligned pointer") :=
  atomicFetchAndOp_load_error binOp pty other hal hsz
    (typedLoadM_int_misaligned_ub hM m ptr t .Atomic hal hmis)

/-- `AtomicStore` of a representable integer through a pointer that is not
aligned to the integer's size is UB. -/
theorem atomicStore_misaligned_ub (hM : StoreChecksAlign M) (m : Machine M)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (i : Int) (t : IntType)
    {al : Align} (hal : alignFromBytes t.size.bytes = some al)
    (hsz : t.size.bytes ≤ x86_64.MAX_ATOMIC_SIZE.bytes)
    (hrep : IntType.can_represent t i = true)
    (hmis : ptr.addr % (t.size.bytes : Int) ≠ 0) :
    evalIntrinsicM m .AtomicStore [(.Ptr ⟨ptr, none⟩, pty), (.Int i, .Int t)] unitType =
      .error (.ub "store to a misaligned pointer") := by
  have ha : alignFromBytesInt (t.size.bytes : Int) = some al := by
    rw [alignFromBytesInt_natCast]
    exact hal
  rw [atomicStore_eq_typedStoreM m ptr pty (.Int i) (.Int t) (layout_int hal) ha hsz]
  obtain rfl := alignFromBytes_eq_some hal
  rw [typedStoreM_int_store_error .Atomic hrep (fun bytes => hM _ _ bytes _ hmis)]
  rfl

/-- `Terminator::Intrinsic` (`spec/lang/step/terminators.md`): after evaluating
`ret_place`, arguments, any returning intrinsic (including all four atomics),
and `place_store`, `next_block = some nb` jumps to `nb` while `next_block = none`
is UB `"return from an intrinsic where caller did not specify next block"`. -/
theorem evalTerminatorM_intrinsic_ok {m m1 m2 m3 m4 : Machine M}
    {op : IntrinsicOp} {argExprs : List ValueExpr} {retExpr : PlaceExpr}
    {nextBlock : Option BbName} {retPlace : Place M} {retTy : «Type»}
    {args : List (Value M × «Type»)} {val : Value M}
    (hplace : evalPlaceM m retExpr = .ok ((retPlace, retTy), m1))
    (hargs : evalArgsM m1 argExprs = .ok (args, m2))
    (hint : evalIntrinsicM m2 op args retTy = .ok (val, m3))
    (hstore : placeStoreM m3 retPlace val retTy = .ok m4) :
    evalTerminatorM m (.Intrinsic op argExprs retExpr nextBlock) =
      match nextBlock with
      | some nb => jumpToBlockM m4 nb
      | none => .error (.ub "return from an intrinsic where caller did not specify next block") := by
  cases nextBlock with
  | none => simp only [evalTerminatorM, hplace, hargs, hint, hstore, interp_ok_bind, ub]
  | some _ => simp only [evalTerminatorM, hplace, hargs, hint, hstore, interp_ok_bind]

/-- `Terminator::Intrinsic` evaluates the return place first (upstream: "First
evaluate return place (left-to-right evaluation)"). If `eval_place` stops, so
does the terminator: no argument is evaluated and no atomic access happens. -/
theorem evalTerminatorM_intrinsic_place_error {m : Machine M} {op : IntrinsicOp}
    {argExprs : List ValueExpr} {retExpr : PlaceExpr} {nextBlock : Option BbName} {e : Stop}
    (hplace : evalPlaceM m retExpr = .error e) :
    evalTerminatorM m (.Intrinsic op argExprs retExpr nextBlock) = .error e := by
  simp only [evalTerminatorM, hplace, interp_error_bind]

/-- Once the return place and the arguments evaluate, a `Stop` of the intrinsic
is the terminator's `Stop`: every UB law above is also UB of the terminator. -/
theorem evalTerminatorM_intrinsic_fn_error {m m1 m2 : Machine M} {op : IntrinsicOp}
    {argExprs : List ValueExpr} {retExpr : PlaceExpr} {nextBlock : Option BbName}
    {retPlace : Place M} {retTy : «Type»} {args : List (Value M × «Type»)} {e : Stop}
    (hplace : evalPlaceM m retExpr = .ok ((retPlace, retTy), m1))
    (hargs : evalArgsM m1 argExprs = .ok (args, m2))
    (hint : evalIntrinsicM m2 op args retTy = .error e) :
    evalTerminatorM m (.Intrinsic op argExprs retExpr nextBlock) = .error e := by
  simp only [evalTerminatorM, hplace, hargs, hint, interp_ok_bind, interp_error_bind]

/-- The returned value is stored only after the intrinsic ran. If `place_store`
stops, so does the terminator for every `next_block`: a faulting store preempts
the missing-`next_block` UB, and `m3` with the intrinsic's accesses is discarded. -/
theorem evalTerminatorM_intrinsic_store_error {m m1 m2 m3 : Machine M}
    {op : IntrinsicOp} {argExprs : List ValueExpr} {retExpr : PlaceExpr}
    {nextBlock : Option BbName} {retPlace : Place M} {retTy : «Type»}
    {args : List (Value M × «Type»)} {val : Value M} {e : Stop}
    (hplace : evalPlaceM m retExpr = .ok ((retPlace, retTy), m1))
    (hargs : evalArgsM m1 argExprs = .ok (args, m2))
    (hint : evalIntrinsicM m2 op args retTy = .ok (val, m3))
    (hstore : placeStoreM m3 retPlace val retTy = .error e) :
    evalTerminatorM m (.Intrinsic op argExprs retExpr nextBlock) = .error e := by
  simp only [evalTerminatorM, hplace, hargs, hint, hstore, interp_ok_bind, interp_error_bind]

/-- A misaligned return place (`aligned = false`, which `eval_place` computes
without failing) is UB only at `place_store`, after the intrinsic succeeded. -/
theorem evalTerminatorM_intrinsic_misaligned_ret_ub {m m1 m2 m3 : Machine M}
    {op : IntrinsicOp} {argExprs : List ValueExpr} {retExpr : PlaceExpr}
    {nextBlock : Option BbName} {retPlace : Place M} {retTy : «Type»}
    {args : List (Value M × «Type»)} {val : Value M}
    (hplace : evalPlaceM m retExpr = .ok ((retPlace, retTy), m1))
    (hargs : evalArgsM m1 argExprs = .ok (args, m2))
    (hint : evalIntrinsicM m2 op args retTy = .ok (val, m3))
    (hmis : retPlace.aligned = false) :
    evalTerminatorM m (.Intrinsic op argExprs retExpr nextBlock) =
      .error (.ub "storing to a place based on a misaligned pointer") := by
  refine evalTerminatorM_intrinsic_store_error hplace hargs hint ?_
  simp only [placeStoreM, hmis, Bool.not_false, ↓reduceIte, ub]

end Guards

/-- `BasicMemory::load` checks alignment first. -/
theorem bm_loadChecksAlign : LoadChecksAlign BM := by
  intro mem ptr len align h
  show BM.load mem ptr len align = _
  simp only [BM.load, is_aligned_eq_false h, Bool.not_false, ↓reduceIte]
  rfl

/-- `BasicMemory::store` checks alignment first. -/
theorem bm_storeChecksAlign : StoreChecksAlign BM := by
  intro mem ptr bytes align h
  show BM.store mem ptr bytes align = _
  simp only [BM.store, is_aligned_eq_false h, Bool.not_false, ↓reduceIte]
  rfl

/-- `TreeBorrowsMemory::load` checks alignment first (in `BasicMemory::load`,
before any borrow-tree access). -/
theorem tbm_loadChecksAlign : LoadChecksAlign TBM := by
  intro mem ptr len align h
  show TreeBorrowsMemory.load mem ptr len align = _
  simp only [TreeBorrowsMemory.load, BasicMemory.load, is_aligned_eq_false h, Bool.not_false,
    ↓reduceIte]
  rfl

/-- `TreeBorrowsMemory::store` checks alignment first (in `BasicMemory::store`,
before any borrow-tree access). -/
theorem tbm_storeChecksAlign : StoreChecksAlign TBM := by
  intro mem ptr bytes align h
  show TreeBorrowsMemory.store mem ptr bytes align = _
  simp only [TreeBorrowsMemory.store, BasicMemory.store, is_aligned_eq_false h, Bool.not_false,
    ↓reduceIte]
  rfl

/-- On `Mach`, every `u32` atomic intrinsic through a pointer whose address is
not a multiple of 4 is UB, whatever the machine and wherever the pointer
points (inside a live allocation or not). -/
theorem atomic_u32_misaligned_ub_bm (m : Mach) (ptr : Ptr) (pty : «Type») (i : Int)
    (cur next other : Val) (binOp : IntBinOp)
    (hi : IntType.can_represent itU32 i = true) (hmis : ptr.addr % 4 ≠ 0) :
    evalIntrinsicM m .AtomicStore [(.Ptr ⟨ptr, none⟩, pty), (.Int i, .Int itU32)] unitType =
      .error (.ub "store to a misaligned pointer") ∧
    evalIntrinsicM m .AtomicLoad [(.Ptr ⟨ptr, none⟩, pty)] (.Int itU32) =
      .error (.ub "load from a misaligned pointer") ∧
    evalIntrinsicM m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (cur, .Int itU32), (next, .Int itU32)] (.Int itU32) =
      .error (.ub "load from a misaligned pointer") ∧
    evalIntrinsicM m (.AtomicFetchAndOp binOp)
        [(.Ptr ⟨ptr, none⟩, pty), (other, .Int itU32)] (.Int itU32) =
      .error (.ub "load from a misaligned pointer") :=
  ⟨atomicStore_misaligned_ub bm_storeChecksAlign m ptr pty i itU32 (al := ⟨4⟩) rfl (by decide) hi
      hmis,
   atomicLoad_misaligned_ub bm_loadChecksAlign m ptr pty itU32 (al := ⟨4⟩) rfl (by decide) hmis,
   atomicCompareExchange_misaligned_ub bm_loadChecksAlign m ptr pty cur next itU32 (al := ⟨4⟩) rfl
      (by decide) hmis,
   atomicFetchAndOp_misaligned_ub bm_loadChecksAlign m binOp ptr pty other itU32 (al := ⟨4⟩) rfl
      (by decide) hmis⟩

/-- On `MachTB`, every `u32` atomic intrinsic through a pointer whose address
is not a multiple of 4 is UB, whatever the machine and the borrow tree. -/
theorem atomic_u32_misaligned_ub_tb (m : MachTB) (ptr : ThinPointer TreeBorrowsProvenance)
    (pty : «Type») (i : Int) (cur next other : Value TBM) (binOp : IntBinOp)
    (hi : IntType.can_represent itU32 i = true) (hmis : ptr.addr % 4 ≠ 0) :
    evalIntrinsicM m .AtomicStore [(.Ptr ⟨ptr, none⟩, pty), (.Int i, .Int itU32)] unitType =
      .error (.ub "store to a misaligned pointer") ∧
    evalIntrinsicM m .AtomicLoad [(.Ptr ⟨ptr, none⟩, pty)] (.Int itU32) =
      .error (.ub "load from a misaligned pointer") ∧
    evalIntrinsicM m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (cur, .Int itU32), (next, .Int itU32)] (.Int itU32) =
      .error (.ub "load from a misaligned pointer") ∧
    evalIntrinsicM m (.AtomicFetchAndOp binOp)
        [(.Ptr ⟨ptr, none⟩, pty), (other, .Int itU32)] (.Int itU32) =
      .error (.ub "load from a misaligned pointer") :=
  ⟨atomicStore_misaligned_ub tbm_storeChecksAlign m ptr pty i itU32 (al := ⟨4⟩) rfl (by decide) hi
      hmis,
   atomicLoad_misaligned_ub tbm_loadChecksAlign m ptr pty itU32 (al := ⟨4⟩) rfl (by decide) hmis,
   atomicCompareExchange_misaligned_ub tbm_loadChecksAlign m ptr pty cur next itU32 (al := ⟨4⟩)
      rfl (by decide) hmis,
   atomicFetchAndOp_misaligned_ub tbm_loadChecksAlign m binOp ptr pty other itU32 (al := ⟨4⟩) rfl
      (by decide) hmis⟩

/-! ### The size and type checks on concrete types, in every memory model -/

section ConcreteTypes

variable {M : Type} [Memory M] [MemoryOps M]

/-- Unsized `[u8]`: `AtomicStore` is UB, whereas `AtomicLoad` is a spec panic
(`expect_size`). -/
theorem atomic_slice_u8_unsized (m : Machine M) (ptr : ThinPointer (Memory.Provenance M))
    (pty : «Type») (v : Value M) (retTy : «Type») :
    evalIntrinsicM m .AtomicStore [(.Ptr ⟨ptr, none⟩, pty), (v, .Slice (.Int itU8))] retTy =
      .error (.ub "invalid second argument to `AtomicStore` intrinsic: unsized type") ∧
    evalIntrinsicM m .AtomicLoad [(.Ptr ⟨ptr, none⟩, pty)] (.Slice (.Int itU8)) =
      .error (.specPanic
        "expect_size called on unsized type: WF ensures intrinsic return types are sized") :=
  ⟨rfl, rfl⟩

/-- A 3-byte `[u8; 3]`: `AtomicStore` and `AtomicLoad` are UB, since 3 is not
a power of two. -/
theorem atomic_array3_size_not_pow2_ub (m : Machine M)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (v : Value M) (retTy : «Type») :
    evalIntrinsicM m .AtomicStore [(.Ptr ⟨ptr, none⟩, pty), (v, .Array (.Int itU8) 3)] retTy =
      .error (.ub
        "invalid second argument to `AtomicStore` intrinsic: size not power of two") ∧
    evalIntrinsicM m .AtomicLoad [(.Ptr ⟨ptr, none⟩, pty)] (.Array (.Int itU8) 3) =
      .error (.ub "invalid return type for `AtomicLoad` intrinsic: size not power of two") :=
  ⟨rfl, rfl⟩

/-- `u128` is 16 bytes, twice `x86_64::MAX_ATOMIC_SIZE`: all four intrinsics
are UB at it. -/
theorem atomic_u128_size_too_big_ub (m : Machine M) (ptr : ThinPointer (Memory.Provenance M))
    (pty : «Type») (v w : Value M) (retTy : «Type») (binOp : IntBinOp) :
    evalIntrinsicM m .AtomicStore [(.Ptr ⟨ptr, none⟩, pty), (v, .Int itU128)] retTy =
      .error (.ub "invalid second argument to `AtomicStore` intrinsic: size too big") ∧
    evalIntrinsicM m .AtomicLoad [(.Ptr ⟨ptr, none⟩, pty)] (.Int itU128) =
      .error (.ub "invalid return type for `AtomicLoad` intrinsic: size too big") ∧
    evalIntrinsicM m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (v, .Int itU128), (w, .Int itU128)] (.Int itU128) =
      .error (.ub "invalid return type for `AtomicCompareExchange` intrinsic: size too big") ∧
    evalIntrinsicM m (.AtomicFetchAndOp binOp)
        [(.Ptr ⟨ptr, none⟩, pty), (v, .Int itU128)] (.Int itU128) =
      .error (.ub "invalid return type for `AtomicFetchAndOp` intrinsic: size too big") := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> kernel_rfl

/-- Type mismatches and non-integer return types on concrete types. -/
theorem atomic_type_mismatch_ub (m : Machine M) (ptr : ThinPointer (Memory.Provenance M))
    (pty : «Type») (v w : Value M) (binOp : IntBinOp) :
    evalIntrinsicM m .AtomicStore [(.Ptr ⟨ptr, none⟩, pty), (v, .Int itU32)] (.Int itU32) =
      .error (.ub "invalid return type for `AtomicStore` intrinsic") ∧
    evalIntrinsicM m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (v, .Int itU8), (w, .Int itU32)] (.Int itU32) =
      .error (.ub "invalid second argument to `AtomicCompareExchange` intrinsic: not same type as return value") ∧
    evalIntrinsicM m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (v, .Int itU32), (w, .Int itU8)] (.Int itU32) =
      .error (.ub "invalid third argument to `AtomicCompareExchange` intrinsic: not same type as return value") ∧
    evalIntrinsicM m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (v, .Bool), (w, .Bool)] .Bool =
      .error (.ub "invalid return type for `Intrinis::AtomicCompareExchange`: only works with integers") ∧
    evalIntrinsicM m (.AtomicFetchAndOp binOp)
        [(.Ptr ⟨ptr, none⟩, pty), (v, .Int itU8)] (.Int itU32) =
      .error (.ub "invalid second argument to `AtomicFetchAndOp` intrinsic: not same type as return value") ∧
    evalIntrinsicM m (.AtomicFetchAndOp binOp)
        [(.Ptr ⟨ptr, none⟩, pty), (v, .Bool)] .Bool =
      .error (.ub "invalid return type for `AtomicFetchAndOp` intrinsic: only works with integers") := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> kernel_rfl

/-- Zero-sized `()` has size 0, which is not a power of two: `AtomicStore`
and `AtomicLoad` are UB at `()`. A wide raw pointer (`*const [u8]`) has size
16, twice `x86_64::MAX_ATOMIC_SIZE`: `AtomicStore` and `AtomicLoad` are UB
with `size too big`. -/
theorem atomic_zst_and_wide_ptr_ub (m : Machine M)
    (ptr : ThinPointer (Memory.Provenance M)) (pty : «Type») (v : Value M) (retTy : «Type») :
    evalIntrinsicM m .AtomicStore [(.Ptr ⟨ptr, none⟩, pty), (v, unitType)] retTy =
      .error (.ub
        "invalid second argument to `AtomicStore` intrinsic: size not power of two") ∧
    evalIntrinsicM m .AtomicLoad [(.Ptr ⟨ptr, none⟩, pty)] unitType =
      .error (.ub "invalid return type for `AtomicLoad` intrinsic: size not power of two") ∧
    evalIntrinsicM m .AtomicStore
        [(.Ptr ⟨ptr, none⟩, pty), (v, .Ptr (.Raw .ElementCount))] retTy =
      .error (.ub "invalid second argument to `AtomicStore` intrinsic: size too big") ∧
    evalIntrinsicM m .AtomicLoad [(.Ptr ⟨ptr, none⟩, pty)] (.Ptr (.Raw .ElementCount)) =
      .error (.ub "invalid return type for `AtomicLoad` intrinsic: size too big") := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> kernel_rfl

end ConcreteTypes

/-! ### Data-race interaction in `ConcurrentMemory`

Upstream MiniRust (`spec/mem/concurrent.md`):
> "fn races(self, other: Self) -> bool {
>      // At least one access modifies the data.
>      if self.ty == AccessType::Load && other.ty == AccessType::Load { return false; }
>
>      // At least one access is non atomic
>      if self.atomicity == Atomicity::Atomic && other.atomicity == Atomicity::Atomic { return false; }
>
>      // The accesses overlap.
>      let end_addr = self.addr + self.len.bytes();
>      let other_end_addr = other.addr + other.len.bytes();
>      end_addr > other.addr && other_end_addr > self.addr
>  }"
The laws below connect the atomic access logs of §2 directly to `Access::races`
and `ConcurrentMemory::check_data_races` (and `CM.check_data_races` on `BM`):
* Any two atomic accesses never race (`access_races_atomic_atomic_false`), so
  any two atomic intrinsics on unsynchronized threads never trigger a data race
  (`atomic_atomic_no_data_race`).
* An atomic store and a non-atomic load (or vice versa) on unsynchronized
  threads at overlapping addresses *do* trigger UB `"Data race"`
  (`atomicStore_nonAtomicLoad_data_race`,
  `atomicFetchAndOp_nonAtomicLoad_data_race`).
* Upstream's `AtomicCompareExchange` note: a *failing* compare-exchange logs
  only an atomic `Load`, so it never races with a non-atomic load on an
  unsynchronized thread (`atomicCompareExchange_failure_nonAtomicLoad_no_data_race`),
  whereas a *succeeding* compare-exchange logs an atomic `Store` and therefore
  *does* race with a non-atomic load at an overlapping address
  (`atomicCompareExchange_success_nonAtomicLoad_data_race`).
* The exemption of a failing compare-exchange is only against *loads*. An
  atomic read, be it an `AtomicLoad` or a compare-exchange that fails, races
  with a non-atomic *store* at an overlapping address
  (`atomicLoad_nonAtomicStore_data_race`,
  `atomicCompareExchange_nonAtomicStore_data_race`).
* The atomic store of `AtomicStore` races with a non-atomic load at every type
  it accepts, not only at integer types
  (`atomicStore_any_type_nonAtomicLoad_data_race`).
* `ConcurrentMemory::check_data_races` either returns or throws UB
  `"Data race"`; it has no other outcome (`check_data_races_error_iff`). -/

/-- Exact characterization of `Access::races`. -/
theorem access_races_iff (a b : Access) :
    Access.races a b = true ↔
      ¬(a.ty = .Load ∧ b.ty = .Load) ∧
      ¬(a.atomicity = .Atomic ∧ b.atomicity = .Atomic) ∧
      a.addr + a.len.bytes > b.addr ∧
      b.addr + b.len.bytes > a.addr := by
  unfold Access.races
  split
  · rename_i hll
    exact ⟨fun h => Bool.noConfusion h, fun ⟨hn, _⟩ => absurd hll hn⟩
  · rename_i hll
    split
    · rename_i haa
      exact ⟨fun h => Bool.noConfusion h, fun ⟨_, hn, _⟩ => absurd haa hn⟩
    · rename_i haa
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      exact ⟨fun ⟨h1, h2⟩ => ⟨hll, haa, h1, h2⟩, fun ⟨_, _, h1, h2⟩ => ⟨h1, h2⟩⟩

/-- `Access::races` is symmetric. -/
theorem access_races_symm (a b : Access) : Access.races a b = Access.races b a := by
  cases hab : Access.races a b with
  | true =>
    have ⟨hll, haa, h1, h2⟩ := (access_races_iff a b).mp hab
    exact ((access_races_iff b a).mpr
      ⟨fun ⟨hb, ha⟩ => hll ⟨ha, hb⟩, fun ⟨hb, ha⟩ => haa ⟨ha, hb⟩, h2, h1⟩).symm
  | false =>
    cases hba : Access.races b a with
    | false => rfl
    | true =>
      have ⟨hll, haa, h1, h2⟩ := (access_races_iff b a).mp hba
      have h := (access_races_iff a b).mpr
        ⟨fun ⟨ha, hb⟩ => hll ⟨hb, ha⟩, fun ⟨ha, hb⟩ => haa ⟨hb, ha⟩, h2, h1⟩
      rw [hab] at h
      cases h

/-- Two atomic accesses never race with each other, regardless of whether they
are loads or stores and regardless of address overlap. -/
theorem access_races_atomic_atomic_false {a b : Access}
    (ha : a.atomicity = .Atomic) (hb : b.atomicity = .Atomic) :
    Access.races a b = false := by
  cases h : Access.races a b with
  | false => rfl
  | true => exact (((access_races_iff a b).mp h).2.1 ⟨ha, hb⟩).elim

/-- Two loads never race with each other, regardless of atomicity. -/
theorem access_races_load_load_false {a b : Access}
    (ha : a.ty = .Load) (hb : b.ty = .Load) :
    Access.races a b = false := by
  cases h : Access.races a b with
  | false => rfl
  | true => exact (((access_races_iff a b).mp h).1 ⟨ha, hb⟩).elim

/-- An atomic store and a non-atomic load at overlapping byte ranges race. -/
theorem access_races_atomic_store_non_atomic_load (addr1 addr2 : Address) (len1 len2 : Size)
    (h1 : addr1 + len1.bytes > addr2) (h2 : addr2 + len2.bytes > addr1) :
    Access.races ⟨.Store, .Atomic, addr1, len1⟩ ⟨.Load, .None, addr2, len2⟩ = true :=
  (access_races_iff _ _).mpr ⟨(fun ⟨h, _⟩ => by cases h), (fun ⟨_, h⟩ => by cases h), h1, h2⟩

/-- A non-atomic store and an atomic load at overlapping byte ranges race. -/
theorem access_races_non_atomic_store_atomic_load (addr1 addr2 : Address) (len1 len2 : Size)
    (h1 : addr1 + len1.bytes > addr2) (h2 : addr2 + len2.bytes > addr1) :
    Access.races ⟨.Store, .None, addr1, len1⟩ ⟨.Load, .Atomic, addr2, len2⟩ = true :=
  (access_races_iff _ _).mpr ⟨(fun ⟨h, _⟩ => by cases h), (fun ⟨h, _⟩ => by cases h), h1, h2⟩

/-- `ConcurrentMemory.check_data_races` at `M = BasicMemory<x86_64>` is
`CM.check_data_races`. -/
theorem check_data_races_bm_eq (cm : ConcurrentMemory BM) (tid : ThreadId)
    (prev : Set ThreadId × List Access) :
    ConcurrentMemory.check_data_races cm tid prev = CM.check_data_races cm tid prev := rfl

section DataRaces

variable {M : Type} [Memory M] [MemoryOps M]

omit [MemoryOps M] in
/-- Complete characterization of when `ConcurrentMemory::check_data_races`
reports UB `"Data race"`. -/
theorem check_data_races_ub_iff (cm : ConcurrentMemory M) (tid : ThreadId)
    (sync : Set ThreadId) (prev : List Access) :
    ConcurrentMemory.check_data_races cm tid (sync, prev) = .error (.ub "Data race") ↔
      setContains sync tid = false ∧
      ∃ a ∈ cm.accesses, ∃ p ∈ prev, Access.races a p = true := by
  unfold ConcurrentMemory.check_data_races
  dsimp only
  split
  · rename_i hsync
    constructor
    · intro h; cases h
    · rintro ⟨hf, _⟩
      rw [hf] at hsync
      cases hsync
  · rename_i hsync
    have hfalse : setContains sync tid = false := by
      cases hb : setContains sync tid with
      | false => rfl
      | true => exact absurd hb hsync
    split
    · rename_i hany
      obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp hany
      obtain ⟨p, hp_mem, hr⟩ := List.any_eq_true.mp hp
      exact ⟨fun _ => ⟨hfalse, a, ha, p, hp_mem, hr⟩, fun _ => rfl⟩
    · rename_i hany
      have hanyF : cm.accesses.any (fun a => prev.any (fun p => Access.races a p)) = false := by
        cases hb : cm.accesses.any (fun a => prev.any (fun p => Access.races a p)) with
        | false => rfl
        | true => exact absurd hb hany
      constructor
      · intro h; cases h
      · rintro ⟨_, a, ha, p, hp_mem, hr⟩
        have h1 := list_any_eq_false_iff.mp hanyF a ha
        have h2 := list_any_eq_false_iff.mp h1 p hp_mem
        rw [h2] at hr
        cases hr

omit [MemoryOps M] in
/-- Complete characterization of when `ConcurrentMemory::check_data_races`
succeeds. -/
theorem check_data_races_ok_iff (cm : ConcurrentMemory M) (tid : ThreadId)
    (sync : Set ThreadId) (prev : List Access) :
    ConcurrentMemory.check_data_races cm tid (sync, prev) = .ok () ↔
      setContains sync tid = true ∨
      ∀ a ∈ cm.accesses, ∀ p ∈ prev, Access.races a p = false := by
  unfold ConcurrentMemory.check_data_races
  dsimp only
  split
  · rename_i hsync
    exact ⟨fun _ => Or.inl hsync, fun _ => rfl⟩
  · rename_i hsync
    split
    · rename_i hany
      constructor
      · intro h; dsimp only [ub] at h; cases h
      · rintro (ht | hall)
        · exact absurd ht hsync
        · obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp hany
          obtain ⟨p, hp_mem, hr⟩ := List.any_eq_true.mp hp
          rw [hall a ha p hp_mem] at hr
          cases hr
    · rename_i hany
      have hanyF : cm.accesses.any (fun a => prev.any (fun p => Access.races a p)) = false := by
        cases hb : cm.accesses.any (fun a => prev.any (fun p => Access.races a p)) with
        | false => rfl
        | true => exact absurd hb hany
      constructor
      · intro _
        exact Or.inr fun a ha p hp =>
          list_any_eq_false_iff.mp (list_any_eq_false_iff.mp hanyF a ha) p hp
      · intro _; rfl

omit [MemoryOps M] in
/-- `ConcurrentMemory::check_data_races` has exactly two outcomes: it returns,
or it throws UB `"Data race"`. It never panics and never stops in any other
way. -/
theorem check_data_races_ok_or_ub (cm : ConcurrentMemory M) (tid : ThreadId)
    (sync : Set ThreadId) (prev : List Access) :
    ConcurrentMemory.check_data_races cm tid (sync, prev) = .ok () ∨
    ConcurrentMemory.check_data_races cm tid (sync, prev) = .error (.ub "Data race") := by
  by_cases hs : setContains sync tid = true
  · exact Or.inl ((check_data_races_ok_iff cm tid sync prev).mpr (Or.inl hs))
  · by_cases hr : ∃ a ∈ cm.accesses, ∃ p ∈ prev, Access.races a p = true
    · refine Or.inr ((check_data_races_ub_iff cm tid sync prev).mpr ⟨?_, hr⟩)
      cases hb : setContains sync tid with
      | false => rfl
      | true => exact absurd hb hs
    · refine Or.inl ((check_data_races_ok_iff cm tid sync prev).mpr
        (Or.inr fun a ha p hp => ?_))
      cases hb : Access.races a p with
      | false => rfl
      | true => exact (hr ⟨a, ha, p, hp, hb⟩).elim

omit [MemoryOps M] in
/-- Complete characterization of every stopping outcome of
`ConcurrentMemory::check_data_races`, for an arbitrary `Stop`: the only one is
UB `"Data race"`, and it occurs exactly when the current thread is not
synchronized with the previous step and one of its accesses races with one of
the previous step's. (`check_data_races_ub_iff` fixes the `Stop` in advance and
so does not exclude other ways of stopping.) -/
theorem check_data_races_error_iff (cm : ConcurrentMemory M) (tid : ThreadId)
    (sync : Set ThreadId) (prev : List Access) (e : Stop) :
    ConcurrentMemory.check_data_races cm tid (sync, prev) = .error e ↔
      e = .ub "Data race" ∧ setContains sync tid = false ∧
      ∃ a ∈ cm.accesses, ∃ p ∈ prev, Access.races a p = true := by
  constructor
  · intro h
    rcases check_data_races_ok_or_ub cm tid sync prev with hok | hub
    · rw [hok] at h
      cases h
    · have he : e = .ub "Data race" := by
        rw [hub] at h
        cases h
        rfl
      exact ⟨he, (check_data_races_ub_iff cm tid sync prev).mp hub⟩
  · rintro ⟨rfl, hrest⟩
    exact (check_data_races_ub_iff cm tid sync prev).mpr hrest

omit [MemoryOps M] in
/-- Two steps whose access logs contain a racing pair of accesses are a data
race in both interleaving orders, for every thread that is not synchronized
with the other step. -/
theorem check_data_races_ub_of_mem {cm1 cm2 : ConcurrentMemory M} {a1 a2 : Access}
    (h1 : a1 ∈ cm1.accesses) (h2 : a2 ∈ cm2.accesses) (hr : Access.races a1 a2 = true)
    {tid : ThreadId} {sync : Set ThreadId} (hunsync : setContains sync tid = false) :
    ConcurrentMemory.check_data_races cm2 tid (sync, cm1.accesses) =
      .error (.ub "Data race") ∧
    ConcurrentMemory.check_data_races cm1 tid (sync, cm2.accesses) =
      .error (.ub "Data race") := by
  refine ⟨(check_data_races_ub_iff cm2 tid sync cm1.accesses).mpr
            ⟨hunsync, a2, h2, a1, h1, ?_⟩,
          (check_data_races_ub_iff cm1 tid sync cm2.accesses).mpr
            ⟨hunsync, a1, h1, a2, h2, hr⟩⟩
  rw [access_races_symm]
  exact hr

/-- Any two successful atomic intrinsics on two steps (each starting from a
fresh access log, as after `reset_data_race_tracking`) never data-race in
`ConcurrentMemory::check_data_races`, even on unsynchronized threads accessing
the same address. -/
theorem atomic_atomic_no_data_race {m0 m1 m2 m3 : Machine M} {op1 op2 : IntrinsicOp}
    {args1 args2 : List (Value M × «Type»)} {retTy1 retTy2 : «Type»} {v1 v2 : Value M}
    (hop1 : isAtomicOp op1 = true) (hop2 : isAtomicOp op2 = true)
    (hemp0 : m0.mem.accesses = []) (hemp2 : m2.mem.accesses = [])
    (h1 : evalIntrinsicM m0 op1 args1 retTy1 = .ok (v1, m1))
    (h2 : evalIntrinsicM m2 op2 args2 retTy2 = .ok (v2, m3))
    (tid : ThreadId) (sync : Set ThreadId) :
    ConcurrentMemory.check_data_races m3.mem tid (sync, m1.mem.accesses) = .ok () := by
  obtain ⟨_, log1, hacc1, _, _, hall1⟩ := evalIntrinsicM_atomic_accesses hop1 h1
  obtain ⟨_, log2, hacc2, _, _, hall2⟩ := evalIntrinsicM_atomic_accesses hop2 h2
  rw [hemp0, List.nil_append] at hacc1
  rw [hemp2, List.nil_append] at hacc2
  refine (check_data_races_ok_iff m3.mem tid sync m1.mem.accesses).mpr (Or.inr fun a ha p hp => ?_)
  rw [hacc2] at ha
  rw [hacc1] at hp
  exact access_races_atomic_atomic_false (hall2 a ha).1 (hall1 p hp).1

/-- An `AtomicStore` of an integer and a non-atomic `typed_load` on
unsynchronized threads at overlapping byte ranges trigger UB `"Data race"` in
`ConcurrentMemory::check_data_races` (in both interleaving orders). -/
theorem atomicStore_nonAtomicLoad_data_race {m0 m1 m2 m3 : Machine M}
    {ptr1 ptr2 : ThinPointer (Memory.Provenance M)} {pty : «Type»} {v1 v2 : Value M}
    {t1 : IntType} {ty2 : «Type»} {size2 : Size} {a2 al2 : Align}
    (h1 : evalIntrinsicM m0 .AtomicStore [(.Ptr ⟨ptr1, none⟩, pty), (v1, .Int t1)] unitType =
      .ok (unitValueM, m1))
    (h2 : typedLoadM m2 ptr2 ty2 al2 .None = .ok (v2, m3))
    (hl2 : Type.layout ty2 = .ok (.Sized size2 a2))
    (hov1 : ptr1.addr + t1.size.bytes > ptr2.addr)
    (hov2 : ptr2.addr + size2.bytes > ptr1.addr)
    {tid : ThreadId} {sync : Set ThreadId} (hunsync : setContains sync tid = false) :
    ConcurrentMemory.check_data_races m3.mem tid (sync, m1.mem.accesses) =
      .error (.ub "Data race") ∧
    ConcurrentMemory.check_data_races m1.mem tid (sync, m3.mem.accesses) =
      .error (.ub "Data race") := by
  obtain ⟨ptr, _, v, ty, _, _, align, hargs, _, _, _, _, _, hs⟩ := atomicStore_ok_iff.mp h1
  have h1a := (List.cons.inj hargs).1
  have h1b := (List.cons.inj (List.cons.inj hargs).2).1
  have hptr : ptr1 = ptr := (Pointer.mk.inj (Value.Ptr.inj (Prod.mk.inj h1a).1)).1
  have hv : v1 = v := (Prod.mk.inj h1b).1
  have hty : .Int t1 = ty := (Prod.mk.inj h1b).2
  rw [← hptr, ← hv, ← hty] at hs
  obtain ⟨bytes, henc, hacc1⟩ := typedStoreM_ok_accesses hs
  have hlen : bytes.length = t1.size.bytes := encodeM_int_length henc
  obtain ⟨sz2, _, hl2', hacc2⟩ := typedLoadM_ok_accesses h2
  have hsz2 : sz2 = size2 := by
    rw [hl2] at hl2'
    cases hl2'
    rfl
  rw [hsz2] at hacc2
  have hmem1 : ⟨.Store, .Atomic, ptr1.addr, t1.size⟩ ∈ m1.mem.accesses := by
    rw [hacc1, hlen]
    exact List.mem_append_right _ (List.Mem.head _)
  have hmem2 : ⟨.Load, .None, ptr2.addr, size2⟩ ∈ m3.mem.accesses := by
    rw [hacc2]
    exact List.mem_append_right _ (List.Mem.head _)
  have hrace : Access.races ⟨.Store, .Atomic, ptr1.addr, t1.size⟩
      ⟨.Load, .None, ptr2.addr, size2⟩ = true :=
    access_races_atomic_store_non_atomic_load ptr1.addr ptr2.addr t1.size size2 hov1 hov2
  refine ⟨(check_data_races_ub_iff _ _ _ _).mpr ⟨hunsync, _, hmem2, _, hmem1, ?_⟩,
          (check_data_races_ub_iff _ _ _ _).mpr ⟨hunsync, _, hmem1, _, hmem2, hrace⟩⟩
  rw [access_races_symm]
  exact hrace

/-- Upstream (`spec/lang/step/intrinsics.md`): "We do *not* do a store on a
failing AtomicCompareExchange. This means that races between a non-atomic load
and a failing AtomicCompareExchange are not considered UB!"
In every memory model, a failing `AtomicCompareExchange` and a non-atomic
`typed_load` on unsynchronized threads (each starting from an empty access log)
never trigger a data race in `ConcurrentMemory::check_data_races`, in either
order, even at the exact same address. The size facts about `t1` are not
hypotheses: `atomicCompareExchange_ok_size` derives them from `hcas`. -/
theorem atomicCompareExchange_failure_nonAtomicLoad_no_data_race
    {m0 m1 m2 m3 : Machine M} {ptr1 ptr2 : ThinPointer (Memory.Provenance M)}
    {pty : «Type»} {cur next before v2 : Value M} {t1 : IntType} {ty2 : «Type»}
    {al2 : Align}
    (hemp0 : m0.mem.accesses = []) (hemp2 : m2.mem.accesses = [])
    (hcas : evalIntrinsicM m0 .AtomicCompareExchange
        [(.Ptr ⟨ptr1, none⟩, pty), (cur, .Int t1), (next, .Int t1)] (.Int t1) =
      .ok (before, m1))
    (hne : cur ≠ before)
    (hload : typedLoadM m2 ptr2 ty2 al2 .None = .ok (v2, m3))
    (tid : ThreadId) (sync : Set ThreadId) :
    ConcurrentMemory.check_data_races m3.mem tid (sync, m1.mem.accesses) = .ok () ∧
    ConcurrentMemory.check_data_races m1.mem tid (sync, m3.mem.accesses) = .ok () := by
  have hacc1 := atomicCompareExchange_failure_accesses hcas hne
  obtain ⟨sz2, _, _, hacc2⟩ := typedLoadM_ok_accesses hload
  rw [hemp0, List.nil_append] at hacc1
  rw [hemp2, List.nil_append] at hacc2
  constructor
  · refine (check_data_races_ok_iff _ _ _ _).mpr (Or.inr fun a ha p hp => ?_)
    rw [hacc2] at ha; rw [hacc1] at hp
    cases ha with
    | head =>
      cases hp with
      | head => exact access_races_load_load_false rfl rfl
      | tail _ hp => cases hp
    | tail _ ha => cases ha
  · refine (check_data_races_ok_iff _ _ _ _).mpr (Or.inr fun a ha p hp => ?_)
    rw [hacc1] at ha; rw [hacc2] at hp
    cases ha with
    | head =>
      cases hp with
      | head => exact access_races_load_load_false rfl rfl
      | tail _ hp => cases hp
    | tail _ ha => cases ha

/-- In contrast to `atomicCompareExchange_failure_nonAtomicLoad_no_data_race`, a
*succeeding* `AtomicCompareExchange` performs an atomic store and therefore
triggers UB `"Data race"` against a non-atomic `typed_load` on an unsynchronized
thread at an overlapping byte range (in both interleaving orders). The size
facts about `t1` are not hypotheses: `atomicCompareExchange_ok_size` derives
them from `hcas`. -/
theorem atomicCompareExchange_success_nonAtomicLoad_data_race
    {m0 m1 m2 m3 : Machine M} {ptr1 ptr2 : ThinPointer (Memory.Provenance M)}
    {pty : «Type»} {cur next v2 : Value M} {t1 : IntType} {ty2 : «Type»}
    {size2 : Size} {a2 al2 : Align}
    (hcas : evalIntrinsicM m0 .AtomicCompareExchange
        [(.Ptr ⟨ptr1, none⟩, pty), (cur, .Int t1), (next, .Int t1)] (.Int t1) =
      .ok (cur, m1))
    (hload : typedLoadM m2 ptr2 ty2 al2 .None = .ok (v2, m3))
    (hl2 : Type.layout ty2 = .ok (.Sized size2 a2))
    (hov1 : ptr1.addr + t1.size.bytes > ptr2.addr)
    (hov2 : ptr2.addr + size2.bytes > ptr1.addr)
    {tid : ThreadId} {sync : Set ThreadId} (hunsync : setContains sync tid = false) :
    ConcurrentMemory.check_data_races m3.mem tid (sync, m1.mem.accesses) =
      .error (.ub "Data race") ∧
    ConcurrentMemory.check_data_races m1.mem tid (sync, m3.mem.accesses) =
      .error (.ub "Data race") := by
  obtain ⟨bytes, henc, hacc1⟩ := atomicCompareExchange_success_accesses hcas
  have hlen : bytes.length = t1.size.bytes := encodeM_int_length henc
  obtain ⟨sz2, _, hl2', hacc2⟩ := typedLoadM_ok_accesses hload
  have hsz2 : sz2 = size2 := by
    rw [hl2] at hl2'
    cases hl2'
    rfl
  rw [hsz2] at hacc2
  have hmem1 : ⟨.Store, .Atomic, ptr1.addr, t1.size⟩ ∈ m1.mem.accesses := by
    rw [hacc1, hlen]
    exact List.mem_append_right _ (List.Mem.tail _ (List.Mem.head _))
  have hmem2 : ⟨.Load, .None, ptr2.addr, size2⟩ ∈ m3.mem.accesses := by
    rw [hacc2]
    exact List.mem_append_right _ (List.Mem.head _)
  have hrace : Access.races ⟨.Store, .Atomic, ptr1.addr, t1.size⟩
      ⟨.Load, .None, ptr2.addr, size2⟩ = true :=
    access_races_atomic_store_non_atomic_load ptr1.addr ptr2.addr t1.size size2 hov1 hov2
  refine ⟨(check_data_races_ub_iff _ _ _ _).mpr ⟨hunsync, _, hmem2, _, hmem1, ?_⟩,
          (check_data_races_ub_iff _ _ _ _).mpr ⟨hunsync, _, hmem1, _, hmem2, hrace⟩⟩
  rw [access_races_symm]
  exact hrace

/-- A successful `AtomicFetchAndOp` performs an atomic store and therefore
triggers UB `"Data race"` against a non-atomic `typed_load` on an unsynchronized
thread at an overlapping byte range (in both interleaving orders). -/
theorem atomicFetchAndOp_nonAtomicLoad_data_race
    {m0 m1 m2 m3 : Machine M} {binOp : IntBinOp}
    {ptr1 ptr2 : ThinPointer (Memory.Provenance M)} {pty : «Type»}
    {other res v2 : Value M} {t1 : IntType} {ty2 : «Type»}
    {size2 : Size} {a2 al2 : Align}
    (hrmw : evalIntrinsicM m0 (.AtomicFetchAndOp binOp)
        [(.Ptr ⟨ptr1, none⟩, pty), (other, .Int t1)] (.Int t1) = .ok (res, m1))
    (hload : typedLoadM m2 ptr2 ty2 al2 .None = .ok (v2, m3))
    (hl2 : Type.layout ty2 = .ok (.Sized size2 a2))
    (hov1 : ptr1.addr + t1.size.bytes > ptr2.addr)
    (hov2 : ptr2.addr + size2.bytes > ptr1.addr)
    {tid : ThreadId} {sync : Set ThreadId} (hunsync : setContains sync tid = false) :
    ConcurrentMemory.check_data_races m3.mem tid (sync, m1.mem.accesses) =
      .error (.ub "Data race") ∧
    ConcurrentMemory.check_data_races m1.mem tid (sync, m3.mem.accesses) =
      .error (.ub "Data race") := by
  obtain ⟨ptr, _, _, _, _, t, _, _, hargs, hret, _, _, _, _, _, hstore⟩ :=
    atomicFetchAndOp_ok_iff.mp hrmw
  have h1a := (List.cons.inj hargs).1
  have hptr : ptr1 = ptr := (Pointer.mk.inj (Value.Ptr.inj (Prod.mk.inj h1a).1)).1
  have ht : t1 = t := by cases hret; rfl
  rw [← hptr, ← ht] at hstore
  obtain ⟨bytes, henc, hacc1⟩ := typedStoreM_ok_accesses hstore
  have hlen : bytes.length = t1.size.bytes := encodeM_int_length henc
  obtain ⟨sz2, _, hl2', hacc2⟩ := typedLoadM_ok_accesses hload
  have hsz2 : sz2 = size2 := by
    rw [hl2] at hl2'
    cases hl2'
    rfl
  rw [hsz2] at hacc2
  have hmem1 : ⟨.Store, .Atomic, ptr1.addr, t1.size⟩ ∈ m1.mem.accesses := by
    rw [hacc1, hlen]
    exact List.mem_append_right _ (List.Mem.head _)
  have hmem2 : ⟨.Load, .None, ptr2.addr, size2⟩ ∈ m3.mem.accesses := by
    rw [hacc2]
    exact List.mem_append_right _ (List.Mem.head _)
  have hrace : Access.races ⟨.Store, .Atomic, ptr1.addr, t1.size⟩
      ⟨.Load, .None, ptr2.addr, size2⟩ = true :=
    access_races_atomic_store_non_atomic_load ptr1.addr ptr2.addr t1.size size2 hov1 hov2
  refine ⟨(check_data_races_ub_iff _ _ _ _).mpr ⟨hunsync, _, hmem2, _, hmem1, ?_⟩,
          (check_data_races_ub_iff _ _ _ _).mpr ⟨hunsync, _, hmem1, _, hmem2, hrace⟩⟩
  rw [access_races_symm]
  exact hrace

/-- `atomicStore_nonAtomicLoad_data_race` without its restriction to integer
types, to the return type `()`, and to the returned value: a successful
`AtomicStore` at *any* type (`bool`, a thin pointer, an integer, ...) logs an
atomic `Store` over the bytes of the encoding of the stored value, and that
store and a non-atomic `typed_load` on unsynchronized threads at overlapping
byte ranges are UB `"Data race"`, in both interleaving orders. -/
theorem atomicStore_any_type_nonAtomicLoad_data_race {m0 m1 m2 m3 : Machine M}
    {ptr1 ptr2 : ThinPointer (Memory.Provenance M)} {pty retTy : «Type»}
    {v1 v2 val : Value M} {ty1 ty2 : «Type»} {size2 : Size} {a2 al2 : Align}
    (h1 : evalIntrinsicM m0 .AtomicStore [(.Ptr ⟨ptr1, none⟩, pty), (v1, ty1)] retTy =
      .ok (val, m1))
    (h2 : typedLoadM m2 ptr2 ty2 al2 .None = .ok (v2, m3))
    (hl2 : Type.layout ty2 = .ok (.Sized size2 a2)) :
    ∃ bytes, Type.encodeM (M := M) ty1 v1 = .ok bytes ∧
      ∀ (tid : ThreadId) (sync : Set ThreadId),
        ptr1.addr + bytes.length > ptr2.addr → ptr2.addr + size2.bytes > ptr1.addr →
        setContains sync tid = false →
        ConcurrentMemory.check_data_races m3.mem tid (sync, m1.mem.accesses) =
          .error (.ub "Data race") ∧
        ConcurrentMemory.check_data_races m1.mem tid (sync, m3.mem.accesses) =
          .error (.ub "Data race") := by
  obtain ⟨ptr, _, v, ty, _, _, align, hargs, _, _, _, _, _, hs⟩ := atomicStore_ok_iff.mp h1
  have h1a := (List.cons.inj hargs).1
  have h1b := (List.cons.inj (List.cons.inj hargs).2).1
  have hptr : ptr1 = ptr := (Pointer.mk.inj (Value.Ptr.inj (Prod.mk.inj h1a).1)).1
  have hv : v1 = v := (Prod.mk.inj h1b).1
  have hty : ty1 = ty := (Prod.mk.inj h1b).2
  rw [← hptr, ← hv, ← hty] at hs
  obtain ⟨bytes, henc, hacc1⟩ := typedStoreM_ok_accesses hs
  obtain ⟨sz2, _, hl2', hacc2⟩ := typedLoadM_ok_accesses h2
  have hsz2 : sz2 = size2 := by
    rw [hl2] at hl2'
    cases hl2'
    rfl
  rw [hsz2] at hacc2
  refine ⟨bytes, henc, fun tid sync hov1 hov2 hunsync => ?_⟩
  have hmem1 : (⟨.Store, .Atomic, ptr1.addr, ⟨bytes.length⟩⟩ : Access) ∈ m1.mem.accesses := by
    rw [hacc1]
    exact List.mem_append_right _ (List.Mem.head _)
  have hmem2 : (⟨.Load, .None, ptr2.addr, size2⟩ : Access) ∈ m3.mem.accesses := by
    rw [hacc2]
    exact List.mem_append_right _ (List.Mem.head _)
  exact check_data_races_ub_of_mem hmem1 hmem2
    (access_races_atomic_store_non_atomic_load ptr1.addr ptr2.addr ⟨bytes.length⟩ size2
      hov1 hov2)
    hunsync

/-- An atomic *read* is not exempt from data races: a successful `AtomicLoad`
logs an atomic `Load`, and that load and a non-atomic `typed_store` on
unsynchronized threads at overlapping byte ranges are UB `"Data race"`, in both
interleaving orders. Only atomic-atomic and load-load pairs are exempt. -/
theorem atomicLoad_nonAtomicStore_data_race {m0 m1 m2 m3 : Machine M}
    {ptr1 ptr2 : ThinPointer (Memory.Provenance M)} {pty retTy ty2 : «Type»}
    {val v2 : Value M} {size1 : Size} {a1 al2 : Align}
    (h1 : evalIntrinsicM m0 .AtomicLoad [(.Ptr ⟨ptr1, none⟩, pty)] retTy = .ok (val, m1))
    (hl1 : Type.layout retTy = .ok (.Sized size1 a1))
    (h2 : typedStoreM m2 ptr2 v2 ty2 al2 .None = .ok m3) :
    ∃ bytes, Type.encodeM (M := M) ty2 v2 = .ok bytes ∧
      ∀ (tid : ThreadId) (sync : Set ThreadId),
        ptr2.addr + bytes.length > ptr1.addr → ptr1.addr + size1.bytes > ptr2.addr →
        setContains sync tid = false →
        ConcurrentMemory.check_data_races m3.mem tid (sync, m1.mem.accesses) =
          .error (.ub "Data race") ∧
        ConcurrentMemory.check_data_races m1.mem tid (sync, m3.mem.accesses) =
          .error (.ub "Data race") := by
  obtain ⟨ptr, _, _, _, _, hargs, _, _, _, hl⟩ := atomicLoad_ok_iff.mp h1
  have hptr : ptr1 = ptr :=
    (Pointer.mk.inj (Value.Ptr.inj (Prod.mk.inj (List.cons.inj hargs).1).1)).1
  rw [← hptr] at hl
  obtain ⟨sz1, _, hl1', hacc1⟩ := typedLoadM_ok_accesses hl
  have hsz1 : sz1 = size1 := by
    rw [hl1] at hl1'
    cases hl1'
    rfl
  rw [hsz1] at hacc1
  obtain ⟨bytes, henc, hacc2⟩ := typedStoreM_ok_accesses h2
  refine ⟨bytes, henc, fun tid sync hov1 hov2 hunsync => ?_⟩
  have hmem1 : (⟨.Load, .Atomic, ptr1.addr, size1⟩ : Access) ∈ m1.mem.accesses := by
    rw [hacc1]
    exact List.mem_append_right _ (List.Mem.head _)
  have hmem2 : (⟨.Store, .None, ptr2.addr, ⟨bytes.length⟩⟩ : Access) ∈ m3.mem.accesses := by
    rw [hacc2]
    exact List.mem_append_right _ (List.Mem.head _)
  exact And.symm (check_data_races_ub_of_mem hmem2 hmem1
    (access_races_non_atomic_store_atomic_load ptr2.addr ptr1.addr ⟨bytes.length⟩ size1
      hov1 hov2)
    hunsync)

/-- A failing `AtomicCompareExchange` is a read, not a no-op: it is exempt from
races with non-atomic *loads*
(`atomicCompareExchange_failure_nonAtomicLoad_no_data_race`), but every
`AtomicCompareExchange` that returns, failing or succeeding, logs an atomic
`Load` of `t1.size` bytes, and that load and a non-atomic `typed_store` on
unsynchronized threads at overlapping byte ranges are UB `"Data race"`, in both
interleaving orders. -/
theorem atomicCompareExchange_nonAtomicStore_data_race {m0 m1 m2 m3 : Machine M}
    {ptr1 ptr2 : ThinPointer (Memory.Provenance M)} {pty ty2 : «Type»}
    {cur next before v2 : Value M} {t1 : IntType} {al2 : Align}
    (hcas : evalIntrinsicM m0 .AtomicCompareExchange
        [(.Ptr ⟨ptr1, none⟩, pty), (cur, .Int t1), (next, .Int t1)] (.Int t1) =
      .ok (before, m1))
    (h2 : typedStoreM m2 ptr2 v2 ty2 al2 .None = .ok m3) :
    ∃ bytes, Type.encodeM (M := M) ty2 v2 = .ok bytes ∧
      ∀ (tid : ThreadId) (sync : Set ThreadId),
        ptr2.addr + bytes.length > ptr1.addr → ptr1.addr + t1.size.bytes > ptr2.addr →
        setContains sync tid = false →
        ConcurrentMemory.check_data_races m3.mem tid (sync, m1.mem.accesses) =
          .error (.ub "Data race") ∧
        ConcurrentMemory.check_data_races m1.mem tid (sync, m3.mem.accesses) =
          .error (.ub "Data race") := by
  obtain ⟨bytes, henc, hacc2⟩ := typedStoreM_ok_accesses h2
  refine ⟨bytes, henc, fun tid sync hov1 hov2 hunsync => ?_⟩
  have hmem1 : (⟨.Load, .Atomic, ptr1.addr, t1.size⟩ : Access) ∈ m1.mem.accesses := by
    rcases atomicCompareExchange_accesses hcas with ⟨_, hacc⟩ | ⟨_, hacc⟩
    · rw [hacc]
      exact List.mem_append_right _ (List.Mem.head _)
    · rw [hacc]
      exact List.mem_append_right _ (List.Mem.head _)
  have hmem2 : (⟨.Store, .None, ptr2.addr, ⟨bytes.length⟩⟩ : Access) ∈ m3.mem.accesses := by
    rw [hacc2]
    exact List.mem_append_right _ (List.Mem.head _)
  exact And.symm (check_data_races_ub_of_mem hmem2 hmem1
    (access_races_non_atomic_store_atomic_load ptr2.addr ptr1.addr ⟨bytes.length⟩ t1.size
      hov1 hov2)
    hunsync)

end DataRaces

/-! ### Provenance under integer atomics

`Type::decode` at `Type::Int` reads the data of each byte and ignores its
provenance, and `Type::encode` at `Type::Int` produces bytes without provenance
(`encodeM_int_no_provenance`). When memory holds the bytes of a pointer and an
integer atomic of pointer size is applied to them:
* `AtomicLoad` and a *failing* `AtomicCompareExchange` only load. In every
  memory model they change memory exactly as `M::load` does
  (`typedLoadM_ok_memory`), and on `Mach`, where `BasicMemory::load` returns
  the memory it was given (`bm_load_memory_eq`), memory is unchanged
  (`atomicLoad_memory_bm`, `atomicCompareExchange_failure_memory_bm`): every
  byte keeps its provenance.
* A *succeeding* `AtomicCompareExchange` and `AtomicFetchAndOp` store bytes
  without provenance (`atomicCompareExchange_success_stores_no_provenance`,
  `atomicFetchAndOp_stores_no_provenance`), even when the integer stored is the
  one that was there.

`atomic_int_provenance_bm` and `atomic_int_provenance_tb` in §4 evaluate all
four cases on concrete machines. -/

/-- `BasicMemory::load` returns the memory it was given: the allocation it
writes back is the allocation it read. -/
theorem bm_load_memory_eq {mem mem' : BM} {ptr : Ptr} {len : Size} {align : Align}
    {bytes : List Byte} (h : BM.load mem ptr len align = .ok (bytes, mem')) : mem' = mem := by
  unfold BM.load at h
  split at h
  · cases h
  · obtain ⟨r, _, h⟩ := interp_bind_eq_ok h
    cases r with
    | none =>
      cases h
      rfl
    | some t =>
      obtain ⟨_, _, _⟩ := t
      dsimp only at h
      obtain ⟨_, hidx, h⟩ := interp_bind_eq_ok h
      obtain ⟨allocs', hs, h⟩ := interp_bind_eq_ok h
      obtain ⟨_, _, h⟩ := interp_bind_eq_ok h
      obtain ⟨_, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok h)
      have hset : allocs' = mem.allocations :=
        (listSet_eq_ok hs).trans
          (MiniRustSpec.Correspondence.set_self_of_getElem? _ _ _ (listIndex_eq_ok hidx))
      subst hset
      rfl

/-- On `Mach`, a successful `typed_load` leaves memory unchanged; only the
access log grows (`typedLoadM_ok_accesses`). -/
theorem typedLoadM_bm_memory_eq {m m' : Mach} {ptr : Ptr} {ty : «Type»} {align : Align}
    {atomicity : Atomicity} {val : Val}
    (h : typedLoadM (M := BM) m ptr ty align atomicity = .ok (val, m')) :
    m'.mem.memory = m.mem.memory := by
  obtain ⟨_, _, _, _, hload, _⟩ := typedLoadM_ok_memory h
  exact bm_load_memory_eq hload

/-- On `Mach`, a successful `AtomicLoad` at any type leaves memory unchanged. In
particular, loading the bytes of a pointer at an integer type returns the bare
address and leaves the provenance of every byte in memory. -/
theorem atomicLoad_memory_bm {m m' : Mach} {args : List (Val × «Type»)} {retTy : «Type»}
    {val : Val} (h : evalIntrinsicM (M := BM) m .AtomicLoad args retTy = .ok (val, m')) :
    m'.mem.memory = m.mem.memory := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hload⟩ := atomicLoad_ok_iff.mp h
  exact typedLoadM_bm_memory_eq hload

/-- On `Mach`, a failing `AtomicCompareExchange` leaves memory unchanged, byte
for byte. In particular, a failing compare-exchange at `usize` on the bytes of
a pointer preserves the provenance of every byte, whereas a succeeding one
erases it (`atomicCompareExchange_success_stores_no_provenance`). -/
theorem atomicCompareExchange_failure_memory_bm {m m' : Mach} {ptr : Ptr} {pty : «Type»}
    {cur next before : Val} {t : IntType}
    (h : evalIntrinsicM (M := BM) m .AtomicCompareExchange
        [(.Ptr ⟨ptr, none⟩, pty), (cur, .Int t), (next, .Int t)] (.Int t) = .ok (before, m'))
    (hne : cur ≠ before) : m'.mem.memory = m.mem.memory := by
  obtain ⟨_, hal, hsz⟩ := atomicCompareExchange_ok_size h
  rw [atomicCompareExchange_eq m ptr pty cur next t hal hsz] at h
  obtain ⟨⟨b, m1⟩, hload, h⟩ := interp_bind_eq_ok h
  dsimp only at h
  cases hv : valueEqM cur b with
  | true =>
    simp only [hv, ↓reduceIte] at h
    obtain ⟨m2, _, h⟩ := interp_bind_eq_ok h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok h)
    exact absurd ((valueEqM_eq_true_iff cur b).mp hv) hne
  | false =>
    simp only [hv, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (interp_pure_eq_ok h)
    exact typedLoadM_bm_memory_eq hload

/-! ## §4. Concrete machines: operational laws, round trips, and mode sensitivity

Every statement of this section is a closed computation that the kernel
evaluates (`decide +kernel`, or `Eq.refl` through `kernel_rfl`). The machines
are written out as literals; `bmCell_allocated`, `tbCell_allocated`, and
`tbShared_reachable` show that the memory models' own operations produce
them. `Mach` witnesses run `evalIntrinsic`, the `BasicMemory` transcription;
`MachTB` witnesses run the polymorphic `evalIntrinsicM`. -/

/-- The `Stop` of an interpretation, if it stopped. -/
def stopOf {α : Type} : Interp α → Option Stop
  | .error s => some s
  | .ok _ => none

/-- A program without functions. No intrinsic reads the program. -/
def emptyProg : Program :=
  { functions := ⟨[]⟩, start := ⟨⟨0⟩⟩, globals := ⟨[]⟩, traits := ⟨[]⟩, vtables := ⟨[]⟩ }

/-- The address `BasicMemory::allocate` picks for the first allocation, `2^32`
(see `bmCell_allocated`); the `k`-th allocation of a machine lands at
`k * cellAddr`. -/
def cellAddr : Int := 4294967296

/-- Initialized bytes without provenance. -/
def initBytes {P : Type} (bs : List UInt8) : List (AbstractByte P) :=
  bs.map (fun b => .Init b none)

/-- Uninitialized bytes. -/
def uninitBytes {P : Type} (n : Nat) : List (AbstractByte P) :=
  List.replicate n .Uninit

/-- The encoding of a pointer: its address bytes, each carrying the pointer's
provenance and the byte's position in the pointer. -/
def provBytes {P : Type} (prov : P) : Int → List UInt8 → List (AbstractByte P)
  | _, [] => []
  | i, b :: bs => .Init b (some ⟨prov, i⟩) :: provBytes prov (i + 1) bs

/-- The little-endian bytes of a `u32` below 256. -/
def u32Bytes {P : Type} (b : UInt8) : List (AbstractByte P) := initBytes [b, 0, 0, 0]

/-- An atomic load of `len` bytes at `addr`. -/
def aLoad (len : Nat) (addr : Int := cellAddr) : Access := ⟨.Load, .Atomic, addr, ⟨len⟩⟩

/-- An atomic store of `len` bytes at `addr`. -/
def aStore (len : Nat) (addr : Int := cellAddr) : Access := ⟨.Store, .Atomic, addr, ⟨len⟩⟩

/-- The non-atomic store with which `Terminator::Intrinsic` writes the
returned value to the return place. -/
def retStore (len : Nat) (addr : Int) : Access := ⟨.Store, .None, addr, ⟨len⟩⟩

/-! ### `Machine<BasicMemory<x86_64>>` (`Mach`) -/

/-- A `Mach` without threads whose memory is `allocs`. -/
def bmMach (allocs : List (Allocation Unit Unit)) (accesses : List Access := []) : Mach :=
  { prog := emptyProg
    mem := { memory := { allocations := allocs, _phantom := ⟨⟩ }, accesses := accesses }
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

/-- A heap allocation at `cellAddr`, 8-aligned, holding `data`. -/
def bmCell (data : List Byte) (live : Bool := true) : Allocation Unit Unit :=
  { data := data, addr := cellAddr, align := ⟨8⟩, kind := .Heap, live := live, extra := () }

/-- The `Mach` whose only allocation is 8 bytes starting with `bytes`. -/
def bmWith (bytes : List Byte) : Mach := bmMach [bmCell (bytes ++ uninitBytes (8 - bytes.length))]

/-- A pointer into allocation 0, `off` bytes in. -/
def bmPtr (off : Int := 0) : Ptr := ⟨cellAddr + off, some (⟨0⟩, ())⟩

/-- A thin pointer argument. -/
def bmArg (ptr : Ptr) : Val × «Type» := (.Ptr ⟨ptr, none⟩, tyRawPtr)

/-- `AtomicStore(ptr, v)` at `ty` on `Mach`. -/
def bmStore (m : Mach) (ptr : Ptr) (v : Val) (ty : «Type») : Interp (Val × Mach) :=
  evalIntrinsic m .AtomicStore [bmArg ptr, (v, ty)] unitType

/-- `AtomicLoad(ptr)` at `ty` on `Mach`. -/
def bmLoad (m : Mach) (ptr : Ptr) (ty : «Type») : Interp (Val × Mach) :=
  evalIntrinsic m .AtomicLoad [bmArg ptr] ty

/-- `AtomicCompareExchange(ptr, cur, next)` at the integer type `t` on `Mach`. -/
def bmCas (m : Mach) (ptr : Ptr) (cur next : Int) (t : IntType) : Interp (Val × Mach) :=
  evalIntrinsic m .AtomicCompareExchange
    [bmArg ptr, (.Int cur, .Int t), (.Int next, .Int t)] (.Int t)

/-- `AtomicFetchAndOp(op)(ptr, o)` at the integer type `t` on `Mach`. -/
def bmRmw (m : Mach) (ptr : Ptr) (op : IntBinOp) (o : Int) (t : IntType) : Interp (Val × Mach) :=
  evalIntrinsic m (.AtomicFetchAndOp op) [bmArg ptr, (.Int o, .Int t)] (.Int t)

/-- `AtomicStore` of `v : ty` into a fresh cell, then `AtomicLoad` at `loadTy`. -/
def bmStoreLoad (v : Val) (ty loadTy : «Type») : Interp (Val × Mach) := do
  let (_, m) ← bmStore (bmWith []) bmPtr v ty
  bmLoad m bmPtr loadTy

/-- What an intrinsic on `Mach` returned and left behind: the value, the data
of every allocation, and the access log. -/
structure BmObs where
  /-- The returned value. -/
  val : Val
  /-- The data of every allocation, in allocation order. -/
  data : List (List Byte)
  /-- The access log of the resulting machine. -/
  log : List Access
  deriving DecidableEq

/-- Observe a successful intrinsic on `Mach`. -/
def bmObs (r : Interp (Val × Mach)) : Option BmObs :=
  match r with
  | .ok (v, m) => some ⟨v, m.mem.memory.allocations.map (fun a => a.data), m.mem.accesses⟩
  | .error _ => none

/-- What a store-then-load round trip of a value with encoding `bytes` must
show on `Mach`: the value comes back, the 8-byte cell starts with `bytes`, and
the log holds one atomic store and one atomic load of `bytes.length` bytes. -/
def bmRoundTrip (v : Val) (bytes : List Byte) : Option BmObs :=
  some ⟨v, [bytes ++ uninitBytes (8 - bytes.length)], [aStore bytes.length, aLoad bytes.length]⟩

/-- `BasicMemory::allocate` of 8 bytes produces exactly the literal cell and
pointer that the `Mach` witnesses use. -/
theorem bmCell_allocated :
    BM.allocate BasicMemory.new .Heap ⟨8⟩ ⟨8⟩ = .ok (bmPtr, (bmWith []).mem.memory) := by
  kernel_rfl

/-- Store-then-load round trips on `Mach` across `u8`, `u16`, `u32`, `u64`,
`i32`, `i64`, `usize`, and `bool`: the stored value comes back, memory holds
its little-endian encoding, and both accesses are atomic at the value's size. -/
theorem atomic_store_load_roundtrip_bm :
    bmObs (bmStoreLoad (.Int 200) (.Int itU8) (.Int itU8)) =
      bmRoundTrip (.Int 200) (initBytes [200]) ∧
    bmObs (bmStoreLoad (.Int 48879) (.Int itU16) (.Int itU16)) =
      bmRoundTrip (.Int 48879) (initBytes [0xEF, 0xBE]) ∧
    bmObs (bmStoreLoad (.Int 3735928559) (.Int itU32) (.Int itU32)) =
      bmRoundTrip (.Int 3735928559) (initBytes [0xEF, 0xBE, 0xAD, 0xDE]) ∧
    bmObs (bmStoreLoad (.Int 81985529216486895) (.Int itU64) (.Int itU64)) =
      bmRoundTrip (.Int 81985529216486895)
        (initBytes [0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01]) ∧
    bmObs (bmStoreLoad (.Int (-2)) (.Int itI32) (.Int itI32)) =
      bmRoundTrip (.Int (-2)) (initBytes [0xFE, 0xFF, 0xFF, 0xFF]) ∧
    bmObs (bmStoreLoad (.Int (-2)) (.Int itI64) (.Int itI64)) =
      bmRoundTrip (.Int (-2)) (initBytes [0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]) ∧
    bmObs (bmStoreLoad (.Int 18446744073709551615) (.Int IntType.usize_ty)
        (.Int IntType.usize_ty)) =
      bmRoundTrip (.Int 18446744073709551615)
        (initBytes [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]) ∧
    bmObs (bmStoreLoad (.Bool true) .Bool .Bool) = bmRoundTrip (.Bool true) (initBytes [1]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- A thin raw pointer (`*const u32`) into the cell, carrying the provenance
of allocation 0. -/
def bmPtrVal : Val := .Ptr ⟨bmPtr 4, none⟩

/-- Atomics preserve provenance exactly when they are used at a pointer type:
a stored thin raw pointer comes back with its provenance, every stored byte
carrying a provenance fragment; loading those bytes as a `u64` gives the bare
address; and loading the bytes of a stored `u64` as a pointer gives a pointer
*without* provenance. -/
theorem atomic_store_load_ptr_roundtrip_bm :
    bmObs (bmStoreLoad bmPtrVal tyRawPtr tyRawPtr) =
      bmRoundTrip bmPtrVal (provBytes (⟨0⟩, ()) 0 [4, 0, 0, 0, 1, 0, 0, 0]) ∧
    (bmObs (bmStoreLoad bmPtrVal tyRawPtr (.Int itU64))).map (fun o => o.val) =
      some (.Int 4294967300) ∧
    (bmObs (bmStoreLoad (.Int 4294967300) (.Int itU64) tyRawPtr)).map (fun o => o.val) =
      some (.Ptr ⟨⟨4294967300, none⟩, none⟩) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- The `Mach` whose cell holds `5u32`. -/
def bmFive : Mach := bmWith (u32Bytes 5)

/-- `AtomicCompareExchange` on `Mach`. Success (`current == before`): memory
becomes `next`, `before` is returned, and the log holds an atomic load and an
atomic store. Failure (`current != before`): memory is unchanged, `before` is
returned, and the log holds *only* the atomic load. -/
theorem atomicCompareExchange_bm :
    bmObs (bmCas bmFive bmPtr 5 9 itU32) =
      some ⟨.Int 5, [u32Bytes 9 ++ uninitBytes 4], [aLoad 4, aStore 4]⟩ ∧
    bmObs (bmCas bmFive bmPtr 6 9 itU32) =
      some ⟨.Int 5, [u32Bytes 5 ++ uninitBytes 4], [aLoad 4]⟩ := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- What `AtomicFetchAndOp` on `bmFive` must show when it stores `n`: it
returns the previous `5` and logs an atomic load and an atomic store. -/
def bmFetched (n : UInt8) : Option BmObs :=
  some ⟨.Int 5, [u32Bytes n ++ uninitBytes 4], [aLoad 4, aStore 4]⟩

/-- In-bounds `AtomicFetchAndOp` on `Mach` for `Add`, `Sub`, `Mul`, `BitAnd`,
`BitOr`, and `BitXor`: each returns `previous` and stores the updated value. -/
theorem atomicFetchAndOp_in_bounds_bm :
    bmObs (bmRmw bmFive bmPtr .Add 3 itU32) = bmFetched 8 ∧
    bmObs (bmRmw bmFive bmPtr .Sub 2 itU32) = bmFetched 3 ∧
    bmObs (bmRmw bmFive bmPtr .Mul 7 itU32) = bmFetched 35 ∧
    bmObs (bmRmw bmFive bmPtr .BitAnd 4 itU32) = bmFetched 4 ∧
    bmObs (bmRmw bmFive bmPtr .BitOr 2 itU32) = bmFetched 7 ∧
    bmObs (bmRmw bmFive bmPtr .BitXor 1 itU32) = bmFetched 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The `Mach` whose cell holds `i32::MIN`. -/
def bmI32Min : Mach := bmWith (initBytes [0, 0, 0, 0x80])

/-- Arithmetic UB of `AtomicFetchAndOp` on `Mach`: division and remainder by
zero, `i32::MIN / -1` and `i32::MIN % -1`, and unchecked shifts by the bit
width or by a negative amount. -/
theorem atomicFetchAndOp_arith_ub_bm :
    bmRmw bmFive bmPtr .Div 0 itU32 = .error (.ub "division by zero") ∧
    bmRmw bmFive bmPtr .Rem 0 itU32 = .error (.ub "modulus of remainder is zero") ∧
    bmRmw bmI32Min bmPtr .Div (-1) itI32 = .error (.ub "overflow in division") ∧
    bmRmw bmI32Min bmPtr .Rem (-1) itI32 = .error (.ub "overflow in remainder") ∧
    bmRmw bmFive bmPtr .ShlUnchecked 32 itU32 = .error (.ub "overflow in unchecked shift") ∧
    bmRmw bmFive bmPtr .ShrUnchecked (-1) itU32 =
      .error (.ub "overflow in unchecked shift") := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> kernel_rfl

/-- The `Mach` whose cell holds `255u8`. -/
def bmU8Max : Mach := bmWith (initBytes [255])

/-- The missing `bring_in_bounds` on `Mach`: `fetch_add(1)` on `255u8` is a
specification panic of `typed_store` (`eval_int_bin_op` returns `256`), whereas
`BinOp::Int(Add)` on the same operands wraps to `0`, and `fetch_add(0)` works. -/
theorem atomicFetchAndOp_add_u8_overflow_bm :
    bmRmw bmU8Max bmPtr .Add 1 itU8 =
      .error (.specPanic "trying to store a value which is ill-formed for its type") ∧
    evalBinOp (.Int .Add) (.Int 255, .Int itU8) (.Int 1, .Int itU8) =
      .ok (.Int 0, .Int itU8) ∧
    bmObs (bmRmw bmU8Max bmPtr .Add 0 itU8) =
      some ⟨.Int 255, [initBytes [255] ++ uninitBytes 7], [aLoad 1, aStore 1]⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · kernel_rfl
  · kernel_rfl
  · decide +kernel

/-- `AddUnchecked` on `255u8 + 1` is UB (`overflow in unchecked add`), whereas
`Add` on the same operands is a spec panic (missing `bring_in_bounds`);
`SubUnchecked` on `0u8 - 1` and `DivExact` on `5u32 / 2` are UB; and `Shl`
wraps the shift count modulo 8 (`1u8 << 8 = 1u8`) while overflowing `128u8 << 1`
is a spec panic. -/
theorem atomicFetchAndOp_unchecked_and_shift_bm :
    bmRmw bmU8Max bmPtr .AddUnchecked 1 itU8 =
      .error (.ub "overflow in unchecked add") ∧
    bmRmw (bmWith (initBytes [0])) bmPtr .SubUnchecked 1 itU8 =
      .error (.ub "overflow in unchecked sub") ∧
    bmRmw bmFive bmPtr .DivExact 2 itU32 =
      .error (.ub "non-zero remainder in exact division") ∧
    bmObs (bmRmw (bmWith (initBytes [1])) bmPtr .Shl 8 itU8) =
      some ⟨.Int 1, [initBytes [1] ++ uninitBytes 7], [aLoad 1, aStore 1]⟩ ∧
    bmRmw (bmWith (initBytes [128])) bmPtr .Shl 1 itU8 =
      .error (.specPanic "trying to store a value which is ill-formed for its type") := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · kernel_rfl
  · kernel_rfl
  · kernel_rfl
  · decide +kernel
  · kernel_rfl

/-- Alignment UB on `Mach` inside a live allocation: a `u32` atomic at
`cellAddr + 1`, and a `u64` atomic at `cellAddr + 4` (aligned for `u32`, not
for `u64`). -/
theorem atomic_misaligned_ub_bm :
    bmStore bmFive (bmPtr 1) (.Int 9) (.Int itU32) =
      .error (.ub "store to a misaligned pointer") ∧
    bmLoad bmFive (bmPtr 1) (.Int itU32) = .error (.ub "load from a misaligned pointer") ∧
    bmCas bmFive (bmPtr 1) 5 9 itU32 = .error (.ub "load from a misaligned pointer") ∧
    bmRmw bmFive (bmPtr 1) .Add 1 itU32 = .error (.ub "load from a misaligned pointer") ∧
    bmLoad bmFive (bmPtr 4) (.Int itU64) = .error (.ub "load from a misaligned pointer") := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> kernel_rfl

/-- Out-of-bounds UB on `Mach`: a `u32` atomic one past the end of the cell. -/
theorem atomic_out_of_bounds_ub_bm :
    bmStore bmFive (bmPtr 8) (.Int 9) (.Int itU32) =
      .error (.ub "dereferencing pointer outside the bounds of its allocation") ∧
    bmLoad bmFive (bmPtr 8) (.Int itU32) =
      .error (.ub "dereferencing pointer outside the bounds of its allocation") ∧
    bmCas bmFive (bmPtr 8) 5 9 itU32 =
      .error (.ub "dereferencing pointer outside the bounds of its allocation") ∧
    bmRmw bmFive (bmPtr 8) .Add 1 itU32 =
      .error (.ub "dereferencing pointer outside the bounds of its allocation") := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> kernel_rfl

/-- The `Mach` whose cell held `5u32` and has been deallocated. -/
def bmDead : Mach := bmMach [bmCell (u32Bytes 5 ++ uninitBytes 4) false]

/-- Dangling-pointer UB on `Mach`: every atomic through a pointer to a dead
allocation. -/
theorem atomic_dead_allocation_ub_bm :
    bmStore bmDead bmPtr (.Int 9) (.Int itU32) =
      .error (.ub "dereferencing pointer to dead allocation") ∧
    bmLoad bmDead bmPtr (.Int itU32) = .error (.ub "dereferencing pointer to dead allocation") ∧
    bmCas bmDead bmPtr 5 9 itU32 = .error (.ub "dereferencing pointer to dead allocation") ∧
    bmRmw bmDead bmPtr .Add 1 itU32 =
      .error (.ub "dereferencing pointer to dead allocation") := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> kernel_rfl

/-- A pointer to the cell's address that has no provenance. -/
def bmNoProv : Ptr := ⟨cellAddr, none⟩

/-- Provenance-less pointer UB on `Mach`: every atomic through a pointer
without provenance, even at the address of a live allocation. -/
theorem atomic_no_provenance_ub_bm :
    bmStore bmFive bmNoProv (.Int 9) (.Int itU32) =
      .error (.ub "dereferencing pointer without provenance") ∧
    bmLoad bmFive bmNoProv (.Int itU32) = .error (.ub "dereferencing pointer without provenance") ∧
    bmCas bmFive bmNoProv 5 9 itU32 = .error (.ub "dereferencing pointer without provenance") ∧
    bmRmw bmFive bmNoProv .Add 1 itU32 =
      .error (.ub "dereferencing pointer without provenance") := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> kernel_rfl

/-- Uninitialized and invalid memory on `Mach`: an atomic load, compare
exchange, or fetch-and-op of uninitialized (or partly initialized) bytes at an
integer type is UB, and so is an atomic load of the byte `2` at `bool`. -/
theorem atomic_uninit_ub_bm :
    bmLoad (bmWith []) bmPtr (.Int itU32) =
      .error (.ub "load at type but the data in memory violates the language invariant") ∧
    bmCas (bmWith []) bmPtr 5 9 itU32 =
      .error (.ub "load at type but the data in memory violates the language invariant") ∧
    bmRmw (bmWith []) bmPtr .Add 1 itU32 =
      .error (.ub "load at type but the data in memory violates the language invariant") ∧
    bmLoad (bmWith (initBytes [5, 0])) bmPtr (.Int itU32) =
      .error (.ub "load at type but the data in memory violates the language invariant") ∧
    bmLoad (bmWith (initBytes [2])) bmPtr .Bool =
      .error (.ub "load at type but the data in memory violates the language invariant") := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> kernel_rfl

/-- Non-atomic `typed_load` of `u32` on `Mach`. -/
def bmNonAtomicLoad (m : Mach) (ptr : Ptr) : Interp (Val × Mach) :=
  typedLoad m ptr (.Int itU32) ⟨4⟩ .None

/-- Run `step1`, collect its accesses via `resetDataRaceTracking` (recording
thread `0` as active with synchronization set `sync`), run `step2`, and check
`CM.check_data_races` for thread `tid`. -/
def bmRaceCheck (step1 : Interp (Val × Mach)) (step2 : Mach → Interp (Val × Mach))
    (tid : ThreadId) (sync : Set ThreadId := ⟨[]⟩) : Interp Unit := do
  let (_, m1) ← step1
  let (prev, m1') :=
    resetDataRaceTracking { m1 with active_thread := 0, synchronized_threads := sync }
  let (_, m2) ← step2 m1'
  CM.check_data_races m2.mem tid prev

/-- Data-race witnesses on `Mach` through `resetDataRaceTracking` and
`CM.check_data_races`:
1. Unsynchronized `AtomicStore` + `AtomicLoad` at `cellAddr`: no race.
2. Unsynchronized `AtomicStore` + non-atomic `typed_load` at `cellAddr`: UB `"Data race"`.
3. Synchronized (`1 ∈ sync`) `AtomicStore` + non-atomic `typed_load`: no race.
4. Same thread (`tid = 0`) `AtomicStore` + non-atomic `typed_load`: no race.
5. Unsynchronized failing `AtomicCompareExchange` + non-atomic `typed_load`: no race.
6. Unsynchronized succeeding `AtomicCompareExchange` + non-atomic `typed_load`: UB `"Data race"`.
7. Unsynchronized `AtomicFetchAndOp` + non-atomic `typed_load`: UB `"Data race"`.
8. Unsynchronized `AtomicStore` at `[0..4)` + non-atomic `typed_load` at `[4..8)`: no race. -/
theorem atomic_data_races_bm :
    bmRaceCheck (bmStore bmFive bmPtr (.Int 9) (.Int itU32))
        (fun m => bmLoad m bmPtr (.Int itU32)) 1 = .ok () ∧
    bmRaceCheck (bmStore bmFive bmPtr (.Int 9) (.Int itU32))
        (fun m => bmNonAtomicLoad m bmPtr) 1 = .error (.ub "Data race") ∧
    bmRaceCheck (bmStore bmFive bmPtr (.Int 9) (.Int itU32))
        (fun m => bmNonAtomicLoad m bmPtr) 1 ⟨[1]⟩ = .ok () ∧
    bmRaceCheck (bmStore bmFive bmPtr (.Int 9) (.Int itU32))
        (fun m => bmNonAtomicLoad m bmPtr) 0 = .ok () ∧
    bmRaceCheck (bmCas bmFive bmPtr 6 9 itU32)
        (fun m => bmNonAtomicLoad m bmPtr) 1 = .ok () ∧
    bmRaceCheck (bmCas bmFive bmPtr 5 9 itU32)
        (fun m => bmNonAtomicLoad m bmPtr) 1 = .error (.ub "Data race") ∧
    bmRaceCheck (bmRmw bmFive bmPtr .Add 1 itU32)
        (fun m => bmNonAtomicLoad m bmPtr) 1 = .error (.ub "Data race") ∧
    bmRaceCheck (bmStore (bmWith (u32Bytes 5 ++ u32Bytes 7)) bmPtr (.Int 9) (.Int itU32))
        (fun m => bmNonAtomicLoad m (bmPtr 4)) 1 = .ok () := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> kernel_rfl

/-- Non-atomic `typed_store` of the `u32` `i` on `Mach`, returning `i`. -/
def bmNonAtomicStore (m : Mach) (ptr : Ptr) (i : Int) : Interp (Val × Mach) := do
  let m' ← typedStore m ptr (.Int i) (.Int itU32) ⟨4⟩ .None
  pure (.Int i, m')

/-- Atomic *reads* against a non-atomic *store* on `Mach`, and an atomic store
at a non-integer type, through `resetDataRaceTracking` and
`CM.check_data_races`:
1. Unsynchronized `AtomicLoad` + non-atomic `typed_store` at `cellAddr`: UB `"Data race"`.
2. Unsynchronized *failing* `AtomicCompareExchange` + non-atomic `typed_store`: UB
   `"Data race"`. A failing compare-exchange is a read, not a no-op.
3. The same pair on synchronized threads (`1 ∈ sync`): no race.
4. The same pair on the same thread (`tid = 0`): no race.
5. Failing `AtomicCompareExchange` at `[0..4)` + non-atomic `typed_store` at `[4..8)`: no race.
6. Unsynchronized `AtomicStore` of a `bool` + non-atomic `typed_load` of the `u32`
   that contains it: UB `"Data race"`. -/
theorem atomic_reads_vs_nonAtomicStore_data_races_bm :
    bmRaceCheck (bmLoad bmFive bmPtr (.Int itU32))
        (fun m => bmNonAtomicStore m bmPtr 7) 1 = .error (.ub "Data race") ∧
    bmRaceCheck (bmCas bmFive bmPtr 6 9 itU32)
        (fun m => bmNonAtomicStore m bmPtr 7) 1 = .error (.ub "Data race") ∧
    bmRaceCheck (bmCas bmFive bmPtr 6 9 itU32)
        (fun m => bmNonAtomicStore m bmPtr 7) 1 ⟨[1]⟩ = .ok () ∧
    bmRaceCheck (bmCas bmFive bmPtr 6 9 itU32)
        (fun m => bmNonAtomicStore m bmPtr 7) 0 = .ok () ∧
    bmRaceCheck (bmCas (bmWith (u32Bytes 5 ++ u32Bytes 7)) bmPtr 6 9 itU32)
        (fun m => bmNonAtomicStore m (bmPtr 4) 7) 1 = .ok () ∧
    bmRaceCheck (bmStore bmFive bmPtr (.Bool true) .Bool)
        (fun m => bmNonAtomicLoad m bmPtr) 1 = .error (.ub "Data race") := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> kernel_rfl

/-- Ill-typed and ill-formed operands on `Mach` (`cellAddr` holds `5u32`).
`AtomicCompareExchange` checks neither `current` nor, when it fails, `next`:
1. `current = true` at `u32` compares unequal to every integer: the
   compare-exchange fails silently and returns `5`.
2. A failing compare-exchange with `next = true` at `u32` returns `5`.
3. A failing compare-exchange with `next = 2^32` at `u32` returns `5`.
4. A *succeeding* one with `next = true` at `u32` is a specification panic of
   `typed_store`.
5. A *succeeding* one with `next = 2^32` at `u32` is the same specification panic.

`AtomicFetchAndOp` reaches its operand only after the load:
6. `other = true` at `u32` is the specification panic of upstream's
   `unreachable!()`.
7. The same call through a dangling pointer is UB of the load, not a panic. -/
theorem atomic_ill_typed_operands_bm :
    bmObs (evalIntrinsic bmFive .AtomicCompareExchange
        [bmArg bmPtr, (.Bool true, .Int itU32), (.Int 9, .Int itU32)] (.Int itU32)) =
      some ⟨.Int 5, [u32Bytes 5 ++ uninitBytes 4], [aLoad 4]⟩ ∧
    bmObs (evalIntrinsic bmFive .AtomicCompareExchange
        [bmArg bmPtr, (.Int 6, .Int itU32), (.Bool true, .Int itU32)] (.Int itU32)) =
      some ⟨.Int 5, [u32Bytes 5 ++ uninitBytes 4], [aLoad 4]⟩ ∧
    bmObs (bmCas bmFive bmPtr 6 4294967296 itU32) =
      some ⟨.Int 5, [u32Bytes 5 ++ uninitBytes 4], [aLoad 4]⟩ ∧
    evalIntrinsic bmFive .AtomicCompareExchange
        [bmArg bmPtr, (.Int 5, .Int itU32), (.Bool true, .Int itU32)] (.Int itU32) =
      .error (.specPanic "trying to store a value which is ill-formed for its type") ∧
    bmCas bmFive bmPtr 5 4294967296 itU32 =
      .error (.specPanic "trying to store a value which is ill-formed for its type") ∧
    evalIntrinsic bmFive (.AtomicFetchAndOp .Add)
        [bmArg bmPtr, (.Bool true, .Int itU32)] (.Int itU32) =
      .error (.specPanic "unreachable: AtomicFetchAndOp other not Value::Int") ∧
    evalIntrinsic bmDead (.AtomicFetchAndOp .Add)
        [bmArg bmPtr, (.Bool true, .Int itU32)] (.Int itU32) =
      .error (.ub "dereferencing pointer to dead allocation") := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · kernel_rfl
  · kernel_rfl
  · kernel_rfl
  · kernel_rfl

/-! ### Provenance under integer atomics on `Mach`

The cell holds the bytes of the thin raw pointer `bmPtrVal`, stored atomically
at pointer type: the address `cellAddr + 4`, each byte carrying a fragment of
the provenance of allocation 0. Integer atomics at `usize` then read the bare
address. Those that only load (`AtomicLoad`, a failing `AtomicCompareExchange`)
leave every provenance fragment in memory, so the pointer can be loaded back
with its provenance; those that store (a succeeding `AtomicCompareExchange`,
`AtomicFetchAndOp`) write bytes without provenance, even when they write the
same integer back, so the pointer loaded back afterwards has no provenance and
cannot be dereferenced (`atomic_no_provenance_ub_bm`). -/

/-- `AtomicStore` of the thin raw pointer `bmPtrVal` at pointer type into a
fresh cell, then `op` on the resulting machine. -/
def bmPtrCell (op : Mach → Interp (Val × Mach)) : Interp (Val × Mach) := do
  let (_, m) ← bmStore (bmWith []) bmPtr bmPtrVal tyRawPtr
  op m

/-- The value that an `AtomicLoad` at pointer type finds in the cell after
`bmPtrCell op`. -/
def bmPtrCellReload (op : Mach → Interp (Val × Mach)) : Option Val :=
  (bmObs (bmPtrCell op >>= fun r => bmLoad r.2 bmPtr tyRawPtr)).map (fun o => o.val)

/-- The bytes of `bmPtrVal` in memory: the little-endian address
`cellAddr + 4`, each byte carrying a fragment of the provenance of allocation 0. -/
def bmPtrProvBytes : List Byte := provBytes (⟨0⟩, ()) 0 [4, 0, 0, 0, 1, 0, 0, 0]

/-- The same address bytes without provenance. -/
def bmPtrAddrBytes : List Byte := initBytes [4, 0, 0, 0, 1, 0, 0, 0]

/-- Provenance under integer atomics at `usize` on `Mach`, on a cell that
holds the bytes of a pointer:
1. `AtomicLoad` returns the bare address; memory keeps every provenance
   fragment, and the pointer loads back with its provenance.
2. A *failing* `AtomicCompareExchange` (expecting `0`) does the same.
3. A *succeeding* `AtomicCompareExchange` that exchanges the address for itself
   leaves the same address bytes *without* provenance, and the pointer loads
   back without provenance.
4. `AtomicFetchAndOp(Add)` of `0` (`fetch_add(0)`) does the same as 3. -/
theorem atomic_int_provenance_bm :
    bmObs (bmPtrCell fun m => bmLoad m bmPtr (.Int itU64)) =
      some ⟨.Int 4294967300, [bmPtrProvBytes], [aStore 8, aLoad 8]⟩ ∧
    bmPtrCellReload (fun m => bmLoad m bmPtr (.Int itU64)) = some bmPtrVal ∧
    bmObs (bmPtrCell fun m => bmCas m bmPtr 0 7 itU64) =
      some ⟨.Int 4294967300, [bmPtrProvBytes], [aStore 8, aLoad 8]⟩ ∧
    bmPtrCellReload (fun m => bmCas m bmPtr 0 7 itU64) = some bmPtrVal ∧
    bmObs (bmPtrCell fun m => bmCas m bmPtr 4294967300 4294967300 itU64) =
      some ⟨.Int 4294967300, [bmPtrAddrBytes], [aStore 8, aLoad 8, aStore 8]⟩ ∧
    bmPtrCellReload (fun m => bmCas m bmPtr 4294967300 4294967300 itU64) =
      some (.Ptr ⟨⟨4294967300, none⟩, none⟩) ∧
    bmObs (bmPtrCell fun m => bmRmw m bmPtr .Add 0 itU64) =
      some ⟨.Int 4294967300, [bmPtrAddrBytes], [aStore 8, aLoad 8, aStore 8]⟩ ∧
    bmPtrCellReload (fun m => bmRmw m bmPtr .Add 0 itU64) =
      some (.Ptr ⟨⟨4294967300, none⟩, none⟩) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ### `Machine<TreeBorrowsMemory<x86_64>>` (`MachTB`) -/

/-- A root borrow-tree node over `n` bytes: `Unique` everywhere, unprotected,
with the given children. `TreeBorrowsMemory::allocate` creates it childless. -/
def tbRoot (n : Nat) (children : List Node := []) : Node :=
  { children := children, permissions := List.replicate n (.Unprot .Unique), «protected» := .No }

/-- A `MachTB` without threads whose memory is `allocs` (implicit writes on). -/
def tbMach (allocs : List (Allocation Path TreeBorrowsAllocationExtra))
    (accesses : List Access := []) : MachTB :=
  { prog := emptyProg
    mem := { memory := { params := ⟨true⟩, mem := { allocations := allocs, _phantom := ⟨⟩ } }
             accesses := accesses }
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

/-- A heap allocation at `cellAddr`, 8-aligned, holding `data`, with a
childless borrow tree. -/
def tbCell (data : List (AbstractByte TreeBorrowsProvenance)) (live : Bool := true) :
    Allocation Path TreeBorrowsAllocationExtra :=
  { data := data, addr := cellAddr, align := ⟨8⟩, kind := .Heap, live := live
    extra := ⟨tbRoot 8⟩ }

/-- The `MachTB` whose only allocation is 8 bytes starting with `bytes`. -/
def tbWith (bytes : List (AbstractByte TreeBorrowsProvenance)) : MachTB :=
  tbMach [tbCell (bytes ++ uninitBytes (8 - bytes.length))]

/-- A pointer into allocation 0, `off` bytes in, whose provenance is the
borrow-tree node at `path` (the root by default). -/
def tbPtr (off : Int := 0) (path : Path := []) : ThinPointer TreeBorrowsProvenance :=
  ⟨cellAddr + off, some (⟨0⟩, path)⟩

/-- A thin pointer argument. -/
def tbArg (ptr : ThinPointer TreeBorrowsProvenance) : Value TBM × «Type» :=
  (.Ptr ⟨ptr, none⟩, tyRawPtr)

/-- `AtomicStore(ptr, v)` at `ty` on `MachTB`. -/
def tbStore (m : MachTB) (ptr : ThinPointer TreeBorrowsProvenance) (v : Value TBM)
    (ty : «Type») : Interp (Value TBM × MachTB) :=
  evalIntrinsicM m .AtomicStore [tbArg ptr, (v, ty)] unitType

/-- `AtomicLoad(ptr)` at `ty` on `MachTB`. -/
def tbLoad (m : MachTB) (ptr : ThinPointer TreeBorrowsProvenance) (ty : «Type») :
    Interp (Value TBM × MachTB) :=
  evalIntrinsicM m .AtomicLoad [tbArg ptr] ty

/-- `AtomicCompareExchange(ptr, cur, next)` at the integer type `t` on `MachTB`. -/
def tbCas (m : MachTB) (ptr : ThinPointer TreeBorrowsProvenance) (cur next : Int)
    (t : IntType) : Interp (Value TBM × MachTB) :=
  evalIntrinsicM m .AtomicCompareExchange
    [tbArg ptr, (.Int cur, .Int t), (.Int next, .Int t)] (.Int t)

/-- `AtomicFetchAndOp(op)(ptr, o)` at the integer type `t` on `MachTB`. -/
def tbRmw (m : MachTB) (ptr : ThinPointer TreeBorrowsProvenance) (op : IntBinOp) (o : Int)
    (t : IntType) : Interp (Value TBM × MachTB) :=
  evalIntrinsicM m (.AtomicFetchAndOp op) [tbArg ptr, (.Int o, .Int t)] (.Int t)

/-- `AtomicStore` of `v : ty` into a fresh cell, then `AtomicLoad` at `loadTy`. -/
def tbStoreLoad (v : Value TBM) (ty loadTy : «Type») : Interp (Value TBM × MachTB) := do
  let (_, m) ← tbStore (tbWith []) tbPtr v ty
  tbLoad m tbPtr loadTy

/-- What an intrinsic on `MachTB` returned and left behind: the value, the
data of every allocation, and the access log. -/
structure TbObs where
  /-- The returned value. -/
  val : Value TBM
  /-- The data of every allocation, in allocation order. -/
  data : List (List (AbstractByte TreeBorrowsProvenance))
  /-- The access log of the resulting machine. -/
  log : List Access
  deriving DecidableEq

/-- Observe a successful intrinsic on `MachTB`. -/
def tbObs (r : Interp (Value TBM × MachTB)) : Option TbObs :=
  match r with
  | .ok (v, m) => some ⟨v, m.mem.memory.mem.allocations.map (fun a => a.data), m.mem.accesses⟩
  | .error _ => none

/-- The permissions that allocation 0's root and its children hold after a
successful intrinsic on `MachTB`. -/
def tbPerms (r : Interp (Value TBM × MachTB)) :
    Option (List Permission × List (List Permission)) :=
  match r with
  | .ok (_, m) =>
    m.mem.memory.mem.allocations.head?.map (fun a =>
      (a.extra.root.permissions, a.extra.root.children.map (fun c => c.permissions)))
  | .error _ => none

/-- What a store-then-load round trip of a value with encoding `bytes` must
show on `MachTB`; see `bmRoundTrip`. -/
def tbRoundTrip (v : Value TBM) (bytes : List (AbstractByte TreeBorrowsProvenance)) :
    Option TbObs :=
  some ⟨v, [bytes ++ uninitBytes (8 - bytes.length)], [aStore bytes.length, aLoad bytes.length]⟩

/-- `TreeBorrowsMemory::allocate` of 8 bytes produces exactly the literal cell
and root pointer that the `MachTB` witnesses use. -/
theorem tbCell_allocated :
    TreeBorrowsMemory.allocate (TreeBorrowsMemory.new ⟨true⟩) .Heap ⟨8⟩ ⟨8⟩ =
      .ok (tbPtr, (tbWith []).mem.memory) := by
  kernel_rfl

/-- Store-then-load round trips on `MachTB` across `u8`, `u16`, `u32`, `u64`,
`i32`, `i64`, `usize`, and `bool`, with the same observations as on `Mach`. -/
theorem atomic_store_load_roundtrip_tb :
    tbObs (tbStoreLoad (.Int 200) (.Int itU8) (.Int itU8)) =
      tbRoundTrip (.Int 200) (initBytes [200]) ∧
    tbObs (tbStoreLoad (.Int 48879) (.Int itU16) (.Int itU16)) =
      tbRoundTrip (.Int 48879) (initBytes [0xEF, 0xBE]) ∧
    tbObs (tbStoreLoad (.Int 3735928559) (.Int itU32) (.Int itU32)) =
      tbRoundTrip (.Int 3735928559) (initBytes [0xEF, 0xBE, 0xAD, 0xDE]) ∧
    tbObs (tbStoreLoad (.Int 81985529216486895) (.Int itU64) (.Int itU64)) =
      tbRoundTrip (.Int 81985529216486895)
        (initBytes [0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01]) ∧
    tbObs (tbStoreLoad (.Int (-2)) (.Int itI32) (.Int itI32)) =
      tbRoundTrip (.Int (-2)) (initBytes [0xFE, 0xFF, 0xFF, 0xFF]) ∧
    tbObs (tbStoreLoad (.Int (-2)) (.Int itI64) (.Int itI64)) =
      tbRoundTrip (.Int (-2)) (initBytes [0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]) ∧
    tbObs (tbStoreLoad (.Int 18446744073709551615) (.Int IntType.usize_ty)
        (.Int IntType.usize_ty)) =
      tbRoundTrip (.Int 18446744073709551615)
        (initBytes [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]) ∧
    tbObs (tbStoreLoad (.Bool true) .Bool .Bool) = tbRoundTrip (.Bool true) (initBytes [1]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- A thin raw pointer (`*const u32`) whose Tree Borrows provenance is the
borrow-tree node at path `[0, 1]` of allocation 0. -/
def tbPtrVal : Value TBM := .Ptr ⟨tbPtr 4 [0, 1], none⟩

/-- Atomics preserve Tree Borrows provenance (allocation *and* tree path)
exactly when they are used at a pointer type; see
`atomic_store_load_ptr_roundtrip_bm`. -/
theorem atomic_store_load_ptr_roundtrip_tb :
    tbObs (tbStoreLoad tbPtrVal tyRawPtr tyRawPtr) =
      tbRoundTrip tbPtrVal (provBytes (⟨0⟩, [0, 1]) 0 [4, 0, 0, 0, 1, 0, 0, 0]) ∧
    (tbObs (tbStoreLoad tbPtrVal tyRawPtr (.Int itU64))).map (fun o => o.val) =
      some (.Int 4294967300) ∧
    (tbObs (tbStoreLoad (.Int 4294967300) (.Int itU64) tyRawPtr)).map (fun o => o.val) =
      some (.Ptr ⟨⟨4294967300, none⟩, none⟩) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- The `MachTB` whose cell holds `5u32`. -/
def tbFive : MachTB := tbWith (u32Bytes 5)

/-- `AtomicCompareExchange` on `MachTB` through the root pointer: success
stores `next` and logs an atomic load and an atomic store; failure leaves
memory unchanged and logs *only* the atomic load. -/
theorem atomicCompareExchange_tb :
    tbObs (tbCas tbFive tbPtr 5 9 itU32) =
      some ⟨.Int 5, [u32Bytes 9 ++ uninitBytes 4], [aLoad 4, aStore 4]⟩ ∧
    tbObs (tbCas tbFive tbPtr 6 9 itU32) =
      some ⟨.Int 5, [u32Bytes 5 ++ uninitBytes 4], [aLoad 4]⟩ := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- What `AtomicFetchAndOp` on `tbFive` must show when it stores `n`. -/
def tbFetched (n : UInt8) : Option TbObs :=
  some ⟨.Int 5, [u32Bytes n ++ uninitBytes 4], [aLoad 4, aStore 4]⟩

/-- In-bounds `AtomicFetchAndOp` on `MachTB` for `Add`, `Sub`, `Mul`, `BitAnd`,
`BitOr`, and `BitXor`: each returns `previous` and stores the updated value. -/
theorem atomicFetchAndOp_in_bounds_tb :
    tbObs (tbRmw tbFive tbPtr .Add 3 itU32) = tbFetched 8 ∧
    tbObs (tbRmw tbFive tbPtr .Sub 2 itU32) = tbFetched 3 ∧
    tbObs (tbRmw tbFive tbPtr .Mul 7 itU32) = tbFetched 35 ∧
    tbObs (tbRmw tbFive tbPtr .BitAnd 4 itU32) = tbFetched 4 ∧
    tbObs (tbRmw tbFive tbPtr .BitOr 2 itU32) = tbFetched 7 ∧
    tbObs (tbRmw tbFive tbPtr .BitXor 1 itU32) = tbFetched 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Arithmetic UB and the missing `bring_in_bounds` of `AtomicFetchAndOp` on
`MachTB`; see `atomicFetchAndOp_arith_ub_bm` and
`atomicFetchAndOp_add_u8_overflow_bm`. -/
theorem atomicFetchAndOp_arith_ub_tb :
    tbRmw tbFive tbPtr .Div 0 itU32 = .error (.ub "division by zero") ∧
    tbRmw tbFive tbPtr .Rem 0 itU32 = .error (.ub "modulus of remainder is zero") ∧
    tbRmw (tbWith (initBytes [0, 0, 0, 0x80])) tbPtr .Div (-1) itI32 =
      .error (.ub "overflow in division") ∧
    tbRmw tbFive tbPtr .ShlUnchecked 32 itU32 = .error (.ub "overflow in unchecked shift") ∧
    tbRmw tbFive tbPtr .ShrUnchecked (-1) itU32 = .error (.ub "overflow in unchecked shift") ∧
    tbRmw (tbWith (initBytes [255])) tbPtr .Add 1 itU8 =
      .error (.specPanic "trying to store a value which is ill-formed for its type") := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> kernel_rfl

/-- Memory UB of the atomics on `MachTB` through the root pointer: misaligned
inside the allocation, one past its end, a dead allocation, no provenance, and
uninitialized memory. -/
theorem atomic_memory_ub_tb :
    tbStore tbFive (tbPtr 1) (.Int 9) (.Int itU32) =
      .error (.ub "store to a misaligned pointer") ∧
    tbCas tbFive (tbPtr 1) 5 9 itU32 = .error (.ub "load from a misaligned pointer") ∧
    tbLoad tbFive (tbPtr 8) (.Int itU32) =
      .error (.ub "dereferencing pointer outside the bounds of its allocation") ∧
    tbRmw tbFive (tbPtr 8) .Add 1 itU32 =
      .error (.ub "dereferencing pointer outside the bounds of its allocation") ∧
    tbStore (tbMach [tbCell (u32Bytes 5 ++ uninitBytes 4) false]) tbPtr (.Int 9) (.Int itU32) =
      .error (.ub "dereferencing pointer to dead allocation") ∧
    tbLoad tbFive ⟨cellAddr, none⟩ (.Int itU32) =
      .error (.ub "dereferencing pointer without provenance") ∧
    tbLoad (tbWith []) tbPtr (.Int itU32) =
      .error (.ub "load at type but the data in memory violates the language invariant") := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> kernel_rfl

/-- Non-atomic `typed_load` of `u32` on `MachTB`. -/
def tbNonAtomicLoad (m : MachTB) (ptr : ThinPointer TreeBorrowsProvenance) :
    Interp (Value TBM × MachTB) :=
  typedLoadM m ptr (.Int itU32) ⟨4⟩ .None

/-- Run `step1`, collect its accesses via `resetDataRaceTrackingM` (recording
thread `0` as active with synchronization set `sync`), run `step2`, and check
`ConcurrentMemory.check_data_races` for thread `tid`. -/
def tbRaceCheck (step1 : Interp (Value TBM × MachTB))
    (step2 : MachTB → Interp (Value TBM × MachTB))
    (tid : ThreadId) (sync : Set ThreadId := ⟨[]⟩) : Interp Unit := do
  let (_, m1) ← step1
  let (prev, m1') :=
    resetDataRaceTrackingM { m1 with active_thread := 0, synchronized_threads := sync }
  let (_, m2) ← step2 m1'
  ConcurrentMemory.check_data_races m2.mem tid prev

/-- Data-race witnesses on `MachTB` through `resetDataRaceTrackingM` and
`ConcurrentMemory.check_data_races`: atomic vs atomic succeeds, atomic store /
succeeding CAS / RMW vs non-atomic load is UB `"Data race"`, and failing CAS
or disjoint byte ranges vs non-atomic load succeed. -/
theorem atomic_data_races_tb :
    tbRaceCheck (tbStore tbFive tbPtr (.Int 9) (.Int itU32))
        (fun m => tbLoad m tbPtr (.Int itU32)) 1 = .ok () ∧
    tbRaceCheck (tbStore tbFive tbPtr (.Int 9) (.Int itU32))
        (fun m => tbNonAtomicLoad m tbPtr) 1 = .error (.ub "Data race") ∧
    tbRaceCheck (tbCas tbFive tbPtr 6 9 itU32)
        (fun m => tbNonAtomicLoad m tbPtr) 1 = .ok () ∧
    tbRaceCheck (tbCas tbFive tbPtr 5 9 itU32)
        (fun m => tbNonAtomicLoad m tbPtr) 1 = .error (.ub "Data race") ∧
    tbRaceCheck (tbRmw tbFive tbPtr .Add 1 itU32)
        (fun m => tbNonAtomicLoad m tbPtr) 1 = .error (.ub "Data race") ∧
    tbRaceCheck (tbRmw tbFive tbPtr .Add 1 itU32)
        (fun m => tbLoad m tbPtr (.Int itU32)) 1 = .ok () ∧
    tbRaceCheck (tbStore (tbWith (u32Bytes 5 ++ u32Bytes 7)) tbPtr (.Int 9) (.Int itU32))
        (fun m => tbNonAtomicLoad m (tbPtr 4)) 1 = .ok () := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> kernel_rfl

/-! ### Tree Borrows `Frozen` permission: a failing compare-exchange is a read

A shared reference `&u32` owns a `Frozen` borrow-tree node: it may read and
may not write. `AtomicLoad` and a *failing* `AtomicCompareExchange` through it
succeed, because upstream performs no store on failure; a *succeeding*
`AtomicCompareExchange`, `AtomicStore`, and `AtomicFetchAndOp` are Tree
Borrows UB. `BasicMemory` has no permissions, so all of them succeed there. -/

/-- `PointeeInfo` of `u32`: 4 bytes, 4-aligned, `Freeze`, no `UnsafeCell`. -/
def u32Pointee : PointeeInfo :=
  { layout := .Sized ⟨4⟩ ⟨4⟩, inhabited := true, unsafe_cells := .Sized [], freeze := true
    unpin := true }

/-- The borrow-tree node of a shared reference to 4 bytes: `Frozen`. -/
def tbFrozenNode : Node :=
  { children := [], permissions := List.replicate 4 (.Unprot .Frozen), «protected» := .No }

/-- The `MachTB` whose allocation holds `5u32` and has been shared-reborrowed
once: the root has the `Frozen` child `[0]`. -/
def tbShared : MachTB :=
  tbMach [{ data := u32Bytes 5, addr := cellAddr, align := ⟨4⟩, kind := .Heap, live := true
            extra := ⟨tbRoot 4 [tbFrozenNode]⟩ }]

/-- The pointer of the shared reference: provenance path `[0]`. -/
def tbSharedPtr : ThinPointer TreeBorrowsProvenance := tbPtr 0 [0]

/-- Allocate 4 bytes, store `5u32`, and retag the root pointer as `&u32`. -/
def tbSharedTrace : Interp (Pointer TreeBorrowsProvenance × TBM) := do
  let (root, tbm) ← TreeBorrowsMemory.allocate (TreeBorrowsMemory.new ⟨true⟩) .Heap ⟨4⟩ ⟨4⟩
  let tbm ← TreeBorrowsMemory.store tbm root (u32Bytes 5) ⟨4⟩
  let (shared, tbm, _) ←
    TreeBorrowsMemory.retag_ptr tbm TreeBorrowsMemory.new_call ⟨root, none⟩
      (.Ref .Immutable u32Pointee) false false (fun _ => specPanic "no vtables")
  pure (shared, tbm)

/-- `tbShared` and `tbSharedPtr` are what `TreeBorrowsMemory` itself produces
for a shared reborrow. -/
theorem tbShared_reachable :
    tbSharedTrace = .ok (⟨tbSharedPtr, none⟩, tbShared.mem.memory) := by
  kernel_rfl

/-- Through a `Frozen` shared reference on `MachTB`: `AtomicLoad` and a
failing `AtomicCompareExchange` succeed, return `5`, log only an atomic load,
and leave every permission as it was; a succeeding `AtomicCompareExchange`,
`AtomicStore`, and `AtomicFetchAndOp` are Tree Borrows UB. -/
theorem atomic_frozen_tb :
    tbObs (tbLoad tbShared tbSharedPtr (.Int itU32)) = some ⟨.Int 5, [u32Bytes 5], [aLoad 4]⟩ ∧
    tbObs (tbCas tbShared tbSharedPtr 6 9 itU32) = some ⟨.Int 5, [u32Bytes 5], [aLoad 4]⟩ ∧
    tbPerms (tbCas tbShared tbSharedPtr 6 9 itU32) =
      some (List.replicate 4 (.Unprot .Unique), [List.replicate 4 (.Unprot .Frozen)]) ∧
    tbCas tbShared tbSharedPtr 5 9 itU32 =
      .error (.ub "Tree Borrows: local write of Frozen reference") ∧
    tbStore tbShared tbSharedPtr (.Int 9) (.Int itU32) =
      .error (.ub "Tree Borrows: local write of Frozen reference") ∧
    tbRmw tbShared tbSharedPtr .Add 1 itU32 =
      .error (.ub "Tree Borrows: local write of Frozen reference") := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · kernel_rfl
  · kernel_rfl
  · kernel_rfl

/-- Mode sensitivity: the three writes that are UB through the shared
reference on `MachTB` all succeed on `Mach`, where memory has no permissions
(`atomicCompareExchange_bm` and `atomicFetchAndOp_in_bounds_bm` give the
resulting memory). -/
theorem atomic_shared_ref_mode_sensitivity :
    (bmObs (bmCas bmFive bmPtr 5 9 itU32)).isSome = true ∧
    stopOf (tbCas tbShared tbSharedPtr 5 9 itU32) =
      some (.ub "Tree Borrows: local write of Frozen reference") ∧
    (bmObs (bmStore bmFive bmPtr (.Int 9) (.Int itU32))).isSome = true ∧
    stopOf (tbStore tbShared tbSharedPtr (.Int 9) (.Int itU32)) =
      some (.ub "Tree Borrows: local write of Frozen reference") ∧
    (bmObs (bmRmw bmFive bmPtr .Add 1 itU32)).isSome = true ∧
    stopOf (tbRmw tbShared tbSharedPtr .Add 1 itU32) =
      some (.ub "Tree Borrows: local write of Frozen reference") := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- An atomic store is a real write for Tree Borrows: through the root pointer
it succeeds and is a foreign write for the shared reference, whose node
becomes `Disabled`; an `AtomicLoad` through the shared reference afterwards is
UB. -/
theorem atomic_root_store_disables_shared_tb :
    tbPerms (tbStore tbShared tbPtr (.Int 9) (.Int itU32)) =
      some (List.replicate 4 (.Unprot .Unique), [List.replicate 4 (.Unprot .Disabled)]) ∧
    stopOf (tbStore tbShared tbPtr (.Int 9) (.Int itU32) >>= fun r =>
        tbLoad r.2 tbSharedPtr (.Int itU32)) =
      some (.ub "Tree Borrows: local read of Disabled reference") := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-! ### Provenance under integer atomics on `MachTB`

The same four cases as `atomic_int_provenance_bm`, with Tree Borrows
provenance (allocation *and* borrow-tree path) in the stored pointer. -/

/-- `AtomicStore` of the thin raw pointer `tbPtrVal` at pointer type into a
fresh cell, then `op` on the resulting machine. -/
def tbPtrCell (op : MachTB → Interp (Value TBM × MachTB)) : Interp (Value TBM × MachTB) := do
  let (_, m) ← tbStore (tbWith []) tbPtr tbPtrVal tyRawPtr
  op m

/-- The value that an `AtomicLoad` at pointer type finds in the cell after
`tbPtrCell op`. -/
def tbPtrCellReload (op : MachTB → Interp (Value TBM × MachTB)) : Option (Value TBM) :=
  (tbObs (tbPtrCell op >>= fun r => tbLoad r.2 tbPtr tyRawPtr)).map (fun o => o.val)

/-- The bytes of `tbPtrVal` in memory: the little-endian address
`cellAddr + 4`, each byte carrying a fragment of the provenance
(allocation 0, path `[0, 1]`). -/
def tbPtrProvBytes : List (AbstractByte TreeBorrowsProvenance) :=
  provBytes (⟨0⟩, [0, 1]) 0 [4, 0, 0, 0, 1, 0, 0, 0]

/-- The same address bytes without provenance. -/
def tbPtrAddrBytes : List (AbstractByte TreeBorrowsProvenance) :=
  initBytes [4, 0, 0, 0, 1, 0, 0, 0]

/-- Provenance under integer atomics at `usize` on `MachTB`; see
`atomic_int_provenance_bm`. `AtomicLoad` and a failing `AtomicCompareExchange`
leave the Tree Borrows provenance of every byte in memory; a succeeding
`AtomicCompareExchange` of the address for itself and `fetch_add(0)` erase it. -/
theorem atomic_int_provenance_tb :
    tbObs (tbPtrCell fun m => tbLoad m tbPtr (.Int itU64)) =
      some ⟨.Int 4294967300, [tbPtrProvBytes], [aStore 8, aLoad 8]⟩ ∧
    tbPtrCellReload (fun m => tbLoad m tbPtr (.Int itU64)) = some tbPtrVal ∧
    tbObs (tbPtrCell fun m => tbCas m tbPtr 0 7 itU64) =
      some ⟨.Int 4294967300, [tbPtrProvBytes], [aStore 8, aLoad 8]⟩ ∧
    tbPtrCellReload (fun m => tbCas m tbPtr 0 7 itU64) = some tbPtrVal ∧
    tbObs (tbPtrCell fun m => tbCas m tbPtr 4294967300 4294967300 itU64) =
      some ⟨.Int 4294967300, [tbPtrAddrBytes], [aStore 8, aLoad 8, aStore 8]⟩ ∧
    tbPtrCellReload (fun m => tbCas m tbPtr 4294967300 4294967300 itU64) =
      some (.Ptr ⟨⟨4294967300, none⟩, none⟩) ∧
    tbObs (tbPtrCell fun m => tbRmw m tbPtr .Add 0 itU64) =
      some ⟨.Int 4294967300, [tbPtrAddrBytes], [aStore 8, aLoad 8, aStore 8]⟩ ∧
    tbPtrCellReload (fun m => tbRmw m tbPtr .Add 0 itU64) =
      some (.Ptr ⟨⟨4294967300, none⟩, none⟩) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ### Tree Borrows `Reserved` permission: only a store activates a two-phase borrow

An unprotected mutable reference `&mut u32` owns a `Reserved` borrow-tree node
until it is first written through: the reservation phase of a two-phase
borrow. In the unprotected state machine of
`spec/mem/tree_borrows/state_machine_unprotected.md`, a local read keeps
`Reserved`, a foreign read keeps `Reserved`, and a local write makes it
`Unique` (upstream's name at `d821c6e3` for the activated state, Miri's
`Active`); a foreign read turns `Unique` into `Frozen`, and a foreign write
turns `Frozen` into `Disabled` (`permissionUnprot_two_phase_transitions`).

For the atomic intrinsics through a `Reserved` reference this means:
* `AtomicLoad` and a *failing* `AtomicCompareExchange` are reads. The node
  stays `Reserved`, a `Frozen` sibling stays usable, and a later foreign read
  through the parent leaves the reference `Reserved` and still activatable.
* `AtomicStore`, `AtomicFetchAndOp`, and a *succeeding* `AtomicCompareExchange`
  are writes. The node becomes `Unique`, a `Frozen` sibling becomes `Disabled`
  (reading through it is UB), and a later foreign read through the parent
  freezes the reference, so that writing through it again is UB.

`tbTwoPhase` is the canonical two-phase shape: a mutable reborrow of the root
followed by a shared reborrow of the root (as for the receiver and the argument
of `v.push(v.len())`). -/

/-- The borrow-tree node of an unprotected mutable reference to 4 bytes that
has not been written through: `Reserved`. -/
def tbReservedNode : Node :=
  { children := [], permissions := List.replicate 4 (.Unprot .Reserved), «protected» := .No }

/-- The `MachTB` whose allocation holds `5u32` and whose root has been
reborrowed twice: mutably (child `[0]`, `Reserved`) and then shared (child
`[1]`, `Frozen`). -/
def tbTwoPhase : MachTB :=
  tbMach [{ data := u32Bytes 5, addr := cellAddr, align := ⟨4⟩, kind := .Heap, live := true
            extra := ⟨tbRoot 4 [tbReservedNode, tbFrozenNode]⟩ }]

/-- The pointer of the mutable reference: provenance path `[0]`. -/
def tbMutPtr : ThinPointer TreeBorrowsProvenance := tbPtr 0 [0]

/-- The pointer of its shared sibling: provenance path `[1]`. -/
def tbSibPtr : ThinPointer TreeBorrowsProvenance := tbPtr 0 [1]

/-- Allocate 4 bytes, store `5u32`, and retag the root pointer first as
`&mut u32` and then as `&u32` (neither at function entry, so unprotected). -/
def tbTwoPhaseTrace :
    Interp (Pointer TreeBorrowsProvenance × Pointer TreeBorrowsProvenance × TBM) := do
  let (root, tbm) ← TreeBorrowsMemory.allocate (TreeBorrowsMemory.new ⟨true⟩) .Heap ⟨4⟩ ⟨4⟩
  let tbm ← TreeBorrowsMemory.store tbm root (u32Bytes 5) ⟨4⟩
  let (mutRef, tbm, _) ←
    TreeBorrowsMemory.retag_ptr tbm TreeBorrowsMemory.new_call ⟨root, none⟩
      (.Ref .Mutable u32Pointee) false false (fun _ => specPanic "no vtables")
  let (shared, tbm, _) ←
    TreeBorrowsMemory.retag_ptr tbm TreeBorrowsMemory.new_call ⟨root, none⟩
      (.Ref .Immutable u32Pointee) false false (fun _ => specPanic "no vtables")
  pure (mutRef, shared, tbm)

/-- `tbTwoPhase`, `tbMutPtr`, and `tbSibPtr` are what `TreeBorrowsMemory` itself
produces for a mutable reborrow followed by a shared reborrow: the mutable
reference is `Reserved`, and the shared reborrow (a foreign read for it) leaves
it `Reserved`. -/
theorem tbTwoPhase_reachable :
    tbTwoPhaseTrace = .ok (⟨tbMutPtr, none⟩, ⟨tbSibPtr, none⟩, tbTwoPhase.mem.memory) := by
  kernel_rfl

/-- The transitions of the unprotected Tree Borrows state machine behind the
two-phase asymmetry: reads, local or foreign, keep `Reserved`; a local write
activates it to `Unique`; a foreign read freezes `Unique`; `Frozen` rejects a
local write and is disabled by a foreign write; `Disabled` rejects a local
read. -/
theorem permissionUnprot_two_phase_transitions :
    PermissionUnprot.transition .Reserved .Read .Local = .ok .Reserved ∧
    PermissionUnprot.transition .Reserved .Read .Foreign = .ok .Reserved ∧
    PermissionUnprot.transition .Reserved .Write .Local = .ok .Unique ∧
    PermissionUnprot.transition .Unique .Read .Foreign = .ok .Frozen ∧
    PermissionUnprot.transition .Frozen .Write .Local =
      .error (.ub "Tree Borrows: local write of Frozen reference") ∧
    PermissionUnprot.transition .Frozen .Write .Foreign = .ok .Disabled ∧
    PermissionUnprot.transition .Disabled .Read .Local =
      .error (.ub "Tree Borrows: local read of Disabled reference") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The permissions of `tbTwoPhase`'s root, of the mutable child `[0]`, and of
the shared child `[1]`, each uniform over the 4 bytes, as `tbPerms` reports
them. -/
def tbTwoPhasePerms (root mutRef shared : PermissionUnprot) :
    Option (List Permission × List (List Permission)) :=
  some (List.replicate 4 (.Unprot root),
    [List.replicate 4 (.Unprot mutRef), List.replicate 4 (.Unprot shared)])

/-- Reads through the `Reserved` reference on `MachTB`: `AtomicLoad` and a
*failing* `AtomicCompareExchange` succeed, return `5`, log only an atomic load,
and leave the reference `Reserved` and its shared sibling `Frozen`. -/
theorem atomic_reserved_reads_tb :
    tbObs (tbLoad tbTwoPhase tbMutPtr (.Int itU32)) =
      some ⟨.Int 5, [u32Bytes 5], [aLoad 4]⟩ ∧
    tbPerms (tbLoad tbTwoPhase tbMutPtr (.Int itU32)) =
      tbTwoPhasePerms .Unique .Reserved .Frozen ∧
    tbObs (tbCas tbTwoPhase tbMutPtr 6 9 itU32) =
      some ⟨.Int 5, [u32Bytes 5], [aLoad 4]⟩ ∧
    tbPerms (tbCas tbTwoPhase tbMutPtr 6 9 itU32) =
      tbTwoPhasePerms .Unique .Reserved .Frozen := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Writes through the `Reserved` reference on `MachTB`: `AtomicStore`, a
*succeeding* `AtomicCompareExchange`, and `AtomicFetchAndOp` succeed, activate
the reference (`Reserved` becomes `Unique`), and disable its shared sibling
(`Frozen` becomes `Disabled`). -/
theorem atomic_reserved_writes_activate_tb :
    tbPerms (tbStore tbTwoPhase tbMutPtr (.Int 9) (.Int itU32)) =
      tbTwoPhasePerms .Unique .Unique .Disabled ∧
    tbObs (tbCas tbTwoPhase tbMutPtr 5 9 itU32) =
      some ⟨.Int 5, [u32Bytes 9], [aLoad 4, aStore 4]⟩ ∧
    tbPerms (tbCas tbTwoPhase tbMutPtr 5 9 itU32) =
      tbTwoPhasePerms .Unique .Unique .Disabled ∧
    tbObs (tbRmw tbTwoPhase tbMutPtr .Add 1 itU32) =
      some ⟨.Int 5, [u32Bytes 6], [aLoad 4, aStore 4]⟩ ∧
    tbPerms (tbRmw tbTwoPhase tbMutPtr .Add 1 itU32) =
      tbTwoPhasePerms .Unique .Unique .Disabled := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- What the difference means for foreign reads on `MachTB`.
After a read through the `Reserved` reference (`AtomicLoad`, a failing
`AtomicCompareExchange`):
1. and 2. an `AtomicLoad` through the shared sibling succeeds and the reference
   is still `Reserved`;
6. after an `AtomicLoad` through the parent (the root pointer), an `AtomicStore`
   through the reference still succeeds and activates it.

After a write through it (`AtomicStore`, a succeeding `AtomicCompareExchange`,
`AtomicFetchAndOp`):
3., 4., and 5. an `AtomicLoad` through the shared sibling is UB;
7. an `AtomicLoad` through the parent freezes the reference (`Unique` becomes
   `Frozen`), and
8. an `AtomicStore` through the reference is then UB. -/
theorem atomic_reserved_foreign_read_asymmetry_tb :
    tbPerms (tbLoad tbTwoPhase tbMutPtr (.Int itU32) >>= fun r =>
        tbLoad r.2 tbSibPtr (.Int itU32)) =
      tbTwoPhasePerms .Unique .Reserved .Frozen ∧
    tbPerms (tbCas tbTwoPhase tbMutPtr 6 9 itU32 >>= fun r =>
        tbLoad r.2 tbSibPtr (.Int itU32)) =
      tbTwoPhasePerms .Unique .Reserved .Frozen ∧
    stopOf (tbStore tbTwoPhase tbMutPtr (.Int 9) (.Int itU32) >>= fun r =>
        tbLoad r.2 tbSibPtr (.Int itU32)) =
      some (.ub "Tree Borrows: local read of Disabled reference") ∧
    stopOf (tbCas tbTwoPhase tbMutPtr 5 9 itU32 >>= fun r =>
        tbLoad r.2 tbSibPtr (.Int itU32)) =
      some (.ub "Tree Borrows: local read of Disabled reference") ∧
    stopOf (tbRmw tbTwoPhase tbMutPtr .Add 1 itU32 >>= fun r =>
        tbLoad r.2 tbSibPtr (.Int itU32)) =
      some (.ub "Tree Borrows: local read of Disabled reference") ∧
    tbPerms (tbCas tbTwoPhase tbMutPtr 6 9 itU32 >>= fun r =>
        tbLoad r.2 tbPtr (.Int itU32) >>= fun r =>
        tbStore r.2 tbMutPtr (.Int 7) (.Int itU32)) =
      tbTwoPhasePerms .Unique .Unique .Disabled ∧
    tbPerms (tbCas tbTwoPhase tbMutPtr 5 9 itU32 >>= fun r =>
        tbLoad r.2 tbPtr (.Int itU32)) =
      tbTwoPhasePerms .Unique .Frozen .Disabled ∧
    stopOf (tbCas tbTwoPhase tbMutPtr 5 9 itU32 >>= fun r =>
        tbLoad r.2 tbPtr (.Int itU32) >>= fun r =>
        tbStore r.2 tbMutPtr (.Int 7) (.Int itU32)) =
      some (.ub "Tree Borrows: local write of Frozen reference") := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ### `Terminator::Intrinsic` end to end: `step` / `steps` and `stepTB` / `stepsTB`

`atomicFn` runs the four atomic intrinsics as terminators of a real MiniRust
function, on a `u32` local `_0` whose address it takes with `&raw`:
```text
bb0: StorageLive(_0 .. _5);
     _1 = AtomicStore(&raw _0, 5)                    -> bb1
bb1: _2 = AtomicLoad(&raw _0)                        -> bb2
bb2: _3 = AtomicCompareExchange(&raw _0, 5, 9)       -> bb3   // succeeds
bb3: _4 = AtomicFetchAndOp(Add)(&raw _0, 1)          -> bb4
bb4: _5 = AtomicCompareExchange(&raw _0, 5, 77)      -> bb5   // fails
bb5: unreachable
```
Each terminator step evaluates the return place and the arguments, runs the
intrinsic, stores the returned value to the return place (a non-atomic
store), and jumps. -/

/-- The local `_n`. -/
def lname (n : Nat) : LocalName := ⟨⟨n⟩⟩

/-- The basic block `bbn`. -/
def bname (n : Nat) : BbName := ⟨⟨n⟩⟩

/-- `&raw _0`. -/
def cellPtrExpr : ValueExpr := .AddrOf (.Local (lname 0)) (.Raw .None)

/-- `&_0`, a shared reference. -/
def cellRefExpr : ValueExpr := .AddrOf (.Local (lname 0)) (.Ref .Immutable u32Pointee)

/-- The `u32` constant `i`. -/
def constU32 (i : Int) : ValueExpr := .Constant (.Int i) (.Int itU32)

/-- A regular block ending in `_ret = op(args) -> bbnext`. -/
def intrinsicBlock (stmts : List Statement) (op : IntrinsicOp) (args : List ValueExpr)
    (ret next : Nat) : BasicBlock :=
  { statements := stmts
    terminator := .Intrinsic op args (.Local (lname ret)) (some (bname next))
    kind := .Regular }

/-- The function above. -/
def atomicFn : Function :=
  { locals := ⟨[(lname 0, .Int itU32), (lname 1, unitType), (lname 2, .Int itU32),
      (lname 3, .Int itU32), (lname 4, .Int itU32), (lname 5, .Int itU32)]⟩
    args := []
    ret := lname 1
    calling_convention := .Rust
    blocks := ⟨[
      (bname 0, intrinsicBlock
        [.StorageLive (lname 0), .StorageLive (lname 1), .StorageLive (lname 2),
         .StorageLive (lname 3), .StorageLive (lname 4), .StorageLive (lname 5)]
        .AtomicStore [cellPtrExpr, constU32 5] 1 1),
      (bname 1, intrinsicBlock [] .AtomicLoad [cellPtrExpr] 2 2),
      (bname 2, intrinsicBlock [] .AtomicCompareExchange
        [cellPtrExpr, constU32 5, constU32 9] 3 3),
      (bname 3, intrinsicBlock [] (.AtomicFetchAndOp .Add) [cellPtrExpr, constU32 1] 4 4),
      (bname 4, intrinsicBlock [] .AtomicCompareExchange
        [cellPtrExpr, constU32 5, constU32 77] 5 5),
      (bname 5, { statements := [], terminator := .Unreachable, kind := .Regular })]⟩
    start := bname 0
    implicit_writes := true }

/-- A function that uses atomics through a shared reference `&_0`:
```text
bb0: StorageLive(_0 .. _2); _0 = 5;
     _2 = AtomicCompareExchange(&_0, 6, 9)           -> bb1   // fails: a read
bb1: _1 = AtomicStore(&_0, 9)                        -> bb2   // a write
bb2: unreachable
``` -/
def sharedRefFn : Function :=
  { locals := ⟨[(lname 0, .Int itU32), (lname 1, unitType), (lname 2, .Int itU32)]⟩
    args := []
    ret := lname 1
    calling_convention := .Rust
    blocks := ⟨[
      (bname 0, intrinsicBlock
        [.StorageLive (lname 0), .StorageLive (lname 1), .StorageLive (lname 2),
         .Assign (.Local (lname 0)) (constU32 5)]
        .AtomicCompareExchange [cellRefExpr, constU32 6, constU32 9] 2 1),
      (bname 1, intrinsicBlock [] .AtomicStore [cellRefExpr, constU32 9] 1 2),
      (bname 2, { statements := [], terminator := .Unreachable, kind := .Regular })]⟩
    start := bname 0
    implicit_writes := true }

/-- The program whose only function is `f`. -/
def progOf (f : Function) : Program :=
  { functions := ⟨[(⟨⟨0⟩⟩, f)]⟩, start := ⟨⟨0⟩⟩, globals := ⟨[]⟩, traits := ⟨[]⟩
    vtables := ⟨[]⟩ }

/-- The `Mach` about to run `f` in its only thread, with empty memory. -/
def bmStart (f : Function) : Mach :=
  { prog := progOf f
    mem := { memory := BasicMemory.new, accesses := [] }
    intptrcast := ⟨⟨[]⟩⟩
    threads := [{ stack := [{ func := f, locals := ⟨[]⟩, stack_pop_action := .BottomOfStack
                              next_block := f.start, next_stmt := 0, extra := () }]
                  state := .Enabled, unwind_payloads := [] }]
    active_thread := 0
    synchronized_threads := ⟨[]⟩
    locks := []
    global_ptrs := ⟨[]⟩
    fn_ptrs := ⟨[]⟩
    vtable_ptrs := ⟨[]⟩
    stdout := ⟨[]⟩
    stderr := ⟨[]⟩ }

/-- The `MachTB` about to run `f` in its only thread, with empty memory. -/
def tbStart (f : Function) : MachTB :=
  { prog := progOf f
    mem := { memory := TreeBorrowsMemory.new ⟨true⟩, accesses := [] }
    intptrcast := ⟨⟨[]⟩⟩
    threads := [{ stack := [{ func := f, locals := ⟨[]⟩, stack_pop_action := .BottomOfStack
                              next_block := f.start, next_stmt := 0
                              extra := TreeBorrowsMemory.new_call }]
                  state := .Enabled, unwind_payloads := [] }]
    active_thread := 0
    synchronized_threads := ⟨[]⟩
    locks := []
    global_ptrs := ⟨[]⟩
    fn_ptrs := ⟨[]⟩
    vtable_ptrs := ⟨[]⟩
    stdout := ⟨[]⟩
    stderr := ⟨[]⟩ }

/-- The memory of a `Mach` after some steps: the data of every allocation (the
locals, in `StorageLive` order) and the accesses of the last step. -/
structure BmMemObs where
  /-- The data of every allocation, in allocation order. -/
  data : List (List Byte)
  /-- The accesses of the last step. -/
  log : List Access
  deriving DecidableEq

/-- Observe a `Mach` that did not stop. -/
def bmMemObs (r : Interp Mach) : Option BmMemObs :=
  match r with
  | .ok m => some ⟨m.mem.memory.allocations.map (fun a => a.data), m.mem.accesses⟩
  | .error _ => none

/-- The memory of a `MachTB` after some steps; see `BmMemObs`. -/
structure TbMemObs where
  /-- The data of every allocation, in allocation order. -/
  data : List (List (AbstractByte TreeBorrowsProvenance))
  /-- The accesses of the last step. -/
  log : List Access
  deriving DecidableEq

/-- Observe a `MachTB` that did not stop. -/
def tbMemObs (r : Interp MachTB) : Option TbMemObs :=
  match r with
  | .ok m => some ⟨m.mem.memory.mem.allocations.map (fun a => a.data), m.mem.accesses⟩
  | .error _ => none

/-- `atomicFn` on `Mach`, one `step` per intrinsic terminator after the six
`StorageLive` steps. `_0` goes `5`, `5`, `9`, `10`, `10`; the returned values
are `()`, `5`, `5` (success), `9`, `10` (failure). The succeeding
compare-exchange logs an atomic load and an atomic store, the failing one only
an atomic load; each step ends with the non-atomic store to the return place.
Twelve `steps` reach `unreachable`. -/
theorem atomicFn_steps_bm :
    bmMemObs (steps 6 (bmStart atomicFn) >>= step) =
      some ⟨[u32Bytes 5, [], uninitBytes 4, uninitBytes 4, uninitBytes 4, uninitBytes 4],
        [aStore 4, retStore 0 (2 * cellAddr)]⟩ ∧
    bmMemObs (steps 7 (bmStart atomicFn) >>= step) =
      some ⟨[u32Bytes 5, [], u32Bytes 5, uninitBytes 4, uninitBytes 4, uninitBytes 4],
        [aLoad 4, retStore 4 (3 * cellAddr)]⟩ ∧
    bmMemObs (steps 8 (bmStart atomicFn) >>= step) =
      some ⟨[u32Bytes 9, [], u32Bytes 5, u32Bytes 5, uninitBytes 4, uninitBytes 4],
        [aLoad 4, aStore 4, retStore 4 (4 * cellAddr)]⟩ ∧
    bmMemObs (steps 9 (bmStart atomicFn) >>= step) =
      some ⟨[u32Bytes 10, [], u32Bytes 5, u32Bytes 5, u32Bytes 9, uninitBytes 4],
        [aLoad 4, aStore 4, retStore 4 (5 * cellAddr)]⟩ ∧
    bmMemObs (steps 10 (bmStart atomicFn) >>= step) =
      some ⟨[u32Bytes 10, [], u32Bytes 5, u32Bytes 5, u32Bytes 9, u32Bytes 10],
        [aLoad 4, retStore 4 (6 * cellAddr)]⟩ ∧
    stopOf (steps 12 (bmStart atomicFn)) = some (.ub "reached unreachable code") := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- `atomicFn` on `MachTB`, one `stepTB` per intrinsic terminator: the same
observations as on `Mach` (`&raw` does not reborrow, so every access goes
through the root of `_0`'s borrow tree). -/
theorem atomicFn_steps_tb :
    tbMemObs (stepsTB 6 (tbStart atomicFn) >>= stepTB) =
      some ⟨[u32Bytes 5, [], uninitBytes 4, uninitBytes 4, uninitBytes 4, uninitBytes 4],
        [aStore 4, retStore 0 (2 * cellAddr)]⟩ ∧
    tbMemObs (stepsTB 7 (tbStart atomicFn) >>= stepTB) =
      some ⟨[u32Bytes 5, [], u32Bytes 5, uninitBytes 4, uninitBytes 4, uninitBytes 4],
        [aLoad 4, retStore 4 (3 * cellAddr)]⟩ ∧
    tbMemObs (stepsTB 8 (tbStart atomicFn) >>= stepTB) =
      some ⟨[u32Bytes 9, [], u32Bytes 5, u32Bytes 5, uninitBytes 4, uninitBytes 4],
        [aLoad 4, aStore 4, retStore 4 (4 * cellAddr)]⟩ ∧
    tbMemObs (stepsTB 9 (tbStart atomicFn) >>= stepTB) =
      some ⟨[u32Bytes 10, [], u32Bytes 5, u32Bytes 5, u32Bytes 9, uninitBytes 4],
        [aLoad 4, aStore 4, retStore 4 (5 * cellAddr)]⟩ ∧
    tbMemObs (stepsTB 10 (tbStart atomicFn) >>= stepTB) =
      some ⟨[u32Bytes 10, [], u32Bytes 5, u32Bytes 5, u32Bytes 9, u32Bytes 10],
        [aLoad 4, retStore 4 (6 * cellAddr)]⟩ ∧
    stopOf (stepsTB 12 (tbStart atomicFn)) = some (.ub "reached unreachable code") := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- `sharedRefFn` end to end. The failing compare-exchange through `&_0`
succeeds on both machines and logs only an atomic load. The `AtomicStore`
through `&_0` stores `9` on `Mach` and is Tree Borrows UB on `MachTB`. -/
theorem sharedRefFn_mode_sensitivity :
    bmMemObs (steps 4 (bmStart sharedRefFn) >>= step) =
      some ⟨[u32Bytes 5, [], u32Bytes 5], [aLoad 4, retStore 4 (3 * cellAddr)]⟩ ∧
    tbMemObs (stepsTB 4 (tbStart sharedRefFn) >>= stepTB) =
      some ⟨[u32Bytes 5, [], u32Bytes 5], [aLoad 4, retStore 4 (3 * cellAddr)]⟩ ∧
    bmMemObs (steps 5 (bmStart sharedRefFn) >>= step) =
      some ⟨[u32Bytes 9, [], u32Bytes 5], [aStore 4, retStore 0 (2 * cellAddr)]⟩ ∧
    stopOf (stepsTB 5 (tbStart sharedRefFn) >>= stepTB) =
      some (.ub "Tree Borrows: local write of Frozen reference") := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Function whose `AtomicStore` terminator omits `next_block` (`none`). -/
def divergingAtomicFn : Function :=
  { locals := ⟨[(lname 0, .Int itU32), (lname 1, unitType)]⟩
    args := [], ret := lname 1, calling_convention := .Rust
    blocks := ⟨[(bname 0,
      { statements := [.StorageLive (lname 0), .StorageLive (lname 1)]
        terminator := .Intrinsic .AtomicStore [cellPtrExpr, constU32 5] (.Local (lname 1)) none
        kind := .Regular })]⟩
    start := bname 0, implicit_writes := true }

/-- `divergingAtomicFn` end to end on `Mach` and `MachTB`: a returning atomic
intrinsic with `next_block = none` hits UB on both memory models. -/
theorem divergingAtomicFn_no_next_block_ub :
    stopOf (steps 2 (bmStart divergingAtomicFn) >>= step) =
      some (.ub "return from an intrinsic where caller did not specify next block") ∧
    stopOf (stepsTB 2 (tbStart divergingAtomicFn) >>= stepTB) =
      some (.ub "return from an intrinsic where caller did not specify next block") := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- `_1 = AtomicStore()` after `stmts`: no arguments and no `next_block`. -/
def faultyAtomicFn (stmts : List Statement) : Function :=
  { locals := ⟨[(lname 1, unitType)]⟩
    args := [], ret := lname 1, calling_convention := .Rust
    blocks := ⟨[(bname 0,
      { statements := stmts
        terminator := .Intrinsic .AtomicStore [] (.Local (lname 1)) none
        kind := .Regular })]⟩
    start := bname 0, implicit_writes := true }

/-- Fault priority of `Terminator::Intrinsic` on `Mach` and `MachTB`: with the
return place `_1` dead, `eval_place` stops first; with `_1` live, the arity
check stops next; the missing `next_block` is never reported. -/
theorem faultyAtomicFn_fault_priority :
    stopOf (step (bmStart (faultyAtomicFn []))) = some (.ub "access to a dead local") ∧
    stopOf (stepTB (tbStart (faultyAtomicFn []))) = some (.ub "access to a dead local") ∧
    stopOf (steps 1 (bmStart (faultyAtomicFn [.StorageLive (lname 1)])) >>= step) =
      some (.ub "invalid number of arguments for `AtomicStore` intrinsic") ∧
    stopOf (stepsTB 1 (tbStart (faultyAtomicFn [.StorageLive (lname 1)])) >>= stepTB) =
      some (.ub "invalid number of arguments for `AtomicStore` intrinsic") := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- `_0 = 5; *(&raw _1[1]) = AtomicLoad(&raw _0)`: the `u32` return place lies
one byte into the `[u8; 8]` local `_1`, misaligned for `u32`. -/
def misalignedRetAtomicFn : Function :=
  { locals := ⟨[(lname 0, .Int itU32), (lname 1, .Array (.Int itU8) 8)]⟩
    args := [], ret := lname 0, calling_convention := .Rust
    blocks := ⟨[(bname 0,
      { statements := [.StorageLive (lname 0), .StorageLive (lname 1),
          .Assign (.Local (lname 0)) (constU32 5)]
        terminator := .Intrinsic .AtomicLoad [cellPtrExpr]
          (.Deref (.AddrOf (.Index (.Local (lname 1)) (constU32 1)) (.Raw .None)) (.Int itU32))
          (some (bname 0))
        kind := .Regular })]⟩
    start := bname 0, implicit_writes := true }

/-- `misalignedRetAtomicFn` end to end: `eval_place` and the `AtomicLoad`
succeed, and only then `place_store` is UB, on both memory models. -/
theorem misalignedRetAtomicFn_store_ub :
    stopOf (steps 3 (bmStart misalignedRetAtomicFn) >>= step) =
      some (.ub "storing to a place based on a misaligned pointer") ∧
    stopOf (stepsTB 3 (tbStart misalignedRetAtomicFn) >>= stepTB) =
      some (.ub "storing to a place based on a misaligned pointer") := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-! ## §5. Vacuity and axiom audit

The conditional laws of §2 and §3 take the outcome of `typed_load` or
`typed_store` as a hypothesis. The instances below discharge those hypotheses
on the concrete machines of §4 and so show that the laws are not vacuous; the
results agree with what the kernel computes directly in §4. -/

/-- The fresh-cell `MachTB` of §4 satisfies `MachTB.wfLive`: its memory is what
`TreeBorrowsMemory::allocate` makes of the empty memory. -/
theorem tbFresh_wfLive : MiniRustSpec.Correspondence.MachTB.wfLive (tbWith []) :=
  MiniRustSpec.Correspondence.TreeBorrowsMemory.allocate_wfLive
    (MiniRustSpec.Correspondence.TreeBorrowsMemory.new_wfLive ⟨true⟩) tbCell_allocated

/-- `evalIntrinsicM_atomic_tb_wfLive` is not vacuous: on the `wfLive`
fresh-cell machine, `AtomicStore` of `7u32` succeeds with an explicitly known
resulting machine, and that machine is `wfLive`. -/
theorem atomicStore_tb_wfLive_witness :
    MiniRustSpec.Correspondence.MachTB.wfLive (tbWith []) ∧
    evalIntrinsicM (tbWith []) .AtomicStore [tbArg tbPtr, (.Int 7, .Int itU32)] unitType =
      .ok (unitValueM, tbMach [tbCell (u32Bytes 7 ++ uninitBytes 4)] [aStore 4]) ∧
    MiniRustSpec.Correspondence.MachTB.wfLive
      (tbMach [tbCell (u32Bytes 7 ++ uninitBytes 4)] [aStore 4]) := by
  have h : evalIntrinsicM (tbWith []) .AtomicStore [tbArg tbPtr, (.Int 7, .Int itU32)]
      unitType = .ok (unitValueM, tbMach [tbCell (u32Bytes 7 ++ uninitBytes 4)] [aStore 4]) := by
    kernel_rfl
  exact ⟨tbFresh_wfLive, h, evalIntrinsicM_atomic_tb_wfLive (op := .AtomicStore) rfl tbFresh_wfLive h⟩

/-- The atomic `typed_load` of `5u32` on `tbFive`, with the resulting machine
written out: only the access log grows. -/
theorem typedLoadM_tbFive :
    typedLoadM tbFive tbPtr (.Int itU32) ⟨4⟩ .Atomic =
      .ok (.Int 5, tbMach [tbCell (u32Bytes 5 ++ uninitBytes 4)] [aLoad 4]) := by
  kernel_rfl

/-- `atomicCompareExchange_failure` on `tbFive`: comparing against `6` returns
`5` and the machine after the load. -/
theorem atomicCompareExchange_failure_instance :
    evalIntrinsicM tbFive .AtomicCompareExchange
        [(.Ptr ⟨tbPtr, none⟩, tyRawPtr), (.Int 6, .Int itU32), (.Int 9, .Int itU32)]
        (.Int itU32) =
      .ok (.Int 5, tbMach [tbCell (u32Bytes 5 ++ uninitBytes 4)] [aLoad 4]) :=
  atomicCompareExchange_failure tyRawPtr (.Int 9) (al := ⟨4⟩) rfl (by decide) typedLoadM_tbFive
    (fun h => absurd (Value.Int.inj h) (by decide))

/-- `atomicCompareExchange_failure_accesses` on `tbFive`: the log of the
failing compare-exchange is exactly one atomic load of 4 bytes. -/
theorem atomicCompareExchange_failure_accesses_instance :
    (tbMach [tbCell (u32Bytes 5 ++ uninitBytes 4)] [aLoad 4]).mem.accesses =
      tbFive.mem.accesses ++ [⟨.Load, .Atomic, tbPtr.addr, itU32.size⟩] :=
  atomicCompareExchange_failure_accesses
    atomicCompareExchange_failure_instance (fun h => absurd (Value.Int.inj h) (by decide))

/-- `atomicCompareExchange_success` on `tbFive`: comparing against `5` stores
`9` and returns `5`. -/
theorem atomicCompareExchange_success_instance :
    evalIntrinsicM tbFive .AtomicCompareExchange
        [(.Ptr ⟨tbPtr, none⟩, tyRawPtr), (.Int 5, .Int itU32), (.Int 9, .Int itU32)]
        (.Int itU32) =
      .ok (.Int 5, tbMach [tbCell (u32Bytes 9 ++ uninitBytes 4)] [aLoad 4, aStore 4]) :=
  atomicCompareExchange_success tyRawPtr (al := ⟨4⟩) rfl (by decide) typedLoadM_tbFive
    (by kernel_rfl)

/-- `atomicFetchAndOp_div_zero_ub` on `tbFive`. -/
theorem atomicFetchAndOp_div_zero_instance :
    evalIntrinsicM tbFive (.AtomicFetchAndOp .Div)
        [(.Ptr ⟨tbPtr, none⟩, tyRawPtr), (.Int 0, .Int itU32)] (.Int itU32) =
      .error (.ub "division by zero") :=
  atomicFetchAndOp_div_zero_ub tyRawPtr (al := ⟨4⟩) rfl (by decide) typedLoadM_tbFive

/-- `atomicFetchAndOp_add_ok` on `tbFive`: `fetch_add(3)` stores `8` and
returns `5`. -/
theorem atomicFetchAndOp_add_instance :
    evalIntrinsicM tbFive (.AtomicFetchAndOp .Add)
        [(.Ptr ⟨tbPtr, none⟩, tyRawPtr), (.Int 3, .Int itU32)] (.Int itU32) =
      .ok (.Int 5, tbMach [tbCell (u32Bytes 8 ++ uninitBytes 4)] [aLoad 4, aStore 4]) :=
  atomicFetchAndOp_add_ok tyRawPtr (al := ⟨4⟩) rfl (by decide) typedLoadM_tbFive (by kernel_rfl)

/-- The atomic `typed_load` of `255u8` on `bmU8Max` through the polymorphic
`typedLoadM` at `M = BasicMemory<x86_64>`. -/
theorem typedLoadM_bmU8Max :
    typedLoadM (M := BM) bmU8Max bmPtr (.Int itU8) ⟨1⟩ .Atomic =
      .ok (.Int 255, bmMach [bmCell (initBytes [255] ++ uninitBytes 7)] [aLoad 1]) := by
  kernel_rfl

/-- `atomicFetchAndOp_add_overflow_specPanic` on `bmU8Max`: the symbolic law
for the missing `bring_in_bounds` applies to `255u8 + 1`, and through
`evalIntrinsicM_bm_eq_atomic` it is the statement about `evalIntrinsic` that
`atomicFetchAndOp_add_u8_overflow_bm` computes. -/
theorem atomicFetchAndOp_add_overflow_instance :
    evalIntrinsicM (M := BM) bmU8Max (.AtomicFetchAndOp .Add)
        [(.Ptr ⟨bmPtr, none⟩, tyRawPtr), (.Int 1, .Int itU8)] (.Int itU8) =
      .error (.specPanic "trying to store a value which is ill-formed for its type") ∧
    evalIntrinsic bmU8Max (.AtomicFetchAndOp .Add)
        [(.Ptr ⟨bmPtr, none⟩, tyRawPtr), (.Int 1, .Int itU8)] (.Int itU8) =
      .error (.specPanic "trying to store a value which is ill-formed for its type") := by
  have h := atomicFetchAndOp_add_overflow_specPanic (M := BM) (o := 1) tyRawPtr (al := ⟨1⟩) rfl
    (by decide) typedLoadM_bmU8Max (by decide)
  exact ⟨h, (evalIntrinsicM_bm_eq_atomic bmU8Max _ _ _ rfl).symm.trans h⟩

/-- The non-atomic `typed_load` of `5u32` on `tbFive`, with the resulting
machine written out. -/
theorem typedLoadM_nonAtomic_tbFive :
    typedLoadM tbFive tbPtr (.Int itU32) ⟨4⟩ .None =
      .ok (.Int 5, tbMach [tbCell (u32Bytes 5 ++ uninitBytes 4)]
        [⟨.Load, .None, cellAddr, ⟨4⟩⟩]) := by
  kernel_rfl

/-- `atomic_atomic_no_data_race` is not vacuous: an `AtomicStore` followed by
an `AtomicLoad` on unsynchronized threads at `cellAddr` passes
`ConcurrentMemory.check_data_races`. -/
theorem atomic_atomic_no_data_race_instance :
    ConcurrentMemory.check_data_races
      (tbMach [tbCell (u32Bytes 5 ++ uninitBytes 4)] [aLoad 4]).mem
      1 (⟨[]⟩, (tbMach [tbCell (u32Bytes 7 ++ uninitBytes 4)] [aStore 4]).mem.accesses) =
      .ok () := by
  have hload : evalIntrinsicM tbFive .AtomicLoad [tbArg tbPtr] (.Int itU32) =
      .ok (.Int 5, tbMach [tbCell (u32Bytes 5 ++ uninitBytes 4)] [aLoad 4]) := by
    kernel_rfl
  exact atomic_atomic_no_data_race (op1 := .AtomicStore) (op2 := .AtomicLoad)
    rfl rfl rfl rfl atomicStore_tb_wfLive_witness.2.1 hload 1 ⟨[]⟩

/-- `atomicStore_nonAtomicLoad_data_race` is not vacuous: an `AtomicStore` and
a non-atomic `typed_load` on unsynchronized threads at `cellAddr` trigger UB
`"Data race"` in both orders. -/
theorem atomicStore_nonAtomicLoad_data_race_instance :
    ConcurrentMemory.check_data_races
      (tbMach [tbCell (u32Bytes 5 ++ uninitBytes 4)] [⟨.Load, .None, cellAddr, ⟨4⟩⟩]).mem
      1 (⟨[]⟩, (tbMach [tbCell (u32Bytes 7 ++ uninitBytes 4)] [aStore 4]).mem.accesses) =
      .error (.ub "Data race") ∧
    ConcurrentMemory.check_data_races
      (tbMach [tbCell (u32Bytes 7 ++ uninitBytes 4)] [aStore 4]).mem
      1 (⟨[]⟩, (tbMach [tbCell (u32Bytes 5 ++ uninitBytes 4)]
        [⟨.Load, .None, cellAddr, ⟨4⟩⟩]).mem.accesses) =
      .error (.ub "Data race") := by
  have hstore : evalIntrinsicM (tbWith []) .AtomicStore
      [(.Ptr ⟨tbPtr, none⟩, tyRawPtr), (.Int 7, .Int itU32)] unitType =
      .ok (unitValueM, tbMach [tbCell (u32Bytes 7 ++ uninitBytes 4)] [aStore 4]) :=
    atomicStore_tb_wfLive_witness.2.1
  have hl2 : Type.layout (.Int itU32) = .ok (.Sized itU32.size ⟨4⟩) := by kernel_rfl
  exact atomicStore_nonAtomicLoad_data_race hstore
    typedLoadM_nonAtomic_tbFive hl2 (by decide) (by decide) rfl

/-- `atomicCompareExchange_failure_nonAtomicLoad_no_data_race` is not vacuous:
a failing `AtomicCompareExchange` and a non-atomic `typed_load` on
unsynchronized threads at `cellAddr` do not race, in either order. -/
theorem atomicCompareExchange_failure_nonAtomicLoad_no_data_race_instance :
    ConcurrentMemory.check_data_races
      (tbMach [tbCell (u32Bytes 5 ++ uninitBytes 4)] [⟨.Load, .None, cellAddr, ⟨4⟩⟩]).mem
      1 (⟨[]⟩, (tbMach [tbCell (u32Bytes 5 ++ uninitBytes 4)] [aLoad 4]).mem.accesses) =
      .ok () ∧
    ConcurrentMemory.check_data_races
      (tbMach [tbCell (u32Bytes 5 ++ uninitBytes 4)] [aLoad 4]).mem
      1 (⟨[]⟩, (tbMach [tbCell (u32Bytes 5 ++ uninitBytes 4)]
        [⟨.Load, .None, cellAddr, ⟨4⟩⟩]).mem.accesses) =
      .ok () :=
  atomicCompareExchange_failure_nonAtomicLoad_no_data_race rfl rfl
    atomicCompareExchange_failure_instance (fun h => absurd (Value.Int.inj h) (by decide))
    typedLoadM_nonAtomic_tbFive 1 ⟨[]⟩

/-- `atomicCompareExchange_success_nonAtomicLoad_data_race` is not vacuous: a
succeeding `AtomicCompareExchange` and a non-atomic `typed_load` on
unsynchronized threads at `cellAddr` trigger UB `"Data race"` in both orders. -/
theorem atomicCompareExchange_success_nonAtomicLoad_data_race_instance :
    ConcurrentMemory.check_data_races
      (tbMach [tbCell (u32Bytes 5 ++ uninitBytes 4)] [⟨.Load, .None, cellAddr, ⟨4⟩⟩]).mem
      1 (⟨[]⟩, (tbMach [tbCell (u32Bytes 9 ++ uninitBytes 4)]
        [aLoad 4, aStore 4]).mem.accesses) =
      .error (.ub "Data race") ∧
    ConcurrentMemory.check_data_races
      (tbMach [tbCell (u32Bytes 9 ++ uninitBytes 4)] [aLoad 4, aStore 4]).mem
      1 (⟨[]⟩, (tbMach [tbCell (u32Bytes 5 ++ uninitBytes 4)]
        [⟨.Load, .None, cellAddr, ⟨4⟩⟩]).mem.accesses) =
      .error (.ub "Data race") := by
  have hl2 : Type.layout (.Int itU32) = .ok (.Sized itU32.size ⟨4⟩) := by kernel_rfl
  exact atomicCompareExchange_success_nonAtomicLoad_data_race
    atomicCompareExchange_success_instance typedLoadM_nonAtomic_tbFive hl2
    (by decide) (by decide) rfl

/-- `atomicFetchAndOp_nonAtomicLoad_data_race` is not vacuous: a successful
`AtomicFetchAndOp` (`fetch_add(3)` on `tbFive`) and a non-atomic `typed_load`
on unsynchronized threads at `cellAddr` trigger UB `"Data race"` in both
orders. -/
theorem atomicFetchAndOp_nonAtomicLoad_data_race_instance :
    ConcurrentMemory.check_data_races
      (tbMach [tbCell (u32Bytes 5 ++ uninitBytes 4)] [⟨.Load, .None, cellAddr, ⟨4⟩⟩]).mem
      1 (⟨[]⟩, (tbMach [tbCell (u32Bytes 8 ++ uninitBytes 4)]
        [aLoad 4, aStore 4]).mem.accesses) =
      .error (.ub "Data race") ∧
    ConcurrentMemory.check_data_races
      (tbMach [tbCell (u32Bytes 8 ++ uninitBytes 4)] [aLoad 4, aStore 4]).mem
      1 (⟨[]⟩, (tbMach [tbCell (u32Bytes 5 ++ uninitBytes 4)]
        [⟨.Load, .None, cellAddr, ⟨4⟩⟩]).mem.accesses) =
      .error (.ub "Data race") := by
  have hl2 : Type.layout (.Int itU32) = .ok (.Sized itU32.size ⟨4⟩) := by kernel_rfl
  exact atomicFetchAndOp_nonAtomicLoad_data_race atomicFetchAndOp_add_instance
    typedLoadM_nonAtomic_tbFive hl2 (by decide) (by decide) rfl

/-- The non-atomic `typed_store` of `7u32` on `tbFive`, with the resulting
machine written out. -/
theorem typedStoreM_nonAtomic_tbFive :
    typedStoreM tbFive tbPtr (.Int 7) (.Int itU32) ⟨4⟩ .None =
      .ok (tbMach [tbCell (u32Bytes 7 ++ uninitBytes 4)]
        [⟨.Store, .None, cellAddr, ⟨4⟩⟩]) := by
  kernel_rfl

/-- `atomicCompareExchange_nonAtomicStore_data_race` is not vacuous: the
*failing* `AtomicCompareExchange` of `atomicCompareExchange_failure_instance`
and a non-atomic `typed_store` on unsynchronized threads at `cellAddr` trigger
UB `"Data race"` in both orders. -/
theorem atomicCompareExchange_nonAtomicStore_data_race_instance :
    ConcurrentMemory.check_data_races
      (tbMach [tbCell (u32Bytes 7 ++ uninitBytes 4)] [⟨.Store, .None, cellAddr, ⟨4⟩⟩]).mem
      1 (⟨[]⟩, (tbMach [tbCell (u32Bytes 5 ++ uninitBytes 4)] [aLoad 4]).mem.accesses) =
      .error (.ub "Data race") ∧
    ConcurrentMemory.check_data_races
      (tbMach [tbCell (u32Bytes 5 ++ uninitBytes 4)] [aLoad 4]).mem
      1 (⟨[]⟩, (tbMach [tbCell (u32Bytes 7 ++ uninitBytes 4)]
        [⟨.Store, .None, cellAddr, ⟨4⟩⟩]).mem.accesses) =
      .error (.ub "Data race") := by
  obtain ⟨bytes, henc, hrace⟩ := atomicCompareExchange_nonAtomicStore_data_race
    atomicCompareExchange_failure_instance typedStoreM_nonAtomic_tbFive
  have hlen : bytes.length = 4 := encodeM_int_length henc
  exact hrace 1 ⟨[]⟩ (by rw [hlen]; decide) (by decide) rfl

/-- `atomicCompareExchange_current_not_int` is not vacuous: on `tbFive`, a
compare-exchange whose `current` is `true` fails silently and returns `5`. -/
theorem atomicCompareExchange_current_not_int_instance :
    evalIntrinsicM tbFive .AtomicCompareExchange
        [(.Ptr ⟨tbPtr, none⟩, tyRawPtr), (.Bool true, .Int itU32), (.Int 9, .Int itU32)]
        (.Int itU32) =
      .ok (.Int 5, tbMach [tbCell (u32Bytes 5 ++ uninitBytes 4)] [aLoad 4]) :=
  atomicCompareExchange_current_not_int tyRawPtr (.Int 9) (al := ⟨4⟩) rfl (by decide)
    typedLoadM_tbFive (fun _ hc => by cases hc)

/-- `atomicCompareExchange_next_out_of_range_specPanic` is not vacuous: on
`tbFive`, a succeeding compare-exchange whose `next` is `2^32` at `u32` is a
specification panic. -/
theorem atomicCompareExchange_next_out_of_range_specPanic_instance :
    evalIntrinsicM tbFive .AtomicCompareExchange
        [(.Ptr ⟨tbPtr, none⟩, tyRawPtr), (.Int 5, .Int itU32), (.Int 4294967296, .Int itU32)]
        (.Int itU32) =
      .error (.specPanic "trying to store a value which is ill-formed for its type") :=
  atomicCompareExchange_next_out_of_range_specPanic tyRawPtr (al := ⟨4⟩) rfl (by decide)
    typedLoadM_tbFive (by decide)

/-- `atomicCompareExchange_failure_memory_bm` is not vacuous: on `bmFive`, the
polymorphic `evalIntrinsicM` at `M = BasicMemory<x86_64>` evaluates a failing
compare-exchange to an explicitly known machine, and that machine has the
memory of `bmFive`. -/
theorem atomicCompareExchange_failure_memory_bm_instance :
    evalIntrinsicM (M := BM) bmFive .AtomicCompareExchange
        [(.Ptr ⟨bmPtr, none⟩, tyRawPtr), (.Int 6, .Int itU32), (.Int 9, .Int itU32)]
        (.Int itU32) =
      .ok (.Int 5, bmMach [bmCell (u32Bytes 5 ++ uninitBytes 4)] [aLoad 4]) ∧
    (bmMach [bmCell (u32Bytes 5 ++ uninitBytes 4)] [aLoad 4]).mem.memory =
      bmFive.mem.memory := by
  have h : evalIntrinsicM (M := BM) bmFive .AtomicCompareExchange
      [(.Ptr ⟨bmPtr, none⟩, tyRawPtr), (.Int 6, .Int itU32), (.Int 9, .Int itU32)]
      (.Int itU32) =
      .ok (.Int 5, bmMach [bmCell (u32Bytes 5 ++ uninitBytes 4)] [aLoad 4]) := by
    kernel_rfl
  exact ⟨h, atomicCompareExchange_failure_memory_bm h
    (fun hc => absurd (Value.Int.inj hc) (by decide))⟩

/-! ### Axiom and import audit -/

section AxiomAudit

open Lean Elab Command

/-! Fail the build unless (1) no `Anneal.*` or `LeanMiriSpec.*` module is
imported, and (2) every declaration of this module (`env.constants.map₂`:
theorems, definitions, instances, and their auxiliary constants) depends only
on Lean's standard axioms `propext`, `Quot.sound`, and `Classical.choice`: no
`sorryAx`, no `Lean.ofReduceBool`, and no `Lean.trustCompiler`. -/

run_cmd do
  let env ← getEnv
  for modName in env.header.moduleNames do
    if (`Anneal).isPrefixOf modName || (`LeanMiriSpec).isPrefixOf modName then
      throwError "import-isolation violation: {modName} must not be imported"
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  for (c, info) in env.constants.map₂.toList do
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      if a == ``sorryAx then throwError "{c} depends on sorryAx"
      if a == ``Lean.ofReduceBool || a == ``Lean.trustCompiler then
        throwError "{c} depends on {a} (compiler-trusting evaluation)"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} depends on non-standard axiom {a}"
    checked := checked + 1
    if (`MiniRustSpec.AtomicIntrinsicsMR).isPrefixOf c then
      if let .thmInfo _ := info then theorems := theorems + 1
  if theorems < 230 then
    throwError "axiom audit is vacuous: only {theorems} theorems of MiniRustSpec.AtomicIntrinsicsMR seen"
  logInfo m!"MiniRustSpec.AtomicIntrinsicsMR: {checked} declarations ({theorems} theorems) depend only on propext, Quot.sound, Classical.choice (sorry_free=true, ofReduceBool_free=true, import_isolated=true)"

end AxiomAudit

end MiniRustSpec.AtomicIntrinsicsMR
