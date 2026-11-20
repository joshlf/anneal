import Trusted
import Anneal
import Mir.FuchsiaUsercopy.assume_initialized_until_split_len
import Obligations.FuchsiaUsercopy.assume_initialized_until_split_len
import Specs.FuchsiaUsercopy.assume_initialized_until_split_len

namespace Proof.FuchsiaUsercopy.assume_initialized_until_split_len

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Anneal.Rustc.V2026_06_01.SymbolicEval

theorem verified : StatefulVerificationResult Obligations.FuchsiaUsercopy.assume_initialized_until_split_len.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl
    (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨buf_len, init_until, h_le, h_lt, rfl⟩, rfl⟩
  apply lift_PureMirConverges rfl
  -- bb0: `StorageLive(_3); StorageLive(_4);
  --   _4 = SubWithOverflow(copy _1, copy _2); assert(!_4.1) -> bb1`
  apply LiftBlock.of_lookup rfl
  repeat apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue
      (val := .aggregate 0 [.scalar ⟨buf_len - init_until, 8⟩, .scalar ⟨0, 1⟩])
      rfl ?h_rv rfl (by nofun) rfl)
  case h_rv =>
    -- `init_until ≤ buf_len`, so the checked subtraction takes its
    -- non-overflow arm.
    change (match Nat.ble init_until buf_len with | true => _ | false => _) = _
    rw [Nat.ble_eq_true_of_le h_le]
    show RvalueEvalResult.ok (.aggregate 0
      [.scalar ⟨wrapScalarBits (buf_len - init_until) 18446744073709551616, 8⟩,
       .scalar ⟨0, 1⟩]) _ _ = _
    rw [wrapScalarBits_eq_of_lt (by omega)]
  apply LiftStmtsTerminator.term_assert (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
  -- bb1: `_3 = move (_4.0); _0 = (copy _2, copy _3); return`
  apply LiftBlock.of_lookup rfl
  apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
  apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  rintro _ _ ⟨⟩
  exact ⟨rfl, by omega⟩

/-! ## Slice-lens companions of `verified`

`assume_initialized_until` (`src/starnix/lib/usercopy/src/lib.rs:224-237`) splits a
`&mut [MaybeUninit<u8>]` buffer of `buf_len` elements with `split_at_mut` at
`initialized_until`. The theorems below take an actual normal return of the captured
MIR (`ReachesRet` of the trusted `mirStatefulTreeWithCallees`), read its result off
`verified`, and show that the returned `(init_len, uninit_len)` is exactly a
`SliceTypedAt.splitAt` / `ActiveTypedSliceMutBorrow.splitAt` decomposition of *any*
typed view of the buffer: the prefix and suffix views have exactly `init_len` and
`uninit_len` elements, their byte windows are adjacent and disjoint, and they
reassemble (`of_splitAt`) into the parent view. -/

section SliceLensCompanions

open Trusted.ITree
open Anneal.SepLogicLenses

/-- Every normal return of the captured MIR on `pre`-admissible arguments returns
`(initialized_until, buf_len - initialized_until)`, read off `verified`. -/
theorem ret_of_run {buf_len init_until : Nat}
    (h_le : init_until ≤ buf_len) (h_lt : buf_len < 18446744073709551616)
    {tr ret mem'}
    (h_run : ReachesRet
      (mirStatefulTreeWithCallees Mir.FuchsiaUsercopy.assume_initialized_until_split_len.body
        [.scalar ⟨buf_len, 8⟩, .scalar ⟨init_until, 8⟩] emptyMemory)
      tr (.normal (ret, mem'))) :
    ret = .aggregate 0 [.scalar ⟨init_until, 8⟩, .scalar ⟨buf_len - init_until, 8⟩] := by
  have h_pre : Specs.FuchsiaUsercopy.assume_initialized_until_split_len.pre
      [.scalar ⟨buf_len, 8⟩, .scalar ⟨init_until, 8⟩] :=
    ⟨buf_len, init_until, h_le, h_lt, rfl⟩
  obtain ⟨_, h_spec⟩ := verified.proof _ emptyMemory ⟨h_pre, rfl⟩
  exact (h_spec (tr, .normal (ret, mem')) h_run ⟨h_pre, rfl⟩ ret mem' rfl
    buf_len init_until rfl).1

/-- **`split_at_mut` view of the verified split.** For every codec `c` and every typed
view `SliceTypedAt c wide xs bytes` of a buffer with `wide.2 = buf_len` elements, the
result `(init_len, uninit_len)` of any normal return splits the view into the prefix
`takeElems wide init_len` (`xs.take init_len`) and the suffix `dropElems wide n init_len`
(`xs.drop init_len`, exactly `uninit_len` elements), whose byte windows are adjacent and
disjoint, and which reassemble into the parent view. -/
theorem split_sliceTypedAt_of_run {buf_len init_until : Nat}
    (h_le : init_until ≤ buf_len) (h_lt : buf_len < 18446744073709551616)
    {tr ret mem'}
    (h_run : ReachesRet
      (mirStatefulTreeWithCallees Mir.FuchsiaUsercopy.assume_initialized_until_split_len.body
        [.scalar ⟨buf_len, 8⟩, .scalar ⟨init_until, 8⟩] emptyMemory)
      tr (.normal (ret, mem')))
    {α : Type} {n : Nat} {c : ByteLensCodec α n} {wide : WidePtrVal} {xs : List α}
    {bytes : ByteMem} (h_buf : SliceTypedAt c wide xs bytes) (h_len : wide.2 = buf_len) :
    ∃ init_len uninit_len : Nat,
      ret = .aggregate 0 [.scalar ⟨init_len, 8⟩, .scalar ⟨uninit_len, 8⟩] ∧
      init_len + uninit_len = wide.2 ∧
      SliceTypedAt c (WidePtrVal.takeElems wide init_len) (xs.take init_len) bytes ∧
      SliceTypedAt c (WidePtrVal.dropElems wide n init_len) (xs.drop init_len) bytes ∧
      (WidePtrVal.dropElems wide n init_len).2 = uninit_len ∧
      DisjointSlice wide.1.offsetBytes (init_len * n)
        (wide.1.offsetBytes + init_len * n) (uninit_len * n) ∧
      SliceTypedAt c wide (xs.take init_len ++ xs.drop init_len) bytes := by
  have hk : init_until ≤ wide.2 := by omega
  obtain ⟨hL, hR, hD⟩ := SliceTypedAt.splitAt h_buf hk
  refine ⟨init_until, buf_len - init_until, ret_of_run h_le h_lt h_run, by omega, hL, hR,
    by rw [WidePtrVal.dropElems_snd, h_len], ?_, SliceTypedAt.of_splitAt hk hL hR⟩
  rw [h_len] at hD
  exact hD

/-- **Borrow-checked `split_at_mut`.** For a live `&mut [T]` lens
(`ActiveTypedSliceMutBorrow`) on the buffer, the verified split yields two `&mut` lenses
under the same tag on the `init_len`-element prefix and the `uninit_len`-element suffix,
with adjacent disjoint windows, which recombine into the parent lens when the halves'
borrows end. -/
theorem split_mutBorrow_of_run {buf_len init_until : Nat}
    (h_le : init_until ≤ buf_len) (h_lt : buf_len < 18446744073709551616)
    {tr ret mem'}
    (h_run : ReachesRet
      (mirStatefulTreeWithCallees Mir.FuchsiaUsercopy.assume_initialized_until_split_len.body
        [.scalar ⟨buf_len, 8⟩, .scalar ⟨init_until, 8⟩] emptyMemory)
      tr (.normal (ret, mem')))
    {α : Type} {n : Nat} {c : ByteLensCodec α n} {borrows : List BorrowEntry} {tag : Nat}
    {wide : WidePtrVal} {xs : List α} {bytes : ByteMem}
    (h_buf : ActiveTypedSliceMutBorrow c borrows tag wide xs bytes) (h_len : wide.2 = buf_len) :
    ∃ init_len uninit_len : Nat,
      ret = .aggregate 0 [.scalar ⟨init_len, 8⟩, .scalar ⟨uninit_len, 8⟩] ∧
      ActiveTypedSliceMutBorrow c borrows tag (WidePtrVal.takeElems wide init_len)
        (xs.take init_len) bytes ∧
      ActiveTypedSliceMutBorrow c borrows tag (WidePtrVal.dropElems wide n init_len)
        (xs.drop init_len) bytes ∧
      (WidePtrVal.dropElems wide n init_len).2 = uninit_len ∧
      DisjointSlice wide.1.offsetBytes (init_len * n)
        (wide.1.offsetBytes + init_len * n) (uninit_len * n) ∧
      ActiveTypedSliceMutBorrow c borrows tag wide (xs.take init_len ++ xs.drop init_len) bytes := by
  have hk : init_until ≤ wide.2 := by omega
  obtain ⟨hL, hR, hD⟩ := ActiveTypedSliceMutBorrow.splitAt h_buf hk
  obtain ⟨-, entry, he, hc, -⟩ := h_buf
  refine ⟨init_until, buf_len - init_until, ret_of_run h_le h_lt h_run, hL, hR,
    by rw [WidePtrVal.dropElems_snd, h_len], ?_,
    ActiveTypedSliceMutBorrow.of_splitAt hk hL hR ⟨entry, he, hc⟩⟩
  rw [h_len] at hD
  exact hD

/-! ### Concrete instance: a real captured-MIR run on a 5-byte buffer -/

/-- The trusted MIR of `assume_initialized_until_split_len(5, 3)` reaches a normal
return of `(3, 2)` (replayed by the kernel-checked `TraceCheck` trace reconstructor). -/
theorem run_5_3 : ∃ tr mem', ReachesRet
    (mirStatefulTreeWithCallees Mir.FuchsiaUsercopy.assume_initialized_until_split_len.body
      [.scalar ⟨5, 8⟩, .scalar ⟨3, 8⟩] emptyMemory)
    tr (.normal (.aggregate 0 [.scalar ⟨3, 8⟩, .scalar ⟨2, 8⟩], mem')) := by
  obtain ⟨tr, out, -, h_out, h_reach⟩ :=
    Anneal.Rustc.V2026_06_01.TraceCheck.checkFullObservedTraceBounded_sound 16
      Mir.FuchsiaUsercopy.assume_initialized_until_split_len.body
      (initMachineStateWithMemoryAndCallees
        Mir.FuchsiaUsercopy.assume_initialized_until_split_len.body
        [.scalar ⟨5, 8⟩, .scalar ⟨3, 8⟩] emptyMemory [])
      [] (.normal (.aggregate 0 [.scalar ⟨3, 8⟩, .scalar ⟨2, 8⟩])) (by decide)
  rcases out with ⟨rv, m⟩ | _ | _
  · exact ⟨tr, m, h_out ▸ h_reach⟩
  · exact (h_out : False).elim
  · exact (h_out : False).elim

/-- The `[MaybeUninit<u8>; 5]` destination image `[10, 20, 30, 0, 0]` (allocation `7`). -/
def demoBytes : ByteMem := ByteLensCodec.encodeElems ByteLensCodec.u8 [10, 20, 30, 0, 0]

/-- The `u8` view of `demoBytes` through the 5-element wide pointer at `⟨7, 0⟩`. -/
theorem demo_view :
    SliceTypedAt ByteLensCodec.u8 (WidePtrVal.mk ⟨7, 0⟩ 5) [10, 20, 30, 0, 0] demoBytes :=
  sliceTypedAt_encodeElems ByteLensCodec.u8 7 [10, 20, 30, 0, 0]

/-- On the concrete run, the verified split of `demoBytes` is the initialized prefix
`[10, 20, 30]` (bytes `[0, 3)`) and the 2-element suffix `[0, 0]` starting at byte `3`. -/
theorem demo_split :
    SliceTypedAt ByteLensCodec.u8 (WidePtrVal.mk ⟨7, 0⟩ 3) [10, 20, 30] demoBytes ∧
      SliceTypedAt ByteLensCodec.u8 (WidePtrVal.mk ⟨7, 3⟩ 2) [0, 0] demoBytes ∧
      DisjointSlice 0 3 3 2 := by
  obtain ⟨tr, mem', h_run⟩ := run_5_3
  obtain ⟨init_len, uninit_len, h_ret, -, hL, hR, -, hD, -⟩ :=
    split_sliceTypedAt_of_run (by decide) (by decide) h_run demo_view rfl
  simp only [Value.aggregate.injEq, List.cons.injEq, Value.scalar.injEq,
    Trusted.Rustc.V2026_06_01.MirAst.ScalarInt.mk.injEq, and_true, true_and] at h_ret
  obtain ⟨rfl, rfl⟩ := h_ret
  exact ⟨hL, hR, hD⟩

end SliceLensCompanions

end Proof.FuchsiaUsercopy.assume_initialized_until_split_len
