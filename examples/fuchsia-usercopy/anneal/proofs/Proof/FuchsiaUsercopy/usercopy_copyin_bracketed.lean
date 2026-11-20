import Trusted
import Anneal
import Mir.FuchsiaUsercopy.usercopy_copyin_bracketed
import Obligations.FuchsiaUsercopy.usercopy_copyin_bracketed
import Specs.FuchsiaUsercopy.usercopy_copyin_bracketed
import Proof.FuchsiaUsercopy.hermetic_copy_stub

namespace Proof.FuchsiaUsercopy.usercopy_copyin_bracketed

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.PureMirExec
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

/-- Fuel-free modular step that may cross an external call. `h_step` says
that the step from `s` satisfies every continuation that holds of `s'`: the
step meets the call contract, and its only successor (for every call answer
the contract admits) is `s'`. Convergence from `s'` then gives convergence from
`s`. -/
private theorem modularWpConverges_step_to {contract : MirCallContract}
    {body : CapturedMir} {s s' : MachineState} {post : MirOutcome → Prop}
    (h_step : ∀ {cont : MirExecState → Prop}, cont (.running s') →
      evalSymNodeTreeModular contract cont post (stepMirSymTree body s))
    (h_next : MirModularWpConverges contract body s' post) :
    MirModularWpConverges contract body s post :=
  let ⟨n, hn⟩ := h_next
  ⟨n + 1, h_step hn⟩

/-- Machine state on entry to block `bb` after bb0's `StorageLive`s, with `_5`
in slot `s5`. -/
private def entryState (bb in_range dest_len fo v : Nat) (s5 : LocalSlot) :
    MachineState :=
  { frame :=
      { blockIdx := bb, stmtIdx := 0,
        locals :=
          [.uninit, .init (.scalar ⟨in_range, 1⟩), .init (.scalar ⟨dest_len, 8⟩),
           .init (.scalar ⟨fo, 8⟩), .init (.scalar ⟨v, 1⟩), s5,
           .uninit, .uninit, .uninit, .uninit] }
    memory := emptyMemory }

/-- From bb3's entry with a byte count `r ≤ dest_len` in `_5`, bb3 checks
`dest_len - r` for overflow and bb4 returns `(r, dest_len - r)` with memory
untouched; `h_Q` discharges the caller's postcondition for that outcome. -/
private theorem bb3_converges {Q : Value → Memory → Prop}
    {in_range dest_len fo v r : Nat}
    (h_r : r ≤ dest_len) (h_dl : dest_len < 18446744073709551616)
    (h_Q : Q (.aggregate 0 [.scalar ⟨r, 8⟩, .scalar ⟨dest_len - r, 8⟩]) emptyMemory) :
    MirModularWpConverges
      Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaim.callContract
      Mir.FuchsiaUsercopy.usercopy_copyin_bracketed.body
      (entryState 3 in_range dest_len fo v (.init (.scalar ⟨r, 8⟩)))
      (mirSafePost Q) := by
  -- bb3: `_7 = copy _5`, then `_8 = SubWithOverflow(copy _2, copy _7)`, whose
  -- overflow test is the first step that does not reduce on its own.
  repeat refine MirModularWpConverges.step ?_
  -- `r ≤ dest_len` selects the non-overflow arm of the checked subtraction.
  show (match Nat.ble r dest_len with | true => _ | false => _)
  rw [Nat.ble_eq_true_of_le h_r]
  -- bb3: `assert(!move (_8.1)) -> bb4`; bb4: `_6 = move (_8.0); _9 = copy _5;
  -- _0 = (move _9, copy _6)`; the final `return` leaves the step tree at `Q`.
  repeat refine MirModularWpConverges.step ?_
  show Q (.aggregate 0
    [_, .scalar ⟨wrapScalarBits (dest_len - r) 18446744073709551616, 8⟩]) _
  -- `simp only` rewrites the wrapped difference without the `rw` motive's
  -- `isDefEq` walk over the unreduced post-step memory, which times out.
  simp only [wrapScalarBits_eq_of_lt (show dest_len - r < 18446744073709551616 by omega)]
  exact h_Q

theorem verified : ModularVerificationResult Obligations.FuchsiaUsercopy.usercopy_copyin_bracketed.modularClaim := by
  refine verifyModularContractMir_of_wpConverges _ _ _ _ ?_
  rintro _ _ ⟨in_range, dest_len, fo, v, h_ir, h_fo, h_dl, h_v, rfl, rfl⟩
  rcases h_ir with rfl | rfl
  · -- `source_in_restricted_range = false`: bb0 jumps to bb1
    -- (`_5 = const 0_usize; goto -> bb3`).
    refine MirModularWpConverges.bind
      (mid := (· = entryState 3 0 dest_len fo v (.init (.scalar ⟨0, 8⟩))))
      (mirStepsConverges_of_runCfgToBlock _ _ _ rfl 3 _ ⟨rfl, rfl⟩) ?_
    rintro _ rfl
    exact bb3_converges (Nat.zero_le _) h_dl ⟨rfl, by rintro _ _ _ _ ⟨⟩; rfl⟩
  · -- `source_in_restricted_range = true`: bb0 jumps to bb2.
    refine MirModularWpConverges.bind (mid := (· = entryState 2 1 dest_len fo v .uninit))
      (mirStepsConverges_of_runCfgToBlock _ _ _ rfl 2 _ ⟨rfl, rfl⟩) ?_
    rintro _ rfl
    -- bb2: `_5 = hermetic_copy_stub(copy _2, copy _3, copy _4) -> [return: bb3]`.
    -- The call meets the stub's contract, and every answer the contract admits
    -- returns `fault_offset` with memory untouched.
    refine modularWpConverges_step_to
      (s' := entryState 3 1 dest_len fo v (.init (.scalar ⟨fo, 8⟩)))
      (fun hc => ⟨⟨rfl, dest_len, fo, v, h_fo, h_dl, h_v, rfl, rfl⟩, ?_⟩)
      (bb3_converges h_fo h_dl ⟨rfl, by rintro _ _ _ _ ⟨⟩; rfl⟩)
    rintro _ ⟨_, _, rfl, rfl, h_ret⟩
    obtain ⟨rfl, -⟩ := h_ret dest_len fo v rfl
    exact hc

/-- Model witness for `hermetic_copy_stub` returning `fault_offset`. -/
def hermeticCopyStubModel (args : List Value) (mem : Memory) : Value × Memory :=
  match args with
  | [ _, .scalar { bits := fo, .. }, _ ] =>
    (.scalar { bits := fo, sizeBytes := 8 }, mem)
  | _ => (.scalar { bits := 0, sizeBytes := 8 }, mem)

/-- End-to-end horizontal linking theorem combining the modular proof of
    `usercopy_copyin_bracketed` with the scoped UB-exception proof of
    `hermetic_copy_stub`. -/
theorem linked_with_ub_exception (fallback : ExternalCallHandler) :
    ((fun args mem =>
      (mirHandledTree
        Mir.FuchsiaUsercopy.usercopy_copyin_bracketed.body
        args mem
        (ubExceptionModelHandler
          Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaim
          hermeticCopyStubModel
          fallback)).toPartial) ≤
      MirClosedStatefulContractSpec
        Specs.FuchsiaUsercopy.usercopy_copyin_bracketed.pre
        Specs.FuchsiaUsercopy.usercopy_copyin_bracketed.pre
        Specs.FuchsiaUsercopy.usercopy_copyin_bracketed.post) ∧
    MirStatefulContractHoldsWithSafety
      Mir.FuchsiaUsercopy.hermetic_copy_stub.body
      (fun args mem =>
        Specs.FuchsiaUsercopy.hermetic_copy_stub.pre args mem ∧
        Specs.FuchsiaUsercopy.hermetic_copy_stub.strictSafetyPre args mem)
      Specs.FuchsiaUsercopy.hermetic_copy_stub.pre
      Specs.FuchsiaUsercopy.hermetic_copy_stub.post := by
  refine linkUbExceptionCallee
    verified
    Proof.FuchsiaUsercopy.hermetic_copy_stub.verified
    hermeticCopyStubModel
    fallback
    ?_
  rintro _ _ ⟨count, fo, v, h_fo, -, -, rfl, rfl⟩ -
  exact ⟨rfl, by rintro _ _ _ ⟨⟩; exact ⟨rfl, h_fo⟩⟩

/-! ## Slice-lens companions of `verified`

`Usercopy::copyin` (`src/starnix/lib/usercopy/src/lib.rs:486-513`) copies into a
`&mut [MaybeUninit<u8>]` destination through the faulting `hermetic_copy` routine and then
hands the destination to `assume_initialized_until`, which `split_at_mut`s it at the byte
count actually read. The theorems below read the result `(read_count, uninit_len)` of an
actual normal return off `verified` (for every environment implementing
`hermetic_copy_stub`'s contract, and for the closed program linked with the verified stub
model) and show that it is exactly an `ActiveTypedSliceMutBorrow.splitAt` of any live
`&mut` lens on the destination: the initialized prefix lens has `read_count` elements
(none when the source is outside the restricted range), the uninitialized suffix lens has
`uninit_len`, both stay under the destination's tag with adjacent disjoint byte windows,
and they recombine into the destination lens. -/

section SliceLensCompanions

open Trusted.ITree
open Anneal.SepLogicLenses

/-- **Copy-in result as a `split_at_mut` of the destination.** If `(ret, mem')` satisfies
the verified `post` on arguments with `fault_offset ≤ dest_len`, then for every live lens
`ActiveTypedSliceMutBorrow c borrows tag dest xs bytes` on a `dest_len`-element destination,
memory is untouched and `ret = (read_count, uninit_len)` splits the lens into the
`read_count`-element initialized prefix and the `uninit_len`-element suffix (same tag),
whose byte windows are adjacent and disjoint and which reassemble into the parent lens;
`read_count = 0` when the source is outside the restricted range. -/
theorem copyin_split_of_post {in_range dest_len fo v : Nat} (h_fo : fo ≤ dest_len)
    {mem : Memory} {ret : Value} {mem' : Memory}
    (h_post : Specs.FuchsiaUsercopy.usercopy_copyin_bracketed.post
      [.scalar ⟨in_range, 1⟩, .scalar ⟨dest_len, 8⟩, .scalar ⟨fo, 8⟩, .scalar ⟨v, 1⟩]
      mem ret mem')
    {α : Type} {n : Nat} {c : ByteLensCodec α n} {borrows : List BorrowEntry} {tag : Nat}
    {dest : WidePtrVal} {xs : List α} {bytes : ByteMem}
    (h_dest : ActiveTypedSliceMutBorrow c borrows tag dest xs bytes) (h_len : dest.2 = dest_len) :
    mem' = mem ∧
      ∃ read_count uninit_len : Nat,
        ret = .aggregate 0 [.scalar ⟨read_count, 8⟩, .scalar ⟨uninit_len, 8⟩] ∧
        (in_range ≠ 1 → read_count = 0) ∧
        read_count + uninit_len = dest.2 ∧
        ActiveTypedSliceMutBorrow c borrows tag (WidePtrVal.takeElems dest read_count)
          (xs.take read_count) bytes ∧
        ActiveTypedSliceMutBorrow c borrows tag (WidePtrVal.dropElems dest n read_count)
          (xs.drop read_count) bytes ∧
        DisjointSlice dest.1.offsetBytes (read_count * n)
          (dest.1.offsetBytes + read_count * n) (uninit_len * n) ∧
        ActiveTypedSliceMutBorrow c borrows tag dest (xs.take read_count ++ xs.drop read_count)
          bytes := by
  obtain ⟨h_mem, h_ret⟩ := h_post
  refine ⟨h_mem, ?_⟩
  -- The byte count read is `fault_offset` (restricted source) or `0`.
  obtain ⟨r, h_r, h_r0, h_ret'⟩ : ∃ r, r ≤ dest_len ∧ (in_range ≠ 1 → r = 0) ∧
      ret = .aggregate 0 [.scalar ⟨r, 8⟩, .scalar ⟨dest_len - r, 8⟩] := by
    have h := h_ret in_range dest_len fo v rfl
    by_cases h1 : in_range = 1
    · rw [ite_eq_left h1] at h
      exact ⟨fo, h_fo, fun h1' => absurd h1 h1', h⟩
    · rw [ite_eq_right h1] at h
      exact ⟨0, Nat.zero_le _, fun _ => rfl, by rw [Nat.sub_zero]; exact h⟩
  have hk : r ≤ dest.2 := by omega
  obtain ⟨hL, hR, hD⟩ := ActiveTypedSliceMutBorrow.splitAt h_dest hk
  obtain ⟨-, entry, he, hc, -⟩ := h_dest
  refine ⟨r, dest_len - r, h_ret', h_r0, by omega, hL, hR, ?_,
    ActiveTypedSliceMutBorrow.of_splitAt hk hL hR ⟨entry, he, hc⟩⟩
  rw [h_len] at hD
  exact hD

/-- Under every external-call environment `h` implementing `hermetic_copy_stub`'s
contract, every normal return of the captured `copyin` MIR satisfies `post` (read off the
modular `verified`). -/
theorem post_of_handledRun {h : ExternalCallHandler}
    (h_env : Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaim.callContract.holdsOn h)
    {args : List Value} {mem : Memory}
    (h_pre : Specs.FuchsiaUsercopy.usercopy_copyin_bracketed.pre args mem)
    {tr ret mem'}
    (h_run : ReachesRet (mirHandledTree Mir.FuchsiaUsercopy.usercopy_copyin_bracketed.body
      args mem h) tr (.normal (ret, mem'))) :
    Specs.FuchsiaUsercopy.usercopy_copyin_bracketed.post args mem ret mem' := by
  obtain ⟨_, h_spec⟩ := verified.proof h h_env args mem h_pre
  exact h_spec (tr, .normal (ret, mem')) h_run h_pre ret mem' rfl

/-- **Modular companion.** For every environment implementing `hermetic_copy_stub`'s
contract, every normal return of `copyin` on `pre`-admissible arguments splits every live
`&mut` lens on the `dest_len`-element destination as in `copyin_split_of_post`. -/
theorem copyin_split_of_handledRun {h : ExternalCallHandler}
    (h_env : Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaim.callContract.holdsOn h)
    {in_range dest_len fo v : Nat} (h_ir : in_range = 0 ∨ in_range = 1) (h_fo : fo ≤ dest_len)
    (h_dl : dest_len < 18446744073709551616) (h_v : v = 0 ∨ v = 1)
    {tr ret mem'}
    (h_run : ReachesRet
      (mirHandledTree Mir.FuchsiaUsercopy.usercopy_copyin_bracketed.body
        [.scalar ⟨in_range, 1⟩, .scalar ⟨dest_len, 8⟩, .scalar ⟨fo, 8⟩, .scalar ⟨v, 1⟩]
        emptyMemory h)
      tr (.normal (ret, mem')))
    {α : Type} {n : Nat} {c : ByteLensCodec α n} {borrows : List BorrowEntry} {tag : Nat}
    {dest : WidePtrVal} {xs : List α} {bytes : ByteMem}
    (h_dest : ActiveTypedSliceMutBorrow c borrows tag dest xs bytes) (h_len : dest.2 = dest_len) :
    mem' = emptyMemory ∧
      ∃ read_count uninit_len : Nat,
        ret = .aggregate 0 [.scalar ⟨read_count, 8⟩, .scalar ⟨uninit_len, 8⟩] ∧
        (in_range ≠ 1 → read_count = 0) ∧
        read_count + uninit_len = dest.2 ∧
        ActiveTypedSliceMutBorrow c borrows tag (WidePtrVal.takeElems dest read_count)
          (xs.take read_count) bytes ∧
        ActiveTypedSliceMutBorrow c borrows tag (WidePtrVal.dropElems dest n read_count)
          (xs.drop read_count) bytes ∧
        DisjointSlice dest.1.offsetBytes (read_count * n)
          (dest.1.offsetBytes + read_count * n) (uninit_len * n) ∧
        ActiveTypedSliceMutBorrow c borrows tag dest (xs.take read_count ++ xs.drop read_count)
          bytes :=
  copyin_split_of_post h_fo
    (post_of_handledRun h_env ⟨in_range, dest_len, fo, v, h_ir, h_fo, h_dl, h_v, rfl, rfl⟩ h_run)
    h_dest h_len

/-- **Closed-world companion.** Linked with the verified UB-exception stub model
(`linked_with_ub_exception`), every normal return of the closed `copyin` program splits
every live `&mut` lens on the destination at the byte count read. -/
theorem copyin_split_linked (fallback : ExternalCallHandler)
    {in_range dest_len fo v : Nat} (h_ir : in_range = 0 ∨ in_range = 1) (h_fo : fo ≤ dest_len)
    (h_dl : dest_len < 18446744073709551616) (h_v : v = 0 ∨ v = 1)
    {tr ret mem'}
    (h_run : ReachesRet
      (mirHandledTree Mir.FuchsiaUsercopy.usercopy_copyin_bracketed.body
        [.scalar ⟨in_range, 1⟩, .scalar ⟨dest_len, 8⟩, .scalar ⟨fo, 8⟩, .scalar ⟨v, 1⟩]
        emptyMemory
        (ubExceptionModelHandler Obligations.FuchsiaUsercopy.hermetic_copy_stub.ubExceptionClaim
          hermeticCopyStubModel fallback))
      tr (.normal (ret, mem')))
    {α : Type} {n : Nat} {c : ByteLensCodec α n} {borrows : List BorrowEntry} {tag : Nat}
    {dest : WidePtrVal} {xs : List α} {bytes : ByteMem}
    (h_dest : ActiveTypedSliceMutBorrow c borrows tag dest xs bytes) (h_len : dest.2 = dest_len) :
    ∃ read_count uninit_len : Nat,
      ret = .aggregate 0 [.scalar ⟨read_count, 8⟩, .scalar ⟨uninit_len, 8⟩] ∧
      ActiveTypedSliceMutBorrow c borrows tag (WidePtrVal.takeElems dest read_count)
        (xs.take read_count) bytes ∧
      ActiveTypedSliceMutBorrow c borrows tag (WidePtrVal.dropElems dest n read_count)
        (xs.drop read_count) bytes ∧
      DisjointSlice dest.1.offsetBytes (read_count * n)
        (dest.1.offsetBytes + read_count * n) (uninit_len * n) := by
  have h_pre : Specs.FuchsiaUsercopy.usercopy_copyin_bracketed.pre
      [.scalar ⟨in_range, 1⟩, .scalar ⟨dest_len, 8⟩, .scalar ⟨fo, 8⟩, .scalar ⟨v, 1⟩]
      emptyMemory :=
    ⟨in_range, dest_len, fo, v, h_ir, h_fo, h_dl, h_v, rfl, rfl⟩
  obtain ⟨_, h_spec⟩ := (linked_with_ub_exception fallback).1 _ _ h_pre
  obtain ⟨-, r, u, h_ret, -, -, hL, hR, hD, -⟩ :=
    copyin_split_of_post h_fo (h_spec (tr, .normal (ret, mem')) h_run h_pre ret mem' rfl)
      h_dest h_len
  exact ⟨r, u, h_ret, hL, hR, hD⟩

/-! ### Concrete instance: a faulting copy-in into a 5-byte destination -/

/-- The 5-byte destination image `[10, 20, 30, 0, 0]` (allocation `7`). -/
def copyinDestBytes : ByteMem := ByteLensCodec.encodeElems ByteLensCodec.u8 [10, 20, 30, 0, 0]

/-- A `.unique` byte-ranged borrow (tag `77`) covering the 5-byte destination. -/
def copyinDestBorrows : List BorrowEntry :=
  [{ tag := 77, targetLocal := 0, targetProjection := [], perm := .unique, rangeOffset := 0,
     rangeLen := 5 }]

/-- The live `&mut [u8]` lens on the destination. -/
theorem copyin_dest_lens :
    ActiveTypedSliceMutBorrow ByteLensCodec.u8 copyinDestBorrows 77 (WidePtrVal.mk ⟨7, 0⟩ 5)
      [10, 20, 30, 0, 0] copyinDestBytes :=
  ⟨sliceTypedAt_encodeElems ByteLensCodec.u8 7 [10, 20, 30, 0, 0], _, rfl,
    ⟨Nat.le_refl 0, Nat.le_refl 5⟩, TreeBorrowPerm.permitsUniqueWrite_unique⟩

/-- A restricted-range copy-in of `dest_len = 5` faulting after `3` bytes returns `(3, 2)`,
which `post` admits; the split is then the `&mut` lens on the 3 bytes read (`[10, 20, 30]`
at byte `0`) and the `&mut` lens on the 2 unread bytes (`[0, 0]` at byte `3`). -/
theorem copyin_demo_split :
    ActiveTypedSliceMutBorrow ByteLensCodec.u8 copyinDestBorrows 77 (WidePtrVal.mk ⟨7, 0⟩ 3)
        [10, 20, 30] copyinDestBytes ∧
      ActiveTypedSliceMutBorrow ByteLensCodec.u8 copyinDestBorrows 77 (WidePtrVal.mk ⟨7, 3⟩ 2)
        [0, 0] copyinDestBytes ∧
      DisjointSlice 0 3 3 2 := by
  have h_post : Specs.FuchsiaUsercopy.usercopy_copyin_bracketed.post
      [.scalar ⟨1, 1⟩, .scalar ⟨5, 8⟩, .scalar ⟨3, 8⟩, .scalar ⟨1, 1⟩] emptyMemory
      (.aggregate 0 [.scalar ⟨3, 8⟩, .scalar ⟨2, 8⟩]) emptyMemory := by
    refine ⟨rfl, fun a b c d h => ?_⟩
    simp only [List.cons.injEq, Value.scalar.injEq,
      Trusted.Rustc.V2026_06_01.MirAst.ScalarInt.mk.injEq, and_true] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    rfl
  obtain ⟨-, r, u, h_ret, -, -, hL, hR, hD, -⟩ :=
    copyin_split_of_post (by decide) h_post copyin_dest_lens rfl
  simp only [Value.aggregate.injEq, List.cons.injEq, Value.scalar.injEq,
    Trusted.Rustc.V2026_06_01.MirAst.ScalarInt.mk.injEq, and_true, true_and] at h_ret
  obtain ⟨rfl, rfl⟩ := h_ret
  exact ⟨hL, hR, hD⟩

end SliceLensCompanions

end Proof.FuchsiaUsercopy.usercopy_copyin_bracketed
