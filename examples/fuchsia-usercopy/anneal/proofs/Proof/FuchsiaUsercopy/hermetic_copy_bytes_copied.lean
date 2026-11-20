import Trusted
import Anneal
import Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied
import Obligations.FuchsiaUsercopy.hermetic_copy_bytes_copied
import Specs.FuchsiaUsercopy.hermetic_copy_bytes_copied

namespace Proof.FuchsiaUsercopy.hermetic_copy_bytes_copied

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Anneal.Rustc.V2026_06_01.SymbolicEval

theorem verified : StatefulVerificationResult Obligations.FuchsiaUsercopy.hermetic_copy_bytes_copied.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl
    (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨base, count, unread, h_bu, h_uc, h_lt, -, rfl⟩, rfl⟩
  apply lift_PureMirConverges rfl
  -- bb0: `StorageLive(_4); _4 = SubWithOverflow(copy _3, copy _1); assert(!_4.1) -> bb1`
  apply LiftBlock.of_lookup rfl
  repeat apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue
      (val := .aggregate 0 [.scalar ⟨unread - base, 8⟩, .scalar ⟨0, 1⟩])
      rfl ?h_rv rfl (by nofun) rfl)
  case h_rv =>
    -- `base ≤ unread`, so the checked subtraction takes its non-overflow arm.
    change (match Nat.ble base unread with | true => _ | false => _) = _
    rw [Nat.ble_eq_true_of_le h_bu]
    show RvalueEvalResult.ok (.aggregate 0
      [.scalar ⟨wrapScalarBits (unread - base) 18446744073709551616, 8⟩,
       .scalar ⟨0, 1⟩]) _ _ = _
    rw [wrapScalarBits_eq_of_lt (by omega)]
  apply LiftStmtsTerminator.term_assert (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
  -- bb1: `_0 = move (_4.0); return`
  apply LiftBlock.of_lookup rfl
  apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
  apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  rintro _ _ _ ⟨⟩
  exact ⟨rfl, h_uc⟩

/-! ## Slice-lens companions of `verified`

`do_hermetic_copy` (`src/starnix/lib/usercopy/src/lib.rs:247-278`) copies `count` bytes to
or from the user buffer at `dest_or_src_base`; the assembly routine returns the first
unread address, and `hermetic_copy_bytes_copied` turns it into the byte count copied. The
theorems below read that count off an actual normal return of the captured MIR (via
`verified`) and connect it to the wide-pointer slice lenses of `Anneal.SepLogicLenses` over
any typed byte view of the user buffer: the copied bytes are exactly the prefix
`takeElems user copied`, the returned `unread_address` is exactly the data pointer of the
uncopied suffix `dropElems user 1 copied` (holding `count - copied` bytes), the two windows
are adjacent and disjoint, and they reassemble into the user buffer view. -/

section SliceLensCompanions

open Trusted.ITree
open Anneal.SepLogicLenses

/-- Every normal return of the captured MIR on `pre`-admissible arguments returns
`unread_address - dest_or_src_base`, read off `verified`. -/
theorem ret_of_run {base count unread : Nat} (h_bu : base ≤ unread)
    (h_uc : unread - base ≤ count) (h_lt : unread < 18446744073709551616)
    (h_count : count < 18446744073709551616) {tr ret mem'}
    (h_run : ReachesRet
      (mirStatefulTreeWithCallees Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body
        [.scalar ⟨base, 8⟩, .scalar ⟨count, 8⟩, .scalar ⟨unread, 8⟩] emptyMemory)
      tr (.normal (ret, mem'))) :
    ret = .scalar ⟨unread - base, 8⟩ := by
  have h_pre : Specs.FuchsiaUsercopy.hermetic_copy_bytes_copied.pre
      [.scalar ⟨base, 8⟩, .scalar ⟨count, 8⟩, .scalar ⟨unread, 8⟩] :=
    ⟨base, count, unread, h_bu, h_uc, h_lt, h_count, rfl⟩
  obtain ⟨_, h_spec⟩ := verified.proof _ emptyMemory ⟨h_pre, rfl⟩
  exact (h_spec (tr, .normal (ret, mem')) h_run ⟨h_pre, rfl⟩ ret mem' rfl
    base count unread rfl).1

/-- **Copied prefix / unread suffix of the user buffer.** For every 1-byte codec `c` and
every typed view `SliceTypedAt c user xs bytes` of the `count`-byte user buffer at
`dest_or_src_base` (`user.1.offsetBytes = base`, `user.2 = count`), any normal return yields
`copied` such that the copied bytes are the prefix view `takeElems user copied`
(`xs.take copied`), the uncopied suffix `dropElems user 1 copied` (`xs.drop copied`, exactly
`count - copied` bytes) starts exactly at `unread_address`, the windows are adjacent and
disjoint, and they reassemble into the user buffer view. -/
theorem copied_prefix_of_run {base count unread : Nat} (h_bu : base ≤ unread)
    (h_uc : unread - base ≤ count) (h_lt : unread < 18446744073709551616)
    (h_count : count < 18446744073709551616) {tr ret mem'}
    (h_run : ReachesRet
      (mirStatefulTreeWithCallees Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body
        [.scalar ⟨base, 8⟩, .scalar ⟨count, 8⟩, .scalar ⟨unread, 8⟩] emptyMemory)
      tr (.normal (ret, mem')))
    {α : Type} {c : ByteLensCodec α 1} {user : WidePtrVal} {xs : List α} {bytes : ByteMem}
    (h_user : SliceTypedAt c user xs bytes) (h_base : user.1.offsetBytes = base)
    (h_len : user.2 = count) :
    ∃ copied : Nat,
      ret = .scalar ⟨copied, 8⟩ ∧
      SliceTypedAt c (WidePtrVal.takeElems user copied) (xs.take copied) bytes ∧
      SliceTypedAt c (WidePtrVal.dropElems user 1 copied) (xs.drop copied) bytes ∧
      (WidePtrVal.dropElems user 1 copied).1.offsetBytes = unread ∧
      (WidePtrVal.dropElems user 1 copied).2 = count - copied ∧
      DisjointSlice user.1.offsetBytes (copied * 1)
        (user.1.offsetBytes + copied * 1) ((user.2 - copied) * 1) ∧
      SliceTypedAt c user (xs.take copied ++ xs.drop copied) bytes := by
  have hk : unread - base ≤ user.2 := by omega
  obtain ⟨hL, hR, hD⟩ := SliceTypedAt.splitAt h_user hk
  refine ⟨unread - base, ret_of_run h_bu h_uc h_lt h_count h_run, hL, hR, ?_,
    by rw [WidePtrVal.dropElems_snd, h_len], hD, SliceTypedAt.of_splitAt hk hL hR⟩
  simp only [WidePtrVal.elemOffset]
  omega

/-! ### Concrete instance: a real captured-MIR run faulting after 3 of 6 bytes -/

/-- The trusted MIR of `hermetic_copy_bytes_copied(4, 6, 7)` reaches a normal return of
`7 - 4 = 3` (replayed by the kernel-checked `TraceCheck` trace reconstructor). -/
theorem run_4_6_7 : ∃ tr mem', ReachesRet
    (mirStatefulTreeWithCallees Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body
      [.scalar ⟨4, 8⟩, .scalar ⟨6, 8⟩, .scalar ⟨7, 8⟩] emptyMemory)
    tr (.normal (.scalar ⟨3, 8⟩, mem')) := by
  obtain ⟨tr, out, -, h_out, h_reach⟩ :=
    Anneal.Rustc.V2026_06_01.TraceCheck.checkFullObservedTraceBounded_sound 16
      Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body
      (initMachineStateWithMemoryAndCallees Mir.FuchsiaUsercopy.hermetic_copy_bytes_copied.body
        [.scalar ⟨4, 8⟩, .scalar ⟨6, 8⟩, .scalar ⟨7, 8⟩] emptyMemory [])
      [] (.normal (.scalar ⟨3, 8⟩)) (by decide)
  rcases out with ⟨rv, m⟩ | _ | _
  · exact ⟨tr, m, h_out ▸ h_reach⟩
  · exact (h_out : False).elim
  · exact (h_out : False).elim

/-- A 10-byte user address-space image `[0, 1, ..., 9]` (allocation `2`). -/
def userSpaceBytes : ByteMem :=
  ByteLensCodec.encodeElems ByteLensCodec.u8 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- The 6-byte user buffer at address `4`, carved out of the address space with
`dropElems`. -/
theorem user_buf_view :
    SliceTypedAt ByteLensCodec.u8 (WidePtrVal.dropElems (WidePtrVal.mk ⟨2, 0⟩ 10) 1 4)
      [4, 5, 6, 7, 8, 9] userSpaceBytes :=
  (SliceTypedAt.splitAt (sliceTypedAt_encodeElems ByteLensCodec.u8 2 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9])
    (k := 4) (by decide)).2.1

/-- On the concrete run, the 3 copied bytes are `[4, 5, 6]` at address `4`, and the unread
suffix `[7, 8, 9]` starts at the returned unread address `7`. -/
theorem demo_copied_prefix :
    SliceTypedAt ByteLensCodec.u8 (WidePtrVal.mk ⟨2, 4⟩ 3) [4, 5, 6] userSpaceBytes ∧
      SliceTypedAt ByteLensCodec.u8 (WidePtrVal.mk ⟨2, 7⟩ 3) [7, 8, 9] userSpaceBytes ∧
      DisjointSlice 4 3 7 3 := by
  obtain ⟨tr, mem', h_run⟩ := run_4_6_7
  obtain ⟨copied, h_ret, hL, hR, -, -, hD, -⟩ :=
    copied_prefix_of_run (by decide) (by decide) (by decide) (by decide) h_run user_buf_view
      rfl rfl
  simp only [Value.scalar.injEq, Trusted.Rustc.V2026_06_01.MirAst.ScalarInt.mk.injEq,
    and_true] at h_ret
  subst h_ret
  exact ⟨hL, hR, hD⟩

end SliceLensCompanions

end Proof.FuchsiaUsercopy.hermetic_copy_bytes_copied
