import Trusted
import Anneal.MirLiftCore
import Anneal.SepLogicLenses
import Anneal.Rustc.V2026_06_01.TraceCheck
import Mir.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked
import Obligations.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked
import Specs.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked

namespace Proof.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.PureMirExec
open Anneal.Rustc.V2026_06_01.SymbolicEval

/-- Closes a step that halts immediately (such as a violated `assume` raising a
waived UB): `MirUbWaivedWpConverges.step` requires `evalSymNodeTreeExec`, which
rejects `.ub`, whereas `evalSymNodeTreeUbWaived` accepts `.halt .ub` at depth
`1` without consulting the continuation. -/
private theorem ubWaivedWpConverges_of_halt
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop}
    (h : evalSymNodeTreeUbWaived (fun _ => False) post (stepMirSymTree body s)) :
    MirUbWaivedWpConverges body s post :=
  ⟨1, h⟩

theorem verified : UbExceptionVerificationResult Obligations.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.ubExceptionClaim := by
  refine (fun h => verifyUbExceptionMir_of_wpConverges _ h ?waived) ?strict
  case strict =>
    rintro _ _ ⟨_, off, len, _, h_off, h_len, h_vs, -, rfl, rfl⟩ ⟨_, _, _, ⟨⟩⟩
    refine mirWpConverges_of_runCfgToBlock _ _ rfl 0 _ ⟨rfl, rfl, ?_⟩
    rintro _ _ _ _ ⟨⟩
    change Value.scalar ⟨wrapScalarBits (off + len) 18446744073709551616, 8⟩ = _
    rw [wrapScalarBits_of_lt
      (Nat.lt_of_le_of_lt (Nat.add_comm len off ▸ Nat.add_le_of_le_sub h_off h_len) h_vs)]
  case waived =>
    intro _ _ h_pre
    have h := h _ _ h_pre
    rcases h_pre with ⟨_, _, _, _, -, -, -, rfl | rfl, rfl, rfl⟩
    · -- When `trusted = false`, the `assume` (`copy _4 != false`) fails and
      -- halts with a waived UB.
      repeat
        first
        | exact ubWaivedWpConverges_of_halt trivial
        | refine MirUbWaivedWpConverges.step ?_
    · exact .of_mirWpConverges (h ⟨_, _, _, rfl⟩)

/-! ## Slice-lens companions of `verified`

`storage_device::buffer::PtrSlice::as_ref_unchecked`
(`src/storage/lib/storage_device/src/buffer.rs:146-152`) forms a `&[u8]` of `len` bytes at
`offset` inside a VMO mapping of `vmo_size` bytes. The theorems below read the returned end
offset of an actual normal return off the UB-exception `verified` (its partial-correctness
half covers every `trusted`; its strict-safety half makes the trusted call UB-free) and show
that the `offset .. offset + len` window is a sound typed subslice of any typed byte view of
the VMO, borrow-checked (`ActiveTypedSliceBorrow`) under the VMO lens's tag, whose window
ends exactly at the returned VMO-relative offset. -/

section SliceLensCompanions

open Trusted.ITree
open Anneal.SepLogicLenses

/-- Every normal return of the captured MIR on `pre`-admissible arguments (any `trusted`)
leaves memory untouched and returns `offset + len` (partial-correctness half of
`verified`). -/
theorem ret_of_run {vmo_size offset len t : Nat} (h_off : offset ≤ vmo_size)
    (h_len : len ≤ vmo_size - offset) (h_vs : vmo_size < 18446744073709551616)
    (h_t : t = 0 ∨ t = 1) {tr ret mem'}
    (h_run : ReachesRet
      (Trusted.VerificationResult.mirStatefulTreeWithCallees Mir.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.body
        [.scalar ⟨vmo_size, 8⟩, .scalar ⟨offset, 8⟩, .scalar ⟨len, 8⟩, .scalar ⟨t, 1⟩]
        emptyMemory)
      tr (.normal (ret, mem'))) :
    mem' = emptyMemory ∧ ret = .scalar ⟨offset + len, 8⟩ := by
  have h_pre : Specs.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.pre
      [.scalar ⟨vmo_size, 8⟩, .scalar ⟨offset, 8⟩, .scalar ⟨len, 8⟩, .scalar ⟨t, 1⟩]
      emptyMemory :=
    ⟨vmo_size, offset, len, t, h_off, h_len, h_vs, h_t, rfl, rfl⟩
  obtain ⟨h_mem, h_ret⟩ := verified.proof.2 _ _ h_pre tr ret mem' h_run
  exact ⟨h_mem, h_ret vmo_size offset len t rfl⟩

/-- For `trusted = true` the call is UB-free: the trusted MIR tree is `TreeSafe`
(strict-safety half of `verified`). -/
theorem treeSafe_of_trusted {vmo_size offset len : Nat} (h_off : offset ≤ vmo_size)
    (h_len : len ≤ vmo_size - offset) (h_vs : vmo_size < 18446744073709551616) :
    TreeSafe
      (Trusted.VerificationResult.mirStatefulTreeWithCallees Mir.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.body
        [.scalar ⟨vmo_size, 8⟩, .scalar ⟨offset, 8⟩, .scalar ⟨len, 8⟩, .scalar ⟨1, 1⟩]
        emptyMemory) := by
  have h_pre : Specs.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.pre
      [.scalar ⟨vmo_size, 8⟩, .scalar ⟨offset, 8⟩, .scalar ⟨len, 8⟩, .scalar ⟨1, 1⟩]
      emptyMemory :=
    ⟨vmo_size, offset, len, 1, h_off, h_len, h_vs, Or.inr rfl, rfl, rfl⟩
  obtain ⟨h_safe, -⟩ := verified.proof.1 _ _ ⟨h_pre, vmo_size, offset, len, rfl⟩
  exact h_safe

/-- A shared-borrow slice lens restricts to every subslice window inside it (the `&[T]`
analogue of `ActiveTypedSliceMutBorrow.splitAt`): the subslice
`takeElems (dropElems wide n off) len` keeps the tag, its byte window stays covered by the
borrow's range, and its view is `(xs.drop off).take len`. -/
theorem sharedBorrow_subslice {α : Type} {n : Nat} {c : ByteLensCodec α n}
    {borrows : List BorrowEntry} {tag : Nat} {wide : WidePtrVal} {xs : List α}
    {bytes : ByteMem} (h : ActiveTypedSliceBorrow c borrows tag wide xs bytes) {off len : Nat}
    (h_fit : off + len ≤ wide.2) :
    ActiveTypedSliceBorrow c borrows tag
      (WidePtrVal.takeElems (WidePtrVal.dropElems wide n off) len) ((xs.drop off).take len)
      bytes := by
  obtain ⟨hs, entry, he, ⟨hc1, hc2⟩, hp⟩ := h
  obtain ⟨-, hDrop, -⟩ := SliceTypedAt.splitAt hs (k := off) (by omega)
  obtain ⟨hSub, -, -⟩ := SliceTypedAt.splitAt hDrop (k := len)
    (by rw [WidePtrVal.dropElems_snd]; omega)
  have h_mul : off * n + len * n ≤ wide.2 * n := by
    rw [← Nat.add_mul]
    exact Nat.mul_le_mul_right n h_fit
  refine ⟨hSub, entry, he, ⟨?_, ?_⟩, hp⟩
  · simp only [WidePtrVal.elemOffset]
    omega
  · simp only [WidePtrVal.elemOffset]
    omega

/-- **`&[u8]` window of the verified slice construction.** For every 1-byte codec `c` and
every shared-borrow lens `ActiveTypedSliceBorrow c borrows tag vmo xs bytes` on the
`vmo_size`-element VMO mapping, any normal return leaves memory untouched and yields an
end offset `end_off ≤ vmo_size` such that the `len`-byte slice at `offset`,
`takeElems (dropElems vmo 1 offset) len`, is a borrow-checked typed subslice of the VMO
(same tag, view `(xs.drop offset).take len`) whose byte window ends exactly at
`elemOffset vmo 1 end_off`. -/
theorem sliceLens_of_run {vmo_size offset len t : Nat} (h_off : offset ≤ vmo_size)
    (h_len : len ≤ vmo_size - offset) (h_vs : vmo_size < 18446744073709551616)
    (h_t : t = 0 ∨ t = 1) {tr ret mem'}
    (h_run : ReachesRet
      (Trusted.VerificationResult.mirStatefulTreeWithCallees Mir.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.body
        [.scalar ⟨vmo_size, 8⟩, .scalar ⟨offset, 8⟩, .scalar ⟨len, 8⟩, .scalar ⟨t, 1⟩]
        emptyMemory)
      tr (.normal (ret, mem')))
    {α : Type} {c : ByteLensCodec α 1} {borrows : List BorrowEntry} {tag : Nat}
    {vmo : WidePtrVal} {xs : List α} {bytes : ByteMem}
    (h_vmo : ActiveTypedSliceBorrow c borrows tag vmo xs bytes) (h_size : vmo.2 = vmo_size) :
    mem' = emptyMemory ∧
      ∃ end_off : Nat,
        ret = .scalar ⟨end_off, 8⟩ ∧
        ActiveTypedSliceBorrow c borrows tag
          (WidePtrVal.takeElems (WidePtrVal.dropElems vmo 1 offset) len)
          ((xs.drop offset).take len) bytes ∧
        (WidePtrVal.takeElems (WidePtrVal.dropElems vmo 1 offset) len).1.offsetBytes +
            (WidePtrVal.takeElems (WidePtrVal.dropElems vmo 1 offset) len).2 * 1 =
          WidePtrVal.elemOffset vmo 1 end_off ∧
        end_off ≤ vmo.2 := by
  obtain ⟨h_mem, h_ret⟩ := ret_of_run h_off h_len h_vs h_t h_run
  refine ⟨h_mem, offset + len, h_ret, sharedBorrow_subslice h_vmo (by omega), ?_, by omega⟩
  simp only [WidePtrVal.elemOffset]
  omega

/-! ### Concrete instance: a real trusted captured-MIR run on a 12-byte VMO -/

/-- The trusted MIR of `vmo_buffer_as_ref_unchecked(12, 4, 6, true)` reaches a normal
return of `4 + 6 = 10` (replayed by the kernel-checked `TraceCheck` trace reconstructor). -/
theorem run_trusted_12_4_6 : ∃ tr mem', ReachesRet
    (Trusted.VerificationResult.mirStatefulTreeWithCallees Mir.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.body
      [.scalar ⟨12, 8⟩, .scalar ⟨4, 8⟩, .scalar ⟨6, 8⟩, .scalar ⟨1, 1⟩] emptyMemory)
    tr (.normal (.scalar ⟨10, 8⟩, mem')) := by
  obtain ⟨tr, out, -, h_out, h_reach⟩ :=
    Anneal.Rustc.V2026_06_01.TraceCheck.checkFullObservedTraceBounded_sound 16
      Mir.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.body
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
        Mir.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.body
        [.scalar ⟨12, 8⟩, .scalar ⟨4, 8⟩, .scalar ⟨6, 8⟩, .scalar ⟨1, 1⟩] emptyMemory [])
      [] (.normal (.scalar ⟨10, 8⟩)) (by decide)
  rcases out with ⟨rv, m⟩ | _ | _
  · exact ⟨tr, m, h_out ▸ h_reach⟩
  · exact (h_out : False).elim
  · exact (h_out : False).elim

/-- A 12-byte trusted VMO mapping `[0, 1, ..., 11]` (allocation `3`). -/
def vmoImage : ByteMem :=
  ByteLensCodec.encodeElems ByteLensCodec.u8 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- A frozen (shared) byte-ranged borrow (tag `41`) covering the whole mapping. -/
def vmoBorrows : List BorrowEntry :=
  [{ tag := 41, targetLocal := 0, targetProjection := [], perm := .frozen, rangeOffset := 0,
     rangeLen := 12 }]

/-- The `&[u8]` lens on the whole mapping. -/
theorem vmo_lens :
    ActiveTypedSliceBorrow ByteLensCodec.u8 vmoBorrows 41 (WidePtrVal.mk ⟨3, 0⟩ 12)
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] vmoImage :=
  ⟨sliceTypedAt_encodeElems ByteLensCodec.u8 3 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], _, rfl,
    ⟨Nat.le_refl 0, Nat.le_refl 12⟩, rfl⟩

/-- On the concrete trusted run, the call is UB-free and the `&[u8]` formed is the
borrow-checked view `[4, 5, 6, 7, 8, 9]` at VMO byte `4`, ending at the returned offset
`10`. -/
theorem demo_trusted_slice :
    TreeSafe
        (Trusted.VerificationResult.mirStatefulTreeWithCallees Mir.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked.body
          [.scalar ⟨12, 8⟩, .scalar ⟨4, 8⟩, .scalar ⟨6, 8⟩, .scalar ⟨1, 1⟩] emptyMemory) ∧
      ActiveTypedSliceBorrow ByteLensCodec.u8 vmoBorrows 41 (WidePtrVal.mk ⟨3, 4⟩ 6)
        [4, 5, 6, 7, 8, 9] vmoImage ∧
      SliceTypedAt ByteLensCodec.u8 (WidePtrVal.mk ⟨3, 4⟩ 6) [4, 5, 6, 7, 8, 9] vmoImage := by
  obtain ⟨tr, mem', h_run⟩ := run_trusted_12_4_6
  obtain ⟨-, end_off, h_ret, h_sub, -, -⟩ :=
    sliceLens_of_run (by decide) (by decide) (by decide) (Or.inr rfl) h_run vmo_lens rfl
  exact ⟨treeSafe_of_trusted (by decide) (by decide) (by decide), h_sub, h_sub.1⟩

end SliceLensCompanions

end Proof.FxfsStorageBoundary.vmo_buffer_as_ref_unchecked
