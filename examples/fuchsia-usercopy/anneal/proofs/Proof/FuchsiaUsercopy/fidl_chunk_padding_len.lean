import Trusted
import Anneal
import Mir.FuchsiaUsercopy.fidl_chunk_padding_len
import Obligations.FuchsiaUsercopy.fidl_chunk_padding_len
import Specs.FuchsiaUsercopy.fidl_chunk_padding_len

namespace Proof.FuchsiaUsercopy.fidl_chunk_padding_len

open Trusted.VerificationResult
open Anneal.PureMirExec
open Anneal.MirLiftCore

theorem verified : StatefulVerificationResult Obligations.FuchsiaUsercopy.fidl_chunk_padding_len.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl
    (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨es, len, h_es, h_len, rfl⟩, rfl⟩
  -- `pre` admits 12 concrete `(es, len)` pairs; each one runs the same
  -- straight-line path, and every overflow / zero-divisor `assert` holds.
  rcases h_es with rfl | rfl | rfl <;> rcases h_len with rfl | rfl | rfl | rfl <;>
  · apply lift_PureMirConverges rfl
    -- bb0..bb4 each end in an `assert` that holds for these inputs: bb0
    -- (`es * len`), bb1 (`+ 7`), bb3 (`/ 8 * 8`), and bb4 (`- (es * len)`)
    -- check for overflow, and bb2 checks the constant divisor `8 != 0`.
    repeat
      apply LiftBlock.of_lookup rfl
      apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
      apply LiftStmtsTerminator.term_assert (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl)
    -- bb5: `_11 = move (_12.0); _0 = (copy _3, copy _11); return`
    apply LiftBlock.of_lookup rfl
    apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
    apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
    rintro _ _ ⟨⟩
    exact ⟨rfl, by decide, by decide⟩

/-! ## Slice-lens companions of `verified`

`DecoderExt::take_slice_slot` (`src/lib/fidl/rust_next/fidl_next_codec/src/decoder.rs:150-179`)
carves an 8-byte-aligned wire slot of `(es * len + pad)` bytes into a `es * len`-byte
payload prefix and a `pad`-byte (`pad < 8`) zero-padding suffix. The theorems below take an
actual normal return of the captured MIR (`ReachesRet` of `mirStatefulTreeWithCallees`),
read `(bl, pad)` off `verified`, and show that the returned lengths decompose any typed
byte view (`SliceTypedAt` or `ActiveTypedSliceMutBorrow`) of the wire slot via
`SliceTypedAt.splitAt` / `ActiveTypedSliceMutBorrow.splitAt` into adjacent, disjoint
payload and padding windows that reassemble (`of_splitAt`) into the parent wire slot. -/

section SliceLensCompanions

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.ITree
open Anneal.SepLogicLenses

/-- Every normal return of the captured MIR on `pre`-admissible `(es, len)` returns
`(es * len, ((es * len + 7) / 8) * 8 - es * len)` with `pad < 8` and
`bl + pad = ((bl + 7) / 8) * 8`, read off `verified`. -/
theorem ret_of_run {es len : Nat}
    (h_es : es = 1 ∨ es = 4 ∨ es = 8)
    (h_len : len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 8)
    {tr ret mem'}
    (h_run : ReachesRet
      (mirStatefulTreeWithCallees Mir.FuchsiaUsercopy.fidl_chunk_padding_len.body
        [.scalar ⟨es, 8⟩, .scalar ⟨len, 8⟩] emptyMemory)
      tr (.normal (ret, mem'))) :
    let bl := es * len
    let pad := ((bl + 7) / 8) * 8 - bl
    ret = .aggregate 0 [.scalar ⟨bl, 8⟩, .scalar ⟨pad, 8⟩] ∧
      pad < 8 ∧
      bl + pad = ((bl + 7) / 8) * 8 := by
  have h_pre : Specs.FuchsiaUsercopy.fidl_chunk_padding_len.pre
      [.scalar ⟨es, 8⟩, .scalar ⟨len, 8⟩] :=
    ⟨es, len, h_es, h_len, rfl⟩
  obtain ⟨_, h_spec⟩ := verified.proof _ emptyMemory ⟨h_pre, rfl⟩
  exact h_spec (tr, .normal (ret, mem')) h_run ⟨h_pre, rfl⟩ ret mem' rfl es len rfl

/-- **FIDL wire-slot decomposition.** For every 1-byte codec `c` and every typed view
`SliceTypedAt c slot xs bytes` of an 8-byte-aligned wire slot with
`slot.2 = ((es * len + 7) / 8) * 8`, any normal return yields `(bl, pad)` (`bl = es * len`,
`pad < 8`) that splits the wire slot into the `bl`-byte payload prefix `takeElems slot bl`
(`xs.take bl`) and the `pad`-byte padding suffix `dropElems slot 1 bl` (`xs.drop bl`),
whose byte windows are adjacent and disjoint and reassemble (`of_splitAt`) into the slot. -/
theorem fidl_slot_split_of_run {es len : Nat}
    (h_es : es = 1 ∨ es = 4 ∨ es = 8)
    (h_len : len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 8)
    {tr ret mem'}
    (h_run : ReachesRet
      (mirStatefulTreeWithCallees Mir.FuchsiaUsercopy.fidl_chunk_padding_len.body
        [.scalar ⟨es, 8⟩, .scalar ⟨len, 8⟩] emptyMemory)
      tr (.normal (ret, mem')))
    {α : Type} {c : ByteLensCodec α 1} {slot : WidePtrVal} {xs : List α} {bytes : ByteMem}
    (h_slot : SliceTypedAt c slot xs bytes)
    (h_slot_len : slot.2 = ((es * len + 7) / 8) * 8) :
    ∃ bl pad : Nat,
      ret = .aggregate 0 [.scalar ⟨bl, 8⟩, .scalar ⟨pad, 8⟩] ∧
      bl = es * len ∧
      pad < 8 ∧
      bl + pad = slot.2 ∧
      SliceTypedAt c (WidePtrVal.takeElems slot bl) (xs.take bl) bytes ∧
      SliceTypedAt c (WidePtrVal.dropElems slot 1 bl) (xs.drop bl) bytes ∧
      (WidePtrVal.dropElems slot 1 bl).2 = pad ∧
      DisjointSlice slot.1.offsetBytes (bl * 1)
        (slot.1.offsetBytes + bl * 1) (pad * 1) ∧
      SliceTypedAt c slot (xs.take bl ++ xs.drop bl) bytes := by
  obtain ⟨h_ret, h_pad_lt, h_sum⟩ := ret_of_run h_es h_len h_run
  let bl := es * len
  let pad := ((bl + 7) / 8) * 8 - bl
  have hk : bl ≤ slot.2 := by omega
  obtain ⟨hL, hR, hD⟩ := SliceTypedAt.splitAt h_slot hk
  have h_sub : slot.2 - bl = pad := by omega
  refine ⟨bl, pad, h_ret, rfl, h_pad_lt, by omega, hL, hR,
    by rw [WidePtrVal.dropElems_snd, h_sub], ?_, SliceTypedAt.of_splitAt hk hL hR⟩
  rw [h_sub] at hD
  exact hD

/-- **Borrow-checked FIDL wire-slot split.** For a live `&mut` byte lens
(`ActiveTypedSliceMutBorrow`) on the wire slot, the verified `(bl, pad)` split yields two
`&mut` lenses under the same tag on the `bl`-byte payload prefix and `pad`-byte padding
suffix, with adjacent disjoint byte windows, which recombine into the parent slot lens. -/
theorem fidl_slot_mutBorrow_split_of_run {es len : Nat}
    (h_es : es = 1 ∨ es = 4 ∨ es = 8)
    (h_len : len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 8)
    {tr ret mem'}
    (h_run : ReachesRet
      (mirStatefulTreeWithCallees Mir.FuchsiaUsercopy.fidl_chunk_padding_len.body
        [.scalar ⟨es, 8⟩, .scalar ⟨len, 8⟩] emptyMemory)
      tr (.normal (ret, mem')))
    {α : Type} {c : ByteLensCodec α 1} {borrows : List BorrowEntry} {tag : Nat}
    {slot : WidePtrVal} {xs : List α} {bytes : ByteMem}
    (h_slot : ActiveTypedSliceMutBorrow c borrows tag slot xs bytes)
    (h_slot_len : slot.2 = ((es * len + 7) / 8) * 8) :
    ∃ bl pad : Nat,
      ret = .aggregate 0 [.scalar ⟨bl, 8⟩, .scalar ⟨pad, 8⟩] ∧
      pad < 8 ∧
      ActiveTypedSliceMutBorrow c borrows tag (WidePtrVal.takeElems slot bl)
        (xs.take bl) bytes ∧
      ActiveTypedSliceMutBorrow c borrows tag (WidePtrVal.dropElems slot 1 bl)
        (xs.drop bl) bytes ∧
      (WidePtrVal.dropElems slot 1 bl).2 = pad ∧
      DisjointSlice slot.1.offsetBytes (bl * 1)
        (slot.1.offsetBytes + bl * 1) (pad * 1) ∧
      ActiveTypedSliceMutBorrow c borrows tag slot (xs.take bl ++ xs.drop bl) bytes := by
  obtain ⟨h_ret, h_pad_lt, h_sum⟩ := ret_of_run h_es h_len h_run
  let bl := es * len
  let pad := ((bl + 7) / 8) * 8 - bl
  have hk : bl ≤ slot.2 := by omega
  obtain ⟨hL, hR, hD⟩ := ActiveTypedSliceMutBorrow.splitAt h_slot hk
  obtain ⟨-, entry, he, hc, -⟩ := h_slot
  have h_sub : slot.2 - bl = pad := by omega
  refine ⟨bl, pad, h_ret, h_pad_lt, hL, hR, by rw [WidePtrVal.dropElems_snd, h_sub], ?_,
    ActiveTypedSliceMutBorrow.of_splitAt hk hL hR ⟨entry, he, hc⟩⟩
  rw [h_sub] at hD
  exact hD

/-! ### Concrete instance: a 3-element `u32` (`es = 4, len = 3`) FIDL slice in a 2-chunk slot -/

/-- The trusted MIR of `fidl_chunk_padding_len(4, 3)` reaches a normal return of
`(12, 4)` (replayed by the kernel-checked `TraceCheck` trace reconstructor). -/
theorem run_4_3 : ∃ tr mem', ReachesRet
    (mirStatefulTreeWithCallees Mir.FuchsiaUsercopy.fidl_chunk_padding_len.body
      [.scalar ⟨4, 8⟩, .scalar ⟨3, 8⟩] emptyMemory)
    tr (.normal (.aggregate 0 [.scalar ⟨12, 8⟩, .scalar ⟨4, 8⟩], mem')) := by
  obtain ⟨tr, out, -, h_out, h_reach⟩ :=
    Anneal.Rustc.V2026_06_01.TraceCheck.checkFullObservedTraceBounded_sound 32
      Mir.FuchsiaUsercopy.fidl_chunk_padding_len.body
      (initMachineStateWithMemoryAndCallees
        Mir.FuchsiaUsercopy.fidl_chunk_padding_len.body
        [.scalar ⟨4, 8⟩, .scalar ⟨3, 8⟩] emptyMemory [])
      [] (.normal (.aggregate 0 [.scalar ⟨12, 8⟩, .scalar ⟨4, 8⟩])) (by decide)
  rcases out with ⟨rv, m⟩ | _ | _
  · exact ⟨tr, m, h_out ▸ h_reach⟩
  · exact (h_out : False).elim
  · exact (h_out : False).elim

/-- A 16-byte (2-chunk) FIDL wire slot `[1..12, 0, 0, 0, 0]` (allocation `9`). -/
def fidlSlotBytes : ByteMem :=
  ByteLensCodec.encodeElems ByteLensCodec.u8
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 0, 0, 0, 0]

/-- The 16-byte `u8` view of `fidlSlotBytes` at `⟨9, 0⟩`. -/
theorem fidlSlot_view :
    SliceTypedAt ByteLensCodec.u8 (WidePtrVal.mk ⟨9, 0⟩ 16)
      [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 0, 0, 0, 0] fidlSlotBytes :=
  sliceTypedAt_encodeElems ByteLensCodec.u8 9
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 0, 0, 0, 0]

/-- On the concrete run (`es = 4, len = 3`), the 16-byte FIDL wire slot splits into the
12-byte payload `[1..12]` at `⟨9, 0⟩` and the 4-byte zero-padding `[0, 0, 0, 0]` at
`⟨9, 12⟩` with `DisjointSlice 0 12 12 4`. -/
theorem demo_fidl_slot_split :
    SliceTypedAt ByteLensCodec.u8 (WidePtrVal.mk ⟨9, 0⟩ 12)
        [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] fidlSlotBytes ∧
      SliceTypedAt ByteLensCodec.u8 (WidePtrVal.mk ⟨9, 12⟩ 4) [0, 0, 0, 0] fidlSlotBytes ∧
      DisjointSlice 0 12 12 4 := by
  obtain ⟨tr, mem', h_run⟩ := run_4_3
  obtain ⟨bl, pad, h_ret, -, -, -, hL, hR, -, hD, -⟩ :=
    fidl_slot_split_of_run (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl))) h_run
      fidlSlot_view rfl
  simp only [Value.aggregate.injEq, List.cons.injEq, Value.scalar.injEq,
    Trusted.Rustc.V2026_06_01.MirAst.ScalarInt.mk.injEq, and_true, true_and] at h_ret
  obtain ⟨rfl, rfl⟩ := h_ret
  exact ⟨hL, hR, hD⟩

end SliceLensCompanions

end Proof.FuchsiaUsercopy.fidl_chunk_padding_len
