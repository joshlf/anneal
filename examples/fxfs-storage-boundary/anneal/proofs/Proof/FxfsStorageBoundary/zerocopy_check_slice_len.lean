import Trusted
import Anneal.MirLiftCore
import Anneal.SepLogicLenses
import Anneal.Rustc.V2026_06_01.TraceCheck
import Mir.FxfsStorageBoundary.zerocopy_check_slice_len
import Obligations.FxfsStorageBoundary.zerocopy_check_slice_len
import Specs.FxfsStorageBoundary.zerocopy_check_slice_len

namespace Proof.FxfsStorageBoundary.zerocopy_check_slice_len

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Anneal.FunctionalTranslation

theorem verified : StatefulVerificationResult Obligations.FxfsStorageBoundary.zerocopy_check_slice_len.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl
    (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨bl, es, h_es_pos, h_bl, -, rfl⟩, rfl⟩
  have h_es0 : Nat.beq es 0 = false :=
    Bool.eq_false_iff.mpr fun h => Nat.ne_of_gt h_es_pos (Nat.eq_of_beq_eq_true h)
  have h_assert : (boolToScalar (Nat.beq es 0)).bits = 0 := by rw [h_es0]; rfl
  apply lift_PureMirConverges rfl
  apply LiftBlock.of_lookup rfl
  apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
  apply LiftStmtsTerminator.term_assert (by rfl) (Or.inr rfl) (by rfl) (by rfl) h_assert
  apply LiftBlock.of_lookup rfl
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue
      (val := .scalar ⟨bl % es, 8⟩) rfl ?h_rem rfl (by nofun) rfl)
  case h_rem =>
    change evalScalarBinOp .rem ⟨bl, 8⟩ ⟨es, 8⟩ _ _ false = _
    simp [evalScalarBinOp, scalarModulus, wrapScalarBits, h_es0,
      show bl.mod es = bl % es from rfl,
      nat_ble_eq_false_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le bl es) h_bl)]
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue
      (val := .scalar ⟨bl - bl % es, 8⟩) rfl ?h_sub rfl (by nofun) rfl)
  case h_sub =>
    change evalScalarBinOp .subUnchecked ⟨bl, 8⟩ ⟨bl % es, 8⟩ _ _ false = _
    simp [evalScalarBinOp, scalarModulus, Nat.ble_eq_true_of_le (Nat.mod_le bl es),
      nat_ble_eq_false_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) h_bl)]
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.term_assert (by rfl) (Or.inr rfl) (by rfl) (by rfl) h_assert
  apply LiftBlock.of_lookup rfl
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue
      (val := .scalar ⟨(bl - bl % es) / es, 8⟩) rfl ?h_div rfl (by nofun) rfl)
  case h_div =>
    change evalScalarBinOp .div ⟨bl - bl % es, 8⟩ ⟨es, 8⟩ _ _ false = _
    simp [evalScalarBinOp, scalarModulus, wrapScalarBits, h_es0,
      show (bl - bl % es).div es = (bl - bl % es) / es from rfl,
      nat_ble_eq_false_of_lt
        (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) h_bl))]
  apply LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)
  apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  rintro _ _ ⟨⟩
  rfl

/-! ## Slice-lens companions of `verified`

`fxfs::zerocopy_serialization::visit_bytes` reinterprets a demonic serialized byte slice of
`byte_len` bytes as a `&[T::Inner]` slice of `elem_size`-byte elements, using the element
count computed by `zerocopy_check_slice_len`. The theorems below read that count off an
actual normal return of the captured MIR (via `verified`) and connect it to the
wide-pointer slice lenses of `Anneal.SepLogicLenses` over a `u8` view of the byte slice:
`count` elements fit (`count * elem_size ≤ byte_len`) but `count + 1` do not; the byte view
splits (`SliceTypedAt.splitAt`) into the element-aligned prefix of exactly
`count * elem_size` bytes and the excluded remainder of `byte_len % elem_size < elem_size`
bytes, with adjacent disjoint windows; and every `FromBytes`-style element codec (one that
decodes every window of initialized bytes) reinterprets the aligned prefix as a
`count`-element `SliceTypedAt` view whose window starts at the byte slice's data pointer. -/

section SliceLensCompanions

open Trusted.ITree
open Anneal.SepLogicLenses

/-- Every normal return of the captured MIR on `pre`-admissible arguments returns
`(byte_len - byte_len % elem_size) / elem_size`, read off `verified`. -/
theorem ret_of_run {bl es : Nat} (h_es : 0 < es) (h_bl : bl < 18446744073709551616)
    (h_es' : es < 18446744073709551616) {tr ret mem'}
    (h_run : ReachesRet
      (mirStatefulTreeWithCallees Mir.FxfsStorageBoundary.zerocopy_check_slice_len.body
        [.scalar ⟨bl, 8⟩, .scalar ⟨es, 8⟩] emptyMemory)
      tr (.normal (ret, mem'))) :
    ret = .scalar ⟨(bl - bl % es) / es, 8⟩ := by
  have h_pre : Specs.FxfsStorageBoundary.zerocopy_check_slice_len.pre
      [.scalar ⟨bl, 8⟩, .scalar ⟨es, 8⟩] :=
    ⟨bl, es, h_es, h_bl, h_es', rfl⟩
  obtain ⟨_, h_spec⟩ := verified.proof _ emptyMemory ⟨h_pre, rfl⟩
  exact h_spec (tr, .normal (ret, mem')) h_run ⟨h_pre, rfl⟩ ret mem' rfl bl es rfl

/-- An initialized abstract byte (any value, any provenance). -/
def InitByte (b : AbstractByte) : Prop := ∃ x p, b = .init x p

/-- `FromBytes`-style element codec (zerocopy's `T: FromBytes`): every `es`-byte window of
initialized bytes decodes to some element. -/
def DecodesInitWindows {α : Type} {es : Nat} (c : ByteLensCodec α es) : Prop :=
  ∀ w : List AbstractByte, w.length = es → (∀ b ∈ w, InitByte b) → ∃ x, c.decode w = some x

/-- A `FromBytes`-style codec decodes every `N`-element window of initialized bytes. -/
theorem decodeElems_of_decodesInitWindows {α : Type} {es : Nat} {c : ByteLensCodec α es}
    (hc : DecodesInitWindows c) :
    ∀ (N : Nat) (w : List AbstractByte), w.length = N * es → (∀ b ∈ w, InitByte b) →
      ∃ ys, ByteLensCodec.decodeElems c N w = some ys
  | 0, w, hw, _ => by
    rw [Nat.zero_mul] at hw
    rw [List.eq_nil_of_length_eq_zero hw]
    exact ⟨[], rfl⟩
  | N + 1, w, hw, hi => by
    rw [Nat.succ_mul] at hw
    obtain ⟨x, hx⟩ := hc (w.take es) (by rw [List.length_take]; omega)
      (fun b hb => hi b (List.mem_of_mem_take hb))
    obtain ⟨ys, hys⟩ := decodeElems_of_decodesInitWindows hc N (w.drop es)
      (by rw [List.length_drop]; omega) (fun b hb => hi b (List.mem_of_mem_drop hb))
    refine ⟨x :: ys, ?_⟩
    unfold ByteLensCodec.decodeElems
    rw [hx, hys]

/-- A `u8` decode succeeds exactly on a single initialized byte. -/
theorem u8_decode_eq_some {w : List AbstractByte} {x : UInt8}
    (h : ByteLensCodec.u8.decode w = some x) : ∃ p, w = [.init x p] := by
  rcases w with _ | ⟨_ | ⟨b, p⟩, _ | ⟨_, _⟩⟩
  · cases h
  · cases h
  · cases h
  · cases h
    exact ⟨p, rfl⟩
  · cases h

/-- Every byte of the first `k ≤ buf.2` bytes of a `u8` view is initialized. -/
theorem initByte_of_u8_view {buf : WidePtrVal} {bs : List UInt8} {bytes : ByteMem}
    (h : SliceTypedAt ByteLensCodec.u8 buf bs bytes) {k : Nat} (hk : k ≤ buf.2) :
    ∀ b ∈ (bytes.drop buf.1.offsetBytes).take k, InitByte b := by
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
  have hik : i < k := by
    simp only [List.length_take, List.length_drop] at hi
    omega
  have hib : i < bs.length := by rw [h.length_eq]; omega
  have ht := h.getElem_typedAt' hib
  rw [typedAt_iff] at ht
  obtain ⟨hlen, hdec⟩ := ht
  obtain ⟨p, hp⟩ := u8_decode_eq_some hdec
  have hlt : buf.1.offsetBytes + i < bytes.length := by
    simp only [WidePtrVal.elemOffset] at hlen
    omega
  have hone : (bytes.drop (WidePtrVal.elemOffset buf 1 i)).take 1 =
      [bytes[buf.1.offsetBytes + i]] := by
    simp only [WidePtrVal.elemOffset, Nat.mul_one]
    rw [List.drop_eq_getElem_cons hlt, List.take_succ_cons, List.take_zero]
  rw [hone, List.cons.injEq] at hp
  refine ⟨bs[i], p, ?_⟩
  rw [List.getElem_take, List.getElem_drop]
  exact hp.1

/-- **`FromBytes` reinterpretation.** If a byte slice has a `u8` view, then every
`FromBytes`-style codec of width `es` gives a typed view of `N` elements at the same data
pointer whenever the `N * es`-byte window fits the byte slice. -/
theorem elemView_of_u8_view {α : Type} {es : Nat} {c : ByteLensCodec α es}
    (hc : DecodesInitWindows c) {buf : WidePtrVal} {bs : List UInt8} {bytes : ByteMem}
    (h : SliceTypedAt ByteLensCodec.u8 buf bs bytes) {N : Nat} (hN : N * es ≤ buf.2) :
    ∃ ys, SliceTypedAt c (WidePtrVal.mk buf.1 N) ys bytes := by
  have hwin : buf.1.offsetBytes + N * es ≤ bytes.length := by
    have := h.window_le
    omega
  obtain ⟨ys, hys⟩ := decodeElems_of_decodesInitWindows hc N
    ((bytes.drop buf.1.offsetBytes).take (N * es))
    (by rw [List.length_take, List.length_drop]; omega) (initByte_of_u8_view h hN)
  exact ⟨ys, sliceTypedAt_of_decodeElems c buf.1.allocId N buf.1.offsetBytes ys bytes hwin hys⟩

/-- **Zerocopy `&[T]` window of the verified element count.** For every `u8` view
`SliceTypedAt u8 buf bs bytes` of a `byte_len`-byte slice, any normal return yields
`count` with `count * elem_size ≤ byte_len < (count + 1) * elem_size`; the byte view splits
into the aligned prefix `takeElems buf (count * elem_size)` and the excluded remainder
`dropElems buf 1 (count * elem_size)` of `byte_len % elem_size` bytes, with adjacent
disjoint windows; and every `FromBytes`-style codec `c` of width `elem_size` reinterprets
the prefix as a `count`-element view `SliceTypedAt c (WidePtrVal.mk buf.1 count) ys`. -/
theorem elemWindow_of_run {bl es : Nat} (h_es : 0 < es) (h_bl : bl < 18446744073709551616)
    (h_es' : es < 18446744073709551616) {tr ret mem'}
    (h_run : ReachesRet
      (mirStatefulTreeWithCallees Mir.FxfsStorageBoundary.zerocopy_check_slice_len.body
        [.scalar ⟨bl, 8⟩, .scalar ⟨es, 8⟩] emptyMemory)
      tr (.normal (ret, mem')))
    {buf : WidePtrVal} {bs : List UInt8} {bytes : ByteMem}
    (h_buf : SliceTypedAt ByteLensCodec.u8 buf bs bytes) (h_len : buf.2 = bl) :
    ∃ count : Nat,
      ret = .scalar ⟨count, 8⟩ ∧
      count * es ≤ bl ∧ bl < (count + 1) * es ∧
      SliceTypedAt ByteLensCodec.u8 (WidePtrVal.takeElems buf (count * es))
        (bs.take (count * es)) bytes ∧
      SliceTypedAt ByteLensCodec.u8 (WidePtrVal.dropElems buf 1 (count * es))
        (bs.drop (count * es)) bytes ∧
      (WidePtrVal.dropElems buf 1 (count * es)).2 = bl % es ∧
      DisjointSlice buf.1.offsetBytes (count * es * 1)
        (buf.1.offsetBytes + count * es * 1) ((buf.2 - count * es) * 1) ∧
      ∀ {α : Type} (c : ByteLensCodec α es), DecodesInitWindows c →
        ∃ ys, ys.length = count ∧ SliceTypedAt c (WidePtrVal.mk buf.1 count) ys bytes := by
  have h_ret := ret_of_run h_es h_bl h_es' h_run
  have hdm := Nat.div_add_mod bl es
  have hmod := Nat.mod_lt bl h_es
  have hcomm : bl / es * es = es * (bl / es) := Nat.mul_comm _ _
  have hcount : (bl - bl % es) / es = bl / es := by
    rw [show bl - bl % es = es * (bl / es) by omega, Nat.mul_div_cancel_left _ h_es]
  have hk : bl / es * es ≤ buf.2 := by omega
  obtain ⟨hL, hR, hD⟩ := SliceTypedAt.splitAt h_buf hk
  refine ⟨bl / es, hcount ▸ h_ret, by omega, by rw [Nat.succ_mul]; omega, hL, hR,
    by rw [WidePtrVal.dropElems_snd]; omega, hD, fun c hc => ?_⟩
  obtain ⟨ys, hys⟩ := elemView_of_u8_view hc h_buf hk
  exact ⟨ys, hys.length_eq, hys⟩

/-! ### Concrete instance: a real captured-MIR run reinterpreting 7 bytes as `[u16]` -/

/-- The little-endian unsigned codecs are `FromBytes`-style: every window of initialized
bytes decodes. -/
theorem uintLE_decodesInitWindows (sz : Nat) : DecodesInitWindows (ByteLensCodec.uintLE sz) := by
  have h_dec : ∀ w : List AbstractByte, (∀ b ∈ w, InitByte b) →
      ∃ v p, decodeLittleEndianBytes w = some (v, p) ∧ v < 256 ^ w.length := by
    intro w
    induction w with
    | nil => exact fun _ => ⟨0, none, rfl, by decide⟩
    | cons b rest ih =>
      intro hi
      obtain ⟨x, p, rfl⟩ := hi b List.mem_cons_self
      obtain ⟨v, q, hv, hlt⟩ := ih (fun b' hb' => hi b' (List.mem_cons_of_mem _ hb'))
      have hx : x.toBitVec.toNat < 256 := x.toBitVec.isLt
      refine ⟨x.toBitVec.toNat + 256 * v, mergeByteProvenance p q, ?_, ?_⟩
      · show (match decodeLittleEndianBytes rest with
          | some (highBits, restProv) =>
            some (Nat.add x.toBitVec.toNat (Nat.mul 256 highBits),
              mergeByteProvenance p restProv)
          | none => none) = _
        rw [hv]
        rfl
      · rw [List.length_cons, Nat.pow_succ]
        have : 256 * v + 256 ≤ 256 ^ rest.length * 256 := by
          rw [Nat.mul_comm (256 ^ rest.length) 256]
          have := Nat.mul_le_mul_left 256 (Nat.succ_le_of_lt hlt)
          rw [Nat.mul_succ] at this
          exact this
        omega
  intro w hw hi
  obtain ⟨v, p, hv, hlt⟩ := h_dec w hi
  rw [hw] at hlt
  refine ⟨⟨v, hlt⟩, ?_⟩
  show (match decodeLittleEndianBytes w with
    | some (v, _) =>
      if h : v < 256 ^ sz then some (⟨v, h⟩ : {v : Nat // v < 256 ^ sz}) else none
    | none => none) = some ⟨v, hlt⟩
  rw [hv]
  exact dite_eq_left hlt

/-- The trusted MIR of `zerocopy_check_slice_len(7, 2)` reaches a normal return of
`(7 - 7 % 2) / 2 = 3` (replayed by the kernel-checked `TraceCheck` trace reconstructor). -/
theorem run_7_2 : ∃ tr mem', ReachesRet
    (mirStatefulTreeWithCallees Mir.FxfsStorageBoundary.zerocopy_check_slice_len.body
      [.scalar ⟨7, 8⟩, .scalar ⟨2, 8⟩] emptyMemory)
    tr (.normal (.scalar ⟨3, 8⟩, mem')) := by
  obtain ⟨tr, out, -, h_out, h_reach⟩ :=
    Anneal.Rustc.V2026_06_01.TraceCheck.checkFullObservedTraceBounded_sound 24
      Mir.FxfsStorageBoundary.zerocopy_check_slice_len.body
      (initMachineStateWithMemoryAndCallees Mir.FxfsStorageBoundary.zerocopy_check_slice_len.body
        [.scalar ⟨7, 8⟩, .scalar ⟨2, 8⟩] emptyMemory [])
      [] (.normal (.scalar ⟨3, 8⟩)) (by decide)
  rcases out with ⟨rv, m⟩ | _ | _
  · exact ⟨tr, m, h_out ▸ h_reach⟩
  · exact (h_out : False).elim
  · exact (h_out : False).elim

/-- A 7-byte serialized slice `[1, 0, 2, 0, 3, 0, 9]` (allocation `5`). -/
def serBytes : ByteMem := ByteLensCodec.encodeElems ByteLensCodec.u8 [1, 0, 2, 0, 3, 0, 9]

/-- The `u8` view of `serBytes` through the 7-element wide pointer at `⟨5, 0⟩`. -/
theorem ser_view :
    SliceTypedAt ByteLensCodec.u8 (WidePtrVal.mk ⟨5, 0⟩ 7) [1, 0, 2, 0, 3, 0, 9] serBytes :=
  sliceTypedAt_encodeElems ByteLensCodec.u8 5 [1, 0, 2, 0, 3, 0, 9]

/-- On the concrete run with `elem_size = 2`, the slice reinterprets as a 3-element `[u16]`
view at byte `0` (the 6-byte aligned prefix `[1, 0, 2, 0, 3, 0]`), and the trailing byte
`[9]` at offset `6` is the excluded remainder. -/
theorem demo_u16_window :
    (∃ ys : List {v : Nat // v < 256 ^ 2}, ys.length = 3 ∧
      SliceTypedAt ByteLensCodec.u16LE (WidePtrVal.mk ⟨5, 0⟩ 3) ys serBytes) ∧
      SliceTypedAt ByteLensCodec.u8 (WidePtrVal.mk ⟨5, 0⟩ 6) [1, 0, 2, 0, 3, 0] serBytes ∧
      SliceTypedAt ByteLensCodec.u8 (WidePtrVal.mk ⟨5, 6⟩ 1) [9] serBytes := by
  obtain ⟨tr, mem', h_run⟩ := run_7_2
  obtain ⟨count, h_ret, -, -, hL, hR, -, -, h_elems⟩ :=
    elemWindow_of_run (by decide) (by decide) (by decide) h_run ser_view rfl
  simp only [Value.scalar.injEq, Trusted.Rustc.V2026_06_01.MirAst.ScalarInt.mk.injEq,
    and_true] at h_ret
  subst h_ret
  exact ⟨h_elems ByteLensCodec.u16LE (uintLE_decodesInitWindows 2), hL, hR⟩

end SliceLensCompanions

end Proof.FxfsStorageBoundary.zerocopy_check_slice_len
