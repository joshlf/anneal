import Trusted
import Anneal.MirLiftCore
import Anneal.SepLogicLenses
import Anneal.Rustc.V2026_06_01.TraceCheck
import Mir.FxfsStorageBoundary.vmo_subslice_bounds_valid
import Obligations.FxfsStorageBoundary.vmo_subslice_bounds_valid
import Specs.FxfsStorageBoundary.vmo_subslice_bounds_valid

namespace Proof.FxfsStorageBoundary.vmo_subslice_bounds_valid

open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Anneal.FunctionalTranslation

theorem verified : StatefulVerificationResult Obligations.FxfsStorageBoundary.vmo_subslice_bounds_valid.statefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec _ rfl
    (fun _ _ h => h.2 ▸ rootActiveMemory_emptyMemory) ?_
  rintro _ _ ⟨⟨base, len, s, e, h_se, h_el, h_bound, rfl⟩, rfl⟩
  have h_es_len : e - s ≤ len := Nat.le_trans (Nat.sub_le e s) h_el
  apply lift_PureMirConverges rfl
  apply LiftBlock.of_lookup rfl
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue
      (val := .scalar ⟨e - s, 8⟩) rfl ?h_sub rfl (by nofun) rfl)
  case h_sub =>
    change evalScalarBinOp .subUnchecked ⟨e, 8⟩ ⟨s, 8⟩ _ _ false = _
    simp [evalScalarBinOp, scalarModulus, Nat.ble_eq_true_of_le h_se,
      nat_ble_eq_false_of_lt
        (Nat.lt_of_le_of_lt (Nat.le_trans h_es_len (Nat.le_add_left _ _)) h_bound)]
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl)
    (evalPureStmtNorm_assign_local_of_evalRvalue
      (val := .scalar ⟨base + (e - s), 8⟩) rfl ?h_add rfl (by nofun) rfl)
  case h_add =>
    change evalScalarBinOp .addUnchecked ⟨base, 8⟩ ⟨e - s, 8⟩ _ _ false = _
    simp [evalScalarBinOp, scalarModulus,
      nat_ble_eq_false_of_lt (Nat.lt_of_le_of_lt (Nat.add_le_add_left h_es_len _) h_bound)]
  apply LiftStmtsTerminator.cons_eval_norm (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  rintro _ _ _ _ ⟨⟩
  rfl

/-! ## Slice-lens companions of `verified`

`storage_device::BufferRef::subslice` (`src/storage/lib/storage_device/src/buffer.rs`)
narrows a VMO-backed buffer `[base_offset, base_offset + buf_len)` to the sub-range
`sub_start..sub_end`. The theorems below read the returned end offset of an actual normal
return off `verified` and tie it to the wide-pointer slice lenses of
`Anneal.SepLogicLenses` over any typed byte view (`u8`, `MaybeUninit<u8>`, ...) of the
parent buffer: the `[sub_start, sub_end)` subslice is a sound typed subslice view inside
the parent window, and the returned offset is the one-past-the-end byte offset
(`WidePtrVal.elemOffset`) of the `sub_end - sub_start`-element window starting at
`base_offset`, itself a typed prefix view inside the parent. -/

section SliceLensCompanions

open Trusted.ITree
open Anneal.SepLogicLenses

/-- Every normal return of the captured MIR on `pre`-admissible arguments returns
`base_offset + (sub_end - sub_start)`, read off `verified`. -/
theorem ret_of_run {base len s e : Nat} (h_se : s ≤ e) (h_el : e ≤ len)
    (h_bound : base + len < 18446744073709551616) {tr ret mem'}
    (h_run : ReachesRet
      (mirStatefulTreeWithCallees Mir.FxfsStorageBoundary.vmo_subslice_bounds_valid.body
        [.scalar ⟨base, 8⟩, .scalar ⟨len, 8⟩, .scalar ⟨s, 8⟩, .scalar ⟨e, 8⟩] emptyMemory)
      tr (.normal (ret, mem'))) :
    ret = .scalar ⟨base + (e - s), 8⟩ := by
  have h_pre : Specs.FxfsStorageBoundary.vmo_subslice_bounds_valid.pre
      [.scalar ⟨base, 8⟩, .scalar ⟨len, 8⟩, .scalar ⟨s, 8⟩, .scalar ⟨e, 8⟩] :=
    ⟨base, len, s, e, h_se, h_el, h_bound, rfl⟩
  obtain ⟨_, h_spec⟩ := verified.proof _ emptyMemory ⟨h_pre, rfl⟩
  exact h_spec (tr, .normal (ret, mem')) h_run ⟨h_pre, rfl⟩ ret mem' rfl base len s e rfl

/-- **Subslice window of the verified bounds computation.** For every 1-byte codec `c` and
every typed view `SliceTypedAt c buf xs bytes` of the parent buffer
(`buf.1.offsetBytes = base_offset`, `buf.2 = buf_len`), any normal return yields an end
offset `end_off` such that
* the `[sub_start, sub_end)` subslice `takeElems (dropElems buf 1 sub_start) (sub_end - sub_start)`
  is a typed view of `(xs.drop sub_start).take (sub_end - sub_start)` with exactly
  `end_off - base_offset` elements, whose byte window lies inside the parent window; and
* `end_off = elemOffset buf 1 (sub_end - sub_start)` is the end of the window
  `takeElems buf (sub_end - sub_start)` (`[base_offset, end_off)`), a typed prefix view of
  the parent, and `end_off ≤ elemOffset buf 1 buf_len`. -/
theorem subslice_window_of_run {base len s e : Nat} (h_se : s ≤ e) (h_el : e ≤ len)
    (h_bound : base + len < 18446744073709551616) {tr ret mem'}
    (h_run : ReachesRet
      (mirStatefulTreeWithCallees Mir.FxfsStorageBoundary.vmo_subslice_bounds_valid.body
        [.scalar ⟨base, 8⟩, .scalar ⟨len, 8⟩, .scalar ⟨s, 8⟩, .scalar ⟨e, 8⟩] emptyMemory)
      tr (.normal (ret, mem')))
    {α : Type} {c : ByteLensCodec α 1} {buf : WidePtrVal} {xs : List α} {bytes : ByteMem}
    (h_buf : SliceTypedAt c buf xs bytes) (h_base : buf.1.offsetBytes = base)
    (h_len : buf.2 = len) :
    ∃ end_off : Nat,
      ret = .scalar ⟨end_off, 8⟩ ∧
      SliceTypedAt c (WidePtrVal.takeElems (WidePtrVal.dropElems buf 1 s) (e - s))
        ((xs.drop s).take (e - s)) bytes ∧
      (WidePtrVal.takeElems (WidePtrVal.dropElems buf 1 s) (e - s)).2 = end_off - base ∧
      buf.1.offsetBytes ≤ (WidePtrVal.dropElems buf 1 s).1.offsetBytes ∧
      (WidePtrVal.dropElems buf 1 s).1.offsetBytes + (e - s) * 1 ≤
        WidePtrVal.elemOffset buf 1 buf.2 ∧
      end_off = WidePtrVal.elemOffset buf 1 (e - s) ∧
      SliceTypedAt c (WidePtrVal.takeElems buf (e - s)) (xs.take (e - s)) bytes ∧
      end_off ≤ WidePtrVal.elemOffset buf 1 buf.2 := by
  have h_ret := ret_of_run h_se h_el h_bound h_run
  -- The subslice: drop `sub_start` elements, then keep `sub_end - sub_start`.
  obtain ⟨-, hDrop, -⟩ := SliceTypedAt.splitAt h_buf (k := s) (by omega)
  obtain ⟨hSub, -, -⟩ := SliceTypedAt.splitAt hDrop (k := e - s)
    (by rw [WidePtrVal.dropElems_snd]; omega)
  -- The re-based prefix window `[base_offset, base_offset + (sub_end - sub_start))`.
  obtain ⟨hPre, -, -⟩ := SliceTypedAt.splitAt h_buf (k := e - s) (by omega)
  refine ⟨base + (e - s), h_ret, hSub, by rw [WidePtrVal.takeElems_snd]; omega, ?_, ?_, ?_,
    hPre, ?_⟩
  · simp only [WidePtrVal.elemOffset]
    omega
  · simp only [WidePtrVal.elemOffset]
    omega
  · simp only [WidePtrVal.elemOffset]
    omega
  · simp only [WidePtrVal.elemOffset]
    omega

/-! ### Concrete instance: a real captured-MIR run on a buffer inside a 12-byte VMO -/

/-- The trusted MIR of `vmo_subslice_bounds_valid(4, 8, 2, 6)` reaches a normal return of
`4 + (6 - 2) = 8` (replayed by the kernel-checked `TraceCheck` trace reconstructor). -/
theorem run_4_8_2_6 : ∃ tr mem', ReachesRet
    (mirStatefulTreeWithCallees Mir.FxfsStorageBoundary.vmo_subslice_bounds_valid.body
      [.scalar ⟨4, 8⟩, .scalar ⟨8, 8⟩, .scalar ⟨2, 8⟩, .scalar ⟨6, 8⟩] emptyMemory)
    tr (.normal (.scalar ⟨8, 8⟩, mem')) := by
  obtain ⟨tr, out, -, h_out, h_reach⟩ :=
    Anneal.Rustc.V2026_06_01.TraceCheck.checkFullObservedTraceBounded_sound 16
      Mir.FxfsStorageBoundary.vmo_subslice_bounds_valid.body
      (initMachineStateWithMemoryAndCallees Mir.FxfsStorageBoundary.vmo_subslice_bounds_valid.body
        [.scalar ⟨4, 8⟩, .scalar ⟨8, 8⟩, .scalar ⟨2, 8⟩, .scalar ⟨6, 8⟩] emptyMemory [])
      [] (.normal (.scalar ⟨8, 8⟩)) (by decide)
  rcases out with ⟨rv, m⟩ | _ | _
  · exact ⟨tr, m, h_out ▸ h_reach⟩
  · exact (h_out : False).elim
  · exact (h_out : False).elim

/-- A 12-byte VMO image `[0, 1, ..., 11]` (allocation `3`). -/
def vmoBytes : ByteMem :=
  ByteLensCodec.encodeElems ByteLensCodec.u8 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- The whole-VMO `u8` view through the 12-element wide pointer at `⟨3, 0⟩`. -/
theorem vmo_view :
    SliceTypedAt ByteLensCodec.u8 (WidePtrVal.mk ⟨3, 0⟩ 12)
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] vmoBytes :=
  sliceTypedAt_encodeElems ByteLensCodec.u8 3 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- The 8-byte parent buffer `[4, 12)` of the VMO, carved out with `dropElems`. -/
theorem buf_view :
    SliceTypedAt ByteLensCodec.u8 (WidePtrVal.dropElems (WidePtrVal.mk ⟨3, 0⟩ 12) 1 4)
      [4, 5, 6, 7, 8, 9, 10, 11] vmoBytes :=
  (SliceTypedAt.splitAt vmo_view (k := 4) (by decide)).2.1

/-- On the concrete run, the subslice `[2, 6)` of the parent buffer at VMO offset `4` is the
view `[6, 7, 8, 9]` at byte `6`, and the returned end offset `8` closes the 4-element
window `[4, 8)` holding `[4, 5, 6, 7]`. -/
theorem demo_subslice :
    SliceTypedAt ByteLensCodec.u8 (WidePtrVal.mk ⟨3, 6⟩ 4) [6, 7, 8, 9] vmoBytes ∧
      SliceTypedAt ByteLensCodec.u8 (WidePtrVal.mk ⟨3, 4⟩ 4) [4, 5, 6, 7] vmoBytes ∧
      (8 : Nat) ≤ 12 := by
  obtain ⟨tr, mem', h_run⟩ := run_4_8_2_6
  obtain ⟨end_off, h_ret, hSub, -, -, -, h_end, hPre, h_in⟩ :=
    subslice_window_of_run (by decide) (by decide) (by decide) h_run buf_view rfl rfl
  simp only [Value.scalar.injEq, Trusted.Rustc.V2026_06_01.MirAst.ScalarInt.mk.injEq,
    and_true] at h_ret
  subst h_ret
  exact ⟨hSub, hPre, h_in⟩

/-! ### The trusted MIR subslice borrow `&(*buf)[sub_start..sub_end]` -/

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.Layout

/-- **Trusted `&(*buf)[sub_start..sub_end]` of the verified range.** For a `u8` parent
buffer over a captured global allocation `alloc`, the length metadata of the fat pointer
that the trusted `evalSliceFatPtrDerefBorrow` produces for the subslice projection
`[sub_start..sub_end]` of the parent fat pointer is exactly `end_off - base_offset` for the
end offset `end_off` of any normal return; the borrowed subslice starts at
`elemPtr buf 1 sub_start` and carries the typed view `(xs.drop sub_start).take (sub_end - sub_start)`
of the allocation's trusted byte image. -/
theorem subsliceBorrow_of_run {base len s e : Nat} (h_se : s ≤ e) (h_el : e ≤ len)
    (h_bound : base + len < 18446744073709551616) {tr ret mem'}
    (h_run : ReachesRet
      (mirStatefulTreeWithCallees Mir.FxfsStorageBoundary.vmo_subslice_bounds_valid.body
        [.scalar ⟨base, 8⟩, .scalar ⟨len, 8⟩, .scalar ⟨s, 8⟩, .scalar ⟨e, 8⟩] emptyMemory)
      tr (.normal (ret, mem')))
    {buf : WidePtrVal} {xs : List UInt8} {alloc : CapturedAllocation}
    (h_buf : SliceTypedAt ByteLensCodec.u8 buf xs (globalAllocByteMem alloc))
    (h_len : buf.2 = len)
    (locals : List LocalSlot) (mem : Memory) (perm : TreeBorrowPerm) (isMut : Bool)
    (elemKind : RigidTy) (pIdx : LayoutIdx) (layouts : LayoutTable) (checkPerm : Bool)
    (localDecls : List LocalDecl) (accessedTyOpt : Option Ty) (checkResultRefAlign : Bool)
    (hNoBorrow : lookupBorrow mem.borrows buf.1.tag = none)
    (hAlloc : lookupGlobalAlloc mem.globals buf.1.allocId = some alloc)
    (hMut : isMut = true → alloc.mutability = .mut)
    (hSz : tyByteSize .nil layouts
      { kind := elemKind,
        layoutIdx := match LayoutTable.lookup layouts pIdx with
          | some { fieldLayouts := flIdx :: _, .. } => flIdx
          | _ => unresolvedLayoutIdx layouts } = some 1) :
    ∃ end_off : Nat,
      ret = .scalar ⟨end_off, 8⟩ ∧
      evalSliceFatPtrDerefBorrow locals mem buf.1 (layoutPointerBytes layouts)
          ⟨buf.2, layoutPointerBytes layouts⟩ [.subslice s e false] perm isMut
          (some { kind := .slice elemKind, layoutIdx := pIdx }) layouts checkPerm localDecls
          accessedTyOpt checkResultRefAlign =
        .ok (WidePtrVal.toValue (layoutPointerBytes layouts)
            (WidePtrVal.mk (WidePtrVal.elemPtr buf 1 s) (end_off - base))) locals mem ∧
      SliceTypedAt ByteLensCodec.u8 (WidePtrVal.mk (WidePtrVal.elemPtr buf 1 s) (end_off - base))
        ((xs.drop s).take (e - s)) (globalAllocByteMem alloc) := by
  have h_ret := ret_of_run h_se h_el h_bound h_run
  obtain ⟨h_eval, h_view⟩ := SliceTypedAt.evalSliceFatPtrDerefBorrow_subslice h_buf locals mem
    perm isMut elemKind pIdx layouts checkPerm localDecls accessedTyOpt checkResultRefAlign s e
    h_se (by omega) hNoBorrow hAlloc hMut hSz
  have h_sub : base + (e - s) - base = e - s := by omega
  refine ⟨base + (e - s), h_ret, ?_, ?_⟩
  · rw [h_sub]
    exact h_eval
  · rw [h_sub]
    exact h_view

/-- The 12-byte VMO as a captured immutable global allocation (allocation `3`). -/
def vmoAlloc : CapturedAllocation :=
  { allocId := 3
    bytes := [some 0, some 1, some 2, some 3, some 4, some 5, some 6, some 7, some 8, some 9,
              some 10, some 11]
    relocations := []
    align := { bytes := 1 }
    mutability := .not }

/-- The `u8` type layout. -/
def u8Layout : TypeLayout :=
  { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := .memory,
    fields := .primitive, variants := .single 0, isUninhabited := false, fieldLayouts := [] }

/-- A 64-bit layout table whose entry `0` is `u8`. -/
def u8Layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [u8Layout] }

/-- The trusted byte image of `vmoAlloc` is the VMO image `vmoBytes`, so the parent buffer
view is a view of the live global. -/
theorem buf_view_global :
    SliceTypedAt ByteLensCodec.u8 (WidePtrVal.dropElems (WidePtrVal.mk ⟨3, 0⟩ 12) 1 4)
      [4, 5, 6, 7, 8, 9, 10, 11] (globalAllocByteMem vmoAlloc) :=
  buf_view

/-- On the concrete run, the trusted MIR borrow `&(*buf)[2..6]` of the parent fat pointer
`(⟨3, 4⟩, 8)` evaluates to the fat pointer `(⟨3, 6⟩, 4)`, whose length `4` is the returned
end offset `8` minus `base_offset = 4`. -/
theorem demo_subslice_borrow :
    evalSliceFatPtrDerefBorrow [] { globals := [vmoAlloc] } ⟨3, 4⟩ 8 ⟨8, 8⟩
        [.subslice 2 6 false] .frozen false (some { kind := .slice (.uint .u8), layoutIdx := 0 })
        u8Layouts true [] none false =
      .ok (WidePtrVal.toValue 8 (WidePtrVal.mk ⟨3, 6⟩ 4)) [] { globals := [vmoAlloc] } := by
  obtain ⟨tr, mem', h_run⟩ := run_4_8_2_6
  obtain ⟨end_off, h_ret, h_eval, -⟩ :=
    subsliceBorrow_of_run (by decide) (by decide) (by decide) h_run buf_view_global rfl
      [] { globals := [vmoAlloc] } .frozen false (.uint .u8) 0 u8Layouts true [] none false
      rfl rfl (fun h => by cases h) rfl
  simp only [Value.scalar.injEq, Trusted.Rustc.V2026_06_01.MirAst.ScalarInt.mk.injEq,
    and_true] at h_ret
  subst h_ret
  exact h_eval

end SliceLensCompanions

end Proof.FxfsStorageBoundary.vmo_subslice_bounds_valid
