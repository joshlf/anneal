import Trusted
import Anneal
import Mir.WireframeDemo.advance_cursor
import Specs.WireframeDemo.advance_cursor
import Obligations.WireframeDemo.advance_cursor

namespace Proof.WireframeDemo.advance_cursor

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Scalars
open Anneal.UnsafeObligations
open Anneal.SepLogic
open Anneal.SepLogicLenses
open Anneal.MirLiftCore
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Specs.WireframeDemo.advance_cursor

/-- Separation-logic lens pointer for the caller-frame `FrameCursor` slot. -/
abbrev cursorRp : RawPtrVal :=
  { allocId := cursorSlotIdx, offset := 0, tag := 1 }

/-- Lens-state derivation of `advance_cursor` across both `switchInt` outcomes
(`bb0 → bb1 → bb2 → bb3 → bb5` when `step ≤ limit - offset`, otherwise
`bb0 → bb1 → bb4 → bb5`), lifting every basic block exactly once. -/
private theorem advance_cursor_lift
    (offset limit step : Nat)
    (h_inv : offset ≤ limit) (h_lim : limit < 65536) :
    LiftLensBlock Mir.WireframeDemo.advance_cursor.body 0
      (initMachineState Mir.WireframeDemo.advance_cursor.body
        [.ptr rootCursorPtr 8, .scalar ⟨step, 2⟩]).frame.locals
      [(cursorRp, cursorValue offset limit)]
      (.scalar ⟨if step ≤ limit - offset then 1 else 0, 1⟩)
      [(cursorRp,
        cursorValue (if step ≤ limit - offset then offset + step else offset) limit)] := by
  have h_sub_wrap : wrapScalarBits (Nat.sub limit offset) (scalarModulus 2) = limit - offset :=
    wrapScalarBits_eq_of_lt (by change limit - offset < 65536; omega)
  -- bb0: `StorageLive(_3..=_9); _4 = copy ((*_1).1); _5 = copy ((*_1).0);
  -- _6 = SubWithOverflow(copy _4, copy _5); assert(!move (_6.1)) -> bb1`
  apply LiftLensBlock.assert (sc := ⟨0, 1⟩) rfl rfl rfl
  · repeat apply LiftLensStmts.cons (.storageLive (.mk rfl (set?_of_setSpineChecked? rfl)))
    apply LiftLensStmts.cons (.pureAssign_uninit_checked
      (.use_deref_field (.copy_deref_field (rp := cursorRp) rfl rfl rfl) rfl) rfl rfl)
    apply LiftLensStmts.cons (.pureAssign_uninit_checked
      (.use_deref_field (.copy_deref_field (rp := cursorRp) rfl rfl rfl) rfl) rfl rfl)
    exact .cons (.pureAssign_uninit_checked (.binaryOp
      (v := .aggregate 0 [.scalar ⟨limit - offset, 2⟩, .scalar ⟨0, 1⟩])
      (.pure (.copy_local rfl)) (.pure (.copy_local rfl)) (fun _ => by
        change (match Nat.ble offset limit with | true => _ | false => _) = _
        rw [Nat.ble_eq_true_of_le h_inv, h_sub_wrap])) rfl rfl) .nil
  · exact .pure (.move_field rfl rfl rfl)
  · rfl
  -- bb1: `_3 = move (_6.0); _7 = Le(copy _2, copy _3);
  -- switchInt(move _7) -> [0: bb4, otherwise: bb2]`, lifted once for both outcomes.
  apply LiftLensBlock.switchInt (target := if step ≤ limit - offset then 2 else 4) rfl rfl rfl
  · apply LiftLensStmts.cons
      (.pureAssign_uninit_checked (.use_pure (.move_field rfl rfl rfl) rfl) rfl rfl)
    exact .cons (.pureAssign_uninit_checked
      (.binaryOp (.pure (.copy_local rfl)) (.pure (.copy_local rfl)) (fun _ => rfl)) rfl rfl) .nil
  · exact .pure (.move_local rfl (set?_of_setSpineChecked? rfl))
  · by_cases h_le : step ≤ limit - offset
    · rw [Nat.ble_eq_true_of_le h_le, ite_eq_left h_le]; rfl
    · rw [(nat_ble_eq_false_iff _ _).2 (Nat.lt_of_not_le h_le), ite_eq_right h_le]; rfl
  by_cases h_le : step ≤ limit - offset
  · simp only [h_le, ↓reduceIte]
    have h_add : offset + step < scalarModulus 2 := by change offset + step < 65536; omega
    -- bb2: `_8 = copy ((*_1).0); _9 = AddWithOverflow(copy _8, copy _2);
    -- assert(!move (_9.1)) -> bb3`
    apply LiftLensBlock.assert (sc := ⟨0, 1⟩) rfl rfl rfl
    · apply LiftLensStmts.cons (.pureAssign_uninit_checked
        (.use_deref_field (.copy_deref_field (rp := cursorRp) rfl rfl rfl) rfl) rfl rfl)
      exact .cons (.pureAssign_uninit_checked (.binaryOp
        (v := .aggregate 0 [.scalar ⟨offset + step, 2⟩, .scalar ⟨0, 1⟩])
        (.pure (.copy_local rfl)) (.pure (.copy_local rfl)) (fun _ => by
          change RvalueEvalResult.ok (.aggregate 0
            [.scalar ⟨wrapScalarBits (offset + step) _, 2⟩,
             .scalar ⟨match Nat.ble _ (offset + step) with | true => 1 | false => 0, 1⟩]) _ _ = _
          rw [(nat_ble_eq_false_iff _ _).2 h_add, wrapScalarBits_eq_of_lt h_add])) rfl rfl) .nil
    · exact .pure (.move_field rfl rfl rfl)
    · rfl
    -- bb3: `((*_1).0) = move (_9.0); _0 = const true; goto -> bb5`
    exact .goto_return rfl rfl rfl (.cons
      (.derefWrite (.field (.use_pure (.move_field rfl rfl rfl) rfl) (rp := cursorRp) rfl rfl rfl))
      (.cons (.pureAssign_uninit_checked (.use_pure .const_scalar rfl) rfl rfl) .nil))
      rfl rfl rfl rfl
  · simp only [h_le, ↓reduceIte]
    -- bb4: `_0 = const false; goto -> bb5`
    exact .goto_return rfl rfl rfl
      (.cons (.pureAssign_uninit_checked (.use_pure .const_scalar rfl) rfl rfl) .nil)
      rfl rfl rfl rfl

/-- Stateful verification certificate for `wireframe_demo::advance_cursor`
via `SepLogicLenses`. -/
theorem verified :
    StatefulVerificationResult Obligations.WireframeDemo.advance_cursor.statefulClaim := by
  refine verifyStatefulMir_of_sepLenses
    Mir.WireframeDemo.advance_cursor.body
    Obligations.WireframeDemo.advance_cursor.statefulClaim.pre
    Obligations.WireframeDemo.advance_cursor.statefulClaim.post ?_
  intro args mem h_pre
  rcases h_pre with
    ⟨_, offset, limit, step, h_inv, h_lim, _, rfl,
     h_callee, h_stack, _, h_borrows, h_caller⟩
  refine ⟨_, _, _, advance_cursor_lift offset limit step h_inv h_lim,
    sepLensStateInv_single_root_borrow h_stack h_callee h_borrows rfl rfl rfl rfl rfl rfl rfl rfl
      (Nat.le_refl _) (by rw [h_caller]; rfl),
    fun m_final hInv _ => ⟨trivial, ?_⟩⟩
  rintro offset' limit' step' - - - ⟨⟩ h_caller'
  cases h_caller.symm.trans h_caller'
  exact ⟨by split <;> omega, rfl, (hInv.entries_valid _ _ (List.Mem.head _)).2.2.1⟩

end Proof.WireframeDemo.advance_cursor
