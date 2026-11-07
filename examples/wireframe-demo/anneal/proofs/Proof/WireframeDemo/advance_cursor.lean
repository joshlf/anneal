import Trusted
import Anneal
import Mir.WireframeDemo.advance_cursor
import Specs.WireframeDemo.advance_cursor
import Obligations.WireframeDemo.advance_cursor

namespace Proof.WireframeDemo.advance_cursor

set_option maxRecDepth 8192
set_option maxHeartbeats 400000

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Scalars
open Anneal.UnsafeObligations
open Anneal.SepLogic
open Anneal.SepLogicLenses
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Specs.WireframeDemo.advance_cursor

/-- Separation-logic lens pointer for the caller-frame `FrameCursor` slot. -/
abbrev cursorRp : RawPtrVal :=
  { allocId := cursorSlotIdx, offset := 0, tag := 1 }

/-- Spine-normalizer for `List LocalSlot` so `set?_of_forceEnv rfl` unifies metavariables
    with flat `[.uninit, .init _, ...]` lists instead of unreduced `List.set` chains. -/
private def forceEnv : List LocalSlot → Option (List LocalSlot)
  | [] => some []
  | .uninit :: tl =>
    match forceEnv tl with
    | some tl' => some (.uninit :: tl')
    | none => none
  | .dead :: tl =>
    match forceEnv tl with
    | some tl' => some (.dead :: tl')
    | none => none
  | .init v :: tl =>
    match forceEnv tl with
    | some tl' => some (.init v :: tl')
    | none => none

private theorem forceEnv_eq_some (env : List LocalSlot) : forceEnv env = some env := by
  induction env with
  | nil => rfl
  | cons hd tl ih => cases hd <;> simp [forceEnv, ih]

private theorem set?_of_forceEnv {env env' : List LocalSlot} {loc : Local} {s : LocalSlot}
    (h : (set? env loc s).bind forceEnv = some env') :
    set? env loc s = some env' := by
  cases hSet : set? env loc s with
  | none => rw [hSet] at h; nomatch h
  | some e =>
    rw [hSet, Option.bind_some, forceEnv_eq_some] at h
    exact h

private theorem cursor_sepLensStateInv
    (offset limit : Nat) (mem : Memory)
    (h_callee : mem.activeCallee = .none)
    (h_stack : mem.callStack = .nil)
    (h_borrows : mem.borrows = [activeCursorBorrow rootCursorPtr])
    (h_caller : mem.callerLocals = cursorCallerLocals offset limit) :
    SepLensStateInv cursorSlotIdx [(cursorRp, cursorValue offset limit)] mem where
  callStack_nil := h_stack
  activeCallee_none := h_callee
  borrows_above_frame b hb := by
    rw [h_borrows] at hb
    rcases List.mem_singleton.mp hb with rfl
    decide
  entries_valid rp v hMem := by
    rcases List.mem_singleton.mp hMem with hEq
    injection hEq with hRp hV
    subst hRp hV
    refine ⟨rfl, Nat.le_refl _, ?_, ?_⟩
    · rw [h_caller]; rfl
    · refine ⟨rfl, ⟨activeCursorBorrow rootCursorPtr, ?_, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
      · rw [h_borrows]; rfl
      · intro b hb _
        rw [h_borrows] at hb
        rcases List.mem_singleton.mp hb with rfl
        rw [h_borrows]
        exact Or.inl ⟨rfl, rfl⟩
  pairwise_disjoint := List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil

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
  have h_ble_inv : Nat.ble offset limit = true := Nat.ble_eq_true_of_le h_inv
  have h_sub_wrap : wrapScalarBits (Nat.sub limit offset) (scalarModulus 2) = limit - offset :=
    wrapScalarBits_eq_of_lt (by change limit - offset < 65536; omega)
  -- bb0: read limit & offset through `cursorRp`, checked sub `limit - offset`, assert no overflow
  apply LiftLensBlock.assert (sc := ⟨0, 1⟩)
  · rfl
  · rfl
  · rfl
  · iterate 7 (apply LiftLensStmts.cons; · exact .storageLive (.mk rfl (set?_of_forceEnv rfl)))
    apply LiftLensStmts.cons
    · exact .pureAssign (.mk (.use_deref_field (.copy_deref_field (rp := cursorRp) rfl rfl rfl)) rfl (fun h => nomatch h) (set?_of_forceEnv rfl))
    apply LiftLensStmts.cons
    · exact .pureAssign (.mk (.use_deref_field (.copy_deref_field (rp := cursorRp) rfl rfl rfl)) rfl (fun h => nomatch h) (set?_of_forceEnv rfl))
    apply LiftLensStmts.cons
    · exact .pureAssign (.mk (.binaryOp (v := .aggregate 0 [.scalar ⟨limit - offset, 2⟩, .scalar ⟨0, 1⟩])
        (.pure (.copy_local rfl)) (.pure (.copy_local rfl))
        (fun _ => by
          change (match Nat.ble offset limit with
            | true => RvalueEvalResult.ok
                (Value.aggregate 0
                  [Value.scalar { bits := wrapScalarBits (Nat.sub limit offset) (scalarModulus 2), sizeBytes := 2 },
                   Value.scalar { bits := 0, sizeBytes := 1 }]) _ _
            | false => _) = _
          rw [h_ble_inv, h_sub_wrap])) rfl (fun h => nomatch h) (set?_of_forceEnv rfl))
    exact .nil
  · exact .pure (.move_field rfl rfl)
  · rfl
  · -- bb1: `_3 = move (_6.0); _7 = Le(copy _2, copy _3); switchInt(move _7)`
    by_cases h_le : step ≤ limit - offset
    · have h_ble_step : Nat.ble step (limit - offset) = true := Nat.ble_eq_true_of_le h_le
      have h_no_ovf : Nat.ble (scalarModulus 2) (Nat.add offset step) = false := by
        cases h_ovf : Nat.ble (scalarModulus 2) (Nat.add offset step)
        · rfl
        · have : 65536 ≤ offset + step := Nat.le_of_ble_eq_true h_ovf
          omega
      have h_add_wrap : wrapScalarBits (Nat.add offset step) (scalarModulus 2) = offset + step :=
        wrapScalarBits_eq_of_lt (by change offset + step < 65536; omega)
      simp only [h_le, ↓reduceIte]
      apply LiftLensBlock.switchInt (target := 2)
      · rfl
      · rfl
      · rfl
      · apply LiftLensStmts.cons
        · exact .pureAssign (.mk (.use_pure (.move_field rfl rfl)) rfl (fun h => nomatch h) (set?_of_forceEnv rfl))
        apply LiftLensStmts.cons
        · exact .pureAssign (.mk (.binaryOp (.pure (.copy_local rfl)) (.pure (.copy_local rfl)) (fun _ => rfl)) rfl (fun h => nomatch h) (set?_of_forceEnv rfl))
        exact .nil
      · exact .pure (.move_local rfl (set?_of_forceEnv rfl))
      · change lookupSwitchTarget (boolToScalar (Nat.ble step (limit - offset))).bits [(0, 4)] 2 = 2
        rw [h_ble_step]; rfl
      · -- bb2: `_8 = copy ((*_1).0); _9 = AddWithOverflow(copy _8, copy _2); assert(!move (_9.1))`
        apply LiftLensBlock.assert (sc := ⟨0, 1⟩)
        · rfl
        · rfl
        · rfl
        · apply LiftLensStmts.cons
          · exact .pureAssign (.mk (.use_deref_field (.copy_deref_field (rp := cursorRp) rfl rfl rfl)) rfl (fun h => nomatch h) (set?_of_forceEnv rfl))
          apply LiftLensStmts.cons
          · exact .pureAssign (.mk (.binaryOp (v := .aggregate 0 [.scalar ⟨offset + step, 2⟩, .scalar ⟨0, 1⟩])
              (.pure (.copy_local rfl)) (.pure (.copy_local rfl))
              (fun _ => by
                change RvalueEvalResult.ok
                  (Value.aggregate 0
                    [Value.scalar { bits := wrapScalarBits (Nat.add offset step) (scalarModulus 2), sizeBytes := 2 },
                     Value.scalar { bits := match Nat.ble (scalarModulus 2) (Nat.add offset step) with
                        | true => 1
                        | false => 0, sizeBytes := 1 }]) _ _ = _
                rw [h_no_ovf, h_add_wrap])) rfl (fun h => nomatch h) (set?_of_forceEnv rfl))
          exact .nil
        · exact .pure (.move_field rfl rfl)
        · rfl
        · -- bb3: `((*_1).0) = move (_9.0); _0 = const true; goto -> bb5`
          apply LiftLensBlock.goto (target := 5)
          · rfl
          · rfl
          · rfl
          · apply LiftLensStmts.cons
            · exact .derefWrite (.field
                (.use_pure (.move_field rfl rfl))
                (rp := cursorRp) rfl rfl rfl)
            apply LiftLensStmts.cons
            · exact .pureAssign (.mk (.use_pure .const_scalar) rfl (fun h => nomatch h) (set?_of_forceEnv rfl))
            exact .nil
          · -- bb5: `return`
            exact LiftLensBlock.return_ rfl rfl rfl .nil rfl
    · have h_ble_step : Nat.ble step (limit - offset) = false := by
        cases h_b : Nat.ble step (limit - offset)
        · rfl
        · exact False.elim (h_le (Nat.le_of_ble_eq_true h_b))
      simp only [h_le, ↓reduceIte]
      apply LiftLensBlock.switchInt (target := 4)
      · rfl
      · rfl
      · rfl
      · apply LiftLensStmts.cons
        · exact .pureAssign (.mk (.use_pure (.move_field rfl rfl)) rfl (fun h => nomatch h) (set?_of_forceEnv rfl))
        apply LiftLensStmts.cons
        · exact .pureAssign (.mk (.binaryOp (.pure (.copy_local rfl)) (.pure (.copy_local rfl)) (fun _ => rfl)) rfl (fun h => nomatch h) (set?_of_forceEnv rfl))
        exact .nil
      · exact .pure (.move_local rfl (set?_of_forceEnv rfl))
      · change lookupSwitchTarget (boolToScalar (Nat.ble step (limit - offset))).bits [(0, 4)] 2 = 4
        rw [h_ble_step]; rfl
      · -- bb4: `_0 = const false; goto -> bb5`
        apply LiftLensBlock.goto (target := 5)
        · rfl
        · rfl
        · rfl
        · apply LiftLensStmts.cons
          · exact .pureAssign (.mk (.use_pure .const_scalar) rfl (fun h => nomatch h) (set?_of_forceEnv rfl))
          exact .nil
        · -- bb5: `return`
          exact LiftLensBlock.return_ rfl rfl rfl .nil rfl

/-- Stateful verification certificate for `wireframe_demo::advance_cursor` via `SepLogicLenses`. -/
theorem verified :
    StatefulVerificationResult Obligations.WireframeDemo.advance_cursor.statefulClaim := by
  refine verifyStatefulMir_of_sepLenses
    Mir.WireframeDemo.advance_cursor.body
    Obligations.WireframeDemo.advance_cursor.statefulClaim.pre
    Obligations.WireframeDemo.advance_cursor.statefulClaim.post ?_
  intro args mem h_pre
  rcases h_pre with
    ⟨_, offset, limit, step, h_inv, h_lim, _, h_args,
     h_callee, h_stack, _, h_borrows, h_caller⟩
  subst h_args
  let newOffset := if step ≤ limit - offset then offset + step else offset
  let retBit := if step ≤ limit - offset then 1 else 0
  refine ⟨[(cursorRp, cursorValue offset limit)],
    [(cursorRp, cursorValue newOffset limit)],
    .scalar ⟨retBit, 1⟩,
    advance_cursor_lift offset limit step h_inv h_lim,
    cursor_sepLensStateInv offset limit mem h_callee h_stack h_borrows h_caller,
    ?_⟩
  intro m_final hInv _
  refine ⟨trivial, ?_⟩
  intro offset' limit' step' _ _ _ h_args_eq h_caller_eq
  injection h_args_eq with _ h_a1
  injection h_a1 with h_s1 _
  injection h_s1 with h_sc1
  injection h_sc1 with h_step_eq _
  have h_slot : get? mem.callerLocals cursorSlotIdx = get? (cursorCallerLocals offset' limit') cursorSlotIdx :=
    congrArg (fun xs => get? xs cursorSlotIdx) h_caller_eq
  rw [h_caller] at h_slot
  dsimp only [cursorCallerLocals, cursorSlotIdx, cursorValue, get?,
    HAppend.hAppend, instHAppendOfAppend, Append.append, List.instAppend,
    List.replicate, List.append] at h_slot
  injection h_slot with h_init
  injection h_init with h_agg
  injection h_agg with _ h_fields
  injection h_fields with h_f0 h_f1
  injection h_f1 with h_f1_hd _
  injection h_f0 with h_off_sc
  injection h_off_sc with h_off_eq _
  injection h_f1_hd with h_lim_sc
  injection h_lim_sc with h_lim_eq _
  subst h_step_eq h_off_eq h_lim_eq
  rcases hInv.entries_valid cursorRp (cursorValue newOffset limit) (List.Mem.head _) with
    ⟨_, _, h_final_caller, _⟩
  refine ⟨?_, rfl, h_final_caller⟩
  show (if step ≤ limit - offset then offset + step else offset) ≤ limit
  split <;> omega

end Proof.WireframeDemo.advance_cursor
