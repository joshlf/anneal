import Trusted
import Anneal.ITreeWP
import Anneal.Rustc.V2026_06_01.Lower
import Anneal.Rustc.V2026_06_01.SymbolicEval

namespace Anneal.Rustc.V2026_06_01.SymbolicEval

open Trusted.Refinement
open Trusted.Sequence
open Trusted.Effect
open Trusted.ITree
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Scalars
open Anneal.ITreeWP
open Anneal.Rustc.V2026_06_01.Lower

/-!
# Closed-Term Symbolic Precondition Pinning & Bitwise Byte-Swap Lemmas

1. **Closed-Term `checkMirRequiresPinsScalars` (`rfl` Reflection)**:
   Verifies in closed-term kernel reduction (`:= by rfl`) that a `#[spec]`
   `requires` companion MIR body pins its scalar parameters to concrete
   `(bits, sizeBytes)` constants, powering `dischargeRustEqScalar1`,
   `dischargeRustEqScalar2`, and width-specialized aliases
   (`dischargeRustEqU8`..`dischargeRustEq2U64`) without open-term `whnf`
   unfolding over symbolic widths.
2. **Bitwise Masking, Byte-Swapping, and `UInt8.ofNat` `@[simp]` Lemmas**:
   Collapses `bitwiseAndBits`, `bitwiseOrBits`, and `(UInt8.ofNat b).toBitVec.toNat`
   symbolically without 16-bit or 32-bit recursive bit-blasting.
-/

section PinChecker

private def dropValues : Nat → List Value → List Value
  | .zero, xs => xs
  | .succ _, .nil => .nil
  | .succ n, _ :: xs => dropValues n xs
def WellTypedScalars : List Nat → List Value → Prop
  | .nil, .nil => True
  | w :: ws, .scalar sc :: vs =>
    sc.sizeBytes = w ∧
      Nat.ble (scalarModulus w) sc.bits = false ∧
      WellTypedScalars ws vs
  | _, _ => False


/-- Abstract local slot tracking either a concrete `LocalSlot` or a symbolic
input argument `.symArg idx` (`args[idx]`). -/
inductive SymSlot : Type where
  | concrete : LocalSlot → SymSlot
  | symArg : Nat → SymSlot

/-- Abstract rvalue/operand value tracking either a concrete `Value` or a
symbolic input argument `.symArg idx` (`args[idx]`). -/
inductive SymVal : Type where
  | concrete : Value → SymVal
  | symArg : Nat → SymVal

/-- Concretize a `SymSlot` against concrete argument list `args`. -/
def concretizeSymSlot (args : List Value) : SymSlot → LocalSlot
  | .concrete slot => slot
  | .symArg idx =>
    match get? args idx with
    | .some v => .init v
    | .none => .uninit

/-- Concretize a `List SymSlot` against concrete argument list `args`. -/
def concretizeSymSlots (args : List Value) : List SymSlot → List LocalSlot
  | .nil => .nil
  | s :: rest => concretizeSymSlot args s :: concretizeSymSlots args rest

/-- Initialize `List SymSlot` for parameter and temporary declarations `decls`
starting at argument index `argIdx` with `remArgs` remaining arguments. -/
def initSymSlotsParams : Nat → Nat → List LocalDecl → List SymSlot
  | _, _, .nil => .nil
  | argIdx, .zero, _ :: decls =>
    .concrete .dead :: initSymSlotsParams argIdx .zero decls
  | argIdx, .succ rem, _ :: decls =>
    .symArg argIdx :: initSymSlotsParams (.succ argIdx) rem decls

/-- Initialize `List SymSlot` for `body.localDecls` with `argCount` input
arguments: local `0` starts `.uninit`, locals `1..=argCount` start as
`.symArg 0 .. .symArg (argCount - 1)`, and locals `> argCount` start `.dead`. -/
def initSymSlots (decls : List LocalDecl) (argCount : Nat) : List SymSlot :=
  match decls with
  | .nil => .nil
  | _ :: restDecls => .concrete .uninit :: initSymSlotsParams 0 argCount restDecls

theorem get?_eq_head_dropValues :
    ∀ (args : List Value) (idx : Nat),
      get? args idx =
        match dropValues idx args with
        | v :: _ => .some v
        | .nil => .none
  | .nil, .zero => rfl
  | .nil, .succ _ => rfl
  | _ :: _, .zero => rfl
  | _ :: rest, .succ idx => get?_eq_head_dropValues rest idx

theorem dropValues_succ_of_cons :
    ∀ (args : List Value) (idx : Nat) (v : Value) (restArgs : List Value),
      dropValues idx args = v :: restArgs →
      dropValues (.succ idx) args = restArgs
  | .nil, .zero, _, _, h => nomatch h
  | .nil, .succ _, _, _, h => nomatch h
  | _ :: _, .zero, _, _, h => by
    injection h
  | _ :: tail, .succ idx, v, restArgs, h =>
    dropValues_succ_of_cons tail idx v restArgs h

theorem initLocalsAux_succ_irrel :
    ∀ (decls : List LocalDecl) (xs : List Value) (i j : Nat),
      initLocalsAux (.succ i) decls xs = initLocalsAux (.succ j) decls xs
  | .nil, _, _, _ => rfl
  | _ :: decls, .nil, i, j => by
    dsimp only [initLocalsAux]
    rw [initLocalsAux_succ_irrel decls .nil i j]
  | _ :: decls, _ :: rest, i, j => by
    dsimp only [initLocalsAux]
    rw [initLocalsAux_succ_irrel decls rest i j]

theorem concretizeSymSlots_initSymSlotsParams_zero
    (args : List Value) :
    ∀ (decls : List LocalDecl) (idx : Nat),
      concretizeSymSlots args (initSymSlotsParams idx .zero decls) =
        initLocalsAux (.succ idx) decls .nil
  | .nil, _ => rfl
  | _ :: decls, idx => by
    dsimp only [initSymSlotsParams, concretizeSymSlots, concretizeSymSlot, initLocalsAux]
    rw [concretizeSymSlots_initSymSlotsParams_zero args decls idx]

theorem concretizeSymSlots_initSymSlotsParams
    (args : List Value) :
    ∀ (decls : List LocalDecl) (remArgs : List Value) (idx : Nat),
      dropValues idx args = remArgs →
      concretizeSymSlots args (initSymSlotsParams idx (length remArgs) decls) =
        initLocalsAux (.succ idx) decls remArgs
  | .nil, _, _, _ => rfl
  | _ :: decls, .nil, idx, _ => by
    dsimp only [length, List.length, initSymSlotsParams, concretizeSymSlots, concretizeSymSlot, initLocalsAux]
    rw [concretizeSymSlots_initSymSlotsParams_zero args decls idx]
  | _ :: decls, v :: restArgs, idx, hDrop => by
    dsimp only [length, List.length, initSymSlotsParams, concretizeSymSlots, concretizeSymSlot, initLocalsAux]
    rw [get?_eq_head_dropValues args idx, hDrop]
    have hNext := dropValues_succ_of_cons args idx v restArgs hDrop
    have hRec := concretizeSymSlots_initSymSlotsParams args decls restArgs (.succ idx) hNext; dsimp only [length] at hRec; dsimp only; rw [hRec]
    rw [initLocalsAux_succ_irrel decls restArgs (.succ idx) idx]

theorem concretizeSymSlots_initSymSlots
    (args : List Value)
    (decls : List LocalDecl)
    (argCount : Nat)
    (h_len : length args = argCount) :
    concretizeSymSlots args (initSymSlots decls argCount) = initLocalsAux 0 decls args := by
  subst h_len
  cases decls with
  | nil => rfl
  | cons _ restDecls =>
    dsimp only [initSymSlots, concretizeSymSlots, concretizeSymSlot, initLocalsAux]
    rw [concretizeSymSlots_initSymSlotsParams args restDecls args 0 rfl]

theorem get?_concretizeSymSlots
    (args : List Value) :
    ∀ (slots : List SymSlot) (idx : Nat),
      get? (concretizeSymSlots args slots) idx =
        match get? slots idx with
        | .some s => .some (concretizeSymSlot args s)
        | .none => .none
  | .nil, _ => rfl
  | _ :: _, .zero => rfl
  | _ :: rest, .succ idx => get?_concretizeSymSlots args rest idx

private theorem concretizeSymSlots_length (args : List Value) :
    ∀ (slots : List SymSlot), (concretizeSymSlots args slots).length = slots.length
  | .nil => rfl
  | _ :: rest => congrArg Nat.succ (concretizeSymSlots_length args rest)

private theorem concretizeSymSlots_set (args : List Value) (s : SymSlot) :
    ∀ (slots : List SymSlot) (idx : Nat),
      (concretizeSymSlots args slots).set idx (concretizeSymSlot args s) =
        concretizeSymSlots args (slots.set idx s)
  | .nil, _ => rfl
  | _ :: _, .zero => rfl
  | _ :: rest, .succ idx => congrArg (_ :: ·) (concretizeSymSlots_set args s rest idx)

theorem set?_concretizeSymSlots
    (args : List Value)
    (s : SymSlot)
    (slots : List SymSlot)
    (idx : Nat) :
    set? (concretizeSymSlots args slots) idx (concretizeSymSlot args s) =
      match set? slots idx s with
      | .some slots' => .some (concretizeSymSlots args slots')
      | .none => .none := by
  unfold set?
  rw [concretizeSymSlots_length, concretizeSymSlots_set]
  split <;> rfl

theorem set?_concretizeSymSlots_concrete
    (args : List Value)
    (slot : LocalSlot) :
    ∀ (slots : List SymSlot) (idx : Nat),
      set? (concretizeSymSlots args slots) idx slot =
        match set? slots idx (.concrete slot) with
        | .some slots' => .some (concretizeSymSlots args slots')
        | .none => .none :=
  set?_concretizeSymSlots args (.concrete slot)

/-- Pure field projection reader independent of `locals`. -/
def readProjectedPure : Value → List ProjectionElem → Option Value
  | val, .nil => .some val
  | .aggregate _ fields, .field idx _ :: rest =>
    match get? fields idx with
    | .some fieldVal => readProjectedPure fieldVal rest
    | .none => .none
  | _, _ => .none

theorem readProjectedPure_sound
    (locals : List LocalSlot) :
    ∀ (val : Value) (proj : List ProjectionElem) (res : Value),
      readProjectedPure val proj = .some res →
      readProjectedValue locals val proj = .ok res
  | val, .nil, res, h => by
    injection h with hEq
    subst hEq
    rfl
  | .aggregate _ fields, .field idx _ :: rest, res, h => by
    dsimp only [readProjectedPure] at h
    dsimp only [readProjectedValue]
    cases hGet : get? fields idx with
    | none =>
      rw [hGet] at h
      nomatch h
    | some fieldVal =>
      rw [hGet] at h
      exact readProjectedPure_sound locals fieldVal rest res h
  | .unit, .field _ _ :: _, _, h => nomatch h
  | .scalar _, .field _ _ :: _, _, h => nomatch h
  | .ptr _ _, .field _ _ :: _, _, h => nomatch h
  | _, .deref :: _, _, h => nomatch h
  | _, .index _ :: _, _, h => nomatch h
  | _, .constantIndex _ _ _ :: _, _, h => nomatch h
  | _, .subslice _ _ _ :: _, _, h => nomatch h
  | _, .downcast _ _ :: _, _, h => nomatch h
  | _, .opaqueCast _ :: _, _, h => nomatch h
  | _, .unwrapUnsafeBinder _ :: _, _, h => nomatch h


/-- Evaluate a non-indirect, non-slice `ConstValue` to a concrete `Value`. -/
def evalSymConstVal : ConstValue → Option Value
  | .zeroSized => .some .unit
  | .scalar (.int s) => .some (.scalar s)
  | .scalar (.ptr p sz) => .some (.ptr p sz)
  | .slice _ _ => .none
  | .indirect _ _ => .none
  | .unevaluated _ => .none

theorem evalSymConstVal_sound
    (locals : List LocalSlot)
    (ty : Ty)
    (cv : ConstValue)
    (borrows : List BorrowEntry)
    (globals : List CapturedAllocation)
    (layouts : LayoutTable)
    {callerLocals : List LocalSlot}
    (v : Value)
    (h : evalSymConstVal cv = .some v) :
    evalOperand locals (.constant { ty := ty, val := cv }) borrows globals layouts callerLocals =
      .ok v locals := by
  cases cv with
  | zeroSized =>
    injection h with hEq
    subst hEq
    rfl
  | scalar cs =>
    cases cs with
    | int s =>
      injection h with hEq
      subst hEq
      rfl
    | ptr p sz =>
      injection h with hEq
      subst hEq
      rfl
  | slice _ _ => nomatch h
  | indirect _ _ => nomatch h
  | unevaluated _ => nomatch h

/-- Evaluate a `Place` read (as in `Operand.copy` or projected `Operand.move`)
over symbolic slots `slots`. -/
def evalSymPlaceCopy
    (slots : List SymSlot)
    (p : Place)
    (borrows : List BorrowEntry) :
    Option SymVal :=
  match p.projection with
  | .deref :: restProj =>
    match get? slots p.local_ with
    | .some (.concrete (.init (.ptr ptrVal _))) =>
      match lookupBorrow borrows ptrVal.tag with
      | .some entry =>
        match entry.perm with
        | .disabled => .none
        | _ =>
          match get? slots entry.targetLocal with
          | .some (.concrete (.init targetRootVal)) =>
            let fullProj :=
              match entry.targetProjection with
              | .nil => restProj
              | ph :: pt => ph :: appendProjections pt restProj
            match readProjectedPure targetRootVal fullProj with
            | .some fieldVal => .some (.concrete fieldVal)
            | .none => .none
          | .some (.symArg idx) =>
            match entry.targetProjection, restProj with
            | .nil, .nil => .some (.symArg idx)
            | _, _ => .none
          | _ => .none
      | .none => .none
    | _ => .none
  | .nil =>
    match get? slots p.local_ with
    | .some (.concrete (.init rootVal)) => .some (.concrete rootVal)
    | .some (.symArg idx) => .some (.symArg idx)
    | _ => .none
  | proj :: rest =>
    match get? slots p.local_ with
    | .some (.concrete (.init rootVal)) =>
      match readProjectedPure rootVal (proj :: rest) with
      | .some fieldVal => .some (.concrete fieldVal)
      | .none => .none
    | _ => .none

/-- Concretize a `PlaceReadResult` for a `SymVal` read against `args`. -/
def concretizeSymReadResult
    (args : List Value)
    (sv : SymVal)
    (slots' : List SymSlot) :
    PlaceReadResult :=
  match sv with
  | .concrete v => .ok v (concretizeSymSlots args slots')
  | .symArg idx =>
    match get? args idx with
    | .some v => .ok v (concretizeSymSlots args slots')
    | .none => .ub

theorem evalSymPlaceCopy_sound_copy
    (args : List Value)
    (slots : List SymSlot)
    (p : Place)
    (borrows : List BorrowEntry)
    (globals : List CapturedAllocation)
    (layouts : LayoutTable)
    {callerLocals : List LocalSlot}
    (sv : SymVal)
    (h : evalSymPlaceCopy slots p borrows = .some sv) :
    evalOperand (concretizeSymSlots args slots) (.copy p) borrows globals layouts callerLocals =
      concretizeSymReadResult args sv slots := by
  cases p with
  | mk loc proj =>
    cases proj with
    | nil =>
      dsimp only [evalSymPlaceCopy] at h
      dsimp only [evalOperand]
      rw [get?_concretizeSymSlots args slots loc]
      cases hGet : get? slots loc with
      | none =>
        rw [hGet] at h
        nomatch h
      | some slot =>
        rw [hGet] at h
        cases slot with
        | symArg idx =>
          injection h with hEq
          subst hEq
          dsimp only [concretizeSymSlot, concretizeSymReadResult]
          cases get? args idx with
          | none => rfl
          | some v => rfl
        | concrete cSlot =>
          cases cSlot with
          | dead => nomatch h
          | uninit => nomatch h
          | init rootVal =>
            injection h with hEq
            subst hEq
            rfl
    | cons pHead pTail =>
      cases pHead with
      | deref =>
        dsimp only [evalSymPlaceCopy] at h
        dsimp only [evalOperand]
        rw [get?_concretizeSymSlots args slots loc]
        cases hGet : get? slots loc with
        | none =>
          rw [hGet] at h
          nomatch h
        | some slot =>
          rw [hGet] at h
          cases slot with
          | symArg _ => nomatch h
          | concrete cSlot =>
            cases cSlot with
            | dead => nomatch h
            | uninit => nomatch h
            | init ptrRoot =>
              cases ptrRoot with
              | unit => nomatch h
              | scalar _ => nomatch h
              | aggregate _ _ => nomatch h
              | ptr ptrVal sz =>
                dsimp only at h
                dsimp only [concretizeSymSlot]
                cases hBorrow : lookupBorrow borrows ptrVal.tag with
                | none =>
                  rw [hBorrow] at h
                  nomatch h
                | some entry =>
                  rw [hBorrow] at h
                  dsimp only [evalSymPlaceCopy] at h
                  dsimp only [evalOperand]
                  cases hPerm : entry.perm with
                  | disabled =>
                    rw [hPerm] at h
                    nomatch h
                  | active | reserved | frozen =>
                    rw [hPerm] at h
                    dsimp only [evalSymPlaceCopy] at h
                    dsimp only [evalOperand]
                    rw [get?_concretizeSymSlots args slots entry.targetLocal]
                    cases hTProj : entry.targetProjection with
                    | nil =>
                      rw [hTProj] at h
                      dsimp only [evalSymPlaceCopy] at h
                      dsimp only [evalOperand]
                      cases hTarget : get? slots entry.targetLocal with
                      | none =>
                        rw [hTarget] at h
                        nomatch h
                      | some tSlot =>
                        rw [hTarget] at h
                        cases tSlot with
                        | symArg idx =>
                          dsimp only at h
                          cases pTail with
                          | cons _ _ => nomatch h
                          | nil =>
                            injection h with hEq
                            subst hEq
                            dsimp only [concretizeSymSlot, concretizeSymReadResult]
                            cases get? args idx with
                            | none => rfl
                            | some v => rfl
                        | concrete tcSlot =>
                          cases tcSlot with
                          | dead => nomatch h
                          | uninit => nomatch h
                          | init targetRootVal =>
                            dsimp only at h
                            dsimp only [concretizeSymSlot]
                            cases hRead : readProjectedPure targetRootVal pTail with
                            | none =>
                              rw [hRead] at h
                              nomatch h
                            | some fieldVal =>
                              rw [hRead] at h
                              injection h with hEq
                              subst hEq
                              dsimp only [concretizeSymReadResult]
                              rw [readProjectedPure_sound
                                (concretizeSymSlots args slots)
                                targetRootVal
                                pTail
                                fieldVal
                                hRead]
                    | cons ph pt =>
                      rw [hTProj] at h
                      dsimp only [evalSymPlaceCopy] at h
                      dsimp only [evalOperand]
                      cases hTarget : get? slots entry.targetLocal with
                      | none =>
                        rw [hTarget] at h
                        nomatch h
                      | some tSlot =>
                        rw [hTarget] at h
                        cases tSlot with
                        | symArg idx =>
                          nomatch h
                        | concrete tcSlot =>
                          cases tcSlot with
                          | dead => nomatch h
                          | uninit => nomatch h
                          | init targetRootVal =>
                            dsimp only at h
                            dsimp only [concretizeSymSlot]
                            cases hRead :
                                readProjectedPure
                                  targetRootVal
                                  (ph :: appendProjections pt pTail) with
                            | none =>
                              rw [hRead] at h
                              nomatch h
                            | some fieldVal =>
                              rw [hRead] at h
                              injection h with hEq
                              subst hEq
                              dsimp only [concretizeSymReadResult]
                              rw [readProjectedPure_sound
                                (concretizeSymSlots args slots)
                                targetRootVal
                                (ph :: appendProjections pt pTail)
                                fieldVal
                                hRead]
      | field fIdx fTy =>
        dsimp only [evalSymPlaceCopy] at h
        dsimp only [evalOperand]
        rw [get?_concretizeSymSlots args slots loc]
        cases hGet : get? slots loc with
        | none =>
          rw [hGet] at h
          nomatch h
        | some slot =>
          rw [hGet] at h
          cases slot with
          | symArg _ => nomatch h
          | concrete cSlot =>
            cases cSlot with
            | dead => nomatch h
            | uninit => nomatch h
            | init rootVal =>
              dsimp only at h
              dsimp only [concretizeSymSlot]
              cases hRead : readProjectedPure rootVal (.field fIdx fTy :: pTail) with
              | none =>
                rw [hRead] at h
                nomatch h
              | some fieldVal =>
                rw [hRead] at h
                injection h with hEq
                subst hEq
                dsimp only [concretizeSymReadResult]
                rw [readProjectedPure_sound
                  (concretizeSymSlots args slots)
                  rootVal
                  (.field fIdx fTy :: pTail)
                  fieldVal
                  hRead]
      | index _ | constantIndex _ _ _ | subslice _ _ _ | downcast _ _ | opaqueCast _ | unwrapUnsafeBinder _ =>
        dsimp only [evalSymPlaceCopy] at h
        cases hGet : get? slots loc with
        | none =>
          rw [hGet] at h
          nomatch h
        | some slot =>
          rw [hGet] at h
          cases slot with
          | symArg _ => nomatch h
          | concrete cSlot =>
            cases cSlot with
            | dead => nomatch h
            | uninit => nomatch h
            | init rootVal =>
              dsimp only at h
              nomatch h


theorem evalOperand_move_cons_eq_copy
    (locals : List LocalSlot)
    (loc : Local)
    (pHead : ProjectionElem)
    (pTail : List ProjectionElem)
    (borrows : List BorrowEntry)
    (globals : List CapturedAllocation)
    (layouts : LayoutTable)
    {callerLocals : List LocalSlot} :
    evalOperand locals (.move ⟨loc, pHead :: pTail⟩) borrows globals layouts callerLocals =
      evalOperand locals (.copy ⟨loc, pHead :: pTail⟩) borrows globals layouts callerLocals := by
  cases pHead <;> rfl

/-- Evaluate an `Operand` over symbolic slots `slots`. -/
def evalSymOperand
    (slots : List SymSlot)
    (op : Operand)
    (borrows : List BorrowEntry) :
    Option (SymVal × List SymSlot) :=
  match op with
  | .copy p =>
    match evalSymPlaceCopy slots p borrows with
    | .some sv => .some (sv, slots)
    | .none => .none
  | .move p =>
    match p.projection with
    | .nil =>
      match get? slots p.local_ with
      | .some (.concrete (.init rootVal)) =>
        match set? slots p.local_ (.concrete .uninit) with
        | .some slots' => .some (.concrete rootVal, slots')
        | .none => .none
      | .some (.symArg idx) =>
        match set? slots p.local_ (.concrete .uninit) with
        | .some slots' => .some (.symArg idx, slots')
        | .none => .none
      | _ => .none
    | _ :: _ =>
      match evalSymPlaceCopy slots p borrows with
      | .some sv => .some (sv, slots)
      | .none => .none
  | .constant c =>
    match evalSymConstVal c.val with
    | .some v => .some (.concrete v, slots)
    | .none => .none

theorem evalSymOperand_sound
    (args : List Value)
    (slots : List SymSlot)
    (op : Operand)
    (borrows : List BorrowEntry)
    (globals : List CapturedAllocation)
    (layouts : LayoutTable)
    {callerLocals : List LocalSlot}
    (sv : SymVal)
    (slots' : List SymSlot)
    (h : evalSymOperand slots op borrows = .some (sv, slots')) :
    evalOperand (concretizeSymSlots args slots) op borrows globals layouts callerLocals =
      concretizeSymReadResult args sv slots' := by
  cases op with
  | copy p =>
    dsimp only [evalSymOperand] at h
    cases hCopy : evalSymPlaceCopy slots p borrows with
    | none =>
      rw [hCopy] at h
      nomatch h
    | some sv0 =>
      rw [hCopy] at h
      injection h with hPair
      injection hPair with hSv hSlots
      subst hSv
      subst hSlots
      exact evalSymPlaceCopy_sound_copy args slots p borrows globals layouts sv0 hCopy
  | move p =>
    cases p with
    | mk loc proj =>
      cases proj with
      | nil =>
        dsimp only [evalSymOperand] at h
        dsimp only [evalOperand]
        rw [get?_concretizeSymSlots args slots loc]
        cases hGet : get? slots loc with
        | none =>
          rw [hGet] at h
          nomatch h
        | some sSlot =>
          rw [hGet] at h
          cases sSlot with
          | symArg idx =>
            dsimp only at h
            cases hSet : set? slots loc (.concrete .uninit) with
            | none =>
              rw [hSet] at h
              nomatch h
            | some slots1 =>
              rw [hSet] at h
              injection h with hPair
              injection hPair with hSv hSlots
              subst hSv
              subst hSlots
              dsimp only [concretizeSymSlot, concretizeSymReadResult]
              cases get? args idx with
              | none => rfl
              | some v =>
                dsimp only
                rw [set?_concretizeSymSlots_concrete args .uninit slots loc, hSet]
          | concrete cSlot =>
            cases cSlot with
            | dead => nomatch h
            | uninit => nomatch h
            | init rootVal =>
              dsimp only at h
              cases hSet : set? slots loc (.concrete .uninit) with
              | none =>
                rw [hSet] at h
                nomatch h
              | some slots1 =>
                rw [hSet] at h
                injection h with hPair
                injection hPair with hSv hSlots
                subst hSv
                subst hSlots
                dsimp only [concretizeSymSlot, concretizeSymReadResult]
                rw [set?_concretizeSymSlots_concrete args .uninit slots loc, hSet]
      | cons pHead pTail =>
        dsimp only [evalSymOperand] at h
        rw [evalOperand_move_cons_eq_copy]
        cases hCopy : evalSymPlaceCopy slots ⟨loc, pHead :: pTail⟩ borrows with
        | none =>
          rw [hCopy] at h
          nomatch h
        | some sv0 =>
          rw [hCopy] at h
          injection h with hPair
          injection hPair with hSv hSlots
          subst hSv
          subst hSlots
          exact evalSymPlaceCopy_sound_copy
            args slots ⟨loc, pHead :: pTail⟩ borrows globals layouts sv0 hCopy
  | constant c =>
    dsimp only [evalSymOperand] at h
    cases c with
    | mk ty cv =>
      dsimp only at h
      cases hCv : evalSymConstVal cv with
      | none =>
        rw [hCv] at h
        nomatch h
      | some v =>
        rw [hCv] at h
        injection h with hPair
        injection hPair with hSv hSlots
        subst hSv
        subst hSlots
        exact evalSymConstVal_sound (concretizeSymSlots args slots) ty cv borrows globals layouts v hCv

/-- Evaluate a list of operands to concrete `Value`s left-to-right. -/
def evalSymOperandsConcrete
    (slots : List SymSlot)
    (ops : List Operand)
    (borrows : List BorrowEntry) :
    Option (List Value × List SymSlot) :=
  match ops with
  | .nil => .some (.nil, slots)
  | op :: rest =>
    match evalSymOperand slots op borrows with
    | .some (.concrete v, slots₁) =>
      match evalSymOperandsConcrete slots₁ rest borrows with
      | .some (vs, slots₂) => .some (v :: vs, slots₂)
      | .none => .none
    | _ => .none

theorem evalSymOperandsConcrete_sound
    (args : List Value)
    {callerLocals : List LocalSlot} :
    ∀ (ops : List Operand)
      (slots : List SymSlot)
      (borrows : List BorrowEntry)
      (globals : List CapturedAllocation)
      (layouts : LayoutTable)
      (vals : List Value)
      (slots' : List SymSlot),
      evalSymOperandsConcrete slots ops borrows = .some (vals, slots') →
      evalOperands (concretizeSymSlots args slots) ops borrows globals layouts callerLocals =
        .ok vals (concretizeSymSlots args slots')
  | .nil, slots, _, _, _, vals, slots', h => by
    injection h with hPair
    injection hPair with hVals hSlots
    subst hVals
    subst hSlots
    rfl
  | op :: rest, slots, borrows, globals, layouts, vals, slots', h => by
    dsimp only [evalSymOperandsConcrete] at h
    dsimp only [evalOperands]
    cases hOp : evalSymOperand slots op borrows with
    | none =>
      rw [hOp] at h
      nomatch h
    | some pair1 =>
      rw [hOp] at h
      cases pair1 with
      | mk sv1 slots1 =>
        cases sv1 with
        | symArg _ => nomatch h
        | concrete v1 =>
          dsimp only at h
          rw [evalSymOperand_sound args slots op borrows globals layouts (.concrete v1) slots1 hOp]
          dsimp only [concretizeSymReadResult]
          cases hRest : evalSymOperandsConcrete slots1 rest borrows with
          | none =>
            rw [hRest] at h
            nomatch h
          | some pair2 =>
            rw [hRest] at h
            cases pair2 with
            | mk vs slots2 =>
              injection h with hPair
              injection hPair with hVals hSlots
              subst hVals
              subst hSlots
              rw [evalSymOperandsConcrete_sound args rest slots1 borrows globals layouts vs slots2 hRest]

/-- Evaluate concrete boolean/equality scalar binary operations. -/
def evalSymScalarBinOp (op : BinOp) (lhs rhs : ScalarInt) : Option Value :=
  match Nat.beq lhs.sizeBytes 0 with
  | true => .none
  | false =>
    let sz := lhs.sizeBytes
    let numBits := Nat.mul sz 8
    let a := lhs.bits
    let b := rhs.bits
    match Nat.beq lhs.sizeBytes rhs.sizeBytes with
    | false => .none
    | true =>
      match op with
      | .bitAnd => .some (.scalar ⟨bitwiseAndBits numBits a b, sz⟩)
      | .bitOr => .some (.scalar ⟨bitwiseOrBits numBits a b, sz⟩)
      | .bitXor => .some (.scalar ⟨bitwiseXorBits numBits a b, sz⟩)
      | .eq => .some (.scalar (boolToScalar (Nat.beq a b)))
      | .ne => .some (.scalar (boolToScalar (Bool.not (Nat.beq a b))))
      | _ => .none

theorem evalSymScalarBinOp_sound
    (op : BinOp)
    (lhs rhs : ScalarInt)
    (locals : List LocalSlot)
    (mem : Memory)
    (isSigned : Bool)
    (v : Value)
    (h : evalSymScalarBinOp op lhs rhs = .some v) :
    evalScalarBinOp op lhs rhs locals mem isSigned = .ok v locals mem := by
  dsimp only [evalSymScalarBinOp] at h
  dsimp only [evalScalarBinOp]
  cases hSz0 : Nat.beq lhs.sizeBytes 0 with
  | true =>
    rw [hSz0] at h
    nomatch h
  | false =>
    rw [hSz0] at h
    dsimp only at h
    dsimp only
    cases hSzEq : Nat.beq lhs.sizeBytes rhs.sizeBytes with
    | false =>
      rw [hSzEq] at h
      nomatch h
    | true =>
      rw [hSzEq] at h
      dsimp only at h
      cases op with
      | bitAnd | bitOr | bitXor | eq | ne =>
        injection h with hEq
        subst hEq
        rfl
      | _ => nomatch h

theorem concretizeSymSlot_not_dead
    (args : List Value)
    (s : SymSlot)
    (hNotDead : match s with | .concrete .dead => False | _ => True) :
    match concretizeSymSlot args s with
    | .dead => False
    | _ => True := by
  cases s with
  | symArg idx =>
    dsimp only [concretizeSymSlot]
    cases get? args idx <;> trivial
  | concrete c =>
    cases c with
    | dead => exact False.elim hNotDead
    | uninit => trivial
    | init _ => trivial

/-- Evaluate an `Rvalue` that produces a `SymVal` (either concrete or `.symArg idx`). -/
def evalSymRvalueConcrete
    (slots : List SymSlot)
    (borrows : List BorrowEntry)
    (nextTag : Nat)
    (rv : Rvalue) :
    Option (SymVal × List SymSlot × List BorrowEntry × Nat) :=
  match rv with
  | .use op =>
    match evalSymOperand slots op borrows with
    | .some (sv, slots') => .some (sv, slots', borrows, nextTag)
    | .none => .none
  | .copyForDeref place =>
    match evalSymPlaceCopy slots place borrows with
    | .some sv => .some (sv, slots, borrows, nextTag)
    | .none => .none
  | .ref borrowKind place =>
    let perm :=
      match borrowKind with
      | .shared => TreeBorrowPerm.frozen
      | .mut false => TreeBorrowPerm.active
      | .mut true => TreeBorrowPerm.reserved
    match place.projection with
    | .deref :: _ => .none
    | _ =>
      match get? slots place.local_ with
      | .none => .none
      | .some (.concrete .dead) => .none
      | .some _ =>
        let entry : BorrowEntry := {
          tag := nextTag
          targetLocal := place.local_
          targetProjection := place.projection
          perm := perm
        }
        .some
          (.concrete (.ptr { allocId := nextTag, offsetBytes := 0 } 8),
           slots,
           entry :: borrows,
           Nat.add nextTag 1)
  | .binaryOp op lhsOp rhsOp =>
    match evalSymOperand slots lhsOp borrows with
    | .some (.concrete (.scalar lhs), slots₁) =>
      match evalSymOperand slots₁ rhsOp borrows with
      | .some (.concrete (.scalar rhs), slots₂) =>
        match evalSymScalarBinOp op lhs rhs with
        | .some v => .some (.concrete v, slots₂, borrows, nextTag)
        | .none => .none
      | _ => .none
    | _ => .none
  | .aggregate .tuple ops =>
    match evalSymOperandsConcrete slots ops borrows with
    | .some (vals, slots') => .some (.concrete (.aggregate 0 vals), slots', borrows, nextTag)
    | .none => .none
  | .aggregate (.adt _ variantIdx _) ops =>
    match evalSymOperandsConcrete slots ops borrows with
    | .some (vals, slots') => .some (.concrete (.aggregate variantIdx vals), slots', borrows, nextTag)
    | .none => .none
  | _ => .none

theorem memory_eta (m : Memory) :
    { m with borrows := m.borrows, nextTag := m.nextTag } = m := by
  cases m
  rfl

/-- Concretize a symbolic `Rvalue` evaluation result against `args`. -/
def concretizeSymRvalueResult
    (args : List Value)
    (sv : SymVal)
    (slots' : List SymSlot)
    (mem' : Memory) :
    RvalueEvalResult :=
  match sv with
  | .concrete v => .ok v (concretizeSymSlots args slots') mem'
  | .symArg idx =>
    match get? args idx with
    | .some v => .ok v (concretizeSymSlots args slots') mem'
    | .none => .ub

theorem evalSymRvalueConcrete_sound
    (args : List Value)
    (slots : List SymSlot)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (rv : Rvalue)
    (sv : SymVal)
    (slots' : List SymSlot)
    (borrows' : List BorrowEntry)
    (nextTag' : Nat)
    (h : evalSymRvalueConcrete slots mem.borrows mem.nextTag rv =
      .some (sv, slots', borrows', nextTag')) :
    evalRvalue (concretizeSymSlots args slots) rv mem localDecls layouts =
      concretizeSymRvalueResult
        args
        sv
        slots'
        { mem with borrows := borrows', nextTag := nextTag' } := by
  cases rv with
  | use op =>
    dsimp only [evalSymRvalueConcrete] at h
    dsimp only [evalRvalue]
    cases hOp : evalSymOperand slots op mem.borrows with
    | none =>
      rw [hOp] at h
      nomatch h
    | some pair =>
      rw [hOp] at h
      cases pair with
      | mk sv0 s1 =>
        injection h with hTup
        injection hTup with hV hRest1
        injection hRest1 with hS hRest2
        injection hRest2 with hB hT
        subst hV; subst hS; subst hB; subst hT
        rw [evalSymOperand_sound args slots op mem.borrows mem.globals layouts sv0 s1 hOp]
        rw [memory_eta mem]
        cases sv0 with
        | concrete _ => rfl
        | symArg idx =>
          dsimp only [concretizeSymReadResult, concretizeSymRvalueResult]
          cases get? args idx <;> rfl
  | copyForDeref place =>
    dsimp only [evalSymRvalueConcrete] at h
    dsimp only [evalRvalue]
    cases hCopy : evalSymPlaceCopy slots place mem.borrows with
    | none =>
      rw [hCopy] at h
      nomatch h
    | some sv0 =>
      rw [hCopy] at h
      injection h with hTup
      injection hTup with hV hRest1
      injection hRest1 with hS hRest2
      injection hRest2 with hB hT
      subst hV; subst hS; subst hB; subst hT
      rw [evalSymPlaceCopy_sound_copy args slots place mem.borrows mem.globals layouts sv0 hCopy]
      rw [memory_eta mem]
      cases sv0 with
      | concrete _ => rfl
      | symArg idx =>
        dsimp only [concretizeSymReadResult, concretizeSymRvalueResult]
        cases get? args idx <;> rfl
  | ref borrowKind place =>
    cases place with
    | mk loc proj =>
      cases proj with
      | nil =>
        dsimp only [evalSymRvalueConcrete] at h
        dsimp only [evalRvalue]
        rw [get?_concretizeSymSlots args slots loc]
        cases hGet : get? slots loc with
        | none =>
          rw [hGet] at h
          nomatch h
        | some sSlot =>
          rw [hGet] at h
          cases sSlot with
          | symArg idx =>
            injection h with hTup
            injection hTup with hV hRest1
            injection hRest1 with hS hRest2
            injection hRest2 with hB hT
            subst hV; subst hS; subst hB; subst hT
            dsimp only [concretizeSymSlot]
            cases get? args idx <;> rfl
          | concrete cSlot =>
            cases cSlot with
            | dead => nomatch h
            | uninit | init _ =>
              injection h with hTup
              injection hTup with hV hRest1
              injection hRest1 with hS hRest2
              injection hRest2 with hB hT
              subst hV; subst hS; subst hB; subst hT
              rfl
      | cons pHead pTail =>
        cases pHead with
        | deref => nomatch h
        | field _ _ | index _ | constantIndex _ _ _ | subslice _ _ _ | downcast _ _ | opaqueCast _ | unwrapUnsafeBinder _ =>
          dsimp only [evalSymRvalueConcrete] at h
          dsimp only [evalRvalue]
          rw [get?_concretizeSymSlots args slots loc]
          cases hGet : get? slots loc with
          | none =>
            rw [hGet] at h
            nomatch h
          | some sSlot =>
            rw [hGet] at h
            cases sSlot with
            | symArg idx =>
              injection h with hTup
              injection hTup with hV hRest1
              injection hRest1 with hS hRest2
              injection hRest2 with hB hT
              subst hV; subst hS; subst hB; subst hT
              dsimp only [concretizeSymSlot]
              cases get? args idx <;> rfl
            | concrete cSlot =>
              cases cSlot with
              | dead => nomatch h
              | uninit | init _ =>
                injection h with hTup
                injection hTup with hV hRest1
                injection hRest1 with hS hRest2
                injection hRest2 with hB hT
                subst hV; subst hS; subst hB; subst hT
                rfl
  | binaryOp op lhsOp rhsOp =>
    dsimp only [evalSymRvalueConcrete] at h
    dsimp only [evalRvalue]
    cases hLhs : evalSymOperand slots lhsOp mem.borrows with
    | none =>
      rw [hLhs] at h
      nomatch h
    | some pair1 =>
      rw [hLhs] at h
      cases pair1 with
      | mk sv1 slots1 =>
        cases sv1 with
        | symArg _ => nomatch h
        | concrete v1 =>
          cases v1 with
          | unit | ptr _ _ | aggregate _ _ => nomatch h
          | scalar lhs =>
            dsimp only at h
            rw [evalSymOperand_sound args slots lhsOp mem.borrows mem.globals layouts (.concrete (.scalar lhs)) slots1 hLhs]
            dsimp only [concretizeSymReadResult]
            cases hRhs : evalSymOperand slots1 rhsOp mem.borrows with
            | none =>
              rw [hRhs] at h
              nomatch h
            | some pair2 =>
              rw [hRhs] at h
              cases pair2 with
              | mk sv2 slots2 =>
                cases sv2 with
                | symArg _ => nomatch h
                | concrete v2 =>
                  cases v2 with
                  | unit | ptr _ _ | aggregate _ _ => nomatch h
                  | scalar rhs =>
                    dsimp only at h
                    rw [evalSymOperand_sound args slots1 rhsOp mem.borrows mem.globals layouts (.concrete (.scalar rhs)) slots2 hRhs]
                    dsimp only [concretizeSymReadResult]
                    cases hBin : evalSymScalarBinOp op lhs rhs with
                    | none =>
                      rw [hBin] at h
                      nomatch h
                    | some resVal =>
                      rw [hBin] at h
                      injection h with hTup
                      injection hTup with hV hRest1
                      injection hRest1 with hS hRest2
                      injection hRest2 with hB hT
                      subst hV; subst hS; subst hB; subst hT
                      exact evalSymScalarBinOp_sound op lhs rhs (concretizeSymSlots args slots2) mem (operandIsSigned localDecls lhsOp layouts) resVal hBin
  | aggregate aggKind ops =>
    cases aggKind with
    | tuple =>
      dsimp only [evalSymRvalueConcrete] at h
      dsimp only [evalRvalue]
      cases hOps : evalSymOperandsConcrete slots ops mem.borrows with
      | none =>
        rw [hOps] at h
        nomatch h
      | some pair =>
        rw [hOps] at h
        cases pair with
        | mk vals s1 =>
          injection h with hTup
          injection hTup with hV hRest1
          injection hRest1 with hS hRest2
          injection hRest2 with hB hT
          subst hV; subst hS; subst hB; subst hT
          rw [evalSymOperandsConcrete_sound args ops slots mem.borrows mem.globals layouts vals s1 hOps]
          rfl
    | adt _ variantIdx _ =>
      dsimp only [evalSymRvalueConcrete] at h
      dsimp only [evalRvalue]
      cases hOps : evalSymOperandsConcrete slots ops mem.borrows with
      | none =>
        rw [hOps] at h
        nomatch h
      | some pair =>
        rw [hOps] at h
        cases pair with
        | mk vals s1 =>
          injection h with hTup
          injection hTup with hV hRest1
          injection hRest1 with hS hRest2
          injection hRest2 with hB hT
          subst hV; subst hS; subst hB; subst hT
          rw [evalSymOperandsConcrete_sound args ops slots mem.borrows mem.globals layouts vals s1 hOps]
          rfl
    | _ => nomatch h
  | _ => nomatch h


/-- Symbolic machine state for single-frame closure abstract interpretation. -/
structure SymState : Type where
  blockIdx : BasicBlockIdx
  stmtIdx : Nat
  slots : List SymSlot
  borrows : List BorrowEntry
  nextTag : Nat

/-- Concretize the `Memory` of a `SymState` for `body`. -/
def concretizeSymMemory (body : CapturedMir) (st : SymState) : Memory :=
  { nextAllocId := length body.allocations
    globals := body.allocations
    borrows := st.borrows
    nextTag := st.nextTag
    callees := .nil
    callStack := .nil
    activeCallee := .none
  }

/-- Concretize a `SymState` against `body` and `args`. -/
def concretizeSymState (body : CapturedMir) (args : List Value) (st : SymState) : MachineState :=
  { frame := {
      blockIdx := st.blockIdx
      stmtIdx := st.stmtIdx
      locals := concretizeSymSlots args st.slots
    }
    memory := concretizeSymMemory body st
  }

/-- Initial `SymState` for `body`. -/
def initSymState (body : CapturedMir) : SymState :=
  { blockIdx := 0
    stmtIdx := 0
    slots := initSymSlots body.localDecls body.argCount
    borrows := .nil
    nextTag := 1
  }

theorem concretizeSymState_initSymState
    (body : CapturedMir)
    (args : List Value)
    (h_len : length args = body.argCount) :
    concretizeSymState body args (initSymState body) = initMachineState body args := by
  dsimp only [concretizeSymState, initSymState, initMachineState, concretizeSymMemory]
  rw [concretizeSymSlots_initSymSlots args body.localDecls body.argCount h_len]

/-- Concrete symbolic step for a single `Statement`. -/
def symStepStmtConcrete
    (st : SymState)
    (stmt : Statement) :
    Option SymState :=
  match stmt.kind with
  | .nop => .some { st with stmtIdx := Nat.add st.stmtIdx 1 }
  | .coverage => .some { st with stmtIdx := Nat.add st.stmtIdx 1 }
  | .constEvalCounter => .some { st with stmtIdx := Nat.add st.stmtIdx 1 }
  | .placeMention place =>
    match get? st.slots place.local_ with
    | .none => .none
    | .some (.concrete .dead) => .none
    | .some _ => .some { st with stmtIdx := Nat.add st.stmtIdx 1 }
  | .storageLive loc =>
    match get? st.slots loc with
    | .some _ =>
      match set? st.slots loc (.concrete .uninit) with
      | .some slots' => .some { st with stmtIdx := Nat.add st.stmtIdx 1, slots := slots' }
      | .none => .none
    | .none => .none
  | .storageDead loc =>
    match get? st.slots loc with
    | .some _ =>
      match set? st.slots loc (.concrete .dead) with
      | .some slots' => .some { st with stmtIdx := Nat.add st.stmtIdx 1, slots := slots' }
      | .none => .none
    | .none => .none
  | .assign dst rv =>
    match dst.projection with
    | .nil =>
      match evalSymRvalueConcrete st.slots st.borrows st.nextTag rv with
      | .some (sv, slots₁, borrows₁, nextTag₁) =>
        match get? slots₁ dst.local_ with
        | .none => .none
        | .some (.concrete .dead) => .none
        | .some _ =>
          let dstSymSlot : SymSlot :=
            match sv with
            | .concrete val => .concrete (.init val)
            | .symArg idx => .symArg idx
          match set? slots₁ dst.local_ dstSymSlot with
          | .some slots₂ =>
            let borrows₂ := invalidateConflictingBorrows borrows₁ dst.local_ .none
            .some {
              st with
              stmtIdx := Nat.add st.stmtIdx 1
              slots := slots₂
              borrows := borrows₂
              nextTag := nextTag₁
            }
          | .none => .none
      | .none => .none
    | _ :: _ => .none
  | _ => .none

/-- Concrete symbolic step for a `Terminator`. -/
def symStepTermConcrete
    (st : SymState)
    (term : Terminator) :
    Option SymState :=
  match term.kind with
  | .goto target =>
    .some { st with blockIdx := target, stmtIdx := 0 }
  | .drop place target _ =>
    match place.projection with
    | .nil =>
      match get? st.slots place.local_ with
      | .none => .none
      | .some (.concrete .dead) => .none
      | .some _ =>
        match set? st.slots place.local_ (.concrete .uninit) with
        | .some slots' => .some { st with blockIdx := target, stmtIdx := 0, slots := slots' }
        | .none => .none
    | _ :: _ => .none
  | .switchInt discr targets =>
    match evalSymOperand st.slots discr st.borrows with
    | .some (.concrete (.scalar sc), slots') =>
      let target := lookupSwitchTarget sc.bits targets.branches targets.otherwise
      .some { st with blockIdx := target, stmtIdx := 0, slots := slots' }
    | _ => .none
  | _ => .none

/-- Execute one concrete symbolic step of `body` from `st`. -/
def symStepConcrete (body : CapturedMir) (st : SymState) : Option SymState :=
  match body.phase with
  | .other _ => .none
  | _ =>
    match get? body.basicBlocks st.blockIdx with
    | .none => .none
    | .some bb =>
      match get? bb.statements st.stmtIdx with
      | .some stmt => symStepStmtConcrete st stmt
      | .none =>
        match Nat.beq st.stmtIdx (length bb.statements) with
        | true => symStepTermConcrete st bb.terminator
        | false => .none

theorem symStepStmtConcrete_sound
    (body : CapturedMir)
    (args : List Value)
    (st st' : SymState)
    (stmt : Statement)
    (h : symStepStmtConcrete st stmt = .some st') :
    evalStmt (concretizeSymState body args st) stmt body.localDecls body.layouts =
      MirStepNode.step (concretizeSymState body args st') ∨
    evalStmt (concretizeSymState body args st) stmt body.localDecls body.layouts =
      MirStepNode.fail .ub := by
  cases stmt with
  | mk kind _ =>
    cases kind with
    | nop | coverage | constEvalCounter =>
      injection h with hEq
      subst hEq
      exact Or.inl rfl
    | placeMention place =>
      dsimp only [symStepStmtConcrete] at h
      dsimp only [evalStmt, concretizeSymState]
      rw [get?_concretizeSymSlots args st.slots place.local_]
      cases hGet : get? st.slots place.local_ with
      | none =>
        rw [hGet] at h
        nomatch h
      | some sSlot =>
        rw [hGet] at h
        cases sSlot with
        | symArg idx =>
          injection h with hEq
          subst hEq
          dsimp only [concretizeSymSlot]
          cases get? args idx <;> exact Or.inl rfl
        | concrete cSlot =>
          cases cSlot with
          | dead => nomatch h
          | uninit | init _ =>
            injection h with hEq
            subst hEq
            exact Or.inl rfl
    | storageLive loc =>
      dsimp only [symStepStmtConcrete] at h
      dsimp only [evalStmt, concretizeSymState]
      rw [get?_concretizeSymSlots args st.slots loc]
      cases hGet : get? st.slots loc with
      | none =>
        rw [hGet] at h
        nomatch h
      | some sSlot =>
        rw [hGet] at h
        dsimp only at h
        dsimp only
        rw [set?_concretizeSymSlots_concrete args .uninit st.slots loc]
        cases hSet : set? st.slots loc (.concrete .uninit) with
        | none =>
          rw [hSet] at h
          nomatch h
        | some slots' =>
          rw [hSet] at h
          injection h with hEq
          subst hEq
          exact Or.inl rfl
    | storageDead loc =>
      dsimp only [symStepStmtConcrete] at h
      dsimp only [evalStmt, concretizeSymState]
      rw [get?_concretizeSymSlots args st.slots loc]
      cases hGet : get? st.slots loc with
      | none =>
        rw [hGet] at h
        nomatch h
      | some sSlot =>
        rw [hGet] at h
        dsimp only at h
        dsimp only
        rw [set?_concretizeSymSlots_concrete args .dead st.slots loc]
        cases hSet : set? st.slots loc (.concrete .dead) with
        | none =>
          rw [hSet] at h
          nomatch h
        | some slots' =>
          rw [hSet] at h
          injection h with hEq
          subst hEq
          exact Or.inl rfl
    | assign dst rv =>
      cases dst with
      | mk dstLoc dstProj =>
        cases dstProj with
        | cons _ _ => nomatch h
        | nil =>
          dsimp only [symStepStmtConcrete] at h
          dsimp only [evalStmt, concretizeSymState]
          cases hRv : evalSymRvalueConcrete st.slots st.borrows st.nextTag rv with
          | none =>
            rw [hRv] at h
            nomatch h
          | some tup =>
            rw [hRv] at h
            cases tup with
            | mk sv rest1 =>
              cases rest1 with
              | mk slots1 rest2 =>
                cases rest2 with
                | mk borrows1 nextTag1 =>
                  dsimp only at h
                  rw [evalSymRvalueConcrete_sound
                    args st.slots (concretizeSymMemory body st) body.localDecls body.layouts
                    rv sv slots1 borrows1 nextTag1 hRv]
                  dsimp only [concretizeSymMemory]
                  cases hGet : get? slots1 dstLoc with
                  | none =>
                    rw [hGet] at h
                    nomatch h
                  | some sSlot =>
                    rw [hGet] at h
                    cases sSlot with
                    | symArg idx =>
                      dsimp only at h
                      cases sv with
                      | concrete val =>
                        dsimp only [concretizeSymRvalueResult] at h ⊢
                        rw [get?_concretizeSymSlots args slots1 dstLoc, hGet]
                        cases hSet : set? slots1 dstLoc (.concrete (.init val)) with
                        | none =>
                          rw [hSet] at h
                          nomatch h
                        | some slots2 =>
                          rw [hSet] at h
                          injection h with hEq
                          subst hEq
                          dsimp only [concretizeSymSlot]
                          cases get? args idx with
                          | none =>
                            dsimp only
                            rw [set?_concretizeSymSlots_concrete args (.init val) slots1 dstLoc, hSet]
                            exact Or.inl rfl
                          | some _ =>
                            dsimp only
                            rw [set?_concretizeSymSlots_concrete args (.init val) slots1 dstLoc, hSet]
                            exact Or.inl rfl
                      | symArg valIdx =>
                        dsimp only at h
                        cases hSet : set? slots1 dstLoc (.symArg valIdx) with
                        | none =>
                          rw [hSet] at h
                          nomatch h
                        | some slots2 =>
                          rw [hSet] at h
                          injection h with hEq
                          subst hEq
                          dsimp only [concretizeSymRvalueResult]
                          cases hArgVal : get? args valIdx with
                          | none => exact Or.inr rfl
                          | some val =>
                            dsimp only
                            rw [get?_concretizeSymSlots args slots1 dstLoc, hGet]
                            have hSetSym := set?_concretizeSymSlots args (.symArg valIdx) slots1 dstLoc
                            dsimp only [concretizeSymSlot] at hSetSym
                            rw [hArgVal, hSet] at hSetSym
                            dsimp only [concretizeSymSlot]
                            cases get? args idx with
                            | none =>
                              dsimp only
                              rw [hSetSym]
                              exact Or.inl rfl
                            | some _ =>
                              dsimp only
                              rw [hSetSym]
                              exact Or.inl rfl
                    | concrete cSlot =>
                      cases cSlot with
                      | dead => nomatch h
                      | uninit | init _ =>
                        dsimp only at h
                        cases sv with
                        | concrete val =>
                          dsimp only [concretizeSymRvalueResult] at h ⊢
                          rw [get?_concretizeSymSlots args slots1 dstLoc, hGet]
                          cases hSet : set? slots1 dstLoc (.concrete (.init val)) with
                          | none =>
                            rw [hSet] at h
                            nomatch h
                          | some slots2 =>
                            rw [hSet] at h
                            injection h with hEq
                            subst hEq
                            dsimp only [concretizeSymSlot]
                            rw [set?_concretizeSymSlots_concrete args (.init val) slots1 dstLoc, hSet]
                            exact Or.inl rfl
                        | symArg valIdx =>
                          dsimp only at h
                          cases hSet : set? slots1 dstLoc (.symArg valIdx) with
                          | none =>
                            rw [hSet] at h
                            nomatch h
                          | some slots2 =>
                            rw [hSet] at h
                            injection h with hEq
                            subst hEq
                            dsimp only [concretizeSymRvalueResult]
                            cases hArgVal : get? args valIdx with
                            | none => exact Or.inr rfl
                            | some val =>
                              dsimp only
                              rw [get?_concretizeSymSlots args slots1 dstLoc, hGet]
                              have hSetSym := set?_concretizeSymSlots args (.symArg valIdx) slots1 dstLoc
                              dsimp only [concretizeSymSlot] at hSetSym
                              rw [hArgVal, hSet] at hSetSym
                              dsimp only [concretizeSymSlot]
                              rw [hSetSym]
                              exact Or.inl rfl
    | _ => nomatch h

theorem symStepTermConcrete_sound
    (body : CapturedMir)
    (args : List Value)
    (st st' : SymState)
    (term : Terminator)
    (h : symStepTermConcrete st term = .some st') :
    evalTerminator (concretizeSymState body args st) term (.some body) =
      MirStepNode.step (concretizeSymState body args st') ∨
    ∃ ev,
      evalTerminator (concretizeSymState body args st) term (.some body) =
        MirStepNode.emitStep ev (concretizeSymState body args st') := by
  cases term with
  | mk kind _ =>
    cases kind with
    | goto target =>
      injection h with hEq
      subst hEq
      exact Or.inl rfl
    | drop place target unwind =>
      cases place with
      | mk loc proj =>
        cases proj with
        | cons _ _ => nomatch h
        | nil =>
          dsimp only [symStepTermConcrete] at h
          dsimp only [evalTerminator, concretizeSymState]
          rw [get?_concretizeSymSlots args st.slots loc]
          cases hGet : get? st.slots loc with
          | none =>
            rw [hGet] at h
            nomatch h
          | some sSlot =>
            rw [hGet] at h
            cases sSlot with
            | symArg idx =>
              dsimp only at h
              cases hSet : set? st.slots loc (.concrete .uninit) with
              | none =>
                rw [hSet] at h
                nomatch h
              | some slots' =>
                rw [hSet] at h
                injection h with hEq
                subst hEq
                refine Or.inl ?_
                dsimp only [concretizeSymSlot]
                cases get? args idx with
                | none =>
                  dsimp only
                  rw [set?_concretizeSymSlots_concrete args .uninit st.slots loc, hSet]
                  rfl
                | some _ =>
                  dsimp only
                  rw [set?_concretizeSymSlots_concrete args .uninit st.slots loc, hSet]
                  rfl
            | concrete cSlot =>
              cases cSlot with
              | dead => nomatch h
              | uninit | init _ =>
                dsimp only at h
                cases hSet : set? st.slots loc (.concrete .uninit) with
                | none =>
                  rw [hSet] at h
                  nomatch h
                | some slots' =>
                  rw [hSet] at h
                  injection h with hEq
                  subst hEq
                  refine Or.inl ?_
                  dsimp only [concretizeSymSlot]
                  rw [set?_concretizeSymSlots_concrete args .uninit st.slots loc, hSet]
                  rfl
    | switchInt discr targets =>
      dsimp only [symStepTermConcrete] at h
      dsimp only [evalTerminator, concretizeSymState, concretizeSymMemory]
      cases hOp : evalSymOperand st.slots discr st.borrows with
      | none =>
        rw [hOp] at h
        nomatch h
      | some pair =>
        rw [hOp] at h
        cases pair with
        | mk sv slots' =>
          cases sv with
          | symArg _ => nomatch h
          | concrete v =>
            cases v with
            | unit | ptr _ _ | aggregate _ _ => nomatch h
            | scalar sc =>
              injection h with hEq
              subst hEq
              refine Or.inr ⟨.event sc.bits, ?_⟩
              rw [evalSymOperand_sound
                args st.slots discr st.borrows body.allocations body.layouts
                (.concrete (.scalar sc)) slots' hOp]
              rfl
    | _ => nomatch h

/-- Direct node evaluator over `MirStepNode` for bounded boolean predicate inversion. -/
def evalMirBoolExecHoldBounded : Nat → CapturedMir → MirExecState → Prop
  | .zero, _, _ => True
  | .succ fuel, body, st =>
    evalNodeWP
      (evalMirBoolExecHoldBounded fuel body)
      (mirSafePost (fun retVal _ => retVal = .scalar { bits := 1, sizeBytes := 1 }))
      (stepMirState body st)

/-- Bounded boolean predicate consequence over `MachineState`. -/
def evalMirBoolHoldBounded (fuel : Nat) (body : CapturedMir) (s : MachineState) : Prop :=
  evalMirBoolExecHoldBounded fuel body (.running s)

/-- Bounded step-node consequence matching `evalMirBoolHoldBounded (.succ fuel)`. -/
def stepResultHoldBounded (fuel : Nat) (body : CapturedMir) (r : MirStepNode) : Prop :=
  evalNodeWP
    (evalMirBoolExecHoldBounded fuel body)
    (mirSafePost (fun retVal _ => retVal = .scalar { bits := 1, sizeBytes := 1 }))
    r

theorem evalMirBoolExecHoldBounded_of_wpMirExecOrExhaustedSym
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (h :
      wpMirExecOrExhaustedSym fuel body st
        (mirSafePost (fun retVal _ => retVal = .scalar { bits := 1, sizeBytes := 1 }))) :
    evalMirBoolExecHoldBounded fuel body st := by
  induction fuel generalizing st with
  | zero => exact True.intro
  | succ fuel' ih =>
    unfold wpMirExecOrExhaustedSym at h
    rw [evalSymNodeTree_eq, stepMirExecSymTree_eval] at h
    unfold evalMirBoolExecHoldBounded
    cases hStep : stepMirState body st with
    | ret out =>
      rw [hStep] at h
      exact h
    | tau st' =>
      rw [hStep] at h
      exact ih st' h
    | vis i k =>
      rw [hStep] at h
      rcases i with f | (e | c)
      · exact False.elim h
      · cases e
        exact ih (k PUnit.unit) h
      · cases c
        intro ans
        exact ih (k ans) (h ans)

theorem wpBoolOrExhausted_of_mirBoolPredicateHolds
    (fuel : Nat) (specBody : CapturedMir) (args : List Value)
    (h_req : MirBoolPredicateHolds specBody args) :
    evalMirBoolHoldBounded fuel specBody (initMachineState specBody args) :=
  evalMirBoolExecHoldBounded_of_wpMirExecOrExhaustedSym fuel specBody
    (.running (initMachineState specBody args))
    (holdBoolMirSym_of_mirBoolPredicateHolds fuel specBody args h_req)



private theorem stepMirFn_concretize_stmt
    (body : CapturedMir) (args : List Value) (st : SymState)
    (bb : BasicBlockData) (stmt : Statement)
    (hNotOther : ∀ msg, body.phase ≠ .other msg)
    (hBb : get? body.basicBlocks st.blockIdx = some bb)
    (hStmt : get? bb.statements st.stmtIdx = some stmt) :
    stepMirFn body (concretizeSymState body args st) =
      evalStmt (concretizeSymState body args st) stmt body.localDecls body.layouts := by
  let s := concretizeSymState body args st
  change stepMirFn body s = evalStmt s stmt body.localDecls body.layouts
  have hCallee : s.memory.activeCallee = none := rfl
  have hBlk : s.frame.blockIdx = st.blockIdx := rfl
  have hSi : s.frame.stmtIdx = st.stmtIdx := rfl
  unfold stepMirFn
  rw [hCallee]
  dsimp only [Option.getD]
  split
  · next msg hm => exact False.elim (hNotOther msg hm)
  · rw [hBlk, hBb]; dsimp only
    rw [hSi, hStmt]

private theorem stepMirFn_concretize_term
    (body : CapturedMir) (args : List Value) (st : SymState)
    (bb : BasicBlockData)
    (hNotOther : ∀ msg, body.phase ≠ .other msg)
    (hBb : get? body.basicBlocks st.blockIdx = some bb)
    (hStmt : get? bb.statements st.stmtIdx = none)
    (hLen : Nat.beq st.stmtIdx (length bb.statements) = true) :
    stepMirFn body (concretizeSymState body args st) =
      evalTerminator (concretizeSymState body args st) bb.terminator (some body) := by
  let s := concretizeSymState body args st
  change stepMirFn body s = evalTerminator s bb.terminator (some body)
  have hCallee : s.memory.activeCallee = none := rfl
  have hBlk : s.frame.blockIdx = st.blockIdx := rfl
  have hSi : s.frame.stmtIdx = st.stmtIdx := rfl
  unfold stepMirFn
  rw [hCallee]
  dsimp only [Option.getD]
  split
  · next msg hm => exact False.elim (hNotOther msg hm)
  · rw [hBlk, hBb]; dsimp only
    rw [hSi, hStmt]; dsimp only
    split
    · rfl
    · next hFalse =>
      exact False.elim (hFalse (beq_iff_eq.mpr (Nat.eq_of_beq_eq_true hLen)))

theorem symStepConcrete_sound
    (fuel : Nat)
    (body : CapturedMir)
    (args : List Value)
    (st st' : SymState)
    (h : symStepConcrete body st = .some st')
    (hHold : evalMirBoolHoldBounded (.succ fuel) body (concretizeSymState body args st)) :
    evalMirBoolHoldBounded fuel body (concretizeSymState body args st') := by
  dsimp only [symStepConcrete] at h
  change stepResultHoldBounded fuel body (stepMirFn body (concretizeSymState body args st)) at hHold
  cases hPhase : body.phase with
  | other _ =>
    rw [hPhase] at h
    nomatch h
  | runtimePostCleanup | runtimeOptimized =>
    have hNotOther : ∀ msg, body.phase ≠ .other msg := by
      intro msg hm; rw [hPhase] at hm; nomatch hm
    rw [hPhase] at h
    dsimp only at h
    cases hBb : get? body.basicBlocks st.blockIdx with
    | none =>
      rw [hBb] at h
      nomatch h
    | some bb =>
      rw [hBb] at h
      dsimp only at h
      cases hStmt : get? bb.statements st.stmtIdx with
      | some stmt =>
        rw [hStmt] at h
        dsimp only at h
        rw [stepMirFn_concretize_stmt body args st bb stmt hNotOther hBb hStmt] at hHold
        rcases symStepStmtConcrete_sound body args st st' stmt h with hStep | hFail
        · rw [hStep] at hHold
          exact hHold
        · rw [hFail] at hHold
          exact False.elim hHold
      | none =>
        rw [hStmt] at h
        dsimp only at h
        cases hLen : Nat.beq st.stmtIdx (length bb.statements) with
        | false =>
          rw [hLen] at h
          nomatch h
        | true =>
          rw [hLen] at h
          dsimp only at h
          rw [stepMirFn_concretize_term body args st bb hNotOther hBb hStmt hLen] at hHold
          rcases symStepTermConcrete_sound body args st st' bb.terminator h with hTerm | ⟨ev, hTerm⟩
          · rw [hTerm] at hHold
            exact hHold
          · rw [hTerm] at hHold
            cases ev <;> exact hHold

/-- Check whether `st` is at a `Return` terminator with local `0` holding
`.scalar ⟨0, 1⟩` (`false`). -/
def symIsReturnFalse (body : CapturedMir) (st : SymState) : Bool :=
  match body.phase with
  | .other _ => false
  | _ =>
    match get? body.basicBlocks st.blockIdx with
    | .none => false
    | .some bb =>
      match get? bb.statements st.stmtIdx with
      | .some _ => false
      | .none =>
        match Nat.beq st.stmtIdx (length bb.statements) with
        | false => false
        | true =>
          match bb.terminator.kind with
          | .return_ =>
            match get? st.slots 0 with
            | .some (.concrete (.init (.scalar ⟨0, 1⟩))) => true
            | _ => false
          | _ => false

theorem symIsReturnFalse_sound
    (fuel : Nat)
    (body : CapturedMir)
    (args : List Value)
    (st : SymState)
    (h : symIsReturnFalse body st = true)
    (hHold : evalMirBoolHoldBounded (.succ fuel) body (concretizeSymState body args st)) :
    False := by
  dsimp only [symIsReturnFalse] at h
  change stepResultHoldBounded fuel body (stepMirFn body (concretizeSymState body args st)) at hHold
  cases hPhase : body.phase with
  | other _ =>
    rw [hPhase] at h
    nomatch h
  | runtimePostCleanup | runtimeOptimized =>
    have hNotOther : ∀ msg, body.phase ≠ .other msg := by
      intro msg hm; rw [hPhase] at hm; nomatch hm
    rw [hPhase] at h
    dsimp only at h
    cases hBb : get? body.basicBlocks st.blockIdx with
    | none =>
      rw [hBb] at h
      nomatch h
    | some bb =>
      rw [hBb] at h
      dsimp only at h
      cases hStmt : get? bb.statements st.stmtIdx with
      | some _ =>
        rw [hStmt] at h
        nomatch h
      | none =>
        rw [hStmt] at h
        dsimp only at h
        cases hLen : Nat.beq st.stmtIdx (length bb.statements) with
        | false =>
          rw [hLen] at h
          nomatch h
        | true =>
          rw [hLen] at h
          dsimp only at h
          rw [stepMirFn_concretize_term body args st bb hNotOther hBb hStmt hLen] at hHold
          cases hTerm : bb.terminator with
          | mk tKind _ =>
            rw [hTerm] at h hHold
            dsimp only at h
            cases tKind with
            | return_ =>
              dsimp only at h
              dsimp only [evalTerminator, concretizeSymState, concretizeSymMemory] at hHold
              rw [get?_concretizeSymSlots args st.slots 0] at hHold
              cases hGet0 : get? st.slots 0 with
              | none =>
                rw [hGet0] at h
                nomatch h
              | some sSlot0 =>
                rw [hGet0] at h hHold
                cases sSlot0 with
                | symArg _ => nomatch h
                | concrete cSlot0 =>
                  cases cSlot0 with
                  | dead | uninit => nomatch h
                  | init retVal =>
                    cases retVal with
                    | unit | ptr _ _ | aggregate _ _ => nomatch h
                    | scalar sc =>
                      cases sc with
                      | mk bits sz =>
                        cases bits with
                        | succ _ => nomatch h
                        | zero =>
                          cases sz with
                          | zero => nomatch h
                          | succ sz' =>
                            cases sz' with
                            | succ _ => nomatch h
                            | zero =>
                              dsimp only [concretizeSymSlot, stepResultHoldBounded, evalNodeWP, MirStepNode.retNormal, mirSafePost] at hHold
                              injection hHold with hSc
                              injection hSc with hBits _
                              nomatch hBits
            | _ => nomatch h

/-- Check whether concrete symbolic execution from `st` reaches `Return` with
`false` (`.scalar ⟨0, 1⟩`) within `fuel` steps. -/
def checkSymReturnsFalse : Nat → CapturedMir → SymState → Bool
  | .zero, _, _ => false
  | .succ fuel, body, st =>
    match symStepConcrete body st with
    | .some st' => checkSymReturnsFalse fuel body st'
    | .none => symIsReturnFalse body st

theorem checkSymReturnsFalse_sound :
    ∀ (fuel : Nat) (body : CapturedMir) (args : List Value) (st : SymState),
      checkSymReturnsFalse fuel body st = true →
      evalMirBoolHoldBounded fuel body (concretizeSymState body args st) →
      False
  | .zero, _, _, _, hCheck, _ => nomatch hCheck
  | .succ fuel, body, args, st, hCheck, hHold => by
    dsimp only [checkSymReturnsFalse] at hCheck
    cases hStep : symStepConcrete body st with
    | some st' =>
      rw [hStep] at hCheck
      exact checkSymReturnsFalse_sound
        fuel body args st' hCheck
        (symStepConcrete_sound fuel body args st st' hStep hHold)
    | none =>
      rw [hStep] at hCheck
      exact symIsReturnFalse_sound fuel body args st hCheck hHold


/-- Substitute `.symArg idx` with `.concrete (.init v)` in a `SymSlot`. -/
def substSymSlot (idx : Nat) (v : Value) : SymSlot → SymSlot
  | .symArg i =>
    match Nat.beq i idx with
    | true => .concrete (.init v)
    | false => .symArg i
  | .concrete c => .concrete c

/-- Substitute `.symArg idx` with `.concrete (.init v)` across `List SymSlot`. -/
def substSymSlots (idx : Nat) (v : Value) : List SymSlot → List SymSlot
  | .nil => .nil
  | s :: rest => substSymSlot idx v s :: substSymSlots idx v rest

theorem concretizeSymSlots_substSymSlots
    (args : List Value)
    (idx : Nat)
    (v : Value)
    (h_arg : get? args idx = .some v) :
    ∀ (slots : List SymSlot),
      concretizeSymSlots args (substSymSlots idx v slots) =
        concretizeSymSlots args slots
  | .nil => rfl
  | s :: rest => by
    dsimp only [substSymSlots, concretizeSymSlots]
    rw [concretizeSymSlots_substSymSlots args idx v h_arg rest]
    cases s with
    | concrete _ => rfl
    | symArg i =>
      dsimp only [substSymSlot]
      cases hEq : Nat.beq i idx with
      | false => rfl
      | true =>
        have hIdx : i = idx := Nat.eq_of_beq_eq_true hEq
        subst hIdx
        dsimp only [concretizeSymSlot]
        rw [h_arg]

/-- Complete a symbolic equality pin at `dstLoc` after evaluating both operands
to `slots₂`. -/
def symFinishPinEq
    (st : SymState)
    (dstLoc : Local)
    (slots₂ : List SymSlot)
    (idx : Nat)
    (expectedSc : ScalarInt) :
    Option (Nat × ScalarInt × SymState × SymState) :=
  match Nat.beq expectedSc.sizeBytes 0 with
  | true => .none
  | false =>
    match get? slots₂ dstLoc with
    | .none => .none
    | .some (.concrete .dead) => .none
    | .some _ =>
      match
        set? slots₂ dstLoc (.concrete (.init (.scalar ⟨1, 1⟩))),
        set? slots₂ dstLoc (.concrete (.init (.scalar ⟨0, 1⟩)))
      with
      | .some slotsTrue, .some slotsFalse =>
        let borrows' := invalidateConflictingBorrows st.borrows dstLoc .none
        let stTrue : SymState := {
          st with
          stmtIdx := Nat.add st.stmtIdx 1
          slots := substSymSlots idx (.scalar expectedSc) slotsTrue
          borrows := borrows'
        }
        let stFalse : SymState := {
          st with
          stmtIdx := Nat.add st.stmtIdx 1
          slots := slotsFalse
          borrows := borrows'
        }
        .some (idx, expectedSc, stTrue, stFalse)
      | _, _ => .none

/-- Extract a symbolic equality pin `(idx, expectedSc, stTrue, stFalse)` from
`stmt` when `stmt` is `.assign ⟨dstLoc, .nil⟩ (.binaryOp .eq lhsOp rhsOp)` comparing
`.symArg idx` against `.concrete (.scalar expectedSc)`. -/
def symExtractPinEqStmt
    (st : SymState)
    (stmt : Statement) :
    Option (Nat × ScalarInt × SymState × SymState) :=
  match stmt.kind with
  | .assign ⟨dstLoc, .nil⟩ (.binaryOp .eq lhsOp rhsOp) =>
    match evalSymOperand st.slots lhsOp st.borrows with
    | .some (sv₁, slots₁) =>
      match evalSymOperand slots₁ rhsOp st.borrows with
      | .some (sv₂, slots₂) =>
        match sv₁, sv₂ with
        | .symArg idx, .concrete (.scalar sc) =>
          symFinishPinEq st dstLoc slots₂ idx sc
        | .concrete (.scalar sc), .symArg idx =>
          symFinishPinEq st dstLoc slots₂ idx sc
        | _, _ => .none
      | .none => .none
    | .none => .none
  | _ => .none

/-- Extract a symbolic equality pin from the current statement of `body` at `st`. -/
def symExtractPinEq
    (body : CapturedMir)
    (st : SymState) :
    Option (Nat × ScalarInt × SymState × SymState) :=
  match body.phase with
  | .other _ => .none
  | _ =>
    match get? body.basicBlocks st.blockIdx with
    | .none => .none
    | .some bb =>
      match get? bb.statements st.stmtIdx with
      | .some stmt => symExtractPinEqStmt st stmt
      | .none => .none

theorem scalarInt_eq_of_parts
    {a b : ScalarInt}
    (hBits : a.bits = b.bits)
    (hSz : a.sizeBytes = b.sizeBytes) :
    a = b := by
  cases a
  cases b
  dsimp only at hBits hSz
  subst hBits
  subst hSz
  rfl

/-- Destination root-local write step of `evalStmt` on `.assign ⟨dstLoc, .nil⟩ rv`. -/
def evalAssignNilRvalueStep
    (s : MachineState)
    (dstLoc : Local)
    (rRes : RvalueEvalResult) :
    MirStepNode :=
  match rRes with
  | .ok val locals₁ mem₁ =>
    match get? locals₁ dstLoc with
    | .some .dead => MirStepNode.fail .ub
    | .some _ =>
      match set? locals₁ dstLoc (.init val) with
      | .some locals₂ =>
        match mem₁.activeProtectors with
        | .nil =>
          let borrows' := invalidateConflictingBorrows mem₁.borrows dstLoc .none
          MirStepNode.step (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
        | protHead :: protTail =>
          match hasProtectedWriteConflict mem₁.borrows (protHead :: protTail) dstLoc .none .nil with
          | true => MirStepNode.fail .ub
          | false =>
            let borrows' := invalidateConflictingBorrows mem₁.borrows dstLoc .none
            MirStepNode.step (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
      | .none => MirStepNode.fail .ub
    | .none => MirStepNode.fail .ub
  | .ub => MirStepNode.fail .ub
  | .unsupported => MirStepNode.unsupported

theorem evalStmt_assign_nil_eq
    (s : MachineState)
    (dstLoc : Local)
    (rv : Rvalue)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    evalStmt s ⟨.assign ⟨dstLoc, .nil⟩ rv, span⟩ localDecls layouts =
      evalAssignNilRvalueStep s dstLoc (evalRvalue s.frame.locals rv s.memory localDecls layouts) := by
  dsimp only [evalStmt, evalAssignNilRvalueStep]
  cases evalRvalue s.frame.locals rv s.memory localDecls layouts <;> rfl

theorem symFinishPinEq_branch_ok_sound
    (fuel : Nat)
    (body : CapturedMir)
    (args : List Value)
    (st : SymState)
    (dstLoc : Local)
    (slots₂ : List SymSlot)
    (idx : Nat)
    (expectedSc : ScalarInt)
    (idxOut : Nat)
    (scOut : ScalarInt)
    (stTrue stFalse : SymState)
    (cmp : Bool)
    (hFin : symFinishPinEq st dstLoc slots₂ idx expectedSc = .some (idxOut, scOut, stTrue, stFalse))
    (hHold :
      stepResultHoldBounded fuel body
        (evalAssignNilRvalueStep
          (concretizeSymState body args st)
          dstLoc
          (.ok (.scalar (boolToScalar cmp)) (concretizeSymSlots args slots₂) (concretizeSymMemory body st)))) :
    idxOut = idx ∧
      scOut = expectedSc ∧
      ((cmp = true ∧
        (get? args idx = .some (.scalar expectedSc) →
          evalMirBoolHoldBounded fuel body (concretizeSymState body args stTrue))) ∨
       evalMirBoolHoldBounded fuel body (concretizeSymState body args stFalse)) := by
  dsimp only [symFinishPinEq] at hFin
  cases hExpSz0 : Nat.beq expectedSc.sizeBytes 0 with
  | true =>
    rw [hExpSz0] at hFin
    nomatch hFin
  | false =>
    rw [hExpSz0] at hFin
    dsimp only at hFin
    cases hGetDst : get? slots₂ dstLoc with
    | none =>
      rw [hGetDst] at hFin
      nomatch hFin
    | some dstSlot =>
      rw [hGetDst] at hFin
      cases dstSlot with
      | symArg dstArgIdx =>
        dsimp only at hFin
        cases hSetT : set? slots₂ dstLoc (.concrete (.init (.scalar ⟨1, 1⟩))) with
        | none =>
          rw [hSetT] at hFin
          nomatch hFin
        | some slotsTrue =>
          rw [hSetT] at hFin
          cases hSetF : set? slots₂ dstLoc (.concrete (.init (.scalar ⟨0, 1⟩))) with
          | none =>
            rw [hSetF] at hFin
            nomatch hFin
          | some slotsFalse =>
            rw [hSetF] at hFin
            injection hFin with hTup
            injection hTup with hIdx hRest1
            injection hRest1 with hSc hRest2
            injection hRest2 with hStT hStF
            subst hIdx; subst hSc; subst hStT; subst hStF
            dsimp only [evalAssignNilRvalueStep, concretizeSymMemory] at hHold
            rw [get?_concretizeSymSlots args slots₂ dstLoc, hGetDst] at hHold
            dsimp only [concretizeSymSlot] at hHold
            have hHoldAfterGet :
                stepResultHoldBounded fuel body
                  (match set? (concretizeSymSlots args slots₂) dstLoc (.init (.scalar (boolToScalar cmp))) with
                  | .some locals₂ =>
                    let borrows' := invalidateConflictingBorrows st.borrows dstLoc .none
                    MirStepNode.step
                      (advanceStmt (concretizeSymState body args st) locals₂
                        { (concretizeSymMemory body st) with borrows := borrows' })
                  | .none => MirStepNode.fail .ub) := by
              cases hArgDst : get? args dstArgIdx with
              | none =>
                rw [hArgDst] at hHold
                exact hHold
              | some _ =>
                rw [hArgDst] at hHold
                exact hHold
            cases cmp with
            | false =>
              dsimp only [boolToScalar] at hHoldAfterGet
              rw [set?_concretizeSymSlots_concrete args (.init (.scalar ⟨0, 1⟩)) slots₂ dstLoc, hSetF] at hHoldAfterGet
              dsimp only [stepResultHoldBounded, evalNodeWP, MirStepNode.step] at hHoldAfterGet
              exact ⟨rfl, rfl, Or.inr hHoldAfterGet⟩
            | true =>
              dsimp only [boolToScalar] at hHoldAfterGet
              rw [set?_concretizeSymSlots_concrete args (.init (.scalar ⟨1, 1⟩)) slots₂ dstLoc, hSetT] at hHoldAfterGet
              dsimp only [stepResultHoldBounded, evalNodeWP, MirStepNode.step] at hHoldAfterGet
              refine ⟨rfl, rfl, Or.inl ⟨rfl, fun hArg => ?_⟩⟩
              dsimp only [concretizeSymState, advanceStmt, concretizeSymMemory] at hHoldAfterGet ⊢
              rw [concretizeSymSlots_substSymSlots args idx (.scalar expectedSc) hArg slotsTrue]
              exact hHoldAfterGet
      | concrete cDst =>
        cases cDst with
        | dead => nomatch hFin
        | uninit | init _ =>
          dsimp only at hFin
          cases hSetT : set? slots₂ dstLoc (.concrete (.init (.scalar ⟨1, 1⟩))) with
          | none =>
            rw [hSetT] at hFin
            nomatch hFin
          | some slotsTrue =>
            rw [hSetT] at hFin
            cases hSetF : set? slots₂ dstLoc (.concrete (.init (.scalar ⟨0, 1⟩))) with
            | none =>
              rw [hSetF] at hFin
              nomatch hFin
            | some slotsFalse =>
              rw [hSetF] at hFin
              injection hFin with hTup
              injection hTup with hIdx hRest1
              injection hRest1 with hSc hRest2
              injection hRest2 with hStT hStF
              subst hIdx; subst hSc; subst hStT; subst hStF
              dsimp only [evalAssignNilRvalueStep, concretizeSymMemory] at hHold
              rw [get?_concretizeSymSlots args slots₂ dstLoc, hGetDst] at hHold
              dsimp only [concretizeSymSlot] at hHold
              cases cmp with
              | false =>
                dsimp only [boolToScalar] at hHold
                rw [set?_concretizeSymSlots_concrete args (.init (.scalar ⟨0, 1⟩)) slots₂ dstLoc, hSetF] at hHold
                dsimp only [stepResultHoldBounded, evalNodeWP, MirStepNode.step] at hHold
                exact ⟨rfl, rfl, Or.inr hHold⟩
              | true =>
                dsimp only [boolToScalar] at hHold
                rw [set?_concretizeSymSlots_concrete args (.init (.scalar ⟨1, 1⟩)) slots₂ dstLoc, hSetT] at hHold
                dsimp only [stepResultHoldBounded, evalNodeWP, MirStepNode.step] at hHold
                refine ⟨rfl, rfl, Or.inl ⟨rfl, fun hArg => ?_⟩⟩
                dsimp only [concretizeSymState, advanceStmt, concretizeSymMemory] at hHold ⊢
                rw [concretizeSymSlots_substSymSlots args idx (.scalar expectedSc) hArg slotsTrue]
                exact hHold

theorem symFinishPinEq_expSz0_false
    {st : SymState}
    {dstLoc : Local}
    {slots₂ : List SymSlot}
    {idx : Nat}
    {expectedSc : ScalarInt}
    {idxOut : Nat}
    {scOut : ScalarInt}
    {stTrue stFalse : SymState}
    (hFin : symFinishPinEq st dstLoc slots₂ idx expectedSc = .some (idxOut, scOut, stTrue, stFalse)) :
    Nat.beq expectedSc.sizeBytes 0 = false := by
  dsimp only [symFinishPinEq] at hFin
  cases h : Nat.beq expectedSc.sizeBytes 0 with
  | false => rfl
  | true =>
    rw [h] at hFin
    nomatch hFin

theorem symExtractPinEq_branch_sound
    (fuel : Nat)
    (body : CapturedMir)
    (args : List Value)
    (st : SymState)
    (idx : Nat)
    (expectedSc : ScalarInt)
    (stTrue stFalse : SymState)
    (hExt : symExtractPinEq body st = .some (idx, expectedSc, stTrue, stFalse))
    (hHold : evalMirBoolHoldBounded (.succ fuel) body (concretizeSymState body args st)) :
    (get? args idx = .some (.scalar expectedSc) ∧
      evalMirBoolHoldBounded fuel body (concretizeSymState body args stTrue)) ∨
    evalMirBoolHoldBounded fuel body (concretizeSymState body args stFalse) := by
  dsimp only [symExtractPinEq] at hExt
  change stepResultHoldBounded fuel body (stepMirFn body (concretizeSymState body args st)) at hHold
  unfold stepMirFn at hHold
  simp only [concretizeSymState, concretizeSymMemory, Option.getD] at hHold
  cases hPhase : body.phase with
  | other _ =>
    rw [hPhase] at hExt
    nomatch hExt
  | runtimePostCleanup | runtimeOptimized =>
    rw [hPhase] at hExt hHold
    dsimp only at hExt hHold
    cases hBb : get? body.basicBlocks st.blockIdx with
    | none =>
      rw [hBb] at hExt
      nomatch hExt
    | some bb =>
      rw [hBb] at hExt hHold
      dsimp only at hExt hHold
      cases hStmt : get? bb.statements st.stmtIdx with
      | none =>
        rw [hStmt] at hExt
        nomatch hExt
      | some stmt =>
        rw [hStmt] at hExt hHold
        dsimp only at hExt hHold
        cases stmt with
        | mk kind _ =>
          cases kind with
          | assign dst rv =>
            cases dst with
            | mk dstLoc dstProj =>
              cases dstProj with
              | cons _ _ => nomatch hExt
              | nil =>
                cases rv with
                | binaryOp op lhsOp rhsOp =>
                  cases op with
                  | eq =>
                    dsimp only [symExtractPinEqStmt] at hExt
                    rw [evalStmt_assign_nil_eq] at hHold
                    dsimp only [evalRvalue] at hHold
                    cases hLhs : evalSymOperand st.slots lhsOp st.borrows with
                    | none =>
                      rw [hLhs] at hExt
                      nomatch hExt
                    | some pair1 =>
                      rw [hLhs] at hExt
                      cases pair1 with
                      | mk sv1 slots1 =>
                        dsimp only at hExt
                        cases hRhs : evalSymOperand slots1 rhsOp st.borrows with
                        | none =>
                          rw [hRhs] at hExt
                          nomatch hExt
                        | some pair2 =>
                          rw [hRhs] at hExt
                          cases pair2 with
                          | mk sv2 slots2 =>
                            dsimp only at hExt
                            rw [evalSymOperand_sound
                              args st.slots lhsOp st.borrows body.allocations body.layouts
                              sv1 slots1 hLhs] at hHold
                            cases sv1 with
                            | symArg idx0 =>
                              cases sv2 with
                              | symArg _ => nomatch hExt
                              | concrete v2 =>
                                cases v2 with
                                | unit | ptr _ _ | aggregate _ _ => nomatch hExt
                                | scalar sc0 =>
                                  dsimp only at hExt
                                  dsimp only [concretizeSymReadResult] at hHold
                                  cases hArg0 : get? args idx0 with
                                  | none =>
                                    rw [hArg0] at hHold
                                    exact False.elim hHold
                                  | some vArg0 =>
                                    rw [hArg0] at hHold
                                    dsimp only at hHold
                                    rw [evalSymOperand_sound
                                      args slots1 rhsOp st.borrows body.allocations body.layouts
                                      (.concrete (.scalar sc0)) slots2 hRhs] at hHold
                                    dsimp only [concretizeSymReadResult] at hHold
                                    cases vArg0 with
                                    | unit | ptr _ _ | aggregate _ _ =>
                                      exact False.elim hHold
                                    | scalar actualSc =>
                                      dsimp only [evalScalarBinOp] at hHold
                                      cases hActSz0 : Nat.beq actualSc.sizeBytes 0 with
                                      | true =>
                                        rw [hActSz0] at hHold
                                        exact False.elim hHold
                                      | false =>
                                        rw [hActSz0] at hHold
                                        dsimp only at hHold
                                        cases hSzEq : Nat.beq actualSc.sizeBytes sc0.sizeBytes with
                                        | false =>
                                          rw [hSzEq] at hHold
                                          exact False.elim hHold
                                        | true =>
                                          rw [hSzEq] at hHold
                                          dsimp only at hHold
                                          have ⟨hIdxEq, hScOutEq, hBranch⟩ :=
                                            symFinishPinEq_branch_ok_sound
                                              fuel body args st dstLoc slots2 idx0 sc0
                                              idx expectedSc stTrue stFalse
                                              (Nat.beq actualSc.bits sc0.bits)
                                              hExt hHold
                                          cases hBranch with
                                          | inr hFalseHold => exact Or.inr hFalseHold
                                          | inl hTruePair =>
                                            have hScEq : actualSc = sc0 :=
                                              scalarInt_eq_of_parts
                                                (Nat.eq_of_beq_eq_true hTruePair.1)
                                                (Nat.eq_of_beq_eq_true hSzEq)
                                            rw [hIdxEq, hScOutEq]
                                            rw [← hScEq]
                                            exact Or.inl ⟨hArg0, hTruePair.2 (by rw [← hScEq]; exact hArg0)⟩
                            | concrete v1 =>
                              cases v1 with
                              | unit | ptr _ _ | aggregate _ _ => nomatch hExt
                              | scalar sc0 =>
                                cases sv2 with
                                | concrete _ => nomatch hExt
                                | symArg idx0 =>
                                  dsimp only at hExt
                                  dsimp only [concretizeSymReadResult] at hHold
                                  rw [evalSymOperand_sound
                                    args slots1 rhsOp st.borrows body.allocations body.layouts
                                    (.symArg idx0) slots2 hRhs] at hHold
                                  dsimp only [concretizeSymReadResult] at hHold
                                  cases hArg0 : get? args idx0 with
                                  | none =>
                                    rw [hArg0] at hHold
                                    exact False.elim hHold
                                  | some vArg0 =>
                                    rw [hArg0] at hHold
                                    dsimp only at hHold
                                    cases vArg0 with
                                    | unit | ptr _ _ | aggregate _ _ =>
                                      exact False.elim hHold
                                    | scalar actualSc =>
                                      dsimp only [evalScalarBinOp] at hHold
                                      rw [symFinishPinEq_expSz0_false hExt] at hHold
                                      dsimp only at hHold
                                      cases hSzEq : Nat.beq sc0.sizeBytes actualSc.sizeBytes with
                                      | false =>
                                        rw [hSzEq] at hHold
                                        exact False.elim hHold
                                      | true =>
                                        rw [hSzEq] at hHold
                                        dsimp only at hHold
                                        have ⟨hIdxEq, hScOutEq, hBranch⟩ :=
                                          symFinishPinEq_branch_ok_sound
                                            fuel body args st dstLoc slots2 idx0 sc0
                                            idx expectedSc stTrue stFalse
                                            (Nat.beq sc0.bits actualSc.bits)
                                            hExt hHold
                                        cases hBranch with
                                        | inr hFalseHold => exact Or.inr hFalseHold
                                        | inl hTruePair =>
                                          have hScEq : sc0 = actualSc :=
                                            scalarInt_eq_of_parts
                                              (Nat.eq_of_beq_eq_true hTruePair.1)
                                              (Nat.eq_of_beq_eq_true hSzEq)
                                          rw [hIdxEq, hScOutEq, hScEq]
                                          exact Or.inl ⟨hArg0, hTruePair.2 (by rw [hScEq]; exact hArg0)⟩
                  | _ => nomatch hExt
                | _ => nomatch hExt
          | _ => nomatch hExt

theorem symExtractPinEq_sound
    (fuel : Nat)
    (body : CapturedMir)
    (args : List Value)
    (st : SymState)
    (idx : Nat)
    (expectedSc : ScalarInt)
    (stTrue stFalse : SymState)
    (hExt : symExtractPinEq body st = .some (idx, expectedSc, stTrue, stFalse))
    (hFalse : checkSymReturnsFalse fuel body stFalse = true)
    (hHold : evalMirBoolHoldBounded (.succ fuel) body (concretizeSymState body args st)) :
    get? args idx = .some (.scalar expectedSc) ∧
      evalMirBoolHoldBounded fuel body (concretizeSymState body args stTrue) := by
  cases symExtractPinEq_branch_sound fuel body args st idx expectedSc stTrue stFalse hExt hHold with
  | inl hTrue => exact hTrue
  | inr hFalseHold => exact False.elim (checkSymReturnsFalse_sound fuel body args stFalse hFalse hFalseHold)


/-- Conjunction of `get? args idx = .some (.scalar sc)` across a list of
`(idx, sc)` scalar pin obligations. -/
def AllScalarPinsHold (args : List Value) : List (Nat × ScalarInt) → Prop
  | .nil => True
  | (idx, sc) :: rest =>
    get? args idx = .some (.scalar sc) ∧ AllScalarPinsHold args rest

/-- Remove the first occurrence of `(idx, sc)` from `pins` if present. -/
def removeScalarPin (idx : Nat) (sc : ScalarInt) :
    List (Nat × ScalarInt) → Option (List (Nat × ScalarInt))
  | .nil => .none
  | (i, s) :: rest =>
    match Bool.and (Nat.beq i idx) (Bool.and (Nat.beq s.bits sc.bits) (Nat.beq s.sizeBytes sc.sizeBytes)) with
    | true => .some rest
    | false =>
      match removeScalarPin idx sc rest with
      | .some rest' => .some ((i, s) :: rest')
      | .none => .none

theorem allScalarPinsHold_of_removeScalarPin
    (args : List Value)
    (idx : Nat)
    (sc : ScalarInt)
    (hHead : get? args idx = .some (.scalar sc)) :
    ∀ (pins pins' : List (Nat × ScalarInt)),
      removeScalarPin idx sc pins = .some pins' →
      AllScalarPinsHold args pins' →
      AllScalarPinsHold args pins
  | .nil, _, hRem, _ => nomatch hRem
  | (i, s) :: rest, pins', hRem, hRestHold => by
    dsimp only [removeScalarPin] at hRem
    cases hEqIdx : Nat.beq i idx with
    | true =>
      rw [hEqIdx] at hRem
      cases hEqBits : Nat.beq s.bits sc.bits with
      | true =>
        rw [hEqBits] at hRem
        cases hEqSz : Nat.beq s.sizeBytes sc.sizeBytes with
        | true =>
          rw [hEqSz] at hRem
          injection hRem with hPins
          subst hPins
          have hIdx : i = idx := Nat.eq_of_beq_eq_true hEqIdx
          have hSc : s = sc :=
            scalarInt_eq_of_parts
              (Nat.eq_of_beq_eq_true hEqBits)
              (Nat.eq_of_beq_eq_true hEqSz)
          subst hIdx
          subst hSc
          exact ⟨hHead, hRestHold⟩
        | false =>
          rw [hEqSz] at hRem
          dsimp only [Bool.and] at hRem
          cases hRec : removeScalarPin idx sc rest with
          | none =>
            rw [hRec] at hRem
            nomatch hRem
          | some rest' =>
            rw [hRec] at hRem
            injection hRem with hPins
            subst hPins
            exact ⟨hRestHold.1, allScalarPinsHold_of_removeScalarPin args idx sc hHead rest rest' hRec hRestHold.2⟩
      | false =>
        rw [hEqBits] at hRem
        dsimp only [Bool.and] at hRem
        cases hRec : removeScalarPin idx sc rest with
        | none =>
          rw [hRec] at hRem
          nomatch hRem
        | some rest' =>
          rw [hRec] at hRem
          injection hRem with hPins
          subst hPins
          exact ⟨hRestHold.1, allScalarPinsHold_of_removeScalarPin args idx sc hHead rest rest' hRec hRestHold.2⟩
    | false =>
      rw [hEqIdx] at hRem
      dsimp only [Bool.and] at hRem
      cases hRec : removeScalarPin idx sc rest with
      | none =>
        rw [hRec] at hRem
        nomatch hRem
      | some rest' =>
        rw [hRec] at hRem
        injection hRem with hPins
        subst hPins
        exact ⟨hRestHold.1, allScalarPinsHold_of_removeScalarPin args idx sc hHead rest rest' hRec hRestHold.2⟩

/-- Symbolic abstract interpreter loop verifying that `body` from `st` pins all
`(idx, sc)` obligations in `pins`. -/
def checkSymPinsLoop : Nat → CapturedMir → SymState → List (Nat × ScalarInt) → Bool
  | _, _, _, .nil => true
  | .zero, _, _, _ :: _ => false
  | .succ fuel, body, st, p :: ps =>
    match symStepConcrete body st with
    | .some st' => checkSymPinsLoop fuel body st' (p :: ps)
    | .none =>
      match symExtractPinEq body st with
      | .some (idx, sc, stTrue, stFalse) =>
        match checkSymReturnsFalse fuel body stFalse with
        | false => false
        | true =>
          match removeScalarPin idx sc (p :: ps) with
          | .some pins' => checkSymPinsLoop fuel body stTrue pins'
          | .none => checkSymPinsLoop fuel body stTrue (p :: ps)
      | .none => false

theorem checkSymPinsLoop_sound :
    ∀ (fuel : Nat)
      (body : CapturedMir)
      (args : List Value)
      (st : SymState)
      (pins : List (Nat × ScalarInt)),
      checkSymPinsLoop fuel body st pins = true →
      evalMirBoolHoldBounded fuel body (concretizeSymState body args st) →
      AllScalarPinsHold args pins
  | _, _, _, _, .nil, _, _ => True.intro
  | .zero, _, _, _, _ :: _, hCheck, _ => nomatch hCheck
  | .succ fuel, body, args, st, p :: ps, hCheck, hHold => by
    dsimp only [checkSymPinsLoop] at hCheck
    cases hStep : symStepConcrete body st with
    | some st' =>
      rw [hStep] at hCheck
      exact checkSymPinsLoop_sound
        fuel body args st' (p :: ps) hCheck
        (symStepConcrete_sound fuel body args st st' hStep hHold)
    | none =>
      rw [hStep] at hCheck
      cases hExt : symExtractPinEq body st with
      | none =>
        rw [hExt] at hCheck
        nomatch hCheck
      | some tup =>
        rw [hExt] at hCheck
        cases tup with
        | mk idx rest1 =>
          cases rest1 with
          | mk sc rest2 =>
            cases rest2 with
            | mk stTrue stFalse =>
              dsimp only at hCheck
              cases hFalse : checkSymReturnsFalse fuel body stFalse with
              | false =>
                rw [hFalse] at hCheck
                nomatch hCheck
              | true =>
                rw [hFalse] at hCheck
                dsimp only at hCheck
                have ⟨hPinIdx, hHoldTrue⟩ :=
                  symExtractPinEq_sound fuel body args st idx sc stTrue stFalse hExt hFalse hHold
                cases hRem : removeScalarPin idx sc (p :: ps) with
                | some pins' =>
                  rw [hRem] at hCheck
                  have hRestHold :=
                    checkSymPinsLoop_sound fuel body args stTrue pins' hCheck hHoldTrue
                  exact allScalarPinsHold_of_removeScalarPin args idx sc hPinIdx (p :: ps) pins' hRem hRestHold
                | none =>
                  rw [hRem] at hCheck
                  exact checkSymPinsLoop_sound fuel body args stTrue (p :: ps) hCheck hHoldTrue

/-- Pair each `ScalarInt` in `xs` with its 0-based argument index starting at `idx`. -/
def zipIdxScalars : Nat → List ScalarInt → List (Nat × ScalarInt)
  | _, .nil => .nil
  | idx, sc :: rest => (idx, sc) :: zipIdxScalars (.succ idx) rest

/-- Map a `List ScalarInt` to `List Value` via `Value.scalar`. -/
def mapScalarValues : List ScalarInt → List Value
  | .nil => .nil
  | sc :: rest => .scalar sc :: mapScalarValues rest

theorem args_eq_mapScalarValues_of_pins
    (args : List Value) :
    ∀ (expected : List ScalarInt)
      (remArgs : List Value)
      (idx : Nat),
      dropValues idx args = remArgs →
      length remArgs = length expected →
      AllScalarPinsHold args (zipIdxScalars idx expected) →
      remArgs = mapScalarValues expected
  | .nil, .nil, _, _, _, _ => rfl
  | .nil, _ :: _, _, _, hLen, _ => nomatch hLen
  | _ :: _, .nil, _, _, hLen, _ => nomatch hLen
  | sc :: restSc, v :: restArgs, idx, hDrop, hLen, ⟨hPin, hRestPins⟩ => by
    rw [get?_eq_head_dropValues args idx, hDrop] at hPin
    injection hPin with hV
    subst hV
    have hNextDrop := dropValues_succ_of_cons args idx (.scalar sc) restArgs hDrop
    dsimp only [length] at hLen
    injection hLen with hLenRest
    dsimp only [mapScalarValues]
    rw [args_eq_mapScalarValues_of_pins args restSc restArgs (.succ idx) hNextDrop hLenRest hRestPins]

theorem args_eq_mapScalarValues
    (args : List Value)
    (expected : List ScalarInt)
    (hLen : length args = length expected)
    (hPins : AllScalarPinsHold args (zipIdxScalars 0 expected)) :
    args = mapScalarValues expected :=
  args_eq_mapScalarValues_of_pins args expected args 0 rfl hLen hPins

/-- Closed-term boolean checker verifying that `specBody` (within `fuel` steps)
pins its `argCount` parameters to `expectedScalars`. -/
def checkMirRequiresPinsScalars
    (fuel : Nat)
    (specBody : CapturedMir)
    (expectedScalars : List ScalarInt) :
    Bool :=
  Bool.and
    (Nat.beq specBody.argCount (length expectedScalars))
    (checkSymPinsLoop fuel specBody (initSymState specBody) (zipIdxScalars 0 expectedScalars))


/--
Soundness theorem for `checkMirRequiresPinsScalars`: when
`checkMirRequiresPinsScalars fuel specBody expectedScalars = true`, any argument
list `args` of length `length expectedScalars` satisfying
`MirBoolPredicateHolds specBody args` is equal to `mapScalarValues expectedScalars`.
-/
theorem checkMirRequiresPinsScalars_sound
    (fuel : Nat)
    (specBody : CapturedMir)
    (expectedScalars : List ScalarInt)
    (args : List Value)
    (h_check : checkMirRequiresPinsScalars fuel specBody expectedScalars = true)
    (h_len : length args = length expectedScalars)
    (h_req : MirBoolPredicateHolds specBody args) :
    args = mapScalarValues expectedScalars := by
  dsimp only [checkMirRequiresPinsScalars] at h_check
  cases hArgEq : Nat.beq specBody.argCount (length expectedScalars) with
  | false =>
    rw [hArgEq] at h_check
    nomatch h_check
  | true =>
    rw [hArgEq] at h_check
    dsimp only [Bool.and] at h_check
    have hHold : evalMirBoolHoldBounded fuel specBody (initMachineState specBody args) :=
      wpBoolOrExhausted_of_mirBoolPredicateHolds fuel specBody args h_req
    have hLenSpec : length args = specBody.argCount :=
      Eq.trans h_len (Eq.symm (Nat.eq_of_beq_eq_true hArgEq))
    rw [← concretizeSymState_initSymState specBody args hLenSpec] at hHold
    have hPins :=
      checkSymPinsLoop_sound
        fuel specBody args (initSymState specBody)
        (zipIdxScalars 0 expectedScalars)
        h_check hHold
    exact args_eq_mapScalarValues args expectedScalars h_len hPins

end PinChecker

/-! ## Pinned `#[spec]` Equality Discharge Combinators (`dischargeRustEqScalar1`/`2`/`3`) -/

/--
Width-parametric one-call discharge combinator for a 1-argument scalar function
annotated with `#[spec(requires: x == constVal, ensures: ...)]` against
`defaultSpec`, using closed-term `checkMirRequiresPinsScalars` (`:= by rfl`).
-/
theorem dischargeRustEqScalar1
    (width : Nat)
    (c : Claim)
    (subjectFuel specFuel : Nat)
    (reqBody ensBody : CapturedMir)
    (constVal : Nat)
    (h_pre :
      ∀ args : List Value,
        c.pre args →
        And
          (Trusted.Sequence.length args = 1)
          (MirBoolPredicateHolds reqBody args) := by
      intro _ h; exact h)
    (h_pins :
      checkMirRequiresPinsScalars
        specFuel
        reqBody
        [{ bits := constVal, sizeBytes := width }] = true := by rfl)
    (h_check :
      checkMirRustPinnedSpec
        subjectFuel
        specFuel
        c.body
        ensBody
        [.scalar { bits := constVal, sizeBytes := width }] =
        true := by rfl)
    (h_post :
      ∀ ret : Value,
        MirBoolPredicateHolds
          ensBody
          ([.scalar { bits := constVal, sizeBytes := width }] ++ [ret]) →
        c.post [.scalar { bits := constVal, sizeBytes := width }] ret := by
      intro _ h; exact h) :
    VerificationResult c := by
  refine verifyMirBounded c subjectFuel (fun args hp => ?_)
  rcases h_pre args hp with ⟨h_len, h_req⟩
  have h_args : args = [.scalar { bits := constVal, sizeBytes := width }] :=
    checkMirRequiresPinsScalars_sound
      specFuel reqBody [{ bits := constVal, sizeBytes := width }] args
      h_pins h_len h_req
  subst h_args
  have h_wp :=
    wpMirBounded_of_checkMirRustPinnedSpec
      subjectFuel specFuel c.body ensBody
      [.scalar { bits := constVal, sizeBytes := width }]
      h_check
  exact wpMirSym_eq_wpMirBounded subjectFuel c.body _ _ ▸
    wpMirSym_mono
      (fun out ho retVal mem' h_out => h_post retVal (ho retVal mem' h_out))
      (wpMirSym_eq_wpMirBounded subjectFuel c.body _ _ ▸ h_wp)

/-- One-call discharge combinator for 1-argument `u8` equality `#[spec]`. -/
abbrev dischargeRustEqU8 := @dischargeRustEqScalar1 1

/-- One-call discharge combinator for 1-argument `u16` equality `#[spec]`. -/
abbrev dischargeRustEqU16 := @dischargeRustEqScalar1 2

/-- One-call discharge combinator for 1-argument `u32` equality `#[spec]`. -/
abbrev dischargeRustEqU32 := @dischargeRustEqScalar1 4

/-- One-call discharge combinator for 1-argument `u64` equality `#[spec]`. -/
abbrev dischargeRustEqU64 := @dischargeRustEqScalar1 8

/-- One-call discharge combinator for 1-argument `usize` equality `#[spec]`. -/
abbrev dischargeRustEqUsize := @dischargeRustEqU64

/--
Width-parametric one-call discharge combinator for a 2-argument scalar function
annotated with `#[spec(requires: x == c1 && y == c2, ensures: ...)]` against
`defaultSpec`, using closed-term `checkMirRequiresPinsScalars` (`:= by rfl`).
-/
theorem dischargeRustEqScalar2
    (w1 w2 : Nat)
    (c : Claim)
    (subjectFuel specFuel : Nat)
    (reqBody ensBody : CapturedMir)
    (c1 c2 : Nat)
    (h_pre :
      ∀ args : List Value,
        c.pre args →
        And
          (Trusted.Sequence.length args = 2)
          (MirBoolPredicateHolds reqBody args) := by
      intro _ h; exact h)
    (h_pins :
      checkMirRequiresPinsScalars
        specFuel
        reqBody
        [ { bits := c1, sizeBytes := w1 }
        , { bits := c2, sizeBytes := w2 } ] = true := by rfl)
    (h_check :
      checkMirRustPinnedSpec
        subjectFuel
        specFuel
        c.body
        ensBody
        [ .scalar { bits := c1, sizeBytes := w1 }
        , .scalar { bits := c2, sizeBytes := w2 } ] =
        true := by rfl)
    (h_post :
      ∀ ret : Value,
        MirBoolPredicateHolds
          ensBody
          ([ .scalar { bits := c1, sizeBytes := w1 }
           , .scalar { bits := c2, sizeBytes := w2 } ] ++ [ret]) →
        c.post
          [ .scalar { bits := c1, sizeBytes := w1 }
          , .scalar { bits := c2, sizeBytes := w2 } ]
          ret := by
      intro _ h; exact h) :
    VerificationResult c := by
  refine verifyMirBounded c subjectFuel (fun args hp => ?_)
  rcases h_pre args hp with ⟨h_len, h_req⟩
  have h_args :
      args =
        [ .scalar { bits := c1, sizeBytes := w1 }
        , .scalar { bits := c2, sizeBytes := w2 } ] :=
    checkMirRequiresPinsScalars_sound
      specFuel reqBody
      [ { bits := c1, sizeBytes := w1 }
      , { bits := c2, sizeBytes := w2 } ]
      args h_pins h_len h_req
  subst h_args
  have h_wp :=
    wpMirBounded_of_checkMirRustPinnedSpec
      subjectFuel specFuel c.body ensBody
      [ .scalar { bits := c1, sizeBytes := w1 }
      , .scalar { bits := c2, sizeBytes := w2 } ]
      h_check
  exact wpMirSym_eq_wpMirBounded subjectFuel c.body _ _ ▸
    wpMirSym_mono
      (fun out ho retVal mem' h_out => h_post retVal (ho retVal mem' h_out))
      (wpMirSym_eq_wpMirBounded subjectFuel c.body _ _ ▸ h_wp)

/-- One-call discharge combinator for 2-argument `(u8, u8)` equality `#[spec]`. -/
abbrev dischargeRustEq2U8 := @dischargeRustEqScalar2 1 1

/-- One-call discharge combinator for 2-argument `(u16, u16)` equality `#[spec]`. -/
abbrev dischargeRustEq2U16 := @dischargeRustEqScalar2 2 2

/-- One-call discharge combinator for 2-argument `(u32, u32)` equality `#[spec]`. -/
abbrev dischargeRustEq2U32 := @dischargeRustEqScalar2 4 4

/-- One-call discharge combinator for 2-argument `(u64, u64)` equality `#[spec]`. -/
abbrev dischargeRustEq2U64 := @dischargeRustEqScalar2 8 8

/-! ## Bitwise Masking, Byte-Swapping, and `UInt8.ofNat` `@[simp]` Lemmas -/

@[simp]
theorem uint8_ofNat_toBitVec_toNat (n : Nat) :
    (UInt8.ofNat n).toBitVec.toNat = n % 256 := rfl

theorem uint8_ofNat_toBitVec_toNat_of_lt {n : Nat} (h : n < 256) :
    (UInt8.ofNat n).toBitVec.toNat = n := by
  rw [uint8_ofNat_toBitVec_toNat]
  exact Nat.mod_eq_of_lt h

@[simp]
theorem bitwiseAndBits_zero_right (m a : Nat) :
    bitwiseAndBits m a 0 = 0 := by
  induction m generalizing a with
  | zero => rfl
  | succ k ih =>
    unfold bitwiseAndBits
    dsimp only
    have h0 : Nat.mod 0 2 = 0 := rfl
    have hdiv0 : Nat.div 0 2 = 0 := rfl
    rw [h0, hdiv0, ih (Nat.div a 2)]
    cases Nat.beq (Nat.mod a 2) 1 <;> rfl

private theorem mod_two_mul_eq (a p : Nat) (hp : 0 < p) :
    a % (2 * p) = a % 2 + 2 * ((a / 2) % p) := by
  have h1 := Nat.div_add_mod a 2
  have h2 := Nat.div_add_mod (a / 2) p
  have h_decomp : a = (2 * p) * ((a / 2) / p) + (a % 2 + 2 * ((a / 2) % p)) := by
    calc
      a = 2 * (a / 2) + a % 2 := h1.symm
      _ = 2 * (p * ((a / 2) / p) + (a / 2) % p) + a % 2 := congrArg (· + a % 2) (congrArg (2 * ·) h2.symm)
      _ = (2 * p) * ((a / 2) / p) + (a % 2 + 2 * ((a / 2) % p)) := by
        rw [Nat.left_distrib, ← Nat.mul_assoc, Nat.add_assoc, Nat.add_comm (2 * ((a / 2) % p)) (a % 2)]
  have h_rem_lt : a % 2 + 2 * ((a / 2) % p) < 2 * p := by
    have h_lt1 : a % 2 < 2 := Nat.mod_lt a (by decide)
    have h_lt2 : (a / 2) % p < p := Nat.mod_lt (a / 2) hp
    omega
  conv => lhs; rw [h_decomp]
  rw [Nat.mul_comm (2 * p) _, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt h_rem_lt]

theorem bitwiseAndBits_mask_low (j m a : Nat) :
    bitwiseAndBits (j + m) a (2 ^ j - 1) = a % (2 ^ j) := by
  induction j generalizing a with
  | zero =>
    simp only [Nat.zero_add, Nat.pow_zero]
    rw [bitwiseAndBits_zero_right, Nat.mod_one]
  | succ k ih =>
    have h_add : k + 1 + m = (k + m) + 1 := by omega
    rw [h_add]
    unfold bitwiseAndBits
    dsimp only
    have h_pos : 0 < 2 ^ k := Nat.two_pow_pos k
    have h_pow : 2 ^ (k + 1) = 2 * 2 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm]
    have h_mod2 : Nat.mod (2 ^ (k + 1) - 1) 2 = 1 := by
      change (2 ^ (k + 1) - 1) % 2 = 1
      rw [h_pow]; omega
    have h_div2 : Nat.div (2 ^ (k + 1) - 1) 2 = 2 ^ k - 1 := by
      change (2 ^ (k + 1) - 1) / 2 = 2 ^ k - 1
      rw [h_pow]; omega
    have h_div_a : Nat.div a 2 = a / 2 := rfl
    have h_mod_a : Nat.mod a 2 = a % 2 := rfl
    rw [h_mod2, h_div2, h_div_a, h_mod_a, ih (a / 2), h_pow, mod_two_mul_eq a (2 ^ k) h_pos]
    cases h_rem : a % 2 with
    | zero =>
      have hbeq : Nat.beq 0 1 = false := rfl
      simp only [hbeq]
      rfl
    | succ r =>
      have hr0 : r = 0 := by
        have : a % 2 < 2 := Nat.mod_lt a (by decide)
        omega
      subst hr0
      have hbeq : Nat.beq 1 1 = true := rfl
      simp only [hbeq]
      rfl

@[simp]
theorem bitwiseAndBits_16_255 (a : Nat) :
    bitwiseAndBits 16 a 255 = a % 256 :=
  bitwiseAndBits_mask_low 8 8 a

@[simp]
theorem bitwiseAndBits_8_1 (a : Nat) :
    bitwiseAndBits 8 a 1 = a % 2 :=
  bitwiseAndBits_mask_low 1 7 a

@[simp]
theorem bitwiseOrBits_zero_right (m : Nat) {a : Nat} (ha : a < 2 ^ m) :
    bitwiseOrBits m a 0 = a := by
  induction m generalizing a with
  | zero =>
    have : a = 0 := by
      simp only [Nat.pow_zero] at ha
      omega
    subst this
    rfl
  | succ k ih =>
    unfold bitwiseOrBits
    have h_pow : 2 ^ (k + 1) = 2 * 2 ^ k := by
      rw [Nat.pow_succ]; omega
    have ha_div : a / 2 < 2 ^ k := by omega
    have h0 : Nat.mod 0 2 = 0 := rfl
    have hdiv0 : Nat.div 0 2 = 0 := rfl
    have h_div_a : Nat.div a 2 = a / 2 := rfl
    have h_mod_a : Nat.mod a 2 = a % 2 := rfl
    rw [h0, hdiv0, h_div_a, h_mod_a, ih ha_div]
    cases h_rem : a % 2 with
    | zero =>
      have hbeq : Nat.beq 0 1 = false := rfl
      simp only [hbeq]
      change 0 + 2 * (a / 2) = a
      omega
    | succ r =>
      have hr0 : r = 0 := by omega
      subst hr0
      have hbeq : Nat.beq 1 1 = true := rfl
      simp only [hbeq]
      change 1 + 2 * (a / 2) = a
      omega

theorem bitwiseOrBits_shift_add (j m hi lo : Nat)
    (hlo : lo < 2 ^ j) (hhi : hi < 2 ^ m) :
    bitwiseOrBits (j + m) (hi * 2 ^ j) lo = hi * 2 ^ j + lo := by
  induction j generalizing lo with
  | zero =>
    simp only [Nat.zero_add, Nat.pow_zero, Nat.mul_one] at hlo ⊢
    have hlo0 : lo = 0 := by omega
    subst hlo0
    rw [Nat.add_zero]
    exact bitwiseOrBits_zero_right m hhi
  | succ k ih =>
    have h_add : k + 1 + m = (k + m) + 1 := by omega
    rw [h_add]
    unfold bitwiseOrBits
    have h_pow : 2 ^ (k + 1) = 2 * 2 ^ k := by
      rw [Nat.pow_succ]; omega
    have h_mul : hi * 2 ^ (k + 1) = 2 * (hi * 2 ^ k) := by
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (hi * 2 ^ k) 2]
    have h_lhs_mod : Nat.mod (hi * 2 ^ (k + 1)) 2 = 0 := by
      change (hi * 2 ^ (k + 1)) % 2 = 0
      rw [h_mul]; omega
    have h_lhs_div : Nat.div (hi * 2 ^ (k + 1)) 2 = hi * 2 ^ k := by
      change (hi * 2 ^ (k + 1)) / 2 = hi * 2 ^ k
      rw [h_mul]; omega
    have h_lo_div : lo / 2 < 2 ^ k := by omega
    have h_div_lo : Nat.div lo 2 = lo / 2 := rfl
    have h_mod_lo : Nat.mod lo 2 = lo % 2 := rfl
    rw [h_lhs_mod, h_lhs_div, h_div_lo, h_mod_lo, ih (lo / 2) h_lo_div]
    cases h_rem : lo % 2 with
    | zero =>
      have hbeq0 : Nat.beq 0 1 = false := rfl
      simp only [hbeq0]
      change 0 + 2 * (hi * 2 ^ k + lo / 2) = hi * 2 ^ (k + 1) + lo
      rw [h_mul]; omega
    | succ r =>
      have hr0 : r = 0 := by omega
      subst hr0
      have hbeq0 : Nat.beq 0 1 = false := rfl
      have hbeq1 : Nat.beq 1 1 = true := rfl
      simp only [hbeq0, hbeq1]
      change 1 + 2 * (hi * 2 ^ k + lo / 2) = hi * 2 ^ (k + 1) + lo
      rw [h_mul]; omega

@[simp]
theorem bitwiseOrBits_16_mul256_add {hi lo : Nat}
    (hhi : hi < 256) (hlo : lo < 256) :
    bitwiseOrBits 16 (hi * 256) lo = hi * 256 + lo :=
  bitwiseOrBits_shift_add 8 8 hi lo hlo hhi

@[simp]
theorem bitwiseOrBits_32_mul256_add {hi lo : Nat}
    (hhi : hi < 16777216) (hlo : lo < 256) :
    bitwiseOrBits 32 (hi * 256) lo = hi * 256 + lo :=
  bitwiseOrBits_shift_add 8 24 hi lo hlo hhi

@[simp]
theorem scalarPow2_eight : scalarPow2 8 = 256 := rfl



@[simp]
theorem wrapScalarBits_eq_of_lt {val modulus : Nat} (h : val < modulus) :
    wrapScalarBits val modulus = val := by
  unfold wrapScalarBits
  have hble : Nat.ble modulus val = false := by
    cases h_eq : Nat.ble modulus val with
    | false => rfl
    | true => exact absurd (Nat.le_of_ble_eq_true h_eq) (Nat.not_le_of_lt h)
  rw [hble]

end Anneal.Rustc.V2026_06_01.SymbolicEval
