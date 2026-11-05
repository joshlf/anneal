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


/-- Abstract local slot tracking either a concrete `LocalSlot`, a symbolic
input argument `.symArg idx` (`args[idx]`), or a 2-tuple `(v0, args[idx])`
(`.symPair0 v0 idx`). -/
inductive SymSlot : Type where
  | concrete : LocalSlot → SymSlot
  | symArg : Nat → SymSlot
  | symPair0 : Value → Nat → SymSlot

/-- Abstract rvalue/operand value tracking a concrete `Value`, a symbolic
input argument `.symArg idx` (`args[idx]`), a 2-tuple `(v0, args[idx])`
(`.symPair0 v0 idx`), or a concrete value `v0` guarded by `args[idx]` being
in-bounds (`.symGuarded v0 idx`). -/
inductive SymVal : Type where
  | concrete : Value → SymVal
  | symArg : Nat → SymVal
  | symPair0 : Value → Nat → SymVal
  | symGuarded : Value → Nat → SymVal

/-- Concretize a `SymSlot` against concrete argument list `args`. -/
def concretizeSymSlot (args : List Value) : SymSlot → LocalSlot
  | .concrete slot => slot
  | .symArg idx =>
    match get? args idx with
    | .some v => .init v
    | .none => .uninit
  | .symPair0 v0 idx =>
    match get? args idx with
    | .some v1 => .init (.aggregate 0 (v0 :: v1 :: .nil))
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
    | .some (.symPair0 v0 idx) => .some (.symPair0 v0 idx)
    | _ => .none
  | proj :: rest =>
    match get? slots p.local_ with
    | .some (.concrete (.init rootVal)) =>
      match readProjectedPure rootVal (proj :: rest) with
      | .some fieldVal => .some (.concrete fieldVal)
      | .none => .none
    | .some (.symPair0 v0 idx) =>
      match proj, rest with
      | .field .zero _, .nil => .some (.symGuarded v0 idx)
      | .field (.succ .zero) _, .nil => .some (.symArg idx)
      | _, _ => .none
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
  | .symPair0 v0 idx =>
    match get? args idx with
    | .some v1 => .ok (.aggregate 0 (v0 :: v1 :: .nil)) (concretizeSymSlots args slots')
    | .none => .ub
  | .symGuarded v0 idx =>
    match get? args idx with
    | .some _ => .ok v0 (concretizeSymSlots args slots')
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
        | symPair0 v0 idx =>
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
          | symArg _ | symPair0 _ _ => nomatch h
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
                        | symPair0 _ _ => nomatch h
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
                        | symArg idx | symPair0 _ idx =>
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
          | symPair0 v0 idx =>
            dsimp only at h
            cases fIdx with
            | zero =>
              cases pTail with
              | cons _ _ => nomatch h
              | nil =>
                injection h with hEq
                subst hEq
                dsimp only [concretizeSymSlot, concretizeSymReadResult]
                cases get? args idx <;> rfl
            | succ fIdx' =>
              cases fIdx' with
              | zero =>
                cases pTail with
                | cons _ _ => nomatch h
                | nil =>
                  injection h with hEq
                  subst hEq
                  dsimp only [concretizeSymSlot, concretizeSymReadResult]
                  cases get? args idx <;> rfl
              | succ _ => nomatch h
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
          | symArg _ | symPair0 _ _ => nomatch h
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
      | .some (.symPair0 v0 idx) =>
        match set? slots p.local_ (.concrete .uninit) with
        | .some slots' => .some (.symPair0 v0 idx, slots')
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
          | symPair0 v0 idx =>
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
        | symArg _ | symPair0 _ _ | symGuarded _ _ => nomatch h
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

/-- Evaluate concrete arithmetic, bitwise, and comparison scalar binary operations. -/
def evalSymScalarBinOp
    (op : BinOp)
    (lhs rhs : ScalarInt)
    (isSigned : Bool := false) :
    Option Value :=
  match Nat.beq lhs.sizeBytes 0 with
  | true => .none
  | false =>
    let sz := lhs.sizeBytes
    let numBits := Nat.mul sz 8
    let modulus := scalarModulus sz
    let a := lhs.bits
    let b := rhs.bits
    match Nat.beq lhs.sizeBytes rhs.sizeBytes with
    | false => .none
    | true =>
      match op with
      | .add =>
        let sum := Nat.add a b
        .some (.scalar ⟨wrapScalarBits sum modulus, sz⟩)
      | .addWithOverflow =>
        let sum := Nat.add a b
        let wrapped : ScalarInt := ⟨wrapScalarBits sum modulus, sz⟩
        let overflowBit :=
          match isSigned with
          | false => match Nat.ble modulus sum with | true => 1 | false => 0
          | true =>
            match signedOverflowAdd a b sz with | true => 1 | false => 0
        .some (.aggregate 0 (.scalar wrapped :: .scalar ⟨overflowBit, 1⟩ :: .nil))
      | .sub =>
        let valBits :=
          match Nat.ble b a with
          | true => wrapScalarBits (Nat.sub a b) modulus
          | false =>
            wrapScalarBits
              (Nat.sub (Nat.add modulus (wrapScalarBits a modulus))
                (wrapScalarBits b modulus))
              modulus
        .some (.scalar ⟨valBits, sz⟩)
      | .subWithOverflow =>
        match isSigned with
        | false =>
          match Nat.ble b a with
          | true =>
            let diff := wrapScalarBits (Nat.sub a b) modulus
            .some (.aggregate 0 (.scalar ⟨diff, sz⟩ :: .scalar ⟨0, 1⟩ :: .nil))
          | false =>
            let wrappedDiff :=
              wrapScalarBits
                (Nat.sub (Nat.add modulus (wrapScalarBits a modulus))
                  (wrapScalarBits b modulus))
                modulus
            .some (.aggregate 0 (.scalar ⟨wrappedDiff, sz⟩ :: .scalar ⟨1, 1⟩ :: .nil))
        | true =>
          let ca := wrapScalarBits a modulus
          let cb := wrapScalarBits b modulus
          let wrappedDiff :=
            match Nat.ble cb ca with
            | true => wrapScalarBits (Nat.sub ca cb) modulus
            | false => wrapScalarBits (Nat.sub (Nat.add modulus ca) cb) modulus
          let overflowBit :=
            match signedOverflowSub a b sz with | true => 1 | false => 0
          .some (.aggregate 0 (.scalar ⟨wrappedDiff, sz⟩ :: .scalar ⟨overflowBit, 1⟩ :: .nil))
      | .mul =>
        let prod := Nat.mul a b
        .some (.scalar ⟨wrapScalarBits prod modulus, sz⟩)
      | .mulWithOverflow =>
        let prod := Nat.mul a b
        let wrapped : ScalarInt := ⟨wrapScalarBits prod modulus, sz⟩
        let overflowBit :=
          match isSigned with
          | false => match Nat.ble modulus prod with | true => 1 | false => 0
          | true =>
            match signedOverflowMul a b sz with | true => 1 | false => 0
        .some (.aggregate 0 (.scalar wrapped :: .scalar ⟨overflowBit, 1⟩ :: .nil))
      | .bitAnd => .some (.scalar ⟨bitwiseAndBits numBits a b, sz⟩)
      | .bitOr => .some (.scalar ⟨bitwiseOrBits numBits a b, sz⟩)
      | .bitXor => .some (.scalar ⟨bitwiseXorBits numBits a b, sz⟩)
      | .eq => .some (.scalar (boolToScalar (Nat.beq a b)))
      | .ne => .some (.scalar (boolToScalar (Bool.not (Nat.beq a b))))
      | .lt =>
        let cmp :=
          match isSigned with
          | false => Bool.not (Nat.ble b a)
          | true => signedLt a b sz
        .some (.scalar (boolToScalar cmp))
      | .le =>
        let cmp :=
          match isSigned with
          | false => Nat.ble a b
          | true => signedLe a b sz
        .some (.scalar (boolToScalar cmp))
      | .gt =>
        let cmp :=
          match isSigned with
          | false => Bool.not (Nat.ble a b)
          | true => signedLt b a sz
        .some (.scalar (boolToScalar cmp))
      | .ge =>
        let cmp :=
          match isSigned with
          | false => Nat.ble b a
          | true => signedLe b a sz
        .some (.scalar (boolToScalar cmp))
      | _ => .none

theorem evalSymScalarBinOp_sound
    (op : BinOp)
    (lhs rhs : ScalarInt)
    (locals : List LocalSlot)
    (mem : Memory)
    (isSigned : Bool)
    (v : Value)
    (h : evalSymScalarBinOp op lhs rhs isSigned = .some v) :
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
      | add | addWithOverflow | mul | mulWithOverflow
      | bitAnd | bitOr | bitXor | eq | ne | lt | le | gt | ge =>
        injection h with hEq
        subst hEq
        rfl
      | sub =>
        injection h with hEq
        subst hEq
        cases Nat.ble rhs.bits lhs.bits <;> rfl
      | subWithOverflow =>
        cases isSigned with
        | false =>
          cases hBle : Nat.ble rhs.bits lhs.bits with
          | true =>
            rw [hBle] at h
            injection h with hEq
            subst hEq
            rfl
          | false =>
            rw [hBle] at h
            injection h with hEq
            subst hEq
            rfl
        | true =>
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
  | symPair0 v0 idx =>
    dsimp only [concretizeSymSlot]
    cases get? args idx <;> trivial
  | concrete c =>
    cases c with
    | dead => exact False.elim hNotDead
    | uninit => trivial
    | init _ => trivial

def symSlotIsDead : SymSlot → Bool
  | .concrete .dead => true
  | _ => false

theorem symSlot_not_dead_of_match_some
    {α : Type}
    {s : SymSlot}
    {k : Option α}
    {res : α}
    (h :
      (match Option.some s with
       | Option.none => Option.none
       | Option.some (.concrete .dead) => Option.none
       | Option.some _ => k) = Option.some res) :
    symSlotIsDead s = false ∧ k = Option.some res := by
  cases s with
  | symArg _ => exact ⟨rfl, h⟩
  | symPair0 _ _ => exact ⟨rfl, h⟩
  | concrete c =>
    cases c with
    | dead => nomatch h
    | uninit | init _ => exact ⟨rfl, h⟩

theorem concretizeSymSlot_eq_of_not_dead
    (args : List Value)
    (s : SymSlot)
    (hNotDead : symSlotIsDead s = false) :
    concretizeSymSlot args s = .uninit ∨ ∃ v, concretizeSymSlot args s = .init v := by
  cases s with
  | symArg idx =>
    dsimp only [concretizeSymSlot]
    cases get? args idx with
    | none => exact Or.inl rfl
    | some v => exact Or.inr ⟨v, rfl⟩
  | symPair0 v0 idx =>
    dsimp only [concretizeSymSlot]
    cases get? args idx with
    | none => exact Or.inl rfl
    | some v1 => exact Or.inr ⟨.aggregate 0 (v0 :: v1 :: .nil), rfl⟩
  | concrete c =>
    cases c with
    | dead => nomatch hNotDead
    | uninit => exact Or.inl rfl
    | init v => exact Or.inr ⟨v, rfl⟩

/-- Resolve static (non-`.deref`, non-`.index`) borrow projection elements. -/
def resolveSymBorrowProjectionElems :
    List ProjectionElem → Option (List ProjectionElem)
  | .nil => .some .nil
  | .deref :: _ => .none
  | .index _ :: _ => .none
  | elem :: rest =>
    match resolveSymBorrowProjectionElems rest with
    | .some rest' => .some (elem :: rest')
    | .none => .none

theorem resolveSymBorrowProjectionElems_sound
    (locals : List LocalSlot)
    (projs resolved : List ProjectionElem)
    (h : resolveSymBorrowProjectionElems projs = .some resolved) :
    resolveBorrowProjectionElems locals projs = .some resolved := by
  induction projs generalizing resolved with
  | nil =>
    injection h with hEq
    subst hEq
    rfl
  | cons pHead pTail ih =>
    cases pHead with
    | deref | index _ => nomatch h
    | field _ _ | constantIndex _ _ _ | subslice _ _ _ | downcast _ _ | opaqueCast _ | unwrapUnsafeBinder _ =>
      dsimp only [resolveSymBorrowProjectionElems] at h
      dsimp only [resolveBorrowProjectionElems]
      cases hRest : resolveSymBorrowProjectionElems pTail with
      | none =>
        rw [hRest] at h
        nomatch h
      | some rest' =>
        rw [hRest] at h
        injection h with hEq
        subst hEq
        rw [ih rest' hRest]

/-- Symbolic counterpart of `freezeDerefReadBorrowsAt` over `slots : List SymSlot`. -/
def freezeSymDerefReadBorrowsAt
    (slots : List SymSlot)
    (ptrLoc : Local)
    (restProj : List ProjectionElem)
    (borrows : List BorrowEntry) :
    List BorrowEntry :=
  match get? slots ptrLoc with
  | .some (.concrete (.init (.ptr ptrVal _))) =>
    match lookupBorrow borrows ptrVal.tag with
    | .some readerEntry =>
      freezeTreeBorrowsOnReadAtProj
        borrows
        borrows
        readerEntry.targetLocal
        (.some ptrVal.tag)
        (appendProjections readerEntry.targetProjection restProj)
        readerEntry.rangeOffset
        readerEntry.rangeLen
    | .none => borrows
  | _ => borrows

theorem freezeSymDerefReadBorrowsAt_sound
    (args : List Value)
    (slots : List SymSlot)
    (ptrLoc : Local)
    (restProj : List ProjectionElem)
    (borrows : List BorrowEntry)
    (sv : SymVal)
    (h :
      evalSymPlaceCopy
        slots
        { local_ := ptrLoc, projection := .deref :: restProj }
        borrows = .some sv) :
    freezeDerefReadBorrowsAt (concretizeSymSlots args slots) ptrLoc restProj borrows =
      freezeSymDerefReadBorrowsAt slots ptrLoc restProj borrows := by
  dsimp only [evalSymPlaceCopy] at h
  dsimp only [freezeDerefReadBorrowsAt, freezeSymDerefReadBorrowsAt]
  rw [get?_concretizeSymSlots args slots ptrLoc]
  cases hGet : get? slots ptrLoc with
  | none => rfl
  | some sSlot =>
    rw [hGet] at h
    cases sSlot with
    | symArg _ | symPair0 _ _ => nomatch h
    | concrete cSlot =>
      cases cSlot with
      | dead | uninit => nomatch h
      | init v =>
        cases v with
        | unit | scalar _ | aggregate _ _ => nomatch h
        | ptr ptrVal sz => rfl

/-- Update `borrows` after an `Operand` read in `Rvalue.use`. -/
def freezeSymOperandReadBorrows
    (slots : List SymSlot)
    (op : Operand)
    (borrows : List BorrowEntry) :
    List BorrowEntry :=
  match op, borrows with
  | .copy { local_ := ptrLoc, projection := .deref :: restProj },
    b₁ :: b₂ :: restBorrows =>
    freezeSymDerefReadBorrowsAt slots ptrLoc restProj (b₁ :: b₂ :: restBorrows)
  | .move { local_ := ptrLoc, projection := .deref :: restProj },
    b₁ :: b₂ :: restBorrows =>
    freezeSymDerefReadBorrowsAt slots ptrLoc restProj (b₁ :: b₂ :: restBorrows)
  | _, _ => borrows

/-- Update `borrows` after a `Place` read in `Rvalue.copyForDeref`. -/
def freezeSymPlaceReadBorrows
    (slots : List SymSlot)
    (place : Place)
    (borrows : List BorrowEntry) :
    List BorrowEntry :=
  match place.projection, borrows with
  | .deref :: restProj, b₁ :: b₂ :: restBorrows =>
    freezeSymDerefReadBorrowsAt slots place.local_ restProj (b₁ :: b₂ :: restBorrows)
  | _, _ => borrows

/-- Evaluate an `Rvalue` that produces a `SymVal`. -/
def evalSymRvalueConcrete
    (slots : List SymSlot)
    (borrows : List BorrowEntry)
    (nextTag : Nat)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (rv : Rvalue) :
    Option (SymVal × List SymSlot × List BorrowEntry × Nat) :=
  match rv with
  | .use op =>
    match evalSymOperand slots op borrows with
    | .some (sv, slots') =>
      .some (sv, slots', freezeSymOperandReadBorrows slots op borrows, nextTag)
    | .none => .none
  | .copyForDeref place =>
    match evalSymPlaceCopy slots place borrows with
    | .some sv =>
      .some (sv, slots, freezeSymPlaceReadBorrows slots place borrows, nextTag)
    | .none => .none
  | .ref borrowKind place =>
    let perm :=
      match borrowKind with
      | .shared => sharedBorrowPerm localDecls layouts place
      | .mut false => TreeBorrowPerm.active
      | .mut true => TreeBorrowPerm.reserved
    match place.projection with
    | .deref :: _ => .none
    | _ =>
      match get? slots place.local_ with
      | .none => .none
      | .some (.concrete .dead) => .none
      | .some _ =>
        match resolveSymBorrowProjectionElems place.projection with
        | .none => .none
        | .some resolvedProj =>
          let entry : BorrowEntry := {
            tag := nextTag
            targetLocal := place.local_
            targetProjection := resolvedProj
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
        match evalSymScalarBinOp op lhs rhs (operandIsSigned localDecls lhsOp layouts) with
        | .some v => .some (.concrete v, slots₂, borrows, nextTag)
        | .none => .none
      | _ => .none
    | _ => .none
  | .aggregate .tuple ops =>
    match evalSymOperandsConcrete slots ops borrows with
    | .some (vals, slots') => .some (.concrete (.aggregate 0 vals), slots', borrows, nextTag)
    | .none =>
      match ops with
      | op0 :: op1 :: .nil =>
        match evalSymOperand slots op0 borrows with
        | .some (.concrete v0, slots₁) =>
          match evalSymOperand slots₁ op1 borrows with
          | .some (.symArg idx, slots₂) =>
            .some (.symPair0 v0 idx, slots₂, borrows, nextTag)
          | _ => .none
        | _ => .none
      | _ => .none
  | .aggregate (.adt _ variantIdx _) ops =>
    match evalSymOperandsConcrete slots ops borrows with
    | .some (vals, slots') => .some (.concrete (.aggregate variantIdx vals), slots', borrows, nextTag)
    | .none => .none
  | _ => .none

theorem memory_eta (m : Memory) :
    { m with borrows := m.borrows, nextTag := m.nextTag } = m := by
  cases m
  rfl

theorem memory_borrows_eta (m : Memory) (b : List BorrowEntry) :
    ({ m with borrows := b, nextTag := m.nextTag } : Memory) = { m with borrows := b } := by
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
  | .symPair0 v0 idx =>
    match get? args idx with
    | .some v1 => .ok (.aggregate 0 (v0 :: v1 :: .nil)) (concretizeSymSlots args slots') mem'
    | .none => .ub
  | .symGuarded v0 idx =>
    match get? args idx with
    | .some _ => .ok v0 (concretizeSymSlots args slots') mem'
    | .none => .ub

theorem concretizeSymReadResult_to_rvalue
    (args : List Value)
    (sv0 : SymVal)
    (s1 : List SymSlot)
    (mem' : Memory) :
    (match concretizeSymReadResult args sv0 s1 with
     | .ok v locals' => RvalueEvalResult.ok v locals' mem'
     | .ub => RvalueEvalResult.ub
     | .unsupported => RvalueEvalResult.unsupported) =
      concretizeSymRvalueResult args sv0 s1 mem' := by
  cases sv0 with
  | concrete _ => rfl
  | symArg idx | symPair0 _ idx | symGuarded _ idx =>
    dsimp only [concretizeSymReadResult, concretizeSymRvalueResult]
    cases get? args idx <;> rfl

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
    (h : evalSymRvalueConcrete slots mem.borrows mem.nextTag localDecls layouts rv =
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
        rw [memory_borrows_eta mem]
        cases op with
        | constant _ =>
          dsimp only [freezeSymOperandReadBorrows]
          exact concretizeSymReadResult_to_rvalue args sv0 s1 mem
        | copy p =>
          cases p with
          | mk loc proj =>
            cases proj with
            | nil =>
              dsimp only [freezeSymOperandReadBorrows]
              exact concretizeSymReadResult_to_rvalue args sv0 s1 mem
            | cons pHead pTail =>
              cases pHead with
              | deref =>
                dsimp only [evalSymOperand] at hOp
                cases hCopy : evalSymPlaceCopy slots { local_ := loc, projection := .deref :: pTail } mem.borrows with
                | none =>
                  rw [hCopy] at hOp
                  nomatch hOp
                | some sv1 =>
                  rw [hCopy] at hOp
                  injection hOp with hPair
                  injection hPair with hSv hSlots
                  subst hSv
                  cases hBs : mem.borrows with
                  | nil =>
                    dsimp only [freezeSymOperandReadBorrows]
                    rw [← hBs]
                    exact concretizeSymReadResult_to_rvalue args sv1 s1 mem
                  | cons b1 rest1 =>
                    cases rest1 with
                    | nil =>
                      dsimp only [freezeSymOperandReadBorrows]
                      rw [← hBs]
                      exact concretizeSymReadResult_to_rvalue args sv1 s1 mem
                    | cons b2 restBorrows =>
                      rw [hBs] at hCopy
                      dsimp only [freezeSymOperandReadBorrows]
                      rw [← freezeSymDerefReadBorrowsAt_sound args slots loc pTail (b1 :: b2 :: restBorrows) sv1 hCopy]
                      exact concretizeSymReadResult_to_rvalue args sv1 s1
                        { mem with borrows := freezeDerefReadBorrowsAt (concretizeSymSlots args slots) loc pTail (b1 :: b2 :: restBorrows) }
              | field _ _ | index _ | constantIndex _ _ _ | subslice _ _ _ | downcast _ _ | opaqueCast _ | unwrapUnsafeBinder _ =>
                dsimp only [freezeSymOperandReadBorrows]
                exact concretizeSymReadResult_to_rvalue args sv0 s1 mem
        | move p =>
          cases p with
          | mk loc proj =>
            cases proj with
            | nil =>
              dsimp only [freezeSymOperandReadBorrows]
              exact concretizeSymReadResult_to_rvalue args sv0 s1 mem
            | cons pHead pTail =>
              cases pHead with
              | deref =>
                dsimp only [evalSymOperand] at hOp
                cases hCopy : evalSymPlaceCopy slots { local_ := loc, projection := .deref :: pTail } mem.borrows with
                | none =>
                  rw [hCopy] at hOp
                  nomatch hOp
                | some sv1 =>
                  rw [hCopy] at hOp
                  injection hOp with hPair
                  injection hPair with hSv hSlots
                  subst hSv
                  cases hBs : mem.borrows with
                  | nil =>
                    dsimp only [freezeSymOperandReadBorrows]
                    rw [← hBs]
                    exact concretizeSymReadResult_to_rvalue args sv1 s1 mem
                  | cons b1 rest1 =>
                    cases rest1 with
                    | nil =>
                      dsimp only [freezeSymOperandReadBorrows]
                      rw [← hBs]
                      exact concretizeSymReadResult_to_rvalue args sv1 s1 mem
                    | cons b2 restBorrows =>
                      rw [hBs] at hCopy
                      dsimp only [freezeSymOperandReadBorrows]
                      rw [← freezeSymDerefReadBorrowsAt_sound args slots loc pTail (b1 :: b2 :: restBorrows) sv1 hCopy]
                      exact concretizeSymReadResult_to_rvalue args sv1 s1
                        { mem with borrows := freezeDerefReadBorrowsAt (concretizeSymSlots args slots) loc pTail (b1 :: b2 :: restBorrows) }
              | field _ _ | index _ | constantIndex _ _ _ | subslice _ _ _ | downcast _ _ | opaqueCast _ | unwrapUnsafeBinder _ =>
                dsimp only [freezeSymOperandReadBorrows]
                exact concretizeSymReadResult_to_rvalue args sv0 s1 mem
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
      rw [memory_borrows_eta mem]
      cases place with
      | mk loc proj =>
        cases proj with
        | nil =>
          dsimp only [freezeSymPlaceReadBorrows]
          exact concretizeSymReadResult_to_rvalue args sv0 slots mem
        | cons pHead pTail =>
          cases pHead with
          | deref =>
            cases hBs : mem.borrows with
            | nil =>
              dsimp only [freezeSymPlaceReadBorrows]
              rw [← hBs]
              exact concretizeSymReadResult_to_rvalue args sv0 slots mem
            | cons b1 rest1 =>
              cases rest1 with
              | nil =>
                dsimp only [freezeSymPlaceReadBorrows]
                rw [← hBs]
                exact concretizeSymReadResult_to_rvalue args sv0 slots mem
              | cons b2 restBorrows =>
                rw [hBs] at hCopy
                dsimp only [freezeSymPlaceReadBorrows]
                rw [← freezeSymDerefReadBorrowsAt_sound args slots loc pTail (b1 :: b2 :: restBorrows) sv0 hCopy]
                exact concretizeSymReadResult_to_rvalue args sv0 slots
                  { mem with borrows := freezeDerefReadBorrowsAt (concretizeSymSlots args slots) loc pTail (b1 :: b2 :: restBorrows) }
          | field _ _ | index _ | constantIndex _ _ _ | subslice _ _ _ | downcast _ _ | opaqueCast _ | unwrapUnsafeBinder _ =>
            dsimp only [freezeSymPlaceReadBorrows]
            exact concretizeSymReadResult_to_rvalue args sv0 slots mem
  | ref borrowKind place =>
    cases place with
    | mk loc proj =>
      cases proj with
      | nil =>
        dsimp only [evalSymRvalueConcrete, resolveSymBorrowProjectionElems] at h
        dsimp only [evalRvalue, resolveBorrowProjectionElems]
        rw [get?_concretizeSymSlots args slots loc]
        cases hGet : get? slots loc with
        | none =>
          rw [hGet] at h
          nomatch h
        | some sSlot =>
          rw [hGet] at h
          have ⟨hNotDead, hOk⟩ := symSlot_not_dead_of_match_some h
          injection hOk with hTup
          injection hTup with hV hRest1
          injection hRest1 with hS hRest2
          injection hRest2 with hB hT
          subst hV; subst hS; subst hB; subst hT
          dsimp only
          rcases concretizeSymSlot_eq_of_not_dead args sSlot hNotDead with hSlot | ⟨_, hSlot⟩ <;>
            (rw [hSlot]; rfl)
      | cons pHead pTail =>
        cases pHead with
        | deref => nomatch h
        | index _ =>
          dsimp only [evalSymRvalueConcrete, resolveSymBorrowProjectionElems] at h
          cases hGet : get? slots loc with
          | none =>
            rw [hGet] at h
            nomatch h
          | some sSlot =>
            rw [hGet] at h
            have ⟨_, hOk⟩ := symSlot_not_dead_of_match_some h
            nomatch hOk
        | field _ _ | constantIndex _ _ _ | subslice _ _ _ | downcast _ _ | opaqueCast _ | unwrapUnsafeBinder _ =>
          dsimp only [evalSymRvalueConcrete, resolveSymBorrowProjectionElems] at h
          dsimp only [evalRvalue, resolveBorrowProjectionElems]
          rw [get?_concretizeSymSlots args slots loc]
          cases hGet : get? slots loc with
          | none =>
            rw [hGet] at h
            nomatch h
          | some sSlot =>
            rw [hGet] at h
            have ⟨hNotDead, hOk⟩ := symSlot_not_dead_of_match_some h
            cases hRes : resolveSymBorrowProjectionElems pTail with
            | none =>
              rw [hRes] at hOk
              nomatch hOk
            | some rest' =>
              rw [hRes] at hOk
              injection hOk with hTup
              injection hTup with hV hRest1
              injection hRest1 with hS hRest2
              injection hRest2 with hB hT
              subst hV; subst hS; subst hB; subst hT
              rw [resolveSymBorrowProjectionElems_sound (concretizeSymSlots args slots) pTail rest' hRes]
              dsimp only
              rcases concretizeSymSlot_eq_of_not_dead args sSlot hNotDead with hSlot | ⟨_, hSlot⟩ <;>
                (rw [hSlot]; rfl)
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
        | symArg _ | symPair0 _ _ | symGuarded _ _ => nomatch h
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
                | symArg _ | symPair0 _ _ | symGuarded _ _ => nomatch h
                | concrete v2 =>
                  cases v2 with
                  | unit | ptr _ _ | aggregate _ _ => nomatch h
                  | scalar rhs =>
                    dsimp only at h
                    rw [evalSymOperand_sound args slots1 rhsOp mem.borrows mem.globals layouts (.concrete (.scalar rhs)) slots2 hRhs]
                    dsimp only [concretizeSymReadResult]
                    cases hBin : evalSymScalarBinOp op lhs rhs (operandIsSigned localDecls lhsOp layouts) with
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
      | none =>
        rw [hOps] at h
        dsimp only at h
        cases ops with
        | nil => nomatch h
        | cons op0 opsRest1 =>
          cases opsRest1 with
          | nil => nomatch h
          | cons op1 opsRest2 =>
            cases opsRest2 with
            | cons _ _ => nomatch h
            | nil =>
              dsimp only at h
              cases hOp0 : evalSymOperand slots op0 mem.borrows with
              | none =>
                rw [hOp0] at h
                nomatch h
              | some pair0 =>
                rw [hOp0] at h
                cases pair0 with
                | mk sv0 slots1 =>
                  cases sv0 with
                  | symArg _ | symPair0 _ _ | symGuarded _ _ => nomatch h
                  | concrete v0 =>
                    dsimp only at h
                    cases hOp1 : evalSymOperand slots1 op1 mem.borrows with
                    | none =>
                      rw [hOp1] at h
                      nomatch h
                    | some pair1 =>
                      rw [hOp1] at h
                      cases pair1 with
                      | mk sv1 slots2 =>
                        cases sv1 with
                        | concrete _ | symPair0 _ _ | symGuarded _ _ => nomatch h
                        | symArg idx =>
                          injection h with hTup
                          injection hTup with hV hRest1
                          injection hRest1 with hS hRest2
                          injection hRest2 with hB hT
                          subst hV; subst hS; subst hB; subst hT
                          dsimp only [evalOperands]
                          rw [evalSymOperand_sound args slots op0 mem.borrows mem.globals layouts (.concrete v0) slots1 hOp0]
                          dsimp only [concretizeSymReadResult]
                          rw [evalSymOperand_sound args slots1 op1 mem.borrows mem.globals layouts (.symArg idx) slots2 hOp1]
                          dsimp only [concretizeSymReadResult, concretizeSymRvalueResult]
                          rw [memory_eta mem]
                          cases get? args idx <;> rfl
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
    traitImpls := body.traitImpls
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
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
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
      match evalSymRvalueConcrete st.slots st.borrows st.nextTag localDecls layouts rv with
      | .some (sv, slots₁, borrows₁, nextTag₁) =>
        match get? slots₁ dst.local_ with
        | .none => .none
        | .some (.concrete .dead) => .none
        | .some _ =>
          let dstSymSlot : SymSlot :=
            match sv with
            | .concrete val => .concrete (.init val)
            | .symArg idx => .symArg idx
            | .symPair0 v0 idx => .symPair0 v0 idx
            | .symGuarded v0 _ => .concrete (.init v0)
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
  | .assert cond expected target _ =>
    match evalSymOperand st.slots cond st.borrows with
    | .some (sv, slots') =>
      match sv with
      | .concrete v =>
        match v with
        | .scalar sc =>
          match expected with
          | true =>
            match Nat.beq sc.bits 1 with
            | true => .some { st with blockIdx := target, stmtIdx := 0, slots := slots' }
            | false => .none
          | false =>
            match Nat.beq sc.bits 0 with
            | true => .some { st with blockIdx := target, stmtIdx := 0, slots := slots' }
            | false => .none
        | _ => .none
      | _ => .none
    | .none => .none
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
      | .some stmt => symStepStmtConcrete body.localDecls body.layouts st stmt
      | .none =>
        match Nat.beq st.stmtIdx (length bb.statements) with
        | true => symStepTermConcrete st bb.terminator
        | false => .none

theorem symStepStmtConcrete_sound
    (body : CapturedMir)
    (args : List Value)
    (st st' : SymState)
    (stmt : Statement)
    (h : symStepStmtConcrete body.localDecls body.layouts st stmt = .some st') :
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
        have ⟨hNotDead, hOk⟩ := symSlot_not_dead_of_match_some h
        injection hOk with hEq
        subst hEq
        dsimp only
        rcases concretizeSymSlot_eq_of_not_dead args sSlot hNotDead with hSlot | ⟨_, hSlot⟩ <;>
          (rw [hSlot]; exact Or.inl rfl)
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
          cases hRv : evalSymRvalueConcrete st.slots st.borrows st.nextTag body.localDecls body.layouts rv with
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
                    have ⟨hNotDead, hOk⟩ := symSlot_not_dead_of_match_some h
                    cases sv with
                    | concrete val =>
                      dsimp only [concretizeSymRvalueResult] at hOk ⊢
                      rw [get?_concretizeSymSlots args slots1 dstLoc, hGet]
                      cases hSet : set? slots1 dstLoc (.concrete (.init val)) with
                      | none =>
                        rw [hSet] at hOk
                        nomatch hOk
                      | some slots2 =>
                        rw [hSet] at hOk
                        injection hOk with hEq
                        subst hEq
                        rw [set?_concretizeSymSlots_concrete args (.init val) slots1 dstLoc, hSet]
                        dsimp only
                        rcases concretizeSymSlot_eq_of_not_dead args sSlot hNotDead with hSlot | ⟨_, hSlot⟩ <;>
                          (rw [hSlot]; exact Or.inl rfl)
                    | symArg valIdx =>
                      dsimp only at hOk
                      cases hSet : set? slots1 dstLoc (.symArg valIdx) with
                      | none =>
                        rw [hSet] at hOk
                        nomatch hOk
                      | some slots2 =>
                        rw [hSet] at hOk
                        injection hOk with hEq
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
                          rw [hSetSym]
                          dsimp only
                          rcases concretizeSymSlot_eq_of_not_dead args sSlot hNotDead with hSlot | ⟨_, hSlot⟩ <;>
                            (rw [hSlot]; exact Or.inl rfl)
                    | symPair0 v0 valIdx =>
                      dsimp only at hOk
                      cases hSet : set? slots1 dstLoc (.symPair0 v0 valIdx) with
                      | none =>
                        rw [hSet] at hOk
                        nomatch hOk
                      | some slots2 =>
                        rw [hSet] at hOk
                        injection hOk with hEq
                        subst hEq
                        dsimp only [concretizeSymRvalueResult]
                        cases hArgVal : get? args valIdx with
                        | none => exact Or.inr rfl
                        | some val =>
                          dsimp only
                          rw [get?_concretizeSymSlots args slots1 dstLoc, hGet]
                          have hSetSym := set?_concretizeSymSlots args (.symPair0 v0 valIdx) slots1 dstLoc
                          dsimp only [concretizeSymSlot] at hSetSym
                          rw [hArgVal, hSet] at hSetSym
                          rw [hSetSym]
                          dsimp only
                          rcases concretizeSymSlot_eq_of_not_dead args sSlot hNotDead with hSlot | ⟨_, hSlot⟩ <;>
                            (rw [hSlot]; exact Or.inl rfl)
                    | symGuarded v0 valIdx =>
                      dsimp only at hOk
                      cases hSet : set? slots1 dstLoc (.concrete (.init v0)) with
                      | none =>
                        rw [hSet] at hOk
                        nomatch hOk
                      | some slots2 =>
                        rw [hSet] at hOk
                        injection hOk with hEq
                        subst hEq
                        dsimp only [concretizeSymRvalueResult]
                        cases hArgVal : get? args valIdx with
                        | none => exact Or.inr rfl
                        | some _ =>
                          dsimp only
                          rw [get?_concretizeSymSlots args slots1 dstLoc, hGet]
                          rw [set?_concretizeSymSlots_concrete args (.init v0) slots1 dstLoc, hSet]
                          dsimp only
                          rcases concretizeSymSlot_eq_of_not_dead args sSlot hNotDead with hSlot | ⟨_, hSlot⟩ <;>
                            (rw [hSlot]; exact Or.inl rfl)
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
            have ⟨hNotDead, hOk⟩ := symSlot_not_dead_of_match_some h
            cases hSet : set? st.slots loc (.concrete .uninit) with
            | none =>
              rw [hSet] at hOk
              nomatch hOk
            | some slots' =>
              rw [hSet] at hOk
              injection hOk with hEq
              subst hEq
              refine Or.inl ?_
              rw [set?_concretizeSymSlots_concrete args .uninit st.slots loc, hSet]
              dsimp only
              rcases concretizeSymSlot_eq_of_not_dead args sSlot hNotDead with hSlot | ⟨_, hSlot⟩ <;>
                (rw [hSlot]; rfl)
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
          | symArg _ | symPair0 _ _ | symGuarded _ _ => nomatch h
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
    | assert cond expected target unwind =>
      dsimp only [symStepTermConcrete] at h
      dsimp only [evalTerminator, concretizeSymState, concretizeSymMemory]
      cases hOp : evalSymOperand st.slots cond st.borrows with
      | none =>
        rw [hOp] at h
        nomatch h
      | some pair =>
        rw [hOp] at h
        cases pair with
        | mk sv slots' =>
          cases sv with
          | symArg _ | symPair0 _ _ | symGuarded _ _ => nomatch h
          | concrete v =>
            cases v with
            | unit | ptr _ _ | aggregate _ _ => nomatch h
            | scalar sc =>
              cases expected with
              | false =>
                dsimp only at h
                cases hEqBit : Nat.beq sc.bits 0 with
                | false =>
                  rw [hEqBit] at h
                  nomatch h
                | true =>
                  rw [hEqBit] at h
                  injection h with hEq
                  subst hEq
                  refine Or.inl ?_
                  rw [evalSymOperand_sound
                    args st.slots cond st.borrows body.allocations body.layouts
                    (.concrete (.scalar sc)) slots' hOp]
                  dsimp only [concretizeSymReadResult]
                  rw [hEqBit]
              | true =>
                dsimp only at h
                cases hEqBit : Nat.beq sc.bits 1 with
                | false =>
                  rw [hEqBit] at h
                  nomatch h
                | true =>
                  rw [hEqBit] at h
                  injection h with hEq
                  subst hEq
                  refine Or.inl ?_
                  rw [evalSymOperand_sound
                    args st.slots cond st.borrows body.allocations body.layouts
                    (.concrete (.scalar sc)) slots' hOp]
                  dsimp only [concretizeSymReadResult]
                  rw [hEqBit]
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
                | symArg _ | symPair0 _ _ => nomatch h
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
  | .symPair0 v0 i =>
    match Nat.beq i idx with
    | true => .concrete (.init (.aggregate 0 (v0 :: v :: .nil)))
    | false => .symPair0 v0 i
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
    | symPair0 v0 i =>
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
      have ⟨hNotDead, hOk⟩ := symSlot_not_dead_of_match_some hFin
      cases hSetT : set? slots₂ dstLoc (.concrete (.init (.scalar ⟨1, 1⟩))) with
      | none =>
        rw [hSetT] at hOk
        nomatch hOk
      | some slotsTrue =>
        rw [hSetT] at hOk
        cases hSetF : set? slots₂ dstLoc (.concrete (.init (.scalar ⟨0, 1⟩))) with
        | none =>
          rw [hSetF] at hOk
          nomatch hOk
        | some slotsFalse =>
          rw [hSetF] at hOk
          injection hOk with hTup
          injection hTup with hIdx hRest1
          injection hRest1 with hSc hRest2
          injection hRest2 with hStT hStF
          subst hIdx; subst hSc; subst hStT; subst hStF
          dsimp only [evalAssignNilRvalueStep, concretizeSymMemory] at hHold
          rw [get?_concretizeSymSlots args slots₂ dstLoc, hGetDst] at hHold
          dsimp only at hHold
          have hHold2 :
            stepResultHoldBounded fuel body
              (match set? (concretizeSymSlots args slots₂) dstLoc (.init (.scalar (boolToScalar cmp))) with
               | .some locals₂ =>
                 let borrows₂ := invalidateConflictingBorrows st.borrows dstLoc .none
                 .step (advanceStmt (concretizeSymState body args st) locals₂ {
                   nextAllocId := length body.allocations
                   globals := body.allocations
                   traitImpls := body.traitImpls
                   borrows := borrows₂
                   nextTag := st.nextTag
                   callees := .nil
                   callStack := .nil
                   activeCallee := .none
                 })
               | .none => .fail .ub) := by
            rcases concretizeSymSlot_eq_of_not_dead args dstSlot hNotDead with hSlot | ⟨_, hSlot⟩ <;>
              (rw [hSlot] at hHold; exact hHold)
          clear hHold
          have hHold := hHold2
          clear hHold2
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
                            | symPair0 _ _ | symGuarded _ _ => nomatch hExt
                            | symArg idx0 =>
                              cases sv2 with
                              | symArg _ | symPair0 _ _ | symGuarded _ _ => nomatch hExt
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
                                | concrete _ | symPair0 _ _ | symGuarded _ _ => nomatch hExt
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

/-! ### Auto-Extracted Witness Pinning, Bounded Ranges, and Modular Call Reflection -/

/-- Optional boolean predicate holding: `MirBoolPredicateHolds body args` when
`optBody = .some body`, and `True` when `optBody = .none`. -/
def OptMirBoolPredicateHolds
    (optBody : Option CapturedMir)
    (args : List Value) :
    Prop :=
  match optBody with
  | .some body => MirBoolPredicateHolds body args
  | .none => True

/-- Computable bounded boolean checker for `OptMirBoolPredicateHolds`. -/
def checkOptMirBoolBounded
    (fuel : Nat)
    (optBody : Option CapturedMir)
    (args : List Value) :
    Bool :=
  match optBody with
  | .some body => checkMirBoolBounded fuel body args
  | .none => true

theorem optMirBoolPredicateHolds_of_checkBounded
    (fuel : Nat)
    (optBody : Option CapturedMir)
    (args : List Value)
    (h : checkOptMirBoolBounded fuel optBody args = true) :
    OptMirBoolPredicateHolds optBody args := by
  cases optBody with
  | none => exact True.intro
  | some body => exact mirBoolPredicateHolds_of_checkBounded fuel body args h

/-- Optional boolean predicate holding with linked `specCallees`:
`MirBoolPredicateHoldsWithCallees body specCallees args` when
`optBody = .some body`, and `True` when `optBody = .none`. -/
def OptMirBoolPredicateHoldsWithCallees
    (optBody : Option CapturedMir)
    (specCallees : List CapturedMir)
    (args : List Value) :
    Prop :=
  match optBody with
  | .some body => MirBoolPredicateHoldsWithCallees body specCallees args
  | .none => True

/-- Computable bounded boolean checker for `OptMirBoolPredicateHoldsWithCallees`. -/
def checkOptMirBoolWithCalleesBounded
    (fuel : Nat)
    (optBody : Option CapturedMir)
    (specCallees : List CapturedMir)
    (args : List Value) :
    Bool :=
  match optBody with
  | .some body => checkMirBoolWithCalleesBounded fuel body specCallees args
  | .none => true

theorem optMirBoolPredicateHoldsWithCallees_of_checkBounded
    (fuel : Nat)
    (optBody : Option CapturedMir)
    (specCallees : List CapturedMir)
    (args : List Value)
    (h : checkOptMirBoolWithCalleesBounded fuel optBody specCallees args = true) :
    OptMirBoolPredicateHoldsWithCallees optBody specCallees args := by
  cases optBody with
  | none => exact True.intro
  | some body =>
    exact mirBoolPredicateHoldsWithCallees_of_checkBounded
      fuel body specCallees args h

/-- Collect `(idx, sc)` scalar equality pins discovered along the true branch of
`body` within `fuel` symbolic steps from `st`. -/
def collectSymPinsLoop :
    Nat → CapturedMir → SymState → List (Nat × ScalarInt)
  | .zero, _, _ => .nil
  | .succ fuel, body, st =>
    match symStepConcrete body st with
    | .some st' => collectSymPinsLoop fuel body st'
    | .none =>
      match symExtractPinEq body st with
      | .some (idx, sc, stTrue, stFalse) =>
        match checkSymReturnsFalse fuel body stFalse with
        | true => (idx, sc) :: collectSymPinsLoop fuel body stTrue
        | false => .nil
      | .none => .nil

/-- Look up the `ScalarInt` pinned for argument index `idx` in `pins`. -/
def lookupScalarPin (idx : Nat) : List (Nat × ScalarInt) → Option ScalarInt
  | .nil => .none
  | (i, sc) :: rest =>
    match Nat.beq i idx with
    | true => .some sc
    | false => lookupScalarPin idx rest

/-- Build the ordered `List ScalarInt` for arguments `idx .. idx + rem - 1` from `pins`. -/
def buildExpectedScalarsAux
    (pins : List (Nat × ScalarInt)) :
    Nat → Nat → List ScalarInt
  | _, .zero => .nil
  | idx, .succ rem =>
    match lookupScalarPin idx pins with
    | .some sc => sc :: buildExpectedScalarsAux pins (.succ idx) rem
    | .none => .nil

/-- Automatically extract the ordered `List ScalarInt` pinned by `specBody` for
its `0 .. specBody.argCount - 1` parameters within `fuel` steps. -/
def extractMirRequiresPins (fuel : Nat) (specBody : CapturedMir) : List ScalarInt :=
  let pins := collectSymPinsLoop fuel specBody (initSymState specBody)
  buildExpectedScalarsAux pins 0 specBody.argCount

/-- Extract pinned scalars from an optional `requires` companion body. -/
def extractOptMirRequiresPins
    (fuel : Nat)
    (optReqBody : Option CapturedMir) :
    List ScalarInt :=
  match optReqBody with
  | .some reqBody => extractMirRequiresPins fuel reqBody
  | .none => .nil

/-- Closed-term boolean checker verifying that `optReqBody` pins its parameters
to `expectedScalars`. -/
def checkOptMirRequiresPinsScalars
    (fuel : Nat)
    (optReqBody : Option CapturedMir)
    (expectedScalars : List ScalarInt) :
    Bool :=
  match optReqBody with
  | .some reqBody => checkMirRequiresPinsScalars fuel reqBody expectedScalars
  | .none => Nat.beq (length expectedScalars) 0

theorem args_eq_nil_of_length_zero :
    ∀ (args : List Value), length args = 0 → args = .nil
  | .nil, _ => rfl
  | _ :: _, h => nomatch h

theorem checkOptMirRequiresPinsScalars_sound
    (fuel : Nat)
    (optReqBody : Option CapturedMir)
    (expectedScalars : List ScalarInt)
    (args : List Value)
    (h_check :
      checkOptMirRequiresPinsScalars fuel optReqBody expectedScalars = true)
    (h_len : length args = length expectedScalars)
    (h_req : OptMirBoolPredicateHolds optReqBody args) :
    args = mapScalarValues expectedScalars := by
  cases optReqBody with
  | some reqBody =>
    exact
      checkMirRequiresPinsScalars_sound
        fuel reqBody expectedScalars args h_check h_len h_req
  | none =>
    dsimp only [checkOptMirRequiresPinsScalars] at h_check
    have hExp0 : length expectedScalars = 0 := Nat.eq_of_beq_eq_true h_check
    have hArgs0 : length args = 0 := Eq.trans h_len hExp0
    rw [args_eq_nil_of_length_zero args hArgs0]
    cases expectedScalars with
    | nil => rfl
    | cons _ _ => nomatch hExp0

/-- Computable check that `subjectBody` evaluates on `args` with `callees`
within `subjectFuel` steps to a normal return value `retVal` satisfying
`checkOptMirBoolBounded specFuel optEnsBody (args ++ [retVal])`. -/
def checkMirRustPinnedSpecOptWithCallees
    (subjectFuel specFuel : Nat)
    (subjectBody : CapturedMir)
    (callees : List CapturedMir)
    (optEnsBody : Option CapturedMir)
    (args : List Value) :
    Bool :=
  let rec loop (fuel : Nat) (st : MirExecState) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 =>
      match stepMirState subjectBody st with
      | .ret (.normal (retVal, _)) =>
        checkOptMirBoolBounded specFuel optEnsBody (args ++ [retVal])
      | .ret .panic => false
      | .ret .abort => false
      | .tau st' => loop fuel' st'
      | .vis (.inl _) _ => false
      | .vis (.inr (.inl _)) k => loop fuel' (k PUnit.unit)
      | .vis (.inr (.inr _)) _ => false
  loop subjectFuel (.running (initMachineStateWithCallees subjectBody args callees))

/-- Computable check that `subjectBody` evaluates on `args` within `subjectFuel`
steps to a normal return value `retVal` satisfying
`checkOptMirBoolBounded specFuel optEnsBody (args ++ [retVal])`. -/
def checkMirRustPinnedSpecOpt
    (subjectFuel specFuel : Nat)
    (subjectBody : CapturedMir)
    (optEnsBody : Option CapturedMir)
    (args : List Value) :
    Bool :=
  checkMirRustPinnedSpecOptWithCallees
    subjectFuel specFuel subjectBody .nil optEnsBody args

theorem wpMirBounded_normal_of_checkMirRustPinnedSpecOptWithCallees
    (subjectFuel specFuel : Nat)
    (subjectBody : CapturedMir)
    (callees : List CapturedMir)
    (optEnsBody : Option CapturedMir)
    (args : List Value)
    (h_ok :
      checkMirRustPinnedSpecOptWithCallees
        subjectFuel specFuel subjectBody callees optEnsBody args = true) :
    wpMirBounded subjectFuel subjectBody
      (initMachineStateWithCallees subjectBody args callees)
      (fun out =>
        ∃ retVal mem',
          out = .normal (retVal, mem') ∧
          OptMirBoolPredicateHolds optEnsBody (args ++ [retVal])) := by
  unfold checkMirRustPinnedSpecOptWithCallees at h_ok
  unfold wpMirBounded
  suffices ∀ (fuel : Nat) (st : MirExecState),
      checkMirRustPinnedSpecOptWithCallees.loop
        specFuel subjectBody optEnsBody args fuel st = true →
      wpCoalBounded fuel mirDefaultWP (stepMirState subjectBody)
        (fun out _ =>
          ∃ retVal mem',
            out = .normal (retVal, mem') ∧
            OptMirBoolPredicateHolds optEnsBody (args ++ [retVal]))
        st PUnit.unit from
    this subjectFuel _ h_ok
  intro fuel
  induction fuel with
  | zero => intro _ h; nomatch h
  | succ fuel' ih =>
    intro st h
    unfold checkMirRustPinnedSpecOptWithCallees.loop at h
    unfold wpCoalBounded
    cases h_step : stepMirState subjectBody st with
    | ret out =>
      simp only [h_step] at h ⊢
      cases out with
      | normal p =>
        rcases p with ⟨rv, m⟩
        exact ⟨rv, m, rfl,
          optMirBoolPredicateHolds_of_checkBounded
            specFuel optEnsBody (args ++ [rv]) h⟩
      | panic => nomatch h
      | abort => nomatch h
    | tau st' =>
      simp only [h_step] at h ⊢
      exact ih st' h
    | vis i k =>
      simp only [h_step] at h ⊢
      rcases i with f | (e | c)
      · nomatch h
      · cases e
        exact ih (k PUnit.unit) h
      · nomatch h

theorem wpMirBounded_normal_of_checkMirRustPinnedSpecOpt
    (subjectFuel specFuel : Nat)
    (subjectBody : CapturedMir)
    (optEnsBody : Option CapturedMir)
    (args : List Value)
    (h_ok :
      checkMirRustPinnedSpecOpt
        subjectFuel specFuel subjectBody optEnsBody args = true) :
    wpMirBounded subjectFuel subjectBody (initMachineState subjectBody args)
      (fun out =>
        ∃ retVal mem',
          out = .normal (retVal, mem') ∧
          OptMirBoolPredicateHolds optEnsBody (args ++ [retVal])) :=
  wpMirBounded_normal_of_checkMirRustPinnedSpecOptWithCallees
    subjectFuel specFuel subjectBody .nil optEnsBody args h_ok

theorem wpMirBounded_safe_of_checkMirRustPinnedSpecOptWithCallees
    (subjectFuel specFuel : Nat)
    (subjectBody : CapturedMir)
    (callees : List CapturedMir)
    (optEnsBody : Option CapturedMir)
    (args : List Value)
    (h_ok :
      checkMirRustPinnedSpecOptWithCallees
        subjectFuel specFuel subjectBody callees optEnsBody args = true) :
    wpMirBounded subjectFuel subjectBody
      (initMachineStateWithCallees subjectBody args callees)
      (fun out =>
        ∀ retVal mem',
          out = .normal (retVal, mem') →
          OptMirBoolPredicateHolds optEnsBody (args ++ [retVal])) := by
  have h_norm :=
    wpMirBounded_normal_of_checkMirRustPinnedSpecOptWithCallees
      subjectFuel specFuel subjectBody callees optEnsBody args h_ok
  rw [← wpMirSym_eq_wpMirBounded] at h_norm ⊢
  refine wpMirSym_mono ?_ h_norm
  intro out ⟨rv, m, h_out, h_ens⟩ retVal mem' h_eq
  rw [h_out] at h_eq
  injection h_eq with h_pair
  cases h_pair
  exact h_ens

theorem wpMirBounded_safe_of_checkMirRustPinnedSpecOpt
    (subjectFuel specFuel : Nat)
    (subjectBody : CapturedMir)
    (optEnsBody : Option CapturedMir)
    (args : List Value)
    (h_ok :
      checkMirRustPinnedSpecOpt
        subjectFuel specFuel subjectBody optEnsBody args = true) :
    wpMirBounded subjectFuel subjectBody (initMachineState subjectBody args)
      (fun out =>
        ∀ retVal mem',
          out = .normal (retVal, mem') →
          OptMirBoolPredicateHolds optEnsBody (args ++ [retVal])) :=
  wpMirBounded_safe_of_checkMirRustPinnedSpecOptWithCallees
    subjectFuel specFuel subjectBody .nil optEnsBody args h_ok

/-- Closed-term checker that automatically extracts pinned arguments from
`optReqBody` and verifies `subjectBody` (with `callees`) against `optEnsBody`. -/
def checkMirAutoPinnedSpecWithCallees
    (subjectFuel specFuel : Nat)
    (subjectBody : CapturedMir)
    (callees : List CapturedMir)
    (optReqBody optEnsBody : Option CapturedMir) :
    Bool :=
  let expected := extractOptMirRequiresPins specFuel optReqBody
  Bool.and
    (Nat.beq subjectBody.argCount (length expected))
    (Bool.and
      (checkOptMirRequiresPinsScalars specFuel optReqBody expected)
      (checkMirRustPinnedSpecOptWithCallees
        subjectFuel specFuel subjectBody callees optEnsBody (mapScalarValues expected)))

/-- Closed-term checker that automatically extracts pinned arguments from
`optReqBody` and verifies `subjectBody` against `optEnsBody`. -/
def checkMirAutoPinnedSpec
    (subjectFuel specFuel : Nat)
    (subjectBody : CapturedMir)
    (optReqBody optEnsBody : Option CapturedMir) :
    Bool :=
  checkMirAutoPinnedSpecWithCallees
    subjectFuel specFuel subjectBody .nil optReqBody optEnsBody

/-- One-call automatic discharge combinator for stateless `Claim`s with pinned
(or 0-argument) `requires` and optional `ensures` (`:= by rfl`). -/
theorem dischargeRustPinnedContractAuto
    (c : Claim)
    (subjectFuel specFuel : Nat)
    (optReqBody optEnsBody : Option CapturedMir)
    (h_pre :
      ∀ args : List Value,
        c.pre args →
        And
          (Trusted.Sequence.length args = c.body.argCount)
          (OptMirBoolPredicateHolds optReqBody args) := by
      intro _ h
      first
      | exact h
      | exact ⟨h, True.intro⟩)
    (h_check :
      checkMirAutoPinnedSpecWithCallees
        subjectFuel specFuel c.body c.callees optReqBody optEnsBody = true := by rfl)
    (h_post :
      ∀ (args : List Value) (ret : Value),
        OptMirBoolPredicateHolds optEnsBody (args ++ [ret]) →
        c.post args ret := by
      intro _ _ h
      first
      | exact h
      | exact True.intro) :
    VerificationResult c := by
  refine verifyMirBounded c subjectFuel (fun args hp => ?_)
  rcases h_pre args hp with ⟨h_len_body, h_req⟩
  dsimp only [checkMirAutoPinnedSpecWithCallees] at h_check
  let expected := extractOptMirRequiresPins specFuel optReqBody
  cases hArgEq : Nat.beq c.body.argCount (length expected) with
  | false =>
    rw [hArgEq] at h_check
    nomatch h_check
  | true =>
    rw [hArgEq] at h_check
    dsimp only [Bool.and] at h_check
    cases hPins : checkOptMirRequiresPinsScalars specFuel optReqBody expected with
    | false =>
      rw [hPins] at h_check
      nomatch h_check
    | true =>
      rw [hPins] at h_check
      dsimp only [Bool.and] at h_check
      have h_len : length args = length expected :=
        Eq.trans h_len_body (Nat.eq_of_beq_eq_true hArgEq)
      have h_args : args = mapScalarValues expected :=
        checkOptMirRequiresPinsScalars_sound
          specFuel optReqBody expected args hPins h_len h_req
      subst h_args
      have h_wp :=
        wpMirBounded_safe_of_checkMirRustPinnedSpecOptWithCallees
          subjectFuel specFuel c.body c.callees optEnsBody (mapScalarValues expected) h_check
      rw [← wpMirSym_eq_wpMirBounded] at h_wp ⊢
      exact wpMirSym_mono
        (fun out ho retVal mem' h_out =>
          h_post (mapScalarValues expected) retVal (ho retVal mem' h_out))
        h_wp

/-- One-call automatic discharge combinator for `TotalClaim`s (`#[spec(safe_total, ...)]`)
with pinned (or 0-argument) `requires` and optional `ensures` (`:= by rfl`). -/
theorem dischargeRustTotalPinnedContractAuto
    (c : TotalClaim)
    (subjectFuel specFuel : Nat)
    (optReqBody optEnsBody : Option CapturedMir)
    (h_pre :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        And
          (And
            (Trusted.Sequence.length args = c.body.argCount)
            (OptMirBoolPredicateHolds optReqBody args))
          (mem = (initMachineState c.body args).memory) := by
      intro _ _ h
      first
      | exact h
      | exact h.1
      | exact ⟨⟨h.1, True.intro⟩, h.2⟩
      | exact ⟨⟨h.1.1, True.intro⟩, h.1.2⟩
      | exact ⟨⟨h.2.1, True.intro⟩, h.1.2⟩)
    (h_check :
      checkMirAutoPinnedSpecWithCallees
        subjectFuel specFuel c.body c.callees optReqBody optEnsBody = true := by rfl)
    (h_post :
      ∀ (args : List Value) (mem : Memory) (ret : Value) (mem' : Memory),
        OptMirBoolPredicateHolds optEnsBody (args ++ [ret]) →
        c.post args mem ret mem' := by
      intro _ _ _ _ h
      first
      | exact h
      | exact True.intro) :
    TotalVerificationResult c := by
  refine verifyTotalMirBounded c subjectFuel (fun args mem hp => ?_)
  rcases h_pre args mem hp with ⟨⟨h_len_body, h_req⟩, h_mem⟩
  subst h_mem
  dsimp only [checkMirAutoPinnedSpecWithCallees] at h_check
  let expected := extractOptMirRequiresPins specFuel optReqBody
  cases hArgEq : Nat.beq c.body.argCount (length expected) with
  | false =>
    rw [hArgEq] at h_check
    nomatch h_check
  | true =>
    rw [hArgEq] at h_check
    dsimp only [Bool.and] at h_check
    cases hPins : checkOptMirRequiresPinsScalars specFuel optReqBody expected with
    | false =>
      rw [hPins] at h_check
      nomatch h_check
    | true =>
      rw [hPins] at h_check
      dsimp only [Bool.and] at h_check
      have h_len : length args = length expected :=
        Eq.trans h_len_body (Nat.eq_of_beq_eq_true hArgEq)
      have h_args : args = mapScalarValues expected :=
        checkOptMirRequiresPinsScalars_sound
          specFuel optReqBody expected args hPins h_len h_req
      subst h_args
      have h_wp :=
        wpMirBounded_normal_of_checkMirRustPinnedSpecOptWithCallees
          subjectFuel specFuel c.body c.callees optEnsBody (mapScalarValues expected) h_check
      have h_init_eq :
          initMachineStateWithMemoryAndCallees c.body (mapScalarValues expected)
            (initMachineState c.body (mapScalarValues expected)).memory c.callees =
          initMachineStateWithCallees c.body (mapScalarValues expected) c.callees := by
        cases c.callees <;> rfl
      rw [h_init_eq]
      rw [← wpMirSym_eq_wpMirBounded] at h_wp ⊢
      exact wpMirSym_mono
        (fun out ⟨rv, m', h_out, h_ens⟩ =>
          ⟨rv, m', h_out,
            h_post (mapScalarValues expected)
              (initMachineState c.body (mapScalarValues expected)).memory
              rv m' h_ens⟩)
        h_wp

/-- Computable check that `subjectBody` evaluates on `args` with `callees`
within `subjectFuel` steps to a normal return value `retVal` satisfying
`checkOptMirBoolWithCalleesBounded specFuel optEnsBody specCallees (args ++ [retVal])`. -/
def checkMirRustPinnedSpecOptWithSpecCallees
    (subjectFuel specFuel : Nat)
    (subjectBody : CapturedMir)
    (callees specCallees : List CapturedMir)
    (optEnsBody : Option CapturedMir)
    (args : List Value) :
    Bool :=
  let rec loop (fuel : Nat) (st : MirExecState) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 =>
      match stepMirState subjectBody st with
      | .ret (.normal (retVal, _)) =>
        checkOptMirBoolWithCalleesBounded
          specFuel optEnsBody specCallees (args ++ [retVal])
      | .ret .panic => false
      | .ret .abort => false
      | .tau st' => loop fuel' st'
      | .vis (.inl _) _ => false
      | .vis (.inr (.inl _)) k => loop fuel' (k PUnit.unit)
      | .vis (.inr (.inr _)) _ => false
  loop subjectFuel (.running (initMachineStateWithCallees subjectBody args callees))

theorem wpMirBounded_normal_of_checkMirRustPinnedSpecOptWithSpecCallees
    (subjectFuel specFuel : Nat)
    (subjectBody : CapturedMir)
    (callees specCallees : List CapturedMir)
    (optEnsBody : Option CapturedMir)
    (args : List Value)
    (h_ok :
      checkMirRustPinnedSpecOptWithSpecCallees
        subjectFuel specFuel subjectBody callees specCallees optEnsBody args = true) :
    wpMirBounded subjectFuel subjectBody
      (initMachineStateWithCallees subjectBody args callees)
      (fun out =>
        ∃ retVal mem',
          out = .normal (retVal, mem') ∧
          OptMirBoolPredicateHoldsWithCallees
            optEnsBody specCallees (args ++ [retVal])) := by
  unfold checkMirRustPinnedSpecOptWithSpecCallees at h_ok
  unfold wpMirBounded
  suffices ∀ (fuel : Nat) (st : MirExecState),
      checkMirRustPinnedSpecOptWithSpecCallees.loop
        specFuel subjectBody specCallees optEnsBody args fuel st = true →
      wpCoalBounded fuel mirDefaultWP (stepMirState subjectBody)
        (fun out _ =>
          ∃ retVal mem',
            out = .normal (retVal, mem') ∧
            OptMirBoolPredicateHoldsWithCallees
              optEnsBody specCallees (args ++ [retVal]))
        st PUnit.unit from
    this subjectFuel _ h_ok
  intro fuel
  induction fuel with
  | zero => intro _ h; nomatch h
  | succ fuel' ih =>
    intro st h
    unfold checkMirRustPinnedSpecOptWithSpecCallees.loop at h
    unfold wpCoalBounded
    cases h_step : stepMirState subjectBody st with
    | ret out =>
      simp only [h_step] at h ⊢
      cases out with
      | normal p =>
        rcases p with ⟨rv, m⟩
        exact ⟨rv, m, rfl,
          optMirBoolPredicateHoldsWithCallees_of_checkBounded
            specFuel optEnsBody specCallees (args ++ [rv]) h⟩
      | panic => nomatch h
      | abort => nomatch h
    | tau st' =>
      simp only [h_step] at h ⊢
      exact ih st' h
    | vis i k =>
      simp only [h_step] at h ⊢
      rcases i with f | (e | c)
      · nomatch h
      · cases e
        exact ih (k PUnit.unit) h
      · nomatch h

theorem wpMirBounded_safe_of_checkMirRustPinnedSpecOptWithSpecCallees
    (subjectFuel specFuel : Nat)
    (subjectBody : CapturedMir)
    (callees specCallees : List CapturedMir)
    (optEnsBody : Option CapturedMir)
    (args : List Value)
    (h_ok :
      checkMirRustPinnedSpecOptWithSpecCallees
        subjectFuel specFuel subjectBody callees specCallees optEnsBody args = true) :
    wpMirBounded subjectFuel subjectBody
      (initMachineStateWithCallees subjectBody args callees)
      (fun out =>
        ∀ retVal mem',
          out = .normal (retVal, mem') →
          OptMirBoolPredicateHoldsWithCallees
            optEnsBody specCallees (args ++ [retVal])) := by
  have h_norm :=
    wpMirBounded_normal_of_checkMirRustPinnedSpecOptWithSpecCallees
      subjectFuel specFuel subjectBody callees specCallees optEnsBody args h_ok
  rw [← wpMirSym_eq_wpMirBounded] at h_norm ⊢
  refine wpMirSym_mono ?_ h_norm
  intro out ⟨rv, m, h_out, h_ens⟩ retVal mem' h_eq
  rw [h_out] at h_eq
  injection h_eq with h_pair
  cases h_pair
  exact h_ens

/-- Closed-term checker that automatically extracts pinned arguments from
`optReqBody` and verifies `subjectBody` (with `callees`) against `optEnsBody`
(with `specCallees`). -/
def checkMirAutoPinnedSpecWithSpecCallees
    (subjectFuel specFuel : Nat)
    (subjectBody : CapturedMir)
    (callees specCallees : List CapturedMir)
    (optReqBody optEnsBody : Option CapturedMir) :
    Bool :=
  let expected := extractOptMirRequiresPins specFuel optReqBody
  Bool.and
    (Nat.beq subjectBody.argCount (length expected))
    (Bool.and
      (checkOptMirRequiresPinsScalars specFuel optReqBody expected)
      (checkMirRustPinnedSpecOptWithSpecCallees
        subjectFuel specFuel subjectBody callees specCallees optEnsBody
        (mapScalarValues expected)))

/-- One-call automatic discharge combinator for stateless `Claim`s with pinned
`requires` and optional `ensures` calling helpers in `specCallees`. -/
theorem dischargeRustPinnedContractWithSpecCalleesAuto
    (c : Claim)
    (subjectFuel specFuel : Nat)
    (specCallees : List CapturedMir)
    (optReqBody optEnsBody : Option CapturedMir)
    (h_pre :
      ∀ args : List Value,
        c.pre args →
        And
          (Trusted.Sequence.length args = c.body.argCount)
          (OptMirBoolPredicateHolds optReqBody args) := by
      intro _ h
      first
      | exact h
      | exact ⟨h, True.intro⟩)
    (h_check :
      checkMirAutoPinnedSpecWithSpecCallees
        subjectFuel specFuel c.body c.callees specCallees
        optReqBody optEnsBody = true := by rfl)
    (h_post :
      ∀ (args : List Value) (ret : Value),
        OptMirBoolPredicateHoldsWithCallees
          optEnsBody specCallees (args ++ [ret]) →
        c.post args ret := by
      intro _ _ h
      first
      | exact h
      | exact True.intro) :
    VerificationResult c := by
  refine verifyMirBounded c subjectFuel (fun args hp => ?_)
  rcases h_pre args hp with ⟨h_len_body, h_req⟩
  dsimp only [checkMirAutoPinnedSpecWithSpecCallees] at h_check
  let expected := extractOptMirRequiresPins specFuel optReqBody
  cases hArgEq : Nat.beq c.body.argCount (length expected) with
  | false =>
    rw [hArgEq] at h_check
    nomatch h_check
  | true =>
    rw [hArgEq] at h_check
    dsimp only [Bool.and] at h_check
    cases hPins : checkOptMirRequiresPinsScalars specFuel optReqBody expected with
    | false =>
      rw [hPins] at h_check
      nomatch h_check
    | true =>
      rw [hPins] at h_check
      dsimp only [Bool.and] at h_check
      have h_len : length args = length expected :=
        Eq.trans h_len_body (Nat.eq_of_beq_eq_true hArgEq)
      have h_args : args = mapScalarValues expected :=
        checkOptMirRequiresPinsScalars_sound
          specFuel optReqBody expected args hPins h_len h_req
      subst h_args
      have h_wp :=
        wpMirBounded_safe_of_checkMirRustPinnedSpecOptWithSpecCallees
          subjectFuel specFuel c.body c.callees specCallees optEnsBody
          (mapScalarValues expected) h_check
      rw [← wpMirSym_eq_wpMirBounded] at h_wp ⊢
      exact wpMirSym_mono
        (fun out ho retVal mem' h_out =>
          h_post (mapScalarValues expected) retVal (ho retVal mem' h_out))
        h_wp

/-- One-call automatic discharge combinator for `TotalClaim`s
(`#[spec(safe_total, ...)]`) with pinned `requires` and optional `ensures`
calling helpers in `specCallees`. -/
theorem dischargeRustTotalPinnedContractWithSpecCalleesAuto
    (c : TotalClaim)
    (subjectFuel specFuel : Nat)
    (specCallees : List CapturedMir)
    (optReqBody optEnsBody : Option CapturedMir)
    (h_pre :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        And
          (And
            (Trusted.Sequence.length args = c.body.argCount)
            (OptMirBoolPredicateHolds optReqBody args))
          (mem = (initMachineState c.body args).memory) := by
      intro _ _ h
      first
      | exact h
      | exact ⟨⟨h.1, True.intro⟩, h.2⟩
      | exact h.1)
    (h_check :
      checkMirAutoPinnedSpecWithSpecCallees
        subjectFuel specFuel c.body c.callees specCallees
        optReqBody optEnsBody = true := by rfl)
    (h_post :
      ∀ (args : List Value) (mem : Memory) (ret : Value) (mem' : Memory),
        OptMirBoolPredicateHoldsWithCallees
          optEnsBody specCallees (args ++ [ret]) →
        c.post args mem ret mem' := by
      intro _ _ _ _ h
      first
      | exact h
      | exact True.intro) :
    TotalVerificationResult c := by
  refine verifyTotalMirBounded c subjectFuel (fun args mem hp => ?_)
  rcases h_pre args mem hp with ⟨⟨h_len_body, h_req⟩, h_mem⟩
  subst h_mem
  dsimp only [checkMirAutoPinnedSpecWithSpecCallees] at h_check
  let expected := extractOptMirRequiresPins specFuel optReqBody
  cases hArgEq : Nat.beq c.body.argCount (length expected) with
  | false =>
    rw [hArgEq] at h_check
    nomatch h_check
  | true =>
    rw [hArgEq] at h_check
    dsimp only [Bool.and] at h_check
    cases hPins : checkOptMirRequiresPinsScalars specFuel optReqBody expected with
    | false =>
      rw [hPins] at h_check
      nomatch h_check
    | true =>
      rw [hPins] at h_check
      dsimp only [Bool.and] at h_check
      have h_len : length args = length expected :=
        Eq.trans h_len_body (Nat.eq_of_beq_eq_true hArgEq)
      have h_args : args = mapScalarValues expected :=
        checkOptMirRequiresPinsScalars_sound
          specFuel optReqBody expected args hPins h_len h_req
      subst h_args
      have h_wp :=
        wpMirBounded_normal_of_checkMirRustPinnedSpecOptWithSpecCallees
          subjectFuel specFuel c.body c.callees specCallees optEnsBody
          (mapScalarValues expected) h_check
      have h_init_eq :
          initMachineStateWithMemoryAndCallees c.body (mapScalarValues expected)
            (initMachineState c.body (mapScalarValues expected)).memory c.callees =
          initMachineStateWithCallees c.body (mapScalarValues expected) c.callees := by
        cases c.callees <;> rfl
      rw [h_init_eq]
      rw [← wpMirSym_eq_wpMirBounded] at h_wp ⊢
      exact wpMirSym_mono
        (fun out ⟨rv, m', h_out, h_ens⟩ =>
          ⟨rv, m', h_out,
            h_post (mapScalarValues expected)
              (initMachineState c.body (mapScalarValues expected)).memory
              rv m' h_ens⟩)
        h_wp

/-! ### 1-Argument Bounded Unsigned Inequality Reflection (`requires: x < K` / `x <= K`) -/

/-- Check whether `op` is an unsigned upper-bound comparison (`<=`, `<`, or `==`). -/
def isUnsignedUpperBoundOp (op : BinOp) : Bool :=
  match op with
  | .le => true
  | .lt => true
  | .eq => true
  | _ => false

/-- Evaluate the boolean comparison result of `op` (`<=`, `<`, `==`) on unsigned
scalars `a` and `b`. -/
def evalUnsignedUpperBoundCmp (op : BinOp) (a b : Nat) : Bool :=
  match op with
  | .le => Nat.ble a b
  | .lt => Bool.not (Nat.ble b a)
  | _ => Nat.beq a b

theorem evalScalarBinOp_unsignedUpperBound_eq
    (op : BinOp)
    (actualSc sc0 : ScalarInt)
    (locals : List LocalSlot)
    (mem : Memory)
    (hOp : isUnsignedUpperBoundOp op = true)
    (hSz0 : Nat.beq actualSc.sizeBytes 0 = false)
    (hSzEq : Nat.beq actualSc.sizeBytes sc0.sizeBytes = true) :
    evalScalarBinOp op actualSc sc0 locals mem false =
      .ok
        (.scalar (boolToScalar (evalUnsignedUpperBoundCmp op actualSc.bits sc0.bits)))
        locals
        mem := by
  dsimp only [evalScalarBinOp]
  rw [hSz0]
  dsimp only
  cases op with
  | eq | lt | le =>
    rw [hSzEq]
    rfl
  | _ => nomatch hOp

/-- Compute the tight inclusive unsigned upper bound on `lhs` for `op` against `rhs`. -/
@[simp, reducible]
def tightUnsignedUpperBoundBits (op : BinOp) (b : Nat) : Nat :=
  match op with
  | .lt => Nat.pred b
  | _ => b

theorem ble_of_evalUnsignedUpperBoundCmp
    (op : BinOp)
    (a b : Nat)
    (hOp : isUnsignedUpperBoundOp op = true)
    (hCmp : evalUnsignedUpperBoundCmp op a b = true) :
    a ≤ tightUnsignedUpperBoundBits op b := by
  cases op with
  | eq =>
    dsimp only [evalUnsignedUpperBoundCmp, tightUnsignedUpperBoundBits] at hCmp ⊢
    exact Nat.le_of_eq (Nat.eq_of_beq_eq_true hCmp)
  | lt =>
    dsimp only [evalUnsignedUpperBoundCmp, tightUnsignedUpperBoundBits] at hCmp ⊢
    cases b with
    | zero =>
      nomatch hCmp
    | succ k =>
      cases hBle : Nat.ble (.succ k) a with
      | true =>
        rw [hBle] at hCmp
        nomatch hCmp
      | false =>
        exact Nat.le_of_lt_succ ((nat_ble_eq_false_iff (.succ k) a).1 hBle)
  | le =>
    dsimp only [evalUnsignedUpperBoundCmp, tightUnsignedUpperBoundBits] at hCmp ⊢
    exact Nat.le_of_ble_eq_true hCmp
  | _ => nomatch hOp

/-- Extract a 1-argument unsigned upper bound `(boundSc, stFalse)` from `stmt`
when `stmt` compares `.symArg 0` against `.concrete (.scalar boundSc)` via
`<=`, `<`, or `==`. -/
def symExtractUpperBound1Stmt
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (st : SymState)
    (stmt : Statement) :
    Option (ScalarInt × SymState) :=
  match stmt.kind with
  | .assign ⟨dstLoc, .nil⟩ (.binaryOp op lhsOp rhsOp) =>
    match isUnsignedUpperBoundOp op, operandIsSigned localDecls lhsOp layouts with
    | true, false =>
      match evalSymOperand st.slots lhsOp st.borrows with
      | .some (sv₁, slots₁) =>
        match sv₁ with
        | .symArg .zero =>
          match evalSymOperand slots₁ rhsOp st.borrows with
          | .some (sv₂, slots₂) =>
            match sv₂ with
            | .concrete (.scalar sc) =>
              let tightSc : ScalarInt := {
                bits := tightUnsignedUpperBoundBits op sc.bits
                sizeBytes := sc.sizeBytes
              }
              match symFinishPinEq st dstLoc slots₂ 0 tightSc with
              | .some (_, scOut, _, stFalse) => .some (scOut, stFalse)
              | .none => .none
            | _ => .none
          | .none => .none
        | _ => .none
      | .none => .none
    | _, _ => .none
  | _ => .none

/-- Extract a 1-argument unsigned upper bound from the current statement of `body` at `st`. -/
def symExtractUpperBound1
    (body : CapturedMir)
    (st : SymState) :
    Option (ScalarInt × SymState) :=
  match body.phase with
  | .other _ => .none
  | _ =>
    match get? body.basicBlocks st.blockIdx with
    | .none => .none
    | .some bb =>
      match get? bb.statements st.stmtIdx with
      | .some stmt => symExtractUpperBound1Stmt body.localDecls body.layouts st stmt
      | .none => .none

theorem symExtractUpperBound1_sound
    (fuel : Nat)
    (body : CapturedMir)
    (args : List Value)
    (st : SymState)
    (boundSc : ScalarInt)
    (stFalse : SymState)
    (hExt : symExtractUpperBound1 body st = .some (boundSc, stFalse))
    (hFalse : checkSymReturnsFalse fuel body stFalse = true)
    (hHold : evalMirBoolHoldBounded (.succ fuel) body (concretizeSymState body args st)) :
    ∃ b : Nat,
      b ≤ boundSc.bits ∧
      get? args 0 = .some (.scalar { bits := b, sizeBytes := boundSc.sizeBytes }) := by
  dsimp only [symExtractUpperBound1] at hExt
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
        | mk kind span =>
          cases kind with
          | assign dst rv =>
            cases dst with
            | mk dstLoc dstProj =>
              cases dstProj with
              | cons _ _ => nomatch hExt
              | nil =>
                cases rv with
                | binaryOp op lhsOp rhsOp =>
                  dsimp only [symExtractUpperBound1Stmt] at hExt
                  cases hOp : isUnsignedUpperBoundOp op with
                  | false =>
                    rw [hOp] at hExt
                    nomatch hExt
                  | true =>
                    rw [hOp] at hExt
                    cases hSig : operandIsSigned body.localDecls lhsOp body.layouts with
                    | true =>
                      rw [hSig] at hExt
                      nomatch hExt
                    | false =>
                      rw [hSig] at hExt
                      dsimp only at hExt
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
                          cases sv1 with
                          | concrete _ | symPair0 _ _ | symGuarded _ _ => nomatch hExt
                          | symArg idx0 =>
                            cases idx0 with
                            | succ _ => nomatch hExt
                            | zero =>
                              dsimp only at hExt
                              cases hRhs : evalSymOperand slots1 rhsOp st.borrows with
                              | none =>
                                rw [hRhs] at hExt
                                nomatch hExt
                              | some pair2 =>
                                rw [hRhs] at hExt
                                cases pair2 with
                                | mk sv2 slots2 =>
                                  cases sv2 with
                                  | symArg _ | symPair0 _ _ | symGuarded _ _ => nomatch hExt
                                  | concrete v2 =>
                                    cases v2 with
                                    | unit | ptr _ _ | aggregate _ _ => nomatch hExt
                                    | scalar sc0 =>
                                      dsimp only at hExt
                                      let tightSc : ScalarInt := {
                                        bits := tightUnsignedUpperBoundBits op sc0.bits
                                        sizeBytes := sc0.sizeBytes
                                      }
                                      cases hFin : symFinishPinEq st dstLoc slots2 0 tightSc with
                                      | none =>
                                        rw [hFin] at hExt
                                        nomatch hExt
                                      | some tup =>
                                        rw [hFin] at hExt
                                        cases tup with
                                        | mk idxOut rest1 =>
                                          cases rest1 with
                                          | mk scOut rest2 =>
                                            cases rest2 with
                                            | mk stTrue stFalseOut =>
                                              injection hExt with hPair
                                              injection hPair with hScOut hStF
                                              subst hScOut
                                              subst hStF
                                              rw [evalSymOperand_sound
                                                args st.slots lhsOp st.borrows body.allocations body.layouts
                                                (.symArg 0) slots1 hLhs] at hHold
                                              dsimp only [concretizeSymReadResult] at hHold
                                              cases hArg0 : get? args 0 with
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
                                                | unit | aggregate _ _ =>
                                                  exact False.elim hHold
                                                | ptr _ _ =>
                                                  cases op with
                                                  | eq | lt | le => exact False.elim hHold
                                                  | _ => nomatch hOp
                                                | scalar actualSc =>
                                                  dsimp only at hHold
                                                  rw [hSig] at hHold
                                                  cases hActSz0 : Nat.beq actualSc.sizeBytes 0 with
                                                  | true =>
                                                    dsimp only [evalScalarBinOp] at hHold
                                                    rw [hActSz0] at hHold
                                                    exact False.elim hHold
                                                  | false =>
                                                    cases hSzEq : Nat.beq actualSc.sizeBytes sc0.sizeBytes with
                                                    | false =>
                                                      dsimp only [evalScalarBinOp] at hHold
                                                      rw [hActSz0] at hHold
                                                      dsimp only at hHold
                                                      cases op with
                                                      | eq | lt | le =>
                                                        rw [hSzEq] at hHold
                                                        exact False.elim hHold
                                                      | _ => nomatch hOp
                                                    | true =>
                                                      rw [evalScalarBinOp_unsignedUpperBound_eq
                                                        op actualSc sc0
                                                        (concretizeSymSlots args slots2)
                                                        { nextAllocId := length body.allocations
                                                          globals := body.allocations
                                                          traitImpls := body.traitImpls
                                                          borrows := st.borrows
                                                          nextTag := st.nextTag
                                                          callees := .nil
                                                          callStack := .nil
                                                          activeCallee := .none }
                                                        hOp hActSz0 hSzEq] at hHold
                                                      have ⟨_, hScEq, hBranch⟩ :=
                                                        symFinishPinEq_branch_ok_sound
                                                          fuel body args st dstLoc slots2 0 tightSc
                                                          idxOut scOut stTrue stFalseOut
                                                          (evalUnsignedUpperBoundCmp op actualSc.bits sc0.bits)
                                                          hFin hHold
                                                      cases hBranch with
                                                      | inr hFalseHold =>
                                                        exact False.elim
                                                          (checkSymReturnsFalse_sound
                                                            fuel body args stFalseOut hFalse hFalseHold)
                                                      | inl hTruePair =>
                                                        have hBle : actualSc.bits ≤ scOut.bits := by
                                                          rw [hScEq]
                                                          exact ble_of_evalUnsignedUpperBoundCmp
                                                            op actualSc.bits sc0.bits hOp hTruePair.1
                                                        have hSz : actualSc.sizeBytes = scOut.sizeBytes := by
                                                          rw [hScEq]
                                                          exact Nat.eq_of_beq_eq_true hSzEq
                                                        refine ⟨actualSc.bits, hBle, ?_⟩
                                                        cases actualSc with
                                                        | mk bits sz =>
                                                          dsimp only at hSz ⊢
                                                          subst hSz
                                                          rfl
                | _ => nomatch hExt
          | _ => nomatch hExt

/-- Extract the 1-argument unsigned upper bound `boundSc` from `body` within `fuel` steps. -/
def extractMirUpperBound1Loop : Nat → CapturedMir → SymState → Option ScalarInt
  | .zero, _, _ => .none
  | .succ fuel, body, st =>
    match symStepConcrete body st with
    | .some st' => extractMirUpperBound1Loop fuel body st'
    | .none =>
      match symExtractUpperBound1 body st with
      | .some (boundSc, stFalse) =>
        match checkSymReturnsFalse fuel body stFalse with
        | true => .some boundSc
        | false => .none
      | .none => .none

/-- Extract the 1-argument unsigned upper bound `boundSc` from `reqBody`. -/
def extractMirUpperBound1 (fuel : Nat) (reqBody : CapturedMir) : Option ScalarInt :=
  extractMirUpperBound1Loop fuel reqBody (initSymState reqBody)

/-- Check that `body` from `st` establishes `arg0 ≤ boundSc.bits` at width `boundSc.sizeBytes`. -/
def checkSymUpperBound1Loop :
    Nat → CapturedMir → SymState → ScalarInt → Bool
  | .zero, _, _, _ => false
  | .succ fuel, body, st, boundSc =>
    match symStepConcrete body st with
    | .some st' => checkSymUpperBound1Loop fuel body st' boundSc
    | .none =>
      match symExtractUpperBound1 body st with
      | .some (scOut, stFalse) =>
        Bool.and
          (Bool.and
            (Nat.beq scOut.bits boundSc.bits)
            (Nat.beq scOut.sizeBytes boundSc.sizeBytes))
          (checkSymReturnsFalse fuel body stFalse)
      | .none => false

theorem checkSymUpperBound1Loop_sound :
    ∀ (fuel : Nat)
      (body : CapturedMir)
      (args : List Value)
      (st : SymState)
      (boundSc : ScalarInt),
      checkSymUpperBound1Loop fuel body st boundSc = true →
      evalMirBoolHoldBounded fuel body (concretizeSymState body args st) →
      ∃ b : Nat,
        b ≤ boundSc.bits ∧
        get? args 0 = .some (.scalar { bits := b, sizeBytes := boundSc.sizeBytes })
  | .zero, _, _, _, _, hCheck, _ => nomatch hCheck
  | .succ fuel, body, args, st, boundSc, hCheck, hHold => by
    dsimp only [checkSymUpperBound1Loop] at hCheck
    cases hStep : symStepConcrete body st with
    | some st' =>
      rw [hStep] at hCheck
      exact checkSymUpperBound1Loop_sound
        fuel body args st' boundSc hCheck
        (symStepConcrete_sound fuel body args st st' hStep hHold)
    | none =>
      rw [hStep] at hCheck
      cases hExt : symExtractUpperBound1 body st with
      | none =>
        rw [hExt] at hCheck
        nomatch hCheck
      | some pair =>
        rw [hExt] at hCheck
        cases pair with
        | mk scOut stFalse =>
          dsimp only at hCheck
          cases hBitsEq : Nat.beq scOut.bits boundSc.bits with
          | false =>
            rw [hBitsEq] at hCheck
            nomatch hCheck
          | true =>
            rw [hBitsEq] at hCheck
            cases hSzEq : Nat.beq scOut.sizeBytes boundSc.sizeBytes with
            | false =>
              rw [hSzEq] at hCheck
              nomatch hCheck
            | true =>
              rw [hSzEq] at hCheck
              dsimp only [Bool.and] at hCheck
              have hScEq : scOut = boundSc :=
                scalarInt_eq_of_parts
                  (Nat.eq_of_beq_eq_true hBitsEq)
                  (Nat.eq_of_beq_eq_true hSzEq)
              subst hScEq
              exact symExtractUpperBound1_sound
                fuel body args st scOut stFalse hExt hCheck hHold

theorem args_eq_singleton_of_get?_zero :
    ∀ (args : List Value) (v : Value),
      length args = 1 →
      get? args 0 = .some v →
      args = [v]
  | .nil, _, hLen, _ => nomatch hLen
  | _ :: .nil, _, _, hGet => by
    injection hGet with hEq
    subst hEq
    rfl
  | _ :: _ :: _, _, hLen, _ => nomatch hLen

/-- Check that `reqBody` is a 1-argument predicate establishing `arg0 ≤ boundSc.bits`. -/
def checkMirUpperBound1
    (fuel : Nat)
    (reqBody : CapturedMir)
    (boundSc : ScalarInt) :
    Bool :=
  Bool.and
    (Nat.beq reqBody.argCount 1)
    (checkSymUpperBound1Loop fuel reqBody (initSymState reqBody) boundSc)

theorem checkMirUpperBound1_sound
    (fuel : Nat)
    (reqBody : CapturedMir)
    (boundSc : ScalarInt)
    (args : List Value)
    (h_check : checkMirUpperBound1 fuel reqBody boundSc = true)
    (h_len : length args = 1)
    (h_req : MirBoolPredicateHolds reqBody args) :
    ∃ b : Nat,
      b ≤ boundSc.bits ∧
      args = [.scalar { bits := b, sizeBytes := boundSc.sizeBytes }] := by
  dsimp only [checkMirUpperBound1] at h_check
  cases hArg1 : Nat.beq reqBody.argCount 1 with
  | false =>
    rw [hArg1] at h_check
    nomatch h_check
  | true =>
    rw [hArg1] at h_check
    dsimp only [Bool.and] at h_check
    have hHold : evalMirBoolHoldBounded fuel reqBody (initMachineState reqBody args) :=
      wpBoolOrExhausted_of_mirBoolPredicateHolds fuel reqBody args h_req
    have hLenSpec : length args = reqBody.argCount :=
      Eq.trans h_len (Eq.symm (Nat.eq_of_beq_eq_true hArg1))
    rw [← concretizeSymState_initSymState reqBody args hLenSpec] at hHold
    rcases checkSymUpperBound1Loop_sound
      fuel reqBody args (initSymState reqBody) boundSc h_check hHold with ⟨b, hBle, hGet0⟩
    exact ⟨b, hBle, args_eq_singleton_of_get?_zero args _ h_len hGet0⟩

/-- Computable bounded checker that `body` returns `false` (`.scalar ⟨0, 1⟩`)
within `fuel` steps on concrete state `st`. -/
def checkMirReturnsFalseExecBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    match stepMirState body st with
    | .ret (.normal (.scalar { bits := 0, sizeBytes := 1 }, _)) => true
    | .ret _ => false
    | .tau st' => checkMirReturnsFalseExecBounded fuel' body st'
    | .vis (.inl _) _ => false
    | .vis (.inr (.inl _)) k => checkMirReturnsFalseExecBounded fuel' body (k PUnit.unit)
    | .vis (.inr (.inr _)) _ => false

/-- Computable bounded checker that `specBody` returns `false` on `args`. -/
def checkMirReturnsFalseBounded
    (fuel : Nat) (specBody : CapturedMir) (args : List Value) : Bool :=
  checkMirReturnsFalseExecBounded fuel specBody (.running (initMachineState specBody args))

private theorem not_dwlp_of_checkMirReturnsFalseExecBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (h_false : checkMirReturnsFalseExecBounded fuel body st = true)
    (h_dwlp :
      DWLP mirDefaultWP (ITree.cofix (stepMirState body) st)
        (fun out _ =>
          ∀ retVal mem',
            out = .normal (retVal, mem') →
            retVal = .scalar { bits := 1, sizeBytes := 1 })
        PUnit.unit) :
    False := by
  induction fuel generalizing st with
  | zero => nomatch h_false
  | succ fuel' ih =>
    unfold checkMirReturnsFalseExecBounded at h_false
    rw [DWLP.unfold_eq, ITree.observe_cofix] at h_dwlp
    cases h_step : stepMirState body st with
    | ret out =>
      rw [h_step] at h_false h_dwlp
      dsimp only [ITreeF.map] at h_dwlp
      cases out with
      | normal p =>
        rcases p with ⟨retVal, mem'⟩
        cases retVal with
        | scalar sc =>
          rcases sc with ⟨bits, sz⟩
          cases bits with
          | zero =>
            cases sz with
            | zero => nomatch h_false
            | succ s' =>
              cases s' with
              | zero =>
                have h_eq := h_dwlp (.scalar { bits := 0, sizeBytes := 1 }) mem' rfl
                injection h_eq with h_sc
                injection h_sc with h_bits _
                nomatch h_bits
              | succ _ => nomatch h_false
          | succ _ => nomatch h_false
        | _ => nomatch h_false
      | panic => nomatch h_false
      | abort => nomatch h_false
    | tau st' =>
      rw [h_step] at h_false h_dwlp
      dsimp only [ITreeF.map] at h_dwlp
      exact ih st' h_false h_dwlp
    | vis i k =>
      rw [h_step] at h_false h_dwlp
      dsimp only [ITreeF.map] at h_dwlp
      rcases i with f | (e | c)
      · nomatch h_false
      · cases e
        exact ih (k PUnit.unit) h_false h_dwlp
      · nomatch h_false

theorem not_mirBoolPredicateHolds_of_checkReturnsFalseBounded
    (fuel : Nat) (specBody : CapturedMir) (args : List Value)
    (h_false : checkMirReturnsFalseBounded fuel specBody args = true)
    (h_req : MirBoolPredicateHolds specBody args) :
    False :=
  not_dwlp_of_checkMirReturnsFalseExecBounded
    fuel specBody (.running (initMachineState specBody args))
    h_false
    ((mirBoolPredicateHolds_iff_dwlp specBody args).1 h_req)

/-- Check that for every `b ≤ maxBits`, either `reqBody` returns `false` on
`[.scalar ⟨b, sz⟩]` or `checkFn [.scalar ⟨b, sz⟩]` holds. -/
def checkAllScalarRange1
    (specFuel : Nat)
    (reqBody : CapturedMir)
    (checkFn : List Value → Bool)
    (sz : Nat) :
    Nat → Bool
  | .zero =>
    let args0 : List Value := [.scalar { bits := 0, sizeBytes := sz }]
    Bool.or
      (checkMirReturnsFalseBounded specFuel reqBody args0)
      (checkFn args0)
  | .succ k =>
    let argsK : List Value := [.scalar { bits := .succ k, sizeBytes := sz }]
    Bool.and
      (Bool.or
        (checkMirReturnsFalseBounded specFuel reqBody argsK)
        (checkFn argsK))
      (checkAllScalarRange1 specFuel reqBody checkFn sz k)

theorem checkAllScalarRange1_at_sound
    (specFuel : Nat)
    (reqBody : CapturedMir)
    (checkFn : List Value → Bool)
    (sz : Nat) :
    ∀ (maxBits b : Nat),
      b ≤ maxBits →
      checkAllScalarRange1 specFuel reqBody checkFn sz maxBits = true →
      MirBoolPredicateHolds reqBody [.scalar { bits := b, sizeBytes := sz }] →
      checkFn [.scalar { bits := b, sizeBytes := sz }] = true
  | .zero, b, hLe, hAll, hReq => by
    have hb0 : b = 0 := Nat.eq_zero_of_le_zero hLe
    subst hb0
    dsimp only [checkAllScalarRange1] at hAll
    cases hFalse : checkMirReturnsFalseBounded specFuel reqBody [.scalar { bits := 0, sizeBytes := sz }] with
    | true =>
      exact False.elim
        (not_mirBoolPredicateHolds_of_checkReturnsFalseBounded specFuel reqBody _ hFalse hReq)
    | false =>
      rw [hFalse] at hAll
      exact hAll
  | .succ k, b, hLe, hAll, hReq => by
    dsimp only [checkAllScalarRange1] at hAll
    cases hHead :
      Bool.or
        (checkMirReturnsFalseBounded specFuel reqBody [.scalar { bits := .succ k, sizeBytes := sz }])
        (checkFn [.scalar { bits := .succ k, sizeBytes := sz }]) with
    | false =>
      rw [hHead] at hAll
      nomatch hAll
    | true =>
      rw [hHead] at hAll
      dsimp only [Bool.and] at hAll
      cases Nat.eq_or_lt_of_le hLe with
      | inl hEq =>
        subst hEq
        cases hFalse :
          checkMirReturnsFalseBounded specFuel reqBody [.scalar { bits := .succ k, sizeBytes := sz }] with
        | true =>
          exact False.elim
            (not_mirBoolPredicateHolds_of_checkReturnsFalseBounded specFuel reqBody _ hFalse hReq)
        | false =>
          rw [hFalse] at hHead
          exact hHead
      | inr hLt =>
        exact checkAllScalarRange1_at_sound
          specFuel reqBody checkFn sz k b (Nat.le_of_lt_succ hLt) hAll hReq

/-- Closed-term checker that automatically extracts an upper bound `b ≤ K` from
`reqBody` and verifies `subjectBody` (with `callees`) against `optEnsBody` for
all `0 ≤ b ≤ K`. -/
def checkMirAutoBoundedRange1SpecWithCallees
    (subjectFuel specFuel : Nat)
    (subjectBody : CapturedMir)
    (callees : List CapturedMir)
    (reqBody : CapturedMir)
    (optEnsBody : Option CapturedMir) :
    Bool :=
  match extractMirUpperBound1 specFuel reqBody with
  | .none => false
  | .some boundSc =>
    Bool.and
      (Nat.beq subjectBody.argCount 1)
      (Bool.and
        (checkMirUpperBound1 specFuel reqBody boundSc)
        (checkAllScalarRange1
          specFuel
          reqBody
          (checkMirRustPinnedSpecOptWithCallees
            subjectFuel specFuel subjectBody callees optEnsBody)
          boundSc.sizeBytes
          boundSc.bits))

/-- Closed-term checker that automatically extracts an upper bound `b ≤ K` from
`reqBody` and verifies `subjectBody` against `optEnsBody` for all `0 ≤ b ≤ K`. -/
def checkMirAutoBoundedRange1Spec
    (subjectFuel specFuel : Nat)
    (subjectBody reqBody : CapturedMir)
    (optEnsBody : Option CapturedMir) :
    Bool :=
  checkMirAutoBoundedRange1SpecWithCallees
    subjectFuel specFuel subjectBody .nil reqBody optEnsBody

/-- One-call automatic discharge combinator for 1-argument unsigned `Claim`s
with a bounded inequality precondition (`requires: x < K` or `x <= K`). -/
theorem dischargeRustBoundedRange1Auto
    (c : Claim)
    (subjectFuel specFuel : Nat)
    (reqBody : CapturedMir)
    (optEnsBody : Option CapturedMir)
    (h_pre :
      ∀ args : List Value,
        c.pre args →
        And
          (Trusted.Sequence.length args = c.body.argCount)
          (MirBoolPredicateHolds reqBody args) := by
      intro _ h; exact h)
    (h_check :
      checkMirAutoBoundedRange1SpecWithCallees
        subjectFuel specFuel c.body c.callees reqBody optEnsBody = true := by rfl)
    (h_post :
      ∀ (args : List Value) (ret : Value),
        OptMirBoolPredicateHolds optEnsBody (args ++ [ret]) →
        c.post args ret := by
      intro _ _ h
      first
      | exact h
      | exact True.intro) :
    VerificationResult c := by
  refine verifyMirBounded c subjectFuel (fun args hp => ?_)
  rcases h_pre args hp with ⟨h_len_body, h_req⟩
  dsimp only [checkMirAutoBoundedRange1SpecWithCallees] at h_check
  cases hExt : extractMirUpperBound1 specFuel reqBody with
  | none =>
    rw [hExt] at h_check
    nomatch h_check
  | some boundSc =>
    rw [hExt] at h_check
    dsimp only at h_check
    cases hArg1 : Nat.beq c.body.argCount 1 with
    | false =>
      rw [hArg1] at h_check
      nomatch h_check
    | true =>
      rw [hArg1] at h_check
      dsimp only [Bool.and] at h_check
      cases hUb : checkMirUpperBound1 specFuel reqBody boundSc with
      | false =>
        rw [hUb] at h_check
        nomatch h_check
      | true =>
        rw [hUb] at h_check
        dsimp only [Bool.and] at h_check
        have h_len1 : length args = 1 :=
          Eq.trans h_len_body (Nat.eq_of_beq_eq_true hArg1)
        rcases checkMirUpperBound1_sound
          specFuel reqBody boundSc args hUb h_len1 h_req with ⟨b, hBle, hArgs⟩
        subst hArgs
        have hRun :=
          checkAllScalarRange1_at_sound
            specFuel reqBody
            (checkMirRustPinnedSpecOptWithCallees
              subjectFuel specFuel c.body c.callees optEnsBody)
            boundSc.sizeBytes boundSc.bits b hBle h_check h_req
        have h_wp :=
          wpMirBounded_safe_of_checkMirRustPinnedSpecOptWithCallees
            subjectFuel specFuel c.body c.callees optEnsBody
            [.scalar { bits := b, sizeBytes := boundSc.sizeBytes }]
            hRun
        rw [← wpMirSym_eq_wpMirBounded] at h_wp ⊢
        exact wpMirSym_mono
          (fun out ho retVal mem' h_out =>
            h_post [.scalar { bits := b, sizeBytes := boundSc.sizeBytes }] retVal
              (ho retVal mem' h_out))
          h_wp

/-- One-call automatic discharge combinator for 1-argument unsigned `TotalClaim`s
(`#[spec(safe_total, ...)]`) with a bounded inequality precondition (`requires: x < K` or `x <= K`). -/
theorem dischargeRustTotalBoundedRange1Auto
    (c : TotalClaim)
    (subjectFuel specFuel : Nat)
    (reqBody : CapturedMir)
    (optEnsBody : Option CapturedMir)
    (h_pre :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        And
          (And
            (Trusted.Sequence.length args = c.body.argCount)
            (MirBoolPredicateHolds reqBody args))
          (mem = (initMachineState c.body args).memory) := by
      intro _ _ h
      first
      | exact h
      | exact h.1)
    (h_check :
      checkMirAutoBoundedRange1SpecWithCallees
        subjectFuel specFuel c.body c.callees reqBody optEnsBody = true := by rfl)
    (h_post :
      ∀ (args : List Value) (mem : Memory) (ret : Value) (mem' : Memory),
        OptMirBoolPredicateHolds optEnsBody (args ++ [ret]) →
        c.post args mem ret mem' := by
      intro _ _ _ _ h
      first
      | exact h
      | exact True.intro) :
    TotalVerificationResult c := by
  refine verifyTotalMirBounded c subjectFuel (fun args mem hp => ?_)
  rcases h_pre args mem hp with ⟨⟨h_len_body, h_req⟩, h_mem⟩
  subst h_mem
  dsimp only [checkMirAutoBoundedRange1SpecWithCallees] at h_check
  cases hExt : extractMirUpperBound1 specFuel reqBody with
  | none =>
    rw [hExt] at h_check
    nomatch h_check
  | some boundSc =>
    rw [hExt] at h_check
    dsimp only at h_check
    cases hArg1 : Nat.beq c.body.argCount 1 with
    | false =>
      rw [hArg1] at h_check
      nomatch h_check
    | true =>
      rw [hArg1] at h_check
      dsimp only [Bool.and] at h_check
      cases hUb : checkMirUpperBound1 specFuel reqBody boundSc with
      | false =>
        rw [hUb] at h_check
        nomatch h_check
      | true =>
        rw [hUb] at h_check
        dsimp only [Bool.and] at h_check
        have h_len1 : length args = 1 :=
          Eq.trans h_len_body (Nat.eq_of_beq_eq_true hArg1)
        rcases checkMirUpperBound1_sound
          specFuel reqBody boundSc args hUb h_len1 h_req with ⟨b, hBle, hArgs⟩
        subst hArgs
        have hRun :=
          checkAllScalarRange1_at_sound
            specFuel reqBody
            (checkMirRustPinnedSpecOptWithCallees
              subjectFuel specFuel c.body c.callees optEnsBody)
            boundSc.sizeBytes boundSc.bits b hBle h_check h_req
        have h_wp :=
          wpMirBounded_normal_of_checkMirRustPinnedSpecOptWithCallees
            subjectFuel specFuel c.body c.callees optEnsBody
            [.scalar { bits := b, sizeBytes := boundSc.sizeBytes }]
            hRun
        let argsB : List Value := [.scalar { bits := b, sizeBytes := boundSc.sizeBytes }]
        have h_init_eq :
            initMachineStateWithMemoryAndCallees c.body argsB
              (initMachineState c.body argsB).memory c.callees =
            initMachineStateWithCallees c.body argsB c.callees := by
          cases c.callees <;> rfl
        rw [h_init_eq]
        rw [← wpMirSym_eq_wpMirBounded] at h_wp ⊢
        exact wpMirSym_mono
          (fun out ⟨rv, m', h_out, h_ens⟩ =>
            ⟨rv, m', h_out,
              h_post argsB (initMachineState c.body argsB).memory rv m' h_ens⟩)
          h_wp

/-- Closed-term checker that automatically extracts an upper bound `b ≤ K` from
`reqBody` and verifies `subjectBody` (with `callees`) against `optEnsBody`
(with `specCallees`) for all `0 ≤ b ≤ K`. -/
def checkMirAutoBoundedRange1SpecWithSpecCallees
    (subjectFuel specFuel : Nat)
    (subjectBody : CapturedMir)
    (callees specCallees : List CapturedMir)
    (reqBody : CapturedMir)
    (optEnsBody : Option CapturedMir) :
    Bool :=
  match extractMirUpperBound1 specFuel reqBody with
  | .none => false
  | .some boundSc =>
    Bool.and
      (Nat.beq subjectBody.argCount 1)
      (Bool.and
        (checkMirUpperBound1 specFuel reqBody boundSc)
        (checkAllScalarRange1
          specFuel
          reqBody
          (checkMirRustPinnedSpecOptWithSpecCallees
            subjectFuel specFuel subjectBody callees specCallees optEnsBody)
          boundSc.sizeBytes
          boundSc.bits))

/-- One-call automatic discharge combinator for 1-argument unsigned `Claim`s
with a bounded inequality precondition (`requires: x < K` or `x <= K`) and an
optional `ensures` calling helpers in `specCallees`. -/
theorem dischargeRustBoundedRange1WithSpecCalleesAuto
    (c : Claim)
    (subjectFuel specFuel : Nat)
    (specCallees : List CapturedMir)
    (reqBody : CapturedMir)
    (optEnsBody : Option CapturedMir)
    (h_pre :
      ∀ args : List Value,
        c.pre args →
        And
          (Trusted.Sequence.length args = c.body.argCount)
          (MirBoolPredicateHolds reqBody args) := by
      intro _ h; exact h)
    (h_check :
      checkMirAutoBoundedRange1SpecWithSpecCallees
        subjectFuel specFuel c.body c.callees specCallees reqBody optEnsBody = true := by rfl)
    (h_post :
      ∀ (args : List Value) (ret : Value),
        OptMirBoolPredicateHoldsWithCallees
          optEnsBody specCallees (args ++ [ret]) →
        c.post args ret := by
      intro _ _ h
      first
      | exact h
      | exact True.intro) :
    VerificationResult c := by
  refine verifyMirBounded c subjectFuel (fun args hp => ?_)
  rcases h_pre args hp with ⟨h_len_body, h_req⟩
  dsimp only [checkMirAutoBoundedRange1SpecWithSpecCallees] at h_check
  cases hExt : extractMirUpperBound1 specFuel reqBody with
  | none =>
    rw [hExt] at h_check
    nomatch h_check
  | some boundSc =>
    rw [hExt] at h_check
    dsimp only at h_check
    cases hArg1 : Nat.beq c.body.argCount 1 with
    | false =>
      rw [hArg1] at h_check
      nomatch h_check
    | true =>
      rw [hArg1] at h_check
      dsimp only [Bool.and] at h_check
      cases hUb : checkMirUpperBound1 specFuel reqBody boundSc with
      | false =>
        rw [hUb] at h_check
        nomatch h_check
      | true =>
        rw [hUb] at h_check
        dsimp only [Bool.and] at h_check
        have h_len1 : length args = 1 :=
          Eq.trans h_len_body (Nat.eq_of_beq_eq_true hArg1)
        rcases checkMirUpperBound1_sound
          specFuel reqBody boundSc args hUb h_len1 h_req with ⟨b, hBle, hArgs⟩
        subst hArgs
        have hRun :=
          checkAllScalarRange1_at_sound
            specFuel reqBody
            (checkMirRustPinnedSpecOptWithSpecCallees
              subjectFuel specFuel c.body c.callees specCallees optEnsBody)
            boundSc.sizeBytes boundSc.bits b hBle h_check h_req
        have h_wp :=
          wpMirBounded_safe_of_checkMirRustPinnedSpecOptWithSpecCallees
            subjectFuel specFuel c.body c.callees specCallees optEnsBody
            [.scalar { bits := b, sizeBytes := boundSc.sizeBytes }]
            hRun
        rw [← wpMirSym_eq_wpMirBounded] at h_wp ⊢
        exact wpMirSym_mono
          (fun out ho retVal mem' h_out =>
            h_post [.scalar { bits := b, sizeBytes := boundSc.sizeBytes }] retVal
              (ho retVal mem' h_out))
          h_wp

/-- One-call automatic discharge combinator for 1-argument unsigned `TotalClaim`s
(`#[spec(safe_total, ...)]`) with a bounded inequality precondition
(`requires: x < K` or `x <= K`) and an optional `ensures` calling helpers in
`specCallees`. -/
theorem dischargeRustTotalBoundedRange1WithSpecCalleesAuto
    (c : TotalClaim)
    (subjectFuel specFuel : Nat)
    (specCallees : List CapturedMir)
    (reqBody : CapturedMir)
    (optEnsBody : Option CapturedMir)
    (h_pre :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        And
          (And
            (Trusted.Sequence.length args = c.body.argCount)
            (MirBoolPredicateHolds reqBody args))
          (mem = (initMachineState c.body args).memory) := by
      intro _ _ h
      first
      | exact h
      | exact h.1)
    (h_check :
      checkMirAutoBoundedRange1SpecWithSpecCallees
        subjectFuel specFuel c.body c.callees specCallees reqBody optEnsBody = true := by rfl)
    (h_post :
      ∀ (args : List Value) (mem : Memory) (ret : Value) (mem' : Memory),
        OptMirBoolPredicateHoldsWithCallees
          optEnsBody specCallees (args ++ [ret]) →
        c.post args mem ret mem' := by
      intro _ _ _ _ h
      first
      | exact h
      | exact True.intro) :
    TotalVerificationResult c := by
  refine verifyTotalMirBounded c subjectFuel (fun args mem hp => ?_)
  rcases h_pre args mem hp with ⟨⟨h_len_body, h_req⟩, h_mem⟩
  subst h_mem
  dsimp only [checkMirAutoBoundedRange1SpecWithSpecCallees] at h_check
  cases hExt : extractMirUpperBound1 specFuel reqBody with
  | none =>
    rw [hExt] at h_check
    nomatch h_check
  | some boundSc =>
    rw [hExt] at h_check
    dsimp only at h_check
    cases hArg1 : Nat.beq c.body.argCount 1 with
    | false =>
      rw [hArg1] at h_check
      nomatch h_check
    | true =>
      rw [hArg1] at h_check
      dsimp only [Bool.and] at h_check
      cases hUb : checkMirUpperBound1 specFuel reqBody boundSc with
      | false =>
        rw [hUb] at h_check
        nomatch h_check
      | true =>
        rw [hUb] at h_check
        dsimp only [Bool.and] at h_check
        have h_len1 : length args = 1 :=
          Eq.trans h_len_body (Nat.eq_of_beq_eq_true hArg1)
        rcases checkMirUpperBound1_sound
          specFuel reqBody boundSc args hUb h_len1 h_req with ⟨b, hBle, hArgs⟩
        subst hArgs
        have hRun :=
          checkAllScalarRange1_at_sound
            specFuel reqBody
            (checkMirRustPinnedSpecOptWithSpecCallees
              subjectFuel specFuel c.body c.callees specCallees optEnsBody)
            boundSc.sizeBytes boundSc.bits b hBle h_check h_req
        have h_wp :=
          wpMirBounded_normal_of_checkMirRustPinnedSpecOptWithSpecCallees
            subjectFuel specFuel c.body c.callees specCallees optEnsBody
            [.scalar { bits := b, sizeBytes := boundSc.sizeBytes }]
            hRun
        let argsB : List Value := [.scalar { bits := b, sizeBytes := boundSc.sizeBytes }]
        have h_init_eq :
            initMachineStateWithMemoryAndCallees c.body argsB
              (initMachineState c.body argsB).memory c.callees =
            initMachineStateWithCallees c.body argsB c.callees := by
          cases c.callees <;> rfl
        rw [h_init_eq]
        rw [← wpMirSym_eq_wpMirBounded] at h_wp ⊢
        exact wpMirSym_mono
          (fun out ⟨rv, m', h_out, h_ens⟩ =>
            ⟨rv, m', h_out,
              h_post argsB (initMachineState c.body argsB).memory rv m' h_ens⟩)
          h_wp

/-- Direct node evaluator over `MirStepNode` for sufficient bounded boolean predicate evaluation. -/
def evalMirBoolExecTrueBounded : Nat → CapturedMir → MirExecState → Prop
  | .zero, _, _ => False
  | .succ fuel, body, st =>
    evalNodeWP
      (evalMirBoolExecTrueBounded fuel body)
      (mirSafePost (fun retVal _ => retVal = .scalar { bits := 1, sizeBytes := 1 }))
      (stepMirState body st)

/-- Sufficient bounded boolean predicate evaluation over `MachineState`. -/
def evalMirBoolTrueBounded (fuel : Nat) (body : CapturedMir) (s : MachineState) : Prop :=
  evalMirBoolExecTrueBounded fuel body (.running s)

/-- Bounded step-node sufficiency matching `evalMirBoolTrueBounded (.succ fuel)`. -/
def stepResultTrueBounded (fuel : Nat) (body : CapturedMir) (r : MirStepNode) : Prop :=
  evalNodeWP
    (evalMirBoolExecTrueBounded fuel body)
    (mirSafePost (fun retVal _ => retVal = .scalar { bits := 1, sizeBytes := 1 }))
    r

theorem wpMirExecSym_of_evalMirBoolExecTrueBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (h : evalMirBoolExecTrueBounded fuel body st) :
    wpMirExecSym fuel body st
      (mirSafePost (fun retVal _ => retVal = .scalar { bits := 1, sizeBytes := 1 })) := by
  induction fuel generalizing st with
  | zero => exact False.elim h
  | succ fuel' ih =>
    unfold evalMirBoolExecTrueBounded at h
    unfold wpMirExecSym
    rw [evalSymNodeTree_eq, stepMirExecSymTree_eval]
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

theorem mirBoolPredicateHolds_of_evalMirBoolTrueBounded
    (fuel : Nat) (specBody : CapturedMir) (args : List Value)
    (h : evalMirBoolTrueBounded fuel specBody (initMachineState specBody args)) :
    MirBoolPredicateHolds specBody args :=
  mirBoolPredicateHolds_of_wpMirSym fuel specBody args
    (wpMirExecSym_of_evalMirBoolExecTrueBounded fuel specBody
      (.running (initMachineState specBody args)) h)

theorem get?_some_of_blt_length :
    ∀ (args : List Value) (idx : Nat),
      Nat.blt idx (length args) = true →
      ∃ v, get? args idx = .some v
  | .nil, _, h => nomatch h
  | v :: _, .zero, _ => ⟨v, rfl⟩
  | _ :: rest, .succ idx, h => get?_some_of_blt_length rest idx h

/-- Check that any symbolic argument index written by `symStepStmtConcrete` is `< argCount`. -/
def symStepStmtInBounds
    (argCount : Nat)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (st : SymState)
    (stmt : Statement) :
    Bool :=
  match stmt.kind with
  | .assign ⟨_, .nil⟩ rv =>
    match evalSymRvalueConcrete st.slots st.borrows st.nextTag localDecls layouts rv with
    | .some (sv, _, _, _) =>
      match sv with
      | .concrete _ => true
      | .symArg idx => Nat.blt idx argCount
      | .symPair0 _ idx => Nat.blt idx argCount
      | .symGuarded _ idx => Nat.blt idx argCount
    | .none => false
  | _ => true

theorem symStepStmtConcrete_step_of_inBounds
    (body : CapturedMir)
    (args : List Value)
    (st st' : SymState)
    (stmt : Statement)
    (hLen : length args = body.argCount)
    (hInB : symStepStmtInBounds body.argCount body.localDecls body.layouts st stmt = true)
    (h : symStepStmtConcrete body.localDecls body.layouts st stmt = .some st') :
    evalStmt (concretizeSymState body args st) stmt body.localDecls body.layouts =
      MirStepNode.step (concretizeSymState body args st') := by
  cases stmt with
  | mk kind _ =>
    cases kind with
    | nop | coverage | constEvalCounter =>
      injection h with hEq
      subst hEq
      rfl
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
        have ⟨hNotDead, hOk⟩ := symSlot_not_dead_of_match_some h
        injection hOk with hEq
        subst hEq
        dsimp only
        rcases concretizeSymSlot_eq_of_not_dead args sSlot hNotDead with hSlot | ⟨_, hSlot⟩ <;>
          (rw [hSlot]; rfl)
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
        dsimp only at h ⊢
        rw [set?_concretizeSymSlots_concrete args .uninit st.slots loc]
        cases hSet : set? st.slots loc (.concrete .uninit) with
        | none =>
          rw [hSet] at h
          nomatch h
        | some slots' =>
          rw [hSet] at h
          injection h with hEq
          subst hEq
          rfl
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
        dsimp only at h ⊢
        rw [set?_concretizeSymSlots_concrete args .dead st.slots loc]
        cases hSet : set? st.slots loc (.concrete .dead) with
        | none =>
          rw [hSet] at h
          nomatch h
        | some slots' =>
          rw [hSet] at h
          injection h with hEq
          subst hEq
          rfl
    | assign dst rv =>
      cases dst with
      | mk dstLoc dstProj =>
        cases dstProj with
        | cons _ _ => nomatch h
        | nil =>
          dsimp only [symStepStmtConcrete] at h
          dsimp only [symStepStmtInBounds] at hInB
          dsimp only [evalStmt, concretizeSymState]
          cases hRv : evalSymRvalueConcrete st.slots st.borrows st.nextTag body.localDecls body.layouts rv with
          | none =>
            rw [hRv] at h
            nomatch h
          | some tup =>
            rw [hRv] at h hInB
            cases tup with
            | mk sv rest1 =>
              cases rest1 with
              | mk slots1 rest2 =>
                cases rest2 with
                | mk borrows1 nextTag1 =>
                  dsimp only at h hInB
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
                    have ⟨hNotDead, hOk⟩ := symSlot_not_dead_of_match_some h
                    cases sv with
                    | concrete val =>
                      dsimp only [concretizeSymRvalueResult] at hOk ⊢
                      rw [get?_concretizeSymSlots args slots1 dstLoc, hGet]
                      cases hSet : set? slots1 dstLoc (.concrete (.init val)) with
                      | none =>
                        rw [hSet] at hOk
                        nomatch hOk
                      | some slots2 =>
                        rw [hSet] at hOk
                        injection hOk with hEq
                        subst hEq
                        rw [set?_concretizeSymSlots_concrete args (.init val) slots1 dstLoc, hSet]
                        dsimp only
                        rcases concretizeSymSlot_eq_of_not_dead args sSlot hNotDead with hSlot | ⟨_, hSlot⟩ <;>
                          (rw [hSlot]; rfl)
                    | symArg valIdx =>
                      dsimp only at hOk hInB
                      cases hSet : set? slots1 dstLoc (.symArg valIdx) with
                      | none =>
                        rw [hSet] at hOk
                        nomatch hOk
                      | some slots2 =>
                        rw [hSet] at hOk
                        injection hOk with hEq
                        subst hEq
                        dsimp only [concretizeSymRvalueResult]
                        cases hArgVal : get? args valIdx with
                        | none =>
                          rcases get?_some_of_blt_length args valIdx (hLen.symm ▸ hInB) with ⟨_, hSome⟩
                          rw [hArgVal] at hSome
                          nomatch hSome
                        | some val =>
                          dsimp only
                          rw [get?_concretizeSymSlots args slots1 dstLoc, hGet]
                          have hSetSym := set?_concretizeSymSlots args (.symArg valIdx) slots1 dstLoc
                          dsimp only [concretizeSymSlot] at hSetSym
                          rw [hArgVal, hSet] at hSetSym
                          rw [hSetSym]
                          dsimp only
                          rcases concretizeSymSlot_eq_of_not_dead args sSlot hNotDead with hSlot | ⟨_, hSlot⟩ <;>
                            (rw [hSlot]; rfl)
                    | symPair0 v0 valIdx =>
                      dsimp only at hOk hInB
                      cases hSet : set? slots1 dstLoc (.symPair0 v0 valIdx) with
                      | none =>
                        rw [hSet] at hOk
                        nomatch hOk
                      | some slots2 =>
                        rw [hSet] at hOk
                        injection hOk with hEq
                        subst hEq
                        dsimp only [concretizeSymRvalueResult]
                        cases hArgVal : get? args valIdx with
                        | none =>
                          rcases get?_some_of_blt_length args valIdx (hLen.symm ▸ hInB) with ⟨_, hSome⟩
                          rw [hArgVal] at hSome
                          nomatch hSome
                        | some val =>
                          dsimp only
                          rw [get?_concretizeSymSlots args slots1 dstLoc, hGet]
                          have hSetSym := set?_concretizeSymSlots args (.symPair0 v0 valIdx) slots1 dstLoc
                          dsimp only [concretizeSymSlot] at hSetSym
                          rw [hArgVal, hSet] at hSetSym
                          rw [hSetSym]
                          dsimp only
                          rcases concretizeSymSlot_eq_of_not_dead args sSlot hNotDead with hSlot | ⟨_, hSlot⟩ <;>
                            (rw [hSlot]; rfl)
                    | symGuarded v0 valIdx =>
                      dsimp only at hOk hInB
                      cases hSet : set? slots1 dstLoc (.concrete (.init v0)) with
                      | none =>
                        rw [hSet] at hOk
                        nomatch hOk
                      | some slots2 =>
                        rw [hSet] at hOk
                        injection hOk with hEq
                        subst hEq
                        dsimp only [concretizeSymRvalueResult]
                        cases hArgVal : get? args valIdx with
                        | none =>
                          rcases get?_some_of_blt_length args valIdx (hLen.symm ▸ hInB) with ⟨_, hSome⟩
                          rw [hArgVal] at hSome
                          nomatch hSome
                        | some _ =>
                          dsimp only
                          rw [get?_concretizeSymSlots args slots1 dstLoc, hGet]
                          rw [set?_concretizeSymSlots_concrete args (.init v0) slots1 dstLoc, hSet]
                          dsimp only
                          rcases concretizeSymSlot_eq_of_not_dead args sSlot hNotDead with hSlot | ⟨_, hSlot⟩ <;>
                            (rw [hSlot]; rfl)
    | _ => nomatch h

/-- Execute one concrete symbolic step of `body` from `st`, requiring any symbolic
argument indices to be `< body.argCount`. -/
def symStepConcreteInBounds (body : CapturedMir) (st : SymState) : Option SymState :=
  match body.phase with
  | .other _ => .none
  | _ =>
    match get? body.basicBlocks st.blockIdx with
    | .none => .none
    | .some bb =>
      match get? bb.statements st.stmtIdx with
      | .some stmt =>
        match symStepStmtInBounds body.argCount body.localDecls body.layouts st stmt with
        | true => symStepStmtConcrete body.localDecls body.layouts st stmt
        | false => .none
      | .none =>
        match Nat.beq st.stmtIdx (length bb.statements) with
        | true => symStepTermConcrete st bb.terminator
        | false => .none

theorem symStepConcreteInBounds_true_sound
    (fuel : Nat)
    (body : CapturedMir)
    (args : List Value)
    (st st' : SymState)
    (hLen : length args = body.argCount)
    (h : symStepConcreteInBounds body st = .some st')
    (hTrue : evalMirBoolTrueBounded fuel body (concretizeSymState body args st')) :
    evalMirBoolTrueBounded (.succ fuel) body (concretizeSymState body args st) := by
  dsimp only [symStepConcreteInBounds] at h
  change stepResultTrueBounded fuel body (stepMirFn body (concretizeSymState body args st))
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
        cases hInB : symStepStmtInBounds body.argCount body.localDecls body.layouts st stmt with
        | false =>
          rw [hInB] at h
          nomatch h
        | true =>
          rw [hInB] at h
          dsimp only at h
          rw [stepMirFn_concretize_stmt body args st bb stmt hNotOther hBb hStmt]
          rw [symStepStmtConcrete_step_of_inBounds body args st st' stmt hLen hInB h]
          exact hTrue
      | none =>
        rw [hStmt] at h
        dsimp only at h
        cases hLenBb : Nat.beq st.stmtIdx (length bb.statements) with
        | false =>
          rw [hLenBb] at h
          nomatch h
        | true =>
          rw [hLenBb] at h
          dsimp only at h
          rw [stepMirFn_concretize_term body args st bb hNotOther hBb hStmt hLenBb]
          rcases symStepTermConcrete_sound body args st st' bb.terminator h with hTerm | ⟨ev, hTerm⟩
          · rw [hTerm]
            exact hTrue
          · rw [hTerm]
            cases ev <;> exact hTrue

/-- Check whether `st` is at a `Return` terminator with local `0` holding
`.scalar ⟨1, 1⟩` (`true`). -/
def symIsReturnTrue (body : CapturedMir) (st : SymState) : Bool :=
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
            | .some (.concrete (.init (.scalar ⟨1, 1⟩))) => true
            | _ => false
          | _ => false

theorem symIsReturnTrue_sound
    (fuel : Nat)
    (body : CapturedMir)
    (args : List Value)
    (st : SymState)
    (h : symIsReturnTrue body st = true) :
    evalMirBoolTrueBounded (.succ fuel) body (concretizeSymState body args st) := by
  dsimp only [symIsReturnTrue] at h
  change stepResultTrueBounded fuel body (stepMirFn body (concretizeSymState body args st))
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
          rw [stepMirFn_concretize_term body args st bb hNotOther hBb hStmt hLen]
          cases hTerm : bb.terminator with
          | mk tKind _ =>
            rw [hTerm] at h
            dsimp only at h
            cases tKind with
            | return_ =>
              dsimp only at h
              dsimp only [evalTerminator, concretizeSymState, concretizeSymMemory]
              rw [get?_concretizeSymSlots args st.slots 0]
              cases hGet0 : get? st.slots 0 with
              | none =>
                rw [hGet0] at h
                nomatch h
              | some sSlot0 =>
                rw [hGet0] at h
                cases sSlot0 with
                | symArg _ | symPair0 _ _ => nomatch h
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
                        | zero => nomatch h
                        | succ b' =>
                          cases b' with
                          | succ _ => nomatch h
                          | zero =>
                            cases sz with
                            | zero => nomatch h
                            | succ sz' =>
                              cases sz' with
                              | succ _ => nomatch h
                              | zero =>
                                rfl
            | _ => nomatch h

/-- Check whether concrete symbolic execution from `st` reaches `Return` with
`true` (`.scalar ⟨1, 1⟩`) within `fuel` steps. -/
def checkSymReturnsTrue : Nat → CapturedMir → SymState → Bool
  | .zero, _, _ => false
  | .succ fuel, body, st =>
    match symStepConcreteInBounds body st with
    | .some st' => checkSymReturnsTrue fuel body st'
    | .none => symIsReturnTrue body st

theorem checkSymReturnsTrue_sound :
    ∀ (fuel : Nat) (body : CapturedMir) (args : List Value) (st : SymState),
      length args = body.argCount →
      checkSymReturnsTrue fuel body st = true →
      evalMirBoolTrueBounded fuel body (concretizeSymState body args st)
  | .zero, _, _, _, _, hCheck => nomatch hCheck
  | .succ fuel, body, args, st, hLen, hCheck => by
    dsimp only [checkSymReturnsTrue] at hCheck
    cases hStep : symStepConcreteInBounds body st with
    | some st' =>
      rw [hStep] at hCheck
      exact symStepConcreteInBounds_true_sound
        fuel body args st st' hLen hStep
        (checkSymReturnsTrue_sound fuel body args st' hLen hCheck)
    | none =>
      rw [hStep] at hCheck
      exact symIsReturnTrue_sound fuel body args st hCheck

/-- Check whether `op` and RHS bits `b` form a valid non-empty unsigned upper bound
comparison (`ret <= b`, or `ret < b` with `b > 0`). -/
def isUnsignedEnsuresUpperOp (op : BinOp) (b : Nat) : Bool :=
  match op with
  | .le => true
  | .lt => Bool.not (Nat.beq b 0)
  | _ => false

theorem isUnsignedUpperBoundOp_of_ensuresUpper
    {op : BinOp} {b : Nat}
    (h : isUnsignedEnsuresUpperOp op b = true) :
    isUnsignedUpperBoundOp op = true := by
  cases op with
  | le | lt => rfl
  | _ => nomatch h

theorem evalUnsignedUpperBoundCmp_eq_true_of_ble
    (op : BinOp)
    (a b : Nat)
    (hOp : isUnsignedEnsuresUpperOp op b = true)
    (hBle : a ≤ tightUnsignedUpperBoundBits op b) :
    evalUnsignedUpperBoundCmp op a b = true := by
  cases op with
  | le =>
    dsimp only [evalUnsignedUpperBoundCmp, tightUnsignedUpperBoundBits] at hBle ⊢
    exact (nat_ble_eq_true_iff a b).2 hBle
  | lt =>
    dsimp only [isUnsignedEnsuresUpperOp, evalUnsignedUpperBoundCmp, tightUnsignedUpperBoundBits] at hOp hBle ⊢
    cases b with
    | zero => nomatch hOp
    | succ k =>
      dsimp only [Nat.pred] at hBle
      rw [(nat_ble_eq_false_iff (.succ k) a).2 (Nat.lt_succ_of_le hBle)]
      rfl
  | _ => nomatch hOp

/-- Complete an `ensures` upper-bound comparison at `dstLoc` by setting `dstLoc` to `true` (`⟨1, 1⟩`). -/
def symFinishEnsTrue
    (st : SymState)
    (dstLoc : Local)
    (slots₂ : List SymSlot)
    (expectedSc : ScalarInt) :
    Option (ScalarInt × SymState) :=
  match Nat.beq expectedSc.sizeBytes 0 with
  | true => .none
  | false =>
    match get? slots₂ dstLoc with
    | .none => .none
    | .some (.concrete .dead) => .none
    | .some _ =>
      match set? slots₂ dstLoc (.concrete (.init (.scalar ⟨1, 1⟩))) with
      | .some slotsTrue =>
        let borrows' := invalidateConflictingBorrows st.borrows dstLoc .none
        let stTrue : SymState := {
          st with
          stmtIdx := Nat.add st.stmtIdx 1
          slots := slotsTrue
          borrows := borrows'
        }
        .some (expectedSc, stTrue)
      | .none => .none

theorem symFinishEnsTrue_ok_sound
    (fuel : Nat)
    (body : CapturedMir)
    (args : List Value)
    (st : SymState)
    (dstLoc : Local)
    (slots₂ : List SymSlot)
    (expectedSc scOut : ScalarInt)
    (stTrue : SymState)
    (hFin : symFinishEnsTrue st dstLoc slots₂ expectedSc = .some (scOut, stTrue))
    (hTrue : evalMirBoolTrueBounded fuel body (concretizeSymState body args stTrue)) :
    scOut = expectedSc ∧
      stepResultTrueBounded fuel body
        (evalAssignNilRvalueStep
          (concretizeSymState body args st)
          dstLoc
          (.ok (.scalar ⟨1, 1⟩) (concretizeSymSlots args slots₂) (concretizeSymMemory body st))) := by
  dsimp only [symFinishEnsTrue] at hFin
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
      have ⟨hNotDead, hOk⟩ := symSlot_not_dead_of_match_some hFin
      cases hSetT : set? slots₂ dstLoc (.concrete (.init (.scalar ⟨1, 1⟩))) with
      | none =>
        rw [hSetT] at hOk
        nomatch hOk
      | some slotsTrue =>
        rw [hSetT] at hOk
        injection hOk with hPair
        injection hPair with hSc hStT
        subst hSc; subst hStT
        refine ⟨rfl, ?_⟩
        dsimp only [evalAssignNilRvalueStep, concretizeSymMemory]
        rw [get?_concretizeSymSlots args slots₂ dstLoc, hGetDst]
        dsimp only
        have hGoal2 :
          stepResultTrueBounded fuel body
            (match set? (concretizeSymSlots args slots₂) dstLoc (.init (.scalar ⟨1, 1⟩)) with
             | .some locals₂ =>
               let borrows₂ := invalidateConflictingBorrows st.borrows dstLoc .none
               .step (advanceStmt (concretizeSymState body args st) locals₂ {
                 nextAllocId := length body.allocations
                 globals := body.allocations
                 traitImpls := body.traitImpls
                 borrows := borrows₂
                 nextTag := st.nextTag
                 callees := .nil
                 callStack := .nil
                 activeCallee := .none
               })
             | .none => .fail .ub) := by
          rw [set?_concretizeSymSlots_concrete args (.init (.scalar ⟨1, 1⟩)) slots₂ dstLoc, hSetT]
          exact hTrue
        rcases concretizeSymSlot_eq_of_not_dead args dstSlot hNotDead with hSlot | ⟨_, hSlot⟩ <;>
          (rw [hSlot]; exact hGoal2)

/-- Extract a 2-argument `ensures` upper bound `(boundSc, stTrue)` from `stmt`
when `stmt` compares `.symArg 1` (`ret`) against `.concrete (.scalar sc)` via
`<=` or `<`. -/
def symExtractEnsuresUpperBound1Stmt
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (st : SymState)
    (stmt : Statement) :
    Option (ScalarInt × SymState) :=
  match stmt.kind with
  | .assign ⟨dstLoc, .nil⟩ (.binaryOp op lhsOp rhsOp) =>
    match evalSymOperand st.slots lhsOp st.borrows with
    | .some (sv₁, slots₁) =>
      match sv₁ with
      | .symArg (.succ .zero) =>
        match evalSymOperand slots₁ rhsOp st.borrows with
        | .some (sv₂, slots₂) =>
          match sv₂ with
          | .concrete (.scalar sc) =>
            match
              isUnsignedEnsuresUpperOp op sc.bits,
              operandIsSigned localDecls lhsOp layouts,
              Nat.beq sc.sizeBytes 0
            with
            | true, false, false =>
              let tightSc : ScalarInt := {
                bits := tightUnsignedUpperBoundBits op sc.bits
                sizeBytes := sc.sizeBytes
              }
              symFinishEnsTrue st dstLoc slots₂ tightSc
            | _, _, _ => .none
          | _ => .none
        | .none => .none
      | _ => .none
    | .none => .none
  | _ => .none

/-- Extract a 2-argument `ensures` upper bound from the current statement of `body` at `st`. -/
def symExtractEnsuresUpperBound1
    (body : CapturedMir)
    (st : SymState) :
    Option (ScalarInt × SymState) :=
  match body.phase with
  | .other _ => .none
  | _ =>
    match get? body.basicBlocks st.blockIdx with
    | .none => .none
    | .some bb =>
      match get? bb.statements st.stmtIdx with
      | .some stmt => symExtractEnsuresUpperBound1Stmt body.localDecls body.layouts st stmt
      | .none => .none

theorem symExtractEnsuresUpperBound1_sound
    (fuel : Nat)
    (body : CapturedMir)
    (args : List Value)
    (st : SymState)
    (boundSc : ScalarInt)
    (stTrue : SymState)
    (r : Nat)
    (hLen : length args = body.argCount)
    (hExt : symExtractEnsuresUpperBound1 body st = .some (boundSc, stTrue))
    (hTrue : checkSymReturnsTrue fuel body stTrue = true)
    (hArg1 : get? args 1 = .some (.scalar { bits := r, sizeBytes := boundSc.sizeBytes }))
    (hBle : r ≤ boundSc.bits) :
    evalMirBoolTrueBounded (.succ fuel) body (concretizeSymState body args st) := by
  dsimp only [symExtractEnsuresUpperBound1] at hExt
  change stepResultTrueBounded fuel body (stepMirFn body (concretizeSymState body args st))
  cases hPhase : body.phase with
  | other _ =>
    rw [hPhase] at hExt
    nomatch hExt
  | runtimePostCleanup | runtimeOptimized =>
    have hNotOther : ∀ msg, body.phase ≠ .other msg := by
      intro msg hm; rw [hPhase] at hm; nomatch hm
    rw [hPhase] at hExt
    dsimp only at hExt
    cases hBb : get? body.basicBlocks st.blockIdx with
    | none =>
      rw [hBb] at hExt
      nomatch hExt
    | some bb =>
      rw [hBb] at hExt
      dsimp only at hExt
      cases hStmt : get? bb.statements st.stmtIdx with
      | none =>
        rw [hStmt] at hExt
        nomatch hExt
      | some stmt =>
        rw [hStmt] at hExt
        dsimp only at hExt
        rw [stepMirFn_concretize_stmt body args st bb stmt hNotOther hBb hStmt]
        cases stmt with
        | mk kind span =>
          cases kind with
          | assign dst rv =>
            cases dst with
            | mk dstLoc dstProj =>
              cases dstProj with
              | cons _ _ => nomatch hExt
              | nil =>
                cases rv with
                | binaryOp op lhsOp rhsOp =>
                  dsimp only [symExtractEnsuresUpperBound1Stmt] at hExt
                  cases hLhs : evalSymOperand st.slots lhsOp st.borrows with
                  | none =>
                    rw [hLhs] at hExt
                    nomatch hExt
                  | some pair1 =>
                    rw [hLhs] at hExt
                    cases pair1 with
                    | mk sv1 slots1 =>
                      cases sv1 with
                      | concrete _ | symPair0 _ _ | symGuarded _ _ => nomatch hExt
                      | symArg idx0 =>
                        cases idx0 with
                        | zero => nomatch hExt
                        | succ idx1 =>
                          cases idx1 with
                          | succ _ => nomatch hExt
                          | zero =>
                            dsimp only at hExt
                            cases hRhs : evalSymOperand slots1 rhsOp st.borrows with
                            | none =>
                              rw [hRhs] at hExt
                              nomatch hExt
                            | some pair2 =>
                              rw [hRhs] at hExt
                              cases pair2 with
                              | mk sv2 slots2 =>
                                cases sv2 with
                                | symArg _ | symPair0 _ _ | symGuarded _ _ => nomatch hExt
                                | concrete v2 =>
                                  cases v2 with
                                  | unit | ptr _ _ | aggregate _ _ => nomatch hExt
                                  | scalar sc0 =>
                                    dsimp only at hExt
                                    cases hOp : isUnsignedEnsuresUpperOp op sc0.bits with
                                    | false =>
                                      rw [hOp] at hExt
                                      nomatch hExt
                                    | true =>
                                      rw [hOp] at hExt
                                      cases hSig : operandIsSigned body.localDecls lhsOp body.layouts with
                                      | true =>
                                        rw [hSig] at hExt
                                        nomatch hExt
                                      | false =>
                                        rw [hSig] at hExt
                                        cases hSz0 : Nat.beq sc0.sizeBytes 0 with
                                        | true =>
                                          rw [hSz0] at hExt
                                          nomatch hExt
                                        | false =>
                                          rw [hSz0] at hExt
                                          dsimp only at hExt
                                          let tightSc : ScalarInt := {
                                            bits := tightUnsignedUpperBoundBits op sc0.bits
                                            sizeBytes := sc0.sizeBytes
                                          }
                                          have ⟨hScEq, hStepTrue⟩ :=
                                            symFinishEnsTrue_ok_sound
                                              fuel body args st dstLoc slots2 tightSc boundSc stTrue
                                              hExt
                                              (checkSymReturnsTrue_sound fuel body args stTrue hLen hTrue)
                                          subst hScEq
                                          rw [evalStmt_assign_nil_eq]
                                          dsimp only [evalRvalue, concretizeSymState, concretizeSymMemory]
                                          rw [evalSymOperand_sound
                                            args st.slots lhsOp st.borrows body.allocations body.layouts
                                            (.symArg 1) slots1 hLhs]
                                          dsimp only [concretizeSymReadResult]
                                          rw [hArg1]
                                          dsimp only
                                          rw [evalSymOperand_sound
                                            args slots1 rhsOp st.borrows body.allocations body.layouts
                                            (.concrete (.scalar sc0)) slots2 hRhs]
                                          dsimp only [concretizeSymReadResult]
                                          rw [hSig]
                                          have hUbOp : isUnsignedUpperBoundOp op = true :=
                                            isUnsignedUpperBoundOp_of_ensuresUpper hOp
                                          have hSzEq : Nat.beq sc0.sizeBytes sc0.sizeBytes = true :=
                                            Nat.beq_refl sc0.sizeBytes
                                          rw [evalScalarBinOp_unsignedUpperBound_eq
                                            op
                                            { bits := r, sizeBytes := sc0.sizeBytes }
                                            sc0
                                            (concretizeSymSlots args slots2)
                                            { nextAllocId := length body.allocations
                                              globals := body.allocations
                                              traitImpls := body.traitImpls
                                              borrows := st.borrows
                                              nextTag := st.nextTag
                                              callees := .nil
                                              callStack := .nil
                                              activeCallee := .none }
                                            hUbOp hSz0 hSzEq]
                                          rw [evalUnsignedUpperBoundCmp_eq_true_of_ble op r sc0.bits hOp hBle]
                                          exact hStepTrue
                | _ => nomatch hExt
          | _ => nomatch hExt

/-- Check that `body` from `st` is satisfied whenever `arg 1` (`ret`) has
`sizeBytes = boundSc.sizeBytes` and `bits ≤ boundSc.bits`. -/
def checkSymEnsuresUpperBound1Loop :
    Nat → CapturedMir → SymState → ScalarInt → Bool
  | .zero, _, _, _ => false
  | .succ fuel, body, st, boundSc =>
    match symStepConcreteInBounds body st with
    | .some st' => checkSymEnsuresUpperBound1Loop fuel body st' boundSc
    | .none =>
      match symExtractEnsuresUpperBound1 body st with
      | .some (scOut, stTrue) =>
        Bool.and
          (Bool.and
            (Nat.beq scOut.bits boundSc.bits)
            (Nat.beq scOut.sizeBytes boundSc.sizeBytes))
          (checkSymReturnsTrue fuel body stTrue)
      | .none => false

theorem checkSymEnsuresUpperBound1Loop_sound :
    ∀ (fuel : Nat)
      (body : CapturedMir)
      (args : List Value)
      (st : SymState)
      (boundSc : ScalarInt)
      (r : Nat),
      length args = body.argCount →
      checkSymEnsuresUpperBound1Loop fuel body st boundSc = true →
      get? args 1 = .some (.scalar { bits := r, sizeBytes := boundSc.sizeBytes }) →
      r ≤ boundSc.bits →
      evalMirBoolTrueBounded fuel body (concretizeSymState body args st)
  | .zero, _, _, _, _, _, _, hCheck, _, _ => nomatch hCheck
  | .succ fuel, body, args, st, boundSc, r, hLen, hCheck, hArg1, hBle => by
    dsimp only [checkSymEnsuresUpperBound1Loop] at hCheck
    cases hStep : symStepConcreteInBounds body st with
    | some st' =>
      rw [hStep] at hCheck
      exact symStepConcreteInBounds_true_sound
        fuel body args st st' hLen hStep
        (checkSymEnsuresUpperBound1Loop_sound
          fuel body args st' boundSc r hLen hCheck hArg1 hBle)
    | none =>
      rw [hStep] at hCheck
      cases hExt : symExtractEnsuresUpperBound1 body st with
      | none =>
        rw [hExt] at hCheck
        nomatch hCheck
      | some pair =>
        rw [hExt] at hCheck
        cases pair with
        | mk scOut stTrue =>
          dsimp only at hCheck
          cases hBitsEq : Nat.beq scOut.bits boundSc.bits with
          | false =>
            rw [hBitsEq] at hCheck
            nomatch hCheck
          | true =>
            rw [hBitsEq] at hCheck
            cases hSzEq : Nat.beq scOut.sizeBytes boundSc.sizeBytes with
            | false =>
              rw [hSzEq] at hCheck
              nomatch hCheck
            | true =>
              rw [hSzEq] at hCheck
              dsimp only [Bool.and] at hCheck
              have hScEq : scOut = boundSc :=
                scalarInt_eq_of_parts
                  (Nat.eq_of_beq_eq_true hBitsEq)
                  (Nat.eq_of_beq_eq_true hSzEq)
              subst hScEq
              exact symExtractEnsuresUpperBound1_sound
                fuel body args st scOut stTrue r hLen hExt hCheck hArg1 hBle

/-- Check that `ensBody` is a 2-argument predicate `[x, ret]` satisfied whenever
`ret` has `sizeBytes = boundSc.sizeBytes` and `bits ≤ boundSc.bits`. -/
def checkMirEnsuresUpperBound1
    (fuel : Nat)
    (ensBody : CapturedMir)
    (boundSc : ScalarInt) :
    Bool :=
  Bool.and
    (Nat.beq ensBody.argCount 2)
    (checkSymEnsuresUpperBound1Loop fuel ensBody (initSymState ensBody) boundSc)

theorem checkMirEnsuresUpperBound1_sound
    (fuel : Nat)
    (ensBody : CapturedMir)
    (boundSc : ScalarInt)
    (v0 : Value)
    (r : Nat)
    (h_check : checkMirEnsuresUpperBound1 fuel ensBody boundSc = true)
    (h_ble : r ≤ boundSc.bits) :
    MirBoolPredicateHolds
      ensBody
      [v0, .scalar { bits := r, sizeBytes := boundSc.sizeBytes }] := by
  dsimp only [checkMirEnsuresUpperBound1] at h_check
  cases hArg2 : Nat.beq ensBody.argCount 2 with
  | false =>
    rw [hArg2] at h_check
    nomatch h_check
  | true =>
    rw [hArg2] at h_check
    dsimp only [Bool.and] at h_check
    let args : List Value := [v0, .scalar { bits := r, sizeBytes := boundSc.sizeBytes }]
    have hLen : length args = ensBody.argCount :=
      Eq.symm (Nat.eq_of_beq_eq_true hArg2)
    apply mirBoolPredicateHolds_of_evalMirBoolTrueBounded fuel ensBody args
    rw [← concretizeSymState_initSymState ensBody args hLen]
    exact checkSymEnsuresUpperBound1Loop_sound
      fuel ensBody args (initSymState ensBody) boundSc r hLen h_check rfl h_ble

/-- Fast AST scan for the first unsigned upper-bound constant comparison in `stmts`. -/
def peekStmtsUpperBound : List Statement → Option ScalarInt
  | .nil => .none
  | stmt :: rest =>
    match stmt.kind with
    | .assign _ (.binaryOp op _ (.constant { val := .scalar (.int sc), .. })) =>
      match isUnsignedUpperBoundOp op with
      | true =>
        .some {
          bits := tightUnsignedUpperBoundBits op sc.bits
          sizeBytes := sc.sizeBytes
        }
      | false => peekStmtsUpperBound rest
    | _ => peekStmtsUpperBound rest

/-- Fast AST scan for the unsigned upper bound constant in `body`'s entry block (`bb0`). -/
def peekMirUpperBound (body : CapturedMir) : ScalarInt :=
  match body.basicBlocks with
  | bb0 :: _ =>
    match peekStmtsUpperBound bb0.statements with
    | .some sc => sc
    | .none => { bits := 0, sizeBytes := 0 }
  | .nil => { bits := 0, sizeBytes := 0 }

/-- Upper-bound bit value extracted by `peekMirUpperBound`. -/
def peekMirUpperBoundBits (body : CapturedMir) : Nat :=
  (peekMirUpperBound body).bits

/-- Scalar width in bytes extracted by `peekMirUpperBound`. -/
def peekMirUpperBoundSz (body : CapturedMir) : Nat :=
  (peekMirUpperBound body).sizeBytes

/-- Pure arithmetic postcondition over `retVal` sufficient for `OptMirBoolPredicateHolds optEnsBody`. -/
def symOptEnsuresUpperPost (optEnsBody : Option CapturedMir) : Value → Memory → Prop :=
  match optEnsBody with
  | .some ensBody =>
    fun retVal _ =>
      match retVal with
      | .scalar retSc =>
        retSc.sizeBytes = peekMirUpperBoundSz ensBody ∧
          retSc.bits ≤ peekMirUpperBoundBits ensBody
      | _ => False
  | .none => fun _ _ => True

/-- Check whether `optEnsBody` is either `.none` or a valid 2-argument unsigned
upper-bound `ensures` companion. -/
def checkOptMirEnsuresUpperBound1
    (specFuel : Nat)
    (optEnsBody : Option CapturedMir) :
    Bool :=
  match optEnsBody with
  | .some ensBody =>
    checkMirEnsuresUpperBound1 specFuel ensBody (peekMirUpperBound ensBody)
  | .none => true

theorem optMirBoolPredicateHolds_of_symOptEnsuresUpperPost
    (specFuel : Nat)
    (optEnsBody : Option CapturedMir)
    (v0 retVal : Value)
    (mem' : Memory)
    (h_ens_check : checkOptMirEnsuresUpperBound1 specFuel optEnsBody = true)
    (h_post : symOptEnsuresUpperPost optEnsBody retVal mem') :
    OptMirBoolPredicateHolds optEnsBody [v0, retVal] := by
  cases optEnsBody with
  | none => exact True.intro
  | some ensBody =>
    dsimp only [checkOptMirEnsuresUpperBound1] at h_ens_check
    dsimp only [symOptEnsuresUpperPost] at h_post
    cases retVal with
    | unit | ptr _ _ | aggregate _ _ => exact False.elim h_post
    | scalar retSc =>
      rcases retSc with ⟨rBits, rSz⟩
      rcases h_post with ⟨hSz, hBle⟩
      dsimp only at hSz hBle
      subst hSz
      exact checkMirEnsuresUpperBound1_sound
        specFuel ensBody (peekMirUpperBound ensBody) v0 rBits h_ens_check hBle

/-- Closed-term checker that `reqBody` and `optEnsBody` are valid 1-argument
unsigned upper-bound companions for `subjectBody`. -/
def checkMirAutoSymRange1Bound
    (specFuel : Nat)
    (subjectBody reqBody : CapturedMir)
    (optEnsBody : Option CapturedMir) :
    Bool :=
  Bool.and
    (Bool.and
      (Nat.beq subjectBody.argCount 1)
      (checkMirUpperBound1 specFuel reqBody (peekMirUpperBound reqBody)))
    (checkOptMirEnsuresUpperBound1 specFuel optEnsBody)

/-- One-call bound-independent symbolic range discharge combinator for
1-argument unsigned `Claim`s with an inequality precondition
(`requires: x < K` or `x <= K`) of arbitrary magnitude `K`. -/
theorem dischargeRustSymRange1Auto
    (c : Claim)
    (subjectFuel specFuel : Nat)
    (reqBody : CapturedMir)
    (optEnsBody : Option CapturedMir)
    (h_pre :
      ∀ args : List Value,
        c.pre args →
        And
          (Trusted.Sequence.length args = c.body.argCount)
          (MirBoolPredicateHolds reqBody args) := by
      intro _ h; exact h)
    (h_bound :
      checkMirAutoSymRange1Bound specFuel c.body reqBody optEnsBody = true := by rfl)
    (h_sym :
      ∀ (b : Nat),
        b ≤ peekMirUpperBoundBits reqBody →
        wpMirSym subjectFuel c.body
          (initMachineStateWithCallees c.body
            [.scalar { bits := b, sizeBytes := peekMirUpperBoundSz reqBody }]
            c.callees)
          (mirNormalPost (symOptEnsuresUpperPost optEnsBody)) := by
      intro b hBle
      (conv at hBle => rhs; whnf)
      (conv => arg 3; arg 2; arg 1; arg 1; arg 2; whnf)
      (repeat' ((conv => whnf); split))
      all_goals (conv => whnf)
      all_goals
        try (refine ⟨?_, ?_⟩
             · (conv => lhs; whnf); (conv => rhs; whnf); try rfl
             · (conv => rhs; whnf); simp_all; try omega)
      all_goals
        try (simp_all; try omega))
    (h_post :
      ∀ (args : List Value) (ret : Value),
        OptMirBoolPredicateHolds optEnsBody (args ++ [ret]) →
        c.post args ret := by
      intro _ _ h
      first
      | exact h
      | exact True.intro) :
    VerificationResult c := by
  refine verifyMirNoPanicSym c subjectFuel (fun args hp => ?_)
  rcases h_pre args hp with ⟨h_len_body, h_req⟩
  dsimp only [checkMirAutoSymRange1Bound] at h_bound
  cases hArg1 : Nat.beq c.body.argCount 1 with
  | false =>
    rw [hArg1] at h_bound
    nomatch h_bound
  | true =>
    rw [hArg1] at h_bound
    cases hReqUb : checkMirUpperBound1 specFuel reqBody (peekMirUpperBound reqBody) with
    | false =>
      rw [hReqUb] at h_bound
      nomatch h_bound
    | true =>
      rw [hReqUb] at h_bound
      dsimp only [Bool.and] at h_bound
      have h_len1 : length args = 1 :=
        Eq.trans h_len_body (Nat.eq_of_beq_eq_true hArg1)
      rcases checkMirUpperBound1_sound
        specFuel reqBody (peekMirUpperBound reqBody) args hReqUb h_len1 h_req with ⟨b, hBle, hArgs⟩
      subst hArgs
      let v0 : Value := .scalar { bits := b, sizeBytes := peekMirUpperBoundSz reqBody }
      exact wpMirSym_mono
        (fun out ho => by
          cases out with
          | normal p =>
            rcases p with ⟨retVal, mem'⟩
            exact h_post [v0] retVal
              (optMirBoolPredicateHolds_of_symOptEnsuresUpperPost
                specFuel optEnsBody v0 retVal mem' h_bound ho)
          | panic => exact False.elim ho
          | abort => exact False.elim ho)
        (h_sym b hBle)

/-- One-call bound-independent symbolic range discharge combinator for
1-argument unsigned `TotalClaim`s (`#[spec(safe_total, ...)]`) with an
inequality precondition (`requires: x < K` or `x <= K`) of arbitrary magnitude `K`. -/
theorem dischargeRustTotalSymRange1Auto
    (c : TotalClaim)
    (subjectFuel specFuel : Nat)
    (reqBody : CapturedMir)
    (optEnsBody : Option CapturedMir)
    (h_pre :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        And
          (And
            (Trusted.Sequence.length args = c.body.argCount)
            (MirBoolPredicateHolds reqBody args))
          (mem = (initMachineState c.body args).memory) := by
      intro _ _ h
      first
      | exact h
      | exact h.1)
    (h_bound :
      checkMirAutoSymRange1Bound specFuel c.body reqBody optEnsBody = true := by rfl)
    (h_sym :
      ∀ (b : Nat),
        b ≤ peekMirUpperBoundBits reqBody →
        wpMirSym subjectFuel c.body
          (initMachineStateWithCallees c.body
            [.scalar { bits := b, sizeBytes := peekMirUpperBoundSz reqBody }]
            c.callees)
          (mirNormalPost (symOptEnsuresUpperPost optEnsBody)) := by
      intro b hBle
      (conv at hBle => rhs; whnf)
      (conv => arg 3; arg 2; arg 1; arg 1; arg 2; whnf)
      (repeat' ((conv => whnf); split))
      all_goals (conv => whnf)
      all_goals
        try (refine ⟨?_, ?_⟩
             · (conv => lhs; whnf); (conv => rhs; whnf); try rfl
             · (conv => rhs; whnf); simp_all; try omega)
      all_goals
        try (simp_all; try omega))
    (h_post :
      ∀ (args : List Value) (mem : Memory) (ret : Value) (mem' : Memory),
        OptMirBoolPredicateHolds optEnsBody (args ++ [ret]) →
        c.post args mem ret mem' := by
      intro _ _ _ _ h
      first
      | exact h
      | exact True.intro) :
    TotalVerificationResult c := by
  refine verifyTotalMirSym c subjectFuel (fun args mem hp => ?_)
  rcases h_pre args mem hp with ⟨⟨h_len_body, h_req⟩, h_mem⟩
  subst h_mem
  dsimp only [checkMirAutoSymRange1Bound] at h_bound
  cases hArg1 : Nat.beq c.body.argCount 1 with
  | false =>
    rw [hArg1] at h_bound
    nomatch h_bound
  | true =>
    rw [hArg1] at h_bound
    cases hReqUb : checkMirUpperBound1 specFuel reqBody (peekMirUpperBound reqBody) with
    | false =>
      rw [hReqUb] at h_bound
      nomatch h_bound
    | true =>
      rw [hReqUb] at h_bound
      dsimp only [Bool.and] at h_bound
      have h_len1 : length args = 1 :=
        Eq.trans h_len_body (Nat.eq_of_beq_eq_true hArg1)
      rcases checkMirUpperBound1_sound
        specFuel reqBody (peekMirUpperBound reqBody) args hReqUb h_len1 h_req with ⟨b, hBle, hArgs⟩
      subst hArgs
      let v0 : Value := .scalar { bits := b, sizeBytes := peekMirUpperBoundSz reqBody }
      change wpMirSym subjectFuel c.body
        (initMachineStateWithMemoryAndCallees c.body [v0]
          (initMachineState c.body [v0]).memory c.callees)
        (mirNormalPost (c.post [v0] (initMachineState c.body [v0]).memory))
      have h_init_eq :
          initMachineStateWithMemoryAndCallees c.body [v0]
            (initMachineState c.body [v0]).memory c.callees =
          initMachineStateWithCallees c.body [v0] c.callees := by
        cases c.callees <;> rfl
      rw [h_init_eq]
      exact wpMirSym_mono
        (fun out ho => by
          cases out with
          | normal p =>
            rcases p with ⟨retVal, mem'⟩
            exact h_post [v0] (initMachineState c.body [v0]).memory retVal mem'
              (optMirBoolPredicateHolds_of_symOptEnsuresUpperPost
                specFuel optEnsBody v0 retVal mem' h_bound ho)
          | panic => exact False.elim ho
          | abort => exact False.elim ho)
        (h_sym b hBle)

/-! ### Compositional Modular Call-Graph Contract Reflection (`dischargeRustModularContractAuto`) -/

/-- Substitute `.symArg (idx + k)` with `vs[k]` for each `v` in `vs`. -/
def substSymSlotsFrom : Nat → List Value → List SymSlot → List SymSlot
  | _, .nil, slots => slots
  | idx, v :: vs, slots =>
    substSymSlotsFrom (.succ idx) vs (substSymSlots idx v slots)

theorem get?_append_left :
    ∀ (xs ys : List Value) (idx : Nat) (v : Value),
      get? xs idx = .some v →
      get? (xs ++ ys) idx = .some v
  | .nil, _, .zero, _, h => nomatch h
  | .nil, _, .succ _, _, h => nomatch h
  | _ :: _, _, .zero, _, h => h
  | _ :: rest, ys, .succ idx, v, h => get?_append_left rest ys idx v h

theorem concretizeSymSlots_substSymSlotsFrom_append
    (callArgs tailArgs : List Value) :
    ∀ (remArgs : List Value) (idx : Nat) (slots : List SymSlot),
      dropValues idx callArgs = remArgs →
      concretizeSymSlots (callArgs ++ tailArgs) (substSymSlotsFrom idx remArgs slots) =
        concretizeSymSlots (callArgs ++ tailArgs) slots
  | .nil, _, _, _ => rfl
  | v :: vs, idx, slots, hDrop => by
    dsimp only [substSymSlotsFrom]
    have hArg0 : get? callArgs idx = .some v := by
      rw [get?_eq_head_dropValues callArgs idx, hDrop]
    have hArg : get? (callArgs ++ tailArgs) idx = .some v :=
      get?_append_left callArgs tailArgs idx v hArg0
    have hNext := dropValues_succ_of_cons callArgs idx v vs hDrop
    rw [concretizeSymSlots_substSymSlotsFrom_append
      callArgs tailArgs vs (.succ idx) (substSymSlots idx v slots) hNext]
    exact concretizeSymSlots_substSymSlots (callArgs ++ tailArgs) idx v hArg slots

/-- Initialize `SymState` for `calleeEnsBody` with `callArgs` pre-substituted
into `.symArg 0 .. .symArg (length callArgs - 1)`, leaving `.symArg (length callArgs)`
symbolic for `retVal`. -/
def initSymStateWithCallArgs
    (calleeEnsBody : CapturedMir)
    (callArgs : List Value) :
    SymState :=
  let st0 := initSymState calleeEnsBody
  { st0 with slots := substSymSlotsFrom 0 callArgs st0.slots }

theorem length_append_singleton :
    ∀ (xs : List Value) (retVal : Value),
      length (xs ++ [retVal]) = .succ (length xs)
  | .nil, _ => rfl
  | _ :: rest, retVal => congrArg Nat.succ (length_append_singleton rest retVal)

theorem get?_append_singleton_length :
    ∀ (xs : List Value) (retVal : Value),
      get? (xs ++ [retVal]) (length xs) = .some retVal
  | .nil, _ => rfl
  | _ :: rest, retVal => get?_append_singleton_length rest retVal

theorem concretizeSymState_initSymStateWithCallArgs
    (calleeEnsBody : CapturedMir)
    (callArgs : List Value)
    (retVal : Value)
    (h_argCount : calleeEnsBody.argCount = .succ (length callArgs)) :
    concretizeSymState calleeEnsBody (callArgs ++ [retVal])
      (initSymStateWithCallArgs calleeEnsBody callArgs) =
      initMachineState calleeEnsBody (callArgs ++ [retVal]) := by
  have hLen : length (callArgs ++ [retVal]) = calleeEnsBody.argCount := by
    rw [length_append_singleton, h_argCount]
  rw [← concretizeSymState_initSymState calleeEnsBody (callArgs ++ [retVal]) hLen]
  dsimp only [concretizeSymState, concretizeSymMemory, initSymStateWithCallArgs, initSymState]
  rw [concretizeSymSlots_substSymSlotsFrom_append
    callArgs [retVal] callArgs 0 (initSymSlots calleeEnsBody.localDecls calleeEnsBody.argCount) rfl]

/-- Extract the concrete `ScalarInt` pinned for `retVal` (`.symArg (length callArgs)`)
by `calleeEnsBody` when invoked with `callArgs`. -/
def extractCalleeEnsuresRetPin
    (fuel : Nat)
    (calleeEnsBody : CapturedMir)
    (callArgs : List Value) :
    Option ScalarInt :=
  let pins :=
    collectSymPinsLoop
      fuel
      calleeEnsBody
      (initSymStateWithCallArgs calleeEnsBody callArgs)
  lookupScalarPin (length callArgs) pins

/-- Check that `calleeEnsBody` pins `retVal` to `expectedRet` when invoked with `callArgs`. -/
def checkCalleeEnsuresPinsRet
    (fuel : Nat)
    (calleeEnsBody : CapturedMir)
    (callArgs : List Value)
    (expectedRet : ScalarInt) :
    Bool :=
  Bool.and
    (Nat.beq calleeEnsBody.argCount (.succ (length callArgs)))
    (checkSymPinsLoop
      fuel
      calleeEnsBody
      (initSymStateWithCallArgs calleeEnsBody callArgs)
      [(length callArgs, expectedRet)])

theorem checkCalleeEnsuresPinsRet_sound
    (fuel : Nat)
    (calleeEnsBody : CapturedMir)
    (callArgs : List Value)
    (expectedRet : ScalarInt)
    (retVal : Value)
    (h_check :
      checkCalleeEnsuresPinsRet fuel calleeEnsBody callArgs expectedRet = true)
    (h_ens : MirBoolPredicateHolds calleeEnsBody (callArgs ++ [retVal])) :
    retVal = .scalar expectedRet := by
  dsimp only [checkCalleeEnsuresPinsRet] at h_check
  cases hArgEq : Nat.beq calleeEnsBody.argCount (.succ (length callArgs)) with
  | false =>
    rw [hArgEq] at h_check
    nomatch h_check
  | true =>
    rw [hArgEq] at h_check
    dsimp only [Bool.and] at h_check
    have hHold :
        evalMirBoolHoldBounded fuel calleeEnsBody
          (initMachineState calleeEnsBody (callArgs ++ [retVal])) :=
      wpBoolOrExhausted_of_mirBoolPredicateHolds
        fuel calleeEnsBody (callArgs ++ [retVal]) h_ens
    rw [← concretizeSymState_initSymStateWithCallArgs
      calleeEnsBody callArgs retVal (Nat.eq_of_beq_eq_true hArgEq)] at hHold
    have ⟨hPin, _⟩ :=
      checkSymPinsLoop_sound
        fuel calleeEnsBody (callArgs ++ [retVal])
        (initSymStateWithCallArgs calleeEnsBody callArgs)
        [(length callArgs, expectedRet)]
        h_check hHold
    rw [get?_append_singleton_length callArgs retVal] at hPin
    injection hPin

/-- Fuel-bounded recursive step loop for `checkMirRustModularPinnedSpec`. -/
def checkMirRustModularPinnedSpecLoop
    (specFuel : Nat)
    (subjectBody : CapturedMir)
    (optSubjectEnsBody : Option CapturedMir)
    (calleeDefPath : String)
    (calleeArgCount : Nat)
    (optCalleeReqBody : Option CapturedMir)
    (calleeEnsBody : CapturedMir)
    (args : List Value) :
    Nat → MirExecState → Bool
  | 0, _ => false
  | fuel' + 1, st =>
    match stepMirState subjectBody st with
    | .ret out =>
      match out with
      | .normal (retVal, _) =>
        checkOptMirBoolBounded specFuel optSubjectEnsBody (args ++ [retVal])
      | .panic => false
      | .abort => false
    | .tau st' =>
      checkMirRustModularPinnedSpecLoop
        specFuel subjectBody optSubjectEnsBody
        calleeDefPath calleeArgCount optCalleeReqBody calleeEnsBody args fuel' st'
    | .vis i k =>
      match i with
      | .inl _ => false
      | .inr rest =>
        match rest with
        | .inl _ =>
          checkMirRustModularPinnedSpecLoop
            specFuel subjectBody optSubjectEnsBody
            calleeDefPath calleeArgCount optCalleeReqBody calleeEnsBody args fuel' (k PUnit.unit)
        | .inr c =>
          match c with
          | .call req =>
            match extractCalleeEnsuresRetPin specFuel calleeEnsBody req.args with
            | .none => false
            | .some expectedRet =>
              Bool.and
                (Bool.and
                  (decide (req.defPath = calleeDefPath))
                  (Bool.and
                    (Nat.beq (length req.args) calleeArgCount)
                    (checkOptMirBoolBounded specFuel optCalleeReqBody req.args)))
                (Bool.and
                  (checkCalleeEnsuresPinsRet specFuel calleeEnsBody req.args expectedRet)
                  (checkMirRustModularPinnedSpecLoop
                    specFuel subjectBody optSubjectEnsBody
                    calleeDefPath calleeArgCount optCalleeReqBody calleeEnsBody args
                    fuel' (k (.returned (.scalar expectedRet) req.memory))))

/-- Computable check that `subjectBody` evaluates on `args` within `subjectFuel`
steps—resolving external calls to `calleeDefPath` via
`(optCalleeReqBody, calleeEnsBody)`—to a normal return value `retVal` satisfying
`checkOptMirBoolBounded specFuel optSubjectEnsBody (args ++ [retVal])`. -/
def checkMirRustModularPinnedSpec
    (subjectFuel specFuel : Nat)
    (subjectBody : CapturedMir)
    (optSubjectEnsBody : Option CapturedMir)
    (calleeDefPath : String)
    (calleeArgCount : Nat)
    (optCalleeReqBody : Option CapturedMir)
    (calleeEnsBody : CapturedMir)
    (args : List Value)
    (callees : List CapturedMir := .nil) :
    Bool :=
  checkMirRustModularPinnedSpecLoop
    specFuel subjectBody optSubjectEnsBody
    calleeDefPath calleeArgCount optCalleeReqBody calleeEnsBody args
    subjectFuel (.running (initMachineStateWithCallees subjectBody args callees))

theorem wpMirModularBounded_of_checkMirRustModularPinnedSpec
    (C : MirCallContract)
    (subjectFuel specFuel : Nat)
    (subjectBody : CapturedMir)
    (optSubjectEnsBody : Option CapturedMir)
    (calleeDefPath : String)
    (calleeArgCount : Nat)
    (optCalleeReqBody : Option CapturedMir)
    (calleeEnsBody : CapturedMir)
    (args : List Value)
    (Q : MirOutcome → Prop)
    (h_call_pre :
      ∀ req : MirCallReq,
        req.defPath = calleeDefPath →
        Trusted.Sequence.length req.args = calleeArgCount →
        OptMirBoolPredicateHolds optCalleeReqBody req.args →
        C.pre req)
    (h_call_post :
      ∀ (req : MirCallReq) (ans : MirCallAns),
        C.post req ans →
        ∃ retVal,
          And (ans = .returned retVal req.memory)
            (MirBoolPredicateHolds calleeEnsBody (req.args ++ [retVal])))
    (h_post :
      ∀ (retVal : Value) (mem' : Memory),
        OptMirBoolPredicateHolds optSubjectEnsBody (args ++ [retVal]) →
        Q (.normal (retVal, mem')))
    (callees : List CapturedMir := .nil)
    (h_ok :
      checkMirRustModularPinnedSpec
        subjectFuel specFuel subjectBody optSubjectEnsBody
        calleeDefPath calleeArgCount optCalleeReqBody calleeEnsBody args callees = true) :
    wpMirModularBounded subjectFuel C.toCallContract subjectBody
      (initMachineStateWithCallees subjectBody args callees) Q := by
  unfold checkMirRustModularPinnedSpec at h_ok
  unfold wpMirModularBounded
  suffices ∀ (fuel : Nat) (st : MirExecState),
      checkMirRustModularPinnedSpecLoop
        specFuel subjectBody optSubjectEnsBody
        calleeDefPath calleeArgCount optCalleeReqBody calleeEnsBody args fuel st = true →
      wpCoalBounded fuel (mirModularWP C.toCallContract) (stepMirState subjectBody)
        (fun out _ => Q out) st PUnit.unit from
    this subjectFuel _ h_ok
  intro fuel
  induction fuel with
  | zero => intro _ h; nomatch h
  | succ fuel' ih =>
    intro st h
    unfold checkMirRustModularPinnedSpecLoop at h
    unfold wpCoalBounded
    cases h_step : stepMirState subjectBody st with
    | ret out =>
      simp only [h_step] at h ⊢
      cases out with
      | normal p =>
        rcases p with ⟨rv, m⟩
        exact h_post rv m (optMirBoolPredicateHolds_of_checkBounded
          specFuel optSubjectEnsBody (args ++ [rv]) h)
      | panic => nomatch h
      | abort => nomatch h
    | tau st' =>
      simp only [h_step] at h ⊢
      exact ih st' h
    | vis i k =>
      simp only [h_step] at h ⊢
      cases i with
      | inl f => nomatch h
      | inr rest =>
        cases rest with
        | inl e =>
          cases e
          exact ih (k PUnit.unit) h
        | inr c =>
          cases c with
          | call req =>
            dsimp only at h
            cases hExt : extractCalleeEnsuresRetPin specFuel calleeEnsBody req.args with
            | none =>
              rw [hExt] at h
              nomatch h
            | some expectedRet =>
              rw [hExt] at h
              dsimp only at h
              cases hPath : decide (req.defPath = calleeDefPath) with
              | false =>
                rw [hPath] at h
                nomatch h
              | true =>
                rw [hPath] at h
                cases hLen : Nat.beq (length req.args) calleeArgCount with
                | false =>
                  rw [hLen] at h
                  nomatch h
                | true =>
                  rw [hLen] at h
                  cases hReq : checkOptMirBoolBounded specFuel optCalleeReqBody req.args with
                  | false =>
                    rw [hReq] at h
                    nomatch h
                  | true =>
                    rw [hReq] at h
                    dsimp only [Bool.and] at h
                    cases hPin :
                      checkCalleeEnsuresPinsRet specFuel calleeEnsBody req.args expectedRet with
                    | false =>
                      rw [hPin] at h
                      nomatch h
                    | true =>
                      rw [hPin] at h
                      dsimp only [Bool.and] at h
                      refine ⟨?_, ?_⟩
                      · exact h_call_pre req
                          (of_decide_eq_true hPath)
                          (Nat.eq_of_beq_eq_true hLen)
                          (optMirBoolPredicateHolds_of_checkBounded
                            specFuel optCalleeReqBody req.args hReq)
                      · intro ans hPost
                        rcases h_call_post req ans hPost with ⟨retVal, hAns, hEns⟩
                        have hRet : retVal = .scalar expectedRet :=
                          checkCalleeEnsuresPinsRet_sound
                            specFuel calleeEnsBody req.args expectedRet retVal hPin hEns
                        rw [hAns, hRet]
                        exact ih (k (.returned (.scalar expectedRet) req.memory)) h

/-- Closed-term checker for a caller with pinned (or 0-argument) `optSubjectReqBody`
invoking `calleeDefPath`. -/
def checkMirAutoModularPinnedSpec
    (subjectFuel specFuel : Nat)
    (subjectBody : CapturedMir)
    (optSubjectReqBody optSubjectEnsBody : Option CapturedMir)
    (calleeDefPath : String)
    (calleeArgCount : Nat)
    (optCalleeReqBody : Option CapturedMir)
    (calleeEnsBody : CapturedMir)
    (callees : List CapturedMir := .nil) :
    Bool :=
  let expected := extractOptMirRequiresPins specFuel optSubjectReqBody
  Bool.and
    (Nat.beq subjectBody.argCount (length expected))
    (Bool.and
      (checkOptMirRequiresPinsScalars specFuel optSubjectReqBody expected)
      (checkMirRustModularPinnedSpec
        subjectFuel specFuel subjectBody optSubjectEnsBody
        calleeDefPath calleeArgCount optCalleeReqBody calleeEnsBody
        (mapScalarValues expected) callees))

/-- One-call automatic discharge combinator for a modular caller (`ModularClaim`)
with pinned (or 0-argument) `requires` invoking a sibling callee `C`. -/
theorem dischargeRustModularContractAuto
    (C : MirCallContract)
    (subjectBody : CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (subjectFuel specFuel : Nat)
    (optSubjectReqBody optSubjectEnsBody : Option CapturedMir)
    (calleeDefPath : String)
    (calleeArgCount : Nat)
    (optCalleeReqBody : Option CapturedMir)
    (calleeEnsBody : CapturedMir)
    (callees : List CapturedMir := .nil)
    (h_pre :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        And
          (And
            (Trusted.Sequence.length args = subjectBody.argCount)
            (OptMirBoolPredicateHolds optSubjectReqBody args))
          (mem = (initMachineState subjectBody args).memory) := by
      intro _ _ h
      first
      | exact h
      | exact h.1
      | exact ⟨⟨h.1, True.intro⟩, h.2⟩
      | exact ⟨⟨h.1.1, True.intro⟩, h.1.2⟩
      | exact ⟨⟨h.2.1, True.intro⟩, h.1.2⟩)
    (h_call_pre :
      ∀ req : MirCallReq,
        req.defPath = calleeDefPath →
        Trusted.Sequence.length req.args = calleeArgCount →
        OptMirBoolPredicateHolds optCalleeReqBody req.args →
        C.pre req := by
      intro _ h_path h_len h_req
      first
      | exact ⟨h_path, h_len, h_req⟩
      | exact ⟨h_path, h_len⟩
      | exact ⟨h_path, h_len, True.intro⟩)
    (h_call_post :
      ∀ (req : MirCallReq) (ans : MirCallAns),
        C.post req ans →
        ∃ retVal,
          And (ans = .returned retVal req.memory)
            (MirBoolPredicateHolds calleeEnsBody (req.args ++ [retVal])) := by
      intro _ _ h
      first
      | exact h
      | (rcases h with ⟨rv, hAns, _, hEns⟩; exact ⟨rv, hAns, hEns⟩))
    (h_check :
      checkMirAutoModularPinnedSpec
        subjectFuel specFuel subjectBody optSubjectReqBody optSubjectEnsBody
        calleeDefPath calleeArgCount optCalleeReqBody calleeEnsBody callees = true := by rfl)
    (h_post :
      ∀ (args : List Value) (mem : Memory) (ret : Value) (mem' : Memory),
        OptMirBoolPredicateHolds optSubjectEnsBody (args ++ [ret]) →
        post args mem ret mem' := by
      intro _ _ _ _ h
      first
      | exact h
      | exact True.intro) :
    ModularVerificationResult
      { body := subjectBody, envAssumed := C.holdsOn, pre := pre, post := post, callees := callees } := by
  refine verifyModularContractWithCalleesMirBounded C subjectBody callees pre post subjectFuel (fun args mem hp => ?_)
  rcases h_pre args mem hp with ⟨⟨h_len_body, h_req⟩, h_mem⟩
  subst h_mem
  dsimp only [checkMirAutoModularPinnedSpec] at h_check
  let expected := extractOptMirRequiresPins specFuel optSubjectReqBody
  cases hArgEq : Nat.beq subjectBody.argCount (length expected) with
  | false =>
    rw [hArgEq] at h_check
    nomatch h_check
  | true =>
    rw [hArgEq] at h_check
    dsimp only [Bool.and] at h_check
    cases hPins : checkOptMirRequiresPinsScalars specFuel optSubjectReqBody expected with
    | false =>
      rw [hPins] at h_check
      nomatch h_check
    | true =>
      rw [hPins] at h_check
      dsimp only [Bool.and] at h_check
      have h_len : length args = length expected :=
        Eq.trans h_len_body (Nat.eq_of_beq_eq_true hArgEq)
      have h_args : args = mapScalarValues expected :=
        checkOptMirRequiresPinsScalars_sound
          specFuel optSubjectReqBody expected args hPins h_len h_req
      subst h_args
      let argsPin := mapScalarValues expected
      have h_init_eq :
          initMachineStateWithMemoryAndCallees subjectBody argsPin
            (initMachineState subjectBody argsPin).memory callees =
          initMachineStateWithCallees subjectBody argsPin callees := by
        cases callees <;> rfl
      rw [h_init_eq]
      exact wpMirModularBounded_of_checkMirRustModularPinnedSpec
        C subjectFuel specFuel subjectBody optSubjectEnsBody
        calleeDefPath calleeArgCount optCalleeReqBody calleeEnsBody
        argsPin
        (fun out =>
          ∀ retVal mem',
            out = .normal (retVal, mem') →
            post argsPin (initMachineState subjectBody argsPin).memory retVal mem')
        h_call_pre h_call_post
        (fun retVal mem' hEns rv m' hOut => by
          injection hOut with hPair
          cases hPair
          exact h_post argsPin (initMachineState subjectBody argsPin).memory retVal mem' hEns)
        callees
        h_check

/-- Closed-term checker for a 1-argument unsigned caller with bounded inequality
`subjectReqBody` (`requires: x < K` or `x <= K`) invoking `calleeDefPath`. -/
def checkMirAutoModularBoundedRange1Spec
    (subjectFuel specFuel : Nat)
    (subjectBody subjectReqBody : CapturedMir)
    (optSubjectEnsBody : Option CapturedMir)
    (calleeDefPath : String)
    (calleeArgCount : Nat)
    (optCalleeReqBody : Option CapturedMir)
    (calleeEnsBody : CapturedMir)
    (callees : List CapturedMir := .nil) :
    Bool :=
  match extractMirUpperBound1 specFuel subjectReqBody with
  | .none => false
  | .some boundSc =>
    Bool.and
      (Nat.beq subjectBody.argCount 1)
      (Bool.and
        (checkMirUpperBound1 specFuel subjectReqBody boundSc)
        (checkAllScalarRange1
          specFuel
          subjectReqBody
          (fun args =>
            checkMirRustModularPinnedSpec
              subjectFuel specFuel subjectBody optSubjectEnsBody
              calleeDefPath calleeArgCount optCalleeReqBody calleeEnsBody args callees)
          boundSc.sizeBytes
          boundSc.bits))

/-- One-call automatic discharge combinator for a 1-argument unsigned modular caller
(`ModularClaim`) with bounded inequality `requires` (`x < K` or `x <= K`) invoking
a sibling callee `C`. -/
theorem dischargeRustModularBoundedRange1Auto
    (C : MirCallContract)
    (subjectBody : CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (subjectFuel specFuel : Nat)
    (subjectReqBody : CapturedMir)
    (optSubjectEnsBody : Option CapturedMir)
    (calleeDefPath : String)
    (calleeArgCount : Nat)
    (optCalleeReqBody : Option CapturedMir)
    (calleeEnsBody : CapturedMir)
    (callees : List CapturedMir := .nil)
    (h_pre :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        And
          (And
            (Trusted.Sequence.length args = subjectBody.argCount)
            (MirBoolPredicateHolds subjectReqBody args))
          (mem = (initMachineState subjectBody args).memory) := by
      intro _ _ h
      first
      | exact h
      | exact h.1)
    (h_call_pre :
      ∀ req : MirCallReq,
        req.defPath = calleeDefPath →
        Trusted.Sequence.length req.args = calleeArgCount →
        OptMirBoolPredicateHolds optCalleeReqBody req.args →
        C.pre req := by
      intro _ h_path h_len h_req
      first
      | exact ⟨h_path, h_len, h_req⟩
      | exact ⟨h_path, h_len⟩
      | exact ⟨h_path, h_len, True.intro⟩)
    (h_call_post :
      ∀ (req : MirCallReq) (ans : MirCallAns),
        C.post req ans →
        ∃ retVal,
          And (ans = .returned retVal req.memory)
            (MirBoolPredicateHolds calleeEnsBody (req.args ++ [retVal])) := by
      intro _ _ h
      first
      | exact h
      | (rcases h with ⟨rv, hAns, _, hEns⟩; exact ⟨rv, hAns, hEns⟩))
    (h_check :
      checkMirAutoModularBoundedRange1Spec
        subjectFuel specFuel subjectBody subjectReqBody optSubjectEnsBody
        calleeDefPath calleeArgCount optCalleeReqBody calleeEnsBody callees = true := by rfl)
    (h_post :
      ∀ (args : List Value) (mem : Memory) (ret : Value) (mem' : Memory),
        OptMirBoolPredicateHolds optSubjectEnsBody (args ++ [ret]) →
        post args mem ret mem' := by
      intro _ _ _ _ h
      first
      | exact h
      | exact True.intro) :
    ModularVerificationResult
      { body := subjectBody, envAssumed := C.holdsOn, pre := pre, post := post, callees := callees } := by
  refine verifyModularContractWithCalleesMirBounded C subjectBody callees pre post subjectFuel (fun args mem hp => ?_)
  rcases h_pre args mem hp with ⟨⟨h_len_body, h_req⟩, h_mem⟩
  subst h_mem
  dsimp only [checkMirAutoModularBoundedRange1Spec] at h_check
  cases hExt : extractMirUpperBound1 specFuel subjectReqBody with
  | none =>
    rw [hExt] at h_check
    nomatch h_check
  | some boundSc =>
    rw [hExt] at h_check
    dsimp only at h_check
    cases hArg1 : Nat.beq subjectBody.argCount 1 with
    | false =>
      rw [hArg1] at h_check
      nomatch h_check
    | true =>
      rw [hArg1] at h_check
      dsimp only [Bool.and] at h_check
      cases hUb : checkMirUpperBound1 specFuel subjectReqBody boundSc with
      | false =>
        rw [hUb] at h_check
        nomatch h_check
      | true =>
        rw [hUb] at h_check
        dsimp only [Bool.and] at h_check
        have h_len1 : length args = 1 :=
          Eq.trans h_len_body (Nat.eq_of_beq_eq_true hArg1)
        rcases checkMirUpperBound1_sound
          specFuel subjectReqBody boundSc args hUb h_len1 h_req with ⟨b, hBle, hArgs⟩
        subst hArgs
        have hRun :=
          checkAllScalarRange1_at_sound
            specFuel subjectReqBody
            (fun args =>
              checkMirRustModularPinnedSpec
                subjectFuel specFuel subjectBody optSubjectEnsBody
                calleeDefPath calleeArgCount optCalleeReqBody calleeEnsBody args callees)
            boundSc.sizeBytes boundSc.bits b hBle h_check h_req
        let argsB : List Value := [.scalar { bits := b, sizeBytes := boundSc.sizeBytes }]
        have h_init_eq :
            initMachineStateWithMemoryAndCallees subjectBody argsB
              (initMachineState subjectBody argsB).memory callees =
            initMachineStateWithCallees subjectBody argsB callees := by
          cases callees <;> rfl
        rw [h_init_eq]
        exact wpMirModularBounded_of_checkMirRustModularPinnedSpec
          C subjectFuel specFuel subjectBody optSubjectEnsBody
          calleeDefPath calleeArgCount optCalleeReqBody calleeEnsBody
          argsB
          (fun out =>
            ∀ retVal mem',
              out = .normal (retVal, mem') →
              post argsB (initMachineState subjectBody argsB).memory retVal mem')
          h_call_pre h_call_post
          (fun retVal mem' hEns rv m' hOut => by
            injection hOut with hPair
            cases hPair
            exact h_post argsB (initMachineState subjectBody argsB).memory retVal mem' hEns)
          callees
          hRun

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
      checkMirRustPinnedSpecWithCallees
        subjectFuel
        specFuel
        c.body
        ensBody
        c.callees
        [.scalar { bits := constVal, sizeBytes := width }] =
        true := by rfl)
    (h_post :
      ∀ ret : Value,
        MirBoolPredicateHoldsWithCallees
          ensBody
          c.callees
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
    wpMirBounded_of_checkMirRustPinnedSpecWithCallees
      subjectFuel specFuel c.body ensBody c.callees
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
      checkMirRustPinnedSpecWithCallees
        subjectFuel
        specFuel
        c.body
        ensBody
        c.callees
        [ .scalar { bits := c1, sizeBytes := w1 }
        , .scalar { bits := c2, sizeBytes := w2 } ] =
        true := by rfl)
    (h_post :
      ∀ ret : Value,
        MirBoolPredicateHoldsWithCallees
          ensBody
          c.callees
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
    wpMirBounded_of_checkMirRustPinnedSpecWithCallees
      subjectFuel specFuel c.body ensBody c.callees
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
