
import Trusted
import Anneal.MirFuelFree
import Anneal.PureMirExec

set_option maxRecDepth 2048
namespace Anneal.PureMirExec

open Trusted.Effect
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.Rustc.V2026_06_01.SymbolicEval

theorem mirBoolPredicateHolds_elim_of_pureExec
    (specBody : CapturedMir) (args : List Value) {P : Prop} [Decidable P]
    (h_pure : checkPureMir specBody = true)
    (h_conv : PureMirConverges specBody (initPureState specBody args)
      (· = .scalar { bits := if P then 1 else 0, sizeBytes := 1 })) :
    MirBoolPredicateHolds specBody args → P := by
  intro h_holds
  have h_conv_wp := mirWpConverges_of_pureExec_init h_pure h_conv
  have h_term : MirWpConverges specBody (initMachineState specBody args) (fun _ => True) :=
    MirWpConverges.mono (fun _ _ => trivial) h_conv_wp
  have h_holds_wp := (mirBoolPredicateHolds_iff_wpConverges specBody args h_term).1 h_holds
  have h_conj := MirWpConverges.conj h_conv_wp h_holds_wp
  rcases MirWpConverges.exists_outcome h_conj with ⟨out, h_out_conv, h_out_holds⟩
  cases out with
  | normal ret =>
    rcases ret with ⟨v, mem⟩
    have h_post : v = .scalar { bits := if P then 1 else 0, sizeBytes := 1 } := h_out_conv.2
    have h_post' : v = .scalar { bits := 1, sizeBytes := 1 } := h_out_holds
    rw [h_post'] at h_post
    injection h_post with h_eq
    injection h_eq with h_eq
    by_cases hP : P
    · exact hP
    · rw [ite_eq_right_iff.mpr (fun h => (hP h).elim)] at h_eq
      contradiction
  | panic => exact False.elim h_out_conv
  | abort => exact False.elim h_out_conv

theorem mirBoolPredicateHoldsWithCallees_iff_wpConverges
    (specBody : CapturedMir) (callees : List CapturedMir) (args : List Value)
    (h_term :
      MirWpConverges specBody (initMachineStateWithCallees specBody args callees) (fun _ => True)) :
    Anneal.MirFuelFree.MirBoolPredicateHoldsWithCallees specBody callees args ↔
      MirWpConverges specBody (initMachineStateWithCallees specBody args callees)
        (mirSafePost
          (fun retVal _ => retVal = .scalar { bits := 1, sizeBytes := 1 })) := by
  constructor
  · intro h_holds
    rcases h_term with ⟨fuel, hf_term⟩
    exact ⟨fuel, (mirBoolPredicateHoldsWithCallees_iff_wpMirBoolWithCalleesSym fuel specBody callees args hf_term).1 h_holds⟩
  · exact mirBoolPredicateHoldsWithCallees_of_wpConverges specBody callees args

theorem mirBoolPredicateHoldsWithCallees_elim_of_pureExec
    (specBody : CapturedMir) (callees : List CapturedMir) (args : List Value) {P : Prop} [Decidable P]
    (h_pure : checkPureMir specBody = true)
    (h_conv : PureMirConvergesWithCallees specBody callees (initPureState specBody args)
      (· = .scalar { bits := if P then 1 else 0, sizeBytes := 1 })) :
    Anneal.MirFuelFree.MirBoolPredicateHoldsWithCallees specBody callees args → P := by
  intro h_holds
  have h_pure' := checkPureMirWithCallees_of_checkPureMir callees 0 specBody.traitImpls h_pure
  have h_conv_wp := mirWpConverges_of_pureExecWithCallees_init h_pure' h_conv
  have h_term : MirWpConverges specBody (initMachineStateWithCallees specBody args callees) (fun _ => True) :=
    MirWpConverges.mono (fun _ _ => trivial) h_conv_wp
  have h_holds_wp := (mirBoolPredicateHoldsWithCallees_iff_wpConverges specBody callees args h_term).1 h_holds
  have h_conj := MirWpConverges.conj h_conv_wp h_holds_wp
  rcases MirWpConverges.exists_outcome h_conj with ⟨out, h_out_conv, h_out_holds⟩
  cases out with
  | normal ret =>
    rcases ret with ⟨v, mem⟩
    have h_post : v = .scalar { bits := if P then 1 else 0, sizeBytes := 1 } := h_out_conv.2
    have h_post' : v = .scalar { bits := 1, sizeBytes := 1 } := h_out_holds
    rw [h_post'] at h_post
    injection h_post with h_eq
    injection h_eq with h_eq
    by_cases hP : P
    · exact hP
    · rw [ite_eq_right_iff.mpr (fun h => (hP h).elim)] at h_eq
      contradiction
  | panic => exact False.elim h_out_conv
  | abort => exact False.elim h_out_conv

def PureMirUniqueTruePath (specBody : CapturedMir) (args : List Value) {P : Prop} : Prop :=
  checkPureMir specBody = true ∧
  (P → PureMirConverges specBody (initPureState specBody args) (· = .scalar { bits := 1, sizeBytes := 1 })) ∧
  (¬ P → PureMirConverges specBody (initPureState specBody args) (· = .scalar { bits := 0, sizeBytes := 1 }))

theorem mirBoolPredicateHolds_elim_of_uniqueTruePath
    (specBody : CapturedMir) (args : List Value) {P : Prop} [Decidable P]
    (h_uniq : PureMirUniqueTruePath specBody args (P := P)) :
    MirBoolPredicateHolds specBody args → P := by
  intro h_holds
  by_cases hP : P
  · exact hP
  · have h_conv : PureMirConverges specBody (initPureState specBody args) (· = .scalar { bits := 0, sizeBytes := 1 }) :=
      h_uniq.2.2 hP
    have h_conv_wp := mirWpConverges_of_pureExec_init h_uniq.1 h_conv
    have h_term : MirWpConverges specBody (initMachineState specBody args) (fun _ => True) :=
      MirWpConverges.mono (fun _ _ => trivial) h_conv_wp
    have h_holds_wp := (mirBoolPredicateHolds_iff_wpConverges specBody args h_term).1 h_holds
    have h_conj := MirWpConverges.conj h_conv_wp h_holds_wp
    rcases MirWpConverges.exists_outcome h_conj with ⟨out, h_out_conv, h_out_holds⟩
    cases out with
    | normal ret =>
      rcases ret with ⟨v, mem⟩
      have h_post : v = .scalar { bits := 0, sizeBytes := 1 } := h_out_conv.2
      have h_post' : v = .scalar { bits := 1, sizeBytes := 1 } := h_out_holds
      rw [h_post'] at h_post
      injection h_post with h_eq
      injection h_eq with h_eq
      contradiction
    | panic => exact False.elim h_out_conv
    | abort => exact False.elim h_out_conv

theorem mirBoolPredicateHolds_intro_of_pureExec
    (specBody : CapturedMir) (args : List Value) {P : Prop}
    (h_pure : checkPureMir specBody = true)
    (h_conv : P → PureMirConverges specBody (initPureState specBody args)
      (· = .scalar { bits := 1, sizeBytes := 1 })) :
    P → MirBoolPredicateHolds specBody args := by
  intro hP
  exact mirBoolPredicateHolds_of_pureExec specBody args h_pure (h_conv hP)

syntax "#mir_lift_spec" ident : command

macro "mir_lift_spec" : tactic => `(tactic|
  first
  | exact mirBoolPredicateHolds_intro_of_pureExec _ _ rfl (fun _ => ⟨40, rfl⟩)
  | refine mirBoolPredicateHolds_elim_of_pureExec _ _ rfl ⟨40, rfl⟩ ?_
  | refine mirBoolPredicateHolds_elim_of_uniqueTruePath _ _ ⟨rfl, fun _ => ⟨40, rfl⟩, fun _ => ⟨40, rfl⟩⟩ ?_
)

end Anneal.PureMirExec
