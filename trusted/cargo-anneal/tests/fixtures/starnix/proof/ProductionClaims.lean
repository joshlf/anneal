-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import InitialCache

namespace ProductionClaims

open Trusted.MirModel Trusted.MirSemantics Anneal.MirWp Endianness
  ProductionReduction

/-- The value that `apply_endianness` returns for each byte-order flag and
width index, written with the same masks and shifts as the Rust source. -/
def sourceOutput (toBe : Bool) (width : Nat) (value : Word) : Word :=
  match toBe, width with
  | false, 0 => value &&& 255
  | false, 1 => value &&& 65535
  | false, 2 => value &&& 4294967295
  | false, _ => value
  | true, 0 => swap8 value
  | true, 1 => swap16 value
  | true, 2 => swap32 value
  | true, _ => swap64 value

/-- Every flag and width runs the captured body to `sourceOutput`. Each path is
executed block by block with `Anneal.MirWp`'s `BlockExec` rules. Symbolic `u64`
assignments store their `BitVec 64` value through `evalStatement_assignU64`;
every other step closes by `eq_refl`, which also checks the returned value
against `sourceOutput`. The assignment rules come before the plain
`blockExec_cons` step: on a symbolic value, `eq_refl` reaches the `checkVal`
test, which never reduces, and fails only after a long search. -/
theorem sourceExecutes (toBe : Bool) (width : Fin 4) (value : Word) :
    Executes sourceBody (initial sourceBody (endianArgs toBe width.val value))
      (u64Val (sourceOutput toBe width.val value)) := by
  revert width value
  cases toBe <;> apply fin4_cases <;> intro value <;>
  · unfold initial
    repeat (first
      | (apply executes_of_blockExec; eq_refl)
      | (apply blockExec_storageLive; eq_refl; eq_refl)
      | (apply blockExec_storageDead; eq_refl; eq_refl)
      | (apply blockExec_cons
         apply evalStatement_assignU64 (rv := .binaryOp .bitAnd _ _)
         eq_refl; eq_refl; eq_refl; eq_refl; apply u64BitAndVal_eq
         eq_refl; eq_refl)
      | (apply blockExec_cons
         apply evalStatement_assignU64 (rv := .binaryOp .bitOr _ _)
         eq_refl; eq_refl; eq_refl; eq_refl; apply u64BitOrVal_eq
         eq_refl; eq_refl)
      | (apply blockExec_cons
         apply evalStatement_assignU64 (rv := .binaryOp .shl _ _)
         eq_refl; eq_refl; eq_refl; eq_refl; apply u64ShlVal_eq
         eq_refl; eq_refl)
      | (apply blockExec_cons
         apply evalStatement_assignU64 (rv := .binaryOp .shr _ _)
         eq_refl; eq_refl; eq_refl; eq_refl; apply u64ShrVal_eq
         eq_refl; eq_refl)
      | (apply blockExec_cons
         apply evalStatement_assignU64 (rv := .use _)
         eq_refl; eq_refl; eq_refl; eq_refl; eq_refl; eq_refl; eq_refl)
      | (apply blockExec_cons; eq_refl)
      | (apply blockExec_nil_step; eq_refl; eq_refl)
      | (apply blockExec_nil_ret; eq_refl; eq_refl))

theorem sourceReturns (toBe : Bool) (width : Fin 4) (value : Word) :
    Returns sourceBody (endianArgs toBe width.val value)
      (u64Val (sourceOutput toBe width.val value)) :=
  executes_returns (sourceExecutes toBe width value)

theorem wellFormed :
    BodyStaticAdmitted sourceProgram sourceBody = true := rfl

theorem behavior_of_sourceReturns {flag : Bool} {width : Fin 4} {value : Word}
    {ret : Val}
    (h_ret : Returns sourceBody (endianArgs flag width.val value) ret) :
    Behavior (entryProgForBody sourceProgram 0)
      { args := endianArgs flag width.val value }
      (.returned ⟨ret, ⟨[]⟩⟩) :=
  behavior_of_returns rfl wellFormed
    (validEntryArgs_bodyEndianArgs sourceBody _ rfl rfl rfl flag width value) h_ret

theorem completed :
    ∀ flag : Bool, ∀ width : Fin 4, ∀ value : Word,
      Safe sourceBody (endianArgs flag width.val value) ∧
      ∃ output, Returns sourceBody (endianArgs flag width.val value) output :=
  fun flag width value =>
    ⟨executes_safe (sourceExecutes flag width value), _,
      sourceReturns flag width value⟩

theorem baseline (safetyPre : List Val → Prop) :
    BodyVerified sourceProgram 0 sourceBody safetyPre := by
  refine bodyVerified_of_safe rfl wellFormed (fun args valid _ => ?_)
  apply validArgs3_elim sourceBody _ rfl rfl (Safe sourceBody) _ args valid
  intro flag width value
  exact (completed flag width value).1

theorem bigEndian_exact :
    ∀ width : Fin 4, ∀ value : Word, ∃ output : Word,
      Behavior (entryProgForBody sourceProgram 0)
        { args := endianArgs true width.val value }
        (.returned ⟨u64Val output, ⟨[]⟩⟩) ∧
      ByteReversal (8 * 2 ^ width.val) value output := by
  refine fin4_cases ?_ ?_ ?_ ?_
  · intro value
    exact ⟨_, behavior_of_sourceReturns (sourceReturns true 0 value),
      swap8_exact value⟩
  · intro value
    exact ⟨_, behavior_of_sourceReturns (sourceReturns true 1 value),
      swap16_exact value⟩
  · intro value
    exact ⟨_, behavior_of_sourceReturns (sourceReturns true 2 value),
      swap32_exact value⟩
  · intro value
    exact ⟨_, behavior_of_sourceReturns (sourceReturns true 3 value),
      swap64_exact value⟩

theorem littleEndian_exact :
    ∀ width : Fin 4, ∀ value : Word, ∃ output : Word,
      Behavior (entryProgForBody sourceProgram 0)
        { args := endianArgs false width.val value }
        (.returned ⟨u64Val output, ⟨[]⟩⟩) ∧
      output = value &&& BitVec.ofNat 64 (2 ^ (8 * 2 ^ width.val) - 1) := by
  refine fin4_cases ?_ ?_ ?_ ?_
  · intro value
    exact ⟨_, behavior_of_sourceReturns (sourceReturns false 0 value), rfl⟩
  · intro value
    exact ⟨_, behavior_of_sourceReturns (sourceReturns false 1 value), rfl⟩
  · intro value
    exact ⟨_, behavior_of_sourceReturns (sourceReturns false 2 value), rfl⟩
  · intro value
    refine ⟨_, behavior_of_sourceReturns (sourceReturns false 3 value), ?_⟩
    have mask : BitVec.ofNat 64 (2 ^ (8 * 2 ^ (3 : Nat)) - 1) =
        BitVec.allOnes 64 := rfl
    change value = value &&& BitVec.ofNat 64 (2 ^ (8 * 2 ^ (3 : Nat)) - 1)
    rw [mask, BitVec.and_allOnes]

theorem bigEndian_involutive :
    ∀ width : Fin 4, ∀ value : Word, ∃ first second : Word,
      Behavior (entryProgForBody sourceProgram 0)
        { args := endianArgs true width.val value }
        (.returned ⟨u64Val first, ⟨[]⟩⟩) ∧
      Behavior (entryProgForBody sourceProgram 0)
        { args := endianArgs true width.val first }
        (.returned ⟨u64Val second, ⟨[]⟩⟩) ∧
      second = value &&& BitVec.ofNat 64 (2 ^ (8 * 2 ^ width.val) - 1) := by
  refine fin4_cases ?_ ?_ ?_ ?_
  · intro value
    exact ⟨_, _, behavior_of_sourceReturns (sourceReturns true 0 value),
      behavior_of_sourceReturns (sourceReturns true 0 (swap8 value)),
      swap8_involutive value⟩
  · intro value
    exact ⟨_, _, behavior_of_sourceReturns (sourceReturns true 1 value),
      behavior_of_sourceReturns (sourceReturns true 1 (swap16 value)),
      swap16_involutive value⟩
  · intro value
    exact ⟨_, _, behavior_of_sourceReturns (sourceReturns true 2 value),
      behavior_of_sourceReturns (sourceReturns true 2 (swap32 value)),
      swap32_involutive value⟩
  · intro value
    refine ⟨_, _, behavior_of_sourceReturns (sourceReturns true 3 value),
      behavior_of_sourceReturns (sourceReturns true 3 (swap64 value)), ?_⟩
    have mask : BitVec.ofNat 64 (2 ^ (8 * 2 ^ (3 : Nat)) - 1) =
        BitVec.allOnes 64 := rfl
    change swap64 (swap64 value) =
      value &&& BitVec.ofNat 64 (2 ^ (8 * 2 ^ (3 : Nat)) - 1)
    rw [mask, BitVec.and_allOnes]
    exact swap64_involutive value

end ProductionClaims
