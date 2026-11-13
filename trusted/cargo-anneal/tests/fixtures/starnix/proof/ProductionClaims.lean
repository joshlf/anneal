-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import ProductionEndpoints

namespace ProductionClaims

open Trusted.Mvp Anneal.Mvp Endianness ProductionReduction ProductionSteps

theorem wellFormed : bodyWF sourceBody = true := by decide

theorem completed :
    ∀ flag : Fin 2, ∀ width : Fin 4, ∀ value : Word,
      Safe sourceBody
        [BitVec.ofNat 64 flag.val, BitVec.ofNat 64 width.val, value] ∧
      ∃ output, Returns sourceBody
        [BitVec.ofNat 64 flag.val, BitVec.ofNat 64 width.val, value] output := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))
  · exact fin4_cases
      (fun v => ⟨(le8 v).1, _, (le8 v).2⟩)
      (fun v => ⟨(le16 v).1, _, (le16 v).2⟩)
      (fun v => ⟨(le32 v).1, _, (le32 v).2⟩)
      (fun v => ⟨(le64 v).1, _, (le64 v).2⟩)
  · exact fin4_cases
      (fun v => ⟨(be8 v).1, _, (be8 v).2⟩)
      (fun v => ⟨(be16 v).1, _, (be16 v).2⟩)
      (fun v => ⟨(be32 v).1, _, (be32 v).2⟩)
      (fun v => ⟨(be64 v).1, _, (be64 v).2⟩)

theorem baseline (safetyPre : List Word → Prop) :
    BodyVerified sourceBody safetyPre := by
  constructor
  · exact wellFormed
  · intro args valid _
    apply validArgs3_elim sourceBody 1363 rfl rfl rfl (Safe sourceBody) _ args valid
    intro flag width value
    exact (completed flag width value).1

theorem bigEndian_exact :
    ∀ width : Fin 4, ∀ value : Word, ∃ output,
      Safe sourceBody [1, BitVec.ofNat 64 width.val, value] ∧
      Returns sourceBody [1, BitVec.ofNat 64 width.val, value] output ∧
      ByteReversal (8 * 2 ^ width.val) value output := by
  refine fin4_cases ?_ ?_ ?_ ?_
  · intro value
    have execution := be8 value
    exact ⟨_, execution.1, execution.2, swap8_exact value⟩
  · intro value
    have execution := be16 value
    exact ⟨_, execution.1, execution.2, swap16_exact value⟩
  · intro value
    have execution := be32 value
    exact ⟨_, execution.1, execution.2, swap32_exact value⟩
  · intro value
    have execution := be64 value
    exact ⟨_, execution.1, execution.2, swap64_exact value⟩

theorem littleEndian_exact :
    ∀ width : Fin 4, ∀ value : Word, ∃ output,
      Safe sourceBody [0, BitVec.ofNat 64 width.val, value] ∧
      Returns sourceBody [0, BitVec.ofNat 64 width.val, value] output ∧
      output = value &&& BitVec.ofNat 64 (2 ^ (8 * 2 ^ width.val) - 1) := by
  refine fin4_cases ?_ ?_ ?_ ?_
  · intro value
    exact ⟨_, (le8 value).1, (le8 value).2, rfl⟩
  · intro value
    exact ⟨_, (le16 value).1, (le16 value).2, rfl⟩
  · intro value
    exact ⟨_, (le32 value).1, (le32 value).2, rfl⟩
  · intro value
    refine ⟨_, (le64 value).1, (le64 value).2, ?_⟩
    have mask : BitVec.ofNat 64 (2 ^ (8 * 2 ^ (3 : Nat)) - 1) =
        BitVec.allOnes 64 := rfl
    change value = value &&& BitVec.ofNat 64 (2 ^ (8 * 2 ^ (3 : Nat)) - 1)
    rw [mask, BitVec.and_allOnes]

theorem bigEndian_involutive :
    ∀ width : Fin 4, ∀ value : Word, ∃ first second,
      Returns sourceBody [1, BitVec.ofNat 64 width.val, value] first ∧
      Returns sourceBody [1, BitVec.ofNat 64 width.val, first] second ∧
      second = value &&& BitVec.ofNat 64 (2 ^ (8 * 2 ^ width.val) - 1) := by
  refine fin4_cases ?_ ?_ ?_ ?_
  · intro value
    exact ⟨_, _, (be8 value).2,
      (be8 (swap8 value)).2, swap8_involutive value⟩
  · intro value
    exact ⟨_, _, (be16 value).2,
      (be16 (swap16 value)).2, swap16_involutive value⟩
  · intro value
    exact ⟨_, _, (be32 value).2,
      (be32 (swap32 value)).2, swap32_involutive value⟩
  · intro value
    refine ⟨_, _, (be64 value).2,
      (be64 (swap64 value)).2, ?_⟩
    have mask : BitVec.ofNat 64 (2 ^ (8 * 2 ^ (3 : Nat)) - 1) =
        BitVec.allOnes 64 := rfl
    change swap64 (swap64 value) =
      value &&& BitVec.ofNat 64 (2 ^ (8 * 2 ^ (3 : Nat)) - 1)
    rw [mask, BitVec.and_allOnes]
    exact swap64_involutive value

end ProductionClaims
