-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Expected
import ProductionSteps

namespace ExecutionProof

open Trusted.Mvp Endianness ProductionReduction ProductionSteps

/-!
All generated paths must prove real source executions before a negative test
can credit rejection of the fixed byte-reversal property. This proof uses the
same generated witness module as that later check, with no expected endpoints.
-/

theorem completed :
    ∀ flag : Fin 2, ∀ width : Fin 4, ∀ value : Word,
      Safe sourceBody
        [BitVec.ofNat 64 flag.val, BitVec.ofNat 64 width.val, value] ∧
      ∃ output, Returns sourceBody
        [BitVec.ofNat 64 flag.val, BitVec.ofNat 64 width.val, value] output := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))
  · exact fin4_cases
      (fun v => ⟨(le8_actual v).1, _, (le8_actual v).2⟩)
      (fun v => ⟨(le16_actual v).1, _, (le16_actual v).2⟩)
      (fun v => ⟨(le32_actual v).1, _, (le32_actual v).2⟩)
      (fun v => ⟨(le64_actual v).1, _, (le64_actual v).2⟩)
  · exact fin4_cases
      (fun v => ⟨(be8_actual v).1, _, (be8_actual v).2⟩)
      (fun v => ⟨(be16_actual v).1, _, (be16_actual v).2⟩)
      (fun v => ⟨(be32_actual v).1, _, (be32_actual v).2⟩)
      (fun v => ⟨(be64_actual v).1, _, (be64_actual v).2⟩)

theorem verify : Expected.claim := by
  constructor
  · rfl
  · constructor
    · intro id body found
      change ([sourceBody] : List Body)[id]? = some body at found
      cases id with
      | zero =>
        have same : sourceBody = body := Option.some.inj found
        subst body
        constructor
        · decide
        · intro args valid _
          apply validArgs3_elim sourceBody 1363 rfl rfl rfl
            (Safe sourceBody) _ args valid
          intro flag width value
          exact (completed flag width value).1
      | succ id => simp at found
    · refine ⟨sourceBody, rfl, ?_⟩
      apply validArgs3_elim sourceBody 1363 rfl rfl rfl
        (fun args => ∃ output, Returns sourceBody args output)
      intro flag width value
      exact (completed flag width value).2

end ExecutionProof
