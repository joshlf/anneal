-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Expected
import InitialCache

namespace ExecutionProof

open Trusted.MirModel Trusted.MirSemantics Anneal.MirWp Endianness
  ProductionReduction

/-!
A negative test may credit rejection of the fixed byte-reversal property only
after the same captured body is shown to return on every valid entry. This
proof reuses `InitialCache.sourceExec`, which states no expected return value
and binds the output to whatever the captured body actually returns.
-/

theorem completed :
    ∀ flag : Bool, ∀ width : Fin 4, ∀ value : Word,
      Safe sourceBody (endianArgs flag width.val value) ∧
      ∃ output, Returns sourceBody (endianArgs flag width.val value) output :=
  fun flag width value =>
    let ⟨output, h_exec⟩ := sourceExec flag width value
    ⟨executes_safe h_exec, output, executes_returns h_exec⟩

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro id body found
    cases id with
    | zero =>
      have same : sourceBody = body := Option.some.inj found
      subst body
      refine bodyVerified_of_safe found rfl (fun args valid _ => ?_)
      apply validArgs3_elim sourceBody _ rfl rfl
        (Safe sourceBody) _ args valid
      intro flag width value
      exact (completed flag width value).1
    | succ id => cases found
  · refine ⟨sourceBody, rfl, ?_⟩
    apply validArgs3_elim sourceBody _ rfl rfl
      (fun args => ∃ output,
        Behavior (entryProgForBody sourceProgram 0) { args := args }
          (.returned ⟨output, ⟨[]⟩⟩))
    intro flag width value
    let ⟨output, h_ret⟩ := (completed flag width value).2
    exact ⟨output, behavior_of_returns rfl rfl
      (validEntryArgs_bodyEndianArgs sourceBody _ rfl rfl rfl flag width value)
      h_ret⟩

end ExecutionProof
