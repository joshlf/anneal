-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Anneal.Mvp.Execution
import Inputs

namespace Endianness

open Trusted.Mvp Anneal.Mvp

/-- Valid source entries have exactly the finite flag and width cases. -/
theorem validArgs3_elim (body : Body) (enumId : Nat)
    (count : body.argCount = 3)
    (flagTy : body.localTys[1]? = some .bool)
    (widthTy : body.localTys[2]? = some (.enum enumId [0, 1, 2, 3]))
    (p : List Word → Prop)
    (inputs : ∀ flag : Fin 2, ∀ width : Fin 4, ∀ value : Word,
      p [BitVec.ofNat 64 flag.val, BitVec.ofNat 64 width.val, value]) :
    ∀ args, argsValid body args → p args := by
  intro args valid
  have length : args.length = 3 := valid.1.trans count
  have b0 : 0 < args.length := length ▸ by decide
  have b1 : 1 < args.length := length ▸ by decide
  have b2 : 2 < args.length := length ▸ by decide
  have flagValid := valid.2 0 args[0] (by simp [b0])
  have widthValid := valid.2 1 args[1] (by simp [b1])
  cases flagValid with
  | intro ty h =>
    have eqTy : ty = .bool := Option.some.inj (h.1.symm.trans flagTy)
    have flagBound : args[0].toNat < 2 := by
      simpa [eqTy, validValue, Ty.admitted] using h.2
    cases widthValid with
    | intro ty' h' =>
      have eqTy' : ty' = .enum enumId [0, 1, 2, 3] :=
        Option.some.inj (h'.1.symm.trans widthTy)
      have widthBound : args[1].toNat < 4 := by
        simpa [eqTy', validValue, Ty.admitted] using h'.2
      have result := inputs ⟨args[0].toNat, flagBound⟩
        ⟨args[1].toNat, widthBound⟩ args[2]
      simp only [BitVec.ofNat_toNat] at result
      exact Eq.mpr (congrArg p (List.eq_getElem_of_length_eq_three args length))
        result

/-- Finite source executions cover baseline safety for all valid entries. -/
theorem bodyVerified_of_finite_runs (body : Body) (enumId : Nat)
    (wellFormed : bodyWF body = true)
    (count : body.argCount = 3)
    (flagTy : body.localTys[1]? = some .bool)
    (widthTy : body.localTys[2]? = some (.enum enumId [0, 1, 2, 3]))
    (completed : ∀ flag : Fin 2, ∀ width : Fin 4, ∀ value : Word,
      ∃ fuel output, run body fuel (initial body
        [BitVec.ofNat 64 flag.val, BitVec.ofNat 64 width.val, value]) =
          some output)
    (safetyPre : List Word → Prop) : BodyVerified body safetyPre := by
  constructor
  · exact wellFormed
  · intro args valid _
    apply validArgs3_elim body enumId count flagTy widthTy (Safe body) _ args valid
    intro flag width value
    cases completed flag width value with
    | intro fuel h =>
      cases h with
      | intro output success =>
        exact (Anneal.Mvp.run_initial_success success).1

end Endianness
