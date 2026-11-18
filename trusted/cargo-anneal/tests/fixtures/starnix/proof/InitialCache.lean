-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Captured
import SourceInputs

namespace ProductionReduction

open Trusted.MirModel Trusted.MirSemantics Anneal.MirWp Endianness

noncomputable abbrev sourceProgram : Program :=
  interpretV2026_10_22_R7189d39d9 Captured.program

noncomputable abbrev sourceBody : Body := sourceProgram.bodies[0]'(by decide)

noncomputable abbrev dataWidthVal (width : Nat) : Val :=
  bodyDataWidthVal sourceBody width

noncomputable abbrev endianArgs (toBe : Bool) (width : Nat) (value : Word) : List Val :=
  bodyEndianArgs sourceBody toBe width value

/-- Execute `sourceBody` symbolically along each `(toBe, width)` path and
bundle the resulting `Val` with its `Executes` certificate. Keeping this
execution witness free of the byte-reversal specification lets both
`ProductionClaims` (which equates `(sourceExec ...).1` with `sourceOutput`) and
`ExecutionProof` (which proves safe termination on mutated captures without
prescribing return values) share one symbolic-execution proof with zero
duplicated tactics. -/
noncomputable def sourceExec (toBe : Bool) (width : Fin 4) (value : Word) :
    { output : Val //
      Executes sourceBody
        (initial sourceBody (endianArgs toBe width.val value)) output } := by
  revert width value
  cases toBe <;> apply fin4_elim <;> intro value <;> apply Subtype.mk <;>
  · unfold initial
    apply executes_of_blockExec
    eq_refl; eq_refl; eq_refl; eq_refl
    repeat (first
      | (apply blockExec_nop)
      | (apply blockExec_storageLive; eq_refl; eq_refl; eq_refl)
      | (apply blockExec_storageDead; eq_refl; eq_refl)
      | (apply blockExec_assignU64 (rv := .binaryOp .bitAnd _ _)
         eq_refl; eq_refl; apply u64BitAndVal_eq; eq_refl; eq_refl)
      | (apply blockExec_assignU64 (rv := .binaryOp .bitOr _ _)
         eq_refl; eq_refl; apply u64BitOrVal_eq; eq_refl; eq_refl)
      | (apply blockExec_assignU64 (rv := .binaryOp .shl _ _)
         eq_refl; eq_refl; apply u64ShlVal_eq; eq_refl; eq_refl)
      | (apply blockExec_assignU64 (rv := .binaryOp .shr _ _)
         eq_refl; eq_refl; apply u64ShrVal_eq; eq_refl; eq_refl)
      | (apply blockExec_assignU64 (rv := .use (.copy _))
         eq_refl; eq_refl; eq_refl; eq_refl; eq_refl)
      | (apply blockExec_assignU64 (rv := .use (.move _))
         eq_refl; eq_refl; eq_refl; eq_refl; eq_refl)
      | (apply blockExec_cons; eq_refl)
      | (apply blockExec_nil_goto; eq_refl; eq_refl; eq_refl)
      | (apply blockExec_nil_step; eq_refl; eq_refl; eq_refl)
      | (apply blockExec_nil_ret; eq_refl))

end ProductionReduction
