-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.NotationExtra
import Init.Data.List.Basic
import Anneal.AiPcc.BitArith
import Anneal.AiPcc.Tnum
import Anneal.AiPcc.WrappedInterval
import Anneal.AiPcc.ReducedProduct

namespace Anneal.AiPcc

/-!
# Domain Canaries for AI-PCC Reduced Product (`Anneal.AiPcc.Canaries`)

Decoupled Pass-1 canary suite exercising the MIR-agnostic `Anneal.AiPcc` domain
modules (`BitArith`, `Tnum`, `WrappedInterval`, and `ReducedProduct`). The
candidate-TCB `MirBridge` / `MirTransfer` / `MirPcc` modules and end-to-end MIR
canaries from `google/zerocopy#4089` are deferred until `Trusted.MirSemantics` /
`Anneal.MirWp` alignment.
-/

/-- Certified loop-header abstract value for `_1`: `0 ≤ _1 ≤ 1024` and low 3
bits known zero (`_1 ≡ 0 (mod 8)`). -/
def stride8HeaderIdxAbs : AbsVal :=
  reduceAbsVal 64
    { init := .init
      tnum := ⟨0, 2040⟩  -- bits 3..10 unknown (0x7F8 = 2040), bits 0..2 = 0
      wi := .iv 0 1024
      sc := .cong 8 0 }

/-- Direct positive and fail-closed unit checks for standalone reduced-product
domain helpers (`InitDom.meet`, `AbsVal.isAligned8`,
`AbsVal.noOverflowAddConst`, `AbsVal.addConstWrap`, and
`AbsVal.subConstWrap`). -/
theorem canary_domain_helpers_tests :
    InitDom.meet .uninit .init = .init ∧
    InitDom.meet .init .bot = .bot ∧
    stride8HeaderIdxAbs.isAligned8 = true ∧
    (AbsVal.const 64 12).isAligned8 = false ∧
    stride8HeaderIdxAbs.noOverflowAddConst 64 8 = true ∧
    (AbsVal.topInit 8).noOverflowAddConst 8 1 = false ∧
    (AbsVal.addConstWrap 8 (AbsVal.const 8 250) 10).exactVal? 8 = some 4 ∧
    (AbsVal.subConstWrap 8 (AbsVal.const 8 4) 10).exactVal? 8 = some 250 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.AiPcc
