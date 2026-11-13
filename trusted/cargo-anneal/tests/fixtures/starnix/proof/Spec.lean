-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted.Mvp
import Endianness

namespace Spec

open Trusted.Mvp Endianness

/-- The selected function returns the reversed bytes within its chosen width. -/
def exactReversal (body : Body) : Prop :=
  ∀ width : Fin 4, ∀ value : Word, ∃ output,
    Safe body [1, BitVec.ofNat 64 width.val, value] ∧
    Returns body [1, BitVec.ofNat 64 width.val, value] output ∧
    ByteReversal (8 * 2 ^ width.val) value output

/-- Little-endian conversion on this target keeps exactly the chosen width. -/
def exactLittleEndian (body : Body) : Prop :=
  ∀ width : Fin 4, ∀ value : Word, ∃ output,
    Safe body [0, BitVec.ofNat 64 width.val, value] ∧
    Returns body [0, BitVec.ofNat 64 width.val, value] output ∧
    output = value &&& BitVec.ofNat 64 (2 ^ (8 * 2 ^ width.val) - 1)

/-- Two completed big-endian conversions recover the masked input. -/
def involution (body : Body) : Prop :=
  ∀ width : Fin 4, ∀ value : Word, ∃ first second,
    Returns body [1, BitVec.ofNat 64 width.val, value] first ∧
    Returns body [1, BitVec.ofNat 64 width.val, first] second ∧
    second = value &&& BitVec.ofNat 64 (2 ^ (8 * 2 ^ width.val) - 1)

def specs : Specs :=
  { safety := fun _ _ => True
    property := fun program => ∃ body, program.bodies = [body] ∧
      exactReversal body ∧ exactLittleEndian body ∧ involution body }

end Spec
