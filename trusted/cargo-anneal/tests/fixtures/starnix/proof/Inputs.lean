-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Endianness

namespace Endianness

/-- Four concrete proofs cover every logical width index. -/
theorem fin4_cases {p : Fin 4 → Prop}
    (h0 : p 0) (h1 : p 1) (h2 : p 2) (h3 : p 3) : ∀ w, p w :=
  Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (Fin.cases h3 (fun i => Fin.elim0 i))))

/-- A valid enum index can be recovered without changing its stored word. -/
theorem fin_encode_decode (x : BitVec 64) {n : Nat} (h : x.toNat < n) :
    BitVec.ofNat 64 (⟨x.toNat, h⟩ : Fin n).val = x := by
  simp

end Endianness
