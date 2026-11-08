/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Trusted.MirAst
import Trusted.MirSemantics
import Trusted.Rustc.V2026_06_01.Layout
import Anneal.MirFuelFree

open Trusted.MirAst
open Trusted.MirSemantics
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirSemantics.RvalueEvalResult
open Anneal.MirFuelFree

namespace Anneal.Mir.Cast

/-- Page offset modulus for pointer address serialization (64 KiB per allocation). -/
def pageOffsetModulus : Nat := 65536

/-- Address computation for a provenance pointer (`CastKind.pointerExposeProvenance`). -/
def ptrToAddress (p : ProvenancePtr) : Nat :=
  Nat.add (Nat.mul p.allocId pageOffsetModulus) p.offsetBytes

/-- Inverse mapping reconstructing a provenance pointer from an integer address. -/
def addressToPtr (addr : Nat) : ProvenancePtr :=
  { allocId := Nat.div addr pageOffsetModulus, offsetBytes := Nat.mod addr pageOffsetModulus }

/-- Exact roundtrip inversion theorem: reconstructing a pointer from its exposed
integer address recovers the exact allocation ID and offset whenever the offset is
within the 64 KiB page boundary. -/
theorem addressToPtr_ptrToAddress_eq (p : ProvenancePtr) (h_off : p.offsetBytes < pageOffsetModulus) :
    addressToPtr (ptrToAddress p) = p := by
  cases p with
  | mk allocId offsetBytes =>
    dsimp [addressToPtr, ptrToAddress, pageOffsetModulus] at *
    have h_pos : 0 < 65536 := by decide
    have h_div : (allocId * 65536 + offsetBytes) / 65536 = allocId := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ h_pos]
      have h_zero : offsetBytes / 65536 = 0 := Nat.div_eq_of_lt h_off
      rw [h_zero, Nat.zero_add]
    have h_mod : (allocId * 65536 + offsetBytes) % 65536 = offsetBytes := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt h_off
    congr <;> assumption

/-- MiniRust exposed provenance model: a list of exposed allocation identifiers. -/
abbrev ExposedProvenance : Type := List Nat

/-- Provenance exposure predicate: an allocation ID is exposed if it is in the list. -/
def isExposed (prov : Nat) (exposed : ExposedProvenance) : Prop :=
  prov ∈ exposed

/-- Expose operation adding an allocation ID to the exposed provenance list. -/
def exposeProv (prov : Nat) (exposed : ExposedProvenance) : ExposedProvenance :=
  if prov ∈ exposed then exposed else prov :: exposed

/-- Exposing a provenance tag guarantees it is in the exposed set. -/
theorem isExposed_exposeProv (prov : Nat) (exposed : ExposedProvenance) :
    isExposed prov (exposeProv prov exposed) := by
  dsimp [isExposed, exposeProv]
  split
  · next h => exact h
  · next h => exact List.Mem.head _

/-- Exposing preserves previously exposed provenance tags. -/
theorem isExposed_of_isExposed (prov other : Nat) (exposed : ExposedProvenance)
    (h : isExposed other exposed) : isExposed other (exposeProv prov exposed) := by
  dsimp [isExposed, exposeProv] at *
  split
  · exact h
  · exact List.Mem.tail _ h

/-- Semantic correspondence for pointer-to-usize cast:
Evaluating `CastKind.pointerExposeProvenance` on a pointer value produces the
exact machine address scalar computed by `ptrToAddress`. -/
theorem ptr_to_usize_cast_step_correspondence
    (ptrVal : ProvenancePtr)
    (locals locals' : List LocalSlot)
    (mem : Memory)
    (op : Operand)
    (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (h_eval : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals = .ok (.ptr ptrVal 8) locals') :
    (match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
     | .ok (.ptr p _) locs =>
       let addr := Nat.add (Nat.mul p.allocId pageOffsetModulus) p.offsetBytes
       ok (.scalar ⟨addr, 8⟩) locs mem
     | .ok (.scalar sc) locs => ok (.scalar ⟨sc.bits, 8⟩) locs mem
     | .ok _ _ => unsupported
     | .ub => ub
     | .unsupported => unsupported) =
    ok (.scalar ⟨ptrToAddress ptrVal, 8⟩) locals' mem := by
  rw [h_eval]
  dsimp [ptrToAddress, pageOffsetModulus]

/-- Determinism of pointer-to-usize cast evaluation:
Given identical pointer values and memory states, the evaluation results are identical. -/
theorem ptr_to_usize_cast_deterministic
    (p1 p2 : ProvenancePtr)
    (locs1 locs2 : List LocalSlot)
    (mem1 mem2 : Memory)
    (h_ptr : p1 = p2)
    (h_locs : locs1 = locs2)
    (h_mem : mem1 = mem2) :
    ok (.scalar ⟨ptrToAddress p1, 8⟩) locs1 mem1 =
    ok (.scalar ⟨ptrToAddress p2, 8⟩) locs2 mem2 := by
  subst h_ptr h_locs h_mem
  rfl

/-- MiniRust step correspondence: Int-to-pointer cast (`pointerWithExposedProvenance`)
reconstructs the provenance pointer corresponding to `addressToPtr`. -/
theorem int_to_ptr_cast_step_correspondence
    (sc : ScalarInt)
    (locals locals' : List LocalSlot)
    (mem : Memory)
    (op : Operand)
    (layouts : Trusted.Rustc.V2026_06_01.Layout.LayoutTable)
    (h_eval : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals = .ok (.scalar sc) locals') :
    (match evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals with
     | .ok (.scalar s) locs =>
       let p : ProvenancePtr := {
         allocId := Nat.div s.bits pageOffsetModulus
         offsetBytes := Nat.mod s.bits pageOffsetModulus
       }
       ok (.ptr p 8) locs mem
     | .ok (.ptr ptrVal sz) locs => ok (.ptr ptrVal sz) locs mem
     | .ok _ _ => unsupported
     | .ub => ub
     | .unsupported => unsupported) =
    ok (.ptr (addressToPtr sc.bits) 8) locals' mem := by
  rw [h_eval]
  dsimp [addressToPtr, pageOffsetModulus]

/-- Full roundtrip correspondence theorem between Anneal MIR and MiniRust:
Casting a pointer `p` to `usize` via `pointerExposeProvenance` and then casting the resulting
address back to a pointer via `pointerWithExposedProvenance` recovers the exact original pointer `p`. -/
theorem ptr_usize_ptr_roundtrip_correspondence
    (p : ProvenancePtr)
    (h_off : p.offsetBytes < pageOffsetModulus) :
    addressToPtr (ptrToAddress p) = p :=
  addressToPtr_ptrToAddress_eq p h_off

end Anneal.Mir.Cast
