prelude
import Anneal

namespace AnnealTests

/-- Captured `MirBody` for `pub fn id(x: usize) -> usize { x }` defined using
    only `Trusted.*` constructors (`ci.type` origin-clean). -/
def idBody : Trusted.MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := [.assign ⟨0⟩ (.use (.copy ⟨1⟩))]
      terminator := .return_ }
  ]

/-- Captured `Trusted.Crate` for `pub fn id(x: usize) -> usize { x }` with
    postcondition `Trusted.EnsuresEqArg 1` (`ret == x`). -/
def idCrate : Trusted.Crate where
  functions := [
    { name := "id"
      prog := idBody
      specs := [Trusted.EnsuresEqArg 1] }
  ]
  tcb := [Trusted.TCBItem.rustcLowering "id" idBody]

/-- Top-level `Trusted.CrateTheorem` for `idCrate`, whose statement (`ci.type`)
    references only `Trusted` and locked foundation constants while its proof
    term (`ci.value?`) discharges the obligation via
    `Anneal.prove_id_copy_ensures_crate` in `theory/`. -/
theorem verify_id_crate : Trusted.CrateTheorem idCrate :=
  Anneal.prove_id_copy_ensures_crate "id"

end AnnealTests
