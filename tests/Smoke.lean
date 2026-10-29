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

/-- Captured `MirBody` for
    `pub fn load_relaxed(a: &AtomicUsize) -> usize { a.load(Ordering::Relaxed) }`
    defined using only `Trusted.*` constructors (`ci.type` origin-clean). -/
def loadRelaxedBody : Trusted.MirBody where
  argTys := [.refAtomicUsize]
  retTy := .usize
  localCount := 3
  blocks := [
    { stmts := [.assign ⟨2⟩ (.use (.constVal (.ordering .relaxed)))]
      terminator := .callAtomicLoad ⟨0⟩ (.copy ⟨1⟩) (.move ⟨2⟩) ⟨1⟩ },
    { stmts := []
      terminator := .return_ }
  ]

/-- Captured `Trusted.Crate` for `load_relaxed` with weak-memory postcondition
    `Trusted.EnsuresAtomicLoad 1`. -/
def loadRelaxedCrate : Trusted.Crate where
  functions := [
    { name := "load_relaxed"
      prog := loadRelaxedBody
      specs := [Trusted.EnsuresAtomicLoad 1] }
  ]
  tcb := [Trusted.TCBItem.rustcLowering "load_relaxed" loadRelaxedBody]

/-- Top-level `Trusted.CrateTheorem` for `loadRelaxedCrate`, whose statement
    (`ci.type`) references only `Trusted` and locked foundation constants while
    its proof term (`ci.value?`) discharges the obligation via
    `Anneal.prove_load_relaxed_ensures_crate` in `theory/`. -/
theorem verify_load_relaxed_crate : Trusted.CrateTheorem loadRelaxedCrate :=
  Anneal.prove_load_relaxed_ensures_crate "load_relaxed"

end AnnealTests
