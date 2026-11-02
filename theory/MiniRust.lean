import MiniRust.LibSpecr
import MiniRust.Snapshots.S2026_05_Matched.Generated.SpecIndex
import MiniRust.Snapshots.S2026_05_Matched.Generated.Ops
import MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.SpecIndex
import MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops

/-!
# `MiniRust` — Top-Level Entry Point for Mechanized MiniRust Specifications

Re-exports the `MiniRust.LibSpecr` runtime library (`SpecrInt`, `Align`, `Size`,
`Offset`, `Endianness`, `GcCow`, `SpecrMap`, `SpecrSet`, `TerminationInfo`,
`NdComp`, `NdResult`, `evalDet`, and the `Trusted.Refinement.Partial` bridge
theorems) and imports all mechanically generated upstream MiniRust snapshots
(`S2026_05_Matched` and `S2026_07_BleedingEdge`).
-/

namespace MiniRust

export MiniRust.LibSpecr (
  SpecrInt
  Align
  Size
  Offset
  Endianness
  GcCow
  SpecrList
  SpecrMap
  SpecrSet
  TerminationInfo
  SpecrResult
  NdComp
  NdResult
)

end MiniRust
