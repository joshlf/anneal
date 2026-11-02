import Correspondence.Framework
import Correspondence.DialectInterface
import Correspondence.GeneratedGaps
import Correspondence.GeneratedGapWitnesses
import Correspondence.V2026_06_01.L1_Scalars
import Correspondence.V2026_06_01.L2_BytesAndLayout
import Correspondence.V2026_06_01.L3_PlacesAndBasicMem
import Correspondence.V2026_06_01.L4_TreeBorrows
import Correspondence.V2026_06_01.Scorecard

/-!
# `Correspondence` — Root Entry Point for Anneal ↔ MiniRust Formal Correspondence

Imports all framework modules, multi-version dialect interfaces, kernel-checked
non-correspondence gap guards & divergence witnesses, universal horizontal slices
`L1`–`L4`, and the top-level `Scorecard` rollup theorem.
-/

namespace Correspondence

export Correspondence.V2026_06_01.Scorecard (
  CorrespondenceScorecard
  all_correspondence_slices_verified
)

end Correspondence
