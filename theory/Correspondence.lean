import Correspondence.Framework
import Correspondence.DialectInterface
import Correspondence.GeneratedGaps
import Correspondence.GeneratedGapWitnesses
import Correspondence.V2026_06_01.L1_Scalars
import Correspondence.V2026_06_01.L2_BytesAndLayout
import Correspondence.V2026_06_01.L3_PlacesAndBasicMem
import Correspondence.V2026_06_01.L4_TreeBorrows
import Correspondence.V2026_06_01.L5_ControlAndCalls
import Correspondence.V2026_06_01.L6_WholeMachine
import Correspondence.V2026_06_01.Scorecard
import Correspondence.V2026_08_01.L1_Scalars
import Correspondence.V2026_08_01.L2_BytesAndLayout
import Correspondence.V2026_08_01.L3_PlacesAndBasicMem
import Correspondence.V2026_08_01.L4_TreeBorrows
import Correspondence.V2026_08_01.L5_ControlAndCalls
import Correspondence.V2026_08_01.L6_WholeMachine
import Correspondence.V2026_08_01.Scorecard

/-!
# `Correspondence` — Root Entry Point for Anneal ↔ MiniRust Formal Correspondence

Imports all framework modules, multi-version dialect interfaces, kernel-checked
non-correspondence gap guards & divergence witnesses, universal horizontal slices
`L1`–`L6` across `V2026_06_01` and `V2026_08_01`, and the top-level `Scorecard`
rollup theorems.
-/

namespace Correspondence

export Correspondence.V2026_06_01.Scorecard (
  CorrespondenceScorecard
  all_correspondence_slices_verified
)

export Correspondence.V2026_08_01.Scorecard (
  V2026_08_01_Scorecard
  v2026_08_01_s2026_07_all_layers_exact_unconditional
  v2026_08_01_s2026_05_epoch_delta_only
  v2026_08_01_correspondence_scorecard
)

end Correspondence
