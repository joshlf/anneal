import Trusted.Refinement
import Trusted.CoInd
import Trusted.Effect
import Trusted.ITree
import Trusted.Sequence
import Trusted.Layout
import Trusted.MirAst
import Trusted.MirSemantics
import Trusted.VerificationResult

namespace Trusted

/-!
Trusted semantic foundation umbrella module for Anneal (`#88`, `#100`, `#102`,
`#103`).

Every module imported here is audited and kernel-replayed by
`trusted/audit/check_trusted.py`. Only semantic definitions and root
`VerificationResult` claim types live in `trusted/lean/`; all proof calculi,
bisimulations, simulations, predicate transformers, and domain lemmas live in
`theory/Anneal/`.
-/

end Trusted
