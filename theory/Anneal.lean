import Trusted

namespace Anneal

/-- Placeholder proof helper in the untrusted `Anneal` library. Theorems in
`tests/` or crate `Proof/` modules may reference `Anneal` declarations inside
their proof terms (`ci.value?`), never in their theorem statements (`ci.type`). -/
theorem trivial_witness : True := True.intro

end Anneal
