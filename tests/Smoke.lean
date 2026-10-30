import Anneal

namespace AnnealTests

/-- A claim theorem whose statement (`ci.type`) references only standard library /
`Trusted` constants (`True`), while its proof term (`ci.value?`) uses the
untrusted `Anneal.trivial_witness` lemma from `theory/`. -/
theorem smoke_claim : True := Anneal.trivial_witness

end AnnealTests
