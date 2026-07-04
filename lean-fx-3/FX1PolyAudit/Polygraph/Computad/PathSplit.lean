import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Computad.PathSplit

/-! # FX1PolyAudit/Polygraph/Computad/PathSplit — zero-axiom gate

Per-declaration zero-axiom gate for the path splitting kit: the split certificate, the
split constructor, and the length partition.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.PathSplit
#assert_no_axioms FX1Poly.Polygraph.splitPathAt
#assert_no_axioms FX1Poly.Polygraph.PathSplit.lengthPartition

end FX1PolyAudit
