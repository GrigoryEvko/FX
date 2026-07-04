import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Computad.PathFactorization

/-! # FX1PolyAudit/Polygraph/Computad/PathFactorization — zero-axiom gate

Per-declaration zero-axiom gate for the self-certifying 1-cell prefix splitter.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.ModalityPath.splitPrefix

end FX1PolyAudit
