import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.SteinerFoundation.AugmentedDirectedComplex

/-! # FX1PolyAudit/Polygraph/Steiner/AugmentedDirectedComplex — zero-axiom gate

Per-declaration zero-axiom gate for the finite-basis augmented directed complex carrier: the row
dot product, the finite index sum, the ADC structure (with its `d d = 0` / `eps d = 0`
obligations), the matrix-vector `applyBoundary`, and the positive-cone predicate.  First gate of
the `Polygraph/Steiner/` layer (Init + ComputerAlgebra only, by the dependency-spine rule).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Steiner.dotProduct
#assert_no_axioms FX1Poly.Polygraph.Steiner.sumOverIndices
#assert_no_axioms FX1Poly.Polygraph.Steiner.AugmentedDirectedComplex
#assert_no_axioms FX1Poly.Polygraph.Steiner.dotEachRowWithVector
#assert_no_axioms FX1Poly.Polygraph.Steiner.AugmentedDirectedComplex.applyBoundary
#assert_no_axioms FX1Poly.Polygraph.Steiner.IsInPositiveCone

end FX1PolyAudit
