import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialLeadingTermCancel

/-! # FX1PolyAudit/.../IntPolynomialLeadingTermCancel — zero-axiom gate

Per-declaration zero-axiom gate for the pseudo-division leading-term cancellation (the seventh brick of
`invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255): the pseudo-division step's replacement dividend has
coefficient `0` at the old top degree when `polyDegree divisor ≤ polyDegree dividend`.

A `rw` chain over the coefficient homomorphisms, the degree↔coefficient bridge, the propext-clean
`natAddSubOfLe`, and the corpus `Int` ring lemmas.  Must be free of `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoStepTopCoeffCancels
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoStepTopCoeffCancelsGrounding
#assert_no_axioms FX1Poly.ComputerAlgebra.fxIntPoly_hasPseudoStepLeadingTermCancellation

end FX1PolyAudit
