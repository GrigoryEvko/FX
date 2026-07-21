import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialLeadingTermCancel

/-! # FX1PolyAudit/.../IntPolynomialLeadingTermCancel — zero-axiom gate

Per-declaration zero-axiom gate for the pseudo-division leading-term cancellation: the step's replacement
dividend has coefficient `0` at the old top degree when `polyDegree divisor ≤ polyDegree dividend`.  A `rw`
chain over the coefficient homomorphisms, the degree↔coefficient bridge, `natAddSubOfLe`, and the corpus
`Int` ring lemmas.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoStepTopCoeffCancels
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoStepTopCoeffCancelsGrounding

end FX1PolyAudit
