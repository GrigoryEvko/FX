import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.ComplexPolynomialGrowthBound

/-! # FX1PolyAudit/ComputerAlgebra/Number/ComplexPolynomialGrowthBound — zero-axiom
    gate

Per-declaration zero-axiom gate for the complex polynomial growth bound
`|p(z)| ≤ Σ|cᵢ||z|ⁱ` (Horner form): modulus nonnegativity
(`modulusIsNonNegativeReal`), the zero-modulus collapse
(`modulusZeroComplexDenotesZero`), the Horner bound definition
(`hornerModulusBound`), the growth bound (`modulusEvalLeHornerBound`), and the
content marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.modulusIsNonNegativeReal
#assert_no_axioms FX1Poly.ComputerAlgebra.modulusZeroComplexDenotesZero
#assert_no_axioms FX1Poly.ComputerAlgebra.hornerModulusBound
#assert_no_axioms FX1Poly.ComputerAlgebra.modulusEvalLeHornerBound
#assert_no_axioms FX1Poly.ComputerAlgebra.fxComplexReal_hasPolynomialGrowthBound

end FX1PolyAudit
