import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.ComplexRealModulusComponentBounds

/-! # FX1PolyAudit/ComputerAlgebra/Number/ComplexRealModulusComponentBounds — zero-axiom
    gate (NUM-C-5 modulus component bounds)

Per-declaration zero-axiom gate for the ℂ modulus component estimates: the
self-plus-nonnegative real order brick, the four component dominations
(`±Re z ≤ |z|`, `±Im z ≤ |z|`), and the abs-sum upper bound `|z| ≤ |Re z| + |Im z|`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.lessEqualRealSelfAddNonNegRight
#assert_no_axioms FX1Poly.ComputerAlgebra.modulusDominatesRealPart
#assert_no_axioms FX1Poly.ComputerAlgebra.negRealPartLeModulus
#assert_no_axioms FX1Poly.ComputerAlgebra.modulusDominatesImaginaryPart
#assert_no_axioms FX1Poly.ComputerAlgebra.negImaginaryPartLeModulus
#assert_no_axioms FX1Poly.ComputerAlgebra.modulusLeComponentAbsSum
#assert_no_axioms FX1Poly.ComputerAlgebra.fxComplexReal_hasModulusComponentBounds

end FX1PolyAudit
