import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.ComplexRealField

/-! # FX1PolyAudit/ComputerAlgebra/Number/ComplexRealField — zero-axiom gate

Per-declaration zero-axiom gate for the ℂ apartness-first Heyting field: the
apartness predicate and its congruence, the complex inverse, the Heyting-field
law (both sides), the `HeytingFieldWitness` structure, and the ℝ and ℂ
instances.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.IsApartFromZeroComplex
#assert_no_axioms FX1Poly.ComputerAlgebra.modulusSquaredRespectsDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.isApartFromZeroComplexRespectsDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.realPositivityWitnessAddNonNegRight
#assert_no_axioms FX1Poly.ComputerAlgebra.realPositivityWitnessOfSquareApart
#assert_no_axioms FX1Poly.ComputerAlgebra.isApartFromZeroComplexOfRealPartApart
#assert_no_axioms FX1Poly.ComputerAlgebra.isApartFromZeroComplexOfImagPartApart
#assert_no_axioms FX1Poly.ComputerAlgebra.inverseComplex
#assert_no_axioms FX1Poly.ComputerAlgebra.mulComplexInverseComplexDenotesOne
#assert_no_axioms FX1Poly.ComputerAlgebra.mulComplexInverseComplexLeftDenotesOne
#assert_no_axioms FX1Poly.ComputerAlgebra.HeytingFieldWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.regularRealHeytingFieldWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.complexHeytingFieldWitness

end FX1PolyAudit
