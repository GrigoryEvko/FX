import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Float.Arithmetic

/-! # FX1PolyAudit/ComputerAlgebra/Float/Arithmetic — zero-axiom gate (FLOAT-1b)

Per-declaration zero-axiom gate for the exact-then-round total float operations
(add/sub/mul) and their half-ulp correctness brackets.  Every declaration must
be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.negateExact
#assert_no_axioms FX1Poly.ComputerAlgebra.negateExactMantissa
#assert_no_axioms FX1Poly.ComputerAlgebra.negateExactExponent
#assert_no_axioms FX1Poly.ComputerAlgebra.addRounded
#assert_no_axioms FX1Poly.ComputerAlgebra.subRounded
#assert_no_axioms FX1Poly.ComputerAlgebra.mulRounded
#assert_no_axioms FX1Poly.ComputerAlgebra.toRadixScaled_addRounded
#assert_no_axioms FX1Poly.ComputerAlgebra.toRadixScaled_subRounded
#assert_no_axioms FX1Poly.ComputerAlgebra.toRadixScaled_mulRounded
#assert_no_axioms FX1Poly.ComputerAlgebra.addRoundedErrorBoundBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.addRoundedErrorBoundAbove
#assert_no_axioms FX1Poly.ComputerAlgebra.mulRoundedErrorBoundBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.mulRoundedErrorBoundAbove

end FX1PolyAudit
