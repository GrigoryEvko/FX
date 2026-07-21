import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Differential.CartesianDifferential

/-! # Cartesian differential category polynomial model: zero-axiom gate

Per-declaration zero-axiom gate for the cartesian differential category polynomial model
over `QnfRat`: the rational coercion, the structural exponent decrement, the formal partial
derivative with canonical well-definedness, the directional derivative, the equality
decision with soundness, the coefficient lemmas for CD.1 additivity, the CD.3 constant and
projection rules, the CD.4 pairing rule, the CD.6 vector-additivity, the ground examples,
and the capability markers.

Every declaration must be free of propext, Quot.sound, Classical.choice, sorry,
native_decide, funext, WellFounded.fix, omega. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.cdfQnfOfNat
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfExpDecrement
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfTermPartialDeriv
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfPartialDeriv
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfTermPartialDerivKeepsCanonical
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfPartialDerivKeepsCanonical
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfDirectionalAux
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfDirectionalDeriv
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfDecidePolyEqBool
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfDecidePolyEqSound
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfTermDerivCoeffFormula
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfTermDerivCoeff
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfTermDerivCoeffZeroCoeff
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfTermDerivCoeffAddCoeff
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfDerivCoeffCons
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfDerivCoeffTermInsert
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfDerivCoeffAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfPartialDerivAdditive
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfTermPartialDerivAbsent
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfDerivConstant
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfDerivVariableOther
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfConcat
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfMapPartialDeriv
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfMapDerivConcat
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfVecAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfVecLookupAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfDirectionalAddVector
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfXSquared
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfTwoX
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfExampleDerivXSquared
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfExampleDerivConstant
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfExampleDerivVariableSame
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfExampleDecideEqualTrue
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfExampleDecideDifferentFalse
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfExampleDirectionalXSquared
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfExampleSecondDerivSymmetric
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfHasPolynomialCdcModel
#assert_no_axioms FX1Poly.ComputerAlgebra.cdfHasFreeCdcCompleteness

end FX1PolyAudit
