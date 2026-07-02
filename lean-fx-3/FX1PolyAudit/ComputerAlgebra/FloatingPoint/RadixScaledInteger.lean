import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.FloatingPoint.RadixScaledInteger

/-! # FX1PolyAudit/ComputerAlgebra/FloatingPoint/RadixScaledInteger — zero-axiom gate
    (FLOAT-2 brick 2)

Per-declaration zero-axiom gate for the RadixScaledInteger carrier: the Int
cancellation helpers, the cross-alignment relation with its decidability and refl/symm
laws, exact multiplication, and the rescaling-preserves-denotation theorem.  (The
`toNat` pins moved to the `Number/IntToNatCycle` gate with their declarations.)

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.intAddNegSwapCancel
#assert_no_axioms FX1Poly.ComputerAlgebra.intSubSubSelfCancel
#assert_no_axioms FX1Poly.ComputerAlgebra.RadixScaledInteger.scaleGapToward
#assert_no_axioms FX1Poly.ComputerAlgebra.RadixScaledInteger.crossAlignedMantissa
#assert_no_axioms FX1Poly.ComputerAlgebra.RadixScaledInteger.DenotesSameAs
#assert_no_axioms FX1Poly.ComputerAlgebra.RadixScaledInteger.decideDenotesSameAs
#assert_no_axioms FX1Poly.ComputerAlgebra.RadixScaledInteger.denotesSameAsRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.RadixScaledInteger.denotesSameAsSymm
#assert_no_axioms FX1Poly.ComputerAlgebra.RadixScaledInteger.denotesSameAsTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.RadixScaledInteger.agreesAtLowerScaleOfDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.RadixScaledInteger.denotesSameAsOfAgreesAtLowerScale
#assert_no_axioms FX1Poly.ComputerAlgebra.RadixScaledInteger.mulExact
#assert_no_axioms FX1Poly.ComputerAlgebra.RadixScaledInteger.mulExactMantissa
#assert_no_axioms FX1Poly.ComputerAlgebra.RadixScaledInteger.mulExactExponent
#assert_no_axioms FX1Poly.ComputerAlgebra.RadixScaledInteger.mulExactRespectsDenotesSameAs
#assert_no_axioms FX1Poly.ComputerAlgebra.RadixScaledInteger.shiftToLowerScale
#assert_no_axioms FX1Poly.ComputerAlgebra.RadixScaledInteger.shiftToLowerScalePreservesDenotation
#assert_no_axioms FX1Poly.ComputerAlgebra.RadixScaledInteger.addExact
#assert_no_axioms FX1Poly.ComputerAlgebra.RadixScaledInteger.addExactMantissa
#assert_no_axioms FX1Poly.ComputerAlgebra.RadixScaledInteger.addExactExponent
#assert_no_axioms FX1Poly.ComputerAlgebra.RadixScaledInteger.addExactComm
#assert_no_axioms FX1Poly.ComputerAlgebra.RadixScaledInteger.addExactZeroDenotesSame

end FX1PolyAudit
