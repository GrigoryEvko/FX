import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Algebra.SetoidRingHom

/-! # FX1PolyAudit/ComputerAlgebra/Algebra/SetoidRingHom — zero-axiom gate
    (NUM-ALG-1)

Per-declaration zero-axiom gate for the arrow level over
`CommutativeRingWitness`: the homomorphism structure, the two carrier-generic
inverse-uniqueness engines, negation preservation, the pointwise hom setoid,
identity and composition, and the three category laws plus the composition
congruence.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidRingHom
#assert_no_axioms FX1Poly.ComputerAlgebra.inverseUniqueInCommutativeRing
#assert_no_axioms FX1Poly.ComputerAlgebra.additiveInverseUniqueInCommutativeRing
#assert_no_axioms FX1Poly.ComputerAlgebra.homPreservesNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.HomDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.homDenotesSameRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.homDenotesSameSymm
#assert_no_axioms FX1Poly.ComputerAlgebra.homDenotesSameTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.identityRingHom
#assert_no_axioms FX1Poly.ComputerAlgebra.composeRingHom
#assert_no_axioms FX1Poly.ComputerAlgebra.composeRingHomIdentityLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.composeRingHomIdentityRight
#assert_no_axioms FX1Poly.ComputerAlgebra.composeRingHomAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.composeRingHomRespectsHomDenotesSame

end FX1PolyAudit
