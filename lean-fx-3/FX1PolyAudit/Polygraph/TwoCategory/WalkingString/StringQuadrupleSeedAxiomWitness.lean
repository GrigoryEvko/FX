import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringQuadrupleSeed

/-! # FX1PolyAudit.…WalkingString.StringQuadrupleSeedAxiomWitness — INDEPENDENT axiom witness (FC-4 r2, R1 seed)

The trusted independent cross-check for the `k = 3` adjoint-quadruple seed: raw `#print axioms` (the built-in, NOT the
custom `#assert_no_axioms` command) on the signature, the index abstraction, the freeness separators, and the `k = 3`
census-carrier bridge.  Each must print `does not depend on any axioms`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.adjointQuadrupleModeSignature
#print axioms FX1Poly.Polygraph.quadLabelIndex
#print axioms FX1Poly.Polygraph.quadIndexWord
#print axioms FX1Poly.Polygraph.quad_letterOne_ne_letterThree
#print axioms FX1Poly.Polygraph.quad_letterTwo_ne_letterFour
#print axioms FX1Poly.Polygraph.quadCupCods_eq_carrierAtThree
#print axioms FX1Poly.Polygraph.quadCapDoms_eq_carrierAtThree
#print axioms FX1Poly.Polygraph.fxString_hasAdjointQuadrupleSeed

end FX1PolyAudit
