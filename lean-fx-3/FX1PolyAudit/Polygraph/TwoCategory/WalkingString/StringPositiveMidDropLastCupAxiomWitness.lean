import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidDropLastCup

/-! # FX1PolyAudit.…WalkingString.StringPositiveMidDropLastCupAxiomWitness — INDEPENDENT axiom witness
(FC-3 r45, R2)

The trusted independent cross-check for the positive-mid drop round: raw `#print axioms` on every
proof-carrying declaration.  Each must print `does not depend on any axioms`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.stringDropLastCup_matching_injective_mid
#print axioms FX1Poly.Polygraph.stringBackAppend_matching_congr_mid
#print axioms FX1Poly.Polygraph.fxString_hasPositiveMidDropLastCup

end FX1PolyAudit
