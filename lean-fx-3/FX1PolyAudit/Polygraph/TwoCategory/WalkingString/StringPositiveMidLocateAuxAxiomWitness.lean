import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidLocateAux

/-! # FX1PolyAudit.…WalkingString.StringPositiveMidLocateAuxAxiomWitness — INDEPENDENT axiom witness
(FC-3 r45, R3)

The trusted independent cross-check for the positive-mid fueled partner-LOCATE round: raw `#print axioms` on
every proof-carrying declaration.  Each must print `does not depend on any axioms`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.stringMatchingLocateAuxMid
#print axioms FX1Poly.Polygraph.fxString_hasPositiveMidLocateAux

end FX1PolyAudit
