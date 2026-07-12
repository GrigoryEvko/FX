import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringIdentificationCapstone

/-! # FX1PolyAudit.…WalkingString.StringIdentificationCapstoneAxiomWitness — INDEPENDENT axiom witness
(FC-3 r46, the post-flip harvest + the #2209 identification)

The trusted independent cross-check for the capstone round: raw `#print axioms` on the harvested terms and the
packaged identification biconditional.  Each must print `does not depend on any axioms`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.stringConvOfColouredMapEq_holds
#print axioms FX1Poly.Polygraph.stringCellValleyTraceEquiv_holds
#print axioms FX1Poly.Polygraph.decidableStringSaturatedConv_viaThreeSubProducers
#print axioms FX1Poly.Polygraph.stringSaturatedConv_iff_matchingOf_eq
#print axioms FX1Poly.Polygraph.fxString_hasIdentificationCapstone

end FX1PolyAudit
