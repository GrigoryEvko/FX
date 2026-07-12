import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidPureCupSort

/-! # FX1PolyAudit.…WalkingString.StringPositiveMidPureCupSortAxiomWitness — INDEPENDENT axiom witness
(FC-3 r45, R4 + R5, THE BRICK)

The trusted independent cross-check for the brick round: raw `#print axioms` on THE BRICK and the
now-unconditional tower theorems fired through it (including the `decide`-carrying distinct-pair fire).  Each
must print `does not depend on any axioms`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.stringPositiveMidPureCupDeterminacy_proof
#print axioms FX1Poly.Polygraph.stringMatchingReductsShareSpineTrace_holds
#print axioms FX1Poly.Polygraph.stringConvOfMapEq_holds
#print axioms FX1Poly.Polygraph.stringSaturatedMatchingCanonicalization_holds
#print axioms FX1Poly.Polygraph.decidableStringSaturatedConv_holds
#print axioms FX1Poly.Polygraph.stringPositiveMidBrick_firesOnDistinctDoubleCup
#print axioms FX1Poly.Polygraph.fxString_hasPositiveMidPureCupSort

end FX1PolyAudit
