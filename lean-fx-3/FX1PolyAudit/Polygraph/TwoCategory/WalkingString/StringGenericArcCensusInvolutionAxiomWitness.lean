import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringGenericArcCensusInvolution

/-! # FX1PolyAudit.…WalkingString.StringGenericArcCensusInvolutionAxiomWitness — INDEPENDENT axiom witness
(FC-4 r7)

The trusted independent cross-check for the involution tranche: raw `#print axioms` (the built-in, NOT the
custom `#assert_no_axioms` command) on the generic census / perfect-matching capstones, the transported
involution / no-fixed-point, the any-width unification, the recovery pair, the `k = 3` fires, and the marker.
Each must print `does not depend on any axioms` (in particular the `by decide` cross-checks pull no
`propext`). -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.genericArcBoundaryCensus_stepArcAtom
#print axioms FX1Poly.Polygraph.genericArcBoundaryCensus_processArcSpine_ofChained
#print axioms FX1Poly.Polygraph.genericArcBoundaryCensus_ofChainedSpineList
#print axioms FX1Poly.Polygraph.genericArcPerfectMatchingTokens_stepArcAtom
#print axioms FX1Poly.Polygraph.genericArcPerfectMatchingTokens_processArcSpine_ofChained
#print axioms FX1Poly.Polygraph.genericArcPerfectMatchingTokens_ofChainedSpineList
#print axioms FX1Poly.Polygraph.genericArcDiagram_partner_isInvolution
#print axioms FX1Poly.Polygraph.genericMatchingOf_partner_isInvolution
#print axioms FX1Poly.Polygraph.genericMatchingOf_partner_neSelf
#print axioms FX1Poly.Polygraph.genericMatchingPartner_isInvolution_anyWidth
#print axioms FX1Poly.Polygraph.stringPartnerInvolution_shippedInhabitant
#print axioms FX1Poly.Polygraph.stringPartnerInvolution_viaGenericClassAtTwo
#print axioms FX1Poly.Polygraph.quadInvolutionWidthZero_matchingComputes
#print axioms FX1Poly.Polygraph.genericInvolutionAnyWidth_firesAtThreeWidthZero
#print axioms FX1Poly.Polygraph.genericInvolutionAnyWidth_firesAtThreeMidOne
#print axioms FX1Poly.Polygraph.genericNeSelf_firesAtThreeMidOne
#print axioms FX1Poly.Polygraph.fxString_hasGenericArcCensusInvolution

end FX1PolyAudit
