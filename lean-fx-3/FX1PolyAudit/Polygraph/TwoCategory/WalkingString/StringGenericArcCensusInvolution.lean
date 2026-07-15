import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringGenericArcCensusInvolution

/-! # FX1PolyAudit.…WalkingString.StringGenericArcCensusInvolution — zero-axiom gate (FC-4 r7, the involution
tranche)

Per-declaration zero-axiom gate for the generic arc census / perfect-matching fold, the transported partner
involution / no-fixed-point, THE ANY-WIDTH involution unification, the `k = 2` recovery pair, the `k = 3`
both-branch fires with their decide cross-checks, the negative control, and the marker.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.genericArcBoundaryCensus_stepArcAtom
#assert_no_axioms FX1Poly.Polygraph.genericArcBoundaryCensus_processArcSpine_ofChained
#assert_no_axioms FX1Poly.Polygraph.genericArcBoundaryCensus_ofChainedSpineList
#assert_no_axioms FX1Poly.Polygraph.genericArcPerfectMatchingTokens_stepArcAtom
#assert_no_axioms FX1Poly.Polygraph.genericArcPerfectMatchingTokens_processArcSpine_ofChained
#assert_no_axioms FX1Poly.Polygraph.genericArcPerfectMatchingTokens_ofChainedSpineList
#assert_no_axioms FX1Poly.Polygraph.genericArcDiagram_partner_isInvolution
#assert_no_axioms FX1Poly.Polygraph.genericMatchingOf_partner_isInvolution
#assert_no_axioms FX1Poly.Polygraph.genericMatchingOf_partner_neSelf
#assert_no_axioms FX1Poly.Polygraph.genericMatchingPartner_isInvolution_anyWidth
#assert_no_axioms FX1Poly.Polygraph.stringPartnerInvolution_shippedInhabitant
#assert_no_axioms FX1Poly.Polygraph.stringPartnerInvolution_viaGenericClassAtTwo
#assert_no_axioms FX1Poly.Polygraph.quadInvolutionWidthZero_matchingComputes
#assert_no_axioms FX1Poly.Polygraph.genericInvolutionAnyWidth_firesAtThreeWidthZero
#assert_no_axioms FX1Poly.Polygraph.genericInvolutionAnyWidth_firesAtThreeMidOne
#assert_no_axioms FX1Poly.Polygraph.genericNeSelf_firesAtThreeMidOne
#assert_no_axioms FX1Poly.Polygraph.fxString_hasGenericArcCensusInvolution

end FX1PolyAudit
