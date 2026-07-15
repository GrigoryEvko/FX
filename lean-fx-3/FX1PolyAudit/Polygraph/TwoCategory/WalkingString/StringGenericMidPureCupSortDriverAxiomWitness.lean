import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringGenericMidPureCupSortDriver

/-! # FX1PolyAudit.…WalkingString.StringGenericMidPureCupSortDriverAxiomWitness — INDEPENDENT axiom witness
(FC-4 r7)

The trusted independent cross-check for the driver tranche: raw `#print axioms` (the built-in, NOT the custom
`#assert_no_axioms` command) on the back-append congruence, the any-width determinacy + proof, both `k = 2`
recovery pairs, the fires, the `k = 3` fixtures / pins / controls, and the marker.  Each must print `does not
depend on any axioms` (in particular the `by decide` matching pins pull no `propext`). -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.genericSpineTraceEquiv_backAppendCongr
#print axioms FX1Poly.Polygraph.GenericMidPureCupDeterminacy
#print axioms FX1Poly.Polygraph.genericMidPureCupDeterminacy_proof
#print axioms FX1Poly.Polygraph.stringPositiveMidDeterminacy_shippedInhabitant
#print axioms FX1Poly.Polygraph.stringPositiveMidDeterminacy_viaGenericClassAtTwo
#print axioms FX1Poly.Polygraph.stringWidthZeroDeterminacy_shippedInhabitant
#print axioms FX1Poly.Polygraph.stringWidthZeroDeterminacy_viaGenericClassAtTwo
#print axioms FX1Poly.Polygraph.genericSortDriver_firesAtTwoOnDistinctDoubleCup
#print axioms FX1Poly.Polygraph.quadSortCupThreeAtTwoW0
#print axioms FX1Poly.Polygraph.quadSortCupThreeAtZeroW0
#print axioms FX1Poly.Polygraph.quadSortCupOneAtZeroOverL3L4
#print axioms FX1Poly.Polygraph.quadSortOrderA
#print axioms FX1Poly.Polygraph.quadSortOrderB
#print axioms FX1Poly.Polygraph.quadSortOrders_matchingsAgree
#print axioms FX1Poly.Polygraph.quadSortOrderA_matchingComputes
#print axioms FX1Poly.Polygraph.quadSortOrders_windowsDiffer
#print axioms FX1Poly.Polygraph.quadSortOrders_headGeneratorsDiffer
#print axioms FX1Poly.Polygraph.quadSortDecision_firesAtThreeWidthZero
#print axioms FX1Poly.Polygraph.quadSortBottomWordMidTwo
#print axioms FX1Poly.Polygraph.quadSortMidCupOneAtZero
#print axioms FX1Poly.Polygraph.quadSortMidCupThreeAtFour
#print axioms FX1Poly.Polygraph.quadSortMidCupThreeAtTwo
#print axioms FX1Poly.Polygraph.quadSortMidCupOneAtZeroDoubled
#print axioms FX1Poly.Polygraph.quadSortMidOrderA
#print axioms FX1Poly.Polygraph.quadSortMidOrderB
#print axioms FX1Poly.Polygraph.quadSortMidOrders_matchingsAgree
#print axioms FX1Poly.Polygraph.quadSortMidOrderA_matchingComputes
#print axioms FX1Poly.Polygraph.quadSortMidOrders_windowsDiffer
#print axioms FX1Poly.Polygraph.quadSortDecision_firesAtThreeMidTwo
#print axioms FX1Poly.Polygraph.quadNestedCupTwoAtOne
#print axioms FX1Poly.Polygraph.quadNestedRainbow
#print axioms FX1Poly.Polygraph.quadNestedRainbow_matchingComputes
#print axioms FX1Poly.Polygraph.quadSortDecision_runsOnNestedRainbow
#print axioms FX1Poly.Polygraph.fxString_hasGenericMidPureCupSortDriver

end FX1PolyAudit
