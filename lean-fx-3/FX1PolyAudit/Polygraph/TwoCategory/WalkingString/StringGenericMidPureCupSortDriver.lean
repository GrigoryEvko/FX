import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringGenericMidPureCupSortDriver

/-! # FX1PolyAudit.…WalkingString.StringGenericMidPureCupSortDriver — zero-axiom gate (FC-4 r7, the driver
tranche)

Per-declaration zero-axiom gate for the generic back-append congruence, the any-width determinacy brick + its
proof, BOTH `k = 2` recovery pairs (positive-mid AND width-`0`), the `k = 2` fire, the `k = 3` fixtures /
decide pins / negative controls, the three `k = 3` sort-decision fires, and the marker.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.genericSpineTraceEquiv_backAppendCongr
#assert_no_axioms FX1Poly.Polygraph.GenericMidPureCupDeterminacy
#assert_no_axioms FX1Poly.Polygraph.genericMidPureCupDeterminacy_proof
#assert_no_axioms FX1Poly.Polygraph.stringPositiveMidDeterminacy_shippedInhabitant
#assert_no_axioms FX1Poly.Polygraph.stringPositiveMidDeterminacy_viaGenericClassAtTwo
#assert_no_axioms FX1Poly.Polygraph.stringWidthZeroDeterminacy_shippedInhabitant
#assert_no_axioms FX1Poly.Polygraph.stringWidthZeroDeterminacy_viaGenericClassAtTwo
#assert_no_axioms FX1Poly.Polygraph.genericSortDriver_firesAtTwoOnDistinctDoubleCup
#assert_no_axioms FX1Poly.Polygraph.quadSortCupThreeAtTwoW0
#assert_no_axioms FX1Poly.Polygraph.quadSortCupThreeAtZeroW0
#assert_no_axioms FX1Poly.Polygraph.quadSortCupOneAtZeroOverL3L4
#assert_no_axioms FX1Poly.Polygraph.quadSortOrderA
#assert_no_axioms FX1Poly.Polygraph.quadSortOrderB
#assert_no_axioms FX1Poly.Polygraph.quadSortOrders_matchingsAgree
#assert_no_axioms FX1Poly.Polygraph.quadSortOrderA_matchingComputes
#assert_no_axioms FX1Poly.Polygraph.quadSortOrders_windowsDiffer
#assert_no_axioms FX1Poly.Polygraph.quadSortOrders_headGeneratorsDiffer
#assert_no_axioms FX1Poly.Polygraph.quadSortDecision_firesAtThreeWidthZero
#assert_no_axioms FX1Poly.Polygraph.quadSortBottomWordMidTwo
#assert_no_axioms FX1Poly.Polygraph.quadSortMidCupOneAtZero
#assert_no_axioms FX1Poly.Polygraph.quadSortMidCupThreeAtFour
#assert_no_axioms FX1Poly.Polygraph.quadSortMidCupThreeAtTwo
#assert_no_axioms FX1Poly.Polygraph.quadSortMidCupOneAtZeroDoubled
#assert_no_axioms FX1Poly.Polygraph.quadSortMidOrderA
#assert_no_axioms FX1Poly.Polygraph.quadSortMidOrderB
#assert_no_axioms FX1Poly.Polygraph.quadSortMidOrders_matchingsAgree
#assert_no_axioms FX1Poly.Polygraph.quadSortMidOrderA_matchingComputes
#assert_no_axioms FX1Poly.Polygraph.quadSortMidOrders_windowsDiffer
#assert_no_axioms FX1Poly.Polygraph.quadSortDecision_firesAtThreeMidTwo
#assert_no_axioms FX1Poly.Polygraph.quadNestedCupTwoAtOne
#assert_no_axioms FX1Poly.Polygraph.quadNestedRainbow
#assert_no_axioms FX1Poly.Polygraph.quadNestedRainbow_matchingComputes
#assert_no_axioms FX1Poly.Polygraph.quadSortDecision_runsOnNestedRainbow
#assert_no_axioms FX1Poly.Polygraph.fxString_hasGenericMidPureCupSortDriver

end FX1PolyAudit
