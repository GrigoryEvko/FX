import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidSpiderBlockExchange

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidSpiderBlockExchangeAudit — zero-axiom gate for the
block-exchange interchange (WP-PROP r3, #2033, the star round).

Per-declaration `#assert_no_axioms` on the route-(iii) block-exchange: the concrete truth-probes, the append-read
/ range-split sub-kit (Init's `range_add` / `length_map` / `map_map` / `sub_add_cancel` all leak `propext`, so
each is re-derived), the four `directSum` quadrant reads, the four block contractions, the two row assemblies, and
the general interchange — the EXACT r2 wall goal, delivered without matrix extensionality. -/

namespace FX1PolyAudit

-- B1 — the concrete block-exchange truth-probes.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockExchangeConcreteDiagTwoThree
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockExchangeConcreteSquare
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockExchangeConcreteNonSquare

-- B1 — the append-read / range-split sub-kit (hand-rolled, propext-clean).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidListMapLength
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRowListGetAppendLow
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRowListGetAppendHigh
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNatListGetAppendLow
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNatListGetAppendHigh
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMapMapFusion
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRangeMapCongr
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidListAppendNil
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRangeAddSplit

-- B1 — the well-formedness predicate + the map/replicate/arithmetic helpers.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMatWellFormed
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRowListGetMap
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNatListGetReplicateZero
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidListLengthReplicate
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddSubCancel
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSubLtOfLtAdd

-- B1 — the four directSum quadrant reads.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDirectSumEntryTopLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDirectSumEntryTopRight
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDirectSumEntryBottomLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDirectSumEntryBottomRight

-- B1 — the finite-sum split + the four block contractions.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNatListSumReplicateZero
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNatListSumRangeAddSplit
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockContractTopLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockContractTopRight
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockContractBottomLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockContractBottomRight

-- B1 — the map split, append congruence, the two row assemblies, and the interchange.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMapRangeAddSplit
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAppendEqCongr
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockExchangeTopRow
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockExchangeBottomRow
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockExchangeInterchange

-- B1 — the markers.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_blockExchangeSubKitShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_blockExchangeInterchangeShipped

end FX1PolyAudit
