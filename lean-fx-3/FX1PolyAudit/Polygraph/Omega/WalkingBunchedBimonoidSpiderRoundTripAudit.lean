import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidSpiderRoundTrip

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidSpiderRoundTripAudit — zero-axiom gate for the general
spider round-trip (WP-PROP r2, #2033).

Per-declaration `#assert_no_axioms` on the matMul-algebra Fubini kit (B1): the concrete matMul-associativity
truth-probes, the hand-rolled `List.range` reindexing kit (Init's `range_succ` / `map_append` / `replicate_succ'`
leak `propext`, so each is re-derived), the finite-sum append law, the `getD`-at-range read kit, and the B1
marker. -/

namespace FX1PolyAudit

-- B1 — the matMul-associativity truth-probes.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMatMulAssocConcreteTwoByTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMatMulAssocConcreteNonSquare

-- B1 — the List.range reindexing kit (hand-rolled, propext-clean).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidListAppendAssoc
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMapAppendDistrib
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMapReplicate
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidReplicateSuccSnoc
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRangeLoopFactors
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRangeSuccSnoc
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRangeMapConstIsReplicate

-- B1 — the finite-sum append law.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNatListSumAppend

-- B1 — the getD-at-range read kit.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNatListGetReplicateSnocLow
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNatListGetReplicateSnocHigh
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRowListGetReplicateSnocLow
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRowListGetReplicateSnocHigh
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNatListGetReplicateLow
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRowListGetReplicateLow
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNatListSumReplicateOne

-- B1 — the marker.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_matMulFubiniKitShipped

-- B2 — the stage target matrices + base-case pins.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidFanMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRowMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidFanMatrixMatchesDeltaFanTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRowMatrixMatchesMuFoldTwo

-- B2 — the delta-stage block reads + the general delta stage lemma.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidFanBlockEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidFanBlockEntryLowZero
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidFanBlockEntryLowOne
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidFanBlockEntryHighZero
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidFanBlockEntryHighOne
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidFanMatMulRowIsOne
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaFanMatrix

-- B2 — the mu-stage block reads + the general mu stage lemma.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRowBlockEntryFirstLow
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRowBlockEntryFirstHigh
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRowBlockEntrySecondLow
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRowBlockEntrySecondHigh
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRowMatMulColIsOne
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuFoldMatrix

-- B2 — the general scalar round-trip + the markers.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidScalarProductIsOne
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSpiderScalarMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_spiderStageLemmasGeneralShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_spiderScalarRoundTripGeneralShipped

-- B3 — the coherence self-attack + the identity-block 2D round-trips + the edges + the markers.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSpiderScalarIsFanFoldComposite
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSpiderScalarWhiskeredRightMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSpiderScalarWhiskeredLeftMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSpiderZeroColumnEdge
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSpiderZeroRowEdge
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSpiderEmptyEdge
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_spiderIdentityBlockExtendedGeneralShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_spiderGeneralRoundTripBlockExchangeWall

end FX1PolyAudit
