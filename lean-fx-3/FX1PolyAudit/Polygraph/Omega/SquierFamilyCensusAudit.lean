import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.SquierFamilyCensus

/-! # FX1PolyAudit.Polygraph.Omega.SquierFamilyCensusAudit — zero-axiom gate for the WP-SQUIER family
census (the #2082 state, WP-SQUIER r2).

Per-declaration `#assert_no_axioms` on the decided-9 enumeration and its exhaustiveness / count, the
coherent-presentation status map, the shipped-four enumeration and count, the grounded four-of-nine census
conjunction, and the census markers (four-of-nine recorded, the walled adjunction, the op-dual reachables,
the multi-object walkers, and the NOT-closed capstone). -/

namespace FX1PolyAudit

-- SquierFamilyCensus.lean — the decided-9 enumeration
#assert_no_axioms FX1Poly.Polygraph.Omega.allSquierFamilyDecidedWalkers
#assert_no_axioms FX1Poly.Polygraph.Omega.squierFamilyDecidedWalkerCountIsNine
#assert_no_axioms FX1Poly.Polygraph.Omega.allSquierFamilyDecidedWalkersExhaustive

-- the status map and the shipped-four enumeration
#assert_no_axioms FX1Poly.Polygraph.Omega.squierFamilyStatus
#assert_no_axioms FX1Poly.Polygraph.Omega.allSquierFamilyShippedWalkers
#assert_no_axioms FX1Poly.Polygraph.Omega.squierFamilyShippedWalkerCountIsFour

-- the grounded four-of-nine census conjunction
#assert_no_axioms FX1Poly.Polygraph.Omega.SquierFamilyFourWalkersCoherentlyPresentedStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.squierFamilyFourWalkersCoherentlyPresented

-- the census markers
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_squierFamilyCoherentPresentationCensusFourOfNineR2
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_walkingAdjunctionCoherentPresentationWalledR2
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_squierFamilyOpDualReachableUnshippedR2
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_multiObjectWalkersOutsideDecidedNineR2
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_squierCapstoneClosedR2

-- the r3 op-dual round: the two-genuine-op-duals and six-of-nine grounded census extensions
#assert_no_axioms FX1Poly.Polygraph.Omega.SquierFamilyTwoGenuineOpDualsCoherentlyPresentedStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.squierFamilyTwoGenuineOpDualsCoherentlyPresented
#assert_no_axioms FX1Poly.Polygraph.Omega.SquierFamilySixWalkersCoherentlyPresentedStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.squierFamilySixWalkersCoherentlyPresented
#assert_no_axioms FX1Poly.Polygraph.Omega.allSquierFamilyGenuinelyPresentedWalkersAfterR3
#assert_no_axioms FX1Poly.Polygraph.Omega.squierFamilyGenuinelyPresentedWalkerCountIsSixAfterR3

-- the r3 census markers and the #2082 endgame ledger
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_squierFamilyTwoGenuineOpDualsShippedInCensusR3
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_squierFamilyPresentationCoveredEightOfNineR3
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_squierKZRidesMonadCoKZRidesComonadR3
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_squierCapstoneRemainingAdjunctionWallR3
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_squierCapstoneRemainingFullBasisNormalizerR3
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_squierCapstoneClosedR3

-- WP-EQUIV r1 (#2068) — the additive walking-equivalence census extension
#assert_no_axioms FX1Poly.Polygraph.Omega.SquierFamilyEquivalenceWalker
#assert_no_axioms FX1Poly.Polygraph.Omega.allSquierFamilyEquivalenceWalkers
#assert_no_axioms FX1Poly.Polygraph.Omega.squierFamilyEquivalenceWalkerCountIsTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.allSquierFamilyEquivalenceWalkersExhaustive
#assert_no_axioms FX1Poly.Polygraph.Omega.squierFamilyEquivalenceStatus
#assert_no_axioms FX1Poly.Polygraph.Omega.SquierFamilyEquivalenceWalkersPresentedStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.squierFamilyEquivalenceWalkersPresented
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_walkingEquivalenceWalkersPresentedInCensus
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_walkingEquivalenceFirstTwoObjectOmegaWalkerInCensus
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_bareWalkingEquivalenceWordProblemOpenInCensus

-- WP-FROBMONAD r1 (#2070) — the additive walking-Frobenius-monad census extension
#assert_no_axioms FX1Poly.Polygraph.Omega.SquierFamilyFrobeniusWalker
#assert_no_axioms FX1Poly.Polygraph.Omega.allSquierFamilyFrobeniusWalkers
#assert_no_axioms FX1Poly.Polygraph.Omega.squierFamilyFrobeniusWalkerCountIsOne
#assert_no_axioms FX1Poly.Polygraph.Omega.allSquierFamilyFrobeniusWalkersExhaustive
#assert_no_axioms FX1Poly.Polygraph.Omega.squierFamilyFrobeniusStatus
#assert_no_axioms FX1Poly.Polygraph.Omega.SquierFamilyFrobeniusWalkerPresentedStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.squierFamilyFrobeniusWalkerPresented
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_walkingFrobeniusMonadPresentedInCensus
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_singleObjectFrobeniusMonadHasOmegaPresentation
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_bareFrobeniusMonadWordProblemWalledInCensus

-- WP-STRONG r1 (#2189) — the additive walking-strong-monad census extension
#assert_no_axioms FX1Poly.Polygraph.Omega.SquierFamilyStrongWalker
#assert_no_axioms FX1Poly.Polygraph.Omega.allSquierFamilyStrongWalkers
#assert_no_axioms FX1Poly.Polygraph.Omega.squierFamilyStrongWalkerCountIsOne
#assert_no_axioms FX1Poly.Polygraph.Omega.allSquierFamilyStrongWalkersExhaustive
#assert_no_axioms FX1Poly.Polygraph.Omega.squierFamilyStrongStatus
#assert_no_axioms FX1Poly.Polygraph.Omega.SquierFamilyStrongWalkerPresentedStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.squierFamilyStrongWalkerPresented
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_walkingStrongMonadPresentedInCensus
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_singleObjectStrongMonadHasOmegaPresentation
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega4_bareStrongMonadTwoCellDecisionWalledInCensus

end FX1PolyAudit
