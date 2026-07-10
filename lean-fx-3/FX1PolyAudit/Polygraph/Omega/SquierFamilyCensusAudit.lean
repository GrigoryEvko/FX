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

end FX1PolyAudit
