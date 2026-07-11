import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.OmegaHouseStyleFamilyLedger

/-! # FX1PolyAudit.Polygraph.Omega.OmegaHouseStyleFamilyLedgerAudit — zero-axiom gate for the family-wide
house-style over-quotient census (OMEGA HOUSE-STYLE SWEEP, WP-BI r4: B2 / B4 / B5).

Per-declaration `#assert_no_axioms` on: the decidable syntactic-shape predicates; the shape-present theorems
(monad / strong / distlaw SHIPPED, involution / cyclic-3 / idempotent SHAPE-MATCHED); the shape-absent theorems
(the walking-equivalence positive example); the family / not-spurious / discriminant / positive-example /
homology-family / cross-lane-flag / censused-bill / ledger markers.

Independent `#print axioms` (NOT fuel-based, MEMORY: mandatory) on the decisive classification facts closes the
gate. -/

namespace FX1PolyAudit

-- B2 — the decidable syntactic-shape predicates.
#assert_no_axioms FX1Poly.Polygraph.Omega.isGenHead
#assert_no_axioms FX1Poly.Polygraph.Omega.isBareGenWhisker

-- B2 — shape present: the SHIPPED over-quotients.
#assert_no_axioms FX1Poly.Polygraph.Omega.omegaHouseStyleMonadUnitUnitLegsAreBareWhiskers
#assert_no_axioms FX1Poly.Polygraph.Omega.omegaHouseStyleStrongUnitUnitLegsAreBareWhiskers
#assert_no_axioms FX1Poly.Polygraph.Omega.omegaHouseStyleDistLawMonadSUnitUnitLegsAreBareWhiskers

-- B2 — shape present but over-quotient UNRESOLVED: the not-spurious trio.
#assert_no_axioms FX1Poly.Polygraph.Omega.omegaHouseStyleInvolutionSssLegsAreBareWhiskers
#assert_no_axioms FX1Poly.Polygraph.Omega.omegaHouseStyleCyclicThreeLegsAreBareWhiskers
#assert_no_axioms FX1Poly.Polygraph.Omega.omegaHouseStyleIdempotentEeeLegsAreBareWhiskers

-- B2 — shape absent: the walking-equivalence positive example.
#assert_no_axioms FX1Poly.Polygraph.Omega.omegaHouseStyleEquivCancellationLegsAreNotBareWhiskers
#assert_no_axioms FX1Poly.Polygraph.Omega.omegaHouseStyleEquivTriangleLegsAreNotBareWhiskers

-- B2 / B4 / B5 — the family ledger markers.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmegaHouseStyle_familyThreeWalkersOverQuotientConfirmed
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmegaHouseStyle_notSpuriousTrioShapeMatchesOverQuotientUnresolved
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmegaHouseStyle_shapeIsNecessaryNotSufficientFaithfulModelDecides
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmegaHouseStyle_walkingEquivalenceIsPositiveExampleShapeAbsent
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmegaHouseStyle_homologyFamilyNoImpactAbelianizationInvisible
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmegaHouseStyle_homologyLaneUntouchedRetractionUserGatedFlag
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmegaHouseStyle_censusedBillFrobeniusTrioModelsOpDualsFubini
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmegaHouseStyle_familyOverQuotientCensusLedgerShipped

-- Independent confirmation (not fuel-based): the decisive classification facts are all axiom-free.
#print axioms FX1Poly.Polygraph.Omega.isBareGenWhisker
#print axioms FX1Poly.Polygraph.Omega.omegaHouseStyleMonadUnitUnitLegsAreBareWhiskers
#print axioms FX1Poly.Polygraph.Omega.omegaHouseStyleInvolutionSssLegsAreBareWhiskers
#print axioms FX1Poly.Polygraph.Omega.omegaHouseStyleEquivCancellationLegsAreNotBareWhiskers
#print axioms FX1Poly.Polygraph.Omega.omegaHouseStyleEquivTriangleLegsAreNotBareWhiskers

end FX1PolyAudit
