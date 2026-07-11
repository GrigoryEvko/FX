import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidSpiderNormalForm

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidSpiderNormalFormAudit — zero-axiom gate for the matrix
PROP opens (WP-PROP r1, #2032/#2033).

Per-declaration `#assert_no_axioms` on: the arity word + the PROP object widths + the width bridge, the hom-set
view (each dim-2 generator's boundary widths), the composition view (domain / codomain preservation), and the B1
marker (B1); the spider building blocks (`deltaFan`, `muFold`, `spiderScalar`) + the instance spiders + the
per-instance round-trips + the B2 markers (B2); the two completeness instances (convertibility over the sound
sub-theory + the derived / round-trip matrix agreements) + the B3 marker (B3); the ledger / census markers (B4).

Independent `#print axioms` (NOT fuel-based, MEMORY: mandatory) on the spider constructor, a round-trip, and the
completeness-instance convertibility closes the gate. -/

namespace FX1PolyAudit

-- B1 — the PROP objects (arity word + widths + bridge).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAPow
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAPowZero_width
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAPowOne_width
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAPowTwo_width
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAPowThree_width
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAPowTwoWidthMatchesAaWord

-- B1 — the hom-set view (boundary widths of each dim-2 generator).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddMuGen_isHomSourceWidth
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddMuGen_isHomTargetWidth
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddDeltaGen_isHomSourceWidth
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddDeltaGen_isHomTargetWidth
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddSigmaGen_isHomSourceWidth
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddSigmaGen_isHomTargetWidth
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddEtaGen_isHomSourceWidth
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddEpsGen_isHomTargetWidth

-- B1 — the composition view (domain / codomain preservation) + the marker.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPropCompositionPreservesDomain
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPropCompositionPreservesCodomain
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPropCompositeSourceWidth
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPropCompositeTargetWidth
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_propHomAndCompositionViewsTypeCheck

-- B2 — the spider building blocks (STRUCTURAL Nat recursions: the key propext / WellFounded check).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaFan
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuFold
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSpiderScalar
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSpiderAllOnesTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSpiderCopyOne
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSpiderTwoByThreeSample

-- B2 — the building-block shape lemmas.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaFanZero_matrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaFanTwo_matrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaFanThree_matrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuFoldZero_matrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuFoldTwo_matrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuFoldThree_matrix

-- B2 — the per-instance round-trips + the direct self-attacks.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSpiderScalarZeroRoundTrip
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSpiderScalarOneRoundTrip
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSpiderScalarTwoRoundTrip
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSpiderScalarThreeRoundTrip
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSpiderEmptyRoundTrip
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSpiderAllOnesTwoRoundTrip
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSpiderTwoByThreeRoundTrip
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidZeroScalarSelfAttack
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMultiplicityTwoSelfAttack

-- B2 — the markers.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_spiderPerInstanceRoundTripShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_spiderGeneralRoundTripReached
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_spiderGeneralStageLemmasReached
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_spiderGeneralRoutingReached

-- B3 — completeness instance 1 (bialgebra-B1 legs converge to the all-ones spider).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBialgebraRightLegConvertibleToSpider
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBialgebraLeftLegConvertibleToSpider
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBialgebraLeftLegMatrixIsSpider
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBialgebraCompletenessInstance

-- B3 — completeness instance 2 (cocommutativity legs converge to the copy spider).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSpiderCopyOneRoundTrip
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCocommRightLegConvertibleToSpiderCopy
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCocommLeftLegConvertibleToSpiderCopy
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCocommLeftLegMatrixIsSpiderCopy
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCocommutativityCompletenessInstance

-- B3 — the marker.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_propCompletenessInstancesShipped

-- Independent confirmation (not fuel-based) of the B1 arity word + a hom-view fact + the spider blocks /
-- round-trip + the two completeness-instance convertibilities.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAPow
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPropCompositionPreservesDomain
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaFan
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuFold
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSpiderAllOnesTwoRoundTrip
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBialgebraCompletenessInstance
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCocommutativityCompletenessInstance

end FX1PolyAudit
