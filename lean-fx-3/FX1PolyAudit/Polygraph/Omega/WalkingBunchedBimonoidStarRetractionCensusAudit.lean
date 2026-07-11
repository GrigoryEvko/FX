import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidStarRetractionCensus

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidStarRetractionCensusAudit — zero-axiom gate for the
NF-induction census, the corrected additive-scope star, the width-2 collision witness, and the r6 residual ledger
(WP-PROP r5, #2033).

Per-declaration `#assert_no_axioms` on: the B2 staged-form census witnesses (id base + five additive generators +
whisker); the additive-fragment predicate; the corrected star + the refutation datum + the in/out witnesses; the
B3 width-2 collision witnesses; and the B2/star/B3/B4 markers.

Independent `#print axioms` on the refutation datum and the two exclusion witnesses closes the gate. -/

namespace FX1PolyAudit

-- B2 — the staged-form census witnesses.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidIdCellStagedWitness
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddMuStagedWitness
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddDeltaStagedWitness
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddEtaStagedWitness
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddEpsStagedWitness
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddSigmaStagedWitness
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWhiskerLeftStagedWitness

-- The additive-fragment predicate + the corrected star + the refutation.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidLabelIsAdditive
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCellUsesOnlyAdditive
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStarStatementAdditive
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMixedMuEqualMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddMuIsAdditive
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMultMuIsNotAdditive

-- B3 — the width-2 collision witnesses.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWidthTwoCollisionMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidScalarCollisionMatrix

-- The markers (B2 / star correction / B3 / B4 residuals + grand ledger).
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_nfBaseGeneratorWhiskerCensusMatrixWitnessed
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_starStatementCorrectedToAdditiveScope
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_unrestrictedStarIsRefutable
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_widthTwoCollisionMatrixWitnessed
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_r6WideCollisionRecursion
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_r6MiddleDeterminismDoubleCoset
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_correctedStarStaysRSix
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_roundFiveGrandLedgerShipped

-- Independent (non-fuel) axiom prints on the refutation datum + exclusion witnesses.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMixedMuEqualMatrix
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddMuIsAdditive
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMultMuIsNotAdditive

end FX1PolyAudit
