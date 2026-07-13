import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidStarDimTwoCanonicalRestatement

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidStarDimTwoCanonicalRestatementAudit — zero-axiom gate
for the corrected #2033 completeness target: dimension-2 pinned, canonical generator nodes (WP-PROP r29).

Per-declaration `#assert_no_axioms` on the canonicity table + fold, the positive generator witnesses, BOTH r29
leak exclusions (the colour mislabel and the boundary-respelled operation node with its every-r7-guard-passing
witness), the dim-2 mislabeled-whisker hazard, the corrected target, and the markers — AND an independent
(non-fuel) `#print axioms` on the restatement spine.  The corrected owner
`fxBunchedBimonoid_dimTwoCanonicalGensStarStillOpen` is `= false` (named, NOT proven — no flip). -/

namespace FX1PolyAudit

-- A1 — the canonicity table and fold.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidGenNodeCanonical
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCellGensCanonical

-- A2 — the positive witnesses (the genuine generators are canonical).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAdditiveGenCanonical
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAaWordCanonical
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddMuGenCanonical
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddDeltaGenCanonical
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddSigmaGenCanonical

-- A3 — the two r29 leak exclusions and the dim-2 hazard witness.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidColourMislabeledMuNotCanonical
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBoundaryRespelledMu
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBoundaryRespelledMuPassesRSevenGuards
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBoundaryRespelledMuNotCanonical
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMislabeledWhiskerPairSeparatedOnlyByCanonicity

-- A4 — the corrected target and the markers.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStarStatementDimTwoCanonicalGens
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_correctedStarRestatedDimTwoCanonicalGens
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_dimTwoCanonicalGensStarStillOpen
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_starDimTwoCanonicalRestatementLedgerShipped

-- Independent (non-fuel) axiom prints — the restatement spine must print NO axioms at all.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCellGensCanonical
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidColourMislabeledMuNotCanonical
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBoundaryRespelledMuNotCanonical
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStarStatementDimTwoCanonicalGens
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_correctedStarRestatedDimTwoCanonicalGens
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_dimTwoCanonicalGensStarStillOpen

end FX1PolyAudit
