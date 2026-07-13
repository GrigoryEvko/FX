import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidStarColourMislabelRefutation

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidStarColourMislabelRefutationAudit — zero-axiom gate
for THE #2033 STAR DECISION: `bunchedBimonoidStarStatementAdditiveWellTyped` refuted (WP-PROP r29).

Per-declaration `#assert_no_axioms` on the refutation datum and its three premise witnesses, the separating
count invariant, the propext-free row-family dimension census, the star-scope absorber, the standalone
non-convertibility, THE DECISION, the dim-3 triviality witness, and the decision markers — AND an independent
(non-fuel) `#print axioms` on the decision spine.  The refutation must be UNCONDITIONALLY axiom-free: a
refutation with `propext` in its closure would not decide the star.  The frozen owner
`fxBunchedBimonoid_correctedWellTypedStarStillOpen` stays `= false` byte-intact (superseded by content, never
edited). -/

namespace FX1PolyAudit

-- A1 — the refutation datum and its three star-premise witnesses.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidColourMislabeledMuOneCell
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidColourMislabeledMuOneCellIsAdditive
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidColourMislabeledMuOneCellWellTyped
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAdditiveGenWellTypedForRefutation
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidColourMislabeledMuOneCellWidthMatchesAdditiveGen

-- A2 — the separating invariant and the two Nat-clash helpers.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddMultLabelCount
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddMultLabelCountAtDimZero
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSuccSuccNeOne
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidOneNeTwoClash

-- A3 — the propext-free row-family dimension census.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSoundRowDimIsTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidHexagonRowDimIsTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrictRowPreservesAddMultCountAtDimOne

-- A4 — the star-scope absorber and the decision spine.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddMultCountAgreementRel
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddMultCountAbsorbsStarScope
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidColourMislabeledMuNotConvToAdditiveGen
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStarStatementAdditiveWellTypedRefuted
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDimThreeEvalTriviallyEqual

-- A5 — the decision markers.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_correctedWellTypedStarDecidedFalse
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_starRefutedByOffDimensionMislabelNotDimTwoContent
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_starColourMislabelRefutationLedgerShipped

-- Independent (non-fuel) axiom prints — the decision spine must print NO axioms at all.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddMultCountAbsorbsStarScope
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidColourMislabeledMuNotConvToAdditiveGen
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStarStatementAdditiveWellTypedRefuted
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_correctedWellTypedStarDecidedFalse
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_starRefutedByOffDimensionMislabelNotDimTwoContent
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_starColourMislabelRefutationLedgerShipped

end FX1PolyAudit
