-- TODO: DELETE THIS GARBAGE -- defective bunchedBimonoid star (refuted r29/r30/r31); superseded by the LafontProp re-founding
import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidStarDimTwoCanonicalFires

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidStarDimTwoCanonicalFiresAudit — zero-axiom gate for
the corrected target's concrete fires: the all-width positive family fire, the flagship width-6 full-premise
fire, and the mu/delta negative control (WP-PROP r29).

Per-declaration `#assert_no_axioms` on the dimension census, the guard inductions (additivity, well-typedness,
canonicity of the folds / fans / powers / both braidings), the family guard theorems, the family instances of
the corrected star, the width-6 record-level matrix equality and full fire, the negative control, and the
marker — AND an independent (non-fuel) `#print axioms` on the fire spine. -/

namespace FX1PolyAudit

-- A1 — the dimension census.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAWordPowWordWidth
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuFoldMatrixRows
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuFoldMatrixCols
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaFanMatrixRows
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaFanMatrixCols
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrandPastBlockMatrixRows
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrandPastBlockMatrixCols
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrandPastBlockRevMatrixRows
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrandPastBlockRevMatrixCols

-- A2 — the additivity inductions.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAWordPowAdditive
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuFoldAdditive
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaFanAdditive
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrandPastBlockAdditive
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrandPastBlockRevAdditive

-- A3 — the well-typedness inductions.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddEtaGenWellTyped
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddEpsGenWellTyped
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAWordPowWellTyped
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuFoldWellTyped
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaFanWellTyped
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrandPastBlockWellTyped
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrandPastBlockRevWellTyped

-- A4 — the canonicity inductions.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddEtaGenCanonical
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddEpsGenCanonical
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAWordPowCanonical
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuFoldCanonical
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaFanCanonical
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrandPastBlockCanonical
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrandPastBlockRevCanonical

-- A5 — the fires.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockThreadingPairSatisfiesGuardsMu
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockThreadingPairSatisfiesGuardsDelta
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCorrectedStarHoldsAtBlockThreadingFamilyMu
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCorrectedStarHoldsAtBlockThreadingFamilyDelta
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockThreadingPairMatrixEqAtWidthSix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCorrectedStarFiredPositiveAtWidthSix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuDeltaMatricesDiffer
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCorrectedStarNegativeControlMuDelta
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_correctedStarFiredOnConcreteData

-- Independent (non-fuel) axiom prints — the fire spine must print NO axioms at all.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockThreadingPairSatisfiesGuardsMu
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockThreadingPairSatisfiesGuardsDelta
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockThreadingPairMatrixEqAtWidthSix
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCorrectedStarFiredPositiveAtWidthSix
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCorrectedStarNegativeControlMuDelta
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_correctedStarFiredOnConcreteData

end FX1PolyAudit
