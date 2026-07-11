import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidRetractionConvDeltas

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidRetractionConvDeltasAudit — zero-axiom gate for the
per-constructor CONVERTIBILITY deltas of the additive NF-retraction (the syntactic lift of the r5 matrix census)
and the honest corrected-star assembly (WP-PROP r6, #2033).

Per-declaration `#assert_no_axioms` on: the five generator CONV deltas (mu/delta via strict chains, eta/eps/sigma
definitional); the id / whisker CONV lifts + the concrete whisker delta; and the B3 markers (including the
`= false` corrected-star residual).

Independent `#print axioms` on the two non-trivial generator CONV deltas closes the gate. -/

namespace FX1PolyAudit

-- The five generator CONV deltas.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuGenConvToMuFoldTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaGenConvToDeltaFanTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidEtaGenConvToMuFoldZero
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidEpsGenConvToDeltaFanZero
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaGenConvToPermTwo

-- The id / whisker CONV lifts + the concrete whisker delta.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidIdCellConvLift
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWhiskerLeftConvLift
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWhiskerRightConvLift
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWhiskerLeftMuConvDelta

-- The B3 markers (generator deltas + id/whisker lifts + star assembly + the residual + the ledger).
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_generatorConvDeltasShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_idWhiskerConvLiftsShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_starAssemblyElementaryCasesShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_correctedStarStillRSixAfterConvDeltas
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_retractionConvDeltasRoundSixLedgerShipped

-- Independent (non-fuel) axiom prints on the two non-trivial generator CONV deltas.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuGenConvToMuFoldTwo
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaGenConvToDeltaFanTwo

end FX1PolyAudit
