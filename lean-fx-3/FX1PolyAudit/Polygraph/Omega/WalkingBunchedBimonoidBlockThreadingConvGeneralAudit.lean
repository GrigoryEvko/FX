import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidBlockThreadingConvGeneral

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidBlockThreadingConvGeneralAudit — zero-axiom gate for
the FULL B1 CONV block-threading delivery: both r28-named generic-width statements inhabited at every width,
both colours (WP-PROP r29).

Per-declaration `#assert_no_axioms` on the left-nested word power + boundary census, the dimension-0 word-CONV
kit, the back-first respelling, the two all-width recursions, the width-0 bases, the statement inhabitations,
the at-any-pad firings, and the supersession markers — AND an independent (non-fuel) `#print axioms` on the
delivery spine.  The recursions are STRUCTURAL (`brecOn`, verified no `WellFounded.fix`); the frozen r27/r28
wall markers stay byte-intact (superseded by content, never edited). -/

namespace FX1PolyAudit

-- A1 — the left-nested word power and the fold/fan boundary census.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAWordPowLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuFoldBoundarySourceIsLeftPow
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuFoldBoundaryTargetIsColour
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaFanBoundarySourceIsColour
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaFanBoundaryTargetIsLeftPow

-- A2 — the dimension-0 word-CONV kit (units, rotations, left/right-nested identification).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWordUnitRightConv
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWordUnitLeftConv
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAWordPowRotateConv
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAWordPowLeftRotateConv
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAWordPowLeftMatchesAWordPowConv

-- A3 — the back-first respelling of the forward block braiding.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrandPastBlockPeelBackConv

-- A4 — the width-0 bases and the two all-width CONV recursions.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockThreadingConvBaseMuZero
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockThreadingConvBaseDeltaZero
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaPastMuFoldBlockThreadConv
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaPastDeltaFanBlockThreadConv

-- A5 — the r28-named statements inhabited + the at-any-pad firings.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockThreadingConvStatementMuDelivered
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockThreadingConvStatementDeltaDelivered
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaPastMuFoldBlockThreadConvAtPosition
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaPastDeltaFanBlockThreadConvAtPosition

-- A6 — the supersession / honest-scope markers.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_blockThreadingConvGeneralStepDelivered
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_genericWidthConvBlockThreadingDelivered
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_wideCollisionStillGatedAfterBlockThreading
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_blockThreadingConvGeneralLedgerShipped

-- Independent (non-fuel) axiom prints — the delivery spine must print NO axioms at all.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrandPastBlockPeelBackConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaPastMuFoldBlockThreadConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaPastDeltaFanBlockThreadConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockThreadingConvStatementMuDelivered
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockThreadingConvStatementDeltaDelivered
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_blockThreadingConvGeneralStepDelivered
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_genericWidthConvBlockThreadingDelivered
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_blockThreadingConvGeneralLedgerShipped

end FX1PolyAudit
