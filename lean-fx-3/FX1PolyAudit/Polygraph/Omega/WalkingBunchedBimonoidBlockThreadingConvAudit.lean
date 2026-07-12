import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidBlockThreadingConv

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidBlockThreadingConvAudit — zero-axiom gate for the CONV
block-threading statement (both colours) and its base case delivered as a convertibility over the star scope
(mu / delta, at width 1, and at a generic pad position), WP-PROP r28 B1.

Per-declaration `#assert_no_axioms` on the named CONV statements, the leg-collapse lemmas, the two base
convertibilities, the two generic-pad firings, and the delivery / no-flip markers — AND an independent (non-fuel)
`#print axioms` on the base convertibilities and the markers.  The project `#assert_no_axioms` macro is fuel-based;
the independent `#print axioms` closes the gate on the `SaturatedConvOverWithId` congruence plumbing (propext-free,
no `Classical`).  The star markers stay `= false` byte-intact (cross-file, not edited). -/

namespace FX1PolyAudit

-- A1 — the named CONV block-threading statements (both colours).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockThreadingConvStatementMu
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockThreadingConvStatementDelta

-- A2 — the mu-side base case: the two leg collapses and the transitive base convertibility.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockThreadingConvBaseMuLeftCollapse
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockThreadingConvBaseMuRightCollapse
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockThreadingConvBaseMu

-- A3 — the delta-side base case: the two leg collapses and the transitive base convertibility.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockThreadingConvBaseDeltaLeftCollapse
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockThreadingConvBaseDeltaRightCollapse
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockThreadingConvBaseDelta

-- A4 — the base fired at a generic pad position (both colours).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockThreadingConvBaseMuAtPosition
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockThreadingConvBaseDeltaAtPosition

-- A5 — the delivery / no-flip markers (incl. the walls that stay false).
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_blockThreadingConvBaseShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_blockThreadingConvGeneralStepStillWalled
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterBlockThreadingBase
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_blockThreadingConvRoundLedgerShipped

-- Independent (non-fuel) axiom prints — closing the gate on the congruence plumbing (propext-free, no Classical).
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockThreadingConvBaseMu
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockThreadingConvBaseDelta
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockThreadingConvBaseMuAtPosition
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockThreadingConvBaseDeltaAtPosition
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_blockThreadingConvBaseShipped
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_blockThreadingConvGeneralStepStillWalled
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterBlockThreadingBase
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_blockThreadingConvRoundLedgerShipped

end FX1PolyAudit
