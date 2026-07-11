import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidWellTypedAbsorber

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidWellTypedAbsorberAudit — zero-axiom gate for the
well-typedness predicate, the `evalCellWellFormed` boundary-width bridge, and the RESTRICTED strict-unit-law
absorber it unlocks (WP-PROP r7, #2033).

Per-declaration `#assert_no_axioms` on: the three predicate components; the headline exclusion of the r6
counterexample + the positives; the boundary-width bridge motive + the `evalCellWellFormed` induction; the two
restricted strict-unit laws + their concrete instances; and the B3 markers.

Independent `#print axioms` on the headline self-attack (`misdeclaredMuNotWellTyped`), the bridge, and the
restricted left-unit law + its `mu_a` instance closes the gate. -/

namespace FX1PolyAudit

-- The predicate + its components.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidGenWidthAgreement
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidVcompComposable
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCellWellTyped

-- The headline exclusion + the positives.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMisdeclaredMuNotWellTyped
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddMuGenWellTyped
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddDeltaGenWellTyped
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddSigmaGenWellTyped

-- The boundary-width bridge.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBoundaryWidthAgrees
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidEvalCellWellFormed

-- The restricted strict-unit laws + concrete instances.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRestrictedVcompUnitLeftRespected
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRestrictedVcompUnitRightRespected
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRestrictedUnitLeftOnAddMu
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRestrictedUnitRightOnAddDelta

-- The B3 markers.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_cellWellTypedPredicateShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_boundaryWidthBridgeShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_restrictedStrictUnitLawsRespectedOnWellTyped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_strictLawCellAbsorberWellTypedPredicateDelivered
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_wellTypedAbsorberIsTheHonestBiTarget
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_wellTypedAbsorberRoundSevenLedgerShipped

-- Independent (non-fuel) axiom prints on the headline + bridge + restricted law.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMisdeclaredMuNotWellTyped
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidEvalCellWellFormed
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRestrictedVcompUnitLeftRespected
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRestrictedUnitLeftOnAddMu

end FX1PolyAudit
