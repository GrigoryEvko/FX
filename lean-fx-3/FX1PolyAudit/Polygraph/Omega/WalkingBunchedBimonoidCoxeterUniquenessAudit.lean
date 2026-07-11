import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidCoxeterUniqueness

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidCoxeterUniquenessAudit — zero-axiom gate for the distant
commutation via the Godement interchange, the complete Coxeter / double-coset move set in scope, and the walled
general `CoxeterWordUnique` bubble-sort (WP-PROP r7, #2033).

Per-declaration `#assert_no_axioms` on: the two distant-swap legs + the interchange conv + the shared-matrix
witness; the two double-coset moves; the five-move bundle; and the B2 markers.

Independent `#print axioms` on the distant-commutation conv (the recon's decisive `StrictAxiomRel` finding) and
the five-move bundle closes the gate. -/

namespace FX1PolyAudit

-- The distant-swap legs + the interchange conv + the shared-matrix witness.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantSwapLeftLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantSwapRightLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantSwapCommuteViaInterchange
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantSwapMatrixShared

-- The two double-coset moves + the five-move bundle.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCommutativityOverStar
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCocommutativityOverStar
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCoxeterMovesAllInScope

-- The B2 markers.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_distantCommutationIsInterchange
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_coxeterMovesAllInScope
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_sortedFormIsConfluenceNotNormalForm
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_coxeterWordUniqueBubbleSortStillUnbuilt
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_coxeterUniquenessRoundSevenLedgerShipped

-- Independent (non-fuel) axiom prints on the decisive finding + the bundle.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantSwapCommuteViaInterchange
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCoxeterMovesAllInScope

end FX1PolyAudit
