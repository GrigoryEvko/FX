import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidPositionGenericMoves

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidPositionGenericMovesAudit — zero-axiom gate for the
position-generic move library: the firing combinator `bunchedBimonoidFireAtPosition`, the seven shipped base
moves lifted to generic position, and the wide-collision recursion's gate (a) [the generic-position naturality
slide] (WP-PROP r9, #2033).

Per-declaration `#assert_no_axioms` on every theorem / marker, PLUS independent (non-fuel) `#print axioms` on the
firing combinator, the two naturality slides at generic position (the gate-(a) deliverable), and the matrix
soundness pins.  The project `#assert_no_axioms` macro is fuel-based; the independent `#print axioms` closes the
gate. -/

namespace FX1PolyAudit

-- L1 — the position-generic firing combinator (non-recursive, whnf-free).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidFireAtPosition

-- L2 — the seven shipped base moves lifted to generic position.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidYangBaxterAtPosition
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidInvolutionAtPosition
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantSwapAtPosition
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCommutativityAtPosition
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCocommutativityAtPosition
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuNaturalitySlideAtPosition
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaNaturalitySlideAtPosition

-- L2 — the matrix soundness pins (fired endpoints share their matrix at small width).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidYangBaxterAtPositionOneZeroLeftMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidYangBaxterAtPositionOneZeroMatrixShared
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuNaturalitySlideAtPositionOneZeroMatrixShared
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCommutativityAtPositionOneZeroMatrixShared

-- The markers.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_fireBaseMoveAtPositionShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_sevenMovesFirableAtGenericPosition
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_genericPositionNaturalitySlideShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_wideCollisionRecursionStillGatedOnCoxeterAndGlue
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterPositionGeneric
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_positionGenericMovesRoundNineLedgerShipped

-- Independent (non-fuel) axiom prints on the combinator, the two gate-(a) slides, and the flagship matrix pins.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidFireAtPosition
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuNaturalitySlideAtPosition
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaNaturalitySlideAtPosition
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidYangBaxterAtPositionOneZeroLeftMatrix
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuNaturalitySlideAtPositionOneZeroMatrixShared
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterPositionGeneric

end FX1PolyAudit
