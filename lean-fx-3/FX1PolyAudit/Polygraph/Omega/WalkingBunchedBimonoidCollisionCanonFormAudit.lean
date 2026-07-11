import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidCollisionCanonForm

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidCollisionCanonFormAudit — zero-axiom gate for the
Coxeter-free collision canon form: the canon-vs-collision matrix matches, the peel-to-generator unit strips, the
flagship `(2,2)` collision-to-staged-NF convertibility (Coxeter-free), the integer-sort negative control, and the
honest markers (WP-PROP r10, #2033).

Per-declaration `#assert_no_axioms` on every def / theorem / marker, PLUS independent (non-fuel) `#print axioms`
on the flagship `(2,2)` convertibility, the two unit strips, the integer-sort refutation, and the star-no-flip
marker.  The project `#assert_no_axioms` macro is fuel-based; the independent `#print axioms` closes the gate. -/

namespace FX1PolyAudit

-- L1 — the collision canon form + its matrix soundness at four widths.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCollisionCanonForm
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCollisionCanonMatchesCollisionTwoOne
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCollisionCanonMatchesCollisionOneTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCollisionCanonMatchesCollisionTwoTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCollisionCanonMatchesCollisionThreeTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCollisionCanonTwoTwoMatchesStagedNF

-- L2 — the peel-to-generator unit strips (Coxeter-free CONV atoms).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuFoldTwoStripToGen
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaFanTwoStripToGen

-- L3 — the flagship (2,2) collision-to-staged-NF convertibility (Coxeter-free).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideCollisionTwoTwoStripToBrick
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideCollisionTwoTwoConvToStagedNF

-- L4 — the integer-sort negative control.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermWordOneZeroMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermWordSortedOneZeroMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBubbleSortNotMatrixPreserving

-- L5 — the markers.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_collisionCanonFormMatrixCorrect
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_collisionTwoTwoConvToStagedNFCoxeterFree
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_integerSortNotMatrixPreserving
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_collisionGeneralStepStillGatedOnBracketMatch
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterCanonForm
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_collisionCanonFormRoundTenLedgerShipped

-- Independent (non-fuel) axiom prints on the flagship convertibility, the two strips, the negative control, and
-- the star-no-flip marker.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideCollisionTwoTwoConvToStagedNF
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuFoldTwoStripToGen
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaFanTwoStripToGen
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBubbleSortNotMatrixPreserving
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCollisionCanonMatchesCollisionThreeTwo
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterCanonForm

end FX1PolyAudit
