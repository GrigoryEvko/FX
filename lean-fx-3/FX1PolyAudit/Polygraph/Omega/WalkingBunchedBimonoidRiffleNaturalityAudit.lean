import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidRiffleNaturality

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidRiffleNaturalityAudit — zero-axiom gate for the riffle
primitive, the collision peel recursion, the width-3 naturality slides, and the refutation of the naive general
`wideSwap` fold (WP-PROP r7, #2033).

Per-declaration `#assert_no_axioms` on: the word power + the `strandPastBlock` riffle primitive + its four matrix
probes + the wide-symmetry match; the two collision peel lemmas; the two width-3 naturality slides (CONV); the
naive `wideSwap` candidate + its refutation; and the B1 markers.

Independent `#print axioms` on the two width-3 slides (the recursion's slide atoms) and the naive-fold refutation
(the decisive truth-probe) closes the gate. -/

namespace FX1PolyAudit

-- The riffle primitive + its matrix probes.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAWordPow
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrandPastBlock
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrandPastBlockZeroMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrandPastBlockOneMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrandPastBlockTwoMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrandPastBlockThreeMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrandPastBlockTwoMatchesWideSymmetryFront

-- The two collision peel lemmas.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuFoldPeel
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaFanPeel

-- The two width-3 naturality slides (CONV over the star scope).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuNaturalitySlideConv
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaNaturalitySlideConv

-- The naive general fold + its refutation.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideSwapNaiveCandidate
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideSwapNaiveFoldRefutedAtTwoTwo

-- The B1 markers (primitive-and-slides + the two byte-intact residual walls + ledger).
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_rifflePrimitiveAndSlidesShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_wideSwapGeneralAssemblyStillUnbuilt
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_wideCollisionRecursionStillUnbuilt
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_riffleNaturalityRoundSevenLedgerShipped

-- Independent (non-fuel) axiom prints on the slide atoms + the decisive refutation.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuNaturalitySlideConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaNaturalitySlideConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideSwapNaiveFoldRefutedAtTwoTwo

end FX1PolyAudit
