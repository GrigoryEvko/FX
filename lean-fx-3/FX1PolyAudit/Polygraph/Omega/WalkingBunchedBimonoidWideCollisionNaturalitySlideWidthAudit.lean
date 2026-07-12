import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidWideCollisionNaturalitySlideWidth

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidWideCollisionNaturalitySlideWidthAudit — zero-axiom gate
for the reverse block-braiding primitive, the generic-WIDTH naturality square's soundness half (both colours,
seven widths incl. one far above natural), and the base slide at a generic-width left pad (WP-PROP r27).

Per-declaration `#assert_no_axioms` on the reverse block braiding (`strandPastBlockRev`) and its matrix pins /
forward-reverse-inverse, the mu-side and delta-side generic-width naturality-square endpoints + their
`decide`-checked soundness at widths 0..6, and the generic-width-pad CONV slides, PLUS the delivery markers —
AND an independent (non-fuel) `#print axioms` on the same public declarations.  The project `#assert_no_axioms`
macro is fuel-based; the independent `#print axioms` closes the gate on the `Decidable.decide` reductions
(propext-free, no `Classical`).  The star markers stay `= false` byte-intact (cross-file, not edited). -/

namespace FX1PolyAudit

-- A1 — the reverse block-braiding primitive + its matrix pins + the forward-reverse inverse.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrandPastBlockRev
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrandPastBlockRevOneMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrandPastBlockRevTwoMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrandPastBlockForwardReverseInverse

-- A2 — the mu-side generic-width naturality square endpoints + soundness at seven widths.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaPastMuFoldBlockLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaPastMuFoldBlockRight
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaPastMuFoldBlockSoundAtWidthZero
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaPastMuFoldBlockSoundAtWidthOne
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaPastMuFoldBlockSoundAtWidthTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaPastMuFoldBlockSoundAtWidthThree
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaPastMuFoldBlockSoundAtWidthFour
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaPastMuFoldBlockSoundAtWidthFive
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaPastMuFoldBlockSoundAtWidthSix

-- A3 — the delta-side generic-width naturality square endpoints + soundness (reverse braiding).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaPastDeltaFanBlockLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaPastDeltaFanBlockRight
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaPastDeltaFanBlockSoundAtWidthTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaPastDeltaFanBlockSoundAtWidthFour
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaPastDeltaFanBlockSoundAtWidthSix

-- A4 — the base slide at a generic-width left pad (CONV over the star scope, all pad widths).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuNaturalitySlideAtLeftPadWidth
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaNaturalitySlideAtLeftPadWidth

-- A5 — the delivery markers (incl. the walls that stay false).
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_reverseBlockBraidingShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_genericWidthNaturalitySquareSoundnessShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_baseSlideAtGenericPadWidthShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_genericWidthConvBlockThreadingStillWalled
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterGenericWidthSoundness
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_wideCollisionNaturalitySlideWidthLedgerShipped

-- Independent (non-fuel) axiom prints on the same public declarations — closing the gate on the
-- `Decidable.decide` reductions (propext-free) and the `SaturatedConvOverWithId` congruence plumbing.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrandPastBlockRev
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrandPastBlockRevTwoMatrix
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStrandPastBlockForwardReverseInverse
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaPastMuFoldBlockSoundAtWidthSix
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaPastDeltaFanBlockSoundAtWidthSix
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuNaturalitySlideAtLeftPadWidth
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaNaturalitySlideAtLeftPadWidth
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_genericWidthNaturalitySquareSoundnessShipped
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_genericWidthConvBlockThreadingStillWalled
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterGenericWidthSoundness
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_wideCollisionNaturalitySlideWidthLedgerShipped

end FX1PolyAudit
