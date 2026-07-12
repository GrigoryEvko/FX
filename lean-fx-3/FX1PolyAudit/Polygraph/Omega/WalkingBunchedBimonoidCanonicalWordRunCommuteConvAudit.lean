import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidCanonicalWordRunCommuteConv

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidCanonicalWordRunCommuteConvAudit — zero-axiom gate for
the CONV run-commute atoms (distant-commutation + braid at the `sigmaAt` word level), the whiskering-`aWordPow`
split reshape, and the exact whisker-coherence wall (WP-PROP r17).

Per-declaration `#assert_no_axioms` on every public theorem / pin / marker, PLUS independent (non-fuel)
`#print axioms` on the distant-commute matrix pins, the split reshape + its matrix pin, and every marker.  The
project `#assert_no_axioms` macro is fuel-based; the independent `#print axioms` closes the gate.  All decls are
public (no `private` helpers in this file). -/

namespace FX1PolyAudit

-- R1 — the distant-commute atom's matrix soundness (widths 4, 5) + the marker.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtDistantCommuteMatrixSharedFourZeroTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtDistantCommuteMatrixSharedFiveOneThree
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_distantCommuteAtomMatrixSoundAndNonVacuous

-- R2 — the buildable whiskering-`aWordPow` split reshape + its matrix pin + the marker.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtWhiskerSplitConv
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtWhiskerSplitMatrixShared
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_whiskeringSplitReshapeShipped

-- R3/R4 — the wall + reduction + B3 bill markers.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_runCommuteConvGatedOnWhiskerAssociatorAndUnitors
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_combFoldConvGatedOnRunCommuteAtoms
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterRunCommute
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_canonicalWordRunCommuteRoundSeventeenLedgerShipped

-- Independent (non-fuel) axiom prints — the theorems, the reshape, and every marker.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtDistantCommuteMatrixSharedFourZeroTwo
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtDistantCommuteMatrixSharedFiveOneThree
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtWhiskerSplitConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtWhiskerSplitMatrixShared
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_distantCommuteAtomMatrixSoundAndNonVacuous
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_whiskeringSplitReshapeShipped
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_runCommuteConvGatedOnWhiskerAssociatorAndUnitors
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_combFoldConvGatedOnRunCommuteAtoms
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterRunCommute
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_canonicalWordRunCommuteRoundSeventeenLedgerShipped

end FX1PolyAudit
