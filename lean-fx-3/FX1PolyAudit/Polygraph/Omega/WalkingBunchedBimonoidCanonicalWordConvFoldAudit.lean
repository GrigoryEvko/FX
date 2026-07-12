import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidCanonicalWordConvFold

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidCanonicalWordConvFoldAudit — zero-axiom gate for the
CONV-fold spelling bridge: the dim-1 word-boundary facts and the whisker-over-vcomp `sigmaAt`-chain bridge
(WP-PROP r15, #2033).

Per-declaration `#assert_no_axioms` on every theorem / marker, PLUS independent (non-fuel) `#print axioms` on the
whisker-over-vcomp bridge, the boundary facts, and the marker.  The project `#assert_no_axioms` macro is
fuel-based; the independent `#print axioms` closes the gate. -/

namespace FX1PolyAudit

-- S0 — the dim-1 word-boundary facts.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAWordPowBoundarySource
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtBoundarySource
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermWordConsBoundarySource

-- S1 — the whisker-over-vcomp spelling bridge + its matrix-soundness pin + the marker.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaChainInvolutionWhiskerConv
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaChainInvolutionWhiskerMatrixShared
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_whiskerOverVcompSpellingBridgeShipped

-- S2 — the generic whisker-over-vcomp bridge + the CANCEL letter CONV + its pin + the marker.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWhiskerOverVcompConv
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCancelLetterConv
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCancelLetterMatrixShared
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_cancelLetterConvShipped

-- Independent (non-fuel) axiom prints on the boundary facts, the bridges, the CANCEL letter, and the markers.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAWordPowBoundarySource
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtBoundarySource
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaChainInvolutionWhiskerConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaChainInvolutionWhiskerMatrixShared
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWhiskerOverVcompConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCancelLetterConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCancelLetterMatrixShared
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_whiskerOverVcompSpellingBridgeShipped
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_cancelLetterConvShipped

end FX1PolyAudit
