import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidIdentityPointUnitor

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidIdentityPointUnitorAudit — zero-axiom gate for the
width-0 identity-point whisker unitor sibling presentation (WP-PROP r20, U1).

Per-declaration `#assert_no_axioms` on the fresh sibling scope, the matrix-soundness lemmas (`I_0 (+) M = M`),
the per-row soundness, the star-scope embedding, the unitor firings, the edge-letter bridge, and every marker,
PLUS an independent (non-fuel) `#print axioms` on the load-bearing declarations and every marker.  The project
`#assert_no_axioms` macro is fuel-based; the independent `#print axioms` closes the gate.  Only public
declarations are listed (the `List`-map helpers are `private`). -/

namespace FX1PolyAudit

-- U1.A — the fresh sibling scope.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStarScopeWithPointUnitor

-- U1.B — matrix soundness (`I_0 (+) M = M`, `M (+) I_0 = M`) + the per-row soundness.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDirectSumIdentityZeroLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDirectSumIdentityZeroRight
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidIdentityPointWhiskerRowEvalRespects

-- U1.C — the sibling absorbs the shipped star scope.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPointUnitorSiblingAbsorbsStar
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStarScopeEmbedsIntoPointUnitorSibling

-- U1.D — the row firings + the edge-letter unitor bridge.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidLeftIdPointUnitorConv
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRightIdPointUnitorConv
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtZeroUnitorConv

-- The markers.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_identityPointUnitorSiblingShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_identityPointUnitorMatrixSound
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_shippedStarScopeStillLacksUnitorNoFlip

-- Independent (non-fuel) axiom prints — the load-bearing declarations and every marker.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDirectSumIdentityZeroLeft
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDirectSumIdentityZeroRight
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidIdentityPointWhiskerRowEvalRespects
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStarScopeEmbedsIntoPointUnitorSibling
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtZeroUnitorConv
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_identityPointUnitorSiblingShipped
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_identityPointUnitorMatrixSound
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_shippedStarScopeStillLacksUnitorNoFlip

end FX1PolyAudit
