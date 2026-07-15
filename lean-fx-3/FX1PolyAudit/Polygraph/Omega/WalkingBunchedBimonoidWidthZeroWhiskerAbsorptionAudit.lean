import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidWidthZeroWhiskerAbsorption

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidWidthZeroWhiskerAbsorptionAudit — zero-axiom gate for the width-0-whisker absorptions: eta over the unital scope, mu over the associative scope (the first muAssoc consumer), the sigma case honestly open. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidEtaWhiskerIdOne
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuWhiskerIdOne
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidEtaWhiskerIdOneAbsorbedUnital
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuWhiskerPivot
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuWhiskerPivotToMuWhisker
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuWhiskerPivotToMu
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuWhiskerIdOneAbsorbedAssociative
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_widthZeroWhiskerAbsorptionTemplateShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_sigmaWidthZeroWhiskerAbsorptionStillOpen

-- Independent (non-fuel) axiom prints on the spine.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidEtaWhiskerIdOneAbsorbedUnital
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuWhiskerIdOneAbsorbedAssociative

end FX1PolyAudit
