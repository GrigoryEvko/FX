import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.Steiner.VaryingWhiskerReconstruct

/-! # FX1PolyAudit/Polygraph/Omega/Steiner/VaryingWhiskerReconstruct — zero-axiom gate (OMEGA-3 r3, B1).

Per-declaration `#assert_no_axioms` on the varying-whisker map-IN reconstruct: both left/right reconstructs,
both iffs, the two genuine verdicts, and the shipped marker. -/

namespace FX1PolyAudit

-- VaryingWhiskerReconstruct.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskeredVaryingWhisker_conv_of_linearizeFull_eq
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskeredVaryingWhisker_conv_iff_linearizeFull_eq
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskeredVaryingWhiskerRight_conv_of_linearizeFull_eq
#assert_no_axioms FX1Poly.Polygraph.Omega.whiskeredVaryingWhiskerRight_conv_iff_linearizeFull_eq
#assert_no_axioms FX1Poly.Polygraph.Omega.varyingWhisker_word_conv_withId
#assert_no_axioms FX1Poly.Polygraph.Omega.varyingWhisker_word_not_conv_withId
#assert_no_axioms FX1Poly.Polygraph.Omega.fxOmega3_varyingWhiskerReconstructShippedR3

end FX1PolyAudit
