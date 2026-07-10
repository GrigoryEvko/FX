import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFinestGapMerge

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutFinestGapMerge — zero-axiom gate for the whisker-frame
gap-merge at the width level (WP-AMALG-2 r10, B2)

Per-declaration zero-axiom gate for the accumulator-shift primitive, the append merge law, the pure-`t` frame
contribution, and the r8 naive-concat refutation.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.bumpHead
#assert_no_axioms FX1Poly.Polygraph.Amalgam.finestGapWidthsAux_bumpHead
#assert_no_axioms FX1Poly.Polygraph.Amalgam.finestGapWidthsAux_nonempty
#assert_no_axioms FX1Poly.Polygraph.Amalgam.foldBodyAtTail
#assert_no_axioms FX1Poly.Polygraph.Amalgam.finestGapWidthsAux_append
#assert_no_axioms FX1Poly.Polygraph.Amalgam.finestGapWidths_tRunFrame
#assert_no_axioms FX1Poly.Polygraph.Amalgam.finestGapWidths_naiveConcatRefuted
#assert_no_axioms FX1Poly.Polygraph.Amalgam.finestGapWidths_frameMergesIntoBody
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasFinestGapMerge

end FX1PolyAudit
