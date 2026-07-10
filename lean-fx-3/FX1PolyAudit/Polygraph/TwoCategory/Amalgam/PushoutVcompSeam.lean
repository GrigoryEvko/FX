import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutVcompSeam

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutVcompSeam — zero-axiom gate for the midPath vcomp seam +
the composed-r8 factorization (WP-AMALG-2 r9, B3/B4)

Per-declaration zero-axiom gate for the seam lemma, its `PushoutLayoutFactorization` packaging, the composed-r8
counterexample's shared block / half-cells / half-convs, the end-to-end factorization, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutFactorizeVcompSeam
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutFactorizeVcompLayout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.vcompSplitBlockPair
#assert_no_axioms FX1Poly.Polygraph.Amalgam.unitThenFaceLowerCell
#assert_no_axioms FX1Poly.Polygraph.Amalgam.vcompSplitBlockUpperConv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.vcompSplitBlockLowerConv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.vcompSplitBlockFactorization
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasMidPathVcompSeam
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_seamNotArbitraryCellCoverage

end FX1PolyAudit
