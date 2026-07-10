import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutMultiGapSplice

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutMultiGapSplice — zero-axiom gate for the multi-gap NF
forward assembly (wall-inert splice)

Per-declaration zero-axiom gate for the per-gap collapse, the three-gap word / normal form, the end-to-end splice
conv, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapCollapse
#assert_no_axioms FX1Poly.Polygraph.Amalgam.threeGapWord
#assert_no_axioms FX1Poly.Polygraph.Amalgam.threeGapWordNormalForm
#assert_no_axioms FX1Poly.Polygraph.Amalgam.threeGapSpliceConv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasMultiGapForwardSplice
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_multiGapFactorizationStaysWalled

end FX1PolyAudit
