import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFinestLayout

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutFinestLayout — zero-axiom gate for the finest
decomposition + empty-gap admission + empty-gap free leg (WP-AMALG-2 r9, B1/B2)

Per-declaration zero-axiom gate for the finest gap-width shape, the r8-word truth-probe (the empty-gap admission),
and the empty-gap re-expression free leg.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.finestGapWidthsAux
#assert_no_axioms FX1Poly.Polygraph.Amalgam.finestGapWidths
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutPathTags
#assert_no_axioms FX1Poly.Polygraph.Amalgam.finestGapWidths_wallWall
#assert_no_axioms FX1Poly.Polygraph.Amalgam.finestGapWidths_wallGapWall
#assert_no_axioms FX1Poly.Polygraph.Amalgam.unitSplitsWall_dom_tags
#assert_no_axioms FX1Poly.Polygraph.Amalgam.unitSplitsWall_cod_tags
#assert_no_axioms FX1Poly.Polygraph.Amalgam.unitSplitsWall_dom_finestGapWidths
#assert_no_axioms FX1Poly.Polygraph.Amalgam.unitSplitsWall_cod_finestGapWidths
#assert_no_axioms FX1Poly.Polygraph.Amalgam.unitSplitsWall_finestSlotCount_domCod_eq
#assert_no_axioms FX1Poly.Polygraph.Amalgam.emptyGapPair
#assert_no_axioms FX1Poly.Polygraph.Amalgam.emptyGapLayout_conv_id
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasFinestDecompositionAdmission
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasEmptyGapFreeLeg

end FX1PolyAudit
