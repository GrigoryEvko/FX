import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.BareConvPatternMultiset

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.BareConvPatternMultiset — zero-axiom gate

Per-declaration zero-axiom gate for the bare-`TwoCellConv` PER-GENERATOR PATTERN-MULTISET — the sound,
non-additive invariant that is the SUP of the additive scalar tower, machine-checked to SEPARATE the r4 `wordCode`
collision, yet not proven complete (the finer Cartier–Foata clique-SEQUENCE is): the count-function carrier
`patternMultiplicity` with its bare-conv SOUNDNESS through interchange (`TwoCellStep.patternMultiplicity_eq`,
`TwoCellConv.patternMultiplicity_eq`); the r4-collision SEPARATION (`wcc_left_patternMultiplicity_L`,
`wcc_right_patternMultiplicity_L`, `wcc_not_conv_viaMultiset`) and the r1 / r2 cross-checks
(`whiskerExchange_patternMultiplicity_separates`, `cellLRRL_patternMultiplicity_separates`); the DECIDABLE sorted
canonical carrier (`listBoolLe`, `insertPat`, `mergePat`, `sortedPatternMultiset`, `listListBoolDecEq`) with its r4
forms and difference (`wcc_left_sortedPatternMultiset`, `wcc_right_sortedPatternMultiset`,
`wordCodeCollision_sortedPatternMultiset_differs`); and the honesty marker
(`fxMode_hasBareConvFlatPatternMultisetSoundAndSeparating`).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.patternMultiplicity
#assert_no_axioms FX1Poly.Polygraph.TwoCellStep.patternMultiplicity_eq
#assert_no_axioms FX1Poly.Polygraph.TwoCellConv.patternMultiplicity_eq
#assert_no_axioms FX1Poly.Polygraph.wcc_left_patternMultiplicity_L
#assert_no_axioms FX1Poly.Polygraph.wcc_right_patternMultiplicity_L
#assert_no_axioms FX1Poly.Polygraph.wcc_not_conv_viaMultiset
#assert_no_axioms FX1Poly.Polygraph.whiskerExchange_patternMultiplicity_separates
#assert_no_axioms FX1Poly.Polygraph.cellLRRL_patternMultiplicity_separates
#assert_no_axioms FX1Poly.Polygraph.listBoolLe
#assert_no_axioms FX1Poly.Polygraph.insertPat
#assert_no_axioms FX1Poly.Polygraph.mergePat
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.sortedPatternMultiset
#assert_no_axioms FX1Poly.Polygraph.listListBoolDecEq
#assert_no_axioms FX1Poly.Polygraph.wcc_left_sortedPatternMultiset
#assert_no_axioms FX1Poly.Polygraph.wcc_right_sortedPatternMultiset
#assert_no_axioms FX1Poly.Polygraph.wordCodeCollision_sortedPatternMultiset_differs
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasBareConvFlatPatternMultisetSoundAndSeparating

end FX1PolyAudit
