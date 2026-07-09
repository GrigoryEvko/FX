import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanStaircase

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringFussCatalanStaircase — zero-axiom gate (FC-3 B)

Per-declaration zero-axiom gate for the FC-3 staircase MEASURE read-off: the structural-weight neutrality lemmas
(whisker / cast on `generatorCount` and `size`), the four-colour CANCEL `generatorCount` drops, the EXTEND
`generatorCount`-neutral + `size`-drop pair, and the pure-CANCEL primary descent.  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringWhiskerLeft_generatorCount
#assert_no_axioms FX1Poly.Polygraph.stringWhiskerRight_generatorCount
#assert_no_axioms FX1Poly.Polygraph.stringCastBoundary_generatorCount
#assert_no_axioms FX1Poly.Polygraph.stringWhiskerLeft_size
#assert_no_axioms FX1Poly.Polygraph.stringWhiskerRight_size
#assert_no_axioms FX1Poly.Polygraph.stringCastBoundary_size
#assert_no_axioms FX1Poly.Polygraph.stringCancelSnakeGlo_dropsTwo
#assert_no_axioms FX1Poly.Polygraph.stringCancelSnakeGhi_dropsTwo
#assert_no_axioms FX1Poly.Polygraph.stringCancelSnakeH_dropsTwo
#assert_no_axioms FX1Poly.Polygraph.stringExtendByIdentity_generatorCount_neutral
#assert_no_axioms FX1Poly.Polygraph.stringExtendByIdentity_size_dropsTwo
#assert_no_axioms FX1Poly.Polygraph.stringSnakeStackF_generatorCount_descends
#assert_no_axioms FX1Poly.Polygraph.fxString_hasStaircaseMeasure
#assert_no_axioms FX1Poly.Polygraph.fxString_hasStaircaseDriver

end FX1PolyAudit
