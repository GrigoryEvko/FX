import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.BareConvWordCodeCompleteness

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.BareConvWordCodeCompleteness — zero-axiom gate

Per-declaration zero-axiom gate for the bare-`TwoCellConv` WORD-CODE COMPLETENESS refutation: the two-generator
Godement collision pair `wordCodeCollisionLeft` / `wordCodeCollisionRight` (built on the `@`-pinned single nil-left
whisker `unitWhiskeredLeftByNil`) with its `generatorCount` / `isInterchangeNormal` smokes; the EQUAL `wordCode`
(`wordCodeCollision_wordCode_eq`); the DISTINCT `coCrossSum` (`wordCodeCollisionLeft_coCrossSum`,
`wordCodeCollisionRight_coCrossSum`, `wordCodeCollision_coCrossSum_differs`); the cast-free `TwoCellConvFull`
(`wordCodeCollision_convFull`); the NOT-bare refutation (`wordCodeCollision_not_twoCellConv`); the r4-PRIMARY
completeness refutation (`wordCode_not_complete`); and the honesty marker
(`fxMode_hasBareConvWordCodeIncompleteProven`).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.unitWhiskeredLeftByNil
#assert_no_axioms FX1Poly.Polygraph.wordCodeCollisionLeft
#assert_no_axioms FX1Poly.Polygraph.wordCodeCollisionRight
#assert_no_axioms FX1Poly.Polygraph.wordCodeCollisionLeft_generatorCount
#assert_no_axioms FX1Poly.Polygraph.wordCodeCollisionRight_generatorCount
#assert_no_axioms FX1Poly.Polygraph.wordCodeCollisionLeft_isInterchangeNormal
#assert_no_axioms FX1Poly.Polygraph.wordCodeCollisionRight_isInterchangeNormal
#assert_no_axioms FX1Poly.Polygraph.wordCodeCollision_wordCode_eq
#assert_no_axioms FX1Poly.Polygraph.wordCodeCollisionLeft_coCrossSum
#assert_no_axioms FX1Poly.Polygraph.wordCodeCollisionRight_coCrossSum
#assert_no_axioms FX1Poly.Polygraph.wordCodeCollision_coCrossSum_differs
#assert_no_axioms FX1Poly.Polygraph.wordCodeCollision_convFull
#assert_no_axioms FX1Poly.Polygraph.wordCodeCollision_not_twoCellConv
#assert_no_axioms FX1Poly.Polygraph.wordCode_not_complete
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasBareConvWordCodeIncompleteProven

end FX1PolyAudit
