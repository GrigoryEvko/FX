import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringColouredRefinement

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringColouredRefinement — zero-axiom gate

Per-declaration zero-axiom gate for the r5 decisive check: the helper 1-cells, the predicted colour-ambiguous
internal-loop witness (`stringMixedBubbleCup`) and its `loops = 0` / bare-cup-indistinguishability / generator-count
facts, the convertible colour-2 bubble on an `F`-context (`stringMixedBubbleOnLeft` + its straighten-to-identity and
matching-consistency), the genuine-`G`-snake-ambiguity-is-convertible bundle, the loop-freedom of every witness, the
per-colour-loop vacuity lemma, and the three markers (no internal colour loop; per-colour loop refinement vacuous;
`ColouredDiagramType` NOT too coarse — r5 hypothesis refuted).
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringLeftPath
#assert_no_axioms FX1Poly.Polygraph.stringRightPath
#assert_no_axioms FX1Poly.Polygraph.stringMixedBubbleInsert
#assert_no_axioms FX1Poly.Polygraph.stringMixedBubbleClose
#assert_no_axioms FX1Poly.Polygraph.stringMixedBubbleCup
#assert_no_axioms FX1Poly.Polygraph.stringMixedBubbleCup_matchingOf
#assert_no_axioms FX1Poly.Polygraph.stringMixedBubbleCup_matchingOf_eq_unitLower
#assert_no_axioms FX1Poly.Polygraph.stringMixedBubbleCup_loops_zero
#assert_no_axioms FX1Poly.Polygraph.stringMixedBubbleCup_generatorCount
#assert_no_axioms FX1Poly.Polygraph.stringMixedBubbleOnLeft
#assert_no_axioms FX1Poly.Polygraph.stringMixedBubbleOnLeft_conv_identity
#assert_no_axioms FX1Poly.Polygraph.stringMixedBubbleOnLeft_matchingOf_eq_identity
#assert_no_axioms FX1Poly.Polygraph.stringGSnakes_colourAmbiguous_and_convertible
#assert_no_axioms FX1Poly.Polygraph.stringWitnesses_loops_zero
#assert_no_axioms FX1Poly.Polygraph.stringPerColourLoopSplit_zero_ofLoopsZero
#assert_no_axioms FX1Poly.Polygraph.fxString_hasInternalColourLoop
#assert_no_axioms FX1Poly.Polygraph.fxString_hasPerColourLoopRefinementContent
#assert_no_axioms FX1Poly.Polygraph.fxString_hasColouredInvariantTooCoarse

end FX1PolyAudit
