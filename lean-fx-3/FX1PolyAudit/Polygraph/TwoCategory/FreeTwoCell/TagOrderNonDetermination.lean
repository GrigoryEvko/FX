import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TagOrderNonDetermination

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/TagOrderNonDetermination — zero-axiom gate

Per-declaration zero-axiom gate for the tag-order falsification: the tagged witness
traces and their two swaps, the equal-tag-lists/equivalent/unequal triple with its
headline, and the candidate-enumeration incompleteness corollary with its computed
evaluations.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.taggedBubbleSourceTrace
#assert_no_axioms FX1Poly.Polygraph.taggedBubbleMiddleTrace
#assert_no_axioms FX1Poly.Polygraph.taggedBubbleSlidTrace
#assert_no_axioms FX1Poly.Polygraph.taggedBubbleFirstSwap
#assert_no_axioms FX1Poly.Polygraph.taggedBubbleSecondSwap
#assert_no_axioms FX1Poly.Polygraph.taggedBubbleTraces_areEquivalent
#assert_no_axioms FX1Poly.Polygraph.taggedBubbleTraces_haveEqualTagLists
#assert_no_axioms FX1Poly.Polygraph.taggedBubbleTraces_areNotEqual
#assert_no_axioms FX1Poly.Polygraph.tagOrder_doesNotDetermineClassMember
#assert_no_axioms FX1Poly.Polygraph.bubbleSlidTrace
#assert_no_axioms FX1Poly.Polygraph.bubbleSlidTrace_isEquivalentToSeed
#assert_no_axioms FX1Poly.Polygraph.bubbleClassEnumerationComputes
#assert_no_axioms FX1Poly.Polygraph.bubbleSlidTrace_isFreshAgainstCandidates
#assert_no_axioms FX1Poly.Polygraph.bubbleSlidTrace_isNotEnumerated
#assert_no_axioms FX1Poly.Polygraph.classEnumerationCandidate_isNotComplete

end FX1PolyAudit
