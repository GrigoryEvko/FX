import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDisjointWordBubble

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringDisjointWordBubble — zero-axiom gate (FC-3 r4, B3)

Per-declaration zero-axiom gate for the word-indexed bubble-to-front driver: the consuming swap producer, the
bubble witness, the trace-equivalence and word-chain consumption theorems, the non-vacuity witness, and the two
honesty markers.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.spineAtomSwap_of_wordFactorization
#assert_no_axioms FX1Poly.Polygraph.atomicTraceEquiv_of_wordBubblesToFront
#assert_no_axioms FX1Poly.Polygraph.spineTraceEquiv_of_wordBubblesToFront
#assert_no_axioms FX1Poly.Polygraph.spineBoundaryWordChained_of_wordBubblesToFront
#assert_no_axioms FX1Poly.Polygraph.stringWordBubble_equalLengthDistinctWord
#assert_no_axioms FX1Poly.Polygraph.stringWordBubbleLeft_equalLengthDistinctWord
#assert_no_axioms FX1Poly.Polygraph.fxString_hasWordBubbleToFront
#assert_no_axioms FX1Poly.Polygraph.fxString_hasWordBubbleSortAssembly

end FX1PolyAudit
