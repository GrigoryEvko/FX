import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupSortComplete

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupSortComplete — zero-axiom gate

Per-declaration zero-axiom gate for the pure-cup completeness assembly: the mirrored sibling-cup
transposition, the prefix purity, and (when landed) the location induction and the top theorem
`pureCupSpine_sort`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.cupSwapStepMirror
#assert_no_axioms FX1Poly.Polygraph.allCupArity_prefix_ofAppend
#assert_no_axioms FX1Poly.Polygraph.chordShift_below
#assert_no_axioms FX1Poly.Polygraph.chordShift_above
#assert_no_axioms FX1Poly.Polygraph.atomicTraceEquiv_prefixCongr
#assert_no_axioms FX1Poly.Polygraph.cupSwapStepSmallerDetail
#assert_no_axioms FX1Poly.Polygraph.locateAux

end FX1PolyAudit
