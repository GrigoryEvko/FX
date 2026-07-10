import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringCapPinWordChain

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringCapPinWordChain — zero-axiom gate (STRING-JOINT r2, WALL 2 brick B)

Per-declaration zero-axiom gate for the reachable-`capPin` fold over the boundary-WORD chain: the label companion
arity reductions, the empty-middle collapse, the seed open-wire length, the label-boundary-word tracking invariant,
the reachable-`capPin` fold predicate and its word-chain discharge / cell-level capstone, the two non-vacuity witnesses,
and the honesty marker.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.advanceLabels_ofCupArity
#assert_no_axioms FX1Poly.Polygraph.advanceLabels_ofCapArity
#assert_no_axioms FX1Poly.Polygraph.pathLabels_lengthZero_nil
#assert_no_axioms FX1Poly.Polygraph.stringInitialWireState_openWires_length
#assert_no_axioms FX1Poly.Polygraph.stringAdvanceLabels_tracksWordChain
#assert_no_axioms FX1Poly.Polygraph.StringCapPinAlongFold
#assert_no_axioms FX1Poly.Polygraph.stringCapPinAlongFold_ofWordChain
#assert_no_axioms FX1Poly.Polygraph.stringCapPinAlongFold_fromCell
#assert_no_axioms FX1Poly.Polygraph.stringCapPinAlongFold_stringCounitLower
#assert_no_axioms FX1Poly.Polygraph.stringCapPinAlongFold_stringCrossLevelCell
#assert_no_axioms FX1Poly.Polygraph.fxString_hasReachableCapPinFold

end FX1PolyAudit
