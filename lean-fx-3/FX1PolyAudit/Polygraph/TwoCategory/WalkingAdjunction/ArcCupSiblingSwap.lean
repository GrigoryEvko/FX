import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupSiblingSwap

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupSiblingSwap — zero-axiom gate

Per-declaration zero-axiom gate for the pure-cup sort's transposition atoms: the empty base case
and the sibling-cup transposition (both a trace step and arc-preserving).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.pureCupSpine_sort_nil
#assert_no_axioms FX1Poly.Polygraph.cupSwapStep

end FX1PolyAudit
