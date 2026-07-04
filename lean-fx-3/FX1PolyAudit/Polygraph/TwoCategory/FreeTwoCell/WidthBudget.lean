import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.WidthBudget

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/WidthBudget — zero-axiom gate

Per-declaration zero-axiom gate for the width-budget arithmetic: the crude growth
budget, the per-atom width facts, the chained width bound, the budget's class
invariance, and the universe-facing member bound.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.traceGrowthBudget
#assert_no_axioms FX1Poly.Polygraph.SpineAtom.codBoundaryLength_le
#assert_no_axioms FX1Poly.Polygraph.SpineAtom.leftContextLength_le_domBoundaryLength
#assert_no_axioms FX1Poly.Polygraph.SpineAtom.rightContextLength_le_domBoundaryLength
#assert_no_axioms FX1Poly.Polygraph.spineBoundaryChained_boundsAtomWidth
#assert_no_axioms FX1Poly.Polygraph.AtomicTraceEquiv.growthBudgetEq
#assert_no_axioms FX1Poly.Polygraph.memberAtomWidth_bounded_ofSeed

end FX1PolyAudit
