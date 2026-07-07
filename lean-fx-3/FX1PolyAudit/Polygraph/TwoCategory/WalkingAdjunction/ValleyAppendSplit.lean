import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyAppendSplit

/-! # FX1PolyAudit/…/ValleyAppendSplit — zero-axiom gate

Per-declaration zero-axiom gate for Piece I of the fib-3 gate: the cup block's loop-preservation
(`processSpine_loops_ofAllCupArity`) and the LOOP leg of the valley-append split (`matchingOf_loops_split`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.processSpine_loops_ofAllCupArity
#assert_no_axioms FX1Poly.Polygraph.matchingOf_loops_split
#assert_no_axioms FX1Poly.Polygraph.stepCup_isSameComponent_bottom
#assert_no_axioms FX1Poly.Polygraph.processSpine_isSameComponent_bottom_ofAllCupArity
#assert_no_axioms FX1Poly.Polygraph.spineHasCupCapAtoms_ofAllCapArity
#assert_no_axioms FX1Poly.Polygraph.spineHasCupCapAtoms_ofAllCupArity
#assert_no_axioms FX1Poly.Polygraph.valleysWithBlockMatchingEq_spineTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasValleyAppendSplitLoopAndFrame

end FX1PolyAudit
