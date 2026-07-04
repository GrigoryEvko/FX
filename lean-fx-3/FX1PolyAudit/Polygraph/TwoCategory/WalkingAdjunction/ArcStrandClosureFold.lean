import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcStrandClosureFold

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcStrandClosureFold — zero-axiom gate

Per-declaration zero-axiom gate for the closed-strand fold (peel campaign H, strand-closure
rung 2): the per-step invariant preservations, the per-atom dispatch, and the two
whole-spine folds (invariant at the end state + end-to-start query stability).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcStrandClosure_stepCupArc
#assert_no_axioms FX1Poly.Polygraph.arcStrandClosure_stepCapArc
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_stepArcAtom_queriesStable
#assert_no_axioms FX1Poly.Polygraph.arcStrandClosure_stepArcAtom
#assert_no_axioms FX1Poly.Polygraph.arcStrandClosure_processArcSpine
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_processArcSpine_queriesStable

end FX1PolyAudit
