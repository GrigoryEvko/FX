import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcDisciplineFold

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcDisciplineFold — zero-axiom gate

Per-declaration zero-axiom gate for the typed-ends discipline fold (peel campaign C,
fold assembly): the arity dispatch equations, the cup/cap forest step, the per-atom
preservation, the whole-spine fold, and the canonical-seed capstone.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stepArcAtom_eq_stepCupArc
#assert_no_axioms FX1Poly.Polygraph.stepArcAtom_eq_stepCapArc
#assert_no_axioms FX1Poly.Polygraph.isUnionFindForest_stepArcAtom_ofCupOrCap
#assert_no_axioms FX1Poly.Polygraph.arcOpenEndsDiscipline_stepArcAtom
#assert_no_axioms FX1Poly.Polygraph.arcOpenEndsDiscipline_processArcSpine
#assert_no_axioms FX1Poly.Polygraph.arcOpenEndsDiscipline_ofChainedSpineList

end FX1PolyAudit
