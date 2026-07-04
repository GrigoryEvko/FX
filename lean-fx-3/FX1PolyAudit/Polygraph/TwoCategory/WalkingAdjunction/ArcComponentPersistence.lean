import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcComponentPersistence

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcComponentPersistence — zero-axiom gate

Per-declaration zero-axiom gate for the component-persistence substrate (peel campaign H,
extract-correspondence substrate): per-step and whole-spine monotonicity of same-component
facts through the arc fold, the query-transfer helper, and the four persistent head-seed
joins at the folded end states.  The private range plumbing is covered transitively.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.isSameComponent_congrOfLinked
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_stepCupArc_ofBase
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_stepCapArc_ofBase
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_stepArcAtom_ofBase
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_processArcSpine_ofBase
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_eventLegLinked
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_legsLinked
#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_eventWireLinked
#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_consumedPairLinked

end FX1PolyAudit
