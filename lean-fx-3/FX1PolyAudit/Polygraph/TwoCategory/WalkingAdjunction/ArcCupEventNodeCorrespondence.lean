import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupEventNodeCorrespondence

/-! # FX1PolyAudit/…/ArcCupEventNodeCorrespondence — zero-axiom gate

Per-declaration zero-axiom gate for the cup-event-node ↔ cup-atom ordering correspondence: the arc
fold only grows `cupEventNodes` at the front (`processArcSpine_cupEventNodes_consSuffix`), so a cup
head's event node `bottomCount + 2` is the LAST element (`arcSeedHeadCup_eventNode_isLast`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.IsConsSuffix.trans
#assert_no_axioms FX1Poly.Polygraph.stepArcAtom_cupEventNodes_consSuffix
#assert_no_axioms FX1Poly.Polygraph.processArcSpine_cupEventNodes_consSuffix
#assert_no_axioms FX1Poly.Polygraph.stepCupHead_cupEventNodes
#assert_no_axioms FX1Poly.Polygraph.processArcSpine_headCup_consSuffix
#assert_no_axioms FX1Poly.Polygraph.arcSeedHeadCup_eventNode_isLast

end FX1PolyAudit
