import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.StageComposite

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/StageComposite — zero-axiom gate

Per-declaration zero-axiom gate for the head-stage-composite trace invariant.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.SpineAtom.stageComposite
#assert_no_axioms FX1Poly.Polygraph.headStageComposite
#assert_no_axioms FX1Poly.Polygraph.SpineAtomSwap.headStageComposite_eq
#assert_no_axioms FX1Poly.Polygraph.AtomicTraceEquiv.headStageComposite_eq
#assert_no_axioms FX1Poly.Polygraph.FrontExtraction.frontStageComposite_eq

end FX1PolyAudit
