import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcHeadExtractionArityDispatch

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcHeadExtractionArityDispatch — zero-axiom gate

Per-declaration zero-axiom gate for the cup/cap arity dispatch: the chained head extraction and
the whole cell reconstruction from the cup case alone.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.spineArcHeadExtractionChained_ofArityDispatch
#assert_no_axioms FX1Poly.Polygraph.adjunctionArcCellReconstruction_ofCupExtraction
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcHeadExtractionArityDispatch

end FX1PolyAudit
