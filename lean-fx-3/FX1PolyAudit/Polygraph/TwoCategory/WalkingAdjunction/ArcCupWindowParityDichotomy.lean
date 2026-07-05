import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupWindowParityDichotomy

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupWindowParityDichotomy — zero-axiom gate

Per-declaration zero-axiom gate for the cup-past-cup base-parity dichotomy: a cup never nests
strictly between another cup's legs, so the cup descent step has the same clean below/past
dichotomy the cap descent enjoys.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.adjunctionModeAtDistance_succ_ne_ofBothBase
#assert_no_axioms FX1Poly.Polygraph.adjunctionBaseWindowDichotomy
#assert_no_axioms FX1Poly.Polygraph.adjunctionCupAtomWindowDichotomy
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupWindowParityDichotomy

end FX1PolyAudit
