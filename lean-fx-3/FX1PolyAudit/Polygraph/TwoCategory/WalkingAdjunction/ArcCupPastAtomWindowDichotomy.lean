import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupPastAtomWindowDichotomy

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupPastAtomWindowDichotomy — zero-axiom gate

Per-declaration zero-axiom gate for the cup descent's per-step disjointness: a cup passes any
cup-or-cap prefix atom below-or-past, unconditionally.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.adjunctionCupPastAtomWindowDichotomy
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupPastAtomWindowDichotomy

end FX1PolyAudit
