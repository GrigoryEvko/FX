import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcParityFold

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcParityFold — zero-axiom gate

Per-declaration zero-axiom gate for the opposite-class invariant's fold transport: the
per-atom dispatch, the whole-fold threading, and the canonical-seed capstone.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcEndTokenParity_stepArcAtom
#assert_no_axioms FX1Poly.Polygraph.arcEndTokenParity_processArcSpine_ofChained
#assert_no_axioms FX1Poly.Polygraph.arcEndTokenParity_ofChainedSpineList
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcParityFold

end FX1PolyAudit
