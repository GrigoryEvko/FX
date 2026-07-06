import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcNonCrossingFold

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcNonCrossingFold — zero-axiom gate

Per-declaration zero-axiom gate for the non-crossing fold transport (cap rung D2a-iv, fold): the
per-atom step, the whole-fold transport threading census-and-non-crossing, and the canonical-seed
capstone.  The private range plumbing is covered transitively.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcNonCrossing_stepArcAtom
#assert_no_axioms FX1Poly.Polygraph.arcNonCrossing_processArcSpine_ofChained
#assert_no_axioms FX1Poly.Polygraph.arcNonCrossing_ofChainedSpineList

end FX1PolyAudit
