import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapPeel

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcSwapPeel — zero-axiom gate

Per-declaration zero-axiom gate for the peel: arc extraction is invariant along the whole
atomic trace equivalence at the walking adjunction.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.extractArc_eq_of_atomicTraceEquiv

end FX1PolyAudit
