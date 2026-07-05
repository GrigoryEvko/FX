import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupHeadRealizeAssembly

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupHeadRealizeAssembly — zero-axiom gate

Per-declaration zero-axiom gate for the cup-head discharge assembled modulo the orbit: the full
extraction conclusion from a located-bubble witness plus the tails cancel.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.cupHeadExtractionConclusion_ofLocatedBubbleAndCancel
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupHeadRealizeAssembly

end FX1PolyAudit
