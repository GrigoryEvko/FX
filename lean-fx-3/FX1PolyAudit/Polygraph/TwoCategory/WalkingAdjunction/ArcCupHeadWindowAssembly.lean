import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupHeadWindowAssembly

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupHeadWindowAssembly — zero-axiom gate

Per-declaration zero-axiom gate for the thinned cup-head discharge: the four-pin assembly with the
codomain-arity pin (arity dichotomy) and the dom-boundary pin (bubble-transported chain) derived, so
the residual is exactly the window pin + the cancel.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.cupHeadExtractionConclusion_ofLocatedBubbleWindowAndCancel
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupHeadWindowAssembly

end FX1PolyAudit
