import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupHeadBoundary

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupHeadBoundary — zero-axiom gate

Per-declaration zero-axiom gate for the cup-head discharge's structural opening: the window
fit, the cod-boundary grows-by-two, and the composite-as-cup-step extract bridge.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupHeadWindowFits
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadCodBoundaryGrows
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadCompositeAsCupStep
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupHeadBoundary

end FX1PolyAudit
