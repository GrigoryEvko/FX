import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupChainedExtract

/-! # FX1PolyAudit/…/ArcCupChainedExtract — zero-axiom gate

Per-declaration zero-axiom gate for the cup-head extract with `legsSeparate` discharged: on the
chained, base-parity-window fragment the capstone transport holds from `(windowFits,
windowParityIsBase, chained)` alone, wiring in the loop-freedom payoff `arcCupHeadFolded_legsSeparate`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_extractArc_ofChained
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupChainedExtract

end FX1PolyAudit
