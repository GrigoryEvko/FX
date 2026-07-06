import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupLastCupReadoff

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupLastCupReadoff — zero-axiom gate

Per-declaration zero-axiom gate for the last-cup short-chord foundations: the boundary-chain open-wire
tracker, the seed `nextFresh` lower bound, the chain-prefix inversion, and (once landed) the general-state
cup forward partner and the assembled `pureCupSpine_lastCup_isShortChord`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.processArcSpine_openWires_length_ofChainedAppend
#assert_no_axioms FX1Poly.Polygraph.processArcSpine_prefix_openWires_eq_lastDomBoundary
#assert_no_axioms FX1Poly.Polygraph.spineBoundaryChained_prefix_ofAppend
#assert_no_axioms FX1Poly.Polygraph.seedBottomCount_le_processArcSpine_nextFresh

end FX1PolyAudit
