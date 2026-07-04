import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupCupSwapSimulation

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupCupSwapSimulation — zero-axiom gate

Per-declaration zero-axiom gate for the CUP x CUP two-step core simulation: the three
position-generic transposition field lemmas (rootComm / cupCorr / capCorr over the cup root
atlas) and the assembled `ArcStepSimCount` between the two run orders of a cup-cup
disjoint-window swap.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.cupPair_rootComm_transposition
#assert_no_axioms FX1Poly.Polygraph.cupPair_cupCorr_transposition
#assert_no_axioms FX1Poly.Polygraph.cupPair_capCorr_transposition
#assert_no_axioms FX1Poly.Polygraph.arcStepSimCount_cupCupSwap

end FX1PolyAudit
