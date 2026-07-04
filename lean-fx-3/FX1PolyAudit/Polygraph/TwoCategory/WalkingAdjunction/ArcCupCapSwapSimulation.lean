import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupCapSwapSimulation

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupCapSwapSimulation — zero-axiom gate

Per-declaration zero-axiom gate for the CUP x CAP two-step core simulation: the past-the-pair
read collapses, the order-S links exposure, the per-order root/count lemmas over the shared
merged links, the three transposition field lemmas, and the assembled `ArcStepSimCount`
between the two run orders of a cup-cap disjoint-window swap.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.natListGetAt_pastInsertedPair
#assert_no_axioms FX1Poly.Polygraph.natListGetAt_pastInsertedPair_succ
#assert_no_axioms FX1Poly.Polygraph.cupCapSwap_linksS
#assert_no_axioms FX1Poly.Polygraph.cupCapSwapS_root_old
#assert_no_axioms FX1Poly.Polygraph.cupCapSwapS_root_triple
#assert_no_axioms FX1Poly.Polygraph.cupCapSwapS_root_capEvent
#assert_no_axioms FX1Poly.Polygraph.cupCapSwapS_root_above
#assert_no_axioms FX1Poly.Polygraph.cupCapSwapS_countOld
#assert_no_axioms FX1Poly.Polygraph.cupCapSwapT_root_old
#assert_no_axioms FX1Poly.Polygraph.cupCapSwapT_root_capEvent
#assert_no_axioms FX1Poly.Polygraph.cupCapSwapT_root_above
#assert_no_axioms FX1Poly.Polygraph.cupCapSwapT_countOld
#assert_no_axioms FX1Poly.Polygraph.cupCapSwap_countMergedZero
#assert_no_axioms FX1Poly.Polygraph.cupCapSwap_rootComm
#assert_no_axioms FX1Poly.Polygraph.cupCapSwap_cupCorr
#assert_no_axioms FX1Poly.Polygraph.cupCapSwap_capCorr
#assert_no_axioms FX1Poly.Polygraph.arcStepSimCount_cupCapSwap

end FX1PolyAudit
