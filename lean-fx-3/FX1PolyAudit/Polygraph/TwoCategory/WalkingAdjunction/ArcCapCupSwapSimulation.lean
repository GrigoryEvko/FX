import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapCupSwapSimulation

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCapCupSwapSimulation — zero-axiom gate

Per-declaration zero-axiom gate for the CAP x CUP two-step core simulation (the mirror of
the CUP x CAP order): the order-T links exposure, the per-order root/count lemmas over the
shared merged links, the merged-count vanishing at fresh roots, the three transposition
field lemmas, and the assembled `ArcStepSimCount` between the two run orders of a cap-cup
disjoint-window swap.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.capCupSwap_linksT
#assert_no_axioms FX1Poly.Polygraph.capCupSwapT_root_old
#assert_no_axioms FX1Poly.Polygraph.capCupSwapT_root_triple
#assert_no_axioms FX1Poly.Polygraph.capCupSwapT_root_capEvent
#assert_no_axioms FX1Poly.Polygraph.capCupSwapT_root_above
#assert_no_axioms FX1Poly.Polygraph.capCupSwapT_countOld
#assert_no_axioms FX1Poly.Polygraph.capCupSwapS_root_old
#assert_no_axioms FX1Poly.Polygraph.capCupSwapS_root_capEvent
#assert_no_axioms FX1Poly.Polygraph.capCupSwapS_root_above
#assert_no_axioms FX1Poly.Polygraph.capCupSwapS_countOld
#assert_no_axioms FX1Poly.Polygraph.capCupSwap_countMergedZero
#assert_no_axioms FX1Poly.Polygraph.capCupSwap_rootComm
#assert_no_axioms FX1Poly.Polygraph.capCupSwap_cupCorr
#assert_no_axioms FX1Poly.Polygraph.capCupSwap_capCorr
#assert_no_axioms FX1Poly.Polygraph.arcStepSimCount_capCupSwap

end FX1PolyAudit
