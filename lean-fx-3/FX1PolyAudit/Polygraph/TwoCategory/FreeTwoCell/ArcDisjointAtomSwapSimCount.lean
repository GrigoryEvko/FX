import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcDisjointAtomSwapSimCount

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcDisjointAtomSwapSimCount — zero-axiom gate (MODE-COMMUTE r25)

Per-declaration zero-axiom gate for the r25 position-disjoint atom-swap brick: the r22 carrier bridge,
the disjoint CUP-swap `ArcStepSimCount` over the `WellFormedArcState` bundle, the two bundle-closure
preservation corollaries, the concrete cup fire + its snapshots, the cap-arm and mixed-arm scalar
disjoint-commutation probes, the overlapping-cap negative control (+ its well-formedness) and the
disjoint-window contrast, the shipped marker, and the four untouched-false honesty pins.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.
Registered in `AuditAll` (paired with the independent `#print axioms` witness). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.blockRotate_eq_compoundFreshBlockTransposition
#assert_no_axioms FX1Poly.Polygraph.arcDisjointCupSwapSimCount_ofWellFormed
#assert_no_axioms FX1Poly.Polygraph.arcDisjointCupSwap_redexWellFormed
#assert_no_axioms FX1Poly.Polygraph.arcDisjointCupSwap_reductWellFormed
#assert_no_axioms FX1Poly.Polygraph.disjointCupSwapSeed
#assert_no_axioms FX1Poly.Polygraph.disjointCupSwapSeed_isWellFormed
#assert_no_axioms FX1Poly.Polygraph.arcDisjointCupSwapFire
#assert_no_axioms FX1Poly.Polygraph.arcDisjointCupSwapFire_redexOpenWires
#assert_no_axioms FX1Poly.Polygraph.arcDisjointCupSwapFire_reductOpenWires
#assert_no_axioms FX1Poly.Polygraph.arcDisjointCupSwapFire_nextFreshAgree
#assert_no_axioms FX1Poly.Polygraph.disjointCapPairSeed
#assert_no_axioms FX1Poly.Polygraph.disjointCapSwap_loopsAgree
#assert_no_axioms FX1Poly.Polygraph.disjointCapSwap_openWiresAgree
#assert_no_axioms FX1Poly.Polygraph.disjointCapSwap_nextFreshAgree
#assert_no_axioms FX1Poly.Polygraph.disjointCapSwap_capEventNodesAgree
#assert_no_axioms FX1Poly.Polygraph.disjointCupCapSeed
#assert_no_axioms FX1Poly.Polygraph.disjointCupCapSwap_loopsAgree
#assert_no_axioms FX1Poly.Polygraph.disjointCupCapSwap_nextFreshAgree
#assert_no_axioms FX1Poly.Polygraph.overlappingCapSeed
#assert_no_axioms FX1Poly.Polygraph.overlappingCapSeed_isWellFormed
#assert_no_axioms FX1Poly.Polygraph.arcOverlappingCapSwap_loopsDiffer
#assert_no_axioms FX1Poly.Polygraph.arcDisjointCapSwap_loopsAgree_contrast
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasDisjointCupSwapSimOverBundle
#assert_no_axioms FX1Poly.Polygraph.arcDisjointCupSwap_swapRenameableProof2_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcDisjointCupSwap_disjointWhiskerSupport_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcDisjointCupSwap_partitionCommute_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcDisjointCupSwap_samePartitionFresh_stays_false

end FX1PolyAudit
