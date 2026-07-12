import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcDisjointAtomSwapSimCount

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcDisjointAtomSwapSimCountAxiomWitness — independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gate in the per-file twin) over every declaration of the r25
position-disjoint atom-swap brick: the r22 carrier bridge, the disjoint CUP-swap `ArcStepSimCount` over
the bundle, the two bundle-closure preservation corollaries, the concrete cup fire + its snapshots, the
cap-arm and mixed-arm scalar disjoint-commutation probes, the overlapping-cap negative control (+ its
well-formedness) and the disjoint-window contrast, the shipped marker, and the four untouched-false
honesty pins.

Each must print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.blockRotate_eq_compoundFreshBlockTransposition
#print axioms FX1Poly.Polygraph.arcDisjointCupSwapSimCount_ofWellFormed
#print axioms FX1Poly.Polygraph.arcDisjointCupSwap_redexWellFormed
#print axioms FX1Poly.Polygraph.arcDisjointCupSwap_reductWellFormed
#print axioms FX1Poly.Polygraph.disjointCupSwapSeed
#print axioms FX1Poly.Polygraph.disjointCupSwapSeed_isWellFormed
#print axioms FX1Poly.Polygraph.arcDisjointCupSwapFire
#print axioms FX1Poly.Polygraph.arcDisjointCupSwapFire_redexOpenWires
#print axioms FX1Poly.Polygraph.arcDisjointCupSwapFire_reductOpenWires
#print axioms FX1Poly.Polygraph.arcDisjointCupSwapFire_nextFreshAgree
#print axioms FX1Poly.Polygraph.disjointCapPairSeed
#print axioms FX1Poly.Polygraph.disjointCapSwap_loopsAgree
#print axioms FX1Poly.Polygraph.disjointCapSwap_openWiresAgree
#print axioms FX1Poly.Polygraph.disjointCapSwap_nextFreshAgree
#print axioms FX1Poly.Polygraph.disjointCapSwap_capEventNodesAgree
#print axioms FX1Poly.Polygraph.disjointCupCapSeed
#print axioms FX1Poly.Polygraph.disjointCupCapSwap_loopsAgree
#print axioms FX1Poly.Polygraph.disjointCupCapSwap_nextFreshAgree
#print axioms FX1Poly.Polygraph.overlappingCapSeed
#print axioms FX1Poly.Polygraph.overlappingCapSeed_isWellFormed
#print axioms FX1Poly.Polygraph.arcOverlappingCapSwap_loopsDiffer
#print axioms FX1Poly.Polygraph.arcDisjointCapSwap_loopsAgree_contrast
#print axioms FX1Poly.Polygraph.fxMode_hasDisjointCupSwapSimOverBundle
#print axioms FX1Poly.Polygraph.arcDisjointCupSwap_swapRenameableProof2_stays_false
#print axioms FX1Poly.Polygraph.arcDisjointCupSwap_disjointWhiskerSupport_stays_false
#print axioms FX1Poly.Polygraph.arcDisjointCupSwap_partitionCommute_stays_false
#print axioms FX1Poly.Polygraph.arcDisjointCupSwap_samePartitionFresh_stays_false

end FX1PolyAudit
