import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcDisjointCapMixedSwapSimCount

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcDisjointCapMixedSwapSimCountAxiomWitness — independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gate in the per-file twin) over every declaration of the r26 CAP x CAP and MIXED
disjoint atom-swap arms: the three arms' seeds / forests / well-formedness, their redex/reduct
bundle-closure corollaries (general + concrete), the block-swap carriers' `openMap` / bounded `rootComm` /
`cupCorr` / `capCorr` / scalar fields, the component-shared and window-overlap negative controls, the
shipped marker, and the four untouched-false honesty pins.

Each must print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.capCapDisjointSeed
#print axioms FX1Poly.Polygraph.capCapDisjointSeed_isForest
#print axioms FX1Poly.Polygraph.capCapDisjointSeed_isWellFormed
#print axioms FX1Poly.Polygraph.capCapDisjointRedex
#print axioms FX1Poly.Polygraph.capCapDisjointReduct
#print axioms FX1Poly.Polygraph.capCapDisjointSwap_redexWellFormed
#print axioms FX1Poly.Polygraph.capCapDisjointSwap_reductWellFormed
#print axioms FX1Poly.Polygraph.capCapDisjointRedex_isWellFormed
#print axioms FX1Poly.Polygraph.capCapDisjointReduct_isWellFormed
#print axioms FX1Poly.Polygraph.capCapDisjointSwap_nextFreshAgree
#print axioms FX1Poly.Polygraph.capCapDisjointSwap_loopsAgree
#print axioms FX1Poly.Polygraph.capCapDisjointSwap_capEventNodesAgree
#print axioms FX1Poly.Polygraph.capCapDisjointSwap_openMap
#print axioms FX1Poly.Polygraph.capCapDisjointSwap_rootCommOnSupport
#print axioms FX1Poly.Polygraph.capCapDisjointSwap_cupCorrOnSupport
#print axioms FX1Poly.Polygraph.capCapDisjointSwap_capCorrOnSupport
#print axioms FX1Poly.Polygraph.mixedCupCapSeed
#print axioms FX1Poly.Polygraph.mixedCupCapSeed_isForest
#print axioms FX1Poly.Polygraph.mixedCupCapSeed_isWellFormed
#print axioms FX1Poly.Polygraph.mixedCupCapRedex
#print axioms FX1Poly.Polygraph.mixedCupCapReduct
#print axioms FX1Poly.Polygraph.mixedCupCapSwap_redexWellFormed
#print axioms FX1Poly.Polygraph.mixedCupCapSwap_reductWellFormed
#print axioms FX1Poly.Polygraph.mixedCupCapRedex_isWellFormed
#print axioms FX1Poly.Polygraph.mixedCupCapReduct_isWellFormed
#print axioms FX1Poly.Polygraph.mixedCupCapSwap_nextFreshAgree
#print axioms FX1Poly.Polygraph.mixedCupCapSwap_loopsAgree
#print axioms FX1Poly.Polygraph.mixedCupCapSwap_openMap
#print axioms FX1Poly.Polygraph.mixedCupCapSwap_rootCommOnSupport
#print axioms FX1Poly.Polygraph.mixedCupCapSwap_cupCorrOnSupport
#print axioms FX1Poly.Polygraph.mixedCupCapSwap_capCorrOnSupport
#print axioms FX1Poly.Polygraph.mixedCapCupSeed
#print axioms FX1Poly.Polygraph.mixedCapCupSeed_isForest
#print axioms FX1Poly.Polygraph.mixedCapCupSeed_isWellFormed
#print axioms FX1Poly.Polygraph.mixedCapCupCapFirst
#print axioms FX1Poly.Polygraph.mixedCapCupCupFirst
#print axioms FX1Poly.Polygraph.mixedCapCupSwap_capFirstWellFormed
#print axioms FX1Poly.Polygraph.mixedCapCupSwap_cupFirstWellFormed
#print axioms FX1Poly.Polygraph.mixedCapCupCapFirst_isWellFormed
#print axioms FX1Poly.Polygraph.mixedCapCupCupFirst_isWellFormed
#print axioms FX1Poly.Polygraph.mixedCapCupSwap_nextFreshAgree
#print axioms FX1Poly.Polygraph.mixedCapCupSwap_loopsAgree
#print axioms FX1Poly.Polygraph.mixedCapCupSwap_openMap
#print axioms FX1Poly.Polygraph.mixedCapCupSwap_rootCommOnSupport
#print axioms FX1Poly.Polygraph.mixedCapCupSwap_cupCorrOnSupport
#print axioms FX1Poly.Polygraph.mixedCapCupSwap_capCorrOnSupport
#print axioms FX1Poly.Polygraph.capCapComponentShareSeed
#print axioms FX1Poly.Polygraph.capCapComponentShareSeed_isForest
#print axioms FX1Poly.Polygraph.capCapComponentShareSeed_isWellFormed
#print axioms FX1Poly.Polygraph.capCapComponentShareSeed_readsShareComponent
#print axioms FX1Poly.Polygraph.capCapComponentShareRedex
#print axioms FX1Poly.Polygraph.capCapComponentShareReduct
#print axioms FX1Poly.Polygraph.capCapComponentShareSwap_rootDiverges
#print axioms FX1Poly.Polygraph.capCapComponentShareSwap_rootValues
#print axioms FX1Poly.Polygraph.overlappingCapControlSeed
#print axioms FX1Poly.Polygraph.overlappingCapControlSeed_isForest
#print axioms FX1Poly.Polygraph.overlappingCapControlSeed_isWellFormed
#print axioms FX1Poly.Polygraph.overlappingCapControlSwap_loopsDiffer
#print axioms FX1Poly.Polygraph.fxMode_hasDisjointCapMixedSwapSupportVerified
#print axioms FX1Poly.Polygraph.arcDisjointCapMixedSwap_swapRenameableProof2_stays_false
#print axioms FX1Poly.Polygraph.arcDisjointCapMixedSwap_disjointWhiskerSupport_stays_false
#print axioms FX1Poly.Polygraph.arcDisjointCapMixedSwap_partitionCommute_stays_false
#print axioms FX1Poly.Polygraph.arcDisjointCapMixedSwap_samePartitionFresh_stays_false

end FX1PolyAudit
