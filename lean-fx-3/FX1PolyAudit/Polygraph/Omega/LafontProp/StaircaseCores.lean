import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.LafontProp.StaircaseCores

/-! # FX1PolyAudit.Polygraph.Omega.LafontProp.StaircaseCores — zero-axiom gate
(LAFONT-REPAIR stage 2 phase 3: the mu and delta bottom cores)

Per-declaration zero-axiom gate for the staircase-cores file: the crossing-pair kit, the
four mirrored naturality rows, the pad-window composition helpers and two-sided pad
congruence, SCALE-TAU with its mirror, the four-strand add-tree kit, SCALE-MU, the
five-strand merge-route alignment, the GADGET-MU spines and assembly, THE MU FAN-DUPLICATION
CORE with its inhabitant of the live open Prop, SCALE-FUSION, the copy-tree kit, the
five-strand copy-route alignment, GADGET-DELTA, THE DELTA FAN-FUSION CORE with its
inhabitant, the fires, and the honest markers (crossing stays open with one burned attack
recorded).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`,
`WellFounded.fix`.  Built by the FX1PolyAudit lib glob; AuditAll registration is a later
round's bookkeeping (AuditAll untouched per this round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoTauPairDiesBare
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoTauPairDiesUnderWire
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoTauPairDiesOverWire
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoCopySlidesBelowParkedStrand
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoAddSlidesBelowParkedStrand
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoDiscardClimbsAcrossParkedStrand
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoZeroSlidesBelowParkedStrand
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoPadWindowOfPadLayersBelow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoPadWindowOfPadLayersAbove
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoPadWindowOfAppendLayers
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoConvPadsWindow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoScaleTowerCrossesDown
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoSwapDescendsIntoScaleTower
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoBalancedAddTreeLeansLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoMidSwapDiesAgainstAddTree
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoScaleTowerDistributesOverAdd
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoSwapThenUpperAddReroutes
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoFiveStrandMergeRoutesAgree
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoGadgetMuLeftSpine
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoGadgetMuRightSpine
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoGadgetDistributesOverAdd
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoMuFanDuplication
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoMuFanDuplicationHolds
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoScaleTowersFuseOverCopy
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoBalancedCopyTreeReassociates
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoCopyTreeAbsorbsMidSwap
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoCopyBelowCrossingReroutes
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoFiveStrandCopyRoutesAgree
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoGadgetsFuseOverCopy
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoDeltaFanFusion
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoDeltaFanFusionHolds
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoMuCoreFire
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoMuCoreFireDenotesEqually
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoScaleMuMatrixPin
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoDeltaCoreFire
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoDeltaCoreFireDenotesEqually
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoScaleFusionMatrixPin
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoScaleMuFireDenotesEqually
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoScaleFusionFireDenotesEqually
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoDistinctScaleTowersStayApart
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.fxLafontStaircase_hasMuDeltaFanCores
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcoCrossingTwoFanSwapProved

end FX1PolyAudit
