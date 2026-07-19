import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.LafontProp.StaircaseCrossingCore

/-! # FX1PolyAudit.Polygraph.Omega.LafontProp.StaircaseCrossingCore — zero-axiom gate
(LAFONT-REPAIR stage 2 phase 4: the crossing bottom core)

Per-declaration zero-axiom gate for the crossing-core file: the pad bookkeeping and gadget
shape kit, the generic scale-window slides and the two padded SCALE-TAU orientations, THE
ONE-GADGET CONJUGATION, the far-pregadget commutation through the canonical parallel form
(both spines), the two-gadget swap across the crossing, THE CROSSING TWO-FAN-SWAP CORE with
its inhabitant of the live open Prop, the fires, the negative control, and the marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`,
`WellFounded.fix`.  Built by the FX1PolyAudit lib glob; AuditAll registration is a later
round's bookkeeping (AuditAll untouched per this round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxPadWindowWithZeroBelowIsPadAbove
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxGadgetPadBelowShape
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxGadgetPadAboveShape
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxScaleAboveBlockReach
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxScaleAboveBlockComposable
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxScaleWindowBlockReach
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxScaleWindowBlockComposable
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxLayerSlidesBelowScaleWindow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxLayerSlidesAboveScaleWindow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxCrossingPushesScaleDeeper
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxScaleSurfacesAcrossCrossing
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxCopyThenRotatedWindowReach
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxGadgetRidesConjugation
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxWindowOneTwoReachFromFour
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxWindowOneThreeReachFromFive
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxWindowTwoTwoReachFromFive
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxWindowThreeOneReachFromFive
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxParallelScaledMergeForm
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxConvBehindWindowPair
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxFarPregadgetsLeftSpine
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxFarPregadgetsRightSpine
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxFarPregadgetsCommute
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxAppendLayersConsExposes
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxAppendLayersNilExposes
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxWindowTwoOneReachFromFour
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxGadgetAboveReach
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxGadgetRidesConjugationShaped
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxUpperGadgetUnconjugates
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxGadgetPairSwapsAcrossCrossing
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxCrossingTwoFanSwap
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxCrossingTwoFanSwapHolds
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxCrossingCoreFire
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxCrossingCoreFireDenotesEqually
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxConjugationFireDenotesEqually
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxGadgetPairSwapFireDenotesEqually
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lcxDistinctColumnFansStayApart
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.fxLafontStaircase_hasCrossingCore

end FX1PolyAudit
