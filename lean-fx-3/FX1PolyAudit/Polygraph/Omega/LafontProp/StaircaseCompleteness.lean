import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.LafontProp.StaircaseCompleteness

/-! # FX1PolyAudit.Polygraph.Omega.LafontProp.StaircaseCompleteness — zero-axiom gate
(LAFONT-REPAIR stage 2 phase 2: canonical form + the wire/eta/epsilon absorption ladder)

Per-declaration zero-axiom gate for the staircase file: the embedded canonical/scale/gadget/
fan layer lists with their composability/reach/denotation/extensionality bookkeeping, the
pad-composition plumbing, the builder unfold equations, the wire-layer deletion tools, the
matrix restriction kit, the eta ladder (scale-tower absorption, gadget absorption, fan
annihilation), the epsilon ladder (gadget-zero-is-crossing, zero-column-fan-is-discard), the
three closed bottom cores, THE BELOW-PAD REDUCTION, the three closed absorption theorems at
all pads, the named open statements with their owner-false Bools, and the marker.  The fire
instantiations live in the split file `StaircaseAbsorptionFires` with their own twin.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`,
`WellFounded.fix`.  Built by the FX1PolyAudit lib glob; AuditAll registration is a later
round's bookkeeping (AuditAll untouched per this round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstCanonicalLayerList
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstScaleLayerList
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstGadgetLayerList
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstFanLayerList
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstZipWithEmptyBottomIsPadBelow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstCanonicalLayersAreComposable
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstCanonicalLayersReach
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstCanonicalDenotesEntry
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstCanonicalDenoteAgrees
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstCanonicalRespectsRectangleAgreement
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstFanRespectsColumnAgreement
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstScaleLayersAreComposable
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstScaleLayersReach
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstGadgetLayersAreComposable
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstGadgetLayersReach
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstFanLayersAreComposable
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstFanLayersReach
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstPadLayersBelowCompose
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstPadLayersAboveCompose
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstPadBelowOfPadAboveIsPadWindow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstPadAboveOfPadBelowIsPadWindow
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstScaleZeroLayerShape
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstScaleSuccUnfolds
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstGadgetLayerShape
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstFanZeroLayerShape
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstFanSuccUnfolds
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstCanonicalSuccUnfolds
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstTrailingWireLayerDies
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstLoneWireLayerDissolves
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstWireLayerBeforeChainDeletes
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstProductAgainstAppendedLayerRestricts
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstProductThroughWireLayerCollapses
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstProductLastColumnThroughBelowWirePad
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstScaleTowerAbsorbsFreshZero
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstGadgetAbsorbsFreshZero
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstFreshZeroAnnihilatesFan
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstGadgetZeroConvertsToCrossing
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstZeroColumnFanIsDiscard
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstProductThroughBottomEtaPad
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstProductThroughBottomEpsilonPad
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstProductThroughBottomEpsilonPadLastColumn
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstEtaCellAbsorbsAtBottomPlain
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstEtaCellAbsorbsAtBottom
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstEpsilonCellAbsorbsAtBottom
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstWireCellAbsorbsAtBottom
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstCellAbsorptionLiftsThroughBelowPads
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstWireCellAbsorbs
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstEtaCellAbsorbs
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstEpsilonCellAbsorbs
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstMuFanDuplicationStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstDeltaFanFusionStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstCrossingTwoFanSwapStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstCanonicalReductionOverStrictLayersStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstMuFanDuplicationProved
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstDeltaFanFusionProved
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstCrossingTwoFanSwapProved
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstCanonicalReductionOverStrictLayersProved
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.fxLafontStaircase_hasWireEtaEpsilonAbsorption

end FX1PolyAudit
