import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.ZXPhaseFree.TransportRides

/-! # FX1PolyAudit.Polygraph.Omega.ZXPhaseFree.TransportRides — zero-axiom gate
(the comb-move rides: the TT crossing window, the CNOT window layer, the
zipped double comb, the crossing ride, and the adjacent comb swap)

Per-declaration zero-axiom gate for the transport-ride brick: the
exchange-pair plumbing, the merge-routing bricks, THE TT CROSSING WINDOW
WHOLE, the FF/TF CNOT windows plus the FT/TT walls with span pins, the zipped
double comb with well-formedness and arity lemmas, the general-position
window, THE CROSSING RIDE, the gadget park behind a comb tail, THE
INTERLEAVING, the creation park, THE ADJACENT COMB SWAP
(`zxtCombSwapHolds : zxfCombSwapStatement`), both fires with kernel span
pins, and the honest marker ledger.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`, `WellFounded.fix`, `funext`.  Built by the
FX1PolyAudit lib glob; AuditAll registration is a later round's bookkeeping
(AuditAll untouched per this round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtLeftFirstToRightFirst
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtRightFirstToLeftFirst
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtCrossThenMergeRight
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtMergeAfterCross

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtCrossWindowTTHolds
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtCrossWindowTTIsProven

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtCnotWindowFFHolds
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtCnotWindowTFHolds
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtCnotWindowFTStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtCnotWindowFTSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtCnotWindowFTIsProven
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtCnotWindowTTStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtCnotWindowTTSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtCnotWindowTTIsProven

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtWhiskerBumpOne
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtGadgetLayersWF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtGadgetLayersCodArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtDoubleLayers
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtDoubleLayersWF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtDoubleLayersCodArity

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtTwoPlusSuccShuffle
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtCrossWindowAt
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtCrossRideDouble

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtOnePlusTwoShuffle
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtDeepForkShuffle
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtCarrierExitShuffle
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtBlockLayerPastCombTail
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtGadgetPastCombTail

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtDoubleOfCombLayers

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtParkedXorRowShape
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtXorPairToDouble
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtCombSwapHolds
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtCombSwapIsProven

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtCombSwapFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtCombSwapFireSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtNormalFormSwapFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtNormalFormSwapFireSpanPin

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtCombXorAbsorbIsProven
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtGeneratorTransportIsProven
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxtHasSwapRide

end FX1PolyAudit
