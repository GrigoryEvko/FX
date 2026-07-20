import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.ZXPhaseFree.CrossingResidual

/-! # FX1PolyAudit.Polygraph.Omega.ZXPhaseFree.CrossingResidual — zero-axiom
gate (the single-comb strand-crossing ride)

Per-declaration zero-axiom gate for the crossing-ride brick: the minimal window
quadruple (FF/FT/TF/TT) with the copy-triple symmetry, the general-position
window, the arity shuffles, the gadget pass, the comb ride, the block ride with
its column-swap plumbing, the generator-blocks fold, the init pass, the
kill-death residual statement, the conditional crossing absorption assembly, the
whiskered kill-death evidence, the fires with their kernel span pins, the
refutation fire, and the honest markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`, `WellFounded.fix`, `funext`.  Built by the
FX1PolyAudit lib glob; AuditAll registration is a later round's bookkeeping
(AuditAll untouched per this round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcStrandWindowFF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcStrandWindowFT
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcStrandWindowTF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcCopyTripleSwap
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcStrandWindowTT
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcStrandCrossWindowAt

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcRideEntryShuffle
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcWindowToTailShuffle
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcGadgetWhiskerRight
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcCrossPastGadget

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcCarryShuffle
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcPassEntryShuffle
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcCombCrossRide

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcSwapHere
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcSwapAdjacent
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcSwapHereLength
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcSwapAdjacentLength
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcSwapAdjacentAtCat
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcSwapRowsAt
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcSwapRowsAtAllWidth
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcRowSplitAt

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcXorRowCrossRide
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcGeneratorBlocksCrossRide
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcCrossPastInit

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcCrossIntoKillStatement
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcCrossingAbsorbOfKillDeath
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcCrossIntoKillPairWhiskered

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcXorRowCrossRideFire
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcXorRowCrossRideFireSpanPin
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcGeneratorBlocksCrossRideFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcCrossPastInitFire
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcCrossIntoKillResidualSpanPin
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcCrossingRideSpanDistinctNotConv

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcHasCrossingRide
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxcCrossingResidualIsClosed

end FX1PolyAudit
