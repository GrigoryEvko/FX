import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.LafontProp.StaircaseInvariantGate

/-! # FX1PolyAudit.Polygraph.Omega.LafontProp.StaircaseInvariantGate — zero-axiom gate
(LAFONT-REPAIR stage 2 phase 1: the invariant-first refutation gate, verdict CLEAN BILL)

Per-declaration zero-axiom gate for the adversarial-hunt file: the six cell-kind weights and
the two Euler weights, the count folds with their append/wire/pad plumbing, the additive
helpers (four-summand exchange, hand-rolled right cancellation), the kernel-checked
36-window row-effect table, the Euler cross-balance with its case engines, THE CONSERVATION
THEOREM over all 24 congruence constructors, the boundary telescope
(cell/layer Euler relations, the pinning theorem, the no-separation-power corollary), the
kill-fires for every candidate family (M4 crossing-parity, B2 eta/delta axes, B3 mu/epsilon
axes, the two split fires for wire/layer weights, the purity fire, the two r3-analog
dissolution fires with their records), the two distinct-matrix negative controls, and the
clean-bill marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`,
`WellFounded.fix`.  Built by the FX1PolyAudit lib glob; AuditAll registration is a later
round's bookkeeping (AuditAll untouched per this round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstMuWeight
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstEtaWeight
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstDeltaWeight
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstEpsilonWeight
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstCrossingWeight
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstWireWeight
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstStrandDroppingWeight
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstStrandRaisingWeight
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstCountLayersBy
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstCountLayers
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstIsOddCount
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstCountLayersByOfAppendLayers
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstWireLayerHasNoWeightedCells
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstPadLayerKeepsWeightedCount
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstPadWindowKeepsWeightedCount
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstAddFourExchange
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstAddRightCancel
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstDoWindowCountsMatch
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstDoesRowEffectTableHold
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstRowEffectTableHolds
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstDoEulerCountsBalance
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstEulerBalanceOfCountsEqual
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstBalanceChainArithmetic
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstBalanceUnderAddedConstants
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstBalanceWithSharedSuffix
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstEulerBalanceAcrossPaddedRowEdge
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstTopSplitKeepsWeightedCount
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstBottomSplitKeepsWeightedCount
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstConvertibleLayersConserveEulerCount
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstCellArityBalance
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstLayerArityBalance
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstEulerCountIsBoundaryPinned
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstPinnedPairBalancesArithmetic
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstEqualBoundaryDataPinsEulerBalance
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstCommutativityWindowsConvert
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstCrossingCountsAcrossCommutativityFire
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstCrossingParityFlipsAcrossCommutativityFire
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstCommutativityFireSidesDenoteEqually
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstCopyAfterZeroWindowsConvert
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstEtaDeltaEpsilonCountsAcrossCopyAfterZeroFire
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstDiscardAfterAddWindowsConvert
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstMuEpsilonCountsAcrossDiscardAfterAddFire
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstNarrowSplitGrowsWireAndLayerCounts
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstWideSplitGrowsWireCountByTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstWireAndLayerCountsAcrossSplitFires
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstGeneratorMaterialConvertsToPureCrossing
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstPurityFireRecord
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstEmptyLayerDissolvesIntoNoSyntax
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstWireLayerDissolvesIntoNoSyntax
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstDissolutionFireRecord
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstWireLayerStaysApartFromDoubling
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lstEmptyListStaysApartFromCrossing
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.fxLafontStrictLayer_invariantGateClean

end FX1PolyAudit
