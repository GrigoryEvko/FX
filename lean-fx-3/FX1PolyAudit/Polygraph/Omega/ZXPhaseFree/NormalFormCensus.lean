import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.ZXPhaseFree.NormalFormCensus

/-! # FX1PolyAudit.Polygraph.Omega.ZXPhaseFree.NormalFormCensus — zero-axiom gate
(THE Z-X NORMAL FORM + THE CENSUS GATE STAGE)

Per-declaration zero-axiom gate for the normal-form census brick: the shape/arith/
scale-row/span-cons kit, the cell relation characterizations (Z source/sink/fork
through the copy-span kit, X merge and zero state/effect through the parity-span
kit, the crossing through the concrete width-4 span), the layer-chaining and
padded-cell workhorses (`zxnConsLayerPairIffAt`, `zxnCatLayersPairIffAt`,
`zxnSingleLayerPairIffAt`, `zxnPadCellPairIff`/`At`), the init/kill boundary
X-chains, THE GENERATOR COMB (`zxnCombLayers` with WF/codArity and THE
CHARACTERIZATION `zxnCombPairIff` — the carrier walk as a conditional xor), the
per-generator block and generator fold (`zxnXorRowPairIff`,
`zxnGeneratorBlockLayersPairIff` — the span characterization), THE NORMAL FORM
(`zxnNormalForm` with `zxnNormalFormWF`, `zxnNormalFormBoundaries`, and THE
STRUCTURAL DENOTATION THEOREM `zxnNormalFormDenotes`), THE CENSUS (the RREF
enumerator with the Galois-number size pins 5/16/67, the surjectivity pins at
boundaries (1,1)/(1,2)/(2,1)/(2,2), the pairwise injectivity pins, and the PROVEN
injectivity `zxnNormalFormInjective`), the end-to-end fires with the negative
control, and the markers (`zxnHasNormalFormFamily`, `zxnCensusComplete`).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`, `WellFounded.fix`, `funext`.  Built by the FX1PolyAudit lib glob;
AuditAll registration is a later round's bookkeeping (AuditAll untouched per this
round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnLengthOneShape
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnLengthTwoShape
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnLengthSuccShape
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnTwoPlusEqOnePlusSucc
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnStepArityShuffle
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnCombCodShuffle
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnForkArityShuffle
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnScaleRow
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnScaleRowLength
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnScaleRowConsFalse
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnScaleRowConsTrue
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnRowXorLeftComm
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnMemSpanSingleInv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnMemSpanConsIff
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnZSourcePairIff
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnZSinkPairIff
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnZForkPairIff
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnXMergePairIff
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnXZeroStatePairIff
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnXZeroEffectPairIff
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnSwapRowsLiteral
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnCrossingPairIff
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnConsLayerPairIff
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnConsLayerPairIffAt
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnSingleLayerPairIffAt
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnCatLayersPairIffAt
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnPadCellPairIff
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnPadCellPairIffAt
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnZeroStateCells
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnKillCells
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnZeroStateCellsDomArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnZeroStateCellsCodArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnKillCellsDomArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnKillCellsCodArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnZeroStateCellsPairIff
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnKillCellsPairIff
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnInitLayer
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnKillLayer
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnInitLayerDomArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnInitLayerCodArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnKillLayerDomArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnKillLayerCodArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnInitLayerPairIff
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnKillLayerPairIff
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnCombLayers
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnCombLayersCodArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnCombLayersWF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnCombPairIff
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnXorRowLayers
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnXorRowLayersWF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnXorRowLayersCodArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnXorRowPairIff
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnXorRowPairIffAt
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnGeneratorBlockLayers
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnGeneratorBlockLayersWF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnGeneratorBlockLayersCodArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnGeneratorBlockLayersPairIff
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnNormalForm
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnNormalFormWF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnNormalFormSourceArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnNormalFormCodArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnNormalFormBoundaries
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnNormalFormDenotes
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnMatrixConsFalseColumn
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnMapConsFalseAll
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnIsReducedAgainstB
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnPivotExtensions
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnCatMatrixLists
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnAllPivotExtensions
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnAllRrefMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnRrefCountWidthTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnRrefCountWidthThree
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnRrefCountWidthFour
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnNfMatchesSubspaceB
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnCensusSurjectivityB
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnCensusSurjectivityOneOne
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnCensusSurjectivityOneTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnCensusSurjectivityTwoOne
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnCensusSurjectivityTwoTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnDistinctFromAllB
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnAllPairsSpanDistinctB
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnCensusInjectivityWidthTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnCensusInjectivityWidthThree
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnCensusInjectivityWidthFour
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnNormalFormInjective
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnFireCopyPairMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnFireCopyPairWFB
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnFireCopyPairCodPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnFireCopyPairDenotes
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnFireXorGraphMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnFireXorGraphWFB
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnFireXorGraphCodPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnFireXorGraphDenotes
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnFireNegativeControl
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnHasNormalFormFamily
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnCensusComplete

end FX1PolyAudit
