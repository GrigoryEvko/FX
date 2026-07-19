import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.ZXPhaseFree.CompletenessGate

/-! # FX1PolyAudit.Polygraph.Omega.ZXPhaseFree.CompletenessGate — zero-axiom gate
(THE INVARIANT-FIRST GATE for `zxpCompletenessStatement` — VERDICT: REFUTED)

Per-declaration zero-axiom gate for the completeness gate brick: the parity/equality kit
(fresh Bool tables, additive parity), the generic cell-weight fold engine with its
cat/wire/whisker/pad/split algebra and the three-level invariance chain
(`zxgWindowMoveFoldEq` / `zxgStepFoldEq` / `zxgConvFoldEq` — structural induction over
EVERY `ZxpConv` constructor), THE ROW-EFFECT DELTA TABLE over the base count vector
(seven components; the explicit 33x7 kernel-pinned matrix `zxgRowDeltaTableValue`, the
two `splitLayer` witnesses, the 6-dimensional row-space basis pin decided by
`zxpSpanEqB`, the 128-functional preserved-lattice classification
`zxgPreservedLatticeClassified`, and the boundary determination of the sole survivor
`zxgLegsParityFunctionalBoundaryDetermined`), THE SEPARATOR (the big-spider count:
row-balanced by 33 kernel decisions, congruence-invariant by the engine, separating the
seed's span-equal well-formed boundary-matched fusion pair), the non-convertibility
`zxgFusedChainedNotConv`, THE REFUTATION `zxgCompletenessRefuted :
zxpCompletenessStatement -> False`, and the verdict marker
(`zxgGateVerdictIsRefuted` true).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`,
`WellFounded.fix`, `funext`.  Built by the FX1PolyAudit lib glob; AuditAll registration
is a later round's bookkeeping (AuditAll untouched per this round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgParityB
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgBoolEqB
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgNatEqBRefl
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgXorBMedial
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgXorBCancelMiddle
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgParityBAdd
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgAddLeftComm
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgAddMedial
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgCellFold
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgLayersFold
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgDiagramFold
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgCellFoldCat
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgCellFoldWires
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgCellFoldWhiskerLayer
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgLayersFoldWhisker
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgLayersFoldCat
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgDiagramFoldPad
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgSplitLayerFoldEq
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxgRowBalancedWeight
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgWindowMoveFoldEq
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgStepFoldEq
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgConvFoldEq
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgCellZCountWeight
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgCellXCountWeight
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgCellWireCountWeight
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgCellCrossCountWeight
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgCellZLegsWeight
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgCellXLegsWeight
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgLayerCount
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgCountVector
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgVectorDeltaMod2
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgRowDeltaMod2
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgAllRowTags
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgMapTagsToDeltas
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgRowDeltaTable
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgRowDeltaTableValue
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgSplitWitnessDelta
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgSplitDeltaWitnessWire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgSplitDeltaWitnessCrossing
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgSplitDeltaWitnessWireValue
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgSplitDeltaWitnessCrossingValue
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgFullDeltaTable
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgDeltaSpanBasis
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgDeltaTableSpanBasisPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgDotB
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgIsOrthogonalToAllB
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgRowEqB
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgConsToAll
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgAllBoolVectors
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgZeroFunctional
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgLegsParityFunctional
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgIsPreservedExactlyLegsParityB
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgPreservedLatticeClassified
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgLegsParityOrthogonalPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgCellSpiderLegsWeight
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgCellLegsWeightSplit
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgCellFoldLegsSplit
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgLayersFoldLegsSplit
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgCellLegsParityBoundary
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgLayerLegsParityBoundary
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgLayersLegsParityBoundary
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgLegsParityFunctionalBoundaryDetermined
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgCellBigSpiderWeight
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgBigSpiderRowBalanced
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgConvBigSpiderCountEq
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgConvBigSpiderCountEqB
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgFusedTripleBigCountOne
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgChainedPairBigCountZero
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgFusedChainedBigCountDistinctB
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgFusedChainedSpanEqTrue
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgFusedTripleWFBTrue
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgChainedPairWFBTrue
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgFusedChainedSameSourcePin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgFusedChainedSameCodPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgFusedChainedNotConv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgCompletenessRefuted
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxgGateVerdictIsRefuted

end FX1PolyAudit
