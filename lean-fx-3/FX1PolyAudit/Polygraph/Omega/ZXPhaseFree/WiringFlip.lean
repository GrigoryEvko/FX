import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.ZXPhaseFree.WiringFlip

/-! # FX1PolyAudit.Polygraph.Omega.ZXPhaseFree.WiringFlip — zero-axiom gate
(THE WIRING SCHEMA: naturality slides + sigma involution as gated window moves,
the gate re-run, the derived symmetric structure, the absorption partials)

Per-declaration zero-axiom gate for the wiring brick: the adjacent-crossing
staircases with WF/arity lemmas and THE ROTATION PAIR CHARACTERIZATIONS, the
whiskered-window pair workhorse, the slide window family (`zxwSlideRight*` /
`zxwSlideLeft*`) with structural all-arity soundness bundles and the
kernel-decided involution, the wiring-extended congruence
(`ZxwWindowMove`/`ZxwStep`/`ZxwConv` + soundness + refutation bridge + full
embedding + pad lift), the engine transports, THE GATE RE-RUN (stair folds, the
honest crossing-count forcing, general slide deltas saturated by literals, the
extended table span pin, the 128-functional reclassification, the collapse, the
negative control, verdict CLEAN), the derived symmetric structure (counit/unit
slides in the wall's committed shapes, sigma involution, YANG-BAXTER as a slide
instance, disjoint-block commutation, the staircase split, the crossing-block
permutation engine `zxwWalkPastBlock`/`zxwBlockPastWalk` + fire), and the honest
(D) partials (absorption + generator-transport + completeness statements
owner-false, transported base cases, the assembly theorem, the conditional
decision, `zxwHasFullDecision := false`).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`, `WellFounded.fix`, `funext`.  Built by the FX1PolyAudit lib glob;
AuditAll registration is a later round's bookkeeping (AuditAll untouched per this
round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwStairFromRightLayers
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwStairFromLeftLayers
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwOnePlusOnePlus
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwWiresCrossingDomArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwWiresCrossingCodArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwCrossingWiresDomArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwCrossingWiresCodArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwStairFromRightWF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwStairFromLeftWF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwStairFromRightCodArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwStairFromLeftCodArity

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwWhiskerLayersPairIff
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwWhiskerLayersPairIffAt
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSnocSplit
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwStairFromRightPairIff
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwStairFromLeftPairIff

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideRightLhs
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideRightRhs
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideLeftLhs
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideLeftRhs
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideRightLhsWF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideRightRhsWF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideLeftLhsWF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideLeftRhsWF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideRightLhsCodArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideRightRhsCodArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideLeftLhsCodArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideLeftRhsCodArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideRightLhsPairIff
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideRightRhsPairIff
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideLeftLhsPairIff
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideLeftRhsPairIff
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideRightBundle
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideLeftBundle
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwInvolutionLhs
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwInvolutionRhs
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwInvolutionBundle

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxwWindowMove
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxwWindowMove.base
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxwWindowMove.slideRight
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxwWindowMove.slideLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxwWindowMove.sigmaInvolution
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwWindowMoveBundle
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxwStep
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxwStep.pad
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwStepBundle
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxwConv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxwConv.step
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxwConv.refl
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxwConv.symm
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxwConv.trans
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwConvSound
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwConvSpanEqB
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwOfZxeConv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwOfZxrConv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwOfZxpConv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwConvLift
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwStepConv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwLiftConv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwMoveConv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideRightConv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideLeftConv

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwParallelFusionZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwParallelFusionX
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwMidMergeFuseZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwMidMergeFuseX
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwMidForkFuseZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwMidForkFuseX
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwCrossingAbsorbInputZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwCrossingAbsorbInputX
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwCrossingAbsorbOutputZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwCrossingAbsorbOutputX
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwWalkAbsorbOutputZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwWalkAbsorbOutputX
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwWalkAbsorbInputZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwWalkAbsorbInputX

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwAddCancelRight
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwStairFromRightFoldVanishing
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwStairFromLeftFoldVanishing
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwStairFromRightCrossFold
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwStairFromLeftCrossFold
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwLayerCountWhisker
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwLayerCountCat
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwStairFromRightLayerCount
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwStairFromLeftLayerCount
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwWireFoldWhisker01
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwWireFoldWhisker10
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwStairFromRightWireFoldParity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwStairFromLeftWireFoldParity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideRightFoldSpiderWeightEq
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideLeftFoldSpiderWeightEq
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideRightWireParityEq
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideLeftWireParityEq
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideRightCrossDelta
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideLeftCrossDelta
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideRightLayerDelta
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideLeftLayerDelta
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideRightDeltaGeneral
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideLeftDeltaGeneral
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideDeltaOddLiteral
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwInvolutionDeltaLiteral
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwInvolutionDeltaValue
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideRightDeltaCases
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideLeftDeltaCases
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwExtendedDeltaTable
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwExtendedDeltaSpanBasisPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwIsPreservedExactlyLegsParityB
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwPreservedLatticeReclassified
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwLegsParityOrthogonalSlideRightDelta
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwLegsParityOrthogonalSlideLeftDelta
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxwSlideBalancedWeight
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxwInvolutionBalancedWeight
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwWindowMoveFoldEq
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwStepFoldEq
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwConvFoldEq
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideBalanceForcesCrossingZero
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwUnitSlideCrossCountShift
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwCrossCountNotSlideBalanced
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwBalancedWeightCollapse
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwBalancedWeightFoldZero
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwBigColourNotConv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwGateVerdictIsClean

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwCounitSlideZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwCounitSlideX
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwUnitSlideZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwUnitSlideX
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSigmaInvolutionFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwYangBaxter
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideSpiderRightFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideSpiderLeftFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwSlideSpiderRightFireSpanPin

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwWhiskerLayerRightZero
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwWhiskerRightZeroCons
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwLayerPastRightLayers
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwLayersPastRightLayer
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwStairFromRightSplit
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwWalkPastBlock
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwBlockPastWalk
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwWalkPastBlockFire

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwAbsorptionStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwAbsorptionIsProven
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwGeneratorTransportStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwGeneratorTransportIsProven
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwEmptyDiagramAbsorbed
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwKillCreateAbsorbedFire
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwCompletenessStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwCompletenessIsProven
#assert_no_axioms
  FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwCompletenessOfAbsorptionAndTransport
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwDecisionUnderCompleteness
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwHasWiringSchema
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxwHasFullDecision

end FX1PolyAudit
