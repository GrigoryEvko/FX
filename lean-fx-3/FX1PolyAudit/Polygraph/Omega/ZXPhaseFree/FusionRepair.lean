import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.ZXPhaseFree.FusionRepair

/-! # FX1PolyAudit.Polygraph.Omega.ZXPhaseFree.FusionRepair — zero-axiom gate
(REPAIR ROUTE R1: the arity-indexed fusion row family + the gate re-run — VERDICT: CLEAN)

Per-declaration zero-axiom gate for the fusion-repair brick: the all-true/parity/chunk
kit, the all-arity spider span characterizations (`zxrCopySpanSound`/`Complete`,
`zxrParitySpanSound`/`Complete`) with the boundary-paired copy/add predicates, THE
FUSION ROW FAMILY (schema R1, both colours, `zxrZFuseLhs`/`Rhs` + mirrors) with
boundary/WF lemmas and the all-arity denotation soundness chain
(`zxrZFuseCoreEquiv`/`zxrXFuseCoreEquiv` — copy-of-copy is copy, add-of-add is add,
through `zxpComposeSpec`/`zxpTensorSpec`/`zxpIdSpec`; NO kernel evaluation of unbounded
instances), the fusion bundles, THE EXTENDED CONGRUENCE (`ZxrWindowMove`/`ZxrStep`/
`ZxrConv` in the seed's exact shapes) with SOUNDNESS `zxrConvSound`, the refutation
bridge `zxrConvSpanEqB`, the seed embedding `zxrOfZxpConv`, THE SEPARATOR'S DEATH
(`zxrFusedChainedConv`, `zxrXQuadConv`, `zxrProperExtensionWitness`), THE GATE RE-RUN
(the generalized fold engine `zxrConvFoldEq`, the old-separator kernel death pins, THE
COLLAPSE THEOREM `zxrBalancedWeightCollapse` killing the whole per-cell weight family
by the Cauchy-equation descent, the general delta saturation lemmas
`zxrZFuseDeltaGeneral`/`zxrXFuseDeltaGeneral`, the extended-table span pin, the
128-functional preserved-lattice re-classification), the Stage-7 fires (unit
absorption, the k = 2 recursion demo, the surviving big-arity FALSE case), and the
honesty markers (`zxrCompletenessStatement` owner-false, `zxrGateVerdictIsClean`).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`,
`WellFounded.fix`, `funext`.  Built by the FX1PolyAudit lib glob; AuditAll registration
is a later round's bookkeeping (AuditAll untouched per this round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrAllTrue
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrAllTrueAllOnesRow
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrAllTrueToAllOnesRow
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrAllTrueCatSplitLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrAllTrueCatSplitRight
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrAllTrueCatIntro
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrAllFalseCatSplitLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrAllFalseCatSplitRight
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrAllFalseCatIntro
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrAllFalseDropN
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrAllTrueTakeN
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrAllTrueDropN
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrAllFalseAllTrueNil
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrCatAllOnes
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrTakeNCatOfPrefix
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrDropNCatOfPrefix
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrRowParity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrRowParityZeroRow
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrRowParityCat
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrRowParityXor
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrXorBEqOfXorFalse
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrXorBReturnFalse
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrXorBBothPairsFalse
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrCopySpanSound
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrCopySpanComplete
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrParityRowsRowEven
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrParitySpanSound
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrParitySpanComplete
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxrCopyPair
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxrAddPair
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrCopyPairMemIff
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrAddPairMemIff
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrZFuseLhs
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrZFuseRhs
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrXFuseLhs
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrXFuseRhs
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrZFuseLhsCodArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrZFuseRhsCodArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrXFuseLhsCodArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrXFuseRhsCodArity
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrZFuseLhsWF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrZFuseRhsWF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrXFuseLhsWF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrXFuseRhsWF
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrZFuseTopLayerEquiv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrZFuseBotLayerEquiv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrXFuseTopLayerEquiv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrXFuseBotLayerEquiv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrZFuseLhsDenoteEquiv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrXFuseLhsDenoteEquiv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrZFuseRhsDenoteEquiv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrXFuseRhsDenoteEquiv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrRowParitySingle
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrZFuseCoreEquiv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrXFuseCoreEquiv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrZFuseBundle
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrXFuseBundle
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxrWindowMove
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxrWindowMove.seed
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxrWindowMove.zFuse
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxrWindowMove.xFuse
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrWindowMoveBundle
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxrStep
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxrStep.pad
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrPadBundle
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrStepBundle
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxrConv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxrConv.step
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxrConv.refl
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxrConv.symm
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxrConv.trans
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrConvSound
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrConvSpanEqB
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrOfZxpConv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrFusedChainedConv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrXChainedTripleDiagram
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrXFusedQuadDiagram
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrXQuadConv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrProperExtensionWitness
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrHopfConvEmbedded
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxrZFuseBalancedWeight
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.ZxrXFuseBalancedWeight
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrWindowMoveFoldEq
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrStepFoldEq
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrConvFoldEq
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrBigSpiderZFuseLhsFoldPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrBigSpiderZFuseRhsFoldPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrBigSpiderNotZFuseBalanced
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrBigSpiderNotXFuseBalanced
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrZCountNotZFuseBalanced
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrXCountNotXFuseBalanced
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrNatLeAddRight
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrNatLeAddLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrNatLeAddRightMono
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrNatLeSuccSelfFalse
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrDescentForcesZero
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrFuseBalanceForcesZero
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrCellFoldSingle
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrZFuseBalanceEquation
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrXFuseBalanceEquation
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrZSpiderWeightZero
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrXSpiderWeightZero
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrBalancedWeightCollapse
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrBalancedWeightFoldZero
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrWireCountFoldWires
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrZFuseLhsCountVector
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrZFuseRhsCountVector
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrXFuseLhsCountVector
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrXFuseRhsCountVector
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrFuseLegsShift
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrZFuseDeltaGeneral
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrXFuseDeltaGeneral
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrFuseDeltaZEven
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrFuseDeltaZOdd
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrFuseDeltaXEven
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrFuseDeltaXOdd
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrZFuseDeltaCases
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrXFuseDeltaCases
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrExtendedDeltaTable
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrExtendedDeltaSpanBasisPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrIsPreservedExactlyLegsParityB
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrPreservedLatticeReclassified
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrLegsParityOrthogonalZFuseDelta
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrLegsParityOrthogonalXFuseDelta
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrZUnitAbsorptionLhsDiagram
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrZUnitAbsorptionRhsDiagram
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrZUnitAbsorptionConv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrZTwoWireChainedDiagram
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrZTwoWireFusedDiagram
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrTwoWireFusionDemo
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrTwoWireSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrZPentaDiagram
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrXPentaDiagram
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrBigColourSpanDistinct
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrBigColourNotConv
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrCompletenessStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrCompletenessIsProven
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrHasAllArityFusionSoundness
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxrGateVerdictIsClean

end FX1PolyAudit
