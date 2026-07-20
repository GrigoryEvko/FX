import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.Quantale.WeightedQuantaleProp

/-! # FX1PolyAudit.Polygraph.Omega.Quantale.WeightedQuantaleProp — zero-axiom gate (WP-QUANTALE)

Per-declaration zero-axiom gate for the weighted (quantale-enriched) word-problem decision over the
finite 3-element chain quantale: the carrier with all quantale laws by finite cases, the
quantale-matrix kit (join-of-tensors product, direct sum, decidable equality), the four-generator
`WeightedDiagram` carrier with its quantale-matrix denotation, per-row soundness (including the
weighted composition law and the special Frobenius law), the full congruence-closure soundness lift,
the decision procedure with its negative direction, the walled quantale presentation-completeness
owner marker, and the ground fires.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`,
`WellFounded.fix`.  All recursion is structural on `Nat` bounds; all fires are kernel `rfl`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.QuantaleThree
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.joinQ
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.tensorQ
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.areQEqual
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.joinBotQ
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.botJoinQ
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.tensorBotQ
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.botTensorQ
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.tensorTopQ
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.topTensorQ
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.joinAssocQ
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.tensorAssocQ
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.tensorJoinDistribLeftQ
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.tensorJoinDistribRightQ
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.joinFourExchangeQ
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.areQEqualSelf
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.eqOfAreQEqual
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.QMatrixEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.botEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.identityQEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.joinBelowQ
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.composeQEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.directSumQEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.weightGenQEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.copyGenQEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.mergeGenQEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.swapGenQEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.doQEntriesAgreeOnRow
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.doQEntriesAgreeOnRows
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.doQEntriesAgreeUpTo
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.swapComposeSwapIsIdentity
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.copyThenMergeAgreesWithIdentity
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.beqSelfIsTrue
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.eqOfBeqIsTrue
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.beqIsFalseOfNe
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.bleIsTrueOfLe
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.leOfBleIsTrue
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.bltIsTrueOfLt
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.ltOfBltIsTrue
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.bltIsFalseOfGe
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.noLtOfEq
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.noLtOfGe
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.ltOrEqOfLtSucc
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.succSubSucc
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.addSubCancelLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.bleFalseGivesReverseLt
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.leOfBltIsFalse
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.leGivesAddSubCancel
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.decomposeIndexAgainstBlock
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.leOfAddLeAddLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.ltOfAddLtAddLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.beqAddLeftCancel
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.joinBelowQRespectsPointwise
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.joinBelowQOfAllBot
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.joinBelowQOfSingleSupport
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.joinBelowQSplitsAtBlock
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.joinBelowQOfPointwiseJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.joinBelowQTensorLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.joinBelowQTensorRight
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.joinBelowQExchange
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.identityQOnDiagonal
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.identityQOffDiagonal
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.directSumQInTopBlock
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.directSumQInBottomBlock
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.directSumQInTopRightBlock
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.directSumQInBottomLeftBlock
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.leftIsTrueOfAndTrue
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.rightIsTrueOfAndTrue
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.agreeOnRowOfPointwise
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.pointwiseOfAgreeOnRow
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.agreeOnRowsOfPointwise
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.pointwiseOfAgreeOnRows
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.agreeUpToOfPointwise
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.pointwiseOfAgreeUpTo
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.WeightedDiagram
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.singleWire
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.denoteQEntries
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.copyDenotesColumnOfTops
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.weightDenotesSingleton
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.swapDenotesTransposition
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.weightComposeLeftSide
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.weightComposeRightSide
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.weightComposeRowIsSound
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.weightTopUnitLeftSide
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.weightTopUnitRightSide
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.weightTopUnitRowIsSound
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.specialFrobeniusLeftSide
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.specialFrobeniusRightSide
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.specialFrobeniusRowIsSound
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.copyCocommLeftSide
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.copyCocommRightSide
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.copyCocommRowIsSound
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.mergeCommLeftSide
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.mergeCommRightSide
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.mergeCommRowIsSound
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.swapInvolutionLeftSide
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.swapInvolutionRightSide
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.swapInvolutionRowIsSound
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.WeightedConv
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.convertibleWeightedDiagramsDenoteEqualQMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.decideWeightedConvBool
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.decisionIsImpliedByWeightedConv
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.notWeightedConvOfDistinctQMatrices
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.quantaleCompletenessStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.qwmHasQuantalePresentationCompleteness
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.fireWeightMidMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.fireWeightTopThenMidDecidesTrue
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.fireMidVersusTopWeightDecidesFalse
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.fireMidWeightNotConvertibleToTopWeight
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.fireTensorDistributesOverJoin
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.fireSpecialFrobeniusDecidesTrue
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.QuantaleThree.bot
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.QuantaleThree.mid
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.QuantaleThree.top
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.WeightedDiagram.identityWires
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.WeightedDiagram.composeSequential
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.WeightedDiagram.tensorParallel
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.WeightedDiagram.weightGen
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.WeightedDiagram.copyGen
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.WeightedDiagram.mergeGen
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.WeightedDiagram.swapGen
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.WeightedConv.fromReflexivity
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.WeightedConv.fromSymmetry
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.WeightedConv.fromTransitivity
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.WeightedConv.underComposeSequential
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.WeightedConv.underTensorParallel
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.WeightedConv.composeIdentitySource
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.WeightedConv.composeIdentityTarget
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.WeightedConv.composeReassociate
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.WeightedConv.tensorIdentityFusion
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.WeightedConv.middleFourInterchange
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.WeightedConv.fromWeightComposeRow
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.WeightedConv.fromWeightTopUnitRow
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.WeightedConv.fromSpecialFrobeniusRow
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.WeightedConv.fromCopyCocommRow
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.WeightedConv.fromMergeCommRow
#assert_no_axioms FX1Poly.Polygraph.Omega.QuantaleProp.WeightedConv.fromSwapInvolutionRow

end FX1PolyAudit
