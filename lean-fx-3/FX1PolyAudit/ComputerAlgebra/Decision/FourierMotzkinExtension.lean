import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Decision.FourierMotzkinExtension

/-! # FX1PolyAudit/ComputerAlgebra/Decision/FourierMotzkinExtension — zero-axiom gate
    (DISSAT-ARITH round-extension push: wall refuted as stated, corrected form
    proven, Farkas completeness inhabited)

Per-declaration zero-axiom gate for the round-extension brick: the Nat kit
additions (hand-rolled `le`-add embeddings, positive-multiplier cancellation
for `le` and `Eq`, product positivity, the succ-shape existential, the
`cond`-of-Option none split), the `LfkInt` transport kit (cross-sum equality
symmetry/transitivity, the `<=`/`<` congruence transports, the one-shift
strictness bridges, the movers `lreIntLeMoveNegAcross` /
`lreIntLeSplitAcross` / `lreIntLeSwapSides` with strict forms, scale
monotonicity/cancellation, the padding strict-slack lemmas, the
positive/negative pivot-entry cross-equalities), the environment-update /
dot-product decomposition kit (`lreZeroCoefficientAt`, `lreUpdateEnvAt`, THE
SPLIT LEMMA `lreDotProductSplitAt`, THE MASTER DECOMPOSITION
`lreDotProductUpdateAt`, the scaled-environment dot `lreDotProductScaledEnv`),
the bespoke membership kit (`lreRowIsAmong`/`lreAllRowsAmong` with
filter/join/cross-combination propagation and scaled-satisfaction
extraction), the row endpoint data (rest dots, lower/upper numerators), THE
COMBO UNFOLD (`lreComboUnfoldForms` and the weak/strict endpoint bounds), the
endpoint arithmetic cores (generic dominance transitivity with middle-
magnitude cancellation, the midpoint lower/upper weak+strict cores, the
lone-bucket whole-unit-pad cores), the dominating-row selection fold with its
membership+dominance invariant, the per-row verification steps
(zero/positive/negative) at the constructed witness, THE CORRECTED
ROUND-EXTENSION THEOREM (`lreRoundExtensionForInequalityRows`, statement
`lreRoundExtensionInequalityStatement`, inhabitant `lreRoundExtensionHolds`),
THE REFUTATION of the sibling wall Prop as stated
(`lreRoundExtensionStatementRefuted` on the `[x = 0, x >= 1]` fixture whose
round output is empty), the cascade (round/driver inequality preservation,
backward driver induction, the scan-clean ground base, unit-provenance seed
extraction with zero-weight peel and head extract, expansion re-assembly),
THE COMPLETENESS INHABITANT `lreFarkasCompletenessHolds :
lfkFarkasCompletenessStatement` (the LinearFarkasCertificate wall Prop,
verbatim), the scaled-checker kit (accepted certificates refute the rational
relaxation), the supersession markers, and the kernel-checked smoke pins
(the concrete two-round backward extension witnesses, the refutation pins,
the completeness fires on the sibling fixtures, the satisfiable controls).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.lreNatLeAddLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.lreNatLeAddRight
#assert_no_axioms FX1Poly.ComputerAlgebra.lreNatMulLeCancelLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.lreNatMulLeftCancelEq
#assert_no_axioms FX1Poly.ComputerAlgebra.lreNatPositiveMulPositive
#assert_no_axioms FX1Poly.ComputerAlgebra.lrePositiveSuccShape
#assert_no_axioms FX1Poly.ComputerAlgebra.lreBoolAndFalseRight
#assert_no_axioms FX1Poly.ComputerAlgebra.lreCondNoneSplit
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntEqSymm
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntEqTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.lreNatAddRightSwap
#assert_no_axioms FX1Poly.ComputerAlgebra.lreNatAddLeftSwap
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntOfNat
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntOne
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntOfNatIsPositive
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntLeTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntLtGivesLeShifted
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntLeShiftedGivesLt
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntLeCongrLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntLeCongrRight
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntLtCongrLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntLtCongrRight
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntLeMoveNegAcross
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntLtMoveNegAcross
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntLeSplitAcross
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntLtSplitAcross
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntLeSwapSides
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntLtSwapSides
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntScaleLtMono
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntLeCancelScale
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntMulZeroLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntAddNegateRightZero
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntEqDropZeroLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntLtOfLeAddPositive
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntLtOfLeSubPositive
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntLeAddNonNegRight
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntAddLeftCommute
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntPositiveMagnitudePositive
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntMulPositiveEntryCrossEq
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntMulNegativeEntryCrossEq
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntSignTrichotomy
#assert_no_axioms FX1Poly.ComputerAlgebra.lreZeroCoefficientAt
#assert_no_axioms FX1Poly.ComputerAlgebra.lreUpdateEnvAt
#assert_no_axioms FX1Poly.ComputerAlgebra.lreDotProductNilEnv
#assert_no_axioms FX1Poly.ComputerAlgebra.lreDotProductSplitAt
#assert_no_axioms FX1Poly.ComputerAlgebra.lreDotProductUpdateAt
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntMulScaleLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.lreDotProductScaledEnv
#assert_no_axioms FX1Poly.ComputerAlgebra.lreRowIsAmong
#assert_no_axioms FX1Poly.ComputerAlgebra.lreAllRowsAmong
#assert_no_axioms FX1Poly.ComputerAlgebra.lreAmongOfEqMember
#assert_no_axioms FX1Poly.ComputerAlgebra.lreAllRowsAmongExtend
#assert_no_axioms FX1Poly.ComputerAlgebra.lreAllRowsAmongSelf
#assert_no_axioms FX1Poly.ComputerAlgebra.lreTestPassesOfAmong
#assert_no_axioms FX1Poly.ComputerAlgebra.lreAmongCondOfTrue
#assert_no_axioms FX1Poly.ComputerAlgebra.lreAmongCondOfFalse
#assert_no_axioms FX1Poly.ComputerAlgebra.lreAmongFilterOfPass
#assert_no_axioms FX1Poly.ComputerAlgebra.lreFilterNilAllFail
#assert_no_axioms FX1Poly.ComputerAlgebra.lreAmongJoinLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.lreAmongJoinRight
#assert_no_axioms FX1Poly.ComputerAlgebra.lreAmongCombineOne
#assert_no_axioms FX1Poly.ComputerAlgebra.lreAmongCrossCombine
#assert_no_axioms FX1Poly.ComputerAlgebra.lreScaleConstraintBound
#assert_no_axioms FX1Poly.ComputerAlgebra.lreRowSatisfiedOfAmong
#assert_no_axioms FX1Poly.ComputerAlgebra.lreJoinedRowsSatisfiedSplit
#assert_no_axioms FX1Poly.ComputerAlgebra.lreRowRestDotAt
#assert_no_axioms FX1Poly.ComputerAlgebra.lreRowLowerNumeratorAt
#assert_no_axioms FX1Poly.ComputerAlgebra.lreRowUpperNumeratorAt
#assert_no_axioms FX1Poly.ComputerAlgebra.lreSatisfactionGivesWeakLe
#assert_no_axioms FX1Poly.ComputerAlgebra.lreScaleRelationStrictOfPositive
#assert_no_axioms FX1Poly.ComputerAlgebra.lreJoinStrictLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.lreJoinStrictRight
#assert_no_axioms FX1Poly.ComputerAlgebra.lreComboUnfoldForms
#assert_no_axioms FX1Poly.ComputerAlgebra.lreComboSatisfactionGivesWeakBound
#assert_no_axioms FX1Poly.ComputerAlgebra.lreComboSatisfactionGivesStrictBound
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntLeFalseFlip
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntLeTermTransport
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntLtTermTransport
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntScaledDominanceTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.lreMidpointLowerWeakCore
#assert_no_axioms FX1Poly.ComputerAlgebra.lreMidpointLowerStrictCore
#assert_no_axioms FX1Poly.ComputerAlgebra.lreMidpointUpperWeakCore
#assert_no_axioms FX1Poly.ComputerAlgebra.lreMidpointUpperStrictCore
#assert_no_axioms FX1Poly.ComputerAlgebra.lreLoneLowerEndpointCore
#assert_no_axioms FX1Poly.ComputerAlgebra.lreLoneUpperEndpointCore
#assert_no_axioms FX1Poly.ComputerAlgebra.lreSelectDominatingRow
#assert_no_axioms FX1Poly.ComputerAlgebra.lreSelectDominatingRowSound
#assert_no_axioms FX1Poly.ComputerAlgebra.lreLowerDominates
#assert_no_axioms FX1Poly.ComputerAlgebra.lreUpperDominates
#assert_no_axioms FX1Poly.ComputerAlgebra.lreLowerDominatesTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.lreUpperDominatesTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.lreUpdatedDotForm
#assert_no_axioms FX1Poly.ComputerAlgebra.lreZeroRowStep
#assert_no_axioms FX1Poly.ComputerAlgebra.lrePositiveRowStep
#assert_no_axioms FX1Poly.ComputerAlgebra.lreNegativeRowStep
#assert_no_axioms FX1Poly.ComputerAlgebra.lreAssembleInputSatisfaction
#assert_no_axioms FX1Poly.ComputerAlgebra.lreRoundExtensionForInequalityRows
#assert_no_axioms FX1Poly.ComputerAlgebra.lreRoundExtensionInequalityStatement
#assert_no_axioms FX1Poly.ComputerAlgebra.lreRoundExtensionHolds
#assert_no_axioms FX1Poly.ComputerAlgebra.lreRefutationEqualityRow
#assert_no_axioms FX1Poly.ComputerAlgebra.lreRefutationInequalityRow
#assert_no_axioms FX1Poly.ComputerAlgebra.lreRefutationRows
#assert_no_axioms FX1Poly.ComputerAlgebra.lreRefutationRoundOutputEmptyPin
#assert_no_axioms FX1Poly.ComputerAlgebra.lreRoundExtensionStatementRefuted
#assert_no_axioms FX1Poly.ComputerAlgebra.lreScaleRelationPreservesInequality
#assert_no_axioms FX1Poly.ComputerAlgebra.lreRoundPreservesInequality
#assert_no_axioms FX1Poly.ComputerAlgebra.lreDriverPreservesInequality
#assert_no_axioms FX1Poly.ComputerAlgebra.lreDriverBackwardExtension
#assert_no_axioms FX1Poly.ComputerAlgebra.lreGroundRowSatisfiedByEmptyEnv
#assert_no_axioms FX1Poly.ComputerAlgebra.lreGroundCleanRowsSatisfied
#assert_no_axioms FX1Poly.ComputerAlgebra.lreSeedRowsFromIndexInequality
#assert_no_axioms FX1Poly.ComputerAlgebra.lreAllConstraintsInequality
#assert_no_axioms FX1Poly.ComputerAlgebra.lreExpandSystemInequality
#assert_no_axioms FX1Poly.ComputerAlgebra.lreConstraintAtIndex
#assert_no_axioms FX1Poly.ComputerAlgebra.lreScaledTrivialSatisfied
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntScaleZeroIsZero
#assert_no_axioms FX1Poly.ComputerAlgebra.lreWeightedSumNilCertificate
#assert_no_axioms FX1Poly.ComputerAlgebra.lreUnitSumZeroPeel
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIntScaleOneCrossEq
#assert_no_axioms FX1Poly.ComputerAlgebra.lreHeadSeedExtract
#assert_no_axioms FX1Poly.ComputerAlgebra.lreUnitSumSatGivesRowSat
#assert_no_axioms FX1Poly.ComputerAlgebra.lreSeedsSatGivesUnitSat
#assert_no_axioms FX1Poly.ComputerAlgebra.lreConstraintAtIndexBeyond
#assert_no_axioms FX1Poly.ComputerAlgebra.lreIndexedSatGivesSystemSat
#assert_no_axioms FX1Poly.ComputerAlgebra.lreSeedsSatGivesSystemSat
#assert_no_axioms FX1Poly.ComputerAlgebra.lreExpandedScaledSatGivesOriginalScaledSat
#assert_no_axioms FX1Poly.ComputerAlgebra.lreFarkasCompletenessHolds
#assert_no_axioms FX1Poly.ComputerAlgebra.lreExpandScaleBoundsCommute
#assert_no_axioms FX1Poly.ComputerAlgebra.lreWeightedSumOfScaledBounds
#assert_no_axioms FX1Poly.ComputerAlgebra.lreGroundContradictionScaledBound
#assert_no_axioms FX1Poly.ComputerAlgebra.lreCheckerAcceptsScaledBounds
#assert_no_axioms FX1Poly.ComputerAlgebra.lreScaledInfeasibilityOfAcceptedCertificate
#assert_no_axioms FX1Poly.ComputerAlgebra.fxDissatArith_hasRoundExtension
#assert_no_axioms FX1Poly.ComputerAlgebra.fxDissatArith_roundExtensionAsStatedRefuted
#assert_no_axioms FX1Poly.ComputerAlgebra.fxDissatArith_hasFourierMotzkinCompletenessProven
#assert_no_axioms FX1Poly.ComputerAlgebra.lreSmokeLowerRow
#assert_no_axioms FX1Poly.ComputerAlgebra.lreSmokeUpperRow
#assert_no_axioms FX1Poly.ComputerAlgebra.lreSmokeExtensionRows
#assert_no_axioms FX1Poly.ComputerAlgebra.lreSmokeRoundOneOutputPin
#assert_no_axioms FX1Poly.ComputerAlgebra.lreSmokeRoundTwoOutputPin
#assert_no_axioms FX1Poly.ComputerAlgebra.lreSmokeBackwardStageOnePin
#assert_no_axioms FX1Poly.ComputerAlgebra.lreSmokeBackwardStageTwoPin
#assert_no_axioms FX1Poly.ComputerAlgebra.lreSmokeExtensionScanCleanPin
#assert_no_axioms FX1Poly.ComputerAlgebra.lreRefutationHypothesisHoldsPin
#assert_no_axioms FX1Poly.ComputerAlgebra.lreRefutationInputRejectsZeroPin
#assert_no_axioms FX1Poly.ComputerAlgebra.lreSmokeCompletenessFiredOnContradictory
#assert_no_axioms FX1Poly.ComputerAlgebra.lreSmokeCompletenessFiredOnStrict
#assert_no_axioms FX1Poly.ComputerAlgebra.lreSmokeCompletenessFiredOnTwoVariableChain

end FX1PolyAudit
