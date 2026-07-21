import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Decision.GroebnerMembership

/-! # FX1PolyAudit/ComputerAlgebra/Decision/GroebnerMembership — zero-axiom gate
    (ideal membership by checkable cofactor certificates, F2 coefficients)

Per-declaration zero-axiom gate for the Gröbner certificate route: the hand-rolled
Bool xor/and kit, the Nat beq/strict-order kit, `GrbVarPower` variable powers with
structural beq, exponent vectors with the merge-with-addition product (`grbExpMul`),
the graded-lex monomial order (`grbMonoLess` over hand-rolled degree + lex) with its
four hand-proved order laws, sorted F2 polynomial lists with insert-fold arithmetic
(`grbMonoInsert` / `grbAdd` / `grbMul` / `grbScaleByMonomial`), the strict-descending
sortedness invariant closed under every operation, the F2 coefficient scan with the
sorted-list extensionality keystone (`grbPolyExtensionality`) and the one-fire AC
family it powers, the semantic ideal-membership inductive `GrbInIdeal`, THE CHECKER
(`grbCheckCertificate`) with the headline soundness `grbCertificateSound` and the
ring-equality corollaries, the evaluation homomorphism (`grbEvalPoly`) grounding the
ideal semantically (`grbInIdealVanishesOnCommonZero`, `grbRingEqualityByCertificate`),
the fuel-bounded finder (`grbReduceStep` / `grbReduce`) with THE INVARIANT
(`grbReduceInvariant`) and finder soundness (`grbFinderSound` — finder success always
yields a certificate the checker accepts), the honest wall
(`grbNonMembershipDecisionStatement`, owner `fxDissatGrob_hasNonMembershipDecision =
false`, walled at Dickson `fxNet4_dicksonWall` + Newman confluence), and the DECIDED
marker `fxDissatGrob_hasCertificateRoute = true`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.grbBoolXor
#assert_no_axioms FX1Poly.ComputerAlgebra.grbBoolXorFalseRight
#assert_no_axioms FX1Poly.ComputerAlgebra.grbBoolXorSelfIsFalse
#assert_no_axioms FX1Poly.ComputerAlgebra.grbBoolXorAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.grbBoolXorSwapLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.grbBoolXorLeftSelfCancel
#assert_no_axioms FX1Poly.ComputerAlgebra.grbBoolXorCrossCancel
#assert_no_axioms FX1Poly.ComputerAlgebra.grbBoolXorLeftInjective
#assert_no_axioms FX1Poly.ComputerAlgebra.grbBoolXorEqFalseImpliesEq
#assert_no_axioms FX1Poly.ComputerAlgebra.grbBoolXorAndRightFactor
#assert_no_axioms FX1Poly.ComputerAlgebra.grbBoolAndDistribXor
#assert_no_axioms FX1Poly.ComputerAlgebra.grbBoolAndSwapLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.grbBoolAndAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.grbBoolAndTrueRight
#assert_no_axioms FX1Poly.ComputerAlgebra.grbBoolAndFalseRight
#assert_no_axioms FX1Poly.ComputerAlgebra.grbBoolAndElim
#assert_no_axioms FX1Poly.ComputerAlgebra.grbBoolAndTrueLeftFalse
#assert_no_axioms FX1Poly.ComputerAlgebra.grbNatBeqRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.grbNatBeqEq
#assert_no_axioms FX1Poly.ComputerAlgebra.grbNatBeqSymmFalse
#assert_no_axioms FX1Poly.ComputerAlgebra.grbNatLess
#assert_no_axioms FX1Poly.ComputerAlgebra.grbNatLessIrrefl
#assert_no_axioms FX1Poly.ComputerAlgebra.grbNatLessAsym
#assert_no_axioms FX1Poly.ComputerAlgebra.grbNatLessTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.grbNatLessTotal
#assert_no_axioms FX1Poly.ComputerAlgebra.grbNatLessOrEq
#assert_no_axioms FX1Poly.ComputerAlgebra.grbNatMinus
#assert_no_axioms FX1Poly.ComputerAlgebra.GrbVarPower
#assert_no_axioms FX1Poly.ComputerAlgebra.GrbVarPower.mk
#assert_no_axioms FX1Poly.ComputerAlgebra.GrbVarPower.variableIndex
#assert_no_axioms FX1Poly.ComputerAlgebra.GrbVarPower.exponent
#assert_no_axioms FX1Poly.ComputerAlgebra.grbVarPowerBeq
#assert_no_axioms FX1Poly.ComputerAlgebra.grbVarPowerBeqRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.grbVarPowerBeqEq
#assert_no_axioms FX1Poly.ComputerAlgebra.GrbExp
#assert_no_axioms FX1Poly.ComputerAlgebra.grbExpBeq
#assert_no_axioms FX1Poly.ComputerAlgebra.grbExpBeqRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.grbExpBeqEq
#assert_no_axioms FX1Poly.ComputerAlgebra.grbExpDegree
#assert_no_axioms FX1Poly.ComputerAlgebra.grbExpInsert
#assert_no_axioms FX1Poly.ComputerAlgebra.grbExpInsertOnSharedVariable
#assert_no_axioms FX1Poly.ComputerAlgebra.grbExpInsertOnEarlierVariable
#assert_no_axioms FX1Poly.ComputerAlgebra.grbExpInsertOnLaterVariable
#assert_no_axioms FX1Poly.ComputerAlgebra.grbExpMul
#assert_no_axioms FX1Poly.ComputerAlgebra.grbExpLexLess
#assert_no_axioms FX1Poly.ComputerAlgebra.grbExpLexLessIrrefl
#assert_no_axioms FX1Poly.ComputerAlgebra.grbExpLexLessAsym
#assert_no_axioms FX1Poly.ComputerAlgebra.grbExpLexLessTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.grbExpLexLessTotal
#assert_no_axioms FX1Poly.ComputerAlgebra.grbMonoLess
#assert_no_axioms FX1Poly.ComputerAlgebra.grbMonoLessIrrefl
#assert_no_axioms FX1Poly.ComputerAlgebra.grbMonoLessAsym
#assert_no_axioms FX1Poly.ComputerAlgebra.grbMonoLessTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.grbMonoLessTotal
#assert_no_axioms FX1Poly.ComputerAlgebra.GrbPoly
#assert_no_axioms FX1Poly.ComputerAlgebra.grbPolyBeq
#assert_no_axioms FX1Poly.ComputerAlgebra.grbPolyBeqRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.grbPolyBeqEq
#assert_no_axioms FX1Poly.ComputerAlgebra.grbZero
#assert_no_axioms FX1Poly.ComputerAlgebra.grbOnePoly
#assert_no_axioms FX1Poly.ComputerAlgebra.grbVariablePoly
#assert_no_axioms FX1Poly.ComputerAlgebra.grbMonoInsert
#assert_no_axioms FX1Poly.ComputerAlgebra.grbMonoInsertOnCollision
#assert_no_axioms FX1Poly.ComputerAlgebra.grbMonoInsertOnGreater
#assert_no_axioms FX1Poly.ComputerAlgebra.grbMonoInsertOnSmaller
#assert_no_axioms FX1Poly.ComputerAlgebra.grbAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.grbNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.grbScale
#assert_no_axioms FX1Poly.ComputerAlgebra.grbScaleByMonomial
#assert_no_axioms FX1Poly.ComputerAlgebra.grbMul
#assert_no_axioms FX1Poly.ComputerAlgebra.grbMulNilLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.grbSumOfProducts
#assert_no_axioms FX1Poly.ComputerAlgebra.GrbPolySorted
#assert_no_axioms FX1Poly.ComputerAlgebra.GrbPolySorted.nilIsSorted
#assert_no_axioms FX1Poly.ComputerAlgebra.GrbPolySorted.singleIsSorted
#assert_no_axioms FX1Poly.ComputerAlgebra.GrbPolySorted.consIsSorted
#assert_no_axioms FX1Poly.ComputerAlgebra.grbSortedTail
#assert_no_axioms FX1Poly.ComputerAlgebra.grbSortedSkip
#assert_no_axioms FX1Poly.ComputerAlgebra.grbMonoInsertUnderHead
#assert_no_axioms FX1Poly.ComputerAlgebra.grbMonoInsertKeepsSorted
#assert_no_axioms FX1Poly.ComputerAlgebra.grbAddKeepsSorted
#assert_no_axioms FX1Poly.ComputerAlgebra.grbMulIsSorted
#assert_no_axioms FX1Poly.ComputerAlgebra.grbSumOfProductsIsSorted
#assert_no_axioms FX1Poly.ComputerAlgebra.grbCoeff
#assert_no_axioms FX1Poly.ComputerAlgebra.grbCoeffMonoInsert
#assert_no_axioms FX1Poly.ComputerAlgebra.grbCoeffAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.grbCoeffFalseUnderHead
#assert_no_axioms FX1Poly.ComputerAlgebra.grbCoeffTrueImpliesLessThanHead
#assert_no_axioms FX1Poly.ComputerAlgebra.grbPolyExtensionality
#assert_no_axioms FX1Poly.ComputerAlgebra.grbAddNilRightIsIdentity
#assert_no_axioms FX1Poly.ComputerAlgebra.grbAddAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.grbAddSwapLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.grbAddCrossCancel
#assert_no_axioms FX1Poly.ComputerAlgebra.grbAddSelfCancelLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.grbAddSelfIsZero
#assert_no_axioms FX1Poly.ComputerAlgebra.grbMulMonoInsert
#assert_no_axioms FX1Poly.ComputerAlgebra.GrbMember
#assert_no_axioms FX1Poly.ComputerAlgebra.GrbMember.atHead
#assert_no_axioms FX1Poly.ComputerAlgebra.GrbMember.inTail
#assert_no_axioms FX1Poly.ComputerAlgebra.GrbInIdeal
#assert_no_axioms FX1Poly.ComputerAlgebra.GrbInIdeal.byZeroPolynomial
#assert_no_axioms FX1Poly.ComputerAlgebra.GrbInIdeal.byGenerator
#assert_no_axioms FX1Poly.ComputerAlgebra.GrbInIdeal.byAddition
#assert_no_axioms FX1Poly.ComputerAlgebra.GrbInIdeal.byPolynomialScale
#assert_no_axioms FX1Poly.ComputerAlgebra.grbCheckCertificate
#assert_no_axioms FX1Poly.ComputerAlgebra.grbSumOfProductsInIdeal
#assert_no_axioms FX1Poly.ComputerAlgebra.grbCertificateSound
#assert_no_axioms FX1Poly.ComputerAlgebra.grbDifferenceInIdealByCertificate
#assert_no_axioms FX1Poly.ComputerAlgebra.grbBoolPow
#assert_no_axioms FX1Poly.ComputerAlgebra.grbBoolPowAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.grbEvalMonomial
#assert_no_axioms FX1Poly.ComputerAlgebra.grbEvalPoly
#assert_no_axioms FX1Poly.ComputerAlgebra.grbEvalMonomialInsert
#assert_no_axioms FX1Poly.ComputerAlgebra.grbEvalMonomialMul
#assert_no_axioms FX1Poly.ComputerAlgebra.grbEvalScaleByMonomial
#assert_no_axioms FX1Poly.ComputerAlgebra.grbEvalPolyMonoInsert
#assert_no_axioms FX1Poly.ComputerAlgebra.grbEvalPolyAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.grbEvalPolyMul
#assert_no_axioms FX1Poly.ComputerAlgebra.grbEvalPolyNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.grbInIdealVanishesOnCommonZero
#assert_no_axioms FX1Poly.ComputerAlgebra.grbRingEqualityByCertificate
#assert_no_axioms FX1Poly.ComputerAlgebra.grbExpLookup
#assert_no_axioms FX1Poly.ComputerAlgebra.grbExpDivides
#assert_no_axioms FX1Poly.ComputerAlgebra.grbExpQuotient
#assert_no_axioms FX1Poly.ComputerAlgebra.GrbReducerChoice
#assert_no_axioms FX1Poly.ComputerAlgebra.GrbReducerChoice.mk
#assert_no_axioms FX1Poly.ComputerAlgebra.GrbReducerChoice.cofactorIndex
#assert_no_axioms FX1Poly.ComputerAlgebra.GrbReducerChoice.quotientExponent
#assert_no_axioms FX1Poly.ComputerAlgebra.GrbReducerChoice.reducerBody
#assert_no_axioms FX1Poly.ComputerAlgebra.grbBumpReducerIndex
#assert_no_axioms FX1Poly.ComputerAlgebra.grbFindReducer
#assert_no_axioms FX1Poly.ComputerAlgebra.grbGeneratorAt
#assert_no_axioms FX1Poly.ComputerAlgebra.grbFindReducerPointsAtGenerator
#assert_no_axioms FX1Poly.ComputerAlgebra.grbHasSameLength
#assert_no_axioms FX1Poly.ComputerAlgebra.grbUpdateCofactors
#assert_no_axioms FX1Poly.ComputerAlgebra.grbUpdateCofactorsKeepLength
#assert_no_axioms FX1Poly.ComputerAlgebra.grbSumUpdateCofactors
#assert_no_axioms FX1Poly.ComputerAlgebra.GrbReduceResult
#assert_no_axioms FX1Poly.ComputerAlgebra.GrbReduceResult.mk
#assert_no_axioms FX1Poly.ComputerAlgebra.GrbReduceResult.remainderPoly
#assert_no_axioms FX1Poly.ComputerAlgebra.GrbReduceResult.cofactorPolys
#assert_no_axioms FX1Poly.ComputerAlgebra.grbApplyReducerChoice
#assert_no_axioms FX1Poly.ComputerAlgebra.grbReduceStep
#assert_no_axioms FX1Poly.ComputerAlgebra.grbReduce
#assert_no_axioms FX1Poly.ComputerAlgebra.grbReduceStepPreservesSum
#assert_no_axioms FX1Poly.ComputerAlgebra.grbReduceOnStuckStep
#assert_no_axioms FX1Poly.ComputerAlgebra.grbReduceOnFiringStep
#assert_no_axioms FX1Poly.ComputerAlgebra.grbReduceInvariant
#assert_no_axioms FX1Poly.ComputerAlgebra.grbZeroCofactorsFor
#assert_no_axioms FX1Poly.ComputerAlgebra.grbZeroCofactorsMatchLength
#assert_no_axioms FX1Poly.ComputerAlgebra.grbSumOfZeroCofactorsIsNil
#assert_no_axioms FX1Poly.ComputerAlgebra.grbFinderSound
#assert_no_axioms FX1Poly.ComputerAlgebra.grbNonMembershipDecisionStatement
#assert_no_axioms FX1Poly.ComputerAlgebra.fxDissatGrob_hasNonMembershipDecision
#assert_no_axioms FX1Poly.ComputerAlgebra.fxDissatGrob_hasCertificateRoute
#assert_no_axioms FX1Poly.ComputerAlgebra.grbSmokeXPlusY
#assert_no_axioms FX1Poly.ComputerAlgebra.grbSmokeSquareOfXPlusY
#assert_no_axioms FX1Poly.ComputerAlgebra.grbSmokeXTimesY
#assert_no_axioms FX1Poly.ComputerAlgebra.grbSmokeTwoGenTarget

end FX1PolyAudit
