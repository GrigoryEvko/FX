import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Decision.ClauseProofChecker

/-! # FX1PolyAudit/ComputerAlgebra/Decision/ClauseProofChecker — zero-axiom gate
    (the certified LRAT-style clause-proof checker: hinted RUP + deletion + RAT)

Per-declaration zero-axiom gate for the clause-proof checker: the Boolean/Nat structural kits,
literals with hand-rolled decidable equality, the clause/formula/forced-list Boolean semantics with
the membership force lemma, the unfalsified-survivor collector with its truth-preservation engine
(`cpcCollectPreservesTruth`), positional clause fetch/removal, the fuel-free hint-driven RUP walk
with the propagation invariant (`cpcRupHintsSound`) and the entailment bridge
(`cpcRupAdditionEntails`), the proof-trace walker with RUP additions, positional deletions, and the
empty-clause acceptance, the RAT extension (whole-formula candidate coverage + the constructive
pivot-flip model-modification chain `cpcFlipEnv`/`cpcRatCandidatesSound`), and the headline theorem
`cpcProofSound`: an accepted trace refutes every assignment of the input formula.

Markers: `fxDissatResidue_hasRupChecker := true`, `fxDissatResidue_hasRatExtension := true`,
`fxDissatResidue_hasCdclFinder := false` (the finder is out of scope by architecture: search is
untrusted, only checking is kernel).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.cpcAndLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcAndRight
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcAndIntro
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcOrCases
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcOrIntroLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcOrIntroRight
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcOrFalseSplit
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcNatBeq
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcNatBeqRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcNatBeqImpliesEq
#assert_no_axioms FX1Poly.ComputerAlgebra.CpcLiteral
#assert_no_axioms FX1Poly.ComputerAlgebra.CpcLiteral.mk
#assert_no_axioms FX1Poly.ComputerAlgebra.CpcLiteral.variableIndex
#assert_no_axioms FX1Poly.ComputerAlgebra.CpcLiteral.isPositive
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcNegate
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcBoolBeq
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcBoolBeqRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcBoolBeqImpliesEq
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcLiteralBeq
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcLiteralBeqRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcLiteralBeqImpliesEq
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcLiteralBeqFalseSymm
#assert_no_axioms FX1Poly.ComputerAlgebra.CpcClause
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcLiteralHolds
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcHoldsNegate
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcClauseHolds
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcFormulaHolds
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcLiteralMember
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcAllLiteralsHold
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcMemberHolds
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcNegateAll
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcFalseClauseNegationsHold
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcCollectUnfalsified
#assert_no_axioms FX1Poly.ComputerAlgebra.CpcClauseStatus
#assert_no_axioms FX1Poly.ComputerAlgebra.CpcClauseStatus.isFalsified
#assert_no_axioms FX1Poly.ComputerAlgebra.CpcClauseStatus.forcesUnit
#assert_no_axioms FX1Poly.ComputerAlgebra.CpcClauseStatus.isUnresolved
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcClauseStatus
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcCollectPreservesTruth
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcStatusFalsifiedCollectNil
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcStatusUnitCollectSingleton
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcGetClause
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcGetClauseHolds
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcRemoveClauseAt
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcRemoveClauseAtPreservesHolds
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcCheckRupHints
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcRupHintsSound
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcCheckRupAddition
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcRupAdditionEntails
#assert_no_axioms FX1Poly.ComputerAlgebra.CpcRatHintGroup
#assert_no_axioms FX1Poly.ComputerAlgebra.CpcRatHintGroup.mk
#assert_no_axioms FX1Poly.ComputerAlgebra.CpcRatHintGroup.candidateIndex
#assert_no_axioms FX1Poly.ComputerAlgebra.CpcRatHintGroup.unitHints
#assert_no_axioms FX1Poly.ComputerAlgebra.CpcProofStep
#assert_no_axioms FX1Poly.ComputerAlgebra.CpcProofStep.addClause
#assert_no_axioms FX1Poly.ComputerAlgebra.CpcProofStep.addRatClause
#assert_no_axioms FX1Poly.ComputerAlgebra.CpcProofStep.deleteClause
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcRatHintLookup
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcRemoveLiteral
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcStackLiterals
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcStackAllHold
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcCheckRatCandidates
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcCheckProofSteps
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcCheckProof
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcFlipEnv
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcFlipEnvSatisfiesPivot
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcFlipEnvPreservesLiteral
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcFlipEnvPreservesClause
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcRemoveLiteralNotMember
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcRemoveLiteralHoldsLift
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcRatCandidateEntails
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcRatCandidatesSound
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcProofStepsSound
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcProofSound
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcPositiveLiteral
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcNegativeLiteral
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcSmokeUnitChainFormula
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcSmokeUnitChainTrace
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcSmokeSatisfiableFormula
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcSmokeChainSatisfiableFormula
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcSmokeFourClauseFormula
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcSmokeFourClauseTrace
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcSmokeRatFormula
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcSmokeRatTrace
#assert_no_axioms FX1Poly.ComputerAlgebra.cpcSmokeRatMissingCandidateFormula
#assert_no_axioms FX1Poly.ComputerAlgebra.fxDissatResidue_hasRupChecker
#assert_no_axioms FX1Poly.ComputerAlgebra.fxDissatResidue_hasRatExtension
#assert_no_axioms FX1Poly.ComputerAlgebra.fxDissatResidue_hasCdclFinder

end FX1PolyAudit
