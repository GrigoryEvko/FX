import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Decision.CombinationDispatch

/-! # FX1PolyAudit/ComputerAlgebra/Decision/CombinationDispatch — zero-axiom gate
    (DISSAT-COMBINE brick: certificate-level Nelson–Oppen combination of the
    ground-congruence and Farkas engines)

Per-declaration zero-axiom gate for the combination dispatch: the cross-sum
equivalence kit on `LfkInt` (symmetry, transitivity via middle-value cancellation,
the unit-multiplication laws), the purified problem `NocProblem` with the shared
interface (variable index ↦ ground term), dense environment lookup and unit /
difference vectors (padding sums, no subtraction), the joint-model semantics
(`nocFunctionalConsistencyHolds`, `nocIsJointModel`) and its two-theory grounding
(`NocMixedModel`, `nocGroundTermValue`, the `GccDeriv` induction
`nocDerivPreservedByModel`, and `nocModelAgreementGivesConsistency` — the bridge is
derived, not assumed), the combination certificate `NocCertificate` with THE CHECKER
(`nocCheckCombination`: every derived equality gcc-checks and the Farkas certificate
refutes the equality-augmented A-side), the soundness chain (`nocDotUnitVector`,
`nocDotDifferenceVector`, `nocDerivedRowSatisfiedOfEnvEq`,
`nocCheckedEqualityGivesEnvEq`, `nocAugmentedSystemSatisfied`) up to the headlines
`nocCombinationSound` / `nocCombinationSoundForMixedSemantics`, the end-to-end finder
(one-round E→A propagation filtered by the checker itself + the sibling
Fourier–Motzkin finder; `nocFinderSound`, `nocFinderRefutesJointModels`), the honest
walls over the faithful mixed AST (`nocPurificationStatement`, owner
`fxDissatCombine_hasPurificationEquivalence = false` — the purifier itself is the
missing artifact; `nocCombinationCompletenessStatement`, owner
`fxDissatCombine_hasCombinationCompleteness = false` — FALSE over ℤ as stated,
convexity / Farkas-ℚ-completeness / amalgamation legs named), the DECIDED markers
`fxDissatCombine_hasDispatchSoundness = true` and
`fxDissatCombine_hasEndToEndFinder = true`, and the kernel-checked smoke pins
(accepted joint contradiction, rejected unprovable-equality and bogus-multiplier
certificates, the pure-A degenerate dispatch, finder hit and miss, the exhibited
joint model of the satisfiable variant, and the universal no-certificate capstone).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.nocIntEqSymm
#assert_no_axioms FX1Poly.ComputerAlgebra.nocNatCrossSumTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.nocIntEqTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.nocIntZeroMul
#assert_no_axioms FX1Poly.ComputerAlgebra.nocPositiveUnit
#assert_no_axioms FX1Poly.ComputerAlgebra.nocNegativeUnit
#assert_no_axioms FX1Poly.ComputerAlgebra.nocIntMulPositiveUnit
#assert_no_axioms FX1Poly.ComputerAlgebra.nocIntMulNegativeUnit
#assert_no_axioms FX1Poly.ComputerAlgebra.nocIntAddNegateEqZero
#assert_no_axioms FX1Poly.ComputerAlgebra.NocProblem
#assert_no_axioms FX1Poly.ComputerAlgebra.NocProblem.mk
#assert_no_axioms FX1Poly.ComputerAlgebra.NocProblem.equationalPart
#assert_no_axioms FX1Poly.ComputerAlgebra.NocProblem.arithmeticPart
#assert_no_axioms FX1Poly.ComputerAlgebra.NocProblem.sharedInterface
#assert_no_axioms FX1Poly.ComputerAlgebra.nocSharedLookup
#assert_no_axioms FX1Poly.ComputerAlgebra.nocEnvValueAt
#assert_no_axioms FX1Poly.ComputerAlgebra.nocUnitCoefficientVector
#assert_no_axioms FX1Poly.ComputerAlgebra.nocDifferenceVector
#assert_no_axioms FX1Poly.ComputerAlgebra.nocDerivedEqualityConstraint
#assert_no_axioms FX1Poly.ComputerAlgebra.nocFunctionalConsistencyHolds
#assert_no_axioms FX1Poly.ComputerAlgebra.nocIsJointModel
#assert_no_axioms FX1Poly.ComputerAlgebra.NocMixedModel
#assert_no_axioms FX1Poly.ComputerAlgebra.NocMixedModel.mk
#assert_no_axioms FX1Poly.ComputerAlgebra.NocMixedModel.symbolValue
#assert_no_axioms FX1Poly.ComputerAlgebra.NocMixedModel.applyValue
#assert_no_axioms FX1Poly.ComputerAlgebra.nocGroundTermValue
#assert_no_axioms FX1Poly.ComputerAlgebra.nocModelRespectsIntEq
#assert_no_axioms FX1Poly.ComputerAlgebra.nocModelSatisfiesEquations
#assert_no_axioms FX1Poly.ComputerAlgebra.nocDerivPreservedByModel
#assert_no_axioms FX1Poly.ComputerAlgebra.nocEnvAgreesWithModel
#assert_no_axioms FX1Poly.ComputerAlgebra.nocModelAgreementGivesConsistency
#assert_no_axioms FX1Poly.ComputerAlgebra.NocCertificate
#assert_no_axioms FX1Poly.ComputerAlgebra.NocCertificate.mk
#assert_no_axioms FX1Poly.ComputerAlgebra.NocCertificate.derivedEqualities
#assert_no_axioms FX1Poly.ComputerAlgebra.NocCertificate.farkasMultipliers
#assert_no_axioms FX1Poly.ComputerAlgebra.nocDecideOptionPairEquality
#assert_no_axioms FX1Poly.ComputerAlgebra.nocCheckDerivedEquality
#assert_no_axioms FX1Poly.ComputerAlgebra.nocCheckAllDerivedEqualities
#assert_no_axioms FX1Poly.ComputerAlgebra.nocAugmentSystem
#assert_no_axioms FX1Poly.ComputerAlgebra.nocCheckCombination
#assert_no_axioms FX1Poly.ComputerAlgebra.nocDotUnitVector
#assert_no_axioms FX1Poly.ComputerAlgebra.nocDotDifferenceVector
#assert_no_axioms FX1Poly.ComputerAlgebra.nocDerivedRowSatisfiedOfEnvEq
#assert_no_axioms FX1Poly.ComputerAlgebra.nocCheckedEqualityGivesEnvEq
#assert_no_axioms FX1Poly.ComputerAlgebra.nocAugmentedSystemSatisfied
#assert_no_axioms FX1Poly.ComputerAlgebra.nocCombinationSound
#assert_no_axioms FX1Poly.ComputerAlgebra.nocCombinationSoundForMixedSemantics
#assert_no_axioms FX1Poly.ComputerAlgebra.nocIndexPairListAppend
#assert_no_axioms FX1Poly.ComputerAlgebra.nocCollectProvablePairs
#assert_no_axioms FX1Poly.ComputerAlgebra.nocPropagateOverSuffix
#assert_no_axioms FX1Poly.ComputerAlgebra.nocPropagateEqualities
#assert_no_axioms FX1Poly.ComputerAlgebra.nocAssembleCertificate
#assert_no_axioms FX1Poly.ComputerAlgebra.nocFindRefutation
#assert_no_axioms FX1Poly.ComputerAlgebra.nocCheckAllAppend
#assert_no_axioms FX1Poly.ComputerAlgebra.nocCollectedPairsAllCheck
#assert_no_axioms FX1Poly.ComputerAlgebra.nocPropagateOverSuffixAllCheck
#assert_no_axioms FX1Poly.ComputerAlgebra.nocPropagatedAllCheck
#assert_no_axioms FX1Poly.ComputerAlgebra.nocAssembleCertificateInversion
#assert_no_axioms FX1Poly.ComputerAlgebra.nocFinderSound
#assert_no_axioms FX1Poly.ComputerAlgebra.nocFinderRefutesJointModels
#assert_no_axioms FX1Poly.ComputerAlgebra.NocMixedTerm
#assert_no_axioms FX1Poly.ComputerAlgebra.NocMixedTerm.symbol
#assert_no_axioms FX1Poly.ComputerAlgebra.NocMixedTerm.apply
#assert_no_axioms FX1Poly.ComputerAlgebra.NocMixedTerm.literal
#assert_no_axioms FX1Poly.ComputerAlgebra.NocMixedTerm.addition
#assert_no_axioms FX1Poly.ComputerAlgebra.NocMixedTerm.scaling
#assert_no_axioms FX1Poly.ComputerAlgebra.nocMixedTermDenotation
#assert_no_axioms FX1Poly.ComputerAlgebra.NocMixedAtom
#assert_no_axioms FX1Poly.ComputerAlgebra.NocMixedAtom.mk
#assert_no_axioms FX1Poly.ComputerAlgebra.NocMixedAtom.leftTerm
#assert_no_axioms FX1Poly.ComputerAlgebra.NocMixedAtom.rightTerm
#assert_no_axioms FX1Poly.ComputerAlgebra.NocMixedAtom.relation
#assert_no_axioms FX1Poly.ComputerAlgebra.nocMixedAtomHolds
#assert_no_axioms FX1Poly.ComputerAlgebra.nocMixedAtomsHold
#assert_no_axioms FX1Poly.ComputerAlgebra.nocPurificationStatement
#assert_no_axioms FX1Poly.ComputerAlgebra.nocCombinationCompletenessStatement
#assert_no_axioms FX1Poly.ComputerAlgebra.fxDissatCombine_hasDispatchSoundness
#assert_no_axioms FX1Poly.ComputerAlgebra.fxDissatCombine_hasEndToEndFinder
#assert_no_axioms FX1Poly.ComputerAlgebra.fxDissatCombine_hasPurificationEquivalence
#assert_no_axioms FX1Poly.ComputerAlgebra.fxDissatCombine_hasCombinationCompleteness
#assert_no_axioms FX1Poly.ComputerAlgebra.nocSmokeTermA
#assert_no_axioms FX1Poly.ComputerAlgebra.nocSmokeTermB
#assert_no_axioms FX1Poly.ComputerAlgebra.nocSmokeTermFofA
#assert_no_axioms FX1Poly.ComputerAlgebra.nocSmokeEquations
#assert_no_axioms FX1Poly.ComputerAlgebra.nocSmokeSharedInterface
#assert_no_axioms FX1Poly.ComputerAlgebra.nocSmokeArithmeticPart
#assert_no_axioms FX1Poly.ComputerAlgebra.nocSmokeProblem
#assert_no_axioms FX1Poly.ComputerAlgebra.nocSmokeCertificate
#assert_no_axioms FX1Poly.ComputerAlgebra.nocSmokeNoEquationsProblem
#assert_no_axioms FX1Poly.ComputerAlgebra.nocSmokeSatisfiableArithmetic
#assert_no_axioms FX1Poly.ComputerAlgebra.nocSmokeSatisfiableProblem
#assert_no_axioms FX1Poly.ComputerAlgebra.nocSmokeSatisfyingEnv
#assert_no_axioms FX1Poly.ComputerAlgebra.nocSmokePureArithmeticProblem
#assert_no_axioms FX1Poly.ComputerAlgebra.nocSmokePureArithmeticCertificate
#assert_no_axioms FX1Poly.ComputerAlgebra.nocSmokeAcceptedPin
#assert_no_axioms FX1Poly.ComputerAlgebra.nocSmokeUnprovableEqualityPin
#assert_no_axioms FX1Poly.ComputerAlgebra.nocSmokeBogusMultipliersPin
#assert_no_axioms FX1Poly.ComputerAlgebra.nocSmokePureArithmeticPin
#assert_no_axioms FX1Poly.ComputerAlgebra.nocSmokeEmptyPin
#assert_no_axioms FX1Poly.ComputerAlgebra.nocSmokeFinderHitPin
#assert_no_axioms FX1Poly.ComputerAlgebra.nocSmokeFinderMissPin
#assert_no_axioms FX1Poly.ComputerAlgebra.nocSmokeLookupForcesSeven
#assert_no_axioms FX1Poly.ComputerAlgebra.nocSmokeSatisfiableJointModelPin
#assert_no_axioms FX1Poly.ComputerAlgebra.nocSmokeSatisfiableHasNoCertificate

end FX1PolyAudit
