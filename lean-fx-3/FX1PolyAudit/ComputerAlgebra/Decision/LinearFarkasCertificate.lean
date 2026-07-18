import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Decision.LinearFarkasCertificate

/-! # FX1PolyAudit/ComputerAlgebra/Decision/LinearFarkasCertificate — zero-axiom gate
    (DISSAT-ARITH brick, half 1: Farkas-certificate refutation for integer linear
    arithmetic, Nat multipliers)

Per-declaration zero-axiom gate for the Farkas certificate route: the hand-rolled
Nat ble/beq reflection + cancellation + mul-monotonicity kit, the Bool conjunction
kit, the unnormalized (positivePart, negativePart) integer pairs `LfkInt` with
cross-sum order/equality and the componentwise algebra, dense coefficient vectors
with PADDING addition and the TRUNCATING dot product (additivity with no length
hypotheses), constraints over `>= / > / =` with Bool satisfaction, the row-splitting
expansion for equalities (`lfkExpandSystem` — an equality consumes two certificate
slots), the weighted sum with zero-degraded scaling (`lfkScaleRelation`) and the
strict-absorbing join (`lfkJoinRelations`), THE CHECKER (`lfkCheckRefutation`:
weighted sum is a ground contradiction), the soundness chain
(`lfkScalePreservesSatisfaction`, `lfkAddPreservesSatisfaction`,
`lfkWeightedSumSatisfied`, `lfkSatisfiesExpandedOfSatisfies`,
`lfkGroundContradictionRefutes`) up to the headline `lfkRefutationSound` /
`lfkRefutationSoundUnconditional`, the honest walls
(`lfkFarkasCompletenessStatement`, owner `fxDissatArith_hasFarkasCompleteness =
false` — future Fourier–Motzkin brick; `lfkPresburgerDecisionStatement`, owner
`fxDissatArith_hasPresburgerDecision = false` — future Cooper brick), the DECIDED
marker `fxDissatArith_hasFarkasCertificate = true`, and the kernel-checked smoke
pins (refutations, rejected bogus certificates, the strictness thread, the
two-slot equality route, and the satisfiable sanity witness).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.lfkNatBeqRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkNatBeqOfEq
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkNatEqOfBeq
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkNatLeOfBle
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkNatBleOfLe
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkNatSuccLeSelfFalse
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkNatAddCongr
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkNatAddSwapMiddle
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkNatAddOneShiftOut
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkNatAddLeftCancel
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkNatAddLeAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkNatLeCongr
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkNatMulLeMulLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkNatMulAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkNatMulLeftCommute
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkNatBothZeroMulSum
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkBoolAndDestruct
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkBoolAndIntro
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkBoolNotTrueImpliesFalse
#assert_no_axioms FX1Poly.ComputerAlgebra.LfkInt
#assert_no_axioms FX1Poly.ComputerAlgebra.LfkInt.mk
#assert_no_axioms FX1Poly.ComputerAlgebra.LfkInt.positivePart
#assert_no_axioms FX1Poly.ComputerAlgebra.LfkInt.negativePart
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntZero
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntMul
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntNegate
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntScaleByNat
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntIsNonNegative
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntIsPositive
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntIsZero
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntEq
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntLe
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntLt
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntMkCongr
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntAddComm
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntAddAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntZeroAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntAddZero
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntEqRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntAddCongr
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntAddSwapMiddle
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntScaleAddDistrib
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntMulAddRight
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntMulScaleRight
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntLeOfLt
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntLeOfEqFlip
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntAddLeAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntAddLtLe
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntAddLeLt
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntAddLtLt
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntAddEqEq
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntScaleLeMono
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntScaleEqMono
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntMulZeroRight
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIntAddZeroPreserving
#assert_no_axioms FX1Poly.ComputerAlgebra.LfkLinearTerm
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkAddCoefficientVectors
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkScaleCoefficientVector
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkNegateCoefficientVector
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkDotProduct
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkDotProductNilRight
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkDotProductAddVectors
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkDotProductScaledVector
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkDotProductNegatedVector
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkAllCoefficientsAreZero
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkDotProductZeroCoefficients
#assert_no_axioms FX1Poly.ComputerAlgebra.LfkRelation
#assert_no_axioms FX1Poly.ComputerAlgebra.LfkRelation.isGreaterOrEqual
#assert_no_axioms FX1Poly.ComputerAlgebra.LfkRelation.isStrictlyGreater
#assert_no_axioms FX1Poly.ComputerAlgebra.LfkRelation.isEqualTo
#assert_no_axioms FX1Poly.ComputerAlgebra.LfkConstraint
#assert_no_axioms FX1Poly.ComputerAlgebra.LfkConstraint.mk
#assert_no_axioms FX1Poly.ComputerAlgebra.LfkConstraint.coefficients
#assert_no_axioms FX1Poly.ComputerAlgebra.LfkConstraint.bound
#assert_no_axioms FX1Poly.ComputerAlgebra.LfkConstraint.relation
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkSatisfiesConstraint
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkSatisfiesSystem
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkEnvMatchesLength
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkForwardEqualityRow
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkFlipEqualityRow
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkExpandSystem
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkScaleRelation
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkJoinRelations
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkScaleConstraint
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkAddConstraints
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkTrivialConstraint
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkTrivialSatisfied
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkWeightedSum
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkBoundViolatesRelation
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkIsGroundContradiction
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkCheckRefutation
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkScalePreservesSatisfaction
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkAddPreservesSatisfaction
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkWeightedSumSatisfied
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkSatisfiesExpandedOfSatisfies
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkGroundContradictionRefutes
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkRefutationSoundUnconditional
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkRefutationSound
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkScaleBoundsForDenominator
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkFarkasCompletenessStatement
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkPresburgerDecisionStatement
#assert_no_axioms FX1Poly.ComputerAlgebra.fxDissatArith_hasFarkasCertificate
#assert_no_axioms FX1Poly.ComputerAlgebra.fxDissatArith_hasFarkasCompleteness
#assert_no_axioms FX1Poly.ComputerAlgebra.fxDissatArith_hasPresburgerDecision
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkSmokeContradictorySystem
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkSmokeSatisfiableTriple
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkSmokeStrictSystem
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkSmokeEqualitySystem
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkSmokeSatisfiablePair
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkSmokeSatisfyingEnv
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkSmokeContradictoryPin
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkSmokeBogusCertificatePin
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkSmokeSatisfiableTriplePin
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkSmokeStrictPin
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkSmokeEqualityPin
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkSmokeEmptyPin
#assert_no_axioms FX1Poly.ComputerAlgebra.lfkSmokeSatisfyingEnvPin

end FX1PolyAudit
