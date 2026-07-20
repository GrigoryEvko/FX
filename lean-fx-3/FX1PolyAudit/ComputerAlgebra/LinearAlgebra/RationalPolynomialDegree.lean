import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.RationalPolynomialDegree

/-! # FX1PolyAudit/.../RationalPolynomialDegree — zero-axiom gate

Per-declaration zero-axiom gate for the ℚ[x] degree-based termination bound — the field step that flips the
committed `rpxHasRemainderDegreeBound` owner-false: the positional coefficient accessor with each ring
operation a coefficientwise homomorphism, the monomial-product coefficient shift, the coefficient bounds
(past-length, trimming agreement, vanishing above the trimmed length), the leading-coefficient↔degree
bridge, the trimmed-length bound from coefficient vanishing, the per-step leading-term cancellation
(`rpdStepTopCoeffCancels`, the field-specific `qnfInvMulCancels` cancellation), the strict trimmed-length
decrease (`rpdStepTrimLengthDecreases`, T1), the fuel adequacy (`rpdRemainderAdequate`, T2), the remainder
degree bound at the adequate fuel (`rpdDivModRemainderDegree`, T3), the fires, and the content marker.

Every definition is structural on the coefficient list and the position; arithmetic routes through the
shipped `qnf*` field laws; the only non-list case analyses are `qnfDecEq _ qnfZero` and `Nat.decLt` (full
`isTrue`/`isFalse` enumeration).  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`, `funext`, `WellFounded.fix`. -/

namespace FX1PolyAudit

-- Small Nat helper
#assert_no_axioms FX1Poly.ComputerAlgebra.rpdNatSubAddCancel

-- The positional coefficient accessor and its ring homomorphisms
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxCoeff
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxCoeffScale
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxCoeffAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxCoeffNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxCoeffSub

-- The monomial-times-polynomial coefficient shift
#assert_no_axioms FX1Poly.ComputerAlgebra.rpdCoeffSingletonZero
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxCoeffMonomialMul
#assert_no_axioms FX1Poly.ComputerAlgebra.rpdCoeffMonomialZeroMulZero

-- Coefficient bounds
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxCoeffPastLength
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxCoeffTrimAgree
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxCoeffZeroFromTrimLength

-- The leading-coefficient↔degree bridge and the trim invariant
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxCoeffTrimLengthEqLastOrZero
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxLeadingCoeffEqCoeffDegree
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxTrimNilOrLastNonzero
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxLeadingCoeffNonzeroWhenNonempty
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxCoeffAtDegreeNonzeroWhenNonempty
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxTrimLengthEqDegreeSucc

-- The trimmed-length bound from coefficient vanishing
#assert_no_axioms FX1Poly.ComputerAlgebra.rpdTrimLengthLeOfVanishFrom
#assert_no_axioms FX1Poly.ComputerAlgebra.rpdTrimNilOfAllCoeffsZero
#assert_no_axioms FX1Poly.ComputerAlgebra.rpdCoeffZeroOfTrimNil
#assert_no_axioms FX1Poly.ComputerAlgebra.rpdTrimLengthLe
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxMonomialMulCoeffVanishesFarAbove

-- T1: the step's leading-term cancellation and strict trimmed-length decrease
#assert_no_axioms FX1Poly.ComputerAlgebra.rpdStepTopCoeffCancels
#assert_no_axioms FX1Poly.ComputerAlgebra.rpdStepTrimLengthDecreases

-- T2: fuel adequacy
#assert_no_axioms FX1Poly.ComputerAlgebra.rpdStepPreservesTrimNil
#assert_no_axioms FX1Poly.ComputerAlgebra.rpdRemainderAdequate

-- T3: the spec completion
#assert_no_axioms FX1Poly.ComputerAlgebra.rpdDivModRemainderDegree

-- The exact (trim-level) single-step reconstruction (the T4 foundation)
#assert_no_axioms FX1Poly.ComputerAlgebra.rpdTrimEqOfCoeffEq
#assert_no_axioms FX1Poly.ComputerAlgebra.rpdQnfAddSubSelf
#assert_no_axioms FX1Poly.ComputerAlgebra.rpdStepReconstructsTrim

-- Fires
#assert_no_axioms FX1Poly.ComputerAlgebra.rpdFireLinearFactorNonzero
#assert_no_axioms FX1Poly.ComputerAlgebra.rpdFireDifferenceOfSquaresNonzero
#assert_no_axioms FX1Poly.ComputerAlgebra.rpdFireDifferenceOfSquaresRemainderDegree
#assert_no_axioms FX1Poly.ComputerAlgebra.rpdFireOnePlusSquareRemainderDegree
#assert_no_axioms FX1Poly.ComputerAlgebra.rpdFireStepTopCoeffCancels
#assert_no_axioms FX1Poly.ComputerAlgebra.rpdFireStepTrimLengthDecreases
#assert_no_axioms FX1Poly.ComputerAlgebra.rpdFireStepReconstructs

-- Content markers
#assert_no_axioms FX1Poly.ComputerAlgebra.rpdHasRemainderDegreeBound
#assert_no_axioms FX1Poly.ComputerAlgebra.rpdHasExactStepReconstruction
#assert_no_axioms FX1Poly.ComputerAlgebra.rpdHasGcdDividesBoth

end FX1PolyAudit
