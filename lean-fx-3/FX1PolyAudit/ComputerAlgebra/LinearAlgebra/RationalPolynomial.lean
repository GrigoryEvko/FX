import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.RationalPolynomial

/-! # FX1PolyAudit/.../RationalPolynomial — zero-axiom gate

Per-declaration zero-axiom gate for the ℚ[x] substrate with EUCLIDEAN division (the field step the committed
ℤ[x] kit cannot take without pseudo-division): the derived `QnfRat` ring helpers, the trailing-zero normal
form / degree / leading coefficient / canonicality, structural Boolean equality, the ring operations with
evaluation proved a ring homomorphism, Euclidean division with its reconstruction invariant and exact
corollary, the Euclidean GCD with common-root capture and the shared-linear-factor bridge, the fires, and
the content markers.

All coefficient arithmetic routes through the shipped `qnf*` field laws; every definition is structural on
the list or on `fuel`; the only non-list case analysis is `qnfDecEq _ qnfZero` and `Nat.decLt` (full
`isTrue`/`isFalse` enumeration).  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`, `WellFounded.fix`. -/

namespace FX1PolyAudit

-- Derived QnfRat ring helpers
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfAddInterchange
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfMulZeroLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfMulZeroRight
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfNegZero
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfNegAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfMulNegRight
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfAddSubCancel
#assert_no_axioms FX1Poly.ComputerAlgebra.qnfBeqFalseOfNe

-- Normal form, degree, leading coefficient, canonicality (T1)
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxTrim
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxLastOrZero
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxDegree
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxLeadingCoeff
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxIsCanonical
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxTrimIsCanonical

-- Structural Boolean equality with beq-iff-eq (T1)
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxBeq
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxBeqSelfIsTrue
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxEqOfBeqTrue
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxBeqIffEq

-- Ring operations (T2)
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxScale
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxMul
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxSub
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxEval

-- Evaluation is a ring homomorphism (T2)
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxEvalAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxEvalScale
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxEvalMul
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxEvalNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxEvalSub
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxTrimPreservesEval

-- Monomial and quotient term
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxMonomial
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxQuotientTerm

-- Euclidean division (T3)
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxDivStepArith
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxDivMod
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxDivModReconstructs
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxDividesEvalMultiple

-- Euclidean GCD (T4)
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxRemainder
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxRemainderVanishesAtCommonRoot
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxGcd
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxGcdVanishesAtCommonRoot
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxGcdRightZero

-- Linear factor and shared-root bridge
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxEvalOne
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxLinearFactor
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxEvalLinearFactor
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxLinearFactorVanishesAtRoot
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxLinearFactorRootAnnihilatesMultiple
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxGcdSeesSharedLinearFactor

-- Fires (T5)
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxFireDifferenceOfSquaresRemainderZero
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxFireDifferenceOfSquaresQuotient
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxFireOnePlusSquareQuotient
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxFireOnePlusSquareRemainder
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxFireRationalQuotientTwoThirds
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxFireRationalRemainderZero
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxFireReconstructsAtFour
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxFireGcdSharesRootAtOne
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxFireGcdCommonFactorDegree
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxFireTrailingZeroNotCanonical
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxFireTrimmedIsCanonical

-- Content marker
#assert_no_axioms FX1Poly.ComputerAlgebra.rpxHasEuclideanDivision

end FX1PolyAudit
