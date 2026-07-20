import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.RationalPolynomialRing

/-! # FX1PolyAudit/.../RationalPolynomialRing — zero-axiom gate

Per-declaration zero-axiom gate for the ℚ[x] list-level ring layer, aggregate division reconstruction, and
"gcd divides both": the coefficient bridge, the `rpxAdd` commutative-monoid layer (comm/assoc/interchange,
plain `Eq`), the `rpxScale` layer (distributivity, composition, scale/mul commutation, plain `Eq`), `rpxMul`
two-sided distributivity (plain `Eq`) and associativity (trim level), the trim congruences, the aggregate
reconstruction (`rpeDivModReconstructsTrim`, T2), the divisibility relation with reflexivity / zero-remainder
divisibility / the linear-combination lemma, the fuel-adequate Euclidean invariant, `rpeGcdDividesBoth`
(supersedes the committed owner-false), the fires, and the content markers.

Every list/scale/mul law is structural on the coefficient list; every trim-level law routes through the
coefficient bridge and the shipped `qnf*` field laws; the gcd fuel bookkeeping uses only calibrated-clean
Nat order lemmas.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`,
`funext`, `WellFounded.fix`. -/

namespace FX1PolyAudit

-- The coefficient bridge
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeCoeffEqOfTrimEq

-- T1a: the rpxAdd commutative-monoid layer (plain Eq)
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeAddNilRight
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeAddComm
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeAddAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeAddInterchange
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeConsZeroAdd

-- T1b: the rpxScale layer (plain Eq)
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeScaleDistributesOverAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeScaleScaleAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeScaleAddScalar
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeScaleMulCommLeft

-- T1c: rpxMul distributivity (plain Eq)
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeMulRightDistrib
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeMulLeftDistrib

-- T1d: trim congruences (via the coefficient bridge)
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeAddRespectsTrim
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeConsZeroRespectsTrim
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeMulConsZeroLeftCoeff
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeMulConsZeroLeftTrim
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeMulCoeffCongrRight
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeMulRespectsTrimRight
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeSingletonMulCoeff
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeMulOneLeftTrim

-- T1e: rpxMul associativity (trim level)
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeMulAssocTrim

-- T2: the aggregate division reconstruction
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeDivModReconstructsTrim

-- T3: divisibility and "gcd divides both"
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeDivides
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeDividesOfDividendTrimNil
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeDividesRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeDividesRespectsTrim
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeTrimAddRightTrimNil
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeExactDivisionGivesDivides
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeLinearCombinationDivides
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeGcdDividesBothInvariant
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeGcdDividesBoth
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeGcdDividesLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeGcdDividesRight

-- Fires
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeFireAddCommClosed
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeFireAddAssocClosed
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeFireRightDistribClosed
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeFireLeftDistribClosed
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeFireScaleDistribClosed
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeFireMulAssocTrimClosed
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeFireReconstructsTrimClosed
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeFireExactDividesDifferenceOfSquares
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeFireGcdDividesDifferenceOfSquaresComputed
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeFireGcdDividesLinearComputed
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeFireGcdDividesLeftDifferenceOfSquares
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeFireGcdDividesRightDifferenceOfSquares

-- Content markers
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeHasListRingLayer
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeHasAggregateReconstruction
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeHasGcdDividesBoth
#assert_no_axioms FX1Poly.ComputerAlgebra.rpeHasBezoutIdentity

end FX1PolyAudit
