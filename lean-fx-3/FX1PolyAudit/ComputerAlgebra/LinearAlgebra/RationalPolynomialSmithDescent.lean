import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.RationalPolynomialSmithDescent

/-! # FX1PolyAudit/.../RationalPolynomialSmithDescent — zero-axiom gate

Per-declaration zero-axiom gate for the ℚ[x] degree-multiplicativity lever (T1 — `rsdDegreeMul`, the
leading-coefficient product law over the field ℚ) and the Smith re-pivot descent core (T2), plus the fires
and content markers.

Every coefficient lemma is structural on the coefficient list with full `Nat.succ`/`zero` casing; arithmetic
routes through the shipped `qnf*` field laws and calibrated-clean core `Nat` lemmas.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `funext`, `WellFounded.fix`. -/

namespace FX1PolyAudit

-- The integral-domain law over ℚ
#assert_no_axioms FX1Poly.ComputerAlgebra.rsdQnfMulNeZero

-- T1 the coefficient calculus for the degree lever
#assert_no_axioms FX1Poly.ComputerAlgebra.rsdConsZeroVanish
#assert_no_axioms FX1Poly.ComputerAlgebra.rsdMulCoeffZeroOfLeftZero
#assert_no_axioms FX1Poly.ComputerAlgebra.rsdMulCoeffTop
#assert_no_axioms FX1Poly.ComputerAlgebra.rsdMulCoeffVanishAbove

-- T1 THE LEVER
#assert_no_axioms FX1Poly.ComputerAlgebra.rsdDegreeMul

-- T2 the re-pivot descent core
#assert_no_axioms FX1Poly.ComputerAlgebra.rsdCofactorNonzeroOfProductNonzero
#assert_no_axioms FX1Poly.ComputerAlgebra.rsdMultipleDegreeGePivot
#assert_no_axioms FX1Poly.ComputerAlgebra.rsdResidueBelowPivotWhenNonzero
#assert_no_axioms FX1Poly.ComputerAlgebra.rsdEntryDegreeOr
#assert_no_axioms FX1Poly.ComputerAlgebra.rsdMinDegreeOver

-- Fires
#assert_no_axioms FX1Poly.ComputerAlgebra.rsdFireLinearPlusTwoNonzero
#assert_no_axioms FX1Poly.ComputerAlgebra.rsdFireLinearMinusOneNonzero
#assert_no_axioms FX1Poly.ComputerAlgebra.rsdFireSquarePlusOneNonzero
#assert_no_axioms FX1Poly.ComputerAlgebra.rsdFireMonomialXNonzero
#assert_no_axioms FX1Poly.ComputerAlgebra.rsdFireDegreeMulLinearTimesLinearTheorem
#assert_no_axioms FX1Poly.ComputerAlgebra.rsdFireDegreeMulLinearTimesLinearValue
#assert_no_axioms FX1Poly.ComputerAlgebra.rsdFireDegreeMulSquareTimesMonomialTheorem
#assert_no_axioms FX1Poly.ComputerAlgebra.rsdFireDegreeMulSquareTimesMonomialValue
#assert_no_axioms FX1Poly.ComputerAlgebra.rsdFireMultipleDegreeGe
#assert_no_axioms FX1Poly.ComputerAlgebra.rsdFireResidueBelowPivotValue
#assert_no_axioms FX1Poly.ComputerAlgebra.rsdFireResidueBelowPivotTheorem
#assert_no_axioms FX1Poly.ComputerAlgebra.rsdFireMinDegreeOverCross

-- Content marker
#assert_no_axioms FX1Poly.ComputerAlgebra.rsdHasDegreeMultiplicativity

end FX1PolyAudit
