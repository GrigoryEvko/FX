import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDegree
import FX1Poly.ComputerAlgebra.LinearAlgebra.SetoidDeterminant

/-! # IntPolynomialRingWitness — ℤ[x] as a setoid commutative ring

ℤ[x] is a `CommutativeRingWitness (List Int)`, which instantiates the entire generic `SetoidMatrix` /
`cofactorDet` tower at polynomials.  This is the parent of the ℤ[x] ring/coefficient sub-arc, whose markers
are consolidated here (see `fxIntPoly_hasPolynomialRingWitness`).

Two coefficient lists denote the same polynomial when they agree at every point (`polyDenotesSame p q :=
∀ point, polyEval point p = polyEval point q`), so every ring law reduces to the corresponding ℤ law under
`polyEval point` via the evaluation homomorphisms — no coefficient-list congruence bookkeeping.

  * `intPolynomialRingWitness : CommutativeRingWitness (List Int)` — ℤ[x] as a setoid commutative ring
    (`zero = []`, `one = [1]`, `add = polyAdd`, `mul = polyMul`, `neg = polyNeg`; nontrivial since they
    disagree at a point).
  * `charMatrix` / `charPolyDeterminant` — the characteristic matrix `x·I − M` and its determinant
    `det(x·I − M)` over ℤ[x] via the generic `cofactorDet` at the polynomial witness, the k×k minors of
    which are the determinantal divisors whose successive GCDs give the invariant factors.

Each ring law is a `polyEval`-homomorphism `rw` + a ℤ law.  Free of `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The evaluation setoid on ℤ[x] -/

/-- Two coefficient lists denote the same polynomial: they evaluate equally at every point. -/
def polyDenotesSame (leftPoly rightPoly : List Int) : Prop :=
  ∀ point : Int, polyEval point leftPoly = polyEval point rightPoly

/-! ## The ℤ[x] commutative-ring witness -/

/-- **ℤ[x] is a setoid commutative ring.**  Coefficient lists under `polyAdd`/`polyMul`/`polyNeg` with the
evaluation setoid; every law is discharged by an evaluation homomorphism plus a ℤ law. -/
def intPolynomialRingWitness : CommutativeRingWitness (List Int) where
  denotesSame := polyDenotesSame
  zero := []
  one := [1]
  add := polyAdd
  mul := polyMul
  neg := polyNeg
  denotesSameIsReflexive := fun _ _ => rfl
  denotesSameIsSymmetric := fun _ _ sameLeftRight point => (sameLeftRight point).symm
  denotesSameIsTransitive := fun _ _ _ sameFirstMiddle sameMiddleLast point =>
    (sameFirstMiddle point).trans (sameMiddleLast point)
  addRespectsDenotesSame := fun _ _ _ _ sameLeft sameRight point => by
    rw [polyEvalAdd, polyEvalAdd, sameLeft point, sameRight point]
  mulRespectsDenotesSame := fun _ _ _ _ sameLeft sameRight point => by
    rw [polyEvalMul, polyEvalMul, sameLeft point, sameRight point]
  negRespectsDenotesSame := fun _ _ sameLeftRight point => by
    rw [polyEvalNeg, polyEvalNeg, sameLeftRight point]
  addIsCommutative := fun _ _ point => by
    rw [polyEvalAdd, polyEvalAdd]; exact intAddComm _ _
  addIsAssociative := fun _ _ _ point => by
    rw [polyEvalAdd, polyEvalAdd, polyEvalAdd, polyEvalAdd]; exact intAddAssoc _ _ _
  zeroIsRightAdditiveIdentity := fun _ point => by
    rw [polyEvalAdd]; exact intAddZero _
  negIsRightAdditiveInverse := fun _ point => by
    rw [polyEvalAdd, polyEvalNeg]; exact intAddRightNeg _
  mulIsCommutative := fun leftFactor rightFactor point =>
    polyEvalMulComm point leftFactor rightFactor
  mulIsAssociative := fun leftFactor middleFactor rightFactor point =>
    polyEvalMulAssoc point leftFactor middleFactor rightFactor
  oneIsRightMultiplicativeIdentity := fun _ point => by
    rw [polyEvalMul, polyEvalOne]; exact intMulOne _
  mulDistributesOverAdd := fun _ _ _ point => by
    rw [polyEvalMul, polyEvalAdd, polyEvalAdd, polyEvalMul, polyEvalMul]
    exact intLeftDistrib _ _ _
  zeroIsApartFromOne := fun sameZeroOne => absurd (sameZeroOne 0) (by decide)

/-! ## The characteristic matrix and its determinant over ℤ[x] -/

/-- The characteristic matrix `x·I − M` of an integer matrix, entries valued in ℤ[x]: the diagonal carries
`x − Mᵢᵢ` (`[−Mᵢᵢ, 1]`), the off-diagonal carries the constant `−Mᵢⱼ` (`[−Mᵢⱼ]`). -/
def charMatrix (matrix : SetoidMatrix Int) : SetoidMatrix (List Int) :=
  { rowCount := matrix.rowCount
    colCount := matrix.colCount
    entry := fun rowIndex colIndex =>
      if rowIndex = colIndex then [- matrix.entry rowIndex colIndex, 1]
      else [- matrix.entry rowIndex colIndex] }

/-- The characteristic polynomial `det(x·I − M)` of a `size × size` integer matrix, as an honest ℤ[x]
determinant via the generic `cofactorDet` at the polynomial ring witness. -/
def charPolyDeterminant (size : Nat) (matrix : SetoidMatrix Int) : List Int :=
  SetoidMatrix.cofactorDet intPolynomialRingWitness size (charMatrix matrix)

/-! ## Groundings -/

/-- The witness's product IS `polyMul`: `(x+1)² = x² + 2x + 1` — `polyTrim (intPolynomialRingWitness.mul
[1,1] [1,1]) = [1,2,1]`. -/
theorem intPolynomialRingWitnessMulGrounding :
    polyTrim (intPolynomialRingWitness.mul [1, 1] [1, 1]) = [1, 2, 1] := by decide

/-- The char poly of `diag(2, 3)` is `(x−2)(x−3) = x² − 5x + 6` — the ℤ[x] determinant of `x·I − diag(2,3)`
trims to `[6, −5, 1]`. -/
theorem charPolyDeterminantDiagGrounding :
    polyTrim (charPolyDeterminant 2
        { rowCount := 2, colCount := 2,
          entry := fun rowIndex colIndex =>
            if rowIndex = 0 ∧ colIndex = 0 then 2
            else if rowIndex = 1 ∧ colIndex = 1 then 3 else 0 })
      = [6, -5, 1] := by decide

/-- Consolidated marker for the ℤ[x] ring and coefficient sub-arc.  Covers: ℤ[x] as a setoid commutative
ring (`intPolynomialRingWitness`) and the characteristic matrix `x·I − M` with its determinant
`det(x·I − M)` (`charPolyDeterminant`) as honest ℤ[x] objects (this file); the evaluation ring homomorphism,
linear factor, composition, powers, and monomials (`IntUnivariatePolynomial`); each positional coefficient
as a ring homomorphism plus the monomial coefficient shift (`IntPolynomialCoeff`); and the coefficient
vanishing bounds past the degree (`IntPolynomialCoeffBounds`). -/
def fxIntPoly_hasPolynomialRingWitness : Bool := true

end FX1Poly.ComputerAlgebra
