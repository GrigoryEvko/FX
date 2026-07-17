import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDegree
import FX1Poly.ComputerAlgebra.LinearAlgebra.SetoidDeterminant

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/IntPolynomialRingWitness — ℤ[x] as a setoid commutative ring
(the first brick of the char-matrix → invariant-factors layer, WP-ENDO #2255)

The `EndomorphismCharPolyThree` r2 docstring named "a POLYNOMIAL-valued matrix `x·I − M` and a determinant
over `ℤ[x]` — a fresh polynomial-ring build" as the route it *avoided* (it computed the char poly via
principal minors instead).  With the full ℤ[x] ring now shipped (`polyAdd`/`polyMul`/`polyNeg` + the
evaluation homomorphisms), that build is now cheap: ℤ[x] is a `CommutativeRingWitness (List Int)`, which
instantiates the ENTIRE generic `SetoidMatrix` / `cofactorDet` tower at polynomials for free.

## The eval-based setoid

Two coefficient lists denote the same polynomial when they agree at **every point** (`polyDenotesSame p q :=
∀ point, polyEval point p = polyEval point q`).  This makes every ring law a one-liner: the evaluation
homomorphisms (`polyEvalAdd`/`polyEvalMul`/`polyEvalNeg`) collapse each polynomial law to the corresponding
ℤ law under `polyEval point`.  No coefficient-list congruence bookkeeping is needed.

## What is PROVEN

  * `intPolynomialRingWitness : CommutativeRingWitness (List Int)` — ℤ[x] is a setoid commutative ring
    (`zero = []`, `one = [1]`, `add = polyAdd`, `mul = polyMul`, `neg = polyNeg`; nontrivial since they
    disagree at a point).
  * `charMatrix` / `charPolyDeterminant` — the characteristic matrix `x·I − M` (entries are the polynomials
    `x − Mᵢᵢ` on the diagonal, `−Mᵢⱼ` off it) and its determinant `det(x·I − M)` over ℤ[x] via the generic
    `cofactorDet` at the polynomial witness — the characteristic polynomial as an honest ℤ[x] determinant,
    the k×k minors of which are the determinantal divisors whose successive GCDs (the shipped ℤ[x] GCD)
    give the invariant factors.

## Zero-axiom design

Each ring law is `polyEval`-homomorphism `rw` + a ℤ law; the setoid is an equivalence by `Eq` transport at
each point.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/ComputerAlgebra/LinearAlgebra/IntPolynomialRingWitness.lean`.
-/

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

/-- Marker: ℤ[x] is a setoid commutative ring (`intPolynomialRingWitness`), instantiating the generic
`SetoidMatrix`/`cofactorDet` tower at polynomials, so the characteristic matrix `x·I − M` and its
determinant `det(x·I − M)` (`charPolyDeterminant`) are honest ℤ[x] objects — the substrate for the
determinantal-divisor / invariant-factor computation over the shipped ℤ[x] GCD. -/
def fxIntPoly_hasPolynomialRingWitness : Bool := true

end FX1Poly.ComputerAlgebra
