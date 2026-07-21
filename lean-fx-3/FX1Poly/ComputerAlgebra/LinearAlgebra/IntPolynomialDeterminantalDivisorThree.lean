import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDeterminantalDivisor

/-! # IntPolynomialDeterminantalDivisorThree — the determinantal divisors separate three classes at dim 3

At dimension 3 there are three similarity classes sharing the characteristic polynomial `(x−2)³` — the
sharpest test that the invariant factors see what the characteristic polynomial cannot: the single Jordan
block `J₃(2)` (invariant factors `[(x−2)³]`, so `d₁ = 1`, `d₂ = 1`), `J₂(2) ⊕ J₁(2)` (`[(x−2), (x−2)²]`, so
`d₁ = 1`, `d₂ = x−2`), and the scalar `2·I₃` (`[(x−2), (x−2), (x−2)]`, so `d₁ = x−2`, `d₂ = (x−2)²`).

`d₁` is the ℤ[x] GCD of the nine `1×1` minors (the entries of `x·I − M`), `d₂` the GCD of the nine `2×2`
minors (rows/cols from the three `2`-subsets of `{0,1,2}`).  The pair `(deg d₁, deg d₂)` is `(0,0)` /
`(0,1)` / `(1,2)` for the three classes — a decidable similarity invariant separating all three where the
characteristic polynomial is completely blind.

Reuses `charMatrixMinor`, `polyGcdList`, and `polyDegree`; the `2`-subset selectors are function-valued
(propext-free); groundings are `decide`.  Free of `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## A `3 × 3` integer matrix from its nine entries -/

/-- The `3 × 3` integer matrix with the given row-major entries. -/
def threeByThreeMatrix (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Int) : SetoidMatrix Int :=
  { rowCount := 3, colCount := 3,
    entry := fun rowIndex colIndex =>
      if rowIndex = 0 then (if colIndex = 0 then a00 else if colIndex = 1 then a01 else a02)
      else if rowIndex = 1 then (if colIndex = 0 then a10 else if colIndex = 1 then a11 else a12)
      else (if colIndex = 0 then a20 else if colIndex = 1 then a21 else a22) }

/-! ## Index selections: the singletons `{2}` and the three `2`-subsets of `{0,1,2}` -/

/-- Select index `2` for every position (the singleton `{2}`). -/
def selectOnlyTwo : Nat → Nat := fun _ => 2

/-- Select the pair `{0, 1}` (the identity on `{0,1}`). -/
def selectRowsZeroOne : Nat → Nat := fun index => index

/-- Select the pair `{0, 2}` (skip the middle index). -/
def selectRowsZeroTwo : Nat → Nat
  | 0 => 0
  | _ => 2

/-- Select the pair `{1, 2}` (the trailing two indices). -/
def selectRowsOneTwo : Nat → Nat
  | 0 => 1
  | _ => 2

/-! ## The first two determinantal divisors at dimension 3 -/

/-- `d₁` of a `3×3` matrix: the ℤ[x] GCD of the nine `1×1` minors of `x·I − M` (its entries). -/
def charMatrixDivisorOneAtThree (matrix : SetoidMatrix Int) : List Int :=
  polyGcdList 24
    [ charMatrixMinor 1 matrix selectOnlyZero selectOnlyZero,
      charMatrixMinor 1 matrix selectOnlyZero selectOnlyOne,
      charMatrixMinor 1 matrix selectOnlyZero selectOnlyTwo,
      charMatrixMinor 1 matrix selectOnlyOne  selectOnlyZero,
      charMatrixMinor 1 matrix selectOnlyOne  selectOnlyOne,
      charMatrixMinor 1 matrix selectOnlyOne  selectOnlyTwo,
      charMatrixMinor 1 matrix selectOnlyTwo  selectOnlyZero,
      charMatrixMinor 1 matrix selectOnlyTwo  selectOnlyOne,
      charMatrixMinor 1 matrix selectOnlyTwo  selectOnlyTwo ]

/-- `d₂` of a `3×3` matrix: the ℤ[x] GCD of the nine `2×2` minors of `x·I − M` (rows and columns each
ranging over the three `2`-subsets `{0,1} {0,2} {1,2}`). -/
def charMatrixDivisorTwoAtThree (matrix : SetoidMatrix Int) : List Int :=
  polyGcdList 24
    [ charMatrixMinor 2 matrix selectRowsZeroOne selectRowsZeroOne,
      charMatrixMinor 2 matrix selectRowsZeroOne selectRowsZeroTwo,
      charMatrixMinor 2 matrix selectRowsZeroOne selectRowsOneTwo,
      charMatrixMinor 2 matrix selectRowsZeroTwo selectRowsZeroOne,
      charMatrixMinor 2 matrix selectRowsZeroTwo selectRowsZeroTwo,
      charMatrixMinor 2 matrix selectRowsZeroTwo selectRowsOneTwo,
      charMatrixMinor 2 matrix selectRowsOneTwo selectRowsZeroOne,
      charMatrixMinor 2 matrix selectRowsOneTwo selectRowsZeroTwo,
      charMatrixMinor 2 matrix selectRowsOneTwo selectRowsOneTwo ]

/-- The `(deg d₁, deg d₂)` determinantal-divisor degree signature of a `3×3` matrix — a decidable
similarity invariant. -/
def divisorDegreeSignatureThree (matrix : SetoidMatrix Int) : Nat × Nat :=
  (polyDegree (charMatrixDivisorOneAtThree matrix), polyDegree (charMatrixDivisorTwoAtThree matrix))

/-! ## The three archetypes of char poly `(x−2)³` -/

/-- The single Jordan block `J₃(2)`. -/
def jordanBlockThree : SetoidMatrix Int := threeByThreeMatrix 2 1 0  0 2 1  0 0 2

/-- `J₂(2) ⊕ J₁(2)` — a `2×2` Jordan block plus a `1×1` block. -/
def jordanTwoPlusOne : SetoidMatrix Int := threeByThreeMatrix 2 1 0  0 2 0  0 0 2

/-- The scalar `2·I₃`. -/
def scalarThree : SetoidMatrix Int := threeByThreeMatrix 2 0 0  0 2 0  0 0 2

/-! ## They share the characteristic polynomial `(x−2)³` -/

/-- All three archetypes have characteristic polynomial `(x−2)³ = x³ − 6x² + 12x − 8` (`[−8, 12, −6, 1]`)
— trace, determinant, and char poly are completely blind to their difference. -/
theorem allThreeShareCharPolyCubed :
    polyTrim (charPolyDeterminant 3 jordanBlockThree) = [-8, 12, -6, 1]
    ∧ polyTrim (charPolyDeterminant 3 jordanTwoPlusOne) = [-8, 12, -6, 1]
    ∧ polyTrim (charPolyDeterminant 3 scalarThree) = [-8, 12, -6, 1] := by decide

/-! ## The determinantal-divisor degree signatures separate all three -/

/-- `J₃(2)` (one block): `(deg d₁, deg d₂) = (0, 0)` — `d₁` and `d₂` are both units. -/
theorem divisorSignatureJordanBlockThree :
    divisorDegreeSignatureThree jordanBlockThree = (0, 0) := by decide

/-- `J₂(2) ⊕ J₁(2)` (two blocks): `(deg d₁, deg d₂) = (0, 1)` — `d₁` a unit, `d₂ = x−2`. -/
theorem divisorSignatureJordanTwoPlusOne :
    divisorDegreeSignatureThree jordanTwoPlusOne = (0, 1) := by decide

/-- `2·I₃` (three blocks): `(deg d₁, deg d₂) = (1, 2)` — `d₁ = x−2`, `d₂ = (x−2)²`. -/
theorem divisorSignatureScalarThree :
    divisorDegreeSignatureThree scalarThree = (1, 2) := by decide

/-! ## The three-way separator -/

/-- Two matrices are declared dissimilar when their determinantal-divisor degree signatures differ.
Reducible so a concrete separation closes by `decide`. -/
@[reducible] def DissimilarByDivisorSignatureThree (source target : SetoidMatrix Int) : Prop :=
  divisorDegreeSignatureThree source ≠ divisorDegreeSignatureThree target

/-- **The three classes of char poly `(x−2)³` are pairwise non-similar, decided by the determinantal
divisors.**  `J₃(2)`, `J₂⊕J₁`, and `2·I₃` all have characteristic polynomial `(x−2)³`, yet their
`(deg d₁, deg d₂)` signatures `(0,0)`, `(0,1)`, `(1,2)` are pairwise distinct — the number-of-Jordan-blocks
structure the characteristic polynomial cannot express, machine-checked at dimension 3. -/
theorem allThreeCubicClassesPairwiseDissimilar :
    DissimilarByDivisorSignatureThree jordanBlockThree jordanTwoPlusOne
    ∧ DissimilarByDivisorSignatureThree jordanBlockThree scalarThree
    ∧ DissimilarByDivisorSignatureThree jordanTwoPlusOne scalarThree := by decide

end FX1Poly.ComputerAlgebra
