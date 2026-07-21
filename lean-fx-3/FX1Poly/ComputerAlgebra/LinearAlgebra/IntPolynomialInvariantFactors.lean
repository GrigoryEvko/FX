import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDeterminantalDivisor
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDivision

/-! # IntPolynomialInvariantFactors — invariant factors and the block count at dimension 2

The invariant factors are `s_k = d_k / d_{k−1}` (`d_0 = 1`).  At dimension 2, `s_1 = d_1`, `s_2 = d_2 / d_1`
computed by monic division: the derogatory `2·I` has `[x−2, x−2]` (two rational-canonical-form blocks), the
cyclic Jordan block and `diag(2,3)` have a single nontrivial factor `s_2 = d_2` (one block).  The block
count `1 + deg d_1` is a decidable similarity invariant separating `2·I` (count `2`) from the Jordan block
`[[2,1],[0,2]]` (count `1`), which share char poly `(x−2)²`.

Invariant factors via `polyDivModMonic` (exact for a monic `d_1`) and the block count via `polyDegree`;
groundings are `decide`.  Free of `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The second invariant factor at dimension 2 -/

/-- The second invariant factor `s_2 = d_2 / d_1` of a `2×2` matrix, computed by monic division of the
characteristic polynomial `d_2` by the first determinantal divisor `d_1`.  Exact (remainder `0`) when
`d_1` is monic — the derogatory case; `fuel 8` is ample for degree `≤ 2`. -/
def invariantFactorSecond (matrix : SetoidMatrix Int) : List Int :=
  (polyDivModMonic 8 (charMatrixDivisorOne matrix) (charPolyDeterminant 2 matrix)).1

/-- The invariant-factor list `[s_1, s_2] = [d_1, d_2/d_1]` of a `2×2` matrix (honest for a monic `d_1`,
i.e. the derogatory case). -/
def invariantFactorsTwo (matrix : SetoidMatrix Int) : List (List Int) :=
  [ charMatrixDivisorOne matrix, invariantFactorSecond matrix ]

/-! ## The rational-canonical-form block count -/

/-- The number of nontrivial invariant factors of a `2×2` matrix — equivalently the number of blocks in
its rational canonical form — is `1 + deg d_1`.  A decidable similarity invariant: `2` for the
derogatory scalar, `1` for a cyclic matrix. -/
def rationalFormBlockCountTwo (matrix : SetoidMatrix Int) : Nat :=
  1 + polyDegree (charMatrixDivisorOne matrix)

/-! ## Groundings — the invariant factors of the derogatory scalar, computed exactly -/

/-- `2·I` has invariant factors `[x−2, x−2]`: both `s_1 = d_1 = x−2` and `s_2 = d_2/d_1 = x−2`
(`[[-2,1], [-2,1]]`).  The division `(x−2)²/(x−2) = x−2` is exact. -/
theorem invariantFactorsScalarAreRepeatedLinear :
    invariantFactorsTwo (twoByTwoMatrix 2 0 0 2) = [[-2, 1], [-2, 1]] := by decide

/-- The invariant factors of `2·I` reconstruct its characteristic polynomial: `s_1 · s_2 = (x−2)(x−2) =
(x−2)² = d_2` (`[4, −4, 1]`) — the exact-division cross-check. -/
theorem invariantFactorsScalarReconstructCharPoly :
    polyTrim (polyMul (charMatrixDivisorOne (twoByTwoMatrix 2 0 0 2))
        (invariantFactorSecond (twoByTwoMatrix 2 0 0 2)))
      = polyTrim (charPolyDeterminant 2 (twoByTwoMatrix 2 0 0 2)) := by decide

/-! ## Groundings — the block count classifies -/

/-- `2·I` is diagonalizable with a repeated eigenvalue: `2` rational-canonical-form blocks. -/
theorem rationalFormBlockCountScalarIsTwo :
    rationalFormBlockCountTwo (twoByTwoMatrix 2 0 0 2) = 2 := by decide

/-- The Jordan block `[[2,1],[0,2]]` is cyclic: a single rational-canonical-form block. -/
theorem rationalFormBlockCountJordanIsOne :
    rationalFormBlockCountTwo (twoByTwoMatrix 2 1 0 2) = 1 := by decide

/-- `diag(2,3)` is cyclic (distinct eigenvalues): a single rational-canonical-form block. -/
theorem rationalFormBlockCountDiagDistinctIsOne :
    rationalFormBlockCountTwo (twoByTwoMatrix 2 0 0 3) = 1 := by decide

/-! ## The classifier separator -/

/-- Two matrices are declared dissimilar when their rational-canonical-form block counts differ (a
decidable similarity invariant).  Reducible so a concrete separation closes by `decide`. -/
@[reducible] def DissimilarByBlockCount (source target : SetoidMatrix Int) : Prop :=
  rationalFormBlockCountTwo source ≠ rationalFormBlockCountTwo target

/-- **`2·I` is provably not similar to the Jordan block `[[2,1],[0,2]]`, by block count.**  They share char
poly `(x−2)²`, but `2·I` has `2` rational-canonical-form blocks while the Jordan block has `1`. -/
theorem scalarNotSimilarToJordanByBlockCount :
    DissimilarByBlockCount (twoByTwoMatrix 2 0 0 2) (twoByTwoMatrix 2 1 0 2) := by decide

end FX1Poly.ComputerAlgebra
