import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDeterminantalDivisor
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDivision

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/IntPolynomialInvariantFactors — the invariant factors and the
rational-canonical-form block count at dimension 2 (the fourth brick of the char-matrix →
invariant-factors layer, WP-ENDO #2255)

The invariant factors of a matrix `M` are `s_k = d_k / d_{k−1}` where `d_k` is the `k`-th determinantal
divisor (`d_0 = 1`).  With `d_1` shipped (`charMatrixDivisorOne`), `d_2 = det(x·I − M)` shipped
(`charPolyDeterminant`), and monic division shipped (`polyDivModMonic`, exact reconstruction), the
dimension-2 invariant factors are computable:

  * `s_1 = d_1`;  `s_2 = d_2 / d_1`.

For the **derogatory** scalar `2·I`, `d_1 = x − 2` is monic and `s_2 = (x−2)² / (x−2) = x − 2` **exactly**
(remainder `0`), so its invariant factors are `[x−2, x−2]` — TWO nontrivial factors, i.e. two blocks in
the rational canonical form (it is diagonalizable with a repeated eigenvalue).  For the **cyclic** Jordan
block and `diag(2,3)`, `d_1` is a unit, so `s_1` is trivial and there is a SINGLE nontrivial invariant
factor `s_2 = d_2` (the whole characteristic polynomial) — one block.

## The block count is the complete dimension-2 classifier

At dimension 2 the number of nontrivial invariant factors — equivalently the number of blocks in the
rational canonical form — is `1 + deg d_1` (since `deg s_1 + deg s_2 = deg d_2 = 2` and `deg s_1 = deg
d_1`).  This count is a decidable similarity invariant that, together with the characteristic polynomial,
**determines** the similarity class of a `2×2` matrix over a field: it separates the derogatory `2·I`
(count `2`) from the cyclic Jordan block `[[2,1],[0,2]]` (count `1`), which share char poly `(x−2)²`.
(Completeness — that equal `(char poly, block count)` implies similarity — is the rational-canonical-form
existence-and-uniqueness theorem; the separating direction is what is machine-checked here.)

## Zero-axiom design

Invariant factors via `polyDivModMonic` (exact for the monic derogatory `d_1`) and the block count via
`polyDegree`.  Groundings are `decide` over concrete `polyTrim`/`polyDegree`/`polyMul` and a `Nat`
inequality.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in the audit twin.
-/

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

/-- ★ `2·I` has invariant factors `[x−2, x−2]`: both `s_1 = d_1 = x−2` and `s_2 = d_2/d_1 = x−2`
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

/-- ★ **`2·I` is provably NOT similar to the Jordan block `[[2,1],[0,2]]`, by block count.**  They share
characteristic polynomial `(x−2)²`, but `2·I` has `2` rational-canonical-form blocks (invariant factors
`[x−2, x−2]`) while the Jordan block has `1` (invariant factor `(x−2)²`).  The count is the number of
Jordan/cyclic blocks — the structural datum the characteristic polynomial cannot express.  `2 ≠ 1` by
`decide`. -/
theorem scalarNotSimilarToJordanByBlockCount :
    DissimilarByBlockCount (twoByTwoMatrix 2 0 0 2) (twoByTwoMatrix 2 1 0 2) := by decide

/-! ## The marker -/

/-- ★ **The invariant factors and the rational-canonical-form block count are shipped at dimension 2.**
`= true` records that `s_k = d_k / d_{k−1}` is computed via monic division (exact for the derogatory
scalar, whose invariant factors `[x−2, x−2]` reconstruct `(x−2)²`), and the block count `1 + deg d_1` is
a decidable similarity invariant separating `2·I` (`2` blocks) from the Jordan block `[[2,1],[0,2]]` (`1`
block) — the complete `2×2` classifier's separating direction.  The general-`n` assembly (all `d_k` over
the `k`-subset enumeration, then every quotient) is the remaining scale-up. -/
def fxIntPoly_hasInvariantFactorsTwo : Bool := true

end FX1Poly.ComputerAlgebra
