import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialCharMinors
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialGcd

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/IntPolynomialDeterminantalDivisor — the first determinantal
divisor `d₁` and a machine-checked similarity separator (the third brick of the char-matrix →
invariant-factors layer, WP-ENDO #2255)

The determinantal divisor `d_k` of a matrix `M` is the ℤ[x] GCD of ALL `k×k` minors of the
characteristic matrix `x·I − M`.  With the ℤ[x] GCD (`polyGcd`) and its fuel adequacy shipped, and the
polynomial minors shipped (`charMatrixMinor`), the first determinantal divisor is a GCD fold over the
`1×1` minors — the entries of `x·I − M`.

At dimension 2 this already **separates similarity where the characteristic polynomial cannot**.  The
scalar `2·I` and the Jordan block `[[2,1],[0,2]]` share the characteristic polynomial `(x−2)² = x² − 4x
+ 4`, so trace, determinant, and char poly are all blind to their difference.  But:

  * `d₁(2·I)` = `gcd(x−2, 0, 0, x−2)` = `x−2` — **degree 1**;
  * `d₁(Jordan)` = `gcd(x−2, −1, 0, x−2)` = a **unit** (the `(0,1)` minor `−1` is invertible) — **degree
    0**.

The degree of `d₁` is invariant under the unit-ambiguity of the GCD (units have degree 0), so
`polyDegree d₁` is a well-defined, decidable similarity invariant.  It differs (`1 ≠ 0`), so `2·I` and
the Jordan block are **provably not similar** — a separation the char poly, trace, and determinant miss.
(`deg d₁` counts the geometric multiplicity's contribution: `d₁` is nontrivial exactly when the minimal
polynomial is a proper divisor of the characteristic polynomial, i.e. the operator is derogatory.)

## Zero-axiom design

`polyGcdList` folds `polyGcd` (structural on fuel) over the minor list; `charMatrixDivisorOne` selects
the four `1×1` minors.  Groundings are `decide` over concrete `polyDegree`/`polyTrim`med `List Int`; the
separator is `decide` on a `Nat` inequality.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in the audit twin.
-/

namespace FX1Poly.ComputerAlgebra

/-! ## The GCD fold -/

/-- The ℤ[x] GCD of a nonempty list of polynomials, folding `polyGcd` from the head.  The empty list
denotes the zero polynomial.  `fuel` bounds each pairwise Euclidean recursion. -/
def polyGcdList (fuel : Nat) : List (List Int) → List Int
  | [] => []
  | first :: rest =>
      rest.foldl (fun accumulator nextPoly => polyGcd fuel accumulator nextPoly) first

/-! ## The first determinantal divisor at dimension 2 -/

/-- The first determinantal divisor `d₁` of a `2×2` matrix: the ℤ[x] GCD of the four `1×1` minors of
`x·I − M` (its diagonal `x − Mᵢᵢ` and off-diagonal `−Mᵢⱼ` entries).  Fuel `16` is more than adequate for
the degree-`≤ 1` entries. -/
def charMatrixDivisorOne (matrix : SetoidMatrix Int) : List Int :=
  polyGcdList 16
    [ charMatrixMinor 1 matrix selectOnlyZero selectOnlyZero,
      charMatrixMinor 1 matrix selectOnlyZero selectOnlyOne,
      charMatrixMinor 1 matrix selectOnlyOne  selectOnlyZero,
      charMatrixMinor 1 matrix selectOnlyOne  selectOnlyOne ]

/-! ## Groundings — `deg d₁` classifies derogatory vs cyclic at dimension 2 -/

/-- `2·I` is derogatory: `d₁ = x − 2`, degree `1` (the off-diagonal minors vanish, the diagonal minors
are both `x − 2`). -/
theorem charMatrixDivisorOneScalarDegreeOne :
    polyDegree (charMatrixDivisorOne (twoByTwoMatrix 2 0 0 2)) = 1 := by decide

/-- The Jordan block `[[2,1],[0,2]]` is cyclic: `d₁` is a unit, degree `0` (the `(0,1)` minor `−1` is
invertible, so the GCD collapses to a unit). -/
theorem charMatrixDivisorOneJordanDegreeZero :
    polyDegree (charMatrixDivisorOne (twoByTwoMatrix 2 1 0 2)) = 0 := by decide

/-- `diag(2,3)` is cyclic: `d₁` is a unit, degree `0` (the two diagonal minors `x−2`, `x−3` are coprime).
-/
theorem charMatrixDivisorOneDiagDistinctDegreeZero :
    polyDegree (charMatrixDivisorOne (twoByTwoMatrix 2 0 0 3)) = 0 := by decide

/-! ## The characteristic polynomial is blind -/

/-- `2·I` and the Jordan block `[[2,1],[0,2]]` share the characteristic polynomial `(x−2)² = x² − 4x + 4`
(`[4, −4, 1]`) — trace, determinant, and char poly cannot tell them apart. -/
theorem scalarAndJordanShareCharPoly :
    polyTrim (charPolyDeterminant 2 (twoByTwoMatrix 2 0 0 2))
      = polyTrim (charPolyDeterminant 2 (twoByTwoMatrix 2 1 0 2))
    ∧ polyTrim (charPolyDeterminant 2 (twoByTwoMatrix 2 0 0 2)) = [4, -4, 1] := by decide

/-! ## The similarity separator -/

/-- Two matrices are declared dissimilar by the first determinantal divisor when the degrees of their
`d₁` differ (an associate-invariant, hence well-defined, decidable comparison).  Reducible so a concrete
separation closes by `decide`. -/
@[reducible] def DissimilarByDivisorOneDegree (source target : SetoidMatrix Int) : Prop :=
  polyDegree (charMatrixDivisorOne source) ≠ polyDegree (charMatrixDivisorOne target)

/-- ★ **`2·I` is provably NOT similar to the Jordan block `[[2,1],[0,2]]`.**  They share the
characteristic polynomial `(x−2)²`, yet `deg d₁` differs (`1` vs `0`): the first determinantal divisor
of `x·I − M` separates them where the char poly, trace, and determinant are blind.  The degree
inequality `1 ≠ 0` closes by `decide` (Nat, propext-free). -/
theorem scalarNotSimilarToJordanByDivisorOne :
    DissimilarByDivisorOneDegree (twoByTwoMatrix 2 0 0 2) (twoByTwoMatrix 2 1 0 2) := by decide

/-! ## The marker -/

/-- ★ **The first determinantal divisor `d₁` and its similarity separation are shipped.**  `= true`
records that the ℤ[x] GCD fold over the `1×1` minors of `x·I − M` computes `d₁`, whose degree is a
decidable similarity invariant separating the derogatory `2·I` (`deg d₁ = 1`) from the cyclic Jordan
block `[[2,1],[0,2]]` (`deg d₁ = 0`) — matrices with equal characteristic polynomial `(x−2)²`.  The full
invariant-factor list (all `d_k` over the `k`-subset enumeration, then the quotients `s_k = d_k/d_{k−1}`)
is the remaining assembly. -/
def fxIntPoly_hasFirstDeterminantalDivisor : Bool := true

end FX1Poly.ComputerAlgebra
