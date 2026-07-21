import FX1Poly.ComputerAlgebra.LinearAlgebra.EndomorphismSimilarity

/-! # EndomorphismMinimalPolynomialTwoByTwo — the min-poly degree separator

The shipped separators — the char poly (`EndomorphismCharPolyThree`), the rank sequence `rank(Mᵏ)`
(`EndomorphismPowerZeroSeparator`), and the general minor rank (`EndomorphismMinorSelector`) — leave one
small equal-char-poly gap at dimension `2`: a scalar matrix versus a Jordan block with the same
eigenvalue.  `diag(2, 2)` and `[[2,1],[0,2]]` share the characteristic polynomial `(x−2)²` and are both
invertible (rank `2` at every power), so char poly, rank sequence, and minor rank are all blind.  They
are dissimilar: the scalar matrix is annihilated by the linear polynomial `x − 2`, the Jordan block is
not (its minimal polynomial is `(x−2)²`).  The minimal-polynomial degree is a similarity invariant
(`Q⁻¹(c·I)Q = c·I`), so it separates them.

At dimension `2` the minimal polynomial has degree `1` exactly when the matrix is scalar, else degree
`2`, so the separator is the "is this matrix scalar" invariant.  The complete invariant-factor
separator over ℚ[x] remains the open wall.

Raw Lean 4 + Init; every declaration axiom-free (the `if (Prop)` idiom, no `List`/`decide` in defs). -/

namespace FX1Poly.ComputerAlgebra

/-! ## Scalarness and the minimal-polynomial degree at dimension 2 -/

/-- A `2×2` matrix is scalar (`c·I`) when its off-diagonal entries vanish and its diagonal entries
agree.  A conjugation-stable (similarity-invariant) property.  Reducible so the decidable `And` of
`Int` equalities is visible to the `if` in the degree function (and to `decide`). -/
@[reducible] def endomorphismIsScalarTwoByTwo (matrix : SetoidMatrix Int) : Prop :=
  matrix.entry 0 1 = 0 ∧ matrix.entry 1 0 = 0 ∧ matrix.entry 0 0 = matrix.entry 1 1

/-- The degree of the minimal polynomial of a `2×2` integer matrix: `1` when the matrix is scalar
(annihilated by a linear `x − c`), else `2` (its minimal polynomial equals the characteristic
polynomial).  A similarity invariant, computed by the decidable scalarness test. -/
def endomorphismMinimalPolynomialDegreeTwoByTwo (matrix : SetoidMatrix Int) : Nat :=
  if endomorphismIsScalarTwoByTwo matrix then 1 else 2

/-- `source` and `target` are dissimilar because their minimal polynomials have different degrees.
Reducible so a concrete separation unfolds to a `Nat` inequality. -/
@[reducible] def EndomorphismDissimilarByMinimalPolynomialDegree (source target : SetoidMatrix Int) : Prop :=
  endomorphismMinimalPolynomialDegreeTwoByTwo source ≠ endomorphismMinimalPolynomialDegreeTwoByTwo target

/-! ## Groundings — the min-poly degree on scalar and non-scalar `2×2` matrices -/

/-- The scalar matrix `diag(2, 2) = 2·I` has minimal polynomial `x − 2` (degree `1`). -/
theorem endomorphismMinimalPolynomialDegreeScalarExample :
    endomorphismMinimalPolynomialDegreeTwoByTwo (setoidMatrixOfRows [[2, 0], [0, 2]]) = 1 := rfl

/-- The Jordan block `[[2,1],[0,2]]` has minimal polynomial `(x − 2)²` (degree `2`) — it is not scalar. -/
theorem endomorphismMinimalPolynomialDegreeJordanExample :
    endomorphismMinimalPolynomialDegreeTwoByTwo (setoidMatrixOfRows [[2, 1], [0, 2]]) = 2 := rfl

/-- The scalar matrix and the Jordan block share the characteristic polynomial `(x − 2)² = x² − 4x + 4`:
the char-poly separator cannot tell them apart. -/
theorem endomorphismJordanVersusScalarShareCharPoly :
    endomorphismCharPolyCoefficients 2 (setoidMatrixOfRows [[2, 0], [0, 2]])
      = endomorphismCharPolyCoefficients 2 (setoidMatrixOfRows [[2, 1], [0, 2]]) := by decide

/-- Both matrices are rank `2` (invertible): the rank separator (and the power-based rank sequence, which
shifts only by `0`) cannot tell them apart either. -/
theorem endomorphismJordanVersusScalarShareRank :
    endomorphismRank2 (setoidMatrixOfRows [[2, 0], [0, 2]])
      = endomorphismRank2 (setoidMatrixOfRows [[2, 1], [0, 2]]) := by decide

/-- The min-poly-degree separator sees what no other shipped separator can: `diag(2,2)` and
`[[2,1],[0,2]]` share the characteristic polynomial `(x−2)²` and the rank `2` (both invertible), yet
the scalar matrix has minimal polynomial `x−2` (degree `1`) and the Jordan block `(x−2)²` (degree `2`),
so they are dissimilar. -/
theorem endomorphismSeparatesScalarFromJordanSameCharPolySameRank :
    EndomorphismDissimilarByMinimalPolynomialDegree
      (setoidMatrixOfRows [[2, 0], [0, 2]])
      (setoidMatrixOfRows [[2, 1], [0, 2]]) := by decide

end FX1Poly.ComputerAlgebra
