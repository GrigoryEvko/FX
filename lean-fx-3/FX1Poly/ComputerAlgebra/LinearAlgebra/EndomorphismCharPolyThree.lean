import FX1Poly.ComputerAlgebra.LinearAlgebra.EndomorphismMinorSelector

/-! # EndomorphismCharPolyThree — the characteristic polynomial via principal minors

The characteristic polynomial `det(x·I − M)` needs no polynomial ring: its coefficients are sums of
principal minors, `e_k = Σ (k×k principal minors)`, computed directly by the general minor selector
(`intMinorDet`, `EndomorphismMinorSelector`).  At dimension `3` the middle coefficient `e₂` is content
the trace/determinant/rank separators cannot see.  The char poly is a partial invariant (equal char
poly does not imply similar); the complete separator, the invariant-factor Smith over ℚ[x], is open.

Raw Lean 4 + Init; every declaration axiom-free (function-valued minor selection keeps `propext` out). -/

namespace FX1Poly.ComputerAlgebra

/-! ## The elementary-symmetric coefficients -/

/-- `e₁`, the trace: the sum of the `1×1` principal minors, coefficient of `x²` (up to sign). -/
def endomorphismTraceThree (matrix : SetoidMatrix Int) : Int :=
  matrix.entry 0 0 + matrix.entry 1 1 + matrix.entry 2 2

/-- `e₂`, the sum of the three `2×2` principal minors (index pairs `{0,1} {0,2} {1,2}`), coefficient
of `x`.  This is the middle coefficient the trace/determinant/rank separators cannot reach. -/
def endomorphismPrincipalTwoMinorSumThree (matrix : SetoidMatrix Int) : Int :=
  intMinorDet matrix 2 selectPairLow selectPairLow
    + intMinorDet matrix 2 selectPairOuter selectPairOuter
    + intMinorDet matrix 2 selectPairHigh selectPairHigh

/-- `e₃`, the determinant: the single `3×3` principal minor, the constant coefficient (up to sign). -/
def endomorphismDeterminantThree (matrix : SetoidMatrix Int) : Int :=
  intCofactorDet 3 matrix

/-- The characteristic polynomial of a `3×3` integer matrix as its coefficient triple
`(e₁, e₂, e₃) = (trace, Σ principal 2×2 minors, det)`.  A similarity invariant, no polynomial ring. -/
def endomorphismCharPolyThree (matrix : SetoidMatrix Int) : Int × Int × Int :=
  (endomorphismTraceThree matrix,
   endomorphismPrincipalTwoMinorSumThree matrix,
   endomorphismDeterminantThree matrix)

/-- `source` and `target` are dissimilar because their characteristic polynomials differ. -/
@[reducible] def EndomorphismDissimilarByCharPolyThree (source target : SetoidMatrix Int) : Prop :=
  endomorphismCharPolyThree source ≠ endomorphismCharPolyThree target

/-! ## Groundings -/

/-- The identity's characteristic polynomial `x³ − 3x² + 3x − 1 = (x−1)³`: triple `(3, 3, 1)`. -/
theorem endomorphismCharPolyThreeIdentityExample :
    endomorphismCharPolyThree (setoidMatrixOfRows [[1, 0, 0], [0, 1, 0], [0, 0, 1]]) = (3, 3, 1) := rfl

/-- The char poly of `diag(0, 1, −1)` is `x³ − x`: triple `(0, −1, 0)`. -/
theorem endomorphismCharPolyThreeDiagOnePlusMinusExample :
    endomorphismCharPolyThree (setoidMatrixOfRows [[0, 0, 0], [0, 1, 0], [0, 0, -1]]) = (0, -1, 0) := rfl

/-- The char poly of `diag(0, 2, −2)` is `x³ − 4x`: triple `(0, −4, 0)` — same trace and determinant
as `diag(0, 1, −1)`, but the middle coefficient is `−4`. -/
theorem endomorphismCharPolyThreeDiagTwoPlusMinusExample :
    endomorphismCharPolyThree (setoidMatrixOfRows [[0, 0, 0], [0, 2, 0], [0, 0, -2]]) = (0, -4, 0) := rfl

/-- The char-poly separator sees what trace, determinant, and rank cannot: `diag(0, 1, −1)` and
`diag(0, 2, −2)` agree on all three yet differ in `e₂` (`x³ − x` vs `x³ − 4x`), so they are
dissimilar.  The refutation projects the middle component and closes by `Int`/`Nat.noConfusion`. -/
theorem endomorphismCharPolyThreeSeparatesEqualTraceEqualDetEqualRank :
    EndomorphismDissimilarByCharPolyThree
      (setoidMatrixOfRows [[0, 0, 0], [0, 1, 0], [0, 0, -1]])
      (setoidMatrixOfRows [[0, 0, 0], [0, 2, 0], [0, 0, -2]]) :=
  fun charPolyEquation =>
    Int.noConfusion
      (congrArg (fun coefficientTriple => coefficientTriple.2.1) charPolyEquation)
      (fun middleCoefficientEquation => Nat.noConfusion middleCoefficientEquation)

end FX1Poly.ComputerAlgebra
