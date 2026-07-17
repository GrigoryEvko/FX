import FX1Poly.ComputerAlgebra.LinearAlgebra.EndomorphismMinorSelector

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/EndomorphismCharPolyThree — the char poly via principal minors

WP-ENDO r2, the `charMatrixCarrier` wall.  The characteristic polynomial `det(x·I − M)` is the sharpest
single similarity invariant short of the full invariant-factor decomposition.  The naive route builds a
POLYNOMIAL-valued matrix `x·I − M` and a determinant over `ℤ[x]` — a fresh polynomial-ring build.  The
sharper route needs no polynomial ring at all: the coefficients of the characteristic polynomial ARE
sums of principal minors,

  `det(x·I − M) = x^n − e₁ x^{n-1} + e₂ x^{n-2} − ⋯ + (−1)ⁿ eₙ`,   `e_k = Σ (k×k principal minors of M)`,

so the general minor selector (`intMinorDet`, [[EndomorphismMinorSelector]]) computes every coefficient
directly.  For dimension `3` the elementary-symmetric triple is `(e₁, e₂, e₃) = (trace, Σ principal 2×2
minors, det)`.

The MIDDLE coefficient `e₂` is genuine content the r1 separators cannot see: `diag(0, 1, −1)` and
`diag(0, 2, −2)` share trace `0`, determinant `0`, AND rank `2` — the trace, determinant, and
rank-at-dimension-`3` separators are ALL blind — yet their characteristic polynomials `x³ − x` and
`x³ − 4x` differ in exactly `e₂` (`−1` versus `−4`).  So the char-poly triple strictly refines every
earlier per-input separator.

The scope stays the r1 PER-INPUT contract: a concrete matrix gets a concrete char-poly certificate
that `decide` checks.  The char poly is a PARTIAL invariant (equal char poly ⇏ similar — see the
split-versus-full-Jordan pair, which shares char poly `x²` yet is separated by the rank sequence,
[[EndomorphismPowerZeroSeparator]]); the complete separator is the invariant-factor Smith-over-`ℚ[x]`
wall, still open.

Raw Lean 4 + Init; every declaration axiom-free (function-valued minor selection keeps `propext` out). -/

namespace FX1Poly.ComputerAlgebra

/-! ## The elementary-symmetric coefficients at dimension 3 -/

/-- `e₁` — the trace, the sum of the `1×1` principal minors.  Coefficient of `x²` (up to sign) in the
characteristic polynomial. -/
def endomorphismTraceThree (matrix : SetoidMatrix Int) : Int :=
  matrix.entry 0 0 + matrix.entry 1 1 + matrix.entry 2 2

/-- `e₂` — the sum of the three `2×2` PRINCIPAL minors (row and column index set equal): the pairs
`{0,1} {0,2} {1,2}`.  Coefficient of `x` in the characteristic polynomial.  This is the middle
coefficient the trace/determinant/rank separators cannot reach. -/
def endomorphismPrincipalTwoMinorSumThree (matrix : SetoidMatrix Int) : Int :=
  intMinorDet matrix 2 selectPairLow selectPairLow
    + intMinorDet matrix 2 selectPairOuter selectPairOuter
    + intMinorDet matrix 2 selectPairHigh selectPairHigh

/-- `e₃` — the determinant, the single `3×3` principal minor.  The constant coefficient (up to sign) of
the characteristic polynomial. -/
def endomorphismDeterminantThree (matrix : SetoidMatrix Int) : Int :=
  intCofactorDet 3 matrix

/-- The characteristic polynomial of a `3×3` integer matrix, presented as its elementary-symmetric
coefficient triple `(e₁, e₂, e₃) = (trace, Σ principal 2×2 minors, det)`.  The polynomial itself is
`x³ − e₁ x² + e₂ x − e₃`.  A similarity invariant, computed entirely from the general minor selector —
no polynomial ring, no polynomial-valued matrix. -/
def endomorphismCharPolyThree (matrix : SetoidMatrix Int) : Int × Int × Int :=
  (endomorphismTraceThree matrix,
   endomorphismPrincipalTwoMinorSumThree matrix,
   endomorphismDeterminantThree matrix)

/-- `source` and `target` are dissimilar because their characteristic polynomials differ. -/
@[reducible] def EndomorphismDissimilarByCharPolyThree (source target : SetoidMatrix Int) : Prop :=
  endomorphismCharPolyThree source ≠ endomorphismCharPolyThree target

/-! ## Groundings — the char-poly triple on concrete `3×3` matrices -/

/-- The identity's characteristic polynomial `x³ − 3x² + 3x − 1 = (x−1)³`: triple `(3, 3, 1)`. -/
theorem endomorphismCharPolyThreeIdentityExample :
    endomorphismCharPolyThree (setoidMatrixOfRows [[1, 0, 0], [0, 1, 0], [0, 0, 1]]) = (3, 3, 1) := rfl

/-- The char poly of `diag(0, 1, −1)` is `x³ − x`: triple `(0, −1, 0)` — trace `0`, principal-`2×2`-minor
sum `−1`, determinant `0`. -/
theorem endomorphismCharPolyThreeDiagOnePlusMinusExample :
    endomorphismCharPolyThree (setoidMatrixOfRows [[0, 0, 0], [0, 1, 0], [0, 0, -1]]) = (0, -1, 0) := rfl

/-- The char poly of `diag(0, 2, −2)` is `x³ − 4x`: triple `(0, −4, 0)` — same trace and determinant as
`diag(0, 1, −1)`, but the middle coefficient is `−4`. -/
theorem endomorphismCharPolyThreeDiagTwoPlusMinusExample :
    endomorphismCharPolyThree (setoidMatrixOfRows [[0, 0, 0], [0, 2, 0], [0, 0, -2]]) = (0, -4, 0) := rfl

/-- ★ The char-poly separator sees what trace, determinant, AND rank cannot.  `diag(0, 1, −1)` and
`diag(0, 2, −2)` agree on trace (`0`), determinant (`0`), and rank (`2`) — every r1 separator and the
rank-at-dimension-`3` separator is blind — yet their characteristic polynomials `x³ − x` and `x³ − 4x`
differ in the middle coefficient, so they are dissimilar.  The `(0,−1,0) ≠ (0,−4,0)` refutation projects
the middle component and closes by `Int`/`Nat.noConfusion`, propext-free. -/
theorem endomorphismCharPolyThreeSeparatesEqualTraceEqualDetEqualRank :
    EndomorphismDissimilarByCharPolyThree
      (setoidMatrixOfRows [[0, 0, 0], [0, 1, 0], [0, 0, -1]])
      (setoidMatrixOfRows [[0, 0, 0], [0, 2, 0], [0, 0, -2]]) :=
  fun charPolyEquation =>
    Int.noConfusion
      (congrArg (fun coefficientTriple => coefficientTriple.2.1) charPolyEquation)
      (fun middleCoefficientEquation => Nat.noConfusion middleCoefficientEquation)

/-! ## The marker -/

/-- ★ **The characteristic polynomial is computed without a polynomial ring.**  `= true` records that
`endomorphismCharPolyThree` reads off the full elementary-symmetric coefficient triple `(trace, Σ
principal 2×2 minors, det)` from the general minor selector — the `charMatrixCarrier` wall of WP-ENDO r1
closed by the principal-minor route rather than a `ℤ[x]`-valued matrix.  The middle coefficient is a
genuine new similarity invariant.  The char poly stays a PARTIAL invariant; the complete separator
(invariant factors via Smith-over-`ℚ[x]`) remains the honest open wall. -/
def fxEndo_hasCharPolyViaPrincipalMinors : Bool := true

end FX1Poly.ComputerAlgebra
