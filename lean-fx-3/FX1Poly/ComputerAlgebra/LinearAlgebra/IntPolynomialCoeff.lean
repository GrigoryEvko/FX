import FX1Poly.ComputerAlgebra.LinearAlgebra.IntUnivariatePolynomial

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/IntPolynomialCoeff — the coefficient accessor
(the fifth brick of `invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255)

The Euclidean GCD's termination rests on the degree strictly dropping at each pseudo-division step, which
is a *leading-term cancellation* fact: the step subtracts two polynomials with the same top coefficient, so
that coefficient vanishes.  Reasoning about individual coefficients is far cleaner through a positional
accessor than through the trailing-zero `polyTrim` length.

## The accessor

`polyCoeff p n` reads the coefficient of `xⁿ` in `p` (0 past the end).  Under it every ring operation is a
pointwise operation on coefficients — `polyCoeff` is a family of ring homomorphisms
`ℤ[x] → ℤ`, one per position — proved by structural induction:
`polyCoeffScale`/`polyCoeffAdd`/`polyCoeffNeg`/`polyCoeffSub`, plus `polyCoeffMonomialAt` (a monomial's
coefficient at its own degree is the scalar).

## Zero-axiom design

Every definition is structural on the coefficient list and the position; every arithmetic step routes
through the corpus `Int` lemmas.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/IntPolynomialCoeff.lean`.
-/

namespace FX1Poly.ComputerAlgebra

/-! ## The positional coefficient accessor -/

/-- `polyCoeff p n` — the coefficient of `xⁿ` in the ascending list `p`, or `0` past the end. -/
def polyCoeff : List Int → Nat → Int
  | [], _ => 0
  | coeff :: _, 0 => coeff
  | _ :: restCoeffs, position + 1 => polyCoeff restCoeffs position

/-! ## Each coefficient is a ring homomorphism -/

/-- **Scaling acts coefficientwise.**  `polyCoeff (scalar · p) n = scalar · polyCoeff p n`. -/
theorem polyCoeffScale (scalar : Int) :
    ∀ (coeffs : List Int) (position : Nat),
      polyCoeff (polyScale scalar coeffs) position = scalar * polyCoeff coeffs position
  | [], _ => (intMulZero scalar).symm
  | _ :: _, 0 => rfl
  | _ :: restCoeffs, position + 1 => polyCoeffScale scalar restCoeffs position

/-- **Addition acts coefficientwise.**  `polyCoeff (p + q) n = polyCoeff p n + polyCoeff q n` (tail padding
handled by the empty-list arm returning `0`). -/
theorem polyCoeffAdd :
    ∀ (leftPoly rightPoly : List Int) (position : Nat),
      polyCoeff (polyAdd leftPoly rightPoly) position
        = polyCoeff leftPoly position + polyCoeff rightPoly position
  | [], rightPoly, position => (intZeroAdd (polyCoeff rightPoly position)).symm
  | _ :: _, [], position => (intAddZero (polyCoeff (_ :: _) position)).symm
  | _ :: _, _ :: _, 0 => rfl
  | _ :: leftTail, _ :: rightTail, position + 1 => polyCoeffAdd leftTail rightTail position

/-- **Negation acts coefficientwise.**  `polyCoeff (-p) n = -(polyCoeff p n)`. -/
theorem polyCoeffNeg :
    ∀ (coeffs : List Int) (position : Nat),
      polyCoeff (polyNeg coeffs) position = -(polyCoeff coeffs position)
  | [], _ => intNegZero.symm
  | _ :: _, 0 => rfl
  | _ :: restCoeffs, position + 1 => polyCoeffNeg restCoeffs position

/-- **Subtraction acts coefficientwise.**  `polyCoeff (p − q) n = polyCoeff p n − polyCoeff q n`. -/
theorem polyCoeffSub (leftPoly rightPoly : List Int) (position : Nat) :
    polyCoeff (polySub leftPoly rightPoly) position
      = polyCoeff leftPoly position - polyCoeff rightPoly position :=
  (polyCoeffAdd leftPoly (polyNeg rightPoly) position).trans
    ((congrArg (polyCoeff leftPoly position + ·) (polyCoeffNeg rightPoly position)).trans
      (intSubEqAddNeg (polyCoeff leftPoly position) (polyCoeff rightPoly position)).symm)

/-- **A monomial's coefficient at its own degree is the scalar.**  `polyCoeff (coeff · x^degree) degree =
coeff`, by induction on the degree. -/
theorem polyCoeffMonomialAt (coeff : Int) :
    ∀ degree : Nat, polyCoeff (polyMonomial coeff degree) degree = coeff
  | 0 => rfl
  | degree + 1 => polyCoeffMonomialAt coeff degree

/-! ## The monomial-times-polynomial coefficient shift (the leading-term-cancellation lever) -/

/-- The one-element zero polynomial reads `0` at every position (the `polyMul` convolution's tail padding). -/
theorem polyCoeffSingletonZero : ∀ position : Nat, polyCoeff [(0 : Int)] position = 0
  | 0 => rfl
  | _ + 1 => rfl

/-- **Multiplying by a monomial shifts and scales coefficients.**  `polyCoeff (coeff · x^degree · poly)
(position + degree) = coeff · polyCoeff poly position`: the degree-`degree` monomial slides `poly` up by
`degree` places and scales it by `coeff`.  By induction on `degree` — the base case is the `polyMul`
convolution `polyAdd (polyScale coeff poly) [0]`, and each successive degree prepends a `0` (a
`polyScale 0 poly` summand that annihilates) and consumes one position.  This is the exact statement the
pseudo-division step needs: the quotient-term product's coefficient at the top position of the dividend. -/
theorem polyCoeffMonomialMul (coeff : Int) (poly : List Int) (position : Nat) :
    ∀ degree : Nat,
      polyCoeff (polyMul (polyMonomial coeff degree) poly) (position + degree)
        = coeff * polyCoeff poly position
  | 0 => by
      show polyCoeff (polyAdd (polyScale coeff poly) [0]) position = coeff * polyCoeff poly position
      rw [polyCoeffAdd, polyCoeffScale, polyCoeffSingletonZero, intAddZero]
  | degree + 1 => by
      show polyCoeff (polyAdd (polyScale 0 poly) (0 :: polyMul (polyMonomial coeff degree) poly))
             (position + degree + 1) = coeff * polyCoeff poly position
      rw [polyCoeffAdd, polyCoeffScale, intZeroMul, intZeroAdd]
      show polyCoeff (polyMul (polyMonomial coeff degree) poly) (position + degree)
             = coeff * polyCoeff poly position
      exact polyCoeffMonomialMul coeff poly position degree

/-! ## Groundings -/

/-- `1 + 2x²` has coefficient `2` at position `2`: `polyCoeff [1, 0, 2] 2 = 2`. -/
theorem polyCoeffExample : polyCoeff [1, 0, 2] 2 = 2 := by decide

/-- Past the end reads `0`: `polyCoeff [1, 0, 2] 5 = 0`. -/
theorem polyCoeffPastEnd : polyCoeff [1, 0, 2] 5 = 0 := by decide

/-- Scaling exhibited: `polyCoeff (polyScale 3 [1, 0, 2]) 2 = 3 * polyCoeff [1, 0, 2] 2` (`6 = 3·2`). -/
theorem polyCoeffScaleGrounding :
    polyCoeff (polyScale 3 [1, 0, 2]) 2 = 3 * polyCoeff [1, 0, 2] 2 := by decide

/-- The monomial shift exhibited: `5·x² · (7 + 2x)` has, at position `2 + 1 = 3`, the coefficient
`5 · (coefficient of x¹ in 7 + 2x) = 5 · 2 = 10` — `polyCoeff (polyMul (polyMonomial 5 2) [7, 2]) 3 =
5 * polyCoeff [7, 2] 1`. -/
theorem polyCoeffMonomialMulGrounding :
    polyCoeff (polyMul (polyMonomial 5 2) [7, 2]) 3 = 5 * polyCoeff [7, 2] 1 := by decide

/-- Marker: the ℤ[x] positional coefficient accessor ships with each coefficient proved a ring
homomorphism (scale/add/neg/sub) plus the monomial-at-its-degree fact — the leading-term-cancellation
substrate for the pseudo-division degree-decrease (the Euclidean GCD's termination lever). -/
def fxIntPoly_hasCoefficientHomomorphisms : Bool := true

end FX1Poly.ComputerAlgebra
