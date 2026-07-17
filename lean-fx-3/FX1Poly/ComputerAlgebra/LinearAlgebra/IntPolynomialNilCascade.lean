import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialGcd
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialCoeffBounds

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/IntPolynomialNilCascade — the zero-polynomial nil cascade
(the seventeenth brick of `invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255)

The nil-preservation primitives the fuel-adequacy → true-fixed-point wiring needs at its zero-polynomial
edge: the coefficient ↔ trims-to-nil bridge in both directions, the vanishing of a zero-coefficient
monomial's products, and the fact that pseudo-dividing the **zero polynomial** yields a zero remainder for
every fuel.

## What is PROVEN

  * `polyTrimNilOfAllCoeffZero`: `(∀ pos, polyCoeff coeffs pos = 0) → polyTrim coeffs = []` — all-zero
    coefficients trim away.
  * `polyCoeffZeroOfTrimNil`: `polyTrim coeffs = [] → polyCoeff coeffs pos = 0` — the converse (a
    trimmed-away polynomial has no coefficients), off r18's `polyCoeffZeroFromTrimLength`.
  * `polyMulZeroMonomialCoeff`: `polyCoeff (polyMul (polyMonomial 0 degree) divisor) pos = 0` — a
    zero-coefficient monomial annihilates any product.
  * `polyPseudoRemZeroDividendTrimsNil`: `polyTrim dividend = [] → polyTrim (polyPseudoRem fuel divisor
    dividend) = []` — pseudo-dividing the zero polynomial leaves a zero remainder (the recursion's step keeps
    the dividend a zero polynomial, so it never escapes nil).

## Zero-axiom design

Structural recursions on the coefficient list / degree / fuel; the coefficient homomorphisms
(`polyCoeffAdd`/`Scale`/`Sub`), `polyCoeffZeroFromTrimLength` (r18), and `Int.decEq`-clean trimming.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated
in `FX1PolyAudit/ComputerAlgebra/LinearAlgebra/IntPolynomialNilCascade.lean`.
-/

namespace FX1Poly.ComputerAlgebra

/-! ## The coefficient ↔ trims-to-nil bridge -/

/-- `polyTrim rest = [] → polyTrim (0 :: rest) = []` — prepending a zero to a trimmed-away tail still trims
away (the trailing-zero drop applies to the new head). -/
theorem polyTrimConsZeroNil (rest : List Int) (trimRestNil : polyTrim rest = []) :
    polyTrim (0 :: rest) = [] := by
  unfold polyTrim
  rw [trimRestNil]
  show (match Int.decEq (0 : Int) 0 with | isTrue _ => ([] : List Int) | isFalse _ => [(0 : Int)]) = []
  rfl

/-- **All-zero coefficients trim to nil.**  `(∀ pos, polyCoeff coeffs pos = 0) → polyTrim coeffs = []`, by
structural induction on the coefficient list — the head is `polyCoeff coeffs 0 = 0` and the tail is all-zero
by shifting the hypothesis. -/
theorem polyTrimNilOfAllCoeffZero : ∀ (coeffs : List Int),
    (∀ pos : Nat, polyCoeff coeffs pos = 0) → polyTrim coeffs = []
  | [], _ => rfl
  | coeff :: rest, allZero => by
      have headZero : coeff = 0 := allZero 0
      have trimRestNil : polyTrim rest = [] :=
        polyTrimNilOfAllCoeffZero rest (fun pos => allZero (pos + 1))
      rw [headZero]
      exact polyTrimConsZeroNil rest trimRestNil

/-- **A trimmed-away polynomial has no coefficients.**  `polyTrim coeffs = [] → polyCoeff coeffs pos = 0`,
off r18's `polyCoeffZeroFromTrimLength` with `(polyTrim coeffs).length = 0 ≤ pos`. -/
theorem polyCoeffZeroOfTrimNil (coeffs : List Int) (pos : Nat) (trimNil : polyTrim coeffs = []) :
    polyCoeff coeffs pos = 0 :=
  polyCoeffZeroFromTrimLength coeffs pos (by rw [trimNil]; exact Nat.zero_le pos)

/-! ## A zero-coefficient monomial annihilates products -/

/-- `polyCoeff [0] pos = 0` — the zero singleton has no coefficients. -/
theorem polyCoeffZeroSingleton : ∀ pos : Nat, polyCoeff [(0 : Int)] pos = 0
  | 0 => rfl
  | _ + 1 => rfl

/-- `polyCoeff (0 :: rest) (pos+1) = polyCoeff rest pos` and `polyCoeff (0 :: rest) 0 = 0` — the leading-zero
shift, packaged for the zero-monomial induction. -/
theorem polyCoeffZeroConsSucc (rest : List Int) (pos : Nat) :
    polyCoeff ((0 : Int) :: rest) (pos + 1) = polyCoeff rest pos := rfl

/-- **A zero-coefficient monomial annihilates any product.**  `polyCoeff (polyMul (polyMonomial 0 degree)
divisor) pos = 0` for every position — the monomial's zero coefficient scales everything to `0`, and its
leading zeros contribute only shifts.  Induction on `degree`. -/
theorem polyMulZeroMonomialCoeff : ∀ (degree : Nat) (divisor : List Int) (pos : Nat),
    polyCoeff (polyMul (polyMonomial 0 degree) divisor) pos = 0
  | 0, divisor, pos => by
      show polyCoeff (polyAdd (polyScale 0 divisor) (0 :: polyMul [] divisor)) pos = 0
      rw [polyCoeffAdd, polyCoeffScale, intZeroMul]
      show (0 : Int) + polyCoeff ((0 : Int) :: polyMul [] divisor) pos = 0
      cases pos with
      | zero => rfl
      | succ predPos =>
          rw [polyCoeffZeroConsSucc]
          show (0 : Int) + polyCoeff (polyMul ([] : List Int) divisor) predPos = 0
          rw [intZeroAdd]
          rfl
  | degree + 1, divisor, pos => by
      show polyCoeff (polyAdd (polyScale 0 divisor) (0 :: polyMul (polyMonomial 0 degree) divisor)) pos = 0
      rw [polyCoeffAdd, polyCoeffScale, intZeroMul, intZeroAdd]
      cases pos with
      | zero => rfl
      | succ predPos =>
          rw [polyCoeffZeroConsSucc]
          exact polyMulZeroMonomialCoeff degree divisor predPos

/-! ## Pseudo-dividing the zero polynomial -/

/-- **Pseudo-dividing the zero polynomial leaves a zero remainder.**  `polyTrim dividend = [] →
polyTrim (polyPseudoRem fuel divisor dividend) = []` for every fuel: the `isTrue` guard returns the (zero)
dividend, and the `isFalse` step replaces it by `leadDivisor·dividend − (leadDividend·x^k)·divisor`, both of
whose coefficients vanish (the dividend is zero, and `leadDividend = 0`), so the step is again a zero
polynomial and the recursion never leaves nil. -/
theorem polyPseudoRemZeroDividendTrimsNil (divisor : List Int) :
    ∀ (fuel : Nat) (dividend : List Int), polyTrim dividend = [] →
      polyTrim (polyPseudoRem fuel divisor dividend) = []
  | 0, _, trimNil => trimNil
  | fuel + 1, dividend, trimNil => by
      show polyTrim (polyPseudoDivMod (fuel + 1) divisor dividend).2.2 = []
      dsimp only [polyPseudoDivMod]
      cases Nat.decLt (polyDegree dividend) (polyDegree divisor) with
      | isTrue _ => exact trimNil
      | isFalse _ =>
          apply polyPseudoRemZeroDividendTrimsNil divisor fuel
          apply polyTrimNilOfAllCoeffZero
          intro pos
          have leadDividendZero : polyLeadingCoeff dividend = 0 := by
            show lastOrZero (polyTrim dividend) = 0
            rw [trimNil]
            rfl
          rw [polyCoeffSub]
          have scaleZero : polyCoeff (polyScale (polyLeadingCoeff divisor) dividend) pos = 0 := by
            rw [polyCoeffScale, polyCoeffZeroOfTrimNil dividend pos trimNil]
            exact intMulZero _
          have mulZero :
              polyCoeff (polyMul
                  (polyMonomial (polyLeadingCoeff dividend) (polyDegree dividend - polyDegree divisor))
                  divisor) pos = 0 := by
            rw [leadDividendZero]
            exact polyMulZeroMonomialCoeff (polyDegree dividend - polyDegree divisor) divisor pos
          rw [scaleZero, mulZero]
          exact (intSubEqAddNeg (0 : Int) 0).trans (intAddRightNeg 0)

/-! ## Grounding -/

/-- Pseudo-dividing the zero polynomial `[0, 0]` by `x + 1` leaves a zero remainder at fuel 5 —
`polyTrim (polyPseudoRem 5 [1, 1] [0, 0]) = []`. -/
theorem polyPseudoRemZeroDividendGrounding : polyTrim (polyPseudoRem 5 [1, 1] [0, 0]) = [] := by decide

/-- Marker: the ℤ[x] zero-polynomial nil cascade — the coefficient ↔ trims-to-nil bridge
(`polyTrimNilOfAllCoeffZero` / `polyCoeffZeroOfTrimNil`), zero-monomial annihilation
(`polyMulZeroMonomialCoeff`), and pseudo-dividing the zero polynomial leaves a zero remainder
(`polyPseudoRemZeroDividendTrimsNil`) — the zero-polynomial edge primitives of the fuel-adequacy wiring. -/
def fxIntPoly_hasZeroPolynomialNilCascade : Bool := true

end FX1Poly.ComputerAlgebra
