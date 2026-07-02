import FX1Poly.ComputerAlgebra.Number.IntMulAssociativity
import FX1Poly.ComputerAlgebra.Number.NatEuclideanDivision

/-! # FX1Poly/ComputerAlgebra/Number/NatGreatestCommonDivisor — counting Euclid
    (NUM-Q-4a)

Init's `Nat.gcd` is defined by well-founded recursion (banned: `WellFounded.fix`
does not compute by kernel reduction and its equation lemmas are propext-dirty).
This module hand-rolls Euclid's algorithm STRUCTURALLY on a fuel argument over
the counting divider (`natDivModCounting`), with the divides certificates proved
by the same fuel induction.

  * `NatDivides divisor value` is the explicit-witness divisibility
    `∃ quotient, value = divisor * quotient` — divisor on the LEFT, matching the
    counting divider's reconstruction shape, so the multiple-of-the-divisor step
    is one `natMulAssoc`.
  * `natGcdWithFuel` recurses on fuel only; the Euclid step swaps
    `(leftValue, rightValue) ↦ (rightValue mod leftValue, leftValue)`, and the
    remainder bound keeps the invariant `leftValue < fuel` — so `fuel =
    leftValue + 1` always suffices (`natGcd`).
  * The divides-left and divides-right certificates are mutually entangled
    through the argument swap, so `natGcdWithFuelDividesBoth` proves the
    conjunction in ONE induction; the wrappers project it.

Deferred to the Bezout/normal-form rungs: greatest-ness (every common divisor
divides the gcd — needs the extended witness), and fuel-irrelevance (the
recurrence equation between `natGcd` calls at different fuels).

## Zero-axiom

Structural fuel recursion, `Exists` witness arithmetic over
`congrArg`/`Eq.trans`, `nomatch` on the empty fuel-exhausted bound.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`, no
`WellFounded.fix`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/Number/NatGreatestCommonDivisor.lean`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Divisibility with explicit witnesses -/

/-- `divisor` divides `value`, witnessed by the cofactor.  The divisor sits on
the LEFT of the product so the counting divider's reconstruction
`dividend = divisor * quotient + remainder` plugs in without commutations. -/
def NatDivides (divisor value : Nat) : Prop :=
  ∃ quotient, value = divisor * quotient

/-- Everything divides zero — `divisor * 0` reduces definitionally. -/
theorem natDividesZero (divisor : Nat) : NatDivides divisor 0 :=
  ⟨0, rfl⟩

/-- Everything divides itself — `value * 1` is `0 + value` definitionally. -/
theorem natDividesRefl (value : Nat) : NatDivides value value :=
  ⟨1, (Nat.zero_add value).symm⟩

/-- Transport divisibility along an equality of the divided value. -/
theorem natDividesOfEq {divisor value otherValue : Nat}
    (areEqual : otherValue = value) (divides : NatDivides divisor value) :
    NatDivides divisor otherValue :=
  match divides with
  | ⟨quotient, valueEquation⟩ => ⟨quotient, areEqual.trans valueEquation⟩

/-- A divisor of `value` divides every right multiple of `value` — one
associativity step on the witness. -/
theorem natDividesMulRight {divisor value : Nat} (scaleFactor : Nat)
    (divides : NatDivides divisor value) :
    NatDivides divisor (value * scaleFactor) :=
  match divides with
  | ⟨quotient, valueEquation⟩ =>
      ⟨quotient * scaleFactor,
        (congrArg (· * scaleFactor) valueEquation).trans
          (natMulAssoc divisor quotient scaleFactor)⟩

/-- A common divisor divides the sum — the witnesses add through left
distributivity. -/
theorem natDividesAdd {divisor leftValue rightValue : Nat}
    (dividesLeft : NatDivides divisor leftValue)
    (dividesRight : NatDivides divisor rightValue) :
    NatDivides divisor (leftValue + rightValue) :=
  match dividesLeft, dividesRight with
  | ⟨leftQuotient, leftEquation⟩, ⟨rightQuotient, rightEquation⟩ =>
      ⟨leftQuotient + rightQuotient,
        (congrArg (· + rightValue) leftEquation).trans
          ((congrArg (divisor * leftQuotient + ·) rightEquation).trans
            (Nat.left_distrib divisor leftQuotient rightQuotient).symm)⟩

/-- A divisor of a successor is positive — a zero divisor would make the
successor a zero product. -/
theorem natDivisorOfSuccIsPositive {divisor valuePredecessor : Nat}
    (divides : NatDivides divisor (valuePredecessor + 1)) : 0 < divisor :=
  match divisor, divides with
  | 0, ⟨quotient, valueEquation⟩ =>
      Nat.noConfusion (valueEquation.trans (Nat.zero_mul quotient))
  | divisorPredecessor + 1, _ =>
      natSuccLeSuccOfLe (natZeroLe divisorPredecessor)

/-! ## Euclid's algorithm, structural on fuel -/

/-- Euclid by counting division, STRUCTURAL on the fuel (never
`WellFounded.fix`).  The step swaps in the remainder:
`gcd(a, b) = gcd(b mod a, a)`.  The first argument strictly decreases, so any
`fuel > leftValue` reaches the zero base case; the fuel-exhausted arm returns
`rightValue` so that `gcd(0, b) = b` holds at EVERY fuel. -/
def natGcdWithFuel : Nat → Nat → Nat → Nat
  | 0, _, rightValue => rightValue
  | _ + 1, 0, rightValue => rightValue
  | fuel + 1, leftPredecessor + 1, rightValue =>
      natGcdWithFuel fuel
        (natDivModCounting rightValue (leftPredecessor + 1)).snd
        (leftPredecessor + 1)

/-- **The divides certificates, jointly** — the two sides are entangled through
Euclid's argument swap, so one fuel induction carries the conjunction: the
callee's divides-right IS the caller's divides-left, and the caller's
divides-right recombines the callee's pair through the reconstruction
`rightValue = leftValue * quotient + remainder`. -/
theorem natGcdWithFuelDividesBoth : ∀ fuel leftValue rightValue : Nat,
    leftValue < fuel →
    NatDivides (natGcdWithFuel fuel leftValue rightValue) leftValue ∧
    NatDivides (natGcdWithFuel fuel leftValue rightValue) rightValue
  | 0, _, _, isBelowFuel => nomatch isBelowFuel
  | _ + 1, 0, rightValue, _ =>
      ⟨natDividesZero rightValue, natDividesRefl rightValue⟩
  | fuel + 1, leftPredecessor + 1, rightValue, isBelowFuel =>
      have remainderIsBelowFuel :
          (natDivModCounting rightValue (leftPredecessor + 1)).snd < fuel :=
        natLeTrans
          (natDivModCountingRemainderIsBounded rightValue (leftPredecessor + 1)
            (natSuccLeSuccOfLe (natZeroLe leftPredecessor)))
          (Nat.le_of_succ_le_succ isBelowFuel)
      match natGcdWithFuelDividesBoth fuel
          (natDivModCounting rightValue (leftPredecessor + 1)).snd
          (leftPredecessor + 1) remainderIsBelowFuel with
      | ⟨dividesRemainder, dividesLeftSucc⟩ =>
          ⟨dividesLeftSucc,
            natDividesOfEq
              (natDivModCountingReconstructs rightValue (leftPredecessor + 1))
              (natDividesAdd
                (natDividesMulRight
                  (natDivModCounting rightValue (leftPredecessor + 1)).fst
                  dividesLeftSucc)
                dividesRemainder)⟩

/-! ## The canonical-fuel wrapper -/

/-- The greatest common divisor — `fuel = leftValue + 1` always suffices
because the first argument strictly decreases along Euclid's swap. -/
def natGcd (leftValue rightValue : Nat) : Nat :=
  natGcdWithFuel (leftValue + 1) leftValue rightValue

/-- `gcd(0, b) = b`, definitionally. -/
theorem natGcdZeroLeft (rightValue : Nat) : natGcd 0 rightValue = rightValue :=
  rfl

/-- The gcd divides its left argument. -/
theorem natGcdDividesLeft (leftValue rightValue : Nat) :
    NatDivides (natGcd leftValue rightValue) leftValue :=
  (natGcdWithFuelDividesBoth (leftValue + 1) leftValue rightValue
    Nat.le.refl).left

/-- The gcd divides its right argument. -/
theorem natGcdDividesRight (leftValue rightValue : Nat) :
    NatDivides (natGcd leftValue rightValue) rightValue :=
  (natGcdWithFuelDividesBoth (leftValue + 1) leftValue rightValue
    Nat.le.refl).right

/-- The gcd of a positive left argument is positive — it divides that
successor.  (The normalized-denominator positivity supplier for the ℚ
canonical form.) -/
theorem natGcdOfSuccLeftIsPositive (leftPredecessor rightValue : Nat) :
    0 < natGcd (leftPredecessor + 1) rightValue :=
  natDivisorOfSuccIsPositive (natGcdDividesLeft (leftPredecessor + 1) rightValue)

end FX1Poly.ComputerAlgebra
