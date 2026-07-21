import FX1Poly.ComputerAlgebra.Number.NatGreatestCommonDivisor
import FX1Poly.ComputerAlgebra.Number.IntNegation
import FX1Poly.ComputerAlgebra.Number.IntOrderAlgebra

/-! # The signed greatest common divisor

The Smith-normal-form engine over ℤ (`ComputerAlgebra/LinearAlgebra/SmithNormalForm`) needs an
integer gcd with witnessed properties: the pivot-selection cascade divides by the gcd, and the
invariant-factor chain `d1 | d2 | ...` is a chain of `IntDivides`. Init's `Int.gcd` and the `Int`
divisibility corpus leak `propext` on this toolchain, so the gcd is built by lifting the Nat kit
(`NatGreatestCommonDivisor`) through `Int.natAbs` and reattaching the sign, certificate-first.

  * `IntDivides divisor value := ∃ factor, value = divisor * factor` — the `Int` sibling of
    `NatDivides` (divisor on the LEFT), the same shape as `IntMatrix`'s `dividesExactly`.
  * `intGcd a b := Int.ofNat (natGcd a.natAbs b.natAbs)` — the canonical NONNEGATIVE
    representative (the ℤ gcd is unique only up to the unit `±1`; nonnegative matches
    `IsSmithNormalFormWithin.diagonalIsNonnegative`).
  * The sign bridges `intDividesOfNatDividesNatAbs` and `natDividesNatAbsOfIntDivides` carry
    `natGcdDividesLeft/Right` and `natDividesGcdOfDividesBoth` up to the signed
    `intGcdDividesLeft/Right` and `intGcdGreatest`.

One caveat: a Bezout coefficient identity over `Int` and a decidable `IntDivides` instance are
not provided here; this module supplies the divides/greatest structure the SNF driver consumes.

Per-constructor `Int` matches and `congrArg`/`Eq.trans` over the negation kit and the Nat gcd
certificates; free of `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`, and `WellFounded.fix`. Per-declaration gated in the audit twin. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Integer divisibility with explicit witnesses -/

/-- `divisor` divides `value` over the integers, with explicit cofactor and divisor on the
LEFT (the `Int` sibling of `NatDivides`). -/
def IntDivides (divisor value : Int) : Prop :=
  ∃ factor, value = divisor * factor

/-- Everything divides itself, via `intMulOne`. -/
theorem intDividesRefl (value : Int) : IntDivides value value :=
  ⟨1, (intMulOne value).symm⟩

/-- Everything divides zero, via `intMulZero`. -/
theorem intDividesZero (divisor : Int) : IntDivides divisor 0 :=
  ⟨0, (intMulZero divisor).symm⟩

/-! ## The `natAbs` sign bridges -/

/-- `Int.negOfNat` keeps its magnitude at `natAbs` — both constructor arms are `rfl`. -/
theorem natAbsNegOfNat : ∀ magnitude : Nat, (Int.negOfNat magnitude).natAbs = magnitude
  | 0 => rfl
  | _ + 1 => rfl

/-- `natAbs` is multiplicative over `Int` products: mixed-sign arms land on `Int.negOfNat`
(magnitude via `natAbsNegOfNat`), same-sign arms are `rfl`. -/
theorem intNatAbsMul : ∀ leftFactor rightFactor : Int,
    (leftFactor * rightFactor).natAbs = leftFactor.natAbs * rightFactor.natAbs
  | .ofNat _, .ofNat _ => rfl
  | .ofNat leftValue, .negSucc rightPredecessor =>
      natAbsNegOfNat (leftValue * (rightPredecessor + 1))
  | .negSucc leftPredecessor, .ofNat rightValue =>
      natAbsNegOfNat ((leftPredecessor + 1) * rightValue)
  | .negSucc _, .negSucc _ => rfl

/-- Rising bridge: magnitude divisibility by `commonDivisor` lifts to `Int` divisibility by
`Int.ofNat commonDivisor`; the `negSucc` value arm pulls the sign out through `intMulNeg`. -/
theorem intDividesOfNatDividesNatAbs {commonDivisor : Nat} {value : Int}
    (divides : NatDivides commonDivisor value.natAbs) :
    IntDivides (Int.ofNat commonDivisor) value :=
  match value, divides with
  | .ofNat _, ⟨quotient, valueEquation⟩ =>
      ⟨Int.ofNat quotient, congrArg Int.ofNat valueEquation⟩
  | .negSucc _, ⟨quotient, valueEquation⟩ =>
      ⟨-(Int.ofNat quotient),
        (congrArg (fun magnitude => -(Int.ofNat magnitude)) valueEquation).trans
          (intMulNeg (Int.ofNat commonDivisor) (Int.ofNat quotient)).symm⟩

/-- Falling bridge: `Int` divisibility descends to magnitude divisibility; the cofactor's
magnitude is the Nat cofactor, via `intNatAbsMul`. -/
theorem natDividesNatAbsOfIntDivides {divisor value : Int}
    (divides : IntDivides divisor value) :
    NatDivides divisor.natAbs value.natAbs :=
  match divides with
  | ⟨factor, valueEquation⟩ =>
      ⟨factor.natAbs,
        (congrArg Int.natAbs valueEquation).trans (intNatAbsMul divisor factor)⟩

/-- Sign normalisation of the divisor: divisibility by `Int.ofNat divisor.natAbs` upgrades to
divisibility by `divisor`; the `negSucc` arm flips the cofactor's sign. -/
theorem intDividesOfNatAbsDivides {divisor value : Int}
    (divides : IntDivides (Int.ofNat divisor.natAbs) value) : IntDivides divisor value :=
  match divisor, divides with
  | .ofNat _, witnessed => witnessed
  | .negSucc predecessor, ⟨factor, valueEquation⟩ =>
      ⟨-factor,
        ((intMulNeg (Int.negSucc predecessor) factor).trans
          ((intNegMul (Int.negSucc predecessor) factor).symm.trans
            ((congrArg (· * factor) (intNegNegOfNat (predecessor + 1))).trans
              valueEquation.symm))).symm⟩

/-! ## The signed gcd -/

/-- The integer gcd: the NONNEGATIVE representative `Int.ofNat (natGcd |a| |b|)`, the canonical
sign choice matching the Smith-normal-form diagonal. -/
def intGcd (leftValue rightValue : Int) : Int :=
  Int.ofNat (natGcd leftValue.natAbs rightValue.natAbs)

/-- The gcd is nonnegative — it is an `Int.ofNat`. -/
theorem intGcdIsNonnegative (leftValue rightValue : Int) :
    (0 : Int) ≤ intGcd leftValue rightValue :=
  intZeroLeOfNat (natGcd leftValue.natAbs rightValue.natAbs)

/-- The gcd divides its left argument, via the sign bridges. -/
theorem intGcdDividesLeft (leftValue rightValue : Int) :
    IntDivides (intGcd leftValue rightValue) leftValue :=
  intDividesOfNatAbsDivides
    (intDividesOfNatDividesNatAbs (natGcdDividesLeft leftValue.natAbs rightValue.natAbs))

/-- The gcd divides its right argument. -/
theorem intGcdDividesRight (leftValue rightValue : Int) :
    IntDivides (intGcd leftValue rightValue) rightValue :=
  intDividesOfNatAbsDivides
    (intDividesOfNatDividesNatAbs (natGcdDividesRight leftValue.natAbs rightValue.natAbs))

/-- Greatest-ness: every common divisor divides the gcd — descend both divisibilities to the
magnitudes, apply `natDividesGcdOfDividesBoth`, and rise back through the divisor sign bridge. -/
theorem intGcdGreatest {commonDivisor leftValue rightValue : Int}
    (dividesLeft : IntDivides commonDivisor leftValue)
    (dividesRight : IntDivides commonDivisor rightValue) :
    IntDivides commonDivisor (intGcd leftValue rightValue) :=
  intDividesOfNatAbsDivides
    (intDividesOfNatDividesNatAbs
      (natDividesGcdOfDividesBoth
        (natDividesNatAbsOfIntDivides dividesLeft)
        (natDividesNatAbsOfIntDivides dividesRight)))

/-- The gcd is commutative, lifting `natGcdComm` through `ofNat`. -/
theorem intGcdComm (leftValue rightValue : Int) :
    intGcd leftValue rightValue = intGcd rightValue leftValue :=
  congrArg Int.ofNat (natGcdComm leftValue.natAbs rightValue.natAbs)

end FX1Poly.ComputerAlgebra
