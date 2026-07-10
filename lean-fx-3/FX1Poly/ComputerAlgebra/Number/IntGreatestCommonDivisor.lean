import FX1Poly.ComputerAlgebra.Number.NatGreatestCommonDivisor
import FX1Poly.ComputerAlgebra.Number.IntNegation
import FX1Poly.ComputerAlgebra.Number.IntOrderAlgebra

/-! # FX1Poly/ComputerAlgebra/Number/IntGreatestCommonDivisor — the signed gcd (H2-SMITH r1, B1a)

The Smith-normal-form engine over ZZ (`ComputerAlgebra/LinearAlgebra/SmithNormalForm`) needs an
INTEGER greatest-common-divisor with witnessed properties: the pivot-selection cascade divides by
the gcd, and the invariant-factor chain `d1 | d2 | ...` is a chain of `IntDivides`.  Init's
`Int.gcd` and the whole `Int` divisibility corpus are propext-dirty on this toolchain, so this
brick lifts the shipped Nat kit (`NatGreatestCommonDivisor`) through `Int.natAbs` and reattaches
the sign, certificate-first.

  * `IntDivides divisor value := ∃ factor, value = divisor * factor` — the `Int` sibling of
    `NatDivides` (divisor on the LEFT), definitionally the same shape as `IntMatrix`'s
    layer-local `dividesExactly`, so the SNF divisibility chain plugs in without a coercion.
  * `intGcd a b := Int.ofNat (natGcd a.natAbs b.natAbs)` — canonicalised NONNEGATIVE (the ZZ gcd
    is unique only up to the unit `±1`; the nonnegative representative matches
    `IsSmithNormalFormWithin.diagonalIsNonnegative`).
  * The two sign bridges — `intDividesOfNatDividesNatAbs` (Nat magnitude divisibility rises to
    `Int`, per-constructor on the value's sign) and `natDividesNatAbsOfIntDivides` (the reverse,
    via `intNatAbsMul`) — carry `natGcdDividesLeft/Right` and `natDividesGcdOfDividesBoth` up to
    the signed `intGcdDividesLeft/Right` and `intGcdGreatest`.

The Bezout coefficient identity over `Int` (the disjunctive `NatBezoutIdentityFor` collapsed to a
single signed pair) and a decidable `IntDivides` instance are the r2 upgrade — this brick ships
the divides/greatest structure the SNF driver and its non-vacuity checks consume.

## Zero-axiom

Per-constructor `Int` matches, `congrArg`/`Eq.trans` over the propext-clean `Int` negation kit
(`intNegMul`, `intMulNeg`, `intNegNegOfNat`) and the shipped Nat gcd certificates.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`, no `WellFounded.fix`.
Per-declaration gated in `FX1PolyAudit/ComputerAlgebra/Number/IntGreatestCommonDivisor.lean`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Integer divisibility with explicit witnesses -/

/-- `divisor` divides `value` over the integers — explicit cofactor, divisor on the LEFT (the
`Int` sibling of `NatDivides`, matching the counting divider's reconstruction shape). -/
def IntDivides (divisor value : Int) : Prop :=
  ∃ factor, value = divisor * factor

/-- Everything divides itself — `value * 1` is `value` through `intMulOne`. -/
theorem intDividesRefl (value : Int) : IntDivides value value :=
  ⟨1, (intMulOne value).symm⟩

/-- Everything divides zero — `divisor * 0` reduces through `intMulZero`. -/
theorem intDividesZero (divisor : Int) : IntDivides divisor 0 :=
  ⟨0, (intMulZero divisor).symm⟩

/-! ## The `natAbs` sign bridges -/

/-- `Int.negOfNat` keeps its magnitude at `natAbs` — both constructor arms are `rfl`. -/
theorem natAbsNegOfNat : ∀ magnitude : Nat, (Int.negOfNat magnitude).natAbs = magnitude
  | 0 => rfl
  | _ + 1 => rfl

/-- `natAbs` is fully multiplicative over `Int` products — the mixed-sign arms land on
`Int.negOfNat`, whose magnitude is read off by `natAbsNegOfNat`; the same-sign arms are `rfl`. -/
theorem intNatAbsMul : ∀ leftFactor rightFactor : Int,
    (leftFactor * rightFactor).natAbs = leftFactor.natAbs * rightFactor.natAbs
  | .ofNat _, .ofNat _ => rfl
  | .ofNat leftValue, .negSucc rightPredecessor =>
      natAbsNegOfNat (leftValue * (rightPredecessor + 1))
  | .negSucc leftPredecessor, .ofNat rightValue =>
      natAbsNegOfNat ((leftPredecessor + 1) * rightValue)
  | .negSucc _, .negSucc _ => rfl

/-- **Rising bridge**: Nat divisibility of a value's magnitude by a magnitude `commonDivisor`
lifts to `Int` divisibility by `Int.ofNat commonDivisor`.  The `negSucc` value arm pulls the
sign out through `intMulNeg`. -/
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

/-- **Falling bridge**: `Int` divisibility descends to Nat divisibility of the magnitudes — the
cofactor's magnitude is the Nat cofactor, transported by `intNatAbsMul`. -/
theorem natDividesNatAbsOfIntDivides {divisor value : Int}
    (divides : IntDivides divisor value) :
    NatDivides divisor.natAbs value.natAbs :=
  match divides with
  | ⟨factor, valueEquation⟩ =>
      ⟨factor.natAbs,
        (congrArg Int.natAbs valueEquation).trans (intNatAbsMul divisor factor)⟩

/-- **Sign normalisation of the divisor**: divisibility by `Int.ofNat divisor.natAbs` upgrades to
divisibility by `divisor` itself — the `negSucc` arm flips the cofactor's sign through
`intMulNeg`/`intNegMul` (`-(negSucc m) = ofNat (m + 1)` by `intNegNegOfNat`). -/
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

/-- The greatest common divisor over the integers — the NONNEGATIVE representative
`Int.ofNat (natGcd |a| |b|)`.  Nonnegativity is the canonical sign choice matching the
Smith-normal-form diagonal. -/
def intGcd (leftValue rightValue : Int) : Int :=
  Int.ofNat (natGcd leftValue.natAbs rightValue.natAbs)

/-- The gcd is nonnegative — it is an `Int.ofNat`. -/
theorem intGcdIsNonnegative (leftValue rightValue : Int) :
    (0 : Int) ≤ intGcd leftValue rightValue :=
  intZeroLeOfNat (natGcd leftValue.natAbs rightValue.natAbs)

/-- The gcd divides its left argument — `natGcdDividesLeft` rises through the sign bridges. -/
theorem intGcdDividesLeft (leftValue rightValue : Int) :
    IntDivides (intGcd leftValue rightValue) leftValue :=
  intDividesOfNatAbsDivides
    (intDividesOfNatDividesNatAbs (natGcdDividesLeft leftValue.natAbs rightValue.natAbs))

/-- The gcd divides its right argument. -/
theorem intGcdDividesRight (leftValue rightValue : Int) :
    IntDivides (intGcd leftValue rightValue) rightValue :=
  intDividesOfNatAbsDivides
    (intDividesOfNatDividesNatAbs (natGcdDividesRight leftValue.natAbs rightValue.natAbs))

/-- **Greatest-ness**: every common divisor divides the gcd — descend both divisibilities to the
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

/-- The gcd is commutative — the underlying Nat gcd is (`natGcdComm`), lifted through `ofNat`. -/
theorem intGcdComm (leftValue rightValue : Int) :
    intGcd leftValue rightValue = intGcd rightValue leftValue :=
  congrArg Int.ofNat (natGcdComm leftValue.natAbs rightValue.natAbs)

end FX1Poly.ComputerAlgebra
