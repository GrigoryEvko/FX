import FX1Poly.ComputerAlgebra.Number.IntNegation
import FX1Poly.ComputerAlgebra.Number.IntOrderCore
import FX1Poly.ComputerAlgebra.Number.IntToNatCycle

/-! # Clamped gaps and the order

Order-aware arithmetic of the clamped gap `(a - b).toNat`, built on the additive-witness
order kit. Once an `intLessEqualDest` witness is in hand every clamped gap computes to a
literal `Nat`, so these identities are witness bookkeeping with no sign splits.

  * `intAddCancelLeft` — `(base + addend) - base = addend`, the witness extractor.
  * `intGapFloorSymm` — the clamped-gap floor `a - (a - b).toNat` is `min a b` written
    min-free, hence order-independent.
  * `intGapFloorLeMinuend` / `intGapFloorLeSubtrahend` — the floor sits below both
    operands, so it is a constructive common lower bound.
  * `intGapAdditionAcrossMiddle` — gaps add across an intermediate bound: `s ≤ t ≤ e`
    gives `(e - s).toNat = (e - t).toNat + (t - s).toNat`.
  * `intGapFloorAttainsLowerBound` — for `b ≤ a`, the floor equals `b`.
  * `intGapToNatEqZeroOfLe` — a backwards gap clamps to `0`.
  * `intPumpedGapsBalance` — below a common lower bound the cycle balance degenerates to
    `A.toNat + rightPump = (-A).toNat + leftPump`.

Additive-witness destruction with `congrArg`/`Eq.trans` chains, free of `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, and `omega`; per-declaration gated
in the audit twin. -/

namespace FX1Poly.ComputerAlgebra

/-- `(base + addend) - base = addend`: cancel the base under an addition, turning an
additive-witness equation into a computed gap. -/
theorem intAddCancelLeft (base addend : Int) : (base + addend) - base = addend :=
  (congrArg (· + -base) (intAddComm base addend)).trans
    ((intAddAssoc addend base (-base)).trans
      ((congrArg (addend + ·) (intAddRightNeg base)).trans (intAddZero addend)))

/-- The clamped-gap floor is symmetric: `a - (a - b).toNat` is `min a b` written
min-free, so it agrees with `b - (b - a).toNat`. Pins exact addition's exponent
independent of operand order. -/
theorem intGapFloorSymm (minuend subtrahend : Int) :
    minuend - Int.ofNat (minuend - subtrahend).toNat =
      subtrahend - Int.ofNat (subtrahend - minuend).toNat :=
  let clampedReverseGap := Int.ofNat (subtrahend - minuend).toNat
  have gapDecomposes :
      Int.ofNat (minuend - subtrahend).toNat =
        clampedReverseGap + (minuend - subtrahend) :=
    (intOfNatToNatDecomposition (minuend - subtrahend)).trans
      (congrArg (fun gapNat => Int.ofNat gapNat + (minuend - subtrahend))
        (congrArg Int.toNat (intNegSub minuend subtrahend)))
  have innerCollapse : minuend + (subtrahend - minuend) = subtrahend :=
    (congrArg (minuend + ·) (intAddComm subtrahend (-minuend))).trans
      ((intAddAssoc minuend (-minuend) subtrahend).symm.trans
        ((congrArg (· + subtrahend) (intAddRightNeg minuend)).trans
          (intZeroAdd subtrahend)))
  (congrArg (fun clampedGap => minuend + -clampedGap) gapDecomposes).trans
    ((congrArg (minuend + ·)
        (intNegAdd clampedReverseGap (minuend - subtrahend))).trans
      ((congrArg (fun negatedGap => minuend + (-clampedReverseGap + negatedGap))
          (intNegSub minuend subtrahend)).trans
        ((congrArg (minuend + ·)
            (intAddComm (-clampedReverseGap) (subtrahend - minuend))).trans
          ((intAddAssoc minuend (subtrahend - minuend) (-clampedReverseGap)).symm.trans
            (congrArg (· + -clampedReverseGap) innerCollapse)))))

/-- The clamped-gap floor sits below its base operand. -/
theorem intGapFloorLeMinuend (minuend subtrahend : Int) :
    minuend - Int.ofNat (minuend - subtrahend).toNat ≤ minuend :=
  intLessEqualOfEqRight
    (intLessEqualIntro (minuend - Int.ofNat (minuend - subtrahend).toNat)
      (minuend - subtrahend).toNat)
    ((intAddAssoc minuend (-(Int.ofNat (minuend - subtrahend).toNat))
        (Int.ofNat (minuend - subtrahend).toNat)).trans
      ((congrArg (minuend + ·)
          (intAddLeftNeg (Int.ofNat (minuend - subtrahend).toNat))).trans
        (intAddZero minuend)))

/-- The clamped-gap floor sits below the other operand too; with `intGapFloorLeMinuend`
this makes the floor a constructive common lower bound. -/
theorem intGapFloorLeSubtrahend (minuend subtrahend : Int) :
    minuend - Int.ofNat (minuend - subtrahend).toNat ≤ subtrahend :=
  intLessEqualOfEqLeft (intGapFloorSymm minuend subtrahend)
    (intGapFloorLeMinuend subtrahend minuend)

/-- Gaps add across an intermediate bound: for `s ≤ t ≤ e`,
`(e - s).toNat = (e - t).toNat + (t - s).toNat`. Both order hypotheses destruct to
additive witnesses, each clamped gap computes to its witness by `intAddCancelLeft`, and
the identity is `Nat.add_comm` on the witnesses. -/
theorem intGapAdditionAcrossMiddle {lowerBound middleBound upperBound : Int}
    (isAboveLower : lowerBound ≤ middleBound)
    (isBelowUpper : middleBound ≤ upperBound) :
    (upperBound - lowerBound).toNat =
      (upperBound - middleBound).toNat + (middleBound - lowerBound).toNat :=
  match intLessEqualDest isBelowUpper, intLessEqualDest isAboveLower with
  | ⟨upperWitness, upperEquation⟩, ⟨lowerWitness, lowerEquation⟩ =>
    have upperGapComputes : (upperBound - middleBound).toNat = upperWitness :=
      congrArg Int.toNat
        ((congrArg (· - middleBound) upperEquation).trans
          (intAddCancelLeft middleBound (Int.ofNat upperWitness)))
    have lowerGapComputes : (middleBound - lowerBound).toNat = lowerWitness :=
      congrArg Int.toNat
        ((congrArg (· - lowerBound) lowerEquation).trans
          (intAddCancelLeft lowerBound (Int.ofNat lowerWitness)))
    have fullGapComputes :
        (upperBound - lowerBound).toNat = lowerWitness + upperWitness :=
      congrArg Int.toNat
        ((congrArg (· - lowerBound)
            (upperEquation.trans
              ((congrArg (· + Int.ofNat upperWitness) lowerEquation).trans
                (intAddAssoc lowerBound (Int.ofNat lowerWitness)
                  (Int.ofNat upperWitness))))).trans
          (intAddCancelLeft lowerBound (Int.ofNat (lowerWitness + upperWitness))))
    fullGapComputes.trans
      ((Nat.add_comm lowerWitness upperWitness).trans
        ((congrArg (upperWitness + ·) lowerGapComputes).symm.trans
          (congrArg (· + (middleBound - lowerBound).toNat) upperGapComputes).symm))

/-- The clamped-gap floor attains an ordered lower bound: for `b ≤ a`, `a - (a - b).toNat`
is exactly `b`. Pins a rounding target as the result's exponent when the target sits
below. -/
theorem intGapFloorAttainsLowerBound {minuend subtrahend : Int}
    (isBelow : subtrahend ≤ minuend) :
    minuend - Int.ofNat (minuend - subtrahend).toNat = subtrahend :=
  match intLessEqualDest isBelow with
  | ⟨differenceWitness, witnessEquation⟩ =>
      (congrArg (fun gapValue => minuend - Int.ofNat gapValue.toNat)
          ((congrArg (· - subtrahend) witnessEquation).trans
            (intAddCancelLeft subtrahend (Int.ofNat differenceWitness)))).trans
        ((congrArg (· - Int.ofNat differenceWitness) witnessEquation).trans
          ((congrArg (· - Int.ofNat differenceWitness)
              (intAddComm subtrahend (Int.ofNat differenceWitness))).trans
            (intAddCancelLeft (Int.ofNat differenceWitness) subtrahend)))

/-- A backwards gap clamps to `0`: destruct the bound to a witness and the gap computes
to a negated `ofNat`, whose `toNat` is `0`. -/
theorem intGapToNatEqZeroOfLe {leftValue rightValue : Int}
    (isLessEqual : leftValue ≤ rightValue) :
    (leftValue - rightValue).toNat = 0 :=
  match intLessEqualDest isLessEqual with
  | ⟨differenceWitness, witnessEquation⟩ =>
    have gapIsNegated : leftValue - rightValue = -(Int.ofNat differenceWitness) :=
      (congrArg (leftValue - ·) witnessEquation).trans
        ((congrArg (leftValue + ·)
            (intNegAdd leftValue (Int.ofNat differenceWitness))).trans
          ((intAddAssoc leftValue (-leftValue)
              (-(Int.ofNat differenceWitness))).symm.trans
            ((congrArg (· + -(Int.ofNat differenceWitness))
                (intAddRightNeg leftValue)).trans
              (intZeroAdd (-(Int.ofNat differenceWitness))))))
    (congrArg Int.toNat gapIsNegated).trans (intToNatNegOfNat differenceWitness)

/-- The pumped exponents balance: for `lowerScale` below both bounds, the cycle balance
on the telescope `(l - r) + (r - t) + (t - l) = 0` degenerates — the two backwards clamps
vanish by `intGapToNatEqZeroOfLe`, leaving the identity that lands two cross-alignment
sides on one total exponent when both are pumped down to `lowerScale`. -/
theorem intPumpedGapsBalance {leftExponent rightExponent lowerScale : Int}
    (isBelowLeft : lowerScale ≤ leftExponent)
    (isBelowRight : lowerScale ≤ rightExponent) :
    (leftExponent - rightExponent).toNat + (rightExponent - lowerScale).toNat =
      (-(leftExponent - rightExponent)).toNat +
        (leftExponent - lowerScale).toNat :=
  have rawBalance :=
    intToNatCycleBalance (intGapCycleTelescopes leftExponent rightExponent lowerScale)
  have leftClampVanishes : (lowerScale - leftExponent).toNat = 0 :=
    intGapToNatEqZeroOfLe isBelowLeft
  have middleClampVanishes : (-(rightExponent - lowerScale)).toNat = 0 :=
    (congrArg Int.toNat (intNegSub rightExponent lowerScale)).trans
      (intGapToNatEqZeroOfLe isBelowRight)
  have lastGapFlips :
      (-(lowerScale - leftExponent)).toNat = (leftExponent - lowerScale).toNat :=
    congrArg Int.toNat (intNegSub lowerScale leftExponent)
  (congrArg ((leftExponent - rightExponent).toNat +
      (rightExponent - lowerScale).toNat + ·) leftClampVanishes).symm.trans
    (rawBalance.trans
      ((congrArg (fun middleClamp => (-(leftExponent - rightExponent)).toNat +
            middleClamp + (-(lowerScale - leftExponent)).toNat)
          middleClampVanishes).trans
        (congrArg ((-(leftExponent - rightExponent)).toNat + 0 + ·) lastGapFlips)))

end FX1Poly.ComputerAlgebra
