import FX1Poly.ComputerAlgebra.Number.IntNegation
import FX1Poly.ComputerAlgebra.Number.IntOrderCore
import FX1Poly.ComputerAlgebra.Number.IntToNatCycle

/-! # FX1Poly/ComputerAlgebra/Number/IntGapArithmetic — clamped gaps meet the order
    (FLOAT-2 brick 4e-i)

The cycle balance handles every ORDER-FREE clamped-gap identity, but the exact-addition
exponent is a genuine `min` (the clamped-gap floor), and pumping a cross-alignment
equation down to a common lower scale needs gap arithmetic BELOW a known bound.  This
module supplies exactly that, on the brick-7 additive-witness order kit — once an
`intLessEqualDest` witness is in hand, every clamped gap COMPUTES to a literal `Nat`
and the identities are witness bookkeeping, with no sign splits:

  * `intAddCancelLeft` — `(base + addend) - base = addend`, the witness extractor.
  * `intGapFloorSymm` — the clamped-gap floor `a - (a-b).toNat` IS `min a b` written
    min-free, so it is order-independent (promoted from the RadixScaledInteger carrier
    now that the floor order facts are its second consumer).
  * `intGapFloorLeMinuend` / `intGapFloorLeSubtrahend` — the floor sits below BOTH
    operands, making it a constructive common-lower-bound former.
  * `intGapAdditionAcrossMiddle` — gaps ADD across an intermediate bound:
    `s ≤ t ≤ e` gives `(e-s).toNat = (e-t).toNat + (t-s).toNat`, the pumping engine.

## Zero-axiom

Additive-witness destruction + `congrArg`/`Eq.trans` chains over the brick-1..7 kit.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/ComputerAlgebra/Number/IntGapArithmetic.lean`. -/

namespace FX1Poly.ComputerAlgebra

/-- `(base + addend) - base = addend` — cancel the base under an addition, the move
that turns an additive-witness equation into a computed gap. -/
theorem intAddCancelLeft (base addend : Int) : (base + addend) - base = addend :=
  (congrArg (· + -base) (intAddComm base addend)).trans
    ((intAddAssoc addend base (-base)).trans
      ((congrArg (addend + ·) (intAddRightNeg base)).trans (intAddZero addend)))

/-- **The clamped-gap floor is symmetric** — `a - (a-b).toNat` IS `min a b`, written
min-free, so it must agree with `b - (b-a).toNat`.  Decompose the clamped gap by
`intOfNatToNatDecomposition`, flip the inner difference by `intNegSub`, and the
telescoping `a + (b - a) = b` collapse finishes.  This pins exact addition's exponent
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

/-- The clamped-gap floor sits below its base operand — restore the base by adding the
clamped gap back (`intLessEqualIntro` + the add-inverse collapse). -/
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

/-- The clamped-gap floor sits below the OTHER operand too — flip the floor onto its
subtrahend presentation by `intGapFloorSymm` and reuse the base bound.  Together with
`intGapFloorLeMinuend` this makes the floor a constructive common lower bound. -/
theorem intGapFloorLeSubtrahend (minuend subtrahend : Int) :
    minuend - Int.ofNat (minuend - subtrahend).toNat ≤ subtrahend :=
  intLessEqualOfEqLeft (intGapFloorSymm minuend subtrahend)
    (intGapFloorLeMinuend subtrahend minuend)

/-- **Gaps add across an intermediate bound** — for `s ≤ t ≤ e`,
`(e-s).toNat = (e-t).toNat + (t-s).toNat`.  Both order hypotheses destruct to additive
witnesses, every clamped gap then COMPUTES to its witness by `intAddCancelLeft`, and
the identity is `Nat.add_comm` on the witnesses.  This is the engine that pumps a
cross-alignment equation down to any common lower scale. -/
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

end FX1Poly.ComputerAlgebra
