import FX1Poly.ComputerAlgebra.Number.IntSubNatNat
import FX1Poly.ComputerAlgebra.Number.IntAddAssociativity
import FX1Poly.ComputerAlgebra.Number.IntNegation

/-! # The clamped-gap cycle balance

Cross-alignment transitivity needs a single order-free identity over the clamped gaps
`(a - b).toNat`:

    A.toNat + B.toNat + C.toNat = (-A).toNat + (-B).toNat + (-C).toNat
                                                whenever A + B + C = 0,

because `ofNat (w.toNat) = ofNat ((-w).toNat) + w` for every Int `w` (the positive-part
decomposition, a two-case bash), so the two sides differ by the telescoping sum
`A + B + C`. Applied to the exponent-gap cycle `A = x - y`, `B = y - z`, `C = z - x`, this
lets the two cross-alignment equations be multiplied up to a common scale and cancelled,
with no `min` and no sign splits.

  * `intToNatOfNat` / `intToNatNegOfNat` — the `toNat` computation pins.
  * `intOfNatToNatDecomposition` — the positive-part decomposition.
  * `intAddSwapMiddle` — the four-term AC shuffle `(a+b)+(c+d) = (a+c)+(b+d)`.
  * `intGapCycleTelescopes` — the exponent-gap cycle sums to zero.
  * `intToNatCycleBalance` — the headline identity, by decomposing all three summands and
    shuffling the telescoping sum out.
  * `intSplitClampsBalance` — the two-exponent corollary the ℚ embedding of radix-scaled
    integers uses.

Two-case constructor bashes with `congrArg`/`Eq.trans` chains, free of `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, and `omega`; per-declaration gated
in the audit twin. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The toNat pins -/

/-- `toNat` computes on the `ofNat` constructor. -/
theorem intToNatOfNat (value : Nat) : (Int.ofNat value).toNat = value := rfl

/-- `toNat` of a negated `ofNat` is `0` — both arms definitional (`-(ofNat 0)` reduces
to `ofNat 0`, `-(ofNat (v+1))` reduces to `negSucc v`). -/
theorem intToNatNegOfNat : ∀ value : Nat, (-(Int.ofNat value)).toNat = 0
  | 0 => rfl
  | _ + 1 => rfl

/-! ## The positive-part decomposition -/

/-- **Positive-part decomposition**: `ofNat (w.toNat) = ofNat ((-w).toNat) + w` for
every Int — the nonnegative arm adds `0` on the left, the negative arm collapses to the
`subNatNat` diagonal. -/
theorem intOfNatToNatDecomposition : ∀ value : Int,
    Int.ofNat value.toNat = Int.ofNat (-value).toNat + value
  | .ofNat valueNat =>
      (intZeroAdd (Int.ofNat valueNat)).symm.trans
        (congrArg (· + Int.ofNat valueNat)
          (congrArg Int.ofNat (intToNatNegOfNat valueNat)).symm)
  | .negSucc valuePredecessor => (intSubNatNatSelf (valuePredecessor + 1)).symm

/-! ## AC plumbing -/

/-- The four-term exchange `(a + b) + (c + d) = (a + c) + (b + d)` — the only AC shuffle
the cycle balance needs. -/
theorem intAddSwapMiddle (firstLeft firstRight secondLeft secondRight : Int) :
    (firstLeft + firstRight) + (secondLeft + secondRight) =
      (firstLeft + secondLeft) + (firstRight + secondRight) :=
  (intAddAssoc firstLeft firstRight (secondLeft + secondRight)).trans
    ((congrArg (firstLeft + ·)
        ((intAddAssoc firstRight secondLeft secondRight).symm.trans
          ((congrArg (· + secondRight) (intAddComm firstRight secondLeft)).trans
            (intAddAssoc secondLeft firstRight secondRight)))).trans
      (intAddAssoc firstLeft secondLeft (firstRight + secondRight)).symm)

/-- The exponent-gap cycle telescopes to zero. -/
theorem intGapCycleTelescopes (firstValue secondValue thirdValue : Int) :
    (firstValue - secondValue) + (secondValue - thirdValue) +
      (thirdValue - firstValue) = 0 :=
  let firstPairCollapses :
      (firstValue + -secondValue) + (secondValue + -thirdValue) =
        firstValue + -thirdValue :=
    (intAddAssoc firstValue (-secondValue) (secondValue + -thirdValue)).trans
      ((congrArg (firstValue + ·)
          ((intAddAssoc (-secondValue) secondValue (-thirdValue)).symm.trans
            ((congrArg (· + -thirdValue) (intAddLeftNeg secondValue)).trans
              (intZeroAdd (-thirdValue))))))
  (congrArg (· + (thirdValue + -firstValue)) firstPairCollapses).trans
    ((intAddAssoc firstValue (-thirdValue) (thirdValue + -firstValue)).trans
      ((congrArg (firstValue + ·)
          ((intAddAssoc (-thirdValue) thirdValue (-firstValue)).symm.trans
            ((congrArg (· + -firstValue) (intAddLeftNeg thirdValue)).trans
              (intZeroAdd (-firstValue))))).trans
        (intAddRightNeg firstValue)))

/-! ## The cycle balance -/

/-- The clamped-gap cycle balance, the order-free identity behind cross-alignment
transitivity: over a telescoping cycle, the sum of positive parts equals the sum of
negative parts. Decompose all three summands by `intOfNatToNatDecomposition`, shuffle
with `intAddSwapMiddle`, and the telescoping sum drops out. -/
theorem intToNatCycleBalance {firstGap secondGap thirdGap : Int}
    (isTelescoping : firstGap + secondGap + thirdGap = 0) :
    firstGap.toNat + secondGap.toNat + thirdGap.toNat =
      (-firstGap).toNat + (-secondGap).toNat + (-thirdGap).toNat :=
  let negFirst := Int.ofNat (-firstGap).toNat
  let negSecond := Int.ofNat (-secondGap).toNat
  let negThird := Int.ofNat (-thirdGap).toNat
  Int.ofNat.inj
    (show Int.ofNat (firstGap.toNat + secondGap.toNat + thirdGap.toNat) =
        Int.ofNat ((-firstGap).toNat + (-secondGap).toNat + (-thirdGap).toNat) from
      (congrArg (fun replaced => (replaced + Int.ofNat secondGap.toNat) +
            Int.ofNat thirdGap.toNat)
          (intOfNatToNatDecomposition firstGap)).trans
        ((congrArg (fun replaced => ((negFirst + firstGap) + replaced) +
              Int.ofNat thirdGap.toNat)
            (intOfNatToNatDecomposition secondGap)).trans
          ((congrArg (((negFirst + firstGap) + (negSecond + secondGap)) + ·)
              (intOfNatToNatDecomposition thirdGap)).trans
            ((congrArg (· + (negThird + thirdGap))
                (intAddSwapMiddle negFirst firstGap negSecond secondGap)).trans
              ((intAddSwapMiddle (negFirst + negSecond) (firstGap + secondGap)
                  negThird thirdGap).trans
                ((congrArg (((negFirst + negSecond) + negThird) + ·)
                    isTelescoping).trans
                  (intAddZero ((negFirst + negSecond) + negThird))))))))

/-- The split-clamps balance, the two-exponent corollary the ℚ embedding of radix-scaled
integers uses: the gap clamp plus the other value's split clamps (`toNat` of each
exponent and of its negation) lands both cross-alignment sides on one total exponent.
Instantiate the cycle balance at the telescoping triple `(left - right, right, -left)`,
fold the double negation and the negated gap, and shuffle. -/
theorem intSplitClampsBalance (leftExponent rightExponent : Int) :
    (leftExponent - rightExponent).toNat +
        (rightExponent.toNat + (-leftExponent).toNat) =
      leftExponent.toNat + (-rightExponent).toNat +
        (rightExponent - leftExponent).toNat :=
  have isTelescoping :
      leftExponent - rightExponent + rightExponent + -leftExponent = 0 :=
    (congrArg (· + -leftExponent)
        ((intAddAssoc leftExponent (-rightExponent) rightExponent).trans
          ((congrArg (leftExponent + ·) (intAddLeftNeg rightExponent)).trans
            (intAddZero leftExponent)))).trans
      (intAddRightNeg leftExponent)
  have rawBalance :
      (leftExponent - rightExponent).toNat + rightExponent.toNat +
          (-leftExponent).toNat =
        (-(leftExponent - rightExponent)).toNat + (-rightExponent).toNat +
          (- -leftExponent).toNat :=
    intToNatCycleBalance isTelescoping
  have negationsFolded :
      (-(leftExponent - rightExponent)).toNat + (-rightExponent).toNat +
          (- -leftExponent).toNat =
        (rightExponent - leftExponent).toNat + (-rightExponent).toNat +
          leftExponent.toNat :=
    (congrArg
        (fun negatedGap =>
          negatedGap + (-rightExponent).toNat + (- -leftExponent).toNat)
        (congrArg Int.toNat (intNegSub leftExponent rightExponent))).trans
      (congrArg
        ((rightExponent - leftExponent).toNat + (-rightExponent).toNat + ·)
        (congrArg Int.toNat (intNegNeg leftExponent)))
  have shuffledToSplits :
      (rightExponent - leftExponent).toNat + (-rightExponent).toNat +
          leftExponent.toNat =
        leftExponent.toNat + (-rightExponent).toNat +
          (rightExponent - leftExponent).toNat :=
    (Nat.add_comm
        ((rightExponent - leftExponent).toNat + (-rightExponent).toNat)
        leftExponent.toNat).trans
      ((congrArg (leftExponent.toNat + ·)
          (Nat.add_comm (rightExponent - leftExponent).toNat
            (-rightExponent).toNat)).trans
        (Nat.add_assoc leftExponent.toNat (-rightExponent).toNat
          (rightExponent - leftExponent).toNat).symm)
  (Nat.add_assoc (leftExponent - rightExponent).toNat rightExponent.toNat
      (-leftExponent).toNat).symm.trans
    (rawBalance.trans (negationsFolded.trans shuffledToSplits))

end FX1Poly.ComputerAlgebra
