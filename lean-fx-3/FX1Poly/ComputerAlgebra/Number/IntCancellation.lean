import FX1Poly.ComputerAlgebra.Number.IntDistributivity
import FX1Poly.ComputerAlgebra.Number.IntNegation
import FX1Poly.ComputerAlgebra.Number.IntPower

/-! # FX1Poly/ComputerAlgebra/Number/IntCancellation — multiplicative cancellation
    (FLOAT-2 brick 3)

Cross-alignment transitivity (and every scaled-comparison argument after it) needs to
CANCEL a common positive scale factor: `a * s = b * s → a = b` for `0 < s`.  Init's
route is propext-dirty with the rest of the order corpus, so this module hand-rolls it
by the difference trick over the brick-4/6/7 kit:

    a * s = b * s  →  (a - b) * s = 0  →  a - b = 0  →  a = b

The middle step (`intEqZeroOfMulOfNatSuccEqZero`) destructs the positive scale to an
explicit successor carrier `ofNat (1 + w)`: an `ofNat` mantissa reduces to a Nat
zero-product fact, a `negSucc` mantissa makes the product a `negSucc` — refuted against
`0` by `noConfusion`.

  * `intMulRightCancel` / `intMulLeftCancel` — the general cancellation laws.
  * `intMulPowerRightCancel` — the consumer-facing form: cancel `radix ^ exponent` for
    a positive radix (via `intPowerPos`).
  * `natAddEqZeroRight` — the right-summand twin of brick-7's `natAddEqZeroLeft`.

## Zero-axiom

Constructor bash + `congrArg`/`Eq.trans` witness arithmetic over the brick-1..8 kit and
`intPower`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/Number/IntCancellation.lean`. -/

namespace FX1Poly.ComputerAlgebra

/-- A Nat sum vanishes only if its right summand does — the right-summand twin of
`natAddEqZeroLeft` (the zero arm is definitional, the successor arm is a `succ`
refuted by `noConfusion`). -/
theorem natAddEqZeroRight : ∀ {leftValue rightValue : Nat},
    leftValue + rightValue = 0 → rightValue = 0
  | _, 0, _ => rfl
  | _, _ + 1, sumEquation => Nat.noConfusion sumEquation

/-- A product with an explicit positive `ofNat` successor vanishes only if the other
factor does.  The `ofNat` arm reduces to a Nat zero-product (killed by
`natAddEqZeroRight` after one `Nat.add_comm` payload shuffle); the `negSucc` arm makes
the product a `negSucc`, refuted against `0`. -/
theorem intEqZeroOfMulOfNatSuccEqZero : ∀ (value : Int) (succPredecessor : Nat),
    value * Int.ofNat (1 + succPredecessor) = 0 → value = 0
  | .ofNat mantissaNat, succPredecessor, productEquation =>
      congrArg Int.ofNat
        (natAddEqZeroRight
          ((congrArg (mantissaNat * ·) (Nat.add_comm 1 succPredecessor)).symm.trans
            (Int.ofNat.inj productEquation)))
  | .negSucc mantissaPredecessor, succPredecessor, productEquation =>
      Int.noConfusion
        ((congrArg Int.negOfNat
            (congrArg ((mantissaPredecessor + 1) * ·)
              (Nat.add_comm 1 succPredecessor))).symm.trans productEquation)

/-- **Right cancellation** for a positive scale factor (Init's route is
propext-dirty).  The difference trick: equal products scale the difference to `0`,
which forces the difference to `0`. -/
theorem intMulRightCancel {leftFactor rightFactor scaleFactor : Int}
    (isScalePositive : (0 : Int) < scaleFactor)
    (productsAreEqual : leftFactor * scaleFactor = rightFactor * scaleFactor) :
    leftFactor = rightFactor :=
  match intLessEqualDest (show (0 : Int) + 1 ≤ scaleFactor from isScalePositive) with
  | ⟨scaleWitness, scaleEquation⟩ =>
      let scaleCarrier : scaleFactor = Int.ofNat (1 + scaleWitness) := scaleEquation
      let scaledDifferenceIsZero :
          (leftFactor + -rightFactor) * Int.ofNat (1 + scaleWitness) = 0 :=
        (congrArg ((leftFactor + -rightFactor) * ·) scaleCarrier).symm.trans
          ((intRightDistrib leftFactor (-rightFactor) scaleFactor).trans
            ((congrArg (leftFactor * scaleFactor + ·)
                (intNegMul rightFactor scaleFactor)).trans
              ((congrArg (· + -(rightFactor * scaleFactor)) productsAreEqual).trans
                (intAddRightNeg (rightFactor * scaleFactor)))))
      let differenceIsZero : leftFactor + -rightFactor = 0 :=
        intEqZeroOfMulOfNatSuccEqZero (leftFactor + -rightFactor) scaleWitness
          scaledDifferenceIsZero
      (intAddZero leftFactor).symm.trans
        ((congrArg (leftFactor + ·) (intAddLeftNeg rightFactor).symm).trans
          ((intAddAssoc leftFactor (-rightFactor) rightFactor).symm.trans
            ((congrArg (· + rightFactor) differenceIsZero).trans
              (intZeroAdd rightFactor))))

/-- **Left cancellation** — corollary through `intMulComm`. -/
theorem intMulLeftCancel {scaleFactor leftFactor rightFactor : Int}
    (isScalePositive : (0 : Int) < scaleFactor)
    (productsAreEqual : scaleFactor * leftFactor = scaleFactor * rightFactor) :
    leftFactor = rightFactor :=
  intMulRightCancel isScalePositive
    ((intMulComm leftFactor scaleFactor).trans
      (productsAreEqual.trans (intMulComm scaleFactor rightFactor)))

/-- The consumer-facing form: cancel a common `radix ^ exponent` scale for a positive
radix — the lemma cross-alignment transitivity runs on. -/
theorem intMulPowerRightCancel {radix leftFactor rightFactor : Int}
    (isRadixPositive : (0 : Int) < radix) (exponentValue : Nat)
    (productsAreEqual : leftFactor * intPower radix exponentValue =
      rightFactor * intPower radix exponentValue) :
    leftFactor = rightFactor :=
  intMulRightCancel (intPowerPos isRadixPositive exponentValue) productsAreEqual

/-! ## Order meets cancellation — monotone scaling and its reflection

The `≤`-shaped siblings of the cancellation laws: multiplying both sides of a bound by
a nonnegative factor preserves it, and a POSITIVE factor reflects it back.  Together
they let cross-alignment ORDER proofs ride the same scale-then-cancel playbook as the
cross-alignment equality proofs. -/

/-- **Multiplication by a nonnegative factor is monotone** — destruct both hypotheses
to additive witnesses; the scaled bound's witness is the `Nat` product (the closing
`ofNat * ofNat = ofNat (_ * _)` collapse is definitional). -/
theorem intMulLeMulRightOfNonNeg {lowValue highValue scaleFactor : Int}
    (isLessEqual : lowValue ≤ highValue)
    (isScaleNonNegative : (0 : Int) ≤ scaleFactor) :
    lowValue * scaleFactor ≤ highValue * scaleFactor :=
  match intLessEqualDest isLessEqual, intZeroLeDest isScaleNonNegative with
  | ⟨differenceWitness, differenceEquation⟩, ⟨scaleMagnitude, scaleEquation⟩ =>
      intLessEqualOfEqRight
        (intLessEqualIntro (lowValue * scaleFactor)
          (differenceWitness * scaleMagnitude))
        (Eq.symm
          ((congrArg (· * scaleFactor) differenceEquation).trans
            ((intRightDistrib lowValue (Int.ofNat differenceWitness)
                scaleFactor).trans
              (congrArg (lowValue * scaleFactor + ·)
                (congrArg (Int.ofNat differenceWitness * ·) scaleEquation)))))

/-- **Order reflection by a positive factor** — by totality: either the bound already
holds, or the reversed bound scales up (monotonicity), antisymmetry forces the scaled
products equal, and the positive factor cancels to an equality of the values. -/
theorem intLeOfMulLeMulRightOfPos {lowValue highValue scaleFactor : Int}
    (isScalePositive : (0 : Int) < scaleFactor)
    (areProductsOrdered : lowValue * scaleFactor ≤ highValue * scaleFactor) :
    lowValue ≤ highValue :=
  match intLessEqualTotal lowValue highValue with
  | .inl isAlreadyOrdered => isAlreadyOrdered
  | .inr isReversed =>
      intLessEqualOfEqRight (intLessEqualRefl lowValue)
        (intMulRightCancel isScalePositive
          (intLessEqualAntisymm areProductsOrdered
            (intMulLeMulRightOfNonNeg isReversed
              (intLessEqualOfLessThan isScalePositive))))

/-- **Negation is antitone** — the bound's additive witness survives the flip: with
`high = low + w`, the negated bound presents as `-low = -high + w` after
`intNegAdd` distributes and the witness cancels its own negation. -/
theorem intNegLeNegOfLe {lowValue highValue : Int}
    (isLessEqual : lowValue ≤ highValue) : -highValue ≤ -lowValue :=
  match intLessEqualDest isLessEqual with
  | ⟨differenceWitness, differenceEquation⟩ =>
      intLessEqualOfEqRight
        (intLessEqualIntro (-highValue) differenceWitness)
        ((congrArg
            (fun highCarrier => -highCarrier + Int.ofNat differenceWitness)
            differenceEquation).trans
          ((congrArg (· + Int.ofNat differenceWitness)
              (intNegAdd lowValue (Int.ofNat differenceWitness))).trans
            ((intAddAssoc (-lowValue) (-(Int.ofNat differenceWitness))
                (Int.ofNat differenceWitness)).trans
              ((congrArg (-lowValue + ·)
                  (intAddLeftNeg (Int.ofNat differenceWitness))).trans
                (intAddZero (-lowValue))))))

/-- **Strict negation antitonicity** — negate the weak bound at the shifted operand
and cancel the unit: from `low + 1 ≤ high`, negation gives `-high ≤ -(low + 1)`,
which re-adds its unit back to `-low`. -/
theorem intNegLtNegOfLt {lowValue highValue : Int}
    (isLessThan : lowValue < highValue) : -highValue < -lowValue :=
  intLessEqualOfEqRight
    (intAddLeAddRight (intNegLeNegOfLe isLessThan) 1)
    ((congrArg (· + 1) (intNegAdd lowValue 1)).trans
      ((intAddAssoc (-lowValue) (-1) 1).trans
        ((congrArg (-lowValue + ·) (intAddLeftNeg 1)).trans
          (intAddZero (-lowValue)))))

/-- **Left-scale monotonicity** — the mirror of `intMulLeMulRightOfNonNeg`
through commutativity on both endpoints. -/
theorem intMulLeMulLeftOfNonNeg {lowValue highValue : Int}
    (isLessEqual : lowValue ≤ highValue) {scaleFactor : Int}
    (isScaleNonNegative : (0 : Int) ≤ scaleFactor) :
    scaleFactor * lowValue ≤ scaleFactor * highValue :=
  intLessEqualOfEqLeft (intMulComm scaleFactor lowValue)
    (intLessEqualOfEqRight
      (intMulLeMulRightOfNonNeg isLessEqual isScaleNonNegative)
      (intMulComm highValue scaleFactor))

/-- **The two-sided product bound**: factors sitting below their magnitude
bounds multiply below the product of the bounds — `±a ≤ b` and `±c ≤ e` with
`0 ≤ e` give `a * c ≤ b * e`.  Constructor split on the left factor's sign:
a nonnegative left factor scales the right hypothesis directly; a negative
one rides `(-a') * c = a' * (-c)` (for `a'` its positive mirror) onto the two
mirrored hypotheses — no halving, no ring identity. -/
theorem intMulLeMulOfMagnitudeLe {leftValue leftBound rightValue rightBound : Int}
    (isLeftBelow : leftValue ≤ leftBound)
    (isNegLeftBelow : -leftValue ≤ leftBound)
    (isRightBelow : rightValue ≤ rightBound)
    (isNegRightBelow : -rightValue ≤ rightBound)
    (isRightBoundNonNegative : (0 : Int) ≤ rightBound) :
    leftValue * rightValue ≤ leftBound * rightBound :=
  match leftValue, isLeftBelow, isNegLeftBelow with
  | .ofNat magnitude, isOfNatBelow, _ =>
      intLessEqualTrans
        (intMulLeMulLeftOfNonNeg isRightBelow (intZeroLeOfNat magnitude))
        (intMulLeMulRightOfNonNeg isOfNatBelow isRightBoundNonNegative)
  | .negSucc magnitudePredecessor, _, isFlippedBelow =>
      have flipsToPositive :
          Int.negSucc magnitudePredecessor * rightValue =
            Int.ofNat (magnitudePredecessor + 1) * -rightValue :=
        (intNegMul (Int.ofNat (magnitudePredecessor + 1)) rightValue).trans
          (intMulNeg (Int.ofNat (magnitudePredecessor + 1)) rightValue).symm
      intLessEqualOfEqLeft flipsToPositive
        (intLessEqualTrans
          (intMulLeMulLeftOfNonNeg isNegRightBelow
            (intZeroLeOfNat (magnitudePredecessor + 1)))
          (intMulLeMulRightOfNonNeg
            (show Int.ofNat (magnitudePredecessor + 1) ≤ leftBound from
              isFlippedBelow)
            isRightBoundNonNegative))

/-! ## Strict square monotonicity — NODE 1 (constructive sqrt substrate, #1961)

The strict siblings of the monotone-scaling kit: a positive scale factor turns a
STRICT bound into a strict bound, and the resulting square-reflection law
(`0 ≤ B → A*A ≤ B*B → A ≤ B`) is the Int-level kernel the rational √-back step
consumes.  Both `<` legs ride the `a < b ≡ a + 1 ≤ b` defeq pin exactly as
`intMulPos`/`intLessThanOfLessThanOfLessEqual` do. -/

/-- **Right multiplication by a positive factor is strictly monotone** —
`a < b` and `0 < c` give `a*c < b*c`.  The scaled unit-step `(a+1)*c = a*c + c`
lifts the weak bound `(a+1)*c ≤ b*c` above the strict floor `a*c < a*c + c`
(the added `c` is positive). -/
theorem intMulLtMulRightOfPos {leftValue rightValue scaleFactor : Int}
    (isLessThan : leftValue < rightValue) (isScalePositive : (0 : Int) < scaleFactor) :
    leftValue * scaleFactor < rightValue * scaleFactor :=
  let distribEq :
      (leftValue + 1) * scaleFactor = leftValue * scaleFactor + scaleFactor :=
    (intRightDistrib leftValue 1 scaleFactor).trans
      (congrArg (leftValue * scaleFactor + ·) (intOneMul scaleFactor))
  let scaledStep :
      (leftValue + 1) * scaleFactor ≤ rightValue * scaleFactor :=
    intMulLeMulRightOfNonNeg (show leftValue + 1 ≤ rightValue from isLessThan)
      (intLessEqualOfLessThan isScalePositive)
  let acPlusCLeBc :
      leftValue * scaleFactor + scaleFactor ≤ rightValue * scaleFactor :=
    intLessEqualOfEqLeft distribEq.symm scaledStep
  let acLtAcPlusC :
      leftValue * scaleFactor < leftValue * scaleFactor + scaleFactor :=
    intLessThanOfEqLeft (intAddZero (leftValue * scaleFactor)).symm
      (intAddLessThanAddLeft isScalePositive (leftValue * scaleFactor))
  intLessThanOfLessThanOfLessEqual acLtAcPlusC acPlusCLeBc

/-- **Left multiplication by a positive factor is strictly monotone** — the
commutativity mirror of `intMulLtMulRightOfPos`. -/
theorem intMulLtMulLeftOfPos {leftValue rightValue scaleFactor : Int}
    (isLessThan : leftValue < rightValue) (isScalePositive : (0 : Int) < scaleFactor) :
    scaleFactor * leftValue < scaleFactor * rightValue :=
  intLessThanOfEqLeft (intMulComm scaleFactor leftValue)
    (intLessThanOfEqRight (intMulLtMulRightOfPos isLessThan isScalePositive)
      (intMulComm rightValue scaleFactor))

/-- **Square reflection** — from `0 ≤ B` and `A*A ≤ B*B`, conclude `A ≤ B`.
By totality: if `A ≤ B` already holds we are done; otherwise `B < A`, whence
`A` is positive, `B*B ≤ A*B < A*A` strictly, contradicting `A*A ≤ B*B`.  The
`0 ≤ A` hypothesis of the naive statement is unnecessary and omitted. -/
theorem intLeOfSqLeSqNonNeg {valueA valueB : Int}
    (isBNonNeg : (0 : Int) ≤ valueB)
    (areSquaresOrdered : valueA * valueA ≤ valueB * valueB) :
    valueA ≤ valueB :=
  match intLessEqualTotal valueA valueB with
  | .inl isOrdered => isOrdered
  | .inr isReversed =>
      match intLtOrEqOfLe isReversed with
      | .inr isEqual =>
          intLessEqualOfEqRight (intLessEqualRefl valueA) isEqual.symm
      | .inl isReversedStrict =>
          let isAPos : (0 : Int) < valueA :=
            intLessThanOfLessEqualOfLessThan isBNonNeg isReversedStrict
          let squareBLeAB : valueB * valueB ≤ valueA * valueB :=
            intMulLeMulRightOfNonNeg (intLessEqualOfLessThan isReversedStrict) isBNonNeg
          let abLtSquareA : valueA * valueB < valueA * valueA :=
            intMulLtMulLeftOfPos isReversedStrict isAPos
          let squareBLtSquareA : valueB * valueB < valueA * valueA :=
            intLessThanOfLessEqualOfLessThan squareBLeAB abLtSquareA
          absurd (intLessThanOfLessEqualOfLessThan areSquaresOrdered squareBLtSquareA)
            (intLessThanIrrefl (valueA * valueA))

end FX1Poly.ComputerAlgebra
