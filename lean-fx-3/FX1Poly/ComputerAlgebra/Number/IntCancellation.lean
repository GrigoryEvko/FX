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

end FX1Poly.ComputerAlgebra
