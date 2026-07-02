import FX1Poly.ComputerAlgebra.Number.IntNegation
import FX1Poly.ComputerAlgebra.Number.IntPower
import FX1Poly.ComputerAlgebra.Number.IntCancellation
import FX1Poly.ComputerAlgebra.Number.IntToNatCycle
import FX1Poly.ComputerAlgebra.Number.IntGapArithmetic
import FX1Poly.ComputerAlgebra.Number.IntExactDivision

/-! # FX1Poly/ComputerAlgebra/FloatingPoint/RadixScaledInteger — the carrier
    (FLOAT-2 brick 2)

The FLOAT-0 design lock: IEEE "infinitely precise then round" never needs the reals,
because every format value is `mantissa * radix ^ exponent` — a RadixScaledInteger.
Flocq evaluates this into `R` (negative exponents produce rationals); the R-free
packaging NEVER evaluates.  Value semantics is CROSS-ALIGNMENT:

    x ~ y  iff  x.mantissa * radix ^ (x.exponent - y.exponent).toNat
              = y.mantissa * radix ^ (y.exponent - x.exponent).toNat

One of the two gaps is always nonpositive, so its `toNat` is `0` and its power is `1` —
this is exactly "scale the larger exponent down to the smaller", with no `min`, no
negative powers, and decidability by `Int.decEq` on the aligned mantissas.

This file ships the structure, the cross-alignment relation (reflexive + symmetric +
decidable + transitive for a positive radix — `denotesSameAsTrans` runs on the
`intToNatCycleBalance` identity, with no sign-ordering case split, and cancels the
common scale via `intMulPowerRightCancel`), exact multiplication, exact addition at
the min-free common scale (mantissa = sum of the cross-aligned mantissas, exponent =
the clamped-gap floor; commutative as a strict record equality via `intGapFloorSymm`,
with the zero-summand identity law by collapse onto `shiftToLowerScale`, and congruence
via the pumping lemmas at the floor-of-floors common scale), and the first
semantic theorem:
`shiftToLowerScalePreservesDenotation` — rescaling a value to a lower exponent by
multiplying its mantissa with `radix ^ shift` denotes the same value.  Two generic Int
cancellation helpers (`intAddNegSwapCancel` / `intSubSubSelfCancel`) live here until a
second consumer promotes them to `Number/`; the `toNat` computation pins were promoted
to `Number/IntToNatCycle` and the clamped-gap floor lemma `intGapFloorSymm` to
`Number/IntGapArithmetic` when their second consumers arrived.

## Zero-axiom

Structure projections + `congrArg`/`Eq.trans` chains over the brick-1..8 kit and
`intPower`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/FloatingPoint/RadixScaledInteger.lean`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Int cancellation helpers -/

/-- `(base - subtracted) - base = -subtracted` — the left-gap collapse. -/
theorem intAddNegSwapCancel (base subtracted : Int) :
    (base + -subtracted) + -base = -subtracted :=
  (congrArg (· + -base) (intAddComm base (-subtracted))).trans
    ((intAddAssoc (-subtracted) base (-base)).trans
      ((congrArg (-subtracted + ·) (intAddRightNeg base)).trans
        (intAddZero (-subtracted))))

/-- `base - (base - subtracted) = subtracted` — the right-gap collapse. -/
theorem intSubSubSelfCancel (base subtracted : Int) :
    base - (base - subtracted) = subtracted :=
  (congrArg (base + ·)
      ((intNegAdd base (-subtracted)).trans
        (congrArg (-base + ·) (intNegNeg subtracted)))).trans
    ((intAddAssoc base (-base) subtracted).symm.trans
      ((congrArg (· + subtracted) (intAddRightNeg base)).trans
        (intZeroAdd subtracted)))

/-! ## The carrier -/

/-- A radix-scaled integer: the exact value `mantissa * radix ^ exponent`, never
evaluated — all semantics goes through cross-alignment. -/
structure RadixScaledInteger where
  mantissa : Int
  exponent : Int

namespace RadixScaledInteger

/-- The alignment gap from `value` down toward `other`'s scale — nonpositive gaps
clamp to `0`, which is what makes cross-alignment min-free. -/
def scaleGapToward (value other : RadixScaledInteger) : Nat :=
  (value.exponent - other.exponent).toNat

/-- `value`'s mantissa rescaled onto the common scale with `other`. -/
def crossAlignedMantissa (radix : Int) (value other : RadixScaledInteger) : Int :=
  value.mantissa * intPower radix (scaleGapToward value other)

/-- **Value equality by cross-alignment** — the R-free replacement for Flocq's `F2R`
evaluation: both mantissas rescaled onto the common scale must agree. -/
def DenotesSameAs (radix : Int) (leftValue rightValue : RadixScaledInteger) : Prop :=
  crossAlignedMantissa radix leftValue rightValue =
    crossAlignedMantissa radix rightValue leftValue

/-- Cross-alignment is decidable — it IS an `Int` equality (`Int.decEq` is clean). -/
def decideDenotesSameAs (radix : Int) (leftValue rightValue : RadixScaledInteger) :
    Decidable (DenotesSameAs radix leftValue rightValue) :=
  Int.decEq (crossAlignedMantissa radix leftValue rightValue)
    (crossAlignedMantissa radix rightValue leftValue)

/-- Reflexivity — the two aligned mantissas are the same term. -/
theorem denotesSameAsRefl (radix : Int) (value : RadixScaledInteger) :
    DenotesSameAs radix value value := rfl

/-- Symmetry — cross-alignment is symmetric by construction. -/
theorem denotesSameAsSymm {radix : Int} {leftValue rightValue : RadixScaledInteger}
    (areSame : DenotesSameAs radix leftValue rightValue) :
    DenotesSameAs radix rightValue leftValue := areSame.symm

/-- **Transitivity** — conditional on a positive radix, which powers the cancellation.
With the exponent-gap cycle `A = left - middle`, `B = middle - right`,
`C = right - left` (so `A + B + C = 0`), scale the first cross-alignment equation by
`radix ^ (B.toNat + C.toNat)` and the second by `radix ^ ((-A).toNat + C.toNat)`: both
land on the SAME total exponent, the middle mantissa cancels by transitivity of `Eq`,
and `intToNatCycleBalance` rewrites the outer exponents so that a common
`radix ^ ((-A).toNat + (-B).toNat)` factors out — `intMulPowerRightCancel` then leaves
exactly cross-alignment of `left` with `right`.  No sign-ordering case split, no
`min`. -/
theorem denotesSameAsTrans {radix : Int} (isRadixPositive : (0 : Int) < radix)
    {leftValue middleValue rightValue : RadixScaledInteger}
    (leftAgreesWithMiddle : DenotesSameAs radix leftValue middleValue)
    (middleAgreesWithRight : DenotesSameAs radix middleValue rightValue) :
    DenotesSameAs radix leftValue rightValue :=
  let gapLeftMiddle := (leftValue.exponent - middleValue.exponent).toNat
  let gapMiddleLeft := (-(leftValue.exponent - middleValue.exponent)).toNat
  let gapMiddleRight := (middleValue.exponent - rightValue.exponent).toNat
  let gapRightMiddle := (-(middleValue.exponent - rightValue.exponent)).toNat
  let gapRightLeft := (rightValue.exponent - leftValue.exponent).toNat
  let gapLeftRight := (-(rightValue.exponent - leftValue.exponent)).toNat
  let commonScale := gapMiddleLeft + gapRightMiddle
  have middleLeftGapFlips :
      (middleValue.exponent - leftValue.exponent).toNat = gapMiddleLeft :=
    congrArg Int.toNat (intNegSub leftValue.exponent middleValue.exponent).symm
  have rightMiddleGapFlips :
      (rightValue.exponent - middleValue.exponent).toNat = gapRightMiddle :=
    congrArg Int.toNat (intNegSub middleValue.exponent rightValue.exponent).symm
  have leftRightGapFlips :
      (leftValue.exponent - rightValue.exponent).toNat = gapLeftRight :=
    congrArg Int.toNat (intNegSub rightValue.exponent leftValue.exponent).symm
  have leftMiddleAtCycleGaps :
      leftValue.mantissa * intPower radix gapLeftMiddle =
        middleValue.mantissa * intPower radix gapMiddleLeft :=
    leftAgreesWithMiddle.trans
      (congrArg (fun gapValue => middleValue.mantissa * intPower radix gapValue)
        middleLeftGapFlips)
  have middleRightAtCycleGaps :
      middleValue.mantissa * intPower radix gapMiddleRight =
        rightValue.mantissa * intPower radix gapRightMiddle :=
    middleAgreesWithRight.trans
      (congrArg (fun gapValue => rightValue.mantissa * intPower radix gapValue)
        rightMiddleGapFlips)
  have cycleBalances :
      gapLeftMiddle + gapMiddleRight + gapRightLeft =
        gapMiddleLeft + gapRightMiddle + gapLeftRight :=
    intToNatCycleBalance
      (intGapCycleTelescopes leftValue.exponent middleValue.exponent
        rightValue.exponent)
  have leftTotalExponent :
      gapLeftMiddle + (gapMiddleRight + gapRightLeft) = gapLeftRight + commonScale :=
    (Nat.add_assoc gapLeftMiddle gapMiddleRight gapRightLeft).symm.trans
      (cycleBalances.trans (Nat.add_comm commonScale gapLeftRight))
  have middleTotalExponent :
      gapMiddleLeft + (gapMiddleRight + gapRightLeft) =
        gapMiddleRight + (gapMiddleLeft + gapRightLeft) :=
    (Nat.add_assoc gapMiddleLeft gapMiddleRight gapRightLeft).symm.trans
      ((congrArg (· + gapRightLeft) (Nat.add_comm gapMiddleLeft gapMiddleRight)).trans
        (Nat.add_assoc gapMiddleRight gapMiddleLeft gapRightLeft))
  have rightTotalExponent :
      gapRightMiddle + (gapMiddleLeft + gapRightLeft) = gapRightLeft + commonScale :=
    (Nat.add_assoc gapRightMiddle gapMiddleLeft gapRightLeft).symm.trans
      ((Nat.add_comm (gapRightMiddle + gapMiddleLeft) gapRightLeft).trans
        (congrArg (gapRightLeft + ·) (Nat.add_comm gapRightMiddle gapMiddleLeft)))
  have scaledChainAgrees :
      leftValue.mantissa * intPower radix gapLeftRight * intPower radix commonScale =
        rightValue.mantissa * intPower radix gapRightLeft *
          intPower radix commonScale :=
    (intMulPowerFold radix leftValue.mantissa gapLeftRight commonScale).trans
      ((congrArg (fun exponentValue => leftValue.mantissa * intPower radix exponentValue)
          leftTotalExponent.symm).trans
        ((intMulPowerFold radix leftValue.mantissa gapLeftMiddle
            (gapMiddleRight + gapRightLeft)).symm.trans
          ((congrArg (· * intPower radix (gapMiddleRight + gapRightLeft))
              leftMiddleAtCycleGaps).trans
            ((intMulPowerFold radix middleValue.mantissa gapMiddleLeft
                (gapMiddleRight + gapRightLeft)).trans
              ((congrArg
                  (fun exponentValue =>
                    middleValue.mantissa * intPower radix exponentValue)
                  middleTotalExponent).trans
                ((intMulPowerFold radix middleValue.mantissa gapMiddleRight
                    (gapMiddleLeft + gapRightLeft)).symm.trans
                  ((congrArg (· * intPower radix (gapMiddleLeft + gapRightLeft))
                      middleRightAtCycleGaps).trans
                    ((intMulPowerFold radix rightValue.mantissa gapRightMiddle
                        (gapMiddleLeft + gapRightLeft)).trans
                      ((congrArg
                          (fun exponentValue =>
                            rightValue.mantissa * intPower radix exponentValue)
                          rightTotalExponent).trans
                        (intMulPowerFold radix rightValue.mantissa gapRightLeft
                            commonScale).symm)))))))))
  have alignedWithoutCommonScale :
      leftValue.mantissa * intPower radix gapLeftRight =
        rightValue.mantissa * intPower radix gapRightLeft :=
    intMulPowerRightCancel isRadixPositive commonScale scaledChainAgrees
  (congrArg (fun gapValue => leftValue.mantissa * intPower radix gapValue)
      leftRightGapFlips).trans alignedWithoutCommonScale

/-- **Pumping down**: cross-aligned values agree at EVERY common lower scale, not just
at the clamped-gap floor — multiply the cross-alignment equation by the missing pump
power; `intPumpedGapsBalance` lands both sides on one total exponent and the common
`radix ^ (-gap).toNat` factor cancels. -/
theorem agreesAtLowerScaleOfDenotesSame {radix : Int}
    (isRadixPositive : (0 : Int) < radix)
    {leftValue rightValue : RadixScaledInteger} {lowerScale : Int}
    (isBelowLeft : lowerScale ≤ leftValue.exponent)
    (isBelowRight : lowerScale ≤ rightValue.exponent)
    (areSame : DenotesSameAs radix leftValue rightValue) :
    leftValue.mantissa * intPower radix (leftValue.exponent - lowerScale).toNat =
      rightValue.mantissa *
        intPower radix (rightValue.exponent - lowerScale).toNat :=
  let alignGap := leftValue.exponent - rightValue.exponent
  let negatedGapNat := (-alignGap).toNat
  let leftPumpNat := (leftValue.exponent - lowerScale).toNat
  let rightPumpNat := (rightValue.exponent - lowerScale).toNat
  have areSameAtCycleGaps :
      leftValue.mantissa * intPower radix alignGap.toNat =
        rightValue.mantissa * intPower radix negatedGapNat :=
    areSame.trans
      (congrArg (fun gapValue => rightValue.mantissa * intPower radix gapValue)
        (congrArg Int.toNat
          (intNegSub leftValue.exponent rightValue.exponent).symm))
  have exponentsBalance :
      alignGap.toNat + rightPumpNat = negatedGapNat + leftPumpNat :=
    intPumpedGapsBalance isBelowLeft isBelowRight
  have scaledAgreement :
      leftValue.mantissa * intPower radix leftPumpNat *
          intPower radix negatedGapNat =
        rightValue.mantissa * intPower radix rightPumpNat *
          intPower radix negatedGapNat :=
    (intMulPowerFold radix leftValue.mantissa leftPumpNat negatedGapNat).trans
      ((congrArg (fun exponentValue => leftValue.mantissa * intPower radix exponentValue)
          (Nat.add_comm leftPumpNat negatedGapNat)).trans
        ((congrArg
            (fun exponentValue => leftValue.mantissa * intPower radix exponentValue)
            exponentsBalance.symm).trans
          ((intMulPowerFold radix leftValue.mantissa alignGap.toNat
              rightPumpNat).symm.trans
            ((congrArg (· * intPower radix rightPumpNat) areSameAtCycleGaps).trans
              ((intMulPowerFold radix rightValue.mantissa negatedGapNat
                  rightPumpNat).trans
                ((congrArg
                    (fun exponentValue =>
                      rightValue.mantissa * intPower radix exponentValue)
                    (Nat.add_comm negatedGapNat rightPumpNat)).trans
                  (intMulPowerFold radix rightValue.mantissa rightPumpNat
                      negatedGapNat).symm))))))
  intMulPowerRightCancel isRadixPositive negatedGapNat scaledAgreement

/-- **Pumping up**: agreement at ANY single common lower scale already forces
cross-alignment — the same balance identity run in the other direction, cancelling the
common pump power instead. -/
theorem denotesSameAsOfAgreesAtLowerScale {radix : Int}
    (isRadixPositive : (0 : Int) < radix)
    {leftValue rightValue : RadixScaledInteger} {lowerScale : Int}
    (isBelowLeft : lowerScale ≤ leftValue.exponent)
    (isBelowRight : lowerScale ≤ rightValue.exponent)
    (agreesAtLowerScale :
      leftValue.mantissa * intPower radix (leftValue.exponent - lowerScale).toNat =
        rightValue.mantissa *
          intPower radix (rightValue.exponent - lowerScale).toNat) :
    DenotesSameAs radix leftValue rightValue :=
  let alignGap := leftValue.exponent - rightValue.exponent
  let negatedGapNat := (-alignGap).toNat
  let leftPumpNat := (leftValue.exponent - lowerScale).toNat
  let rightPumpNat := (rightValue.exponent - lowerScale).toNat
  have exponentsBalance :
      alignGap.toNat + rightPumpNat = negatedGapNat + leftPumpNat :=
    intPumpedGapsBalance isBelowLeft isBelowRight
  have scaledAgreement :
      leftValue.mantissa * intPower radix alignGap.toNat *
          intPower radix rightPumpNat =
        rightValue.mantissa * intPower radix negatedGapNat *
          intPower radix rightPumpNat :=
    (intMulPowerFold radix leftValue.mantissa alignGap.toNat rightPumpNat).trans
      ((congrArg (fun exponentValue => leftValue.mantissa * intPower radix exponentValue)
          exponentsBalance).trans
        ((congrArg
            (fun exponentValue => leftValue.mantissa * intPower radix exponentValue)
            (Nat.add_comm negatedGapNat leftPumpNat)).trans
          ((intMulPowerFold radix leftValue.mantissa leftPumpNat
              negatedGapNat).symm.trans
            ((congrArg (· * intPower radix negatedGapNat) agreesAtLowerScale).trans
              ((intMulPowerFold radix rightValue.mantissa rightPumpNat
                  negatedGapNat).trans
                ((congrArg
                    (fun exponentValue =>
                      rightValue.mantissa * intPower radix exponentValue)
                    (Nat.add_comm rightPumpNat negatedGapNat)).trans
                  (intMulPowerFold radix rightValue.mantissa negatedGapNat
                      rightPumpNat).symm))))))
  have atCycleGaps :
      leftValue.mantissa * intPower radix alignGap.toNat =
        rightValue.mantissa * intPower radix negatedGapNat :=
    intMulPowerRightCancel isRadixPositive rightPumpNat scaledAgreement
  atCycleGaps.trans
    (congrArg (fun gapValue => rightValue.mantissa * intPower radix gapValue)
      (congrArg Int.toNat (intNegSub leftValue.exponent rightValue.exponent)))

/-! ## Exact multiplication -/

/-- Exact multiplication — mantissas multiply, exponents add.  No rounding, no value
loss: this is the "infinitely precise" half of every IEEE operation. -/
def mulExact (leftFactor rightFactor : RadixScaledInteger) : RadixScaledInteger :=
  { mantissa := leftFactor.mantissa * rightFactor.mantissa
    exponent := leftFactor.exponent + rightFactor.exponent }

/-- The mantissa equation of exact multiplication, definitional. -/
theorem mulExactMantissa (leftFactor rightFactor : RadixScaledInteger) :
    (mulExact leftFactor rightFactor).mantissa =
      leftFactor.mantissa * rightFactor.mantissa := rfl

/-- The exponent equation of exact multiplication, definitional. -/
theorem mulExactExponent (leftFactor rightFactor : RadixScaledInteger) :
    (mulExact leftFactor rightFactor).exponent =
      leftFactor.exponent + rightFactor.exponent := rfl

/-- **Exact multiplication is commutative as a strict record equality** — the mantissa
product commutes and the exponent sum commutes; no cross-alignment reasoning needed. -/
theorem mulExactComm (leftFactor rightFactor : RadixScaledInteger) :
    mulExact leftFactor rightFactor = mulExact rightFactor leftFactor :=
  (congrArg
      (fun productMantissa => RadixScaledInteger.mk productMantissa
        (leftFactor.exponent + rightFactor.exponent))
      (intMulComm leftFactor.mantissa rightFactor.mantissa)).trans
    (congrArg
      (RadixScaledInteger.mk (rightFactor.mantissa * leftFactor.mantissa))
      (intAddComm leftFactor.exponent rightFactor.exponent))

/-- **Exact multiplication respects cross-alignment** — congruence of `mulExact` for a
positive radix.  With operand gaps `A` and `B`, the product gap splits as `A + B`
(`intAddSwapMiddle` on the exponent sums), the two hypotheses multiply into ONE
equation at exponent `A.toNat + B.toNat` (`intMulSwapMiddle` + `intPowerAdd`), and the
exponent identity that lets the common `radix ^ ((-A).toNat + (-B).toNat)` cancel out
is `intToNatCycleBalance` at the TRIVIAL cycle `A + B + -(A + B) = 0` — no new balance
identity, no sign split. -/
theorem mulExactRespectsDenotesSameAs {radix : Int}
    (isRadixPositive : (0 : Int) < radix)
    {leftFactor otherLeftFactor rightFactor otherRightFactor : RadixScaledInteger}
    (leftFactorsAgree : DenotesSameAs radix leftFactor otherLeftFactor)
    (rightFactorsAgree : DenotesSameAs radix rightFactor otherRightFactor) :
    DenotesSameAs radix (mulExact leftFactor rightFactor)
      (mulExact otherLeftFactor otherRightFactor) :=
  let leftGap := leftFactor.exponent - otherLeftFactor.exponent
  let rightGap := rightFactor.exponent - otherRightFactor.exponent
  let productGap := leftGap + rightGap
  let forwardGapNat := productGap.toNat
  let backwardGapNat := (-productGap).toNat
  let commonScale := (-leftGap).toNat + (-rightGap).toNat
  let leftMantissaProduct := leftFactor.mantissa * rightFactor.mantissa
  let rightMantissaProduct := otherLeftFactor.mantissa * otherRightFactor.mantissa
  have leftAtCycleGaps :
      leftFactor.mantissa * intPower radix leftGap.toNat =
        otherLeftFactor.mantissa * intPower radix (-leftGap).toNat :=
    leftFactorsAgree.trans
      (congrArg (fun gapValue => otherLeftFactor.mantissa * intPower radix gapValue)
        (congrArg Int.toNat
          (intNegSub leftFactor.exponent otherLeftFactor.exponent).symm))
  have rightAtCycleGaps :
      rightFactor.mantissa * intPower radix rightGap.toNat =
        otherRightFactor.mantissa * intPower radix (-rightGap).toNat :=
    rightFactorsAgree.trans
      (congrArg (fun gapValue => otherRightFactor.mantissa * intPower radix gapValue)
        (congrArg Int.toNat
          (intNegSub rightFactor.exponent otherRightFactor.exponent).symm))
  have combinedAtSummedGaps :
      leftMantissaProduct * intPower radix (leftGap.toNat + rightGap.toNat) =
        rightMantissaProduct * intPower radix commonScale :=
    (Eq.symm
        ((intMulSwapMiddle leftFactor.mantissa (intPower radix leftGap.toNat)
            rightFactor.mantissa (intPower radix rightGap.toNat)).trans
          (congrArg (leftMantissaProduct * ·)
            (intPowerAdd radix leftGap.toNat rightGap.toNat).symm))).trans
      ((congrArg (· * (rightFactor.mantissa * intPower radix rightGap.toNat))
          leftAtCycleGaps).trans
        ((congrArg ((otherLeftFactor.mantissa * intPower radix (-leftGap).toNat) * ·)
            rightAtCycleGaps).trans
          ((intMulSwapMiddle otherLeftFactor.mantissa
              (intPower radix (-leftGap).toNat) otherRightFactor.mantissa
              (intPower radix (-rightGap).toNat)).trans
            (congrArg (rightMantissaProduct * ·)
              (intPowerAdd radix (-leftGap).toNat (-rightGap).toNat).symm))))
  have balanceAtTrivialCycle :
      leftGap.toNat + rightGap.toNat + backwardGapNat =
        (-leftGap).toNat + (-rightGap).toNat + forwardGapNat :=
    (intToNatCycleBalance (firstGap := leftGap) (secondGap := rightGap)
        (thirdGap := -productGap) (intAddRightNeg productGap)).trans
      (congrArg (((-leftGap).toNat + (-rightGap).toNat) + ·)
        (congrArg Int.toNat (intNegNeg productGap)))
  have scaledCombined :
      leftMantissaProduct * intPower radix forwardGapNat *
          intPower radix commonScale =
        rightMantissaProduct * intPower radix backwardGapNat *
          intPower radix commonScale :=
    (intMulPowerFold radix leftMantissaProduct forwardGapNat commonScale).trans
      ((congrArg (fun exponentValue => leftMantissaProduct * intPower radix exponentValue)
          (Nat.add_comm forwardGapNat commonScale)).trans
        ((congrArg
            (fun exponentValue => leftMantissaProduct * intPower radix exponentValue)
            balanceAtTrivialCycle.symm).trans
          ((intMulPowerFold radix leftMantissaProduct
              (leftGap.toNat + rightGap.toNat) backwardGapNat).symm.trans
            ((congrArg (· * intPower radix backwardGapNat) combinedAtSummedGaps).trans
              ((intMulPowerFold radix rightMantissaProduct commonScale
                  backwardGapNat).trans
                ((congrArg
                    (fun exponentValue =>
                      rightMantissaProduct * intPower radix exponentValue)
                    (Nat.add_comm commonScale backwardGapNat)).trans
                  (intMulPowerFold radix rightMantissaProduct backwardGapNat
                      commonScale).symm))))))
  have cancelledAtCycleGaps :
      leftMantissaProduct * intPower radix forwardGapNat =
        rightMantissaProduct * intPower radix backwardGapNat :=
    intMulPowerRightCancel isRadixPositive commonScale scaledCombined
  have productGapSplits :
      (leftFactor.exponent + rightFactor.exponent) -
          (otherLeftFactor.exponent + otherRightFactor.exponent) = productGap :=
    (congrArg ((leftFactor.exponent + rightFactor.exponent) + ·)
        (intNegAdd otherLeftFactor.exponent otherRightFactor.exponent)).trans
      (intAddSwapMiddle leftFactor.exponent rightFactor.exponent
        (-otherLeftFactor.exponent) (-otherRightFactor.exponent))
  have reverseProductGapCollapses :
      (otherLeftFactor.exponent + otherRightFactor.exponent) -
          (leftFactor.exponent + rightFactor.exponent) = -productGap :=
    (intNegSub (leftFactor.exponent + rightFactor.exponent)
        (otherLeftFactor.exponent + otherRightFactor.exponent)).symm.trans
      (congrArg Int.neg productGapSplits)
  (congrArg (fun gapValue => leftMantissaProduct * intPower radix gapValue)
      (congrArg Int.toNat productGapSplits)).trans
    (cancelledAtCycleGaps.trans
      (congrArg (fun gapValue => rightMantissaProduct * intPower radix gapValue)
        (congrArg Int.toNat reverseProductGapCollapses)).symm)

/-! ## Rescaling preserves the denoted value -/

/-- Rescale to a LOWER exponent: multiply the mantissa by `radix ^ shiftAmount`, drop
the exponent by the same amount.  This is the alignment move every add/compare makes. -/
def shiftToLowerScale (radix : Int) (value : RadixScaledInteger) (shiftAmount : Nat) :
    RadixScaledInteger :=
  { mantissa := value.mantissa * intPower radix shiftAmount
    exponent := value.exponent - Int.ofNat shiftAmount }

/-- **Rescaling is value-preserving** — the first semantic theorem of the carrier.
The shifted side's gap collapses to `0` (its power to `1`), the original side's gap
collapses to `shiftAmount`; both aligned mantissas become
`mantissa * radix ^ shiftAmount`. -/
theorem shiftToLowerScalePreservesDenotation (radix : Int) (value : RadixScaledInteger)
    (shiftAmount : Nat) :
    DenotesSameAs radix (shiftToLowerScale radix value shiftAmount) value :=
  let shiftedGapIsZero :
      scaleGapToward (shiftToLowerScale radix value shiftAmount) value = 0 :=
    (congrArg Int.toNat
        (intAddNegSwapCancel value.exponent (Int.ofNat shiftAmount))).trans
      (intToNatNegOfNat shiftAmount)
  let originalGapIsShift :
      scaleGapToward value (shiftToLowerScale radix value shiftAmount) = shiftAmount :=
    congrArg Int.toNat (intSubSubSelfCancel value.exponent (Int.ofNat shiftAmount))
  ((congrArg
        (fun gapValue =>
          (value.mantissa * intPower radix shiftAmount) * intPower radix gapValue)
        shiftedGapIsZero).trans
      (intMulOne (value.mantissa * intPower radix shiftAmount))).trans
    (congrArg (fun gapValue => value.mantissa * intPower radix gapValue)
      originalGapIsShift).symm

/-! ## Exact addition -/

/-- Exact addition at the min-free common scale: the mantissa is the sum of the two
CROSS-ALIGNED mantissas (both already sit at the common lower scale), the exponent is
the clamped-gap floor `left.exponent - gap` — which IS `min` of the two exponents,
written without `min` (`intGapFloorSymm` shows it is order-independent).  No rounding,
no value loss: the "infinitely precise" half of IEEE addition. -/
def addExact (radix : Int) (leftSummand rightSummand : RadixScaledInteger) :
    RadixScaledInteger :=
  { mantissa := crossAlignedMantissa radix leftSummand rightSummand +
      crossAlignedMantissa radix rightSummand leftSummand
    exponent := leftSummand.exponent -
      Int.ofNat (scaleGapToward leftSummand rightSummand) }

/-- The mantissa equation of exact addition, definitional. -/
theorem addExactMantissa (radix : Int) (leftSummand rightSummand : RadixScaledInteger) :
    (addExact radix leftSummand rightSummand).mantissa =
      crossAlignedMantissa radix leftSummand rightSummand +
        crossAlignedMantissa radix rightSummand leftSummand := rfl

/-- The exponent equation of exact addition, definitional. -/
theorem addExactExponent (radix : Int) (leftSummand rightSummand : RadixScaledInteger) :
    (addExact radix leftSummand rightSummand).exponent =
      leftSummand.exponent -
        Int.ofNat (scaleGapToward leftSummand rightSummand) := rfl

/-- **Exact addition is commutative as a strict record equality** — the mantissa sum
commutes and the two floor presentations agree by `intGapFloorSymm`; no cross-alignment
reasoning needed. -/
theorem addExactComm (radix : Int) (leftSummand rightSummand : RadixScaledInteger) :
    addExact radix leftSummand rightSummand =
      addExact radix rightSummand leftSummand :=
  (congrArg
      (fun summedMantissa => RadixScaledInteger.mk summedMantissa
        (leftSummand.exponent -
          Int.ofNat (scaleGapToward leftSummand rightSummand)))
      (intAddComm (crossAlignedMantissa radix leftSummand rightSummand)
        (crossAlignedMantissa radix rightSummand leftSummand))).trans
    (congrArg
      (RadixScaledInteger.mk (crossAlignedMantissa radix rightSummand leftSummand +
        crossAlignedMantissa radix leftSummand rightSummand))
      (intGapFloorSymm leftSummand.exponent rightSummand.exponent))

/-- **Adding a zero-mantissa value denotes the same value** — the zero side's aligned
mantissa vanishes, and what remains IS `shiftToLowerScale` of the original value, so
`shiftToLowerScalePreservesDenotation` closes it.  The identity-element law of exact
addition, for ANY exponent on the zero. -/
theorem addExactZeroDenotesSame (radix : Int) (value : RadixScaledInteger)
    (zeroExponent : Int) :
    DenotesSameAs radix
      (addExact radix value { mantissa := 0, exponent := zeroExponent }) value :=
  let zeroSummand : RadixScaledInteger := { mantissa := 0, exponent := zeroExponent }
  let alignmentGap := scaleGapToward value zeroSummand
  have zeroSideVanishes : crossAlignedMantissa radix zeroSummand value = 0 :=
    intZeroMul (intPower radix (scaleGapToward zeroSummand value))
  have summedMantissaCollapses :
      crossAlignedMantissa radix value zeroSummand +
          crossAlignedMantissa radix zeroSummand value =
        crossAlignedMantissa radix value zeroSummand :=
    (congrArg (crossAlignedMantissa radix value zeroSummand + ·)
        zeroSideVanishes).trans
      (intAddZero (crossAlignedMantissa radix value zeroSummand))
  have collapsesToShift :
      addExact radix value zeroSummand = shiftToLowerScale radix value alignmentGap :=
    congrArg
      (fun summedMantissa => RadixScaledInteger.mk summedMantissa
        (value.exponent - Int.ofNat alignmentGap))
      summedMantissaCollapses
  (congrArg (fun summedValue => crossAlignedMantissa radix summedValue value)
      collapsesToShift).trans
    ((shiftToLowerScalePreservesDenotation radix value alignmentGap).trans
      (congrArg (fun summedValue => crossAlignedMantissa radix value summedValue)
        collapsesToShift.symm))

/-- **The exact sum evaluated below its floor** — at ANY scale below the clamped-gap
floor, the sum's pumped mantissa is the sum of the operands' pumped mantissas:
distribute the pump power over the mantissa sum (`intRightDistrib`), fold each
summand's alignment gap onto the pump (`intMulPowerFold`), and
`intGapAdditionAcrossMiddle` recombines gap-to-floor plus floor-to-scale into
gap-to-scale — the floor-to-operand gaps COMPUTE by `intSubSubSelfCancel` (the right
operand's through `intGapFloorSymm` first). -/
theorem addExactMantissaAtLowerScale (radix : Int)
    (leftSummand rightSummand : RadixScaledInteger) {lowerScale : Int}
    (isBelowFloor : lowerScale ≤ (addExact radix leftSummand rightSummand).exponent) :
    (addExact radix leftSummand rightSummand).mantissa *
        intPower radix
          ((addExact radix leftSummand rightSummand).exponent - lowerScale).toNat =
      leftSummand.mantissa *
          intPower radix (leftSummand.exponent - lowerScale).toNat +
        rightSummand.mantissa *
          intPower radix (rightSummand.exponent - lowerScale).toNat :=
  let leftGapNat := scaleGapToward leftSummand rightSummand
  let rightGapNat := scaleGapToward rightSummand leftSummand
  let floorExponent := leftSummand.exponent - Int.ofNat leftGapNat
  let pumpNat := (floorExponent - lowerScale).toNat
  have leftFloorGapComputes :
      (leftSummand.exponent - floorExponent).toNat = (Int.ofNat leftGapNat).toNat :=
    congrArg Int.toNat
      (intSubSubSelfCancel leftSummand.exponent (Int.ofNat leftGapNat))
  have rightFloorGapComputes :
      (rightSummand.exponent - floorExponent).toNat = (Int.ofNat rightGapNat).toNat :=
    (congrArg (fun floorValue => (rightSummand.exponent - floorValue).toNat)
        (intGapFloorSymm leftSummand.exponent rightSummand.exponent)).trans
      (congrArg Int.toNat
        (intSubSubSelfCancel rightSummand.exponent (Int.ofNat rightGapNat)))
  have leftExponentTotal :
      leftGapNat + pumpNat = (leftSummand.exponent - lowerScale).toNat :=
    (congrArg (· + pumpNat) leftFloorGapComputes).symm.trans
      (intGapAdditionAcrossMiddle isBelowFloor
        (intGapFloorLeMinuend leftSummand.exponent rightSummand.exponent)).symm
  have rightExponentTotal :
      rightGapNat + pumpNat = (rightSummand.exponent - lowerScale).toNat :=
    (congrArg (· + pumpNat) rightFloorGapComputes).symm.trans
      (intGapAdditionAcrossMiddle isBelowFloor
        (intGapFloorLeSubtrahend leftSummand.exponent rightSummand.exponent)).symm
  (intRightDistrib (leftSummand.mantissa * intPower radix leftGapNat)
      (rightSummand.mantissa * intPower radix rightGapNat)
      (intPower radix pumpNat)).trans
    ((congrArg
        (· + rightSummand.mantissa * intPower radix rightGapNat *
          intPower radix pumpNat)
        ((intMulPowerFold radix leftSummand.mantissa leftGapNat pumpNat).trans
          (congrArg
            (fun exponentValue => leftSummand.mantissa * intPower radix exponentValue)
            leftExponentTotal))).trans
      (congrArg
        (leftSummand.mantissa *
            intPower radix (leftSummand.exponent - lowerScale).toNat + ·)
        ((intMulPowerFold radix rightSummand.mantissa rightGapNat pumpNat).trans
          (congrArg
            (fun exponentValue => rightSummand.mantissa * intPower radix exponentValue)
            rightExponentTotal))))

/-- **Exact addition respects cross-alignment** — congruence of `addExact` for a
positive radix.  Pick the common scale = the clamped-gap floor of the two sums' floors
(it sits below all four operand exponents by chaining the floor bounds through
`intLessEqualTrans`), pump both hypotheses down to it
(`agreesAtLowerScaleOfDenotesSame`), add them, recognize each side as the
corresponding sum's mantissa pumped to that scale (`addExactMantissaAtLowerScale`),
and pump back up (`denotesSameAsOfAgreesAtLowerScale`).  With
`mulExactRespectsDenotesSameAs` this makes exact arithmetic well-defined on
cross-alignment classes. -/
theorem addExactRespectsDenotesSameAs {radix : Int}
    (isRadixPositive : (0 : Int) < radix)
    {leftSummand otherLeftSummand rightSummand otherRightSummand : RadixScaledInteger}
    (leftSummandsAgree : DenotesSameAs radix leftSummand otherLeftSummand)
    (rightSummandsAgree : DenotesSameAs radix rightSummand otherRightSummand) :
    DenotesSameAs radix (addExact radix leftSummand rightSummand)
      (addExact radix otherLeftSummand otherRightSummand) :=
  let firstSum := addExact radix leftSummand rightSummand
  let secondSum := addExact radix otherLeftSummand otherRightSummand
  let commonScale := firstSum.exponent -
    Int.ofNat (firstSum.exponent - secondSum.exponent).toNat
  have isBelowFirstFloor : commonScale ≤ firstSum.exponent :=
    intGapFloorLeMinuend firstSum.exponent secondSum.exponent
  have isBelowSecondFloor : commonScale ≤ secondSum.exponent :=
    intGapFloorLeSubtrahend firstSum.exponent secondSum.exponent
  have isBelowLeft : commonScale ≤ leftSummand.exponent :=
    intLessEqualTrans isBelowFirstFloor
      (intGapFloorLeMinuend leftSummand.exponent rightSummand.exponent)
  have isBelowRight : commonScale ≤ rightSummand.exponent :=
    intLessEqualTrans isBelowFirstFloor
      (intGapFloorLeSubtrahend leftSummand.exponent rightSummand.exponent)
  have isBelowOtherLeft : commonScale ≤ otherLeftSummand.exponent :=
    intLessEqualTrans isBelowSecondFloor
      (intGapFloorLeMinuend otherLeftSummand.exponent otherRightSummand.exponent)
  have isBelowOtherRight : commonScale ≤ otherRightSummand.exponent :=
    intLessEqualTrans isBelowSecondFloor
      (intGapFloorLeSubtrahend otherLeftSummand.exponent otherRightSummand.exponent)
  have summandsAgreePumped :
      leftSummand.mantissa *
            intPower radix (leftSummand.exponent - commonScale).toNat +
          rightSummand.mantissa *
            intPower radix (rightSummand.exponent - commonScale).toNat =
        otherLeftSummand.mantissa *
            intPower radix (otherLeftSummand.exponent - commonScale).toNat +
          otherRightSummand.mantissa *
            intPower radix (otherRightSummand.exponent - commonScale).toNat :=
    (congrArg
        (· + rightSummand.mantissa *
          intPower radix (rightSummand.exponent - commonScale).toNat)
        (agreesAtLowerScaleOfDenotesSame isRadixPositive isBelowLeft
          isBelowOtherLeft leftSummandsAgree)).trans
      (congrArg
        (otherLeftSummand.mantissa *
          intPower radix (otherLeftSummand.exponent - commonScale).toNat + ·)
        (agreesAtLowerScaleOfDenotesSame isRadixPositive isBelowRight
          isBelowOtherRight rightSummandsAgree))
  denotesSameAsOfAgreesAtLowerScale isRadixPositive isBelowFirstFloor
    isBelowSecondFloor
    ((addExactMantissaAtLowerScale radix leftSummand rightSummand
        isBelowFirstFloor).trans
      (summandsAgreePumped.trans
        (addExactMantissaAtLowerScale radix otherLeftSummand otherRightSummand
          isBelowSecondFloor).symm))

/-! ## Radix normalization -/

/-- The fuel-bounded normalization loop: while the mantissa's magnitude divides
exactly by the radix, divide it out and raise the exponent.  Structural on the fuel
`Nat` (never `WellFounded.fix`); the `cond`-exposed Bool scrutinee keeps the
correctness proofs to `congrArg` transport.  Reaching the normal form under
`natAbs`-sized fuel is the next brick's theorem, not this definition's claim. -/
def normalizeWithFuel (radix : Int) : Nat → RadixScaledInteger → RadixScaledInteger
  | 0, value => value
  | fuelRemaining + 1, value =>
      cond ((intMagnitudeRemainder radix.toNat value.mantissa).beq 0)
        (normalizeWithFuel radix fuelRemaining
          { mantissa := intMagnitudeQuotient radix.toNat value.mantissa
            exponent := value.exponent + 1 })
        value

/-- **One division step preserves the denoted value**: with the exact factorization
`value.mantissa = quotient * radix` in hand, the rescaled `⟨quotient, exponent + 1⟩`
IS `value` after one `shiftToLowerScale` by `1`, so
`shiftToLowerScalePreservesDenotation` closes it — the division loop is
`shiftToLowerScale` run backwards. -/
theorem divideMantissaStepPreservesDenotation {radix : Int}
    (isRadixPositive : (0 : Int) < radix) (value : RadixScaledInteger)
    (hasZeroRemainder : intMagnitudeRemainder radix.toNat value.mantissa = 0) :
    DenotesSameAs radix
      { mantissa := intMagnitudeQuotient radix.toNat value.mantissa
        exponent := value.exponent + 1 } value :=
  let rescaledValue : RadixScaledInteger :=
    { mantissa := intMagnitudeQuotient radix.toNat value.mantissa
      exponent := value.exponent + 1 }
  have mantissaFactors :
      value.mantissa = rescaledValue.mantissa * Int.ofNat radix.toNat :=
    intMagnitudeDivisionExact radix.toNat value.mantissa hasZeroRemainder
  have radixMagnitudeRestores : Int.ofNat radix.toNat = radix :=
    intOfNatToNatOfNonNeg (intLessEqualOfLessThan isRadixPositive)
  have mantissaCollapses :
      rescaledValue.mantissa * intPower radix 1 = value.mantissa :=
    (congrArg (rescaledValue.mantissa * ·) (intOneMul radix)).trans
      ((congrArg (rescaledValue.mantissa * ·) radixMagnitudeRestores.symm).trans
        mantissaFactors.symm)
  have exponentCollapses :
      rescaledValue.exponent - Int.ofNat 1 = value.exponent :=
    (intAddAssoc value.exponent 1 (-1)).trans
      ((congrArg (value.exponent + ·) (intAddRightNeg 1)).trans
        (intAddZero value.exponent))
  have shiftedCollapsesToOriginal :
      shiftToLowerScale radix rescaledValue 1 = value :=
    (congrArg
        (fun mantissaValue => RadixScaledInteger.mk mantissaValue
          (rescaledValue.exponent - Int.ofNat 1))
        mantissaCollapses).trans
      (congrArg (RadixScaledInteger.mk value.mantissa) exponentCollapses)
  (congrArg (fun otherValue => crossAlignedMantissa radix rescaledValue otherValue)
      shiftedCollapsesToOriginal.symm).trans
    ((shiftToLowerScalePreservesDenotation radix rescaledValue 1).symm.trans
      (congrArg
        (fun shiftedValue => crossAlignedMantissa radix shiftedValue rescaledValue)
        shiftedCollapsesToOriginal))

/-- **Normalization preserves the denoted value** — the loop is a fuel-bounded chain
of value-preserving division steps, closed under `denotesSameAsTrans`; both `cond`
arms are transported by `congrArg` over the Bool equation. -/
theorem normalizeWithFuelPreservesDenotation {radix : Int}
    (isRadixPositive : (0 : Int) < radix) :
    ∀ (fuel : Nat) (value : RadixScaledInteger),
      DenotesSameAs radix (normalizeWithFuel radix fuel value) value
  | 0, value => denotesSameAsRefl radix value
  | fuelRemaining + 1, value =>
    match beqEquation : (intMagnitudeRemainder radix.toNat value.mantissa).beq 0 with
    | true =>
        let rescaledValue : RadixScaledInteger :=
          { mantissa := intMagnitudeQuotient radix.toNat value.mantissa
            exponent := value.exponent + 1 }
        have loopRecurses :
            normalizeWithFuel radix (fuelRemaining + 1) value =
              normalizeWithFuel radix fuelRemaining rescaledValue :=
          congrArg
            (fun conditionBool => cond conditionBool
              (normalizeWithFuel radix fuelRemaining rescaledValue) value)
            beqEquation
        have tailPreserves :
            DenotesSameAs radix
              (normalizeWithFuel radix fuelRemaining rescaledValue) value :=
          denotesSameAsTrans isRadixPositive
            (normalizeWithFuelPreservesDenotation isRadixPositive fuelRemaining
              rescaledValue)
            (divideMantissaStepPreservesDenotation isRadixPositive value
              (Nat.eq_of_beq_eq_true beqEquation))
        (congrArg
            (fun normalizedValue => crossAlignedMantissa radix normalizedValue value)
            loopRecurses).trans
          (tailPreserves.trans
            (congrArg
              (fun normalizedValue => crossAlignedMantissa radix value normalizedValue)
              loopRecurses).symm)
    | false =>
        have loopStops : normalizeWithFuel radix (fuelRemaining + 1) value = value :=
          congrArg
            (fun conditionBool => cond conditionBool
              (normalizeWithFuel radix fuelRemaining
                { mantissa := intMagnitudeQuotient radix.toNat value.mantissa
                  exponent := value.exponent + 1 })
              value)
            beqEquation
        (congrArg
            (fun normalizedValue => crossAlignedMantissa radix normalizedValue value)
            loopStops).trans
          (congrArg
            (fun normalizedValue => crossAlignedMantissa radix value normalizedValue)
            loopStops).symm

/-- A value is NORMALIZED when no further exact division by the radix is possible:
either the mantissa is zero (nothing left to divide), or its magnitude leaves a
nonzero remainder.  Operational by construction, so decidability is plain
`Int`/`Nat` equality. -/
def IsNormalized (radix : Int) (value : RadixScaledInteger) : Prop :=
  value.mantissa = 0 ∨ intMagnitudeRemainder radix.toNat value.mantissa ≠ 0

/-- Normalization status is decidable — two computable equality tests. -/
def decideIsNormalized (radix : Int) (value : RadixScaledInteger) :
    Decidable (IsNormalized radix value) :=
  match Int.decEq value.mantissa 0 with
  | isTrue hasZeroMantissa => isTrue (Or.inl hasZeroMantissa)
  | isFalse hasNonzeroMantissa =>
      match Nat.decEq (intMagnitudeRemainder radix.toNat value.mantissa) 0 with
      | isTrue hasZeroRemainder =>
          isFalse (fun isNormalized =>
            match isNormalized with
            | Or.inl hasZeroMantissa => hasNonzeroMantissa hasZeroMantissa
            | Or.inr hasNonzeroRemainder => hasNonzeroRemainder hasZeroRemainder)
      | isFalse hasNonzeroRemainder => isTrue (Or.inr hasNonzeroRemainder)

/-- **The fuel bound is sufficient**: for a radix above `1`, `natAbs`-many divisions
always reach a normal form.  Fuel `0` forces a zero mantissa
(`natEqZeroOfLeZero` + `intEqZeroOfNatAbsEqZero`); a stopping step IS the nonzero
remainder; a dividing step shrinks the magnitude strictly
(`natExactQuotientWithinFuel` through the `natAbs` bridges), so the induction
hypothesis applies at the smaller fuel. -/
theorem normalizeWithFuelReachesNormalForm {radix : Int}
    (isRadixAboveOne : (1 : Int) < radix) :
    ∀ (fuel : Nat) (value : RadixScaledInteger),
      value.mantissa.natAbs ≤ fuel →
      IsNormalized radix (normalizeWithFuel radix fuel value)
  | 0, value, isWithinFuel =>
      Or.inl (intEqZeroOfNatAbsEqZero (natEqZeroOfLeZero isWithinFuel))
  | fuelRemaining + 1, value, isWithinFuel =>
    match beqEquation : (intMagnitudeRemainder radix.toNat value.mantissa).beq 0 with
    | true =>
        let rescaledValue : RadixScaledInteger :=
          { mantissa := intMagnitudeQuotient radix.toNat value.mantissa
            exponent := value.exponent + 1 }
        have loopRecurses :
            normalizeWithFuel radix (fuelRemaining + 1) value =
              normalizeWithFuel radix fuelRemaining rescaledValue :=
          congrArg
            (fun conditionBool => cond conditionBool
              (normalizeWithFuel radix fuelRemaining rescaledValue) value)
            beqEquation
        have countingRemainderVanishes :
            (natDivModCounting value.mantissa.natAbs radix.toNat).snd = 0 :=
          (intMagnitudeRemainderAsCounting radix.toNat value.mantissa).symm.trans
            (Nat.eq_of_beq_eq_true beqEquation)
        have magnitudeFactors :
            value.mantissa.natAbs =
              radix.toNat * rescaledValue.mantissa.natAbs :=
          (natDivModCountingReconstructs value.mantissa.natAbs radix.toNat).trans
            ((congrArg
                (radix.toNat *
                  (natDivModCounting value.mantissa.natAbs radix.toNat).fst + ·)
                countingRemainderVanishes).trans
              (congrArg (radix.toNat * ·)
                (intMagnitudeQuotientNatAbs radix.toNat value.mantissa).symm))
        have rescaledWithinFuel :
            rescaledValue.mantissa.natAbs ≤ fuelRemaining :=
          natExactQuotientWithinFuel
            (intToNatAtLeastTwoOfOneLessThan isRadixAboveOne) isWithinFuel
            rescaledValue.mantissa.natAbs magnitudeFactors
        Eq.rec
          (motive := fun normalizedValue _ => IsNormalized radix normalizedValue)
          (normalizeWithFuelReachesNormalForm isRadixAboveOne fuelRemaining
            rescaledValue rescaledWithinFuel)
          loopRecurses.symm
    | false =>
        have loopStops :
            normalizeWithFuel radix (fuelRemaining + 1) value = value :=
          congrArg
            (fun conditionBool => cond conditionBool
              (normalizeWithFuel radix fuelRemaining
                { mantissa := intMagnitudeQuotient radix.toNat value.mantissa
                  exponent := value.exponent + 1 })
              value)
            beqEquation
        Eq.rec
          (motive := fun normalizedValue _ => IsNormalized radix normalizedValue)
          (Or.inr (Nat.ne_of_beq_eq_false beqEquation))
          loopStops.symm

/-- **Every value has a normalized representative** — the FLOAT-2 capstone: run the
loop with `natAbs`-sized fuel; it reaches a normal form and preserves the denoted
value.  With decidable cross-alignment and decidable normalization status, this is
the constructive representability package. -/
theorem normalizedRepresentativeExists {radix : Int}
    (isRadixAboveOne : (1 : Int) < radix) (value : RadixScaledInteger) :
    ∃ normalizedValue : RadixScaledInteger,
      IsNormalized radix normalizedValue ∧
        DenotesSameAs radix normalizedValue value :=
  have isRadixPositive : (0 : Int) < radix :=
    intLessEqualOfLessThan isRadixAboveOne
  ⟨normalizeWithFuel radix value.mantissa.natAbs value,
    normalizeWithFuelReachesNormalForm isRadixAboveOne value.mantissa.natAbs value
      Nat.le.refl,
    normalizeWithFuelPreservesDenotation isRadixPositive value.mantissa.natAbs
      value⟩

/-! ## Rounding — toward zero (FLOAT-3)

The rounding architecture: every mode rescales the value to the target exponent and
corrects the magnitude-division quotient — toward-zero takes the quotient as-is,
the directed modes bump it by one on a nonzero remainder against the sign, and
nearest compares the doubled remainder against the divisor.  Toward zero is the
base mode the corrections build on. -/

/-- **Round toward zero to a target exponent** — min-free by the clamped-gap
pattern: the ALIGNMENT gap `(exponent - target).toNat` scales the mantissa up when
the target sits below the value's exponent (exact, no information loss), and the
DIVISION gap `(target - exponent).toNat` divides it down when the target sits above
(the magnitude quotient IS truncation toward zero).  Away from the diagonal exactly
one gap is nonzero; on it both vanish and the division is by `radix ^ 0 = 1`. -/
def roundTowardZero (radix : Int) (value : RadixScaledInteger)
    (targetExponent : Int) : RadixScaledInteger :=
  { mantissa := intMagnitudeQuotient
      (intPower radix (targetExponent - value.exponent).toNat).toNat
      (value.mantissa * intPower radix (value.exponent - targetExponent).toNat)
    exponent := targetExponent }

/-- The mantissa equation of toward-zero rounding, definitional. -/
theorem roundTowardZeroMantissa (radix : Int) (value : RadixScaledInteger)
    (targetExponent : Int) :
    (roundTowardZero radix value targetExponent).mantissa =
      intMagnitudeQuotient
        (intPower radix (targetExponent - value.exponent).toNat).toNat
        (value.mantissa *
          intPower radix (value.exponent - targetExponent).toNat) := rfl

/-- The exponent equation of toward-zero rounding, definitional — the result always
sits at the requested scale. -/
theorem roundTowardZeroExponent (radix : Int) (value : RadixScaledInteger)
    (targetExponent : Int) :
    (roundTowardZero radix value targetExponent).exponent = targetExponent := rfl

/-- **Toward-zero rounding is EXACT at or below the exponent**: when the target
scale sits at or below the value's exponent, rounding IS `shiftToLowerScale` — the
division gap clamps to zero (`intGapToNatEqZeroOfLe`), division by `radix ^ 0 = 1`
is the identity (`intMagnitudeQuotientByOne`), and the target is the clamped-gap
floor (`intGapFloorAttainsLowerBound`).  Unconditional in the radix. -/
theorem roundTowardZeroPreservesDenotationOfTargetBelow (radix : Int)
    {value : RadixScaledInteger} {targetExponent : Int}
    (isTargetBelow : targetExponent ≤ value.exponent) :
    DenotesSameAs radix (roundTowardZero radix value targetExponent) value :=
  let alignmentGapNat := (value.exponent - targetExponent).toNat
  have divisionGapVanishes : (targetExponent - value.exponent).toNat = 0 :=
    intGapToNatEqZeroOfLe isTargetBelow
  have mantissaCollapses :
      (roundTowardZero radix value targetExponent).mantissa =
        value.mantissa * intPower radix alignmentGapNat :=
    (congrArg
        (fun gapNat => intMagnitudeQuotient (intPower radix gapNat).toNat
          (value.mantissa * intPower radix alignmentGapNat))
        divisionGapVanishes).trans
      (intMagnitudeQuotientByOne
        (value.mantissa * intPower radix alignmentGapNat))
  have roundCollapsesToShift :
      roundTowardZero radix value targetExponent =
        shiftToLowerScale radix value alignmentGapNat :=
    (congrArg
        (fun mantissaValue => RadixScaledInteger.mk mantissaValue targetExponent)
        mantissaCollapses).trans
      (congrArg
        (RadixScaledInteger.mk (value.mantissa * intPower radix alignmentGapNat))
        (intGapFloorAttainsLowerBound isTargetBelow).symm)
  Eq.rec
    (motive := fun roundedValue _ => DenotesSameAs radix roundedValue value)
    (shiftToLowerScalePreservesDenotation radix value alignmentGapNat)
    roundCollapsesToShift.symm

/-- **The toward-zero magnitude decomposition** — the exact error certificate's
skeleton.  The pumped mantissa (the value re-expressed at the clamped common scale
with the target) splits as the rounded mantissa's magnitude times the scale divisor
plus the counting divider's remainder: `roundTowardZero` drops EXACTLY that
remainder, nothing else.  Unconditional in the radix and the target — the divider
certificates carry all the content. -/
theorem roundTowardZeroMagnitudeDecomposition (radix : Int)
    (value : RadixScaledInteger) (targetExponent : Int) :
    (value.mantissa *
        intPower radix (value.exponent - targetExponent).toNat).natAbs =
      (roundTowardZero radix value targetExponent).mantissa.natAbs *
          (intPower radix (targetExponent - value.exponent).toNat).toNat +
        intMagnitudeRemainder
          (intPower radix (targetExponent - value.exponent).toNat).toNat
          (value.mantissa *
            intPower radix (value.exponent - targetExponent).toNat) :=
  let scaleDivisor := (intPower radix (targetExponent - value.exponent).toNat).toNat
  let pumpedMantissa :=
    value.mantissa * intPower radix (value.exponent - targetExponent).toNat
  (natDivModCountingReconstructs pumpedMantissa.natAbs scaleDivisor).trans
    ((congrArg (· + (natDivModCounting pumpedMantissa.natAbs scaleDivisor).snd)
        (Nat.mul_comm scaleDivisor
          (natDivModCounting pumpedMantissa.natAbs scaleDivisor).fst)).trans
      ((congrArg
          (fun quotientMagnitude => quotientMagnitude * scaleDivisor +
            (natDivModCounting pumpedMantissa.natAbs scaleDivisor).snd)
          (intMagnitudeQuotientNatAbs scaleDivisor pumpedMantissa).symm).trans
        (congrArg
          ((roundTowardZero radix value targetExponent).mantissa.natAbs *
              scaleDivisor + ·)
          (intMagnitudeRemainderAsCounting scaleDivisor pumpedMantissa).symm)))

/-- **The dropped remainder is strictly below one unit in the last place** — with the
decomposition above, `roundTowardZero`'s error magnitude is strictly below
`radix ^ (target - exponent)`, the target-scale unit expressed at the common scale:
the sub-ulp certificate. -/
theorem roundTowardZeroRemainderIsBounded {radix : Int}
    (isRadixPositive : (0 : Int) < radix)
    (value : RadixScaledInteger) (targetExponent : Int) :
    intMagnitudeRemainder
        (intPower radix (targetExponent - value.exponent).toNat).toNat
        (value.mantissa * intPower radix (value.exponent - targetExponent).toNat) <
      (intPower radix (targetExponent - value.exponent).toNat).toNat :=
  let scaleDivisor := (intPower radix (targetExponent - value.exponent).toNat).toNat
  let pumpedMantissa :=
    value.mantissa * intPower radix (value.exponent - targetExponent).toNat
  have isDivisorPositive : 0 < scaleDivisor :=
    intToNatPosOfPos
      (intPowerPos isRadixPositive (targetExponent - value.exponent).toNat)
  Eq.rec
    (motive := fun remainderValue _ => remainderValue < scaleDivisor)
    (natDivModCountingRemainderIsBounded pumpedMantissa.natAbs scaleDivisor
      isDivisorPositive)
    (intMagnitudeRemainderAsCounting scaleDivisor pumpedMantissa).symm

/-! ## The cross-aligned order (FLOAT-3b)

`≤` on denoted values, min-free like `DenotesSameAs`: compare the two mantissas
rescaled onto their common scale.  Decidable (`Int.decLe`), total, reflexive;
antisymmetry lands EXACTLY on `DenotesSameAs`, so the order is a genuine partial order
on cross-alignment classes.  Transitivity replays the `denotesSameAsTrans` playbook
with `≤`-plumbing — scale both bounds by nonnegative powers onto one total exponent
(`intMulLeMulRightOfNonNeg`), chain, and reflect the common positive power back out
(`intLeOfMulLeMulRightOfPos`).  Congruence in each argument is then a corollary
through `lessEqualAsOfDenotesSame`.  Every rounding-mode correctness certificate
(FLOAT-3c/3d/3e) states its bounds in this order. -/

/-- **Value order by cross-alignment** — both mantissas rescaled onto the common
scale, compared in `Int`. -/
def LessEqualAs (radix : Int) (leftValue rightValue : RadixScaledInteger) : Prop :=
  crossAlignedMantissa radix leftValue rightValue ≤
    crossAlignedMantissa radix rightValue leftValue

/-- The cross-aligned order is decidable — it IS an `Int` bound (`Int.decLe` is
clean). -/
def decideLessEqualAs (radix : Int) (leftValue rightValue : RadixScaledInteger) :
    Decidable (LessEqualAs radix leftValue rightValue) :=
  Int.decLe (crossAlignedMantissa radix leftValue rightValue)
    (crossAlignedMantissa radix rightValue leftValue)

/-- Reflexivity — the two aligned mantissas are the same term. -/
theorem lessEqualAsRefl (radix : Int) (value : RadixScaledInteger) :
    LessEqualAs radix value value :=
  intLessEqualRefl (crossAlignedMantissa radix value value)

/-- Totality — inherited from `intLessEqualTotal` on the aligned mantissas. -/
theorem lessEqualAsTotal (radix : Int) (leftValue rightValue : RadixScaledInteger) :
    LessEqualAs radix leftValue rightValue ∨
      LessEqualAs radix rightValue leftValue :=
  intLessEqualTotal (crossAlignedMantissa radix leftValue rightValue)
    (crossAlignedMantissa radix rightValue leftValue)

/-- Equal denotations are ordered — rewrite reflexivity's right endpoint along the
cross-alignment equation. -/
theorem lessEqualAsOfDenotesSame {radix : Int}
    {leftValue rightValue : RadixScaledInteger}
    (areSame : DenotesSameAs radix leftValue rightValue) :
    LessEqualAs radix leftValue rightValue :=
  intLessEqualOfEqRight
    (intLessEqualRefl (crossAlignedMantissa radix leftValue rightValue)) areSame

/-- **Antisymmetry up to the setoid** — mutual bounds on the aligned mantissas force
the cross-alignment equality: the order is a partial order on denotation classes. -/
theorem denotesSameAsOfLessEqualBoth {radix : Int}
    {leftValue rightValue : RadixScaledInteger}
    (isForward : LessEqualAs radix leftValue rightValue)
    (isBackward : LessEqualAs radix rightValue leftValue) :
    DenotesSameAs radix leftValue rightValue :=
  intLessEqualAntisymm isForward isBackward

/-- **Transitivity** — conditional on a positive radix, mirroring
`denotesSameAsTrans`: convert both bounds to the exponent-gap cycle presentation,
scale each by the complementary nonnegative power so both land on one total exponent
(`intToNatCycleBalance` reconciles the exponents), chain through the shared middle
representation, and reflect the common positive `radix ^ commonScale` factor back out.
No sign-ordering case split, no `min`. -/
theorem lessEqualAsTrans {radix : Int} (isRadixPositive : (0 : Int) < radix)
    {leftValue middleValue rightValue : RadixScaledInteger}
    (leftBelowMiddle : LessEqualAs radix leftValue middleValue)
    (middleBelowRight : LessEqualAs radix middleValue rightValue) :
    LessEqualAs radix leftValue rightValue :=
  let gapLeftMiddle := (leftValue.exponent - middleValue.exponent).toNat
  let gapMiddleLeft := (-(leftValue.exponent - middleValue.exponent)).toNat
  let gapMiddleRight := (middleValue.exponent - rightValue.exponent).toNat
  let gapRightMiddle := (-(middleValue.exponent - rightValue.exponent)).toNat
  let gapRightLeft := (rightValue.exponent - leftValue.exponent).toNat
  let gapLeftRight := (-(rightValue.exponent - leftValue.exponent)).toNat
  let commonScale := gapMiddleLeft + gapRightMiddle
  have middleLeftGapFlips :
      (middleValue.exponent - leftValue.exponent).toNat = gapMiddleLeft :=
    congrArg Int.toNat (intNegSub leftValue.exponent middleValue.exponent).symm
  have rightMiddleGapFlips :
      (rightValue.exponent - middleValue.exponent).toNat = gapRightMiddle :=
    congrArg Int.toNat (intNegSub middleValue.exponent rightValue.exponent).symm
  have leftRightGapFlips :
      (leftValue.exponent - rightValue.exponent).toNat = gapLeftRight :=
    congrArg Int.toNat (intNegSub rightValue.exponent leftValue.exponent).symm
  have leftMiddleAtCycleGaps :
      leftValue.mantissa * intPower radix gapLeftMiddle ≤
        middleValue.mantissa * intPower radix gapMiddleLeft :=
    intLessEqualOfEqRight leftBelowMiddle
      (congrArg (fun gapValue => middleValue.mantissa * intPower radix gapValue)
        middleLeftGapFlips)
  have middleRightAtCycleGaps :
      middleValue.mantissa * intPower radix gapMiddleRight ≤
        rightValue.mantissa * intPower radix gapRightMiddle :=
    intLessEqualOfEqRight middleBelowRight
      (congrArg (fun gapValue => rightValue.mantissa * intPower radix gapValue)
        rightMiddleGapFlips)
  have cycleBalances :
      gapLeftMiddle + gapMiddleRight + gapRightLeft =
        gapMiddleLeft + gapRightMiddle + gapLeftRight :=
    intToNatCycleBalance
      (intGapCycleTelescopes leftValue.exponent middleValue.exponent
        rightValue.exponent)
  have leftTotalExponent :
      gapLeftMiddle + (gapMiddleRight + gapRightLeft) = gapLeftRight + commonScale :=
    (Nat.add_assoc gapLeftMiddle gapMiddleRight gapRightLeft).symm.trans
      (cycleBalances.trans (Nat.add_comm commonScale gapLeftRight))
  have middleTotalExponent :
      gapMiddleLeft + (gapMiddleRight + gapRightLeft) =
        gapMiddleRight + (gapMiddleLeft + gapRightLeft) :=
    (Nat.add_assoc gapMiddleLeft gapMiddleRight gapRightLeft).symm.trans
      ((congrArg (· + gapRightLeft) (Nat.add_comm gapMiddleLeft gapMiddleRight)).trans
        (Nat.add_assoc gapMiddleRight gapMiddleLeft gapRightLeft))
  have rightTotalExponent :
      gapRightMiddle + (gapMiddleLeft + gapRightLeft) = gapRightLeft + commonScale :=
    (Nat.add_assoc gapRightMiddle gapMiddleLeft gapRightLeft).symm.trans
      ((Nat.add_comm (gapRightMiddle + gapMiddleLeft) gapRightLeft).trans
        (congrArg (gapRightLeft + ·) (Nat.add_comm gapRightMiddle gapMiddleLeft)))
  have scaledLeftBelowMiddle :
      leftValue.mantissa * intPower radix gapLeftMiddle *
          intPower radix (gapMiddleRight + gapRightLeft) ≤
        middleValue.mantissa * intPower radix gapMiddleLeft *
          intPower radix (gapMiddleRight + gapRightLeft) :=
    intMulLeMulRightOfNonNeg leftMiddleAtCycleGaps
      (intLessEqualOfLessThan
        (intPowerPos isRadixPositive (gapMiddleRight + gapRightLeft)))
  have scaledMiddleBelowRight :
      middleValue.mantissa * intPower radix gapMiddleRight *
          intPower radix (gapMiddleLeft + gapRightLeft) ≤
        rightValue.mantissa * intPower radix gapRightMiddle *
          intPower radix (gapMiddleLeft + gapRightLeft) :=
    intMulLeMulRightOfNonNeg middleRightAtCycleGaps
      (intLessEqualOfLessThan
        (intPowerPos isRadixPositive (gapMiddleLeft + gapRightLeft)))
  have middleRepresentationsAgree :
      middleValue.mantissa * intPower radix gapMiddleLeft *
          intPower radix (gapMiddleRight + gapRightLeft) =
        middleValue.mantissa * intPower radix gapMiddleRight *
          intPower radix (gapMiddleLeft + gapRightLeft) :=
    (intMulPowerFold radix middleValue.mantissa gapMiddleLeft
        (gapMiddleRight + gapRightLeft)).trans
      ((congrArg
          (fun exponentValue => middleValue.mantissa * intPower radix exponentValue)
          middleTotalExponent).trans
        (intMulPowerFold radix middleValue.mantissa gapMiddleRight
            (gapMiddleLeft + gapRightLeft)).symm)
  have chainedAtTotalExponent :
      leftValue.mantissa * intPower radix gapLeftMiddle *
          intPower radix (gapMiddleRight + gapRightLeft) ≤
        rightValue.mantissa * intPower radix gapRightMiddle *
          intPower radix (gapMiddleLeft + gapRightLeft) :=
    intLessEqualTrans
      (intLessEqualOfEqRight scaledLeftBelowMiddle middleRepresentationsAgree)
      scaledMiddleBelowRight
  have leftEndpointFolds :
      leftValue.mantissa * intPower radix gapLeftRight * intPower radix commonScale =
        leftValue.mantissa * intPower radix gapLeftMiddle *
          intPower radix (gapMiddleRight + gapRightLeft) :=
    (intMulPowerFold radix leftValue.mantissa gapLeftRight commonScale).trans
      ((congrArg
          (fun exponentValue => leftValue.mantissa * intPower radix exponentValue)
          leftTotalExponent.symm).trans
        (intMulPowerFold radix leftValue.mantissa gapLeftMiddle
            (gapMiddleRight + gapRightLeft)).symm)
  have rightEndpointFolds :
      rightValue.mantissa * intPower radix gapRightMiddle *
          intPower radix (gapMiddleLeft + gapRightLeft) =
        rightValue.mantissa * intPower radix gapRightLeft *
          intPower radix commonScale :=
    (intMulPowerFold radix rightValue.mantissa gapRightMiddle
        (gapMiddleLeft + gapRightLeft)).trans
      ((congrArg
          (fun exponentValue => rightValue.mantissa * intPower radix exponentValue)
          rightTotalExponent).trans
        (intMulPowerFold radix rightValue.mantissa gapRightLeft commonScale).symm)
  have cancelledAtCycleGaps :
      leftValue.mantissa * intPower radix gapLeftRight ≤
        rightValue.mantissa * intPower radix gapRightLeft :=
    intLeOfMulLeMulRightOfPos (intPowerPos isRadixPositive commonScale)
      (intLessEqualOfEqLeft leftEndpointFolds
        (intLessEqualOfEqRight chainedAtTotalExponent rightEndpointFolds))
  intLessEqualOfEqLeft
    (congrArg (fun gapValue => leftValue.mantissa * intPower radix gapValue)
      leftRightGapFlips)
    cancelledAtCycleGaps

/-- **Left congruence** — replacing the left operand by a cross-aligned equal keeps
the bound: chain the flipped equality through transitivity. -/
theorem lessEqualAsCongrLeft {radix : Int} (isRadixPositive : (0 : Int) < radix)
    {leftValue otherLeftValue rightValue : RadixScaledInteger}
    (leftsAgree : DenotesSameAs radix leftValue otherLeftValue)
    (isBelow : LessEqualAs radix leftValue rightValue) :
    LessEqualAs radix otherLeftValue rightValue :=
  lessEqualAsTrans isRadixPositive
    (lessEqualAsOfDenotesSame (denotesSameAsSymm leftsAgree)) isBelow

/-- **Right congruence** — replacing the right operand by a cross-aligned equal keeps
the bound. -/
theorem lessEqualAsCongrRight {radix : Int} (isRadixPositive : (0 : Int) < radix)
    {leftValue rightValue otherRightValue : RadixScaledInteger}
    (rightsAgree : DenotesSameAs radix rightValue otherRightValue)
    (isBelow : LessEqualAs radix leftValue rightValue) :
    LessEqualAs radix leftValue otherRightValue :=
  lessEqualAsTrans isRadixPositive isBelow (lessEqualAsOfDenotesSame rightsAgree)

/-! ## Order pumping — bounds transfer to and from every common lower scale

The `≤`-shaped siblings of the pumping pair: a cross-aligned bound holds at EVERY
common lower scale, and a bound at ANY single common lower scale already forces the
cross-aligned bound.  Same balance identity as the equality versions, with
`intMulLeMulRightOfNonNeg` scaling the bound where `congrArg` scaled the equation and
`intLeOfMulLeMulRightOfPos` cancelling where `intMulPowerRightCancel` cancelled.
These are what let the exact operations' monotonicity replay the congruence proofs. -/

/-- **Pumping a bound down**: cross-aligned-ordered values stay ordered at EVERY
common lower scale. -/
theorem boundedAtLowerScaleOfLessEqual {radix : Int}
    (isRadixPositive : (0 : Int) < radix)
    {leftValue rightValue : RadixScaledInteger} {lowerScale : Int}
    (isBelowLeft : lowerScale ≤ leftValue.exponent)
    (isBelowRight : lowerScale ≤ rightValue.exponent)
    (isBelow : LessEqualAs radix leftValue rightValue) :
    leftValue.mantissa * intPower radix (leftValue.exponent - lowerScale).toNat ≤
      rightValue.mantissa *
        intPower radix (rightValue.exponent - lowerScale).toNat :=
  let alignGap := leftValue.exponent - rightValue.exponent
  let negatedGapNat := (-alignGap).toNat
  let leftPumpNat := (leftValue.exponent - lowerScale).toNat
  let rightPumpNat := (rightValue.exponent - lowerScale).toNat
  have boundAtCycleGaps :
      leftValue.mantissa * intPower radix alignGap.toNat ≤
        rightValue.mantissa * intPower radix negatedGapNat :=
    intLessEqualOfEqRight isBelow
      (congrArg (fun gapValue => rightValue.mantissa * intPower radix gapValue)
        (congrArg Int.toNat
          (intNegSub leftValue.exponent rightValue.exponent).symm))
  have exponentsBalance :
      alignGap.toNat + rightPumpNat = negatedGapNat + leftPumpNat :=
    intPumpedGapsBalance isBelowLeft isBelowRight
  have leftSideRealigns :
      leftValue.mantissa * intPower radix leftPumpNat *
          intPower radix negatedGapNat =
        leftValue.mantissa * intPower radix alignGap.toNat *
          intPower radix rightPumpNat :=
    (intMulPowerFold radix leftValue.mantissa leftPumpNat negatedGapNat).trans
      ((congrArg (fun exponentValue => leftValue.mantissa * intPower radix exponentValue)
          (Nat.add_comm leftPumpNat negatedGapNat)).trans
        ((congrArg
            (fun exponentValue => leftValue.mantissa * intPower radix exponentValue)
            exponentsBalance.symm).trans
          (intMulPowerFold radix leftValue.mantissa alignGap.toNat
              rightPumpNat).symm))
  have rightSideRealigns :
      rightValue.mantissa * intPower radix negatedGapNat *
          intPower radix rightPumpNat =
        rightValue.mantissa * intPower radix rightPumpNat *
          intPower radix negatedGapNat :=
    (intMulPowerFold radix rightValue.mantissa negatedGapNat rightPumpNat).trans
      ((congrArg
          (fun exponentValue => rightValue.mantissa * intPower radix exponentValue)
          (Nat.add_comm negatedGapNat rightPumpNat)).trans
        (intMulPowerFold radix rightValue.mantissa rightPumpNat
            negatedGapNat).symm)
  have scaledBound :
      leftValue.mantissa * intPower radix leftPumpNat *
          intPower radix negatedGapNat ≤
        rightValue.mantissa * intPower radix rightPumpNat *
          intPower radix negatedGapNat :=
    intLessEqualOfEqLeft leftSideRealigns
      (intLessEqualOfEqRight
        (intMulLeMulRightOfNonNeg boundAtCycleGaps
          (intLessEqualOfLessThan (intPowerPos isRadixPositive rightPumpNat)))
        rightSideRealigns)
  intLeOfMulLeMulRightOfPos (intPowerPos isRadixPositive negatedGapNat) scaledBound

/-- **Pumping a bound up**: a bound at ANY single common lower scale already forces the
cross-aligned bound. -/
theorem lessEqualAsOfBoundedAtLowerScale {radix : Int}
    (isRadixPositive : (0 : Int) < radix)
    {leftValue rightValue : RadixScaledInteger} {lowerScale : Int}
    (isBelowLeft : lowerScale ≤ leftValue.exponent)
    (isBelowRight : lowerScale ≤ rightValue.exponent)
    (isBoundedAtLowerScale :
      leftValue.mantissa * intPower radix (leftValue.exponent - lowerScale).toNat ≤
        rightValue.mantissa *
          intPower radix (rightValue.exponent - lowerScale).toNat) :
    LessEqualAs radix leftValue rightValue :=
  let alignGap := leftValue.exponent - rightValue.exponent
  let negatedGapNat := (-alignGap).toNat
  let leftPumpNat := (leftValue.exponent - lowerScale).toNat
  let rightPumpNat := (rightValue.exponent - lowerScale).toNat
  have exponentsBalance :
      alignGap.toNat + rightPumpNat = negatedGapNat + leftPumpNat :=
    intPumpedGapsBalance isBelowLeft isBelowRight
  have leftSideRealigns :
      leftValue.mantissa * intPower radix alignGap.toNat *
          intPower radix rightPumpNat =
        leftValue.mantissa * intPower radix leftPumpNat *
          intPower radix negatedGapNat :=
    (intMulPowerFold radix leftValue.mantissa alignGap.toNat rightPumpNat).trans
      ((congrArg (fun exponentValue => leftValue.mantissa * intPower radix exponentValue)
          exponentsBalance).trans
        ((congrArg
            (fun exponentValue => leftValue.mantissa * intPower radix exponentValue)
            (Nat.add_comm negatedGapNat leftPumpNat)).trans
          (intMulPowerFold radix leftValue.mantissa leftPumpNat
              negatedGapNat).symm))
  have rightSideRealigns :
      rightValue.mantissa * intPower radix rightPumpNat *
          intPower radix negatedGapNat =
        rightValue.mantissa * intPower radix negatedGapNat *
          intPower radix rightPumpNat :=
    (intMulPowerFold radix rightValue.mantissa rightPumpNat negatedGapNat).trans
      ((congrArg
          (fun exponentValue => rightValue.mantissa * intPower radix exponentValue)
          (Nat.add_comm rightPumpNat negatedGapNat)).trans
        (intMulPowerFold radix rightValue.mantissa negatedGapNat
            rightPumpNat).symm)
  have scaledBound :
      leftValue.mantissa * intPower radix alignGap.toNat *
          intPower radix rightPumpNat ≤
        rightValue.mantissa * intPower radix negatedGapNat *
          intPower radix rightPumpNat :=
    intLessEqualOfEqLeft leftSideRealigns
      (intLessEqualOfEqRight
        (intMulLeMulRightOfNonNeg isBoundedAtLowerScale
          (intLessEqualOfLessThan (intPowerPos isRadixPositive negatedGapNat)))
        rightSideRealigns)
  have boundAtCycleGaps :
      leftValue.mantissa * intPower radix alignGap.toNat ≤
        rightValue.mantissa * intPower radix negatedGapNat :=
    intLeOfMulLeMulRightOfPos (intPowerPos isRadixPositive rightPumpNat) scaledBound
  intLessEqualOfEqRight boundAtCycleGaps
    (congrArg (fun gapValue => rightValue.mantissa * intPower radix gapValue)
      (congrArg Int.toNat (intNegSub leftValue.exponent rightValue.exponent)))

/-- **Exact addition is monotone in both summands** — the `≤`-shaped
`addExactRespectsDenotesSameAs`: pick the common scale = the clamped-gap floor of the
two sums' floors, pump both bounds down to it (`boundedAtLowerScaleOfLessEqual`), add
them (`intAddLeAddRight` then `intAddLeAddLeft`), recognize each side as the
corresponding sum's mantissa pumped to that scale (`addExactMantissaAtLowerScale`),
and pump the bound back up (`lessEqualAsOfBoundedAtLowerScale`). -/
theorem addExactMonotone {radix : Int} (isRadixPositive : (0 : Int) < radix)
    {leftSummand otherLeftSummand rightSummand otherRightSummand : RadixScaledInteger}
    (leftSummandsOrdered : LessEqualAs radix leftSummand otherLeftSummand)
    (rightSummandsOrdered : LessEqualAs radix rightSummand otherRightSummand) :
    LessEqualAs radix (addExact radix leftSummand rightSummand)
      (addExact radix otherLeftSummand otherRightSummand) :=
  let firstSum := addExact radix leftSummand rightSummand
  let secondSum := addExact radix otherLeftSummand otherRightSummand
  let commonScale := firstSum.exponent -
    Int.ofNat (firstSum.exponent - secondSum.exponent).toNat
  have isBelowFirstFloor : commonScale ≤ firstSum.exponent :=
    intGapFloorLeMinuend firstSum.exponent secondSum.exponent
  have isBelowSecondFloor : commonScale ≤ secondSum.exponent :=
    intGapFloorLeSubtrahend firstSum.exponent secondSum.exponent
  have isBelowLeft : commonScale ≤ leftSummand.exponent :=
    intLessEqualTrans isBelowFirstFloor
      (intGapFloorLeMinuend leftSummand.exponent rightSummand.exponent)
  have isBelowRight : commonScale ≤ rightSummand.exponent :=
    intLessEqualTrans isBelowFirstFloor
      (intGapFloorLeSubtrahend leftSummand.exponent rightSummand.exponent)
  have isBelowOtherLeft : commonScale ≤ otherLeftSummand.exponent :=
    intLessEqualTrans isBelowSecondFloor
      (intGapFloorLeMinuend otherLeftSummand.exponent otherRightSummand.exponent)
  have isBelowOtherRight : commonScale ≤ otherRightSummand.exponent :=
    intLessEqualTrans isBelowSecondFloor
      (intGapFloorLeSubtrahend otherLeftSummand.exponent otherRightSummand.exponent)
  have summandsBoundedPumped :
      leftSummand.mantissa *
            intPower radix (leftSummand.exponent - commonScale).toNat +
          rightSummand.mantissa *
            intPower radix (rightSummand.exponent - commonScale).toNat ≤
        otherLeftSummand.mantissa *
            intPower radix (otherLeftSummand.exponent - commonScale).toNat +
          otherRightSummand.mantissa *
            intPower radix (otherRightSummand.exponent - commonScale).toNat :=
    intLessEqualTrans
      (intAddLeAddRight
        (boundedAtLowerScaleOfLessEqual isRadixPositive isBelowLeft
          isBelowOtherLeft leftSummandsOrdered)
        (rightSummand.mantissa *
          intPower radix (rightSummand.exponent - commonScale).toNat))
      (intAddLeAddLeft
        (boundedAtLowerScaleOfLessEqual isRadixPositive isBelowRight
          isBelowOtherRight rightSummandsOrdered)
        (otherLeftSummand.mantissa *
          intPower radix (otherLeftSummand.exponent - commonScale).toNat))
  lessEqualAsOfBoundedAtLowerScale isRadixPositive isBelowFirstFloor
    isBelowSecondFloor
    (intLessEqualOfEqLeft
      (addExactMantissaAtLowerScale radix leftSummand rightSummand
        isBelowFirstFloor)
      (intLessEqualOfEqRight summandsBoundedPumped
        (addExactMantissaAtLowerScale radix otherLeftSummand otherRightSummand
          isBelowSecondFloor).symm))

/-- **Exact multiplication is monotone in the left factor** against a NONNEGATIVE
cofactor — the `≤`-shaped `mulExactRespectsDenotesSameAs` specialized to a shared
right factor.  The nonnegativity hypothesis is essential: scaling a bound by a
negative mantissa reverses it.  The bound scales by the cofactor's aligned mantissa
(`intMulLeMulRightOfNonNeg` fed by `intMulNonNeg`), the exponent bookkeeping is
verbatim the congruence proof's trivial-cycle balance, and the common power reflects
back out through `intLeOfMulLeMulRightOfPos`. -/
theorem mulExactMonotoneLeft {radix : Int} (isRadixPositive : (0 : Int) < radix)
    {leftFactor otherLeftFactor rightFactor : RadixScaledInteger}
    (isRightFactorNonNegative : (0 : Int) ≤ rightFactor.mantissa)
    (leftFactorsOrdered : LessEqualAs radix leftFactor otherLeftFactor) :
    LessEqualAs radix (mulExact leftFactor rightFactor)
      (mulExact otherLeftFactor rightFactor) :=
  let leftGap := leftFactor.exponent - otherLeftFactor.exponent
  let rightGap := rightFactor.exponent - rightFactor.exponent
  let productGap := leftGap + rightGap
  let forwardGapNat := productGap.toNat
  let backwardGapNat := (-productGap).toNat
  let commonScale := (-leftGap).toNat + (-rightGap).toNat
  let leftMantissaProduct := leftFactor.mantissa * rightFactor.mantissa
  let rightMantissaProduct := otherLeftFactor.mantissa * rightFactor.mantissa
  have leftAtCycleGaps :
      leftFactor.mantissa * intPower radix leftGap.toNat ≤
        otherLeftFactor.mantissa * intPower radix (-leftGap).toNat :=
    intLessEqualOfEqRight leftFactorsOrdered
      (congrArg (fun gapValue => otherLeftFactor.mantissa * intPower radix gapValue)
        (congrArg Int.toNat
          (intNegSub leftFactor.exponent otherLeftFactor.exponent).symm))
  have rightAtCycleGaps :
      rightFactor.mantissa * intPower radix rightGap.toNat =
        rightFactor.mantissa * intPower radix (-rightGap).toNat :=
    congrArg (fun gapValue => rightFactor.mantissa * intPower radix gapValue)
      (congrArg Int.toNat
        (intNegSub rightFactor.exponent rightFactor.exponent).symm)
  have isCofactorNonNegative :
      (0 : Int) ≤ rightFactor.mantissa * intPower radix rightGap.toNat :=
    intMulNonNeg isRightFactorNonNegative
      (intLessEqualOfLessThan (intPowerPos isRadixPositive rightGap.toNat))
  have combinedAtSummedGaps :
      leftMantissaProduct * intPower radix (leftGap.toNat + rightGap.toNat) ≤
        rightMantissaProduct * intPower radix commonScale :=
    intLessEqualOfEqLeft
      (Eq.symm
        ((intMulSwapMiddle leftFactor.mantissa (intPower radix leftGap.toNat)
            rightFactor.mantissa (intPower radix rightGap.toNat)).trans
          (congrArg (leftMantissaProduct * ·)
            (intPowerAdd radix leftGap.toNat rightGap.toNat).symm)))
      (intLessEqualOfEqRight
        (intMulLeMulRightOfNonNeg leftAtCycleGaps isCofactorNonNegative)
        ((congrArg ((otherLeftFactor.mantissa * intPower radix (-leftGap).toNat) * ·)
            rightAtCycleGaps).trans
          ((intMulSwapMiddle otherLeftFactor.mantissa
              (intPower radix (-leftGap).toNat) rightFactor.mantissa
              (intPower radix (-rightGap).toNat)).trans
            (congrArg (rightMantissaProduct * ·)
              (intPowerAdd radix (-leftGap).toNat (-rightGap).toNat).symm))))
  have balanceAtTrivialCycle :
      leftGap.toNat + rightGap.toNat + backwardGapNat =
        (-leftGap).toNat + (-rightGap).toNat + forwardGapNat :=
    (intToNatCycleBalance (firstGap := leftGap) (secondGap := rightGap)
        (thirdGap := -productGap) (intAddRightNeg productGap)).trans
      (congrArg (((-leftGap).toNat + (-rightGap).toNat) + ·)
        (congrArg Int.toNat (intNegNeg productGap)))
  have leftEndpointFolds :
      leftMantissaProduct * intPower radix forwardGapNat *
          intPower radix commonScale =
        leftMantissaProduct * intPower radix (leftGap.toNat + rightGap.toNat) *
          intPower radix backwardGapNat :=
    (intMulPowerFold radix leftMantissaProduct forwardGapNat commonScale).trans
      ((congrArg
          (fun exponentValue => leftMantissaProduct * intPower radix exponentValue)
          (Nat.add_comm forwardGapNat commonScale)).trans
        ((congrArg
            (fun exponentValue => leftMantissaProduct * intPower radix exponentValue)
            balanceAtTrivialCycle.symm).trans
          (intMulPowerFold radix leftMantissaProduct
              (leftGap.toNat + rightGap.toNat) backwardGapNat).symm))
  have rightEndpointFolds :
      rightMantissaProduct * intPower radix commonScale *
          intPower radix backwardGapNat =
        rightMantissaProduct * intPower radix backwardGapNat *
          intPower radix commonScale :=
    (intMulPowerFold radix rightMantissaProduct commonScale backwardGapNat).trans
      ((congrArg
          (fun exponentValue => rightMantissaProduct * intPower radix exponentValue)
          (Nat.add_comm commonScale backwardGapNat)).trans
        (intMulPowerFold radix rightMantissaProduct backwardGapNat
            commonScale).symm)
  have cancelledAtCycleGaps :
      leftMantissaProduct * intPower radix forwardGapNat ≤
        rightMantissaProduct * intPower radix backwardGapNat :=
    intLeOfMulLeMulRightOfPos (intPowerPos isRadixPositive commonScale)
      (intLessEqualOfEqLeft leftEndpointFolds
        (intLessEqualOfEqRight
          (intMulLeMulRightOfNonNeg combinedAtSummedGaps
            (intLessEqualOfLessThan (intPowerPos isRadixPositive backwardGapNat)))
          rightEndpointFolds))
  have productGapSplits :
      (leftFactor.exponent + rightFactor.exponent) -
          (otherLeftFactor.exponent + rightFactor.exponent) = productGap :=
    (congrArg ((leftFactor.exponent + rightFactor.exponent) + ·)
        (intNegAdd otherLeftFactor.exponent rightFactor.exponent)).trans
      (intAddSwapMiddle leftFactor.exponent rightFactor.exponent
        (-otherLeftFactor.exponent) (-rightFactor.exponent))
  have reverseProductGapCollapses :
      (otherLeftFactor.exponent + rightFactor.exponent) -
          (leftFactor.exponent + rightFactor.exponent) = -productGap :=
    (intNegSub (leftFactor.exponent + rightFactor.exponent)
        (otherLeftFactor.exponent + rightFactor.exponent)).symm.trans
      (congrArg Int.neg productGapSplits)
  intLessEqualOfEqLeft
    (congrArg (fun gapValue => leftMantissaProduct * intPower radix gapValue)
      (congrArg Int.toNat productGapSplits))
    (intLessEqualOfEqRight cancelledAtCycleGaps
      (congrArg (fun gapValue => rightMantissaProduct * intPower radix gapValue)
        (congrArg Int.toNat reverseProductGapCollapses)).symm)

/-- **Exact multiplication is monotone in the right factor** against a NONNEGATIVE
cofactor — transport `mulExactMonotoneLeft` along the strict record equality
`mulExactComm` on both endpoints. -/
theorem mulExactMonotoneRight {radix : Int} (isRadixPositive : (0 : Int) < radix)
    {leftFactor rightFactor otherRightFactor : RadixScaledInteger}
    (isLeftFactorNonNegative : (0 : Int) ≤ leftFactor.mantissa)
    (rightFactorsOrdered : LessEqualAs radix rightFactor otherRightFactor) :
    LessEqualAs radix (mulExact leftFactor rightFactor)
      (mulExact leftFactor otherRightFactor) :=
  Eq.rec
    (motive := fun flippedProduct _ =>
      LessEqualAs radix (mulExact leftFactor rightFactor) flippedProduct)
    (Eq.rec
      (motive := fun flippedProduct _ =>
        LessEqualAs radix flippedProduct (mulExact otherRightFactor leftFactor))
      (mulExactMonotoneLeft isRadixPositive isLeftFactorNonNegative
        rightFactorsOrdered)
      (mulExactComm rightFactor leftFactor))
    (mulExactComm otherRightFactor leftFactor)

/-- **Toward-zero rounds DOWN on nonnegative values** — the nonnegative half of the
magnitude bound: truncation drops a nonnegative remainder, so the rounded value sits
below the original in the cross-aligned order.  Destruct the nonnegative pumped
mantissa to an explicit `ofNat` carrier, read the rounded mantissa off the counting
divider's `ofNat` arm, bound quotient-times-divisor by the reconstruction certificate,
and lift the `Nat` bound through the `ofNat` order embedding. -/
theorem roundTowardZeroIsBelowOfNonNegativeMantissa {radix : Int}
    (isRadixPositive : (0 : Int) < radix)
    {value : RadixScaledInteger} (targetExponent : Int)
    (isMantissaNonNegative : (0 : Int) ≤ value.mantissa) :
    LessEqualAs radix (roundTowardZero radix value targetExponent) value :=
  let scaleDivisor := (intPower radix (targetExponent - value.exponent).toNat).toNat
  let pumpedMantissa :=
    value.mantissa * intPower radix (value.exponent - targetExponent).toNat
  have isPumpedNonNegative : (0 : Int) ≤ pumpedMantissa :=
    intMulNonNeg isMantissaNonNegative
      (intLessEqualOfLessThan
        (intPowerPos isRadixPositive (value.exponent - targetExponent).toNat))
  match intZeroLeDest isPumpedNonNegative with
  | ⟨pumpedMagnitude, pumpedEquation⟩ =>
      have quotientTimesDivisorIsBounded :
          (natDivModCounting pumpedMagnitude scaleDivisor).fst * scaleDivisor ≤
            pumpedMagnitude :=
        Nat.le.intro
          ((congrArg (· + (natDivModCounting pumpedMagnitude scaleDivisor).snd)
              (Nat.mul_comm scaleDivisor
                (natDivModCounting pumpedMagnitude scaleDivisor).fst)).symm.trans
            (natDivModCountingReconstructs pumpedMagnitude scaleDivisor).symm)
      have quotientCarrier :
          (roundTowardZero radix value targetExponent).mantissa =
            Int.ofNat (natDivModCounting pumpedMagnitude scaleDivisor).fst :=
        congrArg (intMagnitudeQuotient scaleDivisor) pumpedEquation
      have divisorRestores :
          Int.ofNat scaleDivisor =
            intPower radix (targetExponent - value.exponent).toNat :=
        intOfNatToNatOfNonNeg
          (intLessEqualOfLessThan
            (intPowerPos isRadixPositive (targetExponent - value.exponent).toNat))
      have alignedRoundCollapses :
          (roundTowardZero radix value targetExponent).mantissa *
              intPower radix (targetExponent - value.exponent).toNat =
            Int.ofNat
              ((natDivModCounting pumpedMagnitude scaleDivisor).fst *
                scaleDivisor) :=
        (congrArg (· * intPower radix (targetExponent - value.exponent).toNat)
            quotientCarrier).trans
          (congrArg
            (Int.ofNat (natDivModCounting pumpedMagnitude scaleDivisor).fst * ·)
            divisorRestores.symm)
      intLessEqualOfEqLeft alignedRoundCollapses
        (intLessEqualOfEqRight
          (intOfNatLeOfNat quotientTimesDivisorIsBounded)
          pumpedEquation.symm)

/-- **Toward-zero rounds UP on nonpositive values** — the nonpositive half of the
magnitude bound: truncation drops a nonpositive remainder, so the original sits below
the rounded value in the cross-aligned order.  The nonpositive pumped mantissa
destructs to an explicit NEGATED `ofNat` carrier; a zero magnitude collapses both
sides to zero, a successor magnitude exposes the divider's `negSucc` arm and the
`Nat` bound flips through the negation antitone `intNegLeNegOfLe`. -/
theorem roundTowardZeroIsAboveOfNonPositiveMantissa {radix : Int}
    (isRadixPositive : (0 : Int) < radix)
    {value : RadixScaledInteger} (targetExponent : Int)
    (isMantissaNonPositive : value.mantissa ≤ (0 : Int)) :
    LessEqualAs radix value (roundTowardZero radix value targetExponent) :=
  let scaleDivisor := (intPower radix (targetExponent - value.exponent).toNat).toNat
  let pumpedMantissa :=
    value.mantissa * intPower radix (value.exponent - targetExponent).toNat
  have isPumpedNonPositive : pumpedMantissa ≤ (0 : Int) :=
    intLessEqualOfEqRight
      (intMulLeMulRightOfNonNeg isMantissaNonPositive
        (intLessEqualOfLessThan
          (intPowerPos isRadixPositive (value.exponent - targetExponent).toNat)))
      (intZeroMul (intPower radix (value.exponent - targetExponent).toNat))
  match intLessEqualDest isPumpedNonPositive with
  | ⟨pumpedMagnitude, gapEquation⟩ =>
      have pumpedCarrier : pumpedMantissa = -(Int.ofNat pumpedMagnitude) :=
        (intAddZero pumpedMantissa).symm.trans
          ((congrArg (pumpedMantissa + ·)
              (intAddRightNeg (Int.ofNat pumpedMagnitude)).symm).trans
            ((intAddAssoc pumpedMantissa (Int.ofNat pumpedMagnitude)
                (-(Int.ofNat pumpedMagnitude))).symm.trans
              ((congrArg (· + -(Int.ofNat pumpedMagnitude)) gapEquation.symm).trans
                (intZeroAdd (-(Int.ofNat pumpedMagnitude))))))
      match pumpedMagnitude, pumpedCarrier with
      | 0, zeroCarrier =>
          have quotientVanishes :
              (roundTowardZero radix value targetExponent).mantissa = (0 : Int) :=
            congrArg (intMagnitudeQuotient scaleDivisor) zeroCarrier
          intLessEqualOfEqLeft zeroCarrier
            (intLessEqualOfEqRight (intLessEqualRefl (0 : Int))
              ((congrArg
                  (· * intPower radix (targetExponent - value.exponent).toNat)
                  quotientVanishes).trans
                (intZeroMul
                  (intPower radix (targetExponent - value.exponent).toNat))).symm)
      | successorPredecessor + 1, negativeCarrier =>
          have quotientCarrier :
              (roundTowardZero radix value targetExponent).mantissa =
                -(Int.ofNat
                  (natDivModCounting (successorPredecessor + 1)
                    scaleDivisor).fst) :=
            congrArg (intMagnitudeQuotient scaleDivisor) negativeCarrier
          have quotientTimesDivisorIsBounded :
              (natDivModCounting (successorPredecessor + 1) scaleDivisor).fst *
                  scaleDivisor ≤
                successorPredecessor + 1 :=
            Nat.le.intro
              ((congrArg
                  (· + (natDivModCounting (successorPredecessor + 1)
                    scaleDivisor).snd)
                  (Nat.mul_comm scaleDivisor
                    (natDivModCounting (successorPredecessor + 1)
                      scaleDivisor).fst)).symm.trans
                (natDivModCountingReconstructs (successorPredecessor + 1)
                  scaleDivisor).symm)
          have divisorRestores :
              Int.ofNat scaleDivisor =
                intPower radix (targetExponent - value.exponent).toNat :=
            intOfNatToNatOfNonNeg
              (intLessEqualOfLessThan
                (intPowerPos isRadixPositive
                  (targetExponent - value.exponent).toNat))
          have alignedRoundCollapses :
              (roundTowardZero radix value targetExponent).mantissa *
                  intPower radix (targetExponent - value.exponent).toNat =
                -(Int.ofNat
                  ((natDivModCounting (successorPredecessor + 1)
                    scaleDivisor).fst * scaleDivisor)) :=
            (congrArg (· * intPower radix (targetExponent - value.exponent).toNat)
                quotientCarrier).trans
              ((congrArg
                  (-(Int.ofNat (natDivModCounting (successorPredecessor + 1)
                    scaleDivisor).fst) * ·)
                  divisorRestores.symm).trans
                (intNegMul
                  (Int.ofNat (natDivModCounting (successorPredecessor + 1)
                    scaleDivisor).fst)
                  (Int.ofNat scaleDivisor)))
          intLessEqualOfEqLeft negativeCarrier
            (intLessEqualOfEqRight
              (intNegLeNegOfLe (intOfNatLeOfNat quotientTimesDivisorIsBounded))
              alignedRoundCollapses.symm)

/-! ## Rounding monotonicity (FLOAT-3c capstone)

Toward-zero rounding is monotone in the cross-aligned order.  The whole argument
is a change of scale: re-express each rounded mantissa as ONE magnitude quotient by
the COMMON divisor at a shared lower scale (the two-step clamped-gap floor of both
exponents and the target), pump the order hypothesis down to that scale, and let the
sign-aware `intMagnitudeQuotientIsMonotone` carry it through the division.  No sign
split appears here — the `Int` layer already absorbed it. -/

/-- **The rounded mantissa re-expressed at a common lower scale**: for any scale
below both the value's exponent and the target, the toward-zero mantissa IS the
magnitude quotient of the value pumped to that scale by the target's pump power.
Away from the diagonal one gap clamps: at or below the value's exponent the
division collapses to `1` and the pumped dividend FOLDS through the alignment gap
(`intMagnitudeQuotientScales` at divisor `1`); at or above, the alignment collapses
and the common divisor SPLITS as division gap times pump (`intMagnitudeQuotientScales`
at the division power). -/
theorem roundTowardZeroMantissaAtLowerScale {radix : Int}
    (isRadixPositive : (0 : Int) < radix) (value : RadixScaledInteger)
    {targetExponent lowerScale : Int}
    (isBelowValue : lowerScale ≤ value.exponent)
    (isBelowTarget : lowerScale ≤ targetExponent) :
    (roundTowardZero radix value targetExponent).mantissa =
      intMagnitudeQuotient
        (intPower radix (targetExponent - lowerScale).toNat).toNat
        (value.mantissa * intPower radix (value.exponent - lowerScale).toNat) :=
  have exponentsBalance :
      (targetExponent - value.exponent).toNat +
          (value.exponent - lowerScale).toNat =
        (value.exponent - targetExponent).toNat +
          (targetExponent - lowerScale).toNat :=
    (intPumpedGapsBalance isBelowTarget isBelowValue).trans
      (congrArg (· + (targetExponent - lowerScale).toNat)
        (congrArg Int.toNat (intNegSub targetExponent value.exponent)))
  match intLessEqualTotal targetExponent value.exponent with
  | .inl isTargetBelow =>
      let alignmentGapNat := (value.exponent - targetExponent).toNat
      let valuePumpNat := (value.exponent - lowerScale).toNat
      let targetPumpNat := (targetExponent - lowerScale).toNat
      let targetPumpPower := intPower radix targetPumpNat
      have divisionGapVanishes : (targetExponent - value.exponent).toNat = 0 :=
        intGapToNatEqZeroOfLe isTargetBelow
      have leftCollapses :
          (roundTowardZero radix value targetExponent).mantissa =
            value.mantissa * intPower radix alignmentGapNat :=
        (congrArg
            (fun gapNat => intMagnitudeQuotient (intPower radix gapNat).toNat
              (value.mantissa * intPower radix alignmentGapNat))
            divisionGapVanishes).trans
          (intMagnitudeQuotientByOne
            (value.mantissa * intPower radix alignmentGapNat))
      have pumpSplits : valuePumpNat = alignmentGapNat + targetPumpNat :=
        (Nat.zero_add valuePumpNat).symm.trans
          ((congrArg (· + valuePumpNat) divisionGapVanishes.symm).trans
            exponentsBalance)
      have targetPumpRoundTrip :
          Int.ofNat targetPumpPower.toNat = targetPumpPower :=
        intOfNatToNatOfNonNeg
          (intLessEqualOfLessThan (intPowerPos isRadixPositive targetPumpNat))
      have dividendFolds :
          value.mantissa * intPower radix valuePumpNat =
            value.mantissa * intPower radix alignmentGapNat *
              Int.ofNat targetPumpPower.toNat :=
        (congrArg (fun gapNat => value.mantissa * intPower radix gapNat)
            pumpSplits).trans
          ((congrArg (value.mantissa * ·)
              (intPowerAdd radix alignmentGapNat targetPumpNat)).trans
            ((intMulAssoc value.mantissa (intPower radix alignmentGapNat)
                targetPumpPower).symm.trans
              (congrArg
                (value.mantissa * intPower radix alignmentGapNat * ·)
                targetPumpRoundTrip.symm)))
      leftCollapses.trans
        ((intMagnitudeQuotientByOne
            (value.mantissa * intPower radix alignmentGapNat)).symm.trans
          (((intMagnitudeQuotientScales (divisor := 1) Nat.le.refl
                (intToNatPosOfPos (intPowerPos isRadixPositive targetPumpNat))
                (value.mantissa * intPower radix alignmentGapNat)).symm.trans
              (congrArg
                (fun divisorNat =>
                  intMagnitudeQuotient divisorNat
                    (value.mantissa * intPower radix alignmentGapNat *
                      Int.ofNat targetPumpPower.toNat))
                ((Nat.mul_comm 1 targetPumpPower.toNat).trans
                  (Nat.zero_add targetPumpPower.toNat)))).trans
            (congrArg (intMagnitudeQuotient targetPumpPower.toNat)
              dividendFolds.symm)))
  | .inr isValueBelow =>
      let divisionGapNat := (targetExponent - value.exponent).toNat
      let valuePumpNat := (value.exponent - lowerScale).toNat
      let targetPumpNat := (targetExponent - lowerScale).toNat
      let divisionPower := intPower radix divisionGapNat
      let valuePumpPower := intPower radix valuePumpNat
      have alignmentGapVanishes : (value.exponent - targetExponent).toNat = 0 :=
        intGapToNatEqZeroOfLe isValueBelow
      have leftCollapses :
          (roundTowardZero radix value targetExponent).mantissa =
            intMagnitudeQuotient divisionPower.toNat value.mantissa :=
        (congrArg
            (fun gapNat => intMagnitudeQuotient divisionPower.toNat
              (value.mantissa * intPower radix gapNat))
            alignmentGapVanishes).trans
          (congrArg (intMagnitudeQuotient divisionPower.toNat)
            (intMulOne value.mantissa))
      have targetPumpSplits : targetPumpNat = divisionGapNat + valuePumpNat :=
        (Nat.zero_add targetPumpNat).symm.trans
          ((congrArg (· + targetPumpNat) alignmentGapVanishes.symm).trans
            exponentsBalance.symm)
      have divisionRoundTrip : Int.ofNat divisionPower.toNat = divisionPower :=
        intOfNatToNatOfNonNeg
          (intLessEqualOfLessThan (intPowerPos isRadixPositive divisionGapNat))
      have valuePumpRoundTrip :
          Int.ofNat valuePumpPower.toNat = valuePumpPower :=
        intOfNatToNatOfNonNeg
          (intLessEqualOfLessThan (intPowerPos isRadixPositive valuePumpNat))
      have divisorSplits :
          (intPower radix targetPumpNat).toNat =
            divisionPower.toNat * valuePumpPower.toNat :=
        congrArg Int.toNat
          ((congrArg (intPower radix) targetPumpSplits).trans
            ((intPowerAdd radix divisionGapNat valuePumpNat).trans
              ((congrArg (· * valuePumpPower) divisionRoundTrip.symm).trans
                (congrArg (Int.ofNat divisionPower.toNat * ·)
                  valuePumpRoundTrip.symm))))
      leftCollapses.trans
        (((intMagnitudeQuotientScales
              (intToNatPosOfPos (intPowerPos isRadixPositive divisionGapNat))
              (intToNatPosOfPos (intPowerPos isRadixPositive valuePumpNat))
              value.mantissa).symm.trans
            (congrArg
              (fun divisorNat => intMagnitudeQuotient divisorNat
                (value.mantissa * Int.ofNat valuePumpPower.toNat))
              divisorSplits.symm)).trans
          (congrArg
            (intMagnitudeQuotient (intPower radix targetPumpNat).toNat)
            (congrArg (value.mantissa * ·) valuePumpRoundTrip)))

/-- **Toward-zero rounding is monotone** in the cross-aligned order — the FLOAT-3c
correctness capstone.  Pump both operands down to the two-step clamped-gap floor of
both exponents and the target, where the truncation divisors coincide; the pumped
bound rides `intMagnitudeQuotientIsMonotone` through the common division, and both
sides read back as the rounded mantissas via `roundTowardZeroMantissaAtLowerScale`.
The rounded values share the target exponent, so the cross-aligned goal collapses
to that mantissa bound. -/
theorem roundTowardZeroMonotone {radix : Int} (isRadixPositive : (0 : Int) < radix)
    {leftValue rightValue : RadixScaledInteger} (targetExponent : Int)
    (isOrdered : LessEqualAs radix leftValue rightValue) :
    LessEqualAs radix (roundTowardZero radix leftValue targetExponent)
      (roundTowardZero radix rightValue targetExponent) :=
  let firstFloor := leftValue.exponent -
    Int.ofNat (leftValue.exponent - rightValue.exponent).toNat
  let commonScale := firstFloor - Int.ofNat (firstFloor - targetExponent).toNat
  have isBelowLeft : commonScale ≤ leftValue.exponent :=
    intLessEqualTrans (intGapFloorLeMinuend firstFloor targetExponent)
      (intGapFloorLeMinuend leftValue.exponent rightValue.exponent)
  have isBelowRight : commonScale ≤ rightValue.exponent :=
    intLessEqualTrans (intGapFloorLeMinuend firstFloor targetExponent)
      (intGapFloorLeSubtrahend leftValue.exponent rightValue.exponent)
  have isBelowTarget : commonScale ≤ targetExponent :=
    intGapFloorLeSubtrahend firstFloor targetExponent
  have quotientBound :
      intMagnitudeQuotient
          (intPower radix (targetExponent - commonScale).toNat).toNat
          (leftValue.mantissa *
            intPower radix (leftValue.exponent - commonScale).toNat) ≤
        intMagnitudeQuotient
          (intPower radix (targetExponent - commonScale).toNat).toNat
          (rightValue.mantissa *
            intPower radix (rightValue.exponent - commonScale).toNat) :=
    intMagnitudeQuotientIsMonotone
      (intPower radix (targetExponent - commonScale).toNat).toNat
      (boundedAtLowerScaleOfLessEqual isRadixPositive isBelowLeft isBelowRight
        isOrdered)
  have mantissaBound :
      (roundTowardZero radix leftValue targetExponent).mantissa ≤
        (roundTowardZero radix rightValue targetExponent).mantissa :=
    intLessEqualOfEqLeft
      (roundTowardZeroMantissaAtLowerScale isRadixPositive leftValue
        isBelowLeft isBelowTarget)
      (intLessEqualOfEqRight quotientBound
        (roundTowardZeroMantissaAtLowerScale isRadixPositive rightValue
          isBelowRight isBelowTarget).symm)
  have selfGapVanishes : (targetExponent - targetExponent).toNat = 0 :=
    intGapToNatEqZeroOfLe (intLessEqualRefl targetExponent)
  intLessEqualOfEqLeft
    ((congrArg
        (fun gapNat =>
          (roundTowardZero radix leftValue targetExponent).mantissa *
            intPower radix gapNat)
        selfGapVanishes).trans
      (intMulOne (roundTowardZero radix leftValue targetExponent).mantissa))
    (intLessEqualOfEqRight mantissaBound
      (((congrArg
          (fun gapNat =>
            (roundTowardZero radix rightValue targetExponent).mantissa *
              intPower radix gapNat)
          selfGapVanishes).trans
        (intMulOne
          (roundTowardZero radix rightValue targetExponent).mantissa)).symm))

/-! ## Directed rounding — the floor and ceiling modes (FLOAT-3d)

The directed modes replace the magnitude quotient with the floor/ceiling quotient
in the toward-zero template.  Min-free cross-alignment makes their defining bounds
the `Int`-layer BRACKETS directly: comparing the rounded value against the original
pits the corrected quotient times `radix ^ divisionGap` against the pumped mantissa
— exactly the bracket, once the divisor power round-trips through `toNat`.  No
pumping machinery appears. -/

/-- **Round toward negative infinity** — the toward-zero template with the floor
quotient. -/
def roundTowardNegative (radix : Int) (value : RadixScaledInteger)
    (targetExponent : Int) : RadixScaledInteger :=
  { mantissa := intFloorQuotient
      (intPower radix (targetExponent - value.exponent).toNat).toNat
      (value.mantissa * intPower radix (value.exponent - targetExponent).toNat)
    exponent := targetExponent }

/-- The mantissa equation of floor rounding, definitional. -/
theorem roundTowardNegativeMantissa (radix : Int) (value : RadixScaledInteger)
    (targetExponent : Int) :
    (roundTowardNegative radix value targetExponent).mantissa =
      intFloorQuotient
        (intPower radix (targetExponent - value.exponent).toNat).toNat
        (value.mantissa *
          intPower radix (value.exponent - targetExponent).toNat) := rfl

/-- The exponent equation of floor rounding, definitional. -/
theorem roundTowardNegativeExponent (radix : Int) (value : RadixScaledInteger)
    (targetExponent : Int) :
    (roundTowardNegative radix value targetExponent).exponent =
      targetExponent := rfl

/-- **Floor rounds DOWN**: the floor-rounded value sits at or below the original in
the cross-aligned order — the lower bracket read at the common scale (the rounded
side realigns by the division gap; the original side IS the pumped mantissa). -/
theorem roundTowardNegativeIsBelow {radix : Int}
    (isRadixPositive : (0 : Int) < radix) (value : RadixScaledInteger)
    (targetExponent : Int) :
    LessEqualAs radix (roundTowardNegative radix value targetExponent) value :=
  intLessEqualOfEqLeft
    (congrArg
      (intFloorQuotient
        (intPower radix (targetExponent - value.exponent).toNat).toNat
        (value.mantissa *
          intPower radix (value.exponent - targetExponent).toNat) * ·)
      (intOfNatToNatOfNonNeg
        (intLessEqualOfLessThan
          (intPowerPos isRadixPositive
            (targetExponent - value.exponent).toNat))).symm)
    (intFloorQuotientMulIsBelow
      (intToNatPosOfPos
        (intPowerPos isRadixPositive (targetExponent - value.exponent).toNat))
      (value.mantissa * intPower radix (value.exponent - targetExponent).toNat))

/-- **Round toward positive infinity** — the toward-zero template with the ceiling
quotient. -/
def roundTowardPositive (radix : Int) (value : RadixScaledInteger)
    (targetExponent : Int) : RadixScaledInteger :=
  { mantissa := intCeilQuotient
      (intPower radix (targetExponent - value.exponent).toNat).toNat
      (value.mantissa * intPower radix (value.exponent - targetExponent).toNat)
    exponent := targetExponent }

/-- The mantissa equation of ceiling rounding, definitional. -/
theorem roundTowardPositiveMantissa (radix : Int) (value : RadixScaledInteger)
    (targetExponent : Int) :
    (roundTowardPositive radix value targetExponent).mantissa =
      intCeilQuotient
        (intPower radix (targetExponent - value.exponent).toNat).toNat
        (value.mantissa *
          intPower radix (value.exponent - targetExponent).toNat) := rfl

/-- The exponent equation of ceiling rounding, definitional. -/
theorem roundTowardPositiveExponent (radix : Int) (value : RadixScaledInteger)
    (targetExponent : Int) :
    (roundTowardPositive radix value targetExponent).exponent =
      targetExponent := rfl

/-- **Ceiling rounds UP**: the original sits at or below the ceiling-rounded value
in the cross-aligned order — the dual bracket read at the common scale. -/
theorem roundTowardPositiveIsAbove {radix : Int}
    (isRadixPositive : (0 : Int) < radix) (value : RadixScaledInteger)
    (targetExponent : Int) :
    LessEqualAs radix value (roundTowardPositive radix value targetExponent) :=
  intLessEqualOfEqRight
    (intCeilQuotientMulIsAbove
      (intToNatPosOfPos
        (intPowerPos isRadixPositive (targetExponent - value.exponent).toNat))
      (value.mantissa * intPower radix (value.exponent - targetExponent).toNat))
    (congrArg
      (intCeilQuotient
        (intPower radix (targetExponent - value.exponent).toNat).toNat
        (value.mantissa *
          intPower radix (value.exponent - targetExponent).toNat) * ·)
      (intOfNatToNatOfNonNeg
        (intLessEqualOfLessThan
          (intPowerPos isRadixPositive
            (targetExponent - value.exponent).toNat))))

/-! ## The strict cross-aligned order + directed sub-ulp certificates

`LessThanAs` is the strict companion of `LessEqualAs` — one strict `Int` bound on the
cross-aligned mantissas.  Its first payoff: the directed modes land WITHIN ONE ULP.
One ulp at the target exponent is one unit of rounded mantissa, so the certificates
read: bumping the floor mantissa by one strictly overshoots the value, and dropping
the ceiling mantissa by one strictly undershoots it.  Each is the strict Int-layer
bracket at the common scale, with one right-distributivity step absorbing the extra
divisor into the corrected mantissa. -/

/-- **Strict cross-aligned order** — the strict companion of `LessEqualAs`. -/
def LessThanAs (radix : Int) (leftValue rightValue : RadixScaledInteger) : Prop :=
  crossAlignedMantissa radix leftValue rightValue <
    crossAlignedMantissa radix rightValue leftValue

/-- The strict order is decidable — it IS an `Int` strict bound (`Int.decLt` is
clean). -/
def decideLessThanAs (radix : Int) (leftValue rightValue : RadixScaledInteger) :
    Decidable (LessThanAs radix leftValue rightValue) :=
  Int.decLt (crossAlignedMantissa radix leftValue rightValue)
    (crossAlignedMantissa radix rightValue leftValue)

/-- Strict implies weak — `Int.lt` IS the unit-shifted `Int.le`, so one weakening
step. -/
theorem lessEqualAsOfLessThan {radix : Int} {leftValue rightValue : RadixScaledInteger}
    (isLessThan : LessThanAs radix leftValue rightValue) :
    LessEqualAs radix leftValue rightValue :=
  intLessEqualOfLessThan isLessThan

/-- **Floor lands within one ulp**: bumping the floor-rounded mantissa by ONE unit
(one ulp at the target exponent) strictly overshoots the original.  Together with
`roundTowardNegativeIsBelow`: floor ≤ value < floor + ulp.  The proof reads the
strict floor bracket at the common scale and folds `quotient·divisor + divisor` into
the successor mantissa by right-distributivity. -/
theorem roundTowardNegativeSuccessorIsAbove {radix : Int}
    (isRadixPositive : (0 : Int) < radix) (value : RadixScaledInteger)
    (targetExponent : Int) :
    LessThanAs radix value
      { mantissa := (roundTowardNegative radix value targetExponent).mantissa + 1,
        exponent := targetExponent } :=
  have divisorRoundTrip :
      Int.ofNat (intPower radix (targetExponent - value.exponent).toNat).toNat =
        intPower radix (targetExponent - value.exponent).toNat :=
    intOfNatToNatOfNonNeg
      (intLessEqualOfLessThan
        (intPowerPos isRadixPositive (targetExponent - value.exponent).toNat))
  intLessEqualOfEqRight
    (intFloorQuotientNextMultipleIsAbove
      (intToNatPosOfPos
        (intPowerPos isRadixPositive (targetExponent - value.exponent).toNat))
      (value.mantissa * intPower radix (value.exponent - targetExponent).toNat))
    ((congrArg
        (fun divisorImage =>
          intFloorQuotient
              (intPower radix (targetExponent - value.exponent).toNat).toNat
              (value.mantissa *
                intPower radix (value.exponent - targetExponent).toNat) *
              divisorImage +
            divisorImage)
        divisorRoundTrip).trans
      ((intRightDistrib
          (intFloorQuotient
            (intPower radix (targetExponent - value.exponent).toNat).toNat
            (value.mantissa *
              intPower radix (value.exponent - targetExponent).toNat))
          1 (intPower radix (targetExponent - value.exponent).toNat)).trans
        (congrArg
          (intFloorQuotient
              (intPower radix (targetExponent - value.exponent).toNat).toNat
              (value.mantissa *
                intPower radix (value.exponent - targetExponent).toNat) *
              intPower radix (targetExponent - value.exponent).toNat + ·)
          (intOneMul (intPower radix (targetExponent - value.exponent).toNat)))).symm)

/-- **Ceiling lands within one ulp**: dropping the ceiling-rounded mantissa by ONE
unit strictly undershoots the original.  Together with `roundTowardPositiveIsAbove`:
ceiling − ulp < value ≤ ceiling.  The proof shifts the strict ceiling bracket down by
the divisor and folds `quotient·divisor − divisor` into the predecessor mantissa. -/
theorem roundTowardPositivePredecessorIsBelow {radix : Int}
    (isRadixPositive : (0 : Int) < radix) (value : RadixScaledInteger)
    (targetExponent : Int) :
    LessThanAs radix
      { mantissa := (roundTowardPositive radix value targetExponent).mantissa - 1,
        exponent := targetExponent }
      value :=
  have divisorRoundTrip :
      Int.ofNat (intPower radix (targetExponent - value.exponent).toNat).toNat =
        intPower radix (targetExponent - value.exponent).toNat :=
    intOfNatToNatOfNonNeg
      (intLessEqualOfLessThan
        (intPowerPos isRadixPositive (targetExponent - value.exponent).toNat))
  have negatedUnitFactorFolds :
      (-1 : Int) * intPower radix (targetExponent - value.exponent).toNat =
        -intPower radix (targetExponent - value.exponent).toNat :=
    (intNegMul 1 (intPower radix (targetExponent - value.exponent).toNat)).trans
      (congrArg (fun productValue => -productValue)
        (intOneMul (intPower radix (targetExponent - value.exponent).toNat)))
  have quotientTimesDivisorFolds :
      intCeilQuotient
            (intPower radix (targetExponent - value.exponent).toNat).toNat
            (value.mantissa *
              intPower radix (value.exponent - targetExponent).toNat) *
          Int.ofNat (intPower radix (targetExponent - value.exponent).toNat).toNat +
          -Int.ofNat (intPower radix (targetExponent - value.exponent).toNat).toNat =
        (intCeilQuotient
            (intPower radix (targetExponent - value.exponent).toNat).toNat
            (value.mantissa *
              intPower radix (value.exponent - targetExponent).toNat) + -1) *
          intPower radix (targetExponent - value.exponent).toNat :=
    (congrArg
        (fun divisorImage =>
          intCeilQuotient
              (intPower radix (targetExponent - value.exponent).toNat).toNat
              (value.mantissa *
                intPower radix (value.exponent - targetExponent).toNat) *
              divisorImage +
            -divisorImage)
        divisorRoundTrip).trans
      ((intRightDistrib
          (intCeilQuotient
            (intPower radix (targetExponent - value.exponent).toNat).toNat
            (value.mantissa *
              intPower radix (value.exponent - targetExponent).toNat))
          (-1) (intPower radix (targetExponent - value.exponent).toNat)).trans
        (congrArg
          (intCeilQuotient
              (intPower radix (targetExponent - value.exponent).toNat).toNat
              (value.mantissa *
                intPower radix (value.exponent - targetExponent).toNat) *
              intPower radix (targetExponent - value.exponent).toNat + ·)
          negatedUnitFactorFolds)).symm
  have correctedSideCollapses :
      intCeilQuotient
            (intPower radix (targetExponent - value.exponent).toNat).toNat
            (value.mantissa *
              intPower radix (value.exponent - targetExponent).toNat) *
          Int.ofNat (intPower radix (targetExponent - value.exponent).toNat).toNat +
          1 +
          -Int.ofNat (intPower radix (targetExponent - value.exponent).toNat).toNat =
        (intCeilQuotient
            (intPower radix (targetExponent - value.exponent).toNat).toNat
            (value.mantissa *
              intPower radix (value.exponent - targetExponent).toNat) + -1) *
          intPower radix (targetExponent - value.exponent).toNat + 1 :=
    (intAddAssoc
        (intCeilQuotient
            (intPower radix (targetExponent - value.exponent).toNat).toNat
            (value.mantissa *
              intPower radix (value.exponent - targetExponent).toNat) *
          Int.ofNat (intPower radix (targetExponent - value.exponent).toNat).toNat)
        1
        (-Int.ofNat
          (intPower radix (targetExponent - value.exponent).toNat).toNat)).trans
      ((congrArg
          (intCeilQuotient
              (intPower radix (targetExponent - value.exponent).toNat).toNat
              (value.mantissa *
                intPower radix (value.exponent - targetExponent).toNat) *
              Int.ofNat
                (intPower radix (targetExponent - value.exponent).toNat).toNat + ·)
          (intAddComm 1
            (-Int.ofNat
              (intPower radix (targetExponent - value.exponent).toNat).toNat))).trans
        (((intAddAssoc
            (intCeilQuotient
                (intPower radix (targetExponent - value.exponent).toNat).toNat
                (value.mantissa *
                  intPower radix (value.exponent - targetExponent).toNat) *
              Int.ofNat
                (intPower radix (targetExponent - value.exponent).toNat).toNat)
            (-Int.ofNat
              (intPower radix (targetExponent - value.exponent).toNat).toNat)
            1).symm).trans
          (congrArg (· + 1) quotientTimesDivisorFolds)))
  have pumpedSideCollapses :
      value.mantissa * intPower radix (value.exponent - targetExponent).toNat +
          Int.ofNat (intPower radix (targetExponent - value.exponent).toNat).toNat +
          -Int.ofNat (intPower radix (targetExponent - value.exponent).toNat).toNat =
        value.mantissa * intPower radix (value.exponent - targetExponent).toNat :=
    (intAddAssoc
        (value.mantissa * intPower radix (value.exponent - targetExponent).toNat)
        (Int.ofNat (intPower radix (targetExponent - value.exponent).toNat).toNat)
        (-Int.ofNat
          (intPower radix (targetExponent - value.exponent).toNat).toNat)).trans
      ((congrArg
          (value.mantissa *
              intPower radix (value.exponent - targetExponent).toNat + ·)
          (intAddRightNeg
            (Int.ofNat
              (intPower radix (targetExponent - value.exponent).toNat).toNat))).trans
        (intAddZero
          (value.mantissa * intPower radix (value.exponent - targetExponent).toNat)))
  intLessEqualOfEqLeft correctedSideCollapses.symm
    (intLessEqualOfEqRight
      (intAddLeAddRight
        (intCeilQuotientPreviousMultipleIsBelow
          (intToNatPosOfPos
            (intPowerPos isRadixPositive (targetExponent - value.exponent).toNat))
          (value.mantissa * intPower radix (value.exponent - targetExponent).toNat))
        (-Int.ofNat (intPower radix (targetExponent - value.exponent).toNat).toNat))
      pumpedSideCollapses)

/-! ## The floor Galois property at the carrier

`roundTowardNegative` is the right adjoint to the inclusion of target-exponent
values: a value carried at the target exponent sits below the original iff it sits
below the floor rounding.  The backward direction is `roundTowardNegativeIsBelow` +
transitivity; the forward direction below is the Int-layer Galois adjunction read
through cross-alignment.  Monotonicity then falls out in two lines. -/

/-- **Floor is the greatest representable below** (the universal property): any
value carried at the target exponent that sits below the original also sits below
the floor rounding.  Cross-alignment turns the hypothesis into exactly the Galois
premise (the aligned witness mantissa times the divisor power is below the pumped
dividend), and the conclusion into the quotient bound scaled by the shared
self-gap power. -/
theorem roundTowardNegativeIsGreatestBelow {radix : Int}
    (isRadixPositive : (0 : Int) < radix) (value : RadixScaledInteger)
    {witnessMantissa targetExponent : Int}
    (isWitnessBelowValue : LessEqualAs radix
      { mantissa := witnessMantissa, exponent := targetExponent } value) :
    LessEqualAs radix { mantissa := witnessMantissa, exponent := targetExponent }
      (roundTowardNegative radix value targetExponent) :=
  intMulLeMulRightOfNonNeg
    (intLeFloorQuotientOfMulLe
      (intToNatPosOfPos
        (intPowerPos isRadixPositive (targetExponent - value.exponent).toNat))
      (intLessEqualOfEqLeft
        (congrArg (witnessMantissa * ·)
          (intOfNatToNatOfNonNeg
            (intLessEqualOfLessThan
              (intPowerPos isRadixPositive
                (targetExponent - value.exponent).toNat))))
        isWitnessBelowValue))
    (intLessEqualOfLessThan
      (intPowerPos isRadixPositive (targetExponent - targetExponent).toNat))

/-- **Floor monotonicity** — free from the Galois property: the floor of the left
value is carried at the target exponent and sits below the right value (below-left
chained with the order), hence below the right value's floor. -/
theorem roundTowardNegativeMonotone {radix : Int}
    (isRadixPositive : (0 : Int) < radix)
    {leftValue rightValue : RadixScaledInteger} (targetExponent : Int)
    (isOrdered : LessEqualAs radix leftValue rightValue) :
    LessEqualAs radix (roundTowardNegative radix leftValue targetExponent)
      (roundTowardNegative radix rightValue targetExponent) :=
  roundTowardNegativeIsGreatestBelow isRadixPositive rightValue
    (lessEqualAsTrans isRadixPositive
      (roundTowardNegativeIsBelow isRadixPositive leftValue targetExponent)
      isOrdered)

/-- **Ceiling is the least representable above** (the dual universal property): any
value carried at the target exponent that sits above the original also sits above
the ceiling rounding.  Cross-alignment turns the hypothesis into exactly the dual
Galois premise, and the conclusion into the quotient bound scaled by the shared
self-gap power. -/
theorem roundTowardPositiveIsLeastAbove {radix : Int}
    (isRadixPositive : (0 : Int) < radix) (value : RadixScaledInteger)
    {witnessMantissa targetExponent : Int}
    (isWitnessAboveValue : LessEqualAs radix value
      { mantissa := witnessMantissa, exponent := targetExponent }) :
    LessEqualAs radix (roundTowardPositive radix value targetExponent)
      { mantissa := witnessMantissa, exponent := targetExponent } :=
  intMulLeMulRightOfNonNeg
    (intCeilQuotientLeOfMantissaLeMul
      (intToNatPosOfPos
        (intPowerPos isRadixPositive (targetExponent - value.exponent).toNat))
      (intLessEqualOfEqRight isWitnessAboveValue
        (congrArg (witnessMantissa * ·)
          (intOfNatToNatOfNonNeg
            (intLessEqualOfLessThan
              (intPowerPos isRadixPositive
                (targetExponent - value.exponent).toNat))).symm)))
    (intLessEqualOfLessThan
      (intPowerPos isRadixPositive (targetExponent - targetExponent).toNat))

/-- **Ceiling monotonicity** — free from the dual Galois property: the ceiling of
the right value is carried at the target exponent and sits above the left value
(the order chained with above-right), hence above the left value's ceiling. -/
theorem roundTowardPositiveMonotone {radix : Int}
    (isRadixPositive : (0 : Int) < radix)
    {leftValue rightValue : RadixScaledInteger} (targetExponent : Int)
    (isOrdered : LessEqualAs radix leftValue rightValue) :
    LessEqualAs radix (roundTowardPositive radix leftValue targetExponent)
      (roundTowardPositive radix rightValue targetExponent) :=
  roundTowardPositiveIsLeastAbove isRadixPositive leftValue
    (lessEqualAsTrans isRadixPositive isOrdered
      (roundTowardPositiveIsAbove isRadixPositive rightValue targetExponent))

/-! ## Round to nearest, ties to even — the IEEE default mode

The toward-zero template with the nearest quotient.  Correctness is the HALF-ULP
certificate stated at DOUBLED common scale — `2 * |rounded - value| <= ulp` with no
division by two: twice the rounded value's aligned mantissa stays within one divisor
power (one ulp at the target exponent, read at the common scale) of twice the
original's aligned mantissa, on both sides.  Cross-alignment again turns each side
into the `Int`-layer doubled bracket verbatim — one `toNat` round-trip of the divisor
power plus one commutativity flip (the nearest brackets carry the divisor on the
LEFT of the product, where the floor/ceiling brackets carried it on the right). -/

/-- **Round to nearest, ties to even** — the toward-zero template with the nearest
quotient. -/
def roundNearestTiesEven (radix : Int) (value : RadixScaledInteger)
    (targetExponent : Int) : RadixScaledInteger :=
  { mantissa := intNearestEvenQuotient
      (intPower radix (targetExponent - value.exponent).toNat).toNat
      (value.mantissa * intPower radix (value.exponent - targetExponent).toNat)
    exponent := targetExponent }

/-- The mantissa equation of nearest rounding, definitional. -/
theorem roundNearestTiesEvenMantissa (radix : Int) (value : RadixScaledInteger)
    (targetExponent : Int) :
    (roundNearestTiesEven radix value targetExponent).mantissa =
      intNearestEvenQuotient
        (intPower radix (targetExponent - value.exponent).toNat).toNat
        (value.mantissa *
          intPower radix (value.exponent - targetExponent).toNat) := rfl

/-- The exponent equation of nearest rounding, definitional. -/
theorem roundNearestTiesEvenExponent (radix : Int) (value : RadixScaledInteger)
    (targetExponent : Int) :
    (roundNearestTiesEven radix value targetExponent).exponent =
      targetExponent := rfl

/-- **Doubled half-ulp, below**: at the doubled common scale the nearest-rounded
value never sits more than one ulp-at-the-target-exponent above the original — the
`Int`-layer doubled bracket read through cross-alignment. -/
theorem roundNearestTiesEvenMulTwiceIsBelow {radix : Int}
    (isRadixPositive : (0 : Int) < radix) (value : RadixScaledInteger)
    (targetExponent : Int) :
    2 * crossAlignedMantissa radix
        (roundNearestTiesEven radix value targetExponent) value ≤
      2 * crossAlignedMantissa radix value
          (roundNearestTiesEven radix value targetExponent) +
        intPower radix (targetExponent - value.exponent).toNat :=
  intLessEqualOfEqLeft
    (congrArg (2 * ·)
      ((congrArg
          (intNearestEvenQuotient
            (intPower radix (targetExponent - value.exponent).toNat).toNat
            (value.mantissa *
              intPower radix (value.exponent - targetExponent).toNat) * ·)
          (intOfNatToNatOfNonNeg
            (intLessEqualOfLessThan
              (intPowerPos isRadixPositive
                (targetExponent - value.exponent).toNat))).symm).trans
        (intMulComm
          (intNearestEvenQuotient
            (intPower radix (targetExponent - value.exponent).toNat).toNat
            (value.mantissa *
              intPower radix (value.exponent - targetExponent).toNat))
          (Int.ofNat
            (intPower radix (targetExponent - value.exponent).toNat).toNat))))
    (intLessEqualOfEqRight
      (intNearestEvenQuotientMulTwiceIsBelow
        (intToNatPosOfPos
          (intPowerPos isRadixPositive (targetExponent - value.exponent).toNat))
        (value.mantissa * intPower radix (value.exponent - targetExponent).toNat))
      (congrArg
        (2 * (value.mantissa *
          intPower radix (value.exponent - targetExponent).toNat) + ·)
        (intOfNatToNatOfNonNeg
          (intLessEqualOfLessThan
            (intPowerPos isRadixPositive
              (targetExponent - value.exponent).toNat)))))

/-- **Doubled half-ulp, above**: at the doubled common scale the original never sits
more than one ulp-at-the-target-exponent above the nearest-rounded value — the dual
doubled bracket.  Together with the below half this is `2 * |gap| <= ulp`. -/
theorem roundNearestTiesEvenMulTwiceIsAbove {radix : Int}
    (isRadixPositive : (0 : Int) < radix) (value : RadixScaledInteger)
    (targetExponent : Int) :
    2 * crossAlignedMantissa radix value
        (roundNearestTiesEven radix value targetExponent) ≤
      2 * crossAlignedMantissa radix
          (roundNearestTiesEven radix value targetExponent) value +
        intPower radix (targetExponent - value.exponent).toNat :=
  intLessEqualOfEqRight
    (intNearestEvenQuotientMulTwiceIsAbove
      (intToNatPosOfPos
        (intPowerPos isRadixPositive (targetExponent - value.exponent).toNat))
      (value.mantissa * intPower radix (value.exponent - targetExponent).toNat))
    ((congrArg
        (2 * · +
          Int.ofNat
            (intPower radix (targetExponent - value.exponent).toNat).toNat)
        ((intMulComm
            (Int.ofNat
              (intPower radix (targetExponent - value.exponent).toNat).toNat)
            (intNearestEvenQuotient
              (intPower radix (targetExponent - value.exponent).toNat).toNat
              (value.mantissa *
                intPower radix (value.exponent - targetExponent).toNat))).trans
          (congrArg
            (intNearestEvenQuotient
              (intPower radix (targetExponent - value.exponent).toNat).toNat
              (value.mantissa *
                intPower radix (value.exponent - targetExponent).toNat) * ·)
            (intOfNatToNatOfNonNeg
              (intLessEqualOfLessThan
                (intPowerPos isRadixPositive
                  (targetExponent - value.exponent).toNat)))))).trans
      (congrArg
        (2 * (intNearestEvenQuotient
          (intPower radix (targetExponent - value.exponent).toNat).toNat
          (value.mantissa *
            intPower radix (value.exponent - targetExponent).toNat) *
          intPower radix (targetExponent - value.exponent).toNat) + ·)
        (intOfNatToNatOfNonNeg
          (intLessEqualOfLessThan
            (intPowerPos isRadixPositive
              (targetExponent - value.exponent).toNat)))))

end RadixScaledInteger

end FX1Poly.ComputerAlgebra
