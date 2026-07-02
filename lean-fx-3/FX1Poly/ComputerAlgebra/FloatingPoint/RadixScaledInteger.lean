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

end RadixScaledInteger

end FX1Poly.ComputerAlgebra
