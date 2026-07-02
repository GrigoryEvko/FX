import FX1Poly.ComputerAlgebra.Number.IntNegation
import FX1Poly.ComputerAlgebra.Number.IntPower
import FX1Poly.ComputerAlgebra.Number.IntCancellation
import FX1Poly.ComputerAlgebra.Number.IntToNatCycle

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
common scale via `intMulPowerRightCancel`), exact multiplication, and the first
semantic theorem:
`shiftToLowerScalePreservesDenotation` — rescaling a value to a lower exponent by
multiplying its mantissa with `radix ^ shift` denotes the same value.  Two generic Int
cancellation helpers (`intAddNegSwapCancel` / `intSubSubSelfCancel`) live here until a
second consumer promotes them to `Number/`; the `toNat` computation pins were promoted
to `Number/IntToNatCycle` when the cycle balance became their second consumer.

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

end RadixScaledInteger

end FX1Poly.ComputerAlgebra
