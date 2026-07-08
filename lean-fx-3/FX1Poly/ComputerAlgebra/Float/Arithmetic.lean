import FX1Poly.ComputerAlgebra.Float.FloatFormat

/-! # Float arithmetic — exact-then-round total operations

The IEEE "compute the infinitely-precise result, then round once" model
(fx_design.md §3.11).  Each operation forms the EXACT `RadixScaledInteger`
result via the shipped `addExact` / `mulExact` (never evaluated into ℝ), then
rounds it to the target canonical exponent with `roundNearestToExponent`.  The
correctness contract is inherited verbatim: the rounded result lies within one
half-ulp of the exact result, since its `toRadixScaled` IS
`roundNearestTiesEven` applied to the exact operand (`toRadixScaled_add/mul`),
and the shipped doubled half-ulp bracket applies at that operand.

`Init`-only (via the shipped siblings), structural, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

open RadixScaledInteger

/-- Exact negation: flip the mantissa sign, keep the scale. -/
def negateExact (value : RadixScaledInteger) : RadixScaledInteger :=
  { mantissa := -value.mantissa, exponent := value.exponent }

/-- The mantissa equation of exact negation, definitional. -/
theorem negateExactMantissa (value : RadixScaledInteger) :
    (negateExact value).mantissa = -value.mantissa := rfl

/-- The exponent equation of exact negation, definitional. -/
theorem negateExactExponent (value : RadixScaledInteger) :
    (negateExact value).exponent = value.exponent := rfl

/-! ## Rounded operations -/

/-- Rounded addition: exact sum, then nearest-round to `targetExponent`. -/
def addRounded (fmt : FloatFormat) (targetExponent : Int)
    (leftSummand rightSummand : RadixScaledInteger) : BinaryFloat :=
  roundNearestToExponent fmt (addExact fmt.radix leftSummand rightSummand) targetExponent

/-- Rounded subtraction: exact `left + (-right)`, then nearest-round. -/
def subRounded (fmt : FloatFormat) (targetExponent : Int)
    (leftSummand rightSummand : RadixScaledInteger) : BinaryFloat :=
  roundNearestToExponent fmt
    (addExact fmt.radix leftSummand (negateExact rightSummand)) targetExponent

/-- Rounded multiplication: exact product, then nearest-round. -/
def mulRounded (fmt : FloatFormat) (targetExponent : Int)
    (leftFactor rightFactor : RadixScaledInteger) : BinaryFloat :=
  roundNearestToExponent fmt (mulExact leftFactor rightFactor) targetExponent

/-! ## Each op reads back as nearest-rounding of the exact result -/

/-- The rounded sum reads back as nearest-rounding of the EXACT sum. -/
theorem toRadixScaled_addRounded (fmt : FloatFormat) (targetExponent : Int)
    (leftSummand rightSummand : RadixScaledInteger) :
    BinaryFloat.toRadixScaled (addRounded fmt targetExponent leftSummand rightSummand) =
      RadixScaledInteger.roundNearestTiesEven fmt.radix
        (addExact fmt.radix leftSummand rightSummand) targetExponent :=
  toRadixScaled_roundNearestToExponent fmt (addExact fmt.radix leftSummand rightSummand) targetExponent

/-- The rounded difference reads back as nearest-rounding of the EXACT difference. -/
theorem toRadixScaled_subRounded (fmt : FloatFormat) (targetExponent : Int)
    (leftSummand rightSummand : RadixScaledInteger) :
    BinaryFloat.toRadixScaled (subRounded fmt targetExponent leftSummand rightSummand) =
      RadixScaledInteger.roundNearestTiesEven fmt.radix
        (addExact fmt.radix leftSummand (negateExact rightSummand)) targetExponent :=
  toRadixScaled_roundNearestToExponent fmt
    (addExact fmt.radix leftSummand (negateExact rightSummand)) targetExponent

/-- The rounded product reads back as nearest-rounding of the EXACT product. -/
theorem toRadixScaled_mulRounded (fmt : FloatFormat) (targetExponent : Int)
    (leftFactor rightFactor : RadixScaledInteger) :
    BinaryFloat.toRadixScaled (mulRounded fmt targetExponent leftFactor rightFactor) =
      RadixScaledInteger.roundNearestTiesEven fmt.radix
        (mulExact leftFactor rightFactor) targetExponent :=
  toRadixScaled_roundNearestToExponent fmt (mulExact leftFactor rightFactor) targetExponent

/-! ## Rounded ops land within one half-ulp of the exact result

The doubled half-ulp bracket (`2 * |rounded - exact| <= ulp`, both directions)
applied at the exact operand — the exact-then-round correctness certificate. -/

/-- Rounded addition is within half an ulp of the exact sum (below bracket). -/
theorem addRoundedErrorBoundBelow {fmt : FloatFormat}
    (isRadixPositive : (0 : Int) < fmt.radix) (targetExponent : Int)
    (leftSummand rightSummand : RadixScaledInteger) :
    2 * crossAlignedMantissa fmt.radix
        (BinaryFloat.toRadixScaled (addRounded fmt targetExponent leftSummand rightSummand))
        (addExact fmt.radix leftSummand rightSummand) ≤
      2 * crossAlignedMantissa fmt.radix
          (addExact fmt.radix leftSummand rightSummand)
          (BinaryFloat.toRadixScaled (addRounded fmt targetExponent leftSummand rightSummand)) +
        intPower fmt.radix
          (targetExponent - (addExact fmt.radix leftSummand rightSummand).exponent).toNat :=
  roundNearestErrorBoundBelow isRadixPositive
    (addExact fmt.radix leftSummand rightSummand) targetExponent

/-- Rounded addition is within half an ulp of the exact sum (above bracket). -/
theorem addRoundedErrorBoundAbove {fmt : FloatFormat}
    (isRadixPositive : (0 : Int) < fmt.radix) (targetExponent : Int)
    (leftSummand rightSummand : RadixScaledInteger) :
    2 * crossAlignedMantissa fmt.radix
        (addExact fmt.radix leftSummand rightSummand)
        (BinaryFloat.toRadixScaled (addRounded fmt targetExponent leftSummand rightSummand)) ≤
      2 * crossAlignedMantissa fmt.radix
          (BinaryFloat.toRadixScaled (addRounded fmt targetExponent leftSummand rightSummand))
          (addExact fmt.radix leftSummand rightSummand) +
        intPower fmt.radix
          (targetExponent - (addExact fmt.radix leftSummand rightSummand).exponent).toNat :=
  roundNearestErrorBoundAbove isRadixPositive
    (addExact fmt.radix leftSummand rightSummand) targetExponent

/-- Rounded multiplication is within half an ulp of the exact product (below). -/
theorem mulRoundedErrorBoundBelow {fmt : FloatFormat}
    (isRadixPositive : (0 : Int) < fmt.radix) (targetExponent : Int)
    (leftFactor rightFactor : RadixScaledInteger) :
    2 * crossAlignedMantissa fmt.radix
        (BinaryFloat.toRadixScaled (mulRounded fmt targetExponent leftFactor rightFactor))
        (mulExact leftFactor rightFactor) ≤
      2 * crossAlignedMantissa fmt.radix
          (mulExact leftFactor rightFactor)
          (BinaryFloat.toRadixScaled (mulRounded fmt targetExponent leftFactor rightFactor)) +
        intPower fmt.radix
          (targetExponent - (mulExact leftFactor rightFactor).exponent).toNat :=
  roundNearestErrorBoundBelow isRadixPositive (mulExact leftFactor rightFactor) targetExponent

/-- Rounded multiplication is within half an ulp of the exact product (above). -/
theorem mulRoundedErrorBoundAbove {fmt : FloatFormat}
    (isRadixPositive : (0 : Int) < fmt.radix) (targetExponent : Int)
    (leftFactor rightFactor : RadixScaledInteger) :
    2 * crossAlignedMantissa fmt.radix
        (mulExact leftFactor rightFactor)
        (BinaryFloat.toRadixScaled (mulRounded fmt targetExponent leftFactor rightFactor)) ≤
      2 * crossAlignedMantissa fmt.radix
          (BinaryFloat.toRadixScaled (mulRounded fmt targetExponent leftFactor rightFactor))
          (mulExact leftFactor rightFactor) +
        intPower fmt.radix
          (targetExponent - (mulExact leftFactor rightFactor).exponent).toNat :=
  roundNearestErrorBoundAbove isRadixPositive (mulExact leftFactor rightFactor) targetExponent

end FX1Poly.ComputerAlgebra
