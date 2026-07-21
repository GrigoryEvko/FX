import FX1Poly.ComputerAlgebra.FloatingPoint.RadixScaledInteger

/-! # FloatFormat — the radix-generic float ADT, rounding-into-a-format, and the
    half-ulp error bound

The format layer over the exact-value substrate (fx_design.md §3.11 floating-point
control).  `RadixScaledInteger` = `mantissa * radix^exponent`, never evaluated into
ℝ, together with the full IEEE rounding suite — `roundTowardZero` /
`roundTowardNegative` / `roundTowardPositive` / `roundNearestTiesEven`, each with
its faithfulness + monotonicity + sub-ulp certificate — live in
`FX1Poly/ComputerAlgebra/FloatingPoint/RadixScaledInteger.lean`.

This file follows Flocq's `SpecFloat` / `Binary` split:

* `FloatFormat` — the four numbers `(radix, precision, emin, emax)` that pin a
  concrete format (binary16/32/64, FP8 E4M3/E5M2, FP4 E2M1, dec*).  A `def`
  bundle, not a proof-carrying subtype — positivity of the radix travels as an
  explicit hypothesis, exactly as the rounding theorems demand.

* `BinaryFloat` — the proof-free IEEE ADT (`Flocq.SpecFloat.spec_float`):
  `posZero / negZero / posInf / negInf / nan / finite (sign) (mantissa) (exp)`.
  Its real reading `toRadixScaled` (Flocq `B2R`) sends every non-finite to the
  zero value and a finite to its exact `RadixScaledInteger`.

* `roundNearestToExponent` — round an exact `RadixScaledInteger` to a target
  canonical exponent, delivered as a `BinaryFloat` (sign split off the rounded
  mantissa).  Its `toRadixScaled` is definitionally the `roundNearestTiesEven`, so
  the doubled half-ulp bound `2 * |rounded - value| <= ulp` and the faithfulness
  disjunction lift to the float layer by `congrArg`.

`Init`-only (via the sibling module), structural, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

open RadixScaledInteger

/-! ## The format bundle -/

/-- A concrete floating-point format: values are `mantissa * radix^exponent` with
`mantissa` below `radix^precision` and `emin <= exponent <= emax`.  Radix 2 gives
the IEEE binary formats and the ML low-precision formats; radix 10 gives the
spec's `dec*` decimal family. -/
structure FloatFormat where
  radix     : Int
  precision : Nat
  emin      : Int
  emax      : Int

namespace FloatFormat

/-- IEEE binary16 (half): radix 2, 11 significant bits (10 stored + hidden),
normal exponent range `[-14, 15]`. -/
def binary16 : FloatFormat := { radix := 2, precision := 11, emin := -14, emax := 15 }

/-- IEEE binary32 (single): radix 2, 24 significant bits, `[-126, 127]`. -/
def binary32 : FloatFormat := { radix := 2, precision := 24, emin := -126, emax := 127 }

/-- IEEE binary64 (double): radix 2, 53 significant bits, `[-1022, 1023]`. -/
def binary64 : FloatFormat := { radix := 2, precision := 53, emin := -1022, emax := 1023 }

/-- OCP OFP8 E4M3: radix 2, 4 significant bits (3 stored + hidden), bias 7, no Inf. -/
def fp8E4M3 : FloatFormat := { radix := 2, precision := 4, emin := -6, emax := 8 }

/-- OCP OFP8 E5M2: radix 2, 3 significant bits, bias 15, IEEE-like Inf/NaN. -/
def fp8E5M2 : FloatFormat := { radix := 2, precision := 3, emin := -14, emax := 15 }

/-- OCP MX / NVFP4 element E2M1: radix 2, 2 significant bits, bias 1, no Inf/NaN. -/
def fp4E2M1 : FloatFormat := { radix := 2, precision := 2, emin := 0, emax := 2 }

end FloatFormat

/-! ## The IEEE ADT (proof-free, computational — Flocq `spec_float`) -/

/-- An IEEE-754 value as a finite/special tagged union.  Proof-free: the
format-membership certificate is a separate predicate (`IsCanonicalFinite`), so
the carrier is fully inductive and axiom-clean. -/
inductive BinaryFloat where
  | posZero
  | negZero
  | posInf
  | negInf
  | nan
  | finite (sign : Bool) (mantissa : Nat) (exponent : Int)

namespace BinaryFloat

/-- Reconstruct a signed `Int` from a sign bit and a magnitude, matched to the
`Int` constructors so the round-trip through the constructors is definitional:
`false` is `ofNat`, `true` is `negOfNat` (`negOfNat (n+1) = negSucc n`). -/
def signedMantissa (sign : Bool) (magnitude : Nat) : Int :=
  match sign with
  | false => Int.ofNat magnitude
  | true  => Int.negOfNat magnitude

/-- Build a finite float from a signed mantissa by peeling the sign off the `Int`
constructor — `ofNat` is nonnegative, `negSucc` is strictly negative. -/
def ofSignedMantissa (mantissa : Int) (exponent : Int) : BinaryFloat :=
  match mantissa with
  | Int.ofNat magnitude    => .finite false magnitude exponent
  | Int.negSucc predecessor => .finite true (predecessor + 1) exponent

/-- The exact real reading (Flocq `B2R`): a finite maps to its exact
`RadixScaledInteger`; every non-finite maps to the zero value. -/
def toRadixScaled : BinaryFloat → RadixScaledInteger
  | .finite sign magnitude exponent => { mantissa := signedMantissa sign magnitude, exponent := exponent }
  | .posZero => { mantissa := 0, exponent := 0 }
  | .negZero => { mantissa := 0, exponent := 0 }
  | .posInf  => { mantissa := 0, exponent := 0 }
  | .negInf  => { mantissa := 0, exponent := 0 }
  | .nan     => { mantissa := 0, exponent := 0 }

/-- `ofSignedMantissa` reads back exactly the signed mantissa and exponent it was
built from — both `Int` constructors close by `rfl`. -/
theorem toRadixScaled_ofSignedMantissa (mantissa : Int) (exponent : Int) :
    toRadixScaled (ofSignedMantissa mantissa exponent) = { mantissa := mantissa, exponent := exponent } :=
  match mantissa with
  | Int.ofNat _    => rfl
  | Int.negSucc _  => rfl

/-! ## Classifiers -/

/-- Is this a finite value (not an infinity or a NaN)? -/
def isFinite : BinaryFloat → Bool
  | .posZero => true
  | .negZero => true
  | .finite _ _ _ => true
  | .posInf => false
  | .negInf => false
  | .nan    => false

/-- Is this a NaN? -/
def isNaN : BinaryFloat → Bool
  | .nan => true
  | .posZero => false
  | .negZero => false
  | .posInf  => false
  | .negInf  => false
  | .finite _ _ _ => false

/-- Is this an infinity (either sign)? -/
def isInfinite : BinaryFloat → Bool
  | .posInf => true
  | .negInf => true
  | .posZero => false
  | .negZero => false
  | .nan     => false
  | .finite _ _ _ => false

/-- Is this a zero (either sign)? -/
def isZero : BinaryFloat → Bool
  | .posZero => true
  | .negZero => true
  | .posInf  => false
  | .negInf  => false
  | .nan     => false
  | .finite _ _ _ => false

/-- Format-membership certificate for a finite value: the magnitude is below
`radix^precision` and the exponent lies in `[emin, emax]`.  This is Flocq's
`bounded` predicate, kept out of the carrier. -/
def IsCanonicalFinite (fmt : FloatFormat) : BinaryFloat → Prop
  | .finite _ magnitude exponent =>
      Int.ofNat magnitude < intPower fmt.radix fmt.precision ∧
        fmt.emin ≤ exponent ∧ exponent ≤ fmt.emax
  | .posZero => False
  | .negZero => False
  | .posInf  => False
  | .negInf  => False
  | .nan     => False

end BinaryFloat

/-! ## Rounding an exact value into the format

`roundNearestToExponent fmt value targetExponent` rounds the exact
`RadixScaledInteger` `value` to the nearest representable at `targetExponent`
(ties to even), and returns it as a `BinaryFloat`.  Its exact reading is
definitionally `RadixScaledInteger.roundNearestTiesEven`, so the correctness
certificates lift verbatim. -/

/-- Round `value` to nearest, ties-to-even, at `targetExponent`, delivered as a
`BinaryFloat`. -/
def roundNearestToExponent (fmt : FloatFormat) (value : RadixScaledInteger)
    (targetExponent : Int) : BinaryFloat :=
  BinaryFloat.ofSignedMantissa
    (RadixScaledInteger.roundNearestTiesEven fmt.radix value targetExponent).mantissa
    targetExponent

/-- The rounded float reads back as exactly the nearest-rounded exact value — the
bridge that carries every certificate to the float layer. -/
theorem toRadixScaled_roundNearestToExponent (fmt : FloatFormat) (value : RadixScaledInteger)
    (targetExponent : Int) :
    BinaryFloat.toRadixScaled (roundNearestToExponent fmt value targetExponent) =
      RadixScaledInteger.roundNearestTiesEven fmt.radix value targetExponent :=
  BinaryFloat.toRadixScaled_ofSignedMantissa
    (RadixScaledInteger.roundNearestTiesEven fmt.radix value targetExponent).mantissa
    targetExponent

/-! ## The half-ulp error bound at the float layer

The two doubled-bracket inequalities, transported through the
`toRadixScaled = roundNearestTiesEven` bridge.  Together they are
`2 * |rounded - value| <= ulp` where the ulp is `radix^(targetExponent -
value.exponent)` read at the common (lower) scale. -/

/-- Rounded stays within half an ulp above (doubled, no division by two). -/
theorem roundNearestErrorBoundBelow {fmt : FloatFormat}
    (isRadixPositive : (0 : Int) < fmt.radix) (value : RadixScaledInteger)
    (targetExponent : Int) :
    2 * crossAlignedMantissa fmt.radix
        (BinaryFloat.toRadixScaled (roundNearestToExponent fmt value targetExponent)) value ≤
      2 * crossAlignedMantissa fmt.radix value
          (BinaryFloat.toRadixScaled (roundNearestToExponent fmt value targetExponent)) +
        intPower fmt.radix (targetExponent - value.exponent).toNat :=
  (congrArg
      (fun rounded =>
        2 * crossAlignedMantissa fmt.radix rounded value ≤
          2 * crossAlignedMantissa fmt.radix value rounded +
            intPower fmt.radix (targetExponent - value.exponent).toNat)
      (toRadixScaled_roundNearestToExponent fmt value targetExponent)).mpr
    (RadixScaledInteger.roundNearestTiesEvenMulTwiceIsBelow isRadixPositive value targetExponent)

/-- The value stays within half an ulp above the rounded (doubled dual). -/
theorem roundNearestErrorBoundAbove {fmt : FloatFormat}
    (isRadixPositive : (0 : Int) < fmt.radix) (value : RadixScaledInteger)
    (targetExponent : Int) :
    2 * crossAlignedMantissa fmt.radix value
        (BinaryFloat.toRadixScaled (roundNearestToExponent fmt value targetExponent)) ≤
      2 * crossAlignedMantissa fmt.radix
          (BinaryFloat.toRadixScaled (roundNearestToExponent fmt value targetExponent)) value +
        intPower fmt.radix (targetExponent - value.exponent).toNat :=
  (congrArg
      (fun rounded =>
        2 * crossAlignedMantissa fmt.radix value rounded ≤
          2 * crossAlignedMantissa fmt.radix rounded value +
            intPower fmt.radix (targetExponent - value.exponent).toNat)
      (toRadixScaled_roundNearestToExponent fmt value targetExponent)).mpr
    (RadixScaledInteger.roundNearestTiesEvenMulTwiceIsAbove isRadixPositive value targetExponent)

/-- Faithfulness at the float layer: the rounded value is one of the two
directed roundings (floor toward `-inf`, ceiling toward `+inf`) at the target
exponent — never anything in between. -/
theorem roundNearestIsFaithful {fmt : FloatFormat}
    (isRadixPositive : (0 : Int) < fmt.radix) (value : RadixScaledInteger)
    (targetExponent : Int) :
    BinaryFloat.toRadixScaled (roundNearestToExponent fmt value targetExponent) =
        RadixScaledInteger.roundTowardNegative fmt.radix value targetExponent ∨
      BinaryFloat.toRadixScaled (roundNearestToExponent fmt value targetExponent) =
        RadixScaledInteger.roundTowardPositive fmt.radix value targetExponent :=
  match RadixScaledInteger.roundNearestTiesEvenIsFaithful isRadixPositive value targetExponent with
  | .inl isFloor =>
      .inl ((toRadixScaled_roundNearestToExponent fmt value targetExponent).trans isFloor)
  | .inr isCeil =>
      .inr ((toRadixScaled_roundNearestToExponent fmt value targetExponent).trans isCeil)

end FX1Poly.ComputerAlgebra
