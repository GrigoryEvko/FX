import FX1Poly.ComputerAlgebra.Number.IntOrderAlgebra
import FX1Poly.ComputerAlgebra.Number.IntDistributivity
import FX1Poly.ComputerAlgebra.Float.FloatFormat

/-! # BlockScaled — MXFP4 / NVFP4 block-scaled quantization and the precision bridge

The microscaling model (OCP MX v1.0, NVIDIA NVFP4): a block of `blockSize`
low-precision elements (E2M1) shares one block scale.  The reconstructed value of
element `i` is `element_i * block_scale` — an exact product of two
`RadixScaledInteger`s (`mulExact`), so dequantization introduces no error of its
own; every bit of error lives in the per-element quantization, which the
`roundNearestTiesEven` half-ulp bracket certifies.

The precision bridge (dim-14 Precision) is `dequantizeErrorBound{Below,Above}`:
multiplying the exact block scale through the per-element doubled half-ulp bracket
scales the error linearly — the reconstructed quantized element stays within
`scale * (half-ulp)` of the reconstructed exact element.  The bridge rests on two
facts:

* `crossAlignedMantissaMulExactRight` — cross-alignment factors the shared scale
  out of a `mulExact` product (the block scale cancels in the exponent gap).
* `intMulLeOfNonnegLeft` — multiplying an `Int` `≤` by a nonnegative scalar
  preserves it.

`Init`-only, structural, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

open RadixScaledInteger

/-! ## Int scaffolding -/

/-- `(a + c) - (b + c) = a - b` — the shared summand cancels.  Init's cancellation
lemmas are propext-dirty; this rides the clean negation/associativity corpus. -/
theorem intAddSubAddRightCancel (leftValue rightValue shared : Int) :
    (leftValue + shared) - (rightValue + shared) = leftValue - rightValue :=
  (intSubEqAddNeg (leftValue + shared) (rightValue + shared)).trans
    ((congrArg ((leftValue + shared) + ·) (intNegAdd rightValue shared)).trans
      ((intAddAssoc leftValue shared (-rightValue + -shared)).trans
        ((congrArg (leftValue + ·)
            ((congrArg (shared + ·) (intAddComm (-rightValue) (-shared))).trans
              ((intAddAssoc shared (-shared) (-rightValue)).symm.trans
                ((congrArg (· + -rightValue) (intAddRightNeg shared)).trans
                  (intZeroAdd (-rightValue)))))).trans
          (intSubEqAddNeg leftValue rightValue).symm)))

/-- Multiplying an `Int` inequality on the left by a nonnegative scalar preserves it.
The scalar is an `ofNat` carrier, so the gap witness scales to the `Nat` product. -/
theorem intMulLeOfNonnegLeft {scaleValue leftValue rightValue : Int}
    (isNonnegative : (0 : Int) ≤ scaleValue) (isLessEqual : leftValue ≤ rightValue) :
    scaleValue * leftValue ≤ scaleValue * rightValue :=
  match intZeroLeDest isNonnegative, intLessEqualDest isLessEqual with
  | ⟨scaleNat, scaleEquation⟩, ⟨difference, differenceEquation⟩ =>
      let expandRight :
          scaleValue * rightValue = scaleValue * leftValue + Int.ofNat (scaleNat * difference) :=
        (congrArg (scaleValue * ·) differenceEquation).trans
          ((intLeftDistrib scaleValue leftValue (Int.ofNat difference)).trans
            (congrArg (scaleValue * leftValue + ·)
              (congrArg (· * Int.ofNat difference) scaleEquation)))
      intLessEqualOfEqRight
        (intLessEqualIntro (scaleValue * leftValue) (scaleNat * difference))
        expandRight.symm

/-- `scaleValue * (2 * inner) = 2 * (scaleValue * inner)` — pull the doubling out. -/
theorem intMulTwoSwap (scaleValue inner : Int) :
    scaleValue * (2 * inner) = 2 * (scaleValue * inner) :=
  (intMulAssoc scaleValue 2 inner).symm.trans
    ((congrArg (· * inner) (intMulComm scaleValue 2)).trans
      (intMulAssoc 2 scaleValue inner))

/-! ## Cross-alignment factors the shared scale out of `mulExact` -/

/-- The alignment gap between two `mulExact`-by-the-same-scale products equals the
gap between the original operands — the shared scale exponent cancels. -/
theorem scaleGapTowardMulExactRight (leftValue rightValue scale : RadixScaledInteger) :
    scaleGapToward (mulExact leftValue scale) (mulExact rightValue scale) =
      scaleGapToward leftValue rightValue :=
  congrArg Int.toNat
    (intAddSubAddRightCancel leftValue.exponent rightValue.exponent scale.exponent)

/-- Scale factoring: cross-aligning two `mulExact`-by-`scale` products pulls the
scale mantissa out in front of the operands' cross-alignment. -/
theorem crossAlignedMantissaMulExactRight (radix : Int)
    (leftValue rightValue scale : RadixScaledInteger) :
    crossAlignedMantissa radix (mulExact leftValue scale) (mulExact rightValue scale) =
      scale.mantissa * crossAlignedMantissa radix leftValue rightValue :=
  (congrArg
      (fun gap => (mulExact leftValue scale).mantissa * intPower radix gap)
      (scaleGapTowardMulExactRight leftValue rightValue scale)).trans
    ((congrArg (· * intPower radix (scaleGapToward leftValue rightValue))
        (mulExactMantissa leftValue scale)).trans
      ((intMulAssoc leftValue.mantissa scale.mantissa
          (intPower radix (scaleGapToward leftValue rightValue))).trans
        ((congrArg (leftValue.mantissa * ·)
            (intMulComm scale.mantissa
              (intPower radix (scaleGapToward leftValue rightValue)))).trans
          ((intMulAssoc leftValue.mantissa
              (intPower radix (scaleGapToward leftValue rightValue)) scale.mantissa).symm.trans
            (intMulComm
              (leftValue.mantissa * intPower radix (scaleGapToward leftValue rightValue))
              scale.mantissa)))))

/-- The doubled bracket scales by a nonnegative scale: multiplying both
operands by `scale` (with `0 ≤ scale.mantissa`) rescales the doubled half-ulp
bracket by `scale.mantissa`.  The engine of the precision bridge. -/
theorem crossAlignedBracketScaledByMul {radix : Int}
    (leftValue rightValue scale : RadixScaledInteger)
    (isScaleNonnegative : (0 : Int) ≤ scale.mantissa) (extra : Int)
    (bracket :
      2 * crossAlignedMantissa radix leftValue rightValue ≤
        2 * crossAlignedMantissa radix rightValue leftValue + extra) :
    2 * crossAlignedMantissa radix (mulExact leftValue scale) (mulExact rightValue scale) ≤
      2 * crossAlignedMantissa radix (mulExact rightValue scale) (mulExact leftValue scale) +
        scale.mantissa * extra :=
  let scaledBracket :
      scale.mantissa * (2 * crossAlignedMantissa radix leftValue rightValue) ≤
        scale.mantissa * (2 * crossAlignedMantissa radix rightValue leftValue + extra) :=
    intMulLeOfNonnegLeft isScaleNonnegative bracket
  let leftRewrite :
      scale.mantissa * (2 * crossAlignedMantissa radix leftValue rightValue) =
        2 * crossAlignedMantissa radix (mulExact leftValue scale) (mulExact rightValue scale) :=
    (intMulTwoSwap scale.mantissa (crossAlignedMantissa radix leftValue rightValue)).trans
      (congrArg (2 * ·) (crossAlignedMantissaMulExactRight radix leftValue rightValue scale).symm)
  let rightRewrite :
      scale.mantissa * (2 * crossAlignedMantissa radix rightValue leftValue + extra) =
        2 * crossAlignedMantissa radix (mulExact rightValue scale) (mulExact leftValue scale) +
          scale.mantissa * extra :=
    (intLeftDistrib scale.mantissa
        (2 * crossAlignedMantissa radix rightValue leftValue) extra).trans
      (congrArg (· + scale.mantissa * extra)
        ((intMulTwoSwap scale.mantissa (crossAlignedMantissa radix rightValue leftValue)).trans
          (congrArg (2 * ·)
            (crossAlignedMantissaMulExactRight radix rightValue leftValue scale).symm)))
  intLessEqualOfEqRight (intLessEqualOfEqLeft leftRewrite.symm scaledBracket) rightRewrite

/-! ## The block formats + the block model -/

/-- A block-scaled format: a per-element format sharing one block scale format over
`blockSize` elements. -/
structure BlockScaleFormat where
  elementFormat : FloatFormat
  scaleFormat   : FloatFormat
  blockSize     : Nat

/-- OCP MX E8M0 shared scale: exponent-only (8 bits, bias 127), pure powers of two
— a single implicit-`1.0` significand, radix 2, exponent range `[-127, 127]`. -/
def e8m0Scale : FloatFormat := { radix := 2, precision := 1, emin := -127, emax := 127 }

/-- MXFP4 (OCP MX v1.0): E2M1 elements, E8M0 power-of-two block scale, 32-element
blocks. -/
def mxfp4 : BlockScaleFormat :=
  { elementFormat := FloatFormat.fp4E2M1, scaleFormat := e8m0Scale, blockSize := 32 }

/-- NVFP4 (NVIDIA Blackwell): E2M1 elements, FP8 E4M3 real-valued block scale,
16-element blocks. -/
def nvfp4 : BlockScaleFormat :=
  { elementFormat := FloatFormat.fp4E2M1, scaleFormat := FloatFormat.fp8E4M3, blockSize := 16 }

/-- A concrete block: one shared scale + a list of exact element values. -/
structure ScaledBlock where
  scale    : RadixScaledInteger
  elements : List RadixScaledInteger

/-- Reconstruct one element: the exact product of the element value and the block
scale — no rounding, so no dequantization error. -/
def dequantizeElement (scale element : RadixScaledInteger) : RadixScaledInteger :=
  mulExact element scale

/-- Reconstruct a whole block: map exact reconstruction over the elements. -/
def dequantize (block : ScaledBlock) : List RadixScaledInteger :=
  block.elements.map (dequantizeElement block.scale)

/-- The reconstructed mantissa is exactly `element.mantissa * scale.mantissa`. -/
theorem dequantizeElementMantissa (scale element : RadixScaledInteger) :
    (dequantizeElement scale element).mantissa = element.mantissa * scale.mantissa :=
  mulExactMantissa element scale

/-- The reconstructed exponent is exactly `element.exponent + scale.exponent`. -/
theorem dequantizeElementExponent (scale element : RadixScaledInteger) :
    (dequantizeElement scale element).exponent = element.exponent + scale.exponent :=
  mulExactExponent element scale

/-- `map` preserves length — structural on the list (Init's `List.length_map` is
proved by `simp` and pulls `propext`). -/
theorem listMapLength {ElemType ResultType : Type} (mapping : ElemType → ResultType) :
    ∀ values : List ElemType, (values.map mapping).length = values.length
  | [] => rfl
  | _ :: rest => congrArg (· + 1) (listMapLength mapping rest)

/-- Dequantization preserves the block length (one reconstructed value per element). -/
theorem dequantizeLength (block : ScaledBlock) :
    (dequantize block).length = block.elements.length :=
  listMapLength (dequantizeElement block.scale) block.elements

/-! ## The precision bridge: block reconstruction scales the per-element half-ulp

For an element quantized as `roundNearestTiesEven radix exactElement targetExponent`
with a nonnegative block scale, the reconstructed quantized value stays within
`scale.mantissa * (one ulp)` of the reconstructed exact value — both directions. -/

/-- Reconstructed quantized element stays within a scaled half-ulp above. -/
theorem dequantizeErrorBoundBelow {radix : Int} (isRadixPositive : (0 : Int) < radix)
    (exactElement scale : RadixScaledInteger) (isScaleNonnegative : (0 : Int) ≤ scale.mantissa)
    (targetExponent : Int) :
    2 * crossAlignedMantissa radix
        (dequantizeElement scale (RadixScaledInteger.roundNearestTiesEven radix exactElement targetExponent))
        (dequantizeElement scale exactElement) ≤
      2 * crossAlignedMantissa radix
          (dequantizeElement scale exactElement)
          (dequantizeElement scale (RadixScaledInteger.roundNearestTiesEven radix exactElement targetExponent)) +
        scale.mantissa * intPower radix (targetExponent - exactElement.exponent).toNat :=
  crossAlignedBracketScaledByMul
    (RadixScaledInteger.roundNearestTiesEven radix exactElement targetExponent) exactElement scale
    isScaleNonnegative (intPower radix (targetExponent - exactElement.exponent).toNat)
    (RadixScaledInteger.roundNearestTiesEvenMulTwiceIsBelow isRadixPositive exactElement targetExponent)

/-- Reconstructed exact element stays within a scaled half-ulp above the quantized. -/
theorem dequantizeErrorBoundAbove {radix : Int} (isRadixPositive : (0 : Int) < radix)
    (exactElement scale : RadixScaledInteger) (isScaleNonnegative : (0 : Int) ≤ scale.mantissa)
    (targetExponent : Int) :
    2 * crossAlignedMantissa radix
        (dequantizeElement scale exactElement)
        (dequantizeElement scale (RadixScaledInteger.roundNearestTiesEven radix exactElement targetExponent)) ≤
      2 * crossAlignedMantissa radix
          (dequantizeElement scale (RadixScaledInteger.roundNearestTiesEven radix exactElement targetExponent))
          (dequantizeElement scale exactElement) +
        scale.mantissa * intPower radix (targetExponent - exactElement.exponent).toNat :=
  crossAlignedBracketScaledByMul
    exactElement (RadixScaledInteger.roundNearestTiesEven radix exactElement targetExponent) scale
    isScaleNonnegative (intPower radix (targetExponent - exactElement.exponent).toNat)
    (RadixScaledInteger.roundNearestTiesEvenMulTwiceIsAbove isRadixPositive exactElement targetExponent)

end FX1Poly.ComputerAlgebra
