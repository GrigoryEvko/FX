import FX1Poly.ComputerAlgebra.Number.ComplexRealTriangleInequality

/-! # ComplexRealModulusComponentBounds — the ℂ modulus component estimates (NUM-C-5)

The pointwise component bounds on the Gaussian-real modulus, clean corollaries of
the just-shipped square-root monotonicity layer (`sqrtRealMonotone`,
`selfLeSqrtRealSquare`) and the square-order reflection (`nonNegSquareOrderReflect`).
These are the elementary inequalities complex analysis leans on toward the
Fundamental Theorem of Algebra:

* `modulusDominatesRealPart` / `negRealPartLeModulus` — `±Re z ≤ |z|`;
* `modulusDominatesImaginaryPart` / `negImaginaryPartLeModulus` — `±Im z ≤ |z|`;
* `modulusLeComponentAbsSum` — `|z| ≤ |Re z| + |Im z|`.

The single new ℝ brick is the self-plus-nonnegative order fact
`lessEqualRealSelfAddNonNegRight` (`x ≤ x + y` for `y ≥ 0`), which reduces to
`realNonNegativeRespectsDenotesSame` on the cancellation identity
`(x + y) − x ~ y`.  Every component estimate then reads off the chain
`c ≤ √(c²) ≤ √(c² + d²) = |z|` (the middle step by `sqrtRealMonotone` on
`c² ≤ c² + d²`), and the abs-sum estimate reflects
`|z|² = |Re z|² + |Im z|² ≤ (|Re z| + |Im z|)²` back through the nonnegative
square root by `nonNegSquareOrderReflect`.

## Zero-axiom

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`, `WellFounded.fix`.  Pure term composition of the shipped monotone/self/
reflect lemmas and ℝ-ring congruences; no real order or equality is ever
case-split.  Per-declaration gated in the audit twin. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The self-plus-nonnegative real order brick (NUM-C-5a) -/

/-- **A real sits below itself plus any nonnegative real** — `x ≤ x + y` from
`y ≥ 0`.  The added value is recovered from the sum (`(x + y) − x ~ y`), and a
pointwise-nonnegative real clears the vanishing lower bound at every index; the
setoid-invariance of that nonnegativity carries the bound onto the difference
`(x + y) − x`, which is exactly `LessEqualReal x (x + y)`. -/
theorem lessEqualRealSelfAddNonNegRight (baseValue : RegularReal)
    {addend : RegularReal} (isAddendNonNegative : IsNonNegativeReal addend) :
    LessEqualReal baseValue (addReal baseValue addend) :=
  realNonNegativeRespectsDenotesSame
    (denotesSameRealSymm (subRealAddLeftCancelDenotesSame baseValue addend))
    (realVanishingLowerBoundOfNonNeg isAddendNonNegative)

/-! ## The real-part component bounds (NUM-C-5b) -/

/-- **The modulus dominates the real part** — `Re z ≤ |z|`.  The chain
`Re z ≤ √((Re z)²)` (`selfLeSqrtRealSquare`) `≤ √((Re z)² + (Im z)²) = |z|`
(`sqrtRealMonotone` on `(Re z)² ≤ (Re z)² + (Im z)²`, the imaginary square being
nonnegative). -/
theorem modulusDominatesRealPart (value : ComplexReal) :
    LessEqualReal value.realPart (modulus value) :=
  lessEqualRealTrans
    (selfLeSqrtRealSquare value.realPart)
    (sqrtRealMonotone
      (mulRealSelfIsNonNegativeReal value.realPart)
      (modulusSquaredIsNonNegativeReal value)
      (lessEqualRealSelfAddNonNegRight
        (mulReal value.realPart value.realPart)
        (mulRealSelfIsNonNegativeReal value.imaginaryPart)))

/-- **The negated real part is dominated by the modulus** — `−Re z ≤ |z|`, i.e.
`−|z| ≤ Re z`.  Same chain applied to `−Re z`, using the sign-blind square
`(−Re z)² ~ (Re z)²` to relocate the left endpoint of the squared order. -/
theorem negRealPartLeModulus (value : ComplexReal) :
    LessEqualReal (negReal value.realPart) (modulus value) :=
  have isNegSquareBelow :
      LessEqualReal (mulReal (negReal value.realPart) (negReal value.realPart))
        (modulusSquared value) :=
    lessEqualRealCongr
      (denotesSameRealSymm (mulRealNegNegDenotesSame value.realPart))
      (denotesSameRealRefl (modulusSquared value))
      (lessEqualRealSelfAddNonNegRight
        (mulReal value.realPart value.realPart)
        (mulRealSelfIsNonNegativeReal value.imaginaryPart))
  lessEqualRealTrans
    (selfLeSqrtRealSquare (negReal value.realPart))
    (sqrtRealMonotone
      (mulRealSelfIsNonNegativeReal (negReal value.realPart))
      (modulusSquaredIsNonNegativeReal value)
      isNegSquareBelow)

/-! ## The imaginary-part component bounds (NUM-C-5c) -/

/-- **The modulus dominates the imaginary part** — `Im z ≤ |z|`.  Symmetric to the
real-part bound; the add-nonnegative step lands `(Im z)² ≤ (Im z)² + (Re z)²` and
commutativity re-orders the radicand to `(Re z)² + (Im z)² = |z|²`. -/
theorem modulusDominatesImaginaryPart (value : ComplexReal) :
    LessEqualReal value.imaginaryPart (modulus value) :=
  have isImagSquareBelow :
      LessEqualReal (mulReal value.imaginaryPart value.imaginaryPart)
        (modulusSquared value) :=
    lessEqualRealCongr
      (denotesSameRealRefl (mulReal value.imaginaryPart value.imaginaryPart))
      (addRealComm (mulReal value.imaginaryPart value.imaginaryPart)
        (mulReal value.realPart value.realPart))
      (lessEqualRealSelfAddNonNegRight
        (mulReal value.imaginaryPart value.imaginaryPart)
        (mulRealSelfIsNonNegativeReal value.realPart))
  lessEqualRealTrans
    (selfLeSqrtRealSquare value.imaginaryPart)
    (sqrtRealMonotone
      (mulRealSelfIsNonNegativeReal value.imaginaryPart)
      (modulusSquaredIsNonNegativeReal value)
      isImagSquareBelow)

/-- **The negated imaginary part is dominated by the modulus** — `−Im z ≤ |z|`.
The imaginary sibling of `negRealPartLeModulus`, `(−Im z)² ~ (Im z)²` relocating
the left endpoint of the imaginary squared order. -/
theorem negImaginaryPartLeModulus (value : ComplexReal) :
    LessEqualReal (negReal value.imaginaryPart) (modulus value) :=
  have isImagSquareBelow :
      LessEqualReal (mulReal value.imaginaryPart value.imaginaryPart)
        (modulusSquared value) :=
    lessEqualRealCongr
      (denotesSameRealRefl (mulReal value.imaginaryPart value.imaginaryPart))
      (addRealComm (mulReal value.imaginaryPart value.imaginaryPart)
        (mulReal value.realPart value.realPart))
      (lessEqualRealSelfAddNonNegRight
        (mulReal value.imaginaryPart value.imaginaryPart)
        (mulRealSelfIsNonNegativeReal value.realPart))
  have isNegSquareBelow :
      LessEqualReal
        (mulReal (negReal value.imaginaryPart) (negReal value.imaginaryPart))
        (modulusSquared value) :=
    lessEqualRealCongr
      (denotesSameRealSymm (mulRealNegNegDenotesSame value.imaginaryPart))
      (denotesSameRealRefl (modulusSquared value))
      isImagSquareBelow
  lessEqualRealTrans
    (selfLeSqrtRealSquare (negReal value.imaginaryPart))
    (sqrtRealMonotone
      (mulRealSelfIsNonNegativeReal (negReal value.imaginaryPart))
      (modulusSquaredIsNonNegativeReal value)
      isNegSquareBelow)

/-! ## The abs-sum upper bound (NUM-C-5d) -/

/-- **The modulus is bounded by the component absolute values' sum** —
`|z| ≤ |Re z| + |Im z|`.  Both sides are nonnegative, so it suffices to compare
squares (`nonNegSquareOrderReflect`).  The binomial expansion
`(|Re z| + |Im z|)² ~ (|Re z|² + |Im z|²) + 2·|Re z|·|Im z|` recovers the two
component squares to `(Re z)²` and `(Im z)²` (`sqrtRealSquareDenotesSame`), so its
square prefix denotes `|z|²`; the nonnegative cross term
`|Re z|·|Im z| + |Re z|·|Im z|` then lifts `|z|² ≤ (|Re z| + |Im z|)²` by
`lessEqualRealSelfAddNonNegRight`. -/
theorem modulusLeComponentAbsSum (value : ComplexReal) :
    LessEqualReal (modulus value)
      (addReal
        (sqrtReal (mulReal value.realPart value.realPart)
          (mulRealSelfIsNonNegativeReal value.realPart))
        (sqrtReal (mulReal value.imaginaryPart value.imaginaryPart)
          (mulRealSelfIsNonNegativeReal value.imaginaryPart))) :=
  let absoluteReal :=
    sqrtReal (mulReal value.realPart value.realPart)
      (mulRealSelfIsNonNegativeReal value.realPart)
  let absoluteImaginary :=
    sqrtReal (mulReal value.imaginaryPart value.imaginaryPart)
      (mulRealSelfIsNonNegativeReal value.imaginaryPart)
  let absoluteSum := addReal absoluteReal absoluteImaginary
  have isAbsoluteRealNonNegative : IsNonNegativeReal absoluteReal :=
    sqrtRealIsNonNegativeReal (mulReal value.realPart value.realPart)
      (mulRealSelfIsNonNegativeReal value.realPart)
  have isAbsoluteImaginaryNonNegative : IsNonNegativeReal absoluteImaginary :=
    sqrtRealIsNonNegativeReal (mulReal value.imaginaryPart value.imaginaryPart)
      (mulRealSelfIsNonNegativeReal value.imaginaryPart)
  have squaresDenoteModulusSquared :
      DenotesSameReal
        (addReal (mulReal absoluteReal absoluteReal)
          (mulReal absoluteImaginary absoluteImaginary))
        (modulusSquared value) :=
    addRealRespectsDenotesSame
      (sqrtRealSquareDenotesSame (mulRealSelfIsNonNegativeReal value.realPart))
      (sqrtRealSquareDenotesSame (mulRealSelfIsNonNegativeReal value.imaginaryPart))
  have isCrossSumNonNegative :
      IsNonNegativeReal
        (addReal (mulReal absoluteReal absoluteImaginary)
          (mulReal absoluteReal absoluteImaginary)) :=
    addRealPreservesIsNonNegativeReal
      (mulRealPreservesIsNonNegativeReal isAbsoluteRealNonNegative
        isAbsoluteImaginaryNonNegative)
      (mulRealPreservesIsNonNegativeReal isAbsoluteRealNonNegative
        isAbsoluteImaginaryNonNegative)
  have isModulusSquaredBelowSumSquare :
      LessEqualReal (modulusSquared value) (mulReal absoluteSum absoluteSum) :=
    lessEqualRealCongr
      squaresDenoteModulusSquared
      (denotesSameRealSymm (squareSumExpand absoluteReal absoluteImaginary))
      (lessEqualRealSelfAddNonNegRight
        (addReal (mulReal absoluteReal absoluteReal)
          (mulReal absoluteImaginary absoluteImaginary))
        isCrossSumNonNegative)
  have isModulusSquareBelow :
      LessEqualReal (mulReal (modulus value) (modulus value))
        (mulReal absoluteSum absoluteSum) :=
    lessEqualRealCongr
      (denotesSameRealSymm (modulusSquareDenotesModulusSquared value))
      (denotesSameRealRefl (mulReal absoluteSum absoluteSum))
      isModulusSquaredBelowSumSquare
  nonNegSquareOrderReflect
    (sqrtRealIsNonNegativeReal (modulusSquared value)
      (modulusSquaredIsNonNegativeReal value))
    (addRealPreservesIsNonNegativeReal isAbsoluteRealNonNegative
      isAbsoluteImaginaryNonNegative)
    isModulusSquareBelow

/-- Marker: the ℂ modulus carries the pointwise component bounds
(`±Re z ≤ |z|`, `±Im z ≤ |z|`, `|z| ≤ |Re z| + |Im z|`). -/
def fxComplexReal_hasModulusComponentBounds : Bool := true

end FX1Poly.ComputerAlgebra
