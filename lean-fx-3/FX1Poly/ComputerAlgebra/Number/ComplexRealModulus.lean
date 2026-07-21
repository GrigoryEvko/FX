import FX1Poly.ComputerAlgebra.Number.ComplexReal
import FX1Poly.ComputerAlgebra.Number.RegularRealSquareRoot

/-! # ComplexRealModulus — the modulus of a Gaussian real

The metric layer over `ComplexReal`: the squared modulus `|z|² = a² + b²`, its
pointwise nonnegativity, the modulus `|z| = sqrt(a² + b²)` via `sqrtReal`, and the
two ring identities that pin it down:

* `|z|²` is a pointwise-nonnegative real (a sum of two rational squares at every
  index), so it feeds `sqrtReal` directly — the `0 ≤ value → IsNonNegativeReal
  (canonicalise value)` bridge is bypassed;
* the square law `|z|² ~ |z| * |z|` is `sqrtRealSquareDenotesSame` at this
  radicand;
* `z * conj z ~ |z|²` (the imaginary part cancels to zero), pure ℝ-ring
  negation-passing.

Two sign-blind square-nonneg lemmas support this
(`intMulSelfNonNegative`, `mulExactSelfIsNonNegative`): the underlying
nonneg-product facts need both factors nonnegative, but a square is nonnegative
regardless of sign.  Both are full-enumeration matches — no wildcard, no propext.

Zero axioms throughout. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-! ## Sign-blind square nonnegativity -/

/-- A square Int is nonnegative, sign-blind, by full three-shape enumeration on
the integer (`ofNat` splits definitionally into the two `ofNat` cases; `negSucc`
squares to `ofNat (succ * succ)` by `Int.mul`).  No sign split, no negation
lemmas — each arm is one `intZeroLeOfNat`. -/
theorem intMulSelfNonNegative : ∀ value : Int, (0 : Int) ≤ value * value
  | .ofNat naturalPart => intZeroLeOfNat (naturalPart * naturalPart)
  | .negSucc magnitudePredecessor =>
      intZeroLeOfNat ((magnitudePredecessor + 1) * (magnitudePredecessor + 1))

/-- A square rational is nonnegative: the numerator of `mulExact s s` is
`s.numerator * s.numerator`, sign-blind nonnegative by `intMulSelfNonNegative`,
read back through the numerator-sign bridge. -/
theorem mulExactSelfIsNonNegative (sample : RationalPair) :
    IsNonNegative (mulExact sample sample) :=
  isNonNegativeOfNumeratorNonNegative (intMulSelfNonNegative sample.numerator)

/-! ## Pointwise nonnegativity of squares and sums of reals -/

/-- A real square is pointwise nonnegative: every approximant of
`mulReal value value` is `mulExact s s` on the same sample `s`, a rational
square. -/
theorem mulRealSelfIsNonNegativeReal (value : RegularReal) :
    IsNonNegativeReal (mulReal value value) :=
  fun index =>
    mulExactSelfIsNonNegative
      (value.approximation (productSamplingIndex value value index))

/-- Pointwise nonnegativity is closed under addition: each approximant of
`addReal` is `addExact` of the two summands' doubled samples, both nonnegative. -/
theorem addRealPreservesIsNonNegativeReal {leftValue rightValue : RegularReal}
    (isLeftNonNegative : IsNonNegativeReal leftValue)
    (isRightNonNegative : IsNonNegativeReal rightValue) :
    IsNonNegativeReal (addReal leftValue rightValue) :=
  fun index =>
    addExactIsNonNegative
      (isLeftNonNegative (2 * index + 1))
      (isRightNonNegative (2 * index + 1))

/-! ## The squared modulus -/

/-- The squared modulus `|z|² = a² + b²` — a bare ℝ-ring term, no `sqrtReal`. -/
def modulusSquared (value : ComplexReal) : RegularReal :=
  addReal (mulReal value.realPart value.realPart)
    (mulReal value.imaginaryPart value.imaginaryPart)

/-- `|z|²` is pointwise nonnegative — a sum of two real squares. -/
theorem modulusSquaredIsNonNegativeReal (value : ComplexReal) :
    IsNonNegativeReal (modulusSquared value) :=
  addRealPreservesIsNonNegativeReal
    (mulRealSelfIsNonNegativeReal value.realPart)
    (mulRealSelfIsNonNegativeReal value.imaginaryPart)

/-- `z * conj z ~ |z|²`: the imaginary part cancels to zero.  The real part pulls
a double negation out of `b * (-b)`; the imaginary part swaps and commutes to
`(-X) + X ~ 0` with `X = a * b`.  Pure ℝ-ring negation-passing. -/
theorem mulComplexConjDenotesModulusSquared (value : ComplexReal) :
    DenotesSameComplex (mulComplex value (conjComplex value))
      { realPart := modulusSquared value
        imaginaryPart := constantReal zeroRational } :=
  let realPartValue := value.realPart
  let imaginaryPartValue := value.imaginaryPart
  let crossProduct := mulReal realPartValue imaginaryPartValue
  ⟨denotesSameRealTrans
      (addRealRespectsDenotesSame
        (denotesSameRealRefl (mulReal realPartValue realPartValue))
        (denotesSameRealTrans
          (negRealRespectsDenotesSame
            (mulRealNegRightDenotesSame imaginaryPartValue imaginaryPartValue))
          (negRealNegRealDenotesSame
            (mulReal imaginaryPartValue imaginaryPartValue))))
      (denotesSameRealRefl (modulusSquared value)),
    denotesSameRealTrans
      (addRealRespectsDenotesSame
        (mulRealNegRightDenotesSame realPartValue imaginaryPartValue)
        (mulRealComm imaginaryPartValue realPartValue))
      (denotesSameRealTrans
        (addRealComm (negReal crossProduct) crossProduct)
        (addRealNegRight crossProduct))⟩

/-! ## The modulus -/

/-- The modulus `|z| = sqrt(a² + b²)` — `sqrtReal` fed the pointwise
nonnegativity witness. -/
def modulus (value : ComplexReal) : RegularReal :=
  sqrtReal (modulusSquared value) (modulusSquaredIsNonNegativeReal value)

/-- The square law `|z| * |z| ~ |z|²` — `sqrtRealSquareDenotesSame` at the squared
modulus. -/
theorem modulusSquareDenotesModulusSquared (value : ComplexReal) :
    DenotesSameReal (mulReal (modulus value) (modulus value))
      (modulusSquared value) :=
  sqrtRealSquareDenotesSame (modulusSquaredIsNonNegativeReal value)

end FX1Poly.ComputerAlgebra
