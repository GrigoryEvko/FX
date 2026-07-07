import FX1Poly.ComputerAlgebra.Number.ComplexReal
import FX1Poly.ComputerAlgebra.Number.RegularRealSquareRoot

/-! # ComplexRealModulus — the modulus of a Gaussian real (NUM-C-2)

The metric layer over `ComplexReal`: the squared modulus `|z|^2 = a^2 + b^2`,
its pointwise nonnegativity, the modulus `|z| = sqrt(a^2 + b^2)` via the
shipped `sqrtReal`, and the two ring identities that pin it down:

* `|z|^2` is a POINTWISE-nonnegative real (a sum of two rational squares at
  every index), so it feeds `sqrtReal` directly — the deferred
  `0 <=_R value -> IsNonNegativeReal (canonicalise value)` bridge is bypassed;
* the square law `|z|^2 ~ |z| * |z|` is the shipped `sqrtRealSquareDenotesSame`
  verbatim;
* `z * conj z ~ |z|^2` (the imaginary part cancels to zero), pure ℝ-ring
  negation-passing over the shipped bricks.

The sole genuinely new prerequisites are the two SIGN-BLIND square-nonneg
bricks (`intMulSelfNonNegative`, `mulExactSelfIsNonNegative`): every shipped
nonneg-product fact needs BOTH factors nonnegative, but a square is
nonnegative regardless of sign.  Both are full-enumeration matches — no
wildcard, no propext.

Zero axioms throughout. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-! ## The sign-blind square-nonneg bricks -/

/-- **A square Int is nonnegative** — sign-blind, by full three-shape
enumeration on the integer (`ofNat` splits definitionally into the two
`ofNat` cases; `negSucc` squares to `ofNat (succ * succ)` by `Int.mul`).  No
sign split, no negation lemmas — each arm is one `intZeroLeOfNat`. -/
theorem intMulSelfNonNegative : ∀ value : Int, (0 : Int) ≤ value * value
  | .ofNat naturalPart => intZeroLeOfNat (naturalPart * naturalPart)
  | .negSucc magnitudePredecessor =>
      intZeroLeOfNat ((magnitudePredecessor + 1) * (magnitudePredecessor + 1))

/-- **A square rational is nonnegative** — the numerator of `mulExact s s` is
`s.numerator * s.numerator`, sign-blind nonnegative by `intMulSelfNonNegative`,
read back through the numerator-sign bridge. -/
theorem mulExactSelfIsNonNegative (sample : RationalPair) :
    IsNonNegative (mulExact sample sample) :=
  isNonNegativeOfNumeratorNonNegative (intMulSelfNonNegative sample.numerator)

/-! ## Pointwise nonnegativity of squares and sums of reals -/

/-- **A real square is pointwise nonnegative** — every approximant of
`mulReal value value` is `mulExact s s` on the SAME sample `s`, a rational
square. -/
theorem mulRealSelfIsNonNegativeReal (value : RegularReal) :
    IsNonNegativeReal (mulReal value value) :=
  fun index =>
    mulExactSelfIsNonNegative
      (value.approximation (productSamplingIndex value value index))

/-- **Pointwise nonnegativity is closed under addition** — each approximant
of `addReal` is `addExact` of the two summands' doubled samples, both
nonnegative. -/
theorem addRealPreservesIsNonNegativeReal {leftValue rightValue : RegularReal}
    (isLeftNonNegative : IsNonNegativeReal leftValue)
    (isRightNonNegative : IsNonNegativeReal rightValue) :
    IsNonNegativeReal (addReal leftValue rightValue) :=
  fun index =>
    addExactIsNonNegative
      (isLeftNonNegative (2 * index + 1))
      (isRightNonNegative (2 * index + 1))

/-! ## The squared modulus -/

/-- **The squared modulus** `|z|^2 = a^2 + b^2` — a bare ℝ-ring term, no
`sqrtReal`. -/
def modulusSquared (value : ComplexReal) : RegularReal :=
  addReal (mulReal value.realPart value.realPart)
    (mulReal value.imaginaryPart value.imaginaryPart)

/-- `|z|^2` is pointwise nonnegative — a sum of two real squares. -/
theorem modulusSquaredIsNonNegativeReal (value : ComplexReal) :
    IsNonNegativeReal (modulusSquared value) :=
  addRealPreservesIsNonNegativeReal
    (mulRealSelfIsNonNegativeReal value.realPart)
    (mulRealSelfIsNonNegativeReal value.imaginaryPart)

/-- **`z * conj z ~ |z|^2`** — the imaginary part cancels to zero.  The real
part pulls a double negation out of `b * (-b)`; the imaginary part swaps and
commutes to `(-X) + X ~ 0` with `X = a * b`.  Pure ℝ-ring negation-passing;
no new real bricks. -/
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

/-- **The modulus** `|z| = sqrt(a^2 + b^2)` — the shipped `sqrtReal` fed the
pointwise nonnegativity witness. -/
def modulus (value : ComplexReal) : RegularReal :=
  sqrtReal (modulusSquared value) (modulusSquaredIsNonNegativeReal value)

/-- **The square law** `|z| * |z| ~ |z|^2` — the shipped
`sqrtRealSquareDenotesSame` at the squared modulus. -/
theorem modulusSquareDenotesModulusSquared (value : ComplexReal) :
    DenotesSameReal (mulReal (modulus value) (modulus value))
      (modulusSquared value) :=
  sqrtRealSquareDenotesSame (modulusSquaredIsNonNegativeReal value)

end FX1Poly.ComputerAlgebra
