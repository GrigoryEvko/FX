import FX1Poly.ComputerAlgebra.Number.ComplexRealModulusLaws
import FX1Poly.ComputerAlgebra.Number.ComplexRealField

/-! # ComplexRealModulusUnitLaws — modulus unit laws

Three order-free modulus equalities completing the multiplicative-modulus
fragment on the zero-axiom Gaussian-real setoid, each a corollary of the
square-root and modulus-multiplicativity lemmas:

* Conjugate invariance `|conj z| ~ |z|` (`modulusConjDenotesSame`).  The squared
  modulus is sign-blind in the imaginary part — `(-b)² ~ b²` — so
  `|conj z|² ~ |z|²` by addend congruence, and `sqrtRealRespectsDenotesSame` lifts
  it to the roots.

* Unit modulus `|1| ~ 1` (`modulusOneDenotesSame`).  `|1|² ~ 1` by the ring
  (`1² + 0² ~ 1`), and both `|1|` and `1` are nonnegative reals squaring to the
  same value, so `nonNegSquareCancel` identifies them.

* Inverse modulus cancellation `|z⁻¹| * |z| ~ 1` on apartness
  (`modulusInverseTimesSelfDenotesOne`).  Fold the product of moduli back into the
  modulus of the product (`modulusMulDenotesSame` reversed), rewrite through the
  Heyting-field law `z⁻¹ z ~ 1` under the modulus congruence
  (`modulusRespectsDenotesSameComplex`), then land on `1` by the unit modulus.

Zero axioms throughout — setoid equality, ring, and square-root congruence. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-! ## Nonnegativity of the real unit -/

/-- The constant real one is pointwise nonnegative: every approximant is
`oneRational`, whose numerator `1` is nonnegative. -/
theorem oneRealIsNonNegativeReal : IsNonNegativeReal (constantReal oneRational) :=
  fun _ => isNonNegativeOfNumeratorNonNegative (intZeroLeOfNat 1)

/-! ## The modulus congruence over the product setoid -/

/-- The modulus respects the product setoid: same complex reals have same-real
moduli.  The squared moduli agree by `modulusSquaredRespectsDenotesSame`, and
`sqrtRealRespectsDenotesSame` lifts that to the roots. -/
theorem modulusRespectsDenotesSameComplex {leftValue rightValue : ComplexReal}
    (areSame : DenotesSameComplex leftValue rightValue) :
    DenotesSameReal (modulus leftValue) (modulus rightValue) :=
  sqrtRealRespectsDenotesSame
    (modulusSquaredIsNonNegativeReal leftValue)
    (modulusSquaredIsNonNegativeReal rightValue)
    (modulusSquaredRespectsDenotesSame areSame)

/-! ## Conjugate invariance -/

/-- `|conj z| ~ |z|`: the modulus is conjugation-invariant.  The squared modulus
differs only in the imaginary square `(-b)(-b)`, which folds back to `b * b` by two
negation passes and one double-negation collapse; addend congruence gives
`|conj z|² ~ |z|²`, and `sqrtRealRespectsDenotesSame` lifts it. -/
theorem modulusConjDenotesSame (value : ComplexReal) :
    DenotesSameReal (modulus (conjComplex value)) (modulus value) :=
  have squaredModulusAgreesUnderConjugation :
      DenotesSameReal (modulusSquared (conjComplex value)) (modulusSquared value) :=
    addRealRespectsDenotesSame
      (denotesSameRealRefl (mulReal value.realPart value.realPart))
      (denotesSameRealTrans
        (mulRealNegLeftDenotesSame value.imaginaryPart (negReal value.imaginaryPart))
        (denotesSameRealTrans
          (negRealRespectsDenotesSame
            (mulRealNegRightDenotesSame value.imaginaryPart value.imaginaryPart))
          (negRealNegRealDenotesSame
            (mulReal value.imaginaryPart value.imaginaryPart))))
  sqrtRealRespectsDenotesSame
    (modulusSquaredIsNonNegativeReal (conjComplex value))
    (modulusSquaredIsNonNegativeReal value)
    squaredModulusAgreesUnderConjugation

/-! ## Unit modulus -/

/-- `|1| ~ 1`: the modulus of the complex unit is the real unit.  `|1|² ~ 1`
(`1² + 0² ~ 1`), and `|1|` and `1` are both nonnegative reals squaring to the same
value, so `nonNegSquareCancel` identifies them. -/
theorem modulusOneDenotesSame :
    DenotesSameReal (modulus oneComplex) (constantReal oneRational) :=
  have squaredModulusOfOneIsOne :
      DenotesSameReal (modulusSquared oneComplex) (constantReal oneRational) :=
    denotesSameRealTrans
      (addRealRespectsDenotesSame
        (mulRealOneRight (constantReal oneRational))
        (mulRealZeroRight (constantReal zeroRational)))
      (addRealZeroRight (constantReal oneRational))
  have squaresAgree :
      DenotesSameReal (mulReal (modulus oneComplex) (modulus oneComplex))
        (mulReal (constantReal oneRational) (constantReal oneRational)) :=
    denotesSameRealTrans
      (denotesSameRealTrans
        (modulusSquareDenotesModulusSquared oneComplex)
        squaredModulusOfOneIsOne)
      (denotesSameRealSymm (mulRealOneRight (constantReal oneRational)))
  nonNegSquareCancel
    (sqrtRealIsNonNegativeReal (modulusSquared oneComplex)
      (modulusSquaredIsNonNegativeReal oneComplex))
    oneRealIsNonNegativeReal
    squaresAgree

/-! ## Inverse modulus cancellation -/

/-- `|z⁻¹| * |z| ~ 1` on apartness: the modulus carries the Heyting-field inverse
to the real inverse.  Fold `|z⁻¹| * |z|` back into `|z⁻¹ z|`
(`modulusMulDenotesSame` reversed), rewrite the argument through the field law
`z⁻¹ z ~ 1` under the modulus congruence, and land on `1` by the unit modulus. -/
theorem modulusInverseTimesSelfDenotesOne (value : ComplexReal)
    (isApart : IsApartFromZeroComplex value) :
    DenotesSameReal
      (mulReal (modulus (inverseComplex value isApart)) (modulus value))
      (constantReal oneRational) :=
  denotesSameRealTrans
    (denotesSameRealSymm
      (modulusMulDenotesSame (inverseComplex value isApart) value))
    (denotesSameRealTrans
      (modulusRespectsDenotesSameComplex
        (mulComplexInverseComplexLeftDenotesOne value isApart))
      modulusOneDenotesSame)

/-- Marker: the ℂ modulus satisfies the conjugate / unit / inverse laws. -/
def fxComplexReal_hasModulusUnitLaws : Bool := true

end FX1Poly.ComputerAlgebra
