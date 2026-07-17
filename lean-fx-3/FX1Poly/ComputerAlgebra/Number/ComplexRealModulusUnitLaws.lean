import FX1Poly.ComputerAlgebra.Number.ComplexRealModulusLaws
import FX1Poly.ComputerAlgebra.Number.ComplexRealField

/-! # ComplexRealModulusUnitLaws — the ℂ modulus unit laws (NUM-C-3, completing)

The three ORDER-FREE modulus equalities that finish the multiplicative-modulus
fragment on the zero-axiom Gaussian-real setoid, each a direct corollary of the
shipped square-root and modulus-multiplicativity bricks — no order, no
decidability, no √-metric analysis beyond what already landed:

* **Conjugate invariance** `|conj z| ~ |z|` (`modulusConjDenotesSame`).  The
  squared modulus is sign-blind in the imaginary part — `(-b)^2 ~ b^2` — so
  `|conj z|^2 ~ |z|^2` by addend congruence, and `sqrtRealRespectsDenotesSame`
  lifts that to the roots (the differing pointwise-nonneg witnesses are
  irrelevant to the value).

* **Unit modulus** `|1| ~ 1` (`modulusOneDenotesSame`).  `|1|^2 ~ 1` by the ring
  (`1^2 + 0^2 ~ 1`), and both `|1|` and `1` are nonnegative reals squaring to the
  same thing, so `nonNegSquareCancel` identifies them.

* **Inverse modulus cancellation** `|z^{-1}| * |z| ~ 1` on apartness
  (`modulusInverseTimesSelfDenotesOne`).  Fold the product of moduli back into
  the modulus of the product (`modulusMulDenotesSame` reversed), rewrite through
  the Heyting-field law `z^{-1} z ~ 1` under the modulus congruence proved here
  (`modulusRespectsDenotesSameComplex`), then land on `1` by the unit modulus.

Zero axioms throughout — pure setoid equality, ring, and √-congruence. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-! ## Nonnegativity of the real unit -/

/-- **The constant real one is pointwise nonnegative** — every approximant is
`oneRational`, whose numerator `1` is nonnegative. -/
theorem oneRealIsNonNegativeReal : IsNonNegativeReal (constantReal oneRational) :=
  fun _ => isNonNegativeOfNumeratorNonNegative (intZeroLeOfNat 1)

/-! ## The modulus congruence over the product setoid -/

/-- **The modulus respects the product setoid** — same complex reals have
same-real moduli.  The squared moduli agree by `modulusSquaredRespectsDenotesSame`,
and `sqrtRealRespectsDenotesSame` lifts that to the roots. -/
theorem modulusRespectsDenotesSameComplex {leftValue rightValue : ComplexReal}
    (areSame : DenotesSameComplex leftValue rightValue) :
    DenotesSameReal (modulus leftValue) (modulus rightValue) :=
  sqrtRealRespectsDenotesSame
    (modulusSquaredIsNonNegativeReal leftValue)
    (modulusSquaredIsNonNegativeReal rightValue)
    (modulusSquaredRespectsDenotesSame areSame)

/-! ## Conjugate invariance -/

/-- **`|conj z| ~ |z|`** — the modulus is conjugation-invariant.  The squared
modulus differs only in the imaginary square `(-b)(-b)`, which folds back to
`b * b` by two negation passes and one double-negation collapse; addend
congruence then gives `|conj z|^2 ~ |z|^2`, and `sqrtRealRespectsDenotesSame`
lifts it. -/
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

/-- **`|1| ~ 1`** — the modulus of the complex unit is the real unit.  `|1|^2 ~ 1`
(`1^2 + 0^2 ~ 1`), and `|1|` and `1` are both nonnegative reals squaring to the
same value, so `nonNegSquareCancel` identifies them. -/
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

/-- **`|z^{-1}| * |z| ~ 1`** on apartness — the modulus carries the Heyting-field
inverse to the real inverse.  Fold `|z^{-1}| * |z|` back into `|z^{-1} z|`
(`modulusMulDenotesSame` reversed), rewrite the argument through the field law
`z^{-1} z ~ 1` under the modulus congruence, and land on `1` by the unit
modulus. -/
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
