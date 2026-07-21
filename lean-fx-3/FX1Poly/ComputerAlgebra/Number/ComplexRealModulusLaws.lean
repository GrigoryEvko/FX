import FX1Poly.ComputerAlgebra.Number.ComplexRealModulus
import FX1Poly.ComputerAlgebra.Number.RegularRealSquareRootMultiplicative

/-! # ComplexRealModulusLaws — the modulus is multiplicative

`|z * w| ~ |z| * |w|` on the zero-axiom Gaussian-real setoid, the payoff of
`sqrtRealMulDenotesSame`.  Two steps:

* The squared-modulus identity `|z * w|² ~ |z|² * |w|²`
  (`modulusSquaredMulDenotesSame`).  Rather than expand the Gauss product's cross
  terms directly, this rides the ℂ commutative ring: the real part of
  `(z w) conj(z w)` is `|z w|²` (`mulComplexConjDenotesModulusSquared`), and
  `conj(z w) ~ conj z * conj w` (`conjComplexMulComplex`) lets the four-factor
  product regroup — via the multiplicative medial from `mulComplexAssoc` and
  `mulComplexComm` — into `(z conj z)(w conj w)`, whose real part is `|z|² * |w|²`
  (the imaginary parts vanish, so the Gauss real part sheds its `0 * 0` term).

* Modulus multiplicativity `|z w| ~ |z| * |w|` (`modulusMulDenotesSame`).  Both `|z w|` and
  `|z| * |w|` are square roots of `|z|² * |w|²` up to the setoid: rewrite the
  radicand by the squared identity (`sqrtRealRespectsDenotesSame`), then split the
  root of the product (`sqrtRealMulDenotesSame`).

Zero axioms throughout. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-! ## The multiplicative medial on ℂ -/

/-- The multiplicative medial on ℂ: swap the two inner factors of a four-term
product, `(a * b) * (c * d) ~ (a * c) * (b * d)`.  Associativity out, commute the
middle pair, associativity back — the ℂ analogue of `mulRealMedial` over
`mulComplexAssoc` and `mulComplexComm`.  Re-associates `(z w)(conj z conj w)` to
`(z conj z)(w conj w)`. -/
theorem mulComplexMedial (firstValue secondValue thirdValue fourthValue : ComplexReal) :
    DenotesSameComplex
      (mulComplex (mulComplex firstValue secondValue) (mulComplex thirdValue fourthValue))
      (mulComplex (mulComplex firstValue thirdValue) (mulComplex secondValue fourthValue)) :=
  denotesSameComplexTrans
    (mulComplexAssoc firstValue secondValue (mulComplex thirdValue fourthValue))
    (denotesSameComplexTrans
      (mulComplexRespectsDenotesSame (denotesSameComplexRefl firstValue)
        (denotesSameComplexTrans
          (denotesSameComplexSymm
            (mulComplexAssoc secondValue thirdValue fourthValue))
          (denotesSameComplexTrans
            (mulComplexRespectsDenotesSame (mulComplexComm secondValue thirdValue)
              (denotesSameComplexRefl fourthValue))
            (mulComplexAssoc thirdValue secondValue fourthValue))))
      (denotesSameComplexSymm
        (mulComplexAssoc firstValue thirdValue (mulComplex secondValue fourthValue))))

/-! ## The squared-modulus identity -/

/-- `|z * w|² ~ |z|² * |w|²`: the squared modulus is multiplicative.  Routed
through the conjugate rather than the direct `(ac - bd)² + (ad + bc)²` expansion:
`|z w|² ~ Re((z w) conj(z w))`, regroup `(z w)(conj z conj w)` to
`(z conj z)(w conj w)` by the medial, whose real part sheds the vanishing imaginary
cross term to land on `|z|² * |w|²`. -/
theorem modulusSquaredMulDenotesSame (leftValue rightValue : ComplexReal) :
    DenotesSameReal (modulusSquared (mulComplex leftValue rightValue))
      (mulReal (modulusSquared leftValue) (modulusSquared rightValue)) :=
  let product := mulComplex leftValue rightValue
  let squaredModulusProduct :=
    mulReal (modulusSquared leftValue) (modulusSquared rightValue)
  have productConjugateRegroups :
      DenotesSameComplex
        (mulComplex product (conjComplex product))
        (mulComplex (mulComplex leftValue (conjComplex leftValue))
          (mulComplex rightValue (conjComplex rightValue))) :=
    denotesSameComplexTrans
      (mulComplexRespectsDenotesSame (denotesSameComplexRefl product)
        (conjComplexMulComplex leftValue rightValue))
      (mulComplexMedial leftValue rightValue
        (conjComplex leftValue) (conjComplex rightValue))
  have regroupedDenotesModulusProducts :
      DenotesSameComplex
        (mulComplex (mulComplex leftValue (conjComplex leftValue))
          (mulComplex rightValue (conjComplex rightValue)))
        (mulComplex
          { realPart := modulusSquared leftValue
            imaginaryPart := constantReal zeroRational }
          { realPart := modulusSquared rightValue
            imaginaryPart := constantReal zeroRational }) :=
    mulComplexRespectsDenotesSame
      (mulComplexConjDenotesModulusSquared leftValue)
      (mulComplexConjDenotesModulusSquared rightValue)
  denotesSameRealTrans
    (denotesSameRealSymm (mulComplexConjDenotesModulusSquared product).left)
    (denotesSameRealTrans productConjugateRegroups.left
      (denotesSameRealTrans regroupedDenotesModulusProducts.left
        (denotesSameRealTrans
          (subRealRespectsDenotesSame
            (denotesSameRealRefl squaredModulusProduct)
            (mulRealZeroRight (constantReal zeroRational)))
          (subRealZeroRightDenotesSame squaredModulusProduct))))

/-! ## Modulus multiplicativity -/

/-- `|z * w| ~ |z| * |w|`: the modulus is multiplicative.  Rewrite the radicand of
`|z w| = sqrt |z w|²` by the squared identity, then split the root of the product
`sqrt(|z|² * |w|²)` with `sqrtRealMulDenotesSame`; the resulting
`sqrt |z|² * sqrt |w|²` is `|z| * |w|` by definition. -/
theorem modulusMulDenotesSame (leftValue rightValue : ComplexReal) :
    DenotesSameReal (modulus (mulComplex leftValue rightValue))
      (mulReal (modulus leftValue) (modulus rightValue)) :=
  denotesSameRealTrans
    (sqrtRealRespectsDenotesSame
      (modulusSquaredIsNonNegativeReal (mulComplex leftValue rightValue))
      (mulRealPreservesIsNonNegativeReal
        (modulusSquaredIsNonNegativeReal leftValue)
        (modulusSquaredIsNonNegativeReal rightValue))
      (modulusSquaredMulDenotesSame leftValue rightValue))
    (sqrtRealMulDenotesSame
      (modulusSquaredIsNonNegativeReal leftValue)
      (modulusSquaredIsNonNegativeReal rightValue)
      (mulRealPreservesIsNonNegativeReal
        (modulusSquaredIsNonNegativeReal leftValue)
        (modulusSquaredIsNonNegativeReal rightValue)))

/-- Marker: the ℂ modulus is multiplicative on the Gaussian-real setoid. -/
def fxComplexReal_hasModulusMultiplicativity : Bool := true

end FX1Poly.ComputerAlgebra
