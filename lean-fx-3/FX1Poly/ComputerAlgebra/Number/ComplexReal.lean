import FX1Poly.ComputerAlgebra.Number.RegularRealRing

/-! # ComplexReal — the Gaussian reals over `RegularReal` (NUM-C-1)

The ℂ carrier: a pair of Bishop regular reals `(re, im)`.  No new carrier
analysis — `ComplexReal` is literally `RegularReal x RegularReal`, its
sameness the PRODUCT setoid (both components denote the same real), and its
operations componentwise except `mulComplex`, which is the Gauss product
`(a+bi)(c+di) = (ac - bd) + (ad + bc) i`.

Everything here composes the ℝ layer:

* the setoid refl/symm/trans and every operation CONGRUENCE ride the shipped
  `RegularReal` setoid/congruences alone — no ring law;
* the CONJUGATION laws (`conj∘conj`, `conj` over `+`, `conj` over `·`) ride
  the negation-passing bricks — pointwise reals, no ring reassociation;
* the commutative-ring laws lift the `RegularReal` ring laws (NUM-R-4)
  componentwise; commutativity/identity/inverse close here, while
  associativity of `+` and associativity/distributivity of `·` wait on the
  slack-closure ℝ bricks (`addRealAssoc`, `mulRealAssoc`,
  `mulRealLeftDistrib`).

Sameness is UNDECIDABLE (inherited from `DenotesSameReal`), never `Eq` on the
approximation sequences — so no `funext`, no `Quot`, zero axioms throughout.

The modulus `|z| = sqrt(a^2 + b^2)` and the Heyting-field structure are the
metric layer (NUM-C-2), out of scope here — they need `sqrtReal`. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-- **A complex regular real** — a pair of Bishop reals. -/
structure ComplexReal where
  realPart : RegularReal
  imaginaryPart : RegularReal

/-- **Sameness of complex reals** — the PRODUCT setoid: both components
denote the same Bishop real.  Undecidable, inherited from `DenotesSameReal`. -/
def DenotesSameComplex (leftValue rightValue : ComplexReal) : Prop :=
  DenotesSameReal leftValue.realPart rightValue.realPart ∧
    DenotesSameReal leftValue.imaginaryPart rightValue.imaginaryPart

/-- Reflexivity — componentwise real reflexivity. -/
theorem denotesSameComplexRefl (value : ComplexReal) :
    DenotesSameComplex value value :=
  ⟨denotesSameRealRefl value.realPart, denotesSameRealRefl value.imaginaryPart⟩

/-- Symmetry — componentwise. -/
theorem denotesSameComplexSymm {leftValue rightValue : ComplexReal}
    (areSame : DenotesSameComplex leftValue rightValue) :
    DenotesSameComplex rightValue leftValue :=
  ⟨denotesSameRealSymm areSame.left, denotesSameRealSymm areSame.right⟩

/-- Transitivity — componentwise. -/
theorem denotesSameComplexTrans {firstValue middleValue lastValue : ComplexReal}
    (isFirstSame : DenotesSameComplex firstValue middleValue)
    (isLastSame : DenotesSameComplex middleValue lastValue) :
    DenotesSameComplex firstValue lastValue :=
  ⟨denotesSameRealTrans isFirstSame.left isLastSame.left,
    denotesSameRealTrans isFirstSame.right isLastSame.right⟩

/-! ## Operations and constants -/

/-- Componentwise addition. -/
def addComplex (leftValue rightValue : ComplexReal) : ComplexReal :=
  { realPart := addReal leftValue.realPart rightValue.realPart
    imaginaryPart := addReal leftValue.imaginaryPart rightValue.imaginaryPart }

/-- Componentwise negation. -/
def negComplex (value : ComplexReal) : ComplexReal :=
  { realPart := negReal value.realPart
    imaginaryPart := negReal value.imaginaryPart }

/-- Componentwise subtraction. -/
def subComplex (leftValue rightValue : ComplexReal) : ComplexReal :=
  { realPart := subReal leftValue.realPart rightValue.realPart
    imaginaryPart := subReal leftValue.imaginaryPart rightValue.imaginaryPart }

/-- The Gauss product `(a+bi)(c+di) = (ac - bd) + (ad + bc) i`. -/
def mulComplex (leftValue rightValue : ComplexReal) : ComplexReal :=
  { realPart :=
      subReal (mulReal leftValue.realPart rightValue.realPart)
        (mulReal leftValue.imaginaryPart rightValue.imaginaryPart)
    imaginaryPart :=
      addReal (mulReal leftValue.realPart rightValue.imaginaryPart)
        (mulReal leftValue.imaginaryPart rightValue.realPart) }

/-- Complex conjugation `conj(a+bi) = a - bi` — the `*`-ring involution. -/
def conjComplex (value : ComplexReal) : ComplexReal :=
  { realPart := value.realPart
    imaginaryPart := negReal value.imaginaryPart }

/-- The additive/complex zero `0 + 0i`. -/
def zeroComplex : ComplexReal :=
  { realPart := constantReal zeroRational
    imaginaryPart := constantReal zeroRational }

/-- The multiplicative unit `1 + 0i`. -/
def oneComplex : ComplexReal :=
  { realPart := constantReal oneRational
    imaginaryPart := constantReal zeroRational }

/-- The imaginary unit `0 + 1i`. -/
def imaginaryUnit : ComplexReal :=
  { realPart := constantReal zeroRational
    imaginaryPart := constantReal oneRational }

/-! ## Operation congruences — every op respects the product setoid

Each rides the shipped `RegularReal` setoid congruences alone; no ring law. -/

/-- Addition respects the product setoid. -/
theorem addComplexRespectsDenotesSame
    {leftValue newLeftValue rightValue newRightValue : ComplexReal}
    (leftAgrees : DenotesSameComplex leftValue newLeftValue)
    (rightAgrees : DenotesSameComplex rightValue newRightValue) :
    DenotesSameComplex (addComplex leftValue rightValue)
      (addComplex newLeftValue newRightValue) :=
  ⟨addRealRespectsDenotesSame leftAgrees.left rightAgrees.left,
    addRealRespectsDenotesSame leftAgrees.right rightAgrees.right⟩

/-- Negation respects the product setoid. -/
theorem negComplexRespectsDenotesSame
    {leftValue newLeftValue : ComplexReal}
    (areSame : DenotesSameComplex leftValue newLeftValue) :
    DenotesSameComplex (negComplex leftValue) (negComplex newLeftValue) :=
  ⟨negRealRespectsDenotesSame areSame.left,
    negRealRespectsDenotesSame areSame.right⟩

/-- Subtraction respects the product setoid. -/
theorem subComplexRespectsDenotesSame
    {leftValue newLeftValue rightValue newRightValue : ComplexReal}
    (leftAgrees : DenotesSameComplex leftValue newLeftValue)
    (rightAgrees : DenotesSameComplex rightValue newRightValue) :
    DenotesSameComplex (subComplex leftValue rightValue)
      (subComplex newLeftValue newRightValue) :=
  ⟨subRealRespectsDenotesSame leftAgrees.left rightAgrees.left,
    subRealRespectsDenotesSame leftAgrees.right rightAgrees.right⟩

/-- Multiplication respects the product setoid — each of the four
sub-products rides its own `mulRealRespectsDenotesSame`; the cross-index
slack lives inside that shipped congruence. -/
theorem mulComplexRespectsDenotesSame
    {leftValue newLeftValue rightValue newRightValue : ComplexReal}
    (leftAgrees : DenotesSameComplex leftValue newLeftValue)
    (rightAgrees : DenotesSameComplex rightValue newRightValue) :
    DenotesSameComplex (mulComplex leftValue rightValue)
      (mulComplex newLeftValue newRightValue) :=
  ⟨subRealRespectsDenotesSame
      (mulRealRespectsDenotesSame leftAgrees.left rightAgrees.left)
      (mulRealRespectsDenotesSame leftAgrees.right rightAgrees.right),
    addRealRespectsDenotesSame
      (mulRealRespectsDenotesSame leftAgrees.left rightAgrees.right)
      (mulRealRespectsDenotesSame leftAgrees.right rightAgrees.left)⟩

/-- Conjugation respects the product setoid. -/
theorem conjComplexRespectsDenotesSame
    {leftValue newLeftValue : ComplexReal}
    (areSame : DenotesSameComplex leftValue newLeftValue) :
    DenotesSameComplex (conjComplex leftValue) (conjComplex newLeftValue) :=
  ⟨areSame.left, negRealRespectsDenotesSame areSame.right⟩

/-! ## Conjugation laws — reachable without the slack-closure ring bricks -/

/-- `conj(conj z) ~ z` — real part reflexive, imaginary part double negation. -/
theorem conjComplexInvolutive (value : ComplexReal) :
    DenotesSameComplex (conjComplex (conjComplex value)) value :=
  ⟨denotesSameRealRefl value.realPart,
    negRealNegRealDenotesSame value.imaginaryPart⟩

/-- `conj(z + w) ~ conj z + conj w` — real part reflexive, imaginary part is
`neg(a + b) ~ neg a + neg b`. -/
theorem conjComplexAddComplex (leftValue rightValue : ComplexReal) :
    DenotesSameComplex (conjComplex (addComplex leftValue rightValue))
      (addComplex (conjComplex leftValue) (conjComplex rightValue)) :=
  ⟨denotesSameRealRefl (addReal leftValue.realPart rightValue.realPart),
    negRealAddRealDenotesSame leftValue.imaginaryPart
      rightValue.imaginaryPart⟩

/-- `conj(z * w) ~ conj z * conj w` — the one conj law with content, but pure
negation-passing: the real part pulls a double negation out of `(-b)(-d)`,
the imaginary part pushes negations inward through the product and folds them
over the sum.  No `mulRealComm/Assoc/Distrib`. -/
theorem conjComplexMulComplex (leftValue rightValue : ComplexReal) :
    DenotesSameComplex (conjComplex (mulComplex leftValue rightValue))
      (mulComplex (conjComplex leftValue) (conjComplex rightValue)) :=
  have imaginaryProductSignsFold :
      DenotesSameReal
        (mulReal (negReal leftValue.imaginaryPart)
          (negReal rightValue.imaginaryPart))
        (mulReal leftValue.imaginaryPart rightValue.imaginaryPart) :=
    denotesSameRealTrans
      (mulRealNegLeftDenotesSame leftValue.imaginaryPart
        (negReal rightValue.imaginaryPart))
      (denotesSameRealTrans
        (negRealRespectsDenotesSame
          (mulRealNegRightDenotesSame leftValue.imaginaryPart
            rightValue.imaginaryPart))
        (negRealNegRealDenotesSame
          (mulReal leftValue.imaginaryPart rightValue.imaginaryPart)))
  ⟨subRealRespectsDenotesSame
      (denotesSameRealRefl
        (mulReal leftValue.realPart rightValue.realPart))
      (denotesSameRealSymm imaginaryProductSignsFold),
    denotesSameRealTrans
      (negRealAddRealDenotesSame
        (mulReal leftValue.realPart rightValue.imaginaryPart)
        (mulReal leftValue.imaginaryPart rightValue.realPart))
      (addRealRespectsDenotesSame
        (denotesSameRealSymm
          (mulRealNegRightDenotesSame leftValue.realPart
            rightValue.imaginaryPart))
        (denotesSameRealSymm
          (mulRealNegLeftDenotesSame leftValue.imaginaryPart
            rightValue.realPart)))⟩

/-! ## Commutative-ring laws (the closable half)

Commutativity, additive inverse, and the identities lift the componentwise
`RegularReal` ring laws.  Associativity of `+` and assoc/distrib of `·` wait
on the slack-closure ℝ bricks. -/

/-- **Addition is commutative** — componentwise `addRealComm`. -/
theorem addComplexComm (leftValue rightValue : ComplexReal) :
    DenotesSameComplex (addComplex leftValue rightValue)
      (addComplex rightValue leftValue) :=
  ⟨addRealComm leftValue.realPart rightValue.realPart,
    addRealComm leftValue.imaginaryPart rightValue.imaginaryPart⟩

/-- **Zero is a right identity** for complex addition — componentwise. -/
theorem addComplexZeroRight (value : ComplexReal) :
    DenotesSameComplex (addComplex value zeroComplex) value :=
  ⟨addRealZeroRight value.realPart, addRealZeroRight value.imaginaryPart⟩

/-- **Addition is associative** — componentwise `addRealAssoc`. -/
theorem addComplexAssoc (firstValue middleValue lastValue : ComplexReal) :
    DenotesSameComplex
      (addComplex (addComplex firstValue middleValue) lastValue)
      (addComplex firstValue (addComplex middleValue lastValue)) :=
  ⟨addRealAssoc firstValue.realPart middleValue.realPart lastValue.realPart,
    addRealAssoc firstValue.imaginaryPart middleValue.imaginaryPart
      lastValue.imaginaryPart⟩

/-- **Zero is a left identity** for complex addition — componentwise. -/
theorem addComplexZeroLeft (value : ComplexReal) :
    DenotesSameComplex (addComplex zeroComplex value) value :=
  ⟨addRealZeroLeft value.realPart, addRealZeroLeft value.imaginaryPart⟩

/-- **Negation is a right inverse** for complex addition — componentwise. -/
theorem addComplexNegRight (value : ComplexReal) :
    DenotesSameComplex (addComplex value (negComplex value)) zeroComplex :=
  ⟨addRealNegRight value.realPart, addRealNegRight value.imaginaryPart⟩

/-- **Multiplication is commutative** — real part swaps both products under
the difference; imaginary part swaps both products then commutes the sum. -/
theorem mulComplexComm (leftValue rightValue : ComplexReal) :
    DenotesSameComplex (mulComplex leftValue rightValue)
      (mulComplex rightValue leftValue) :=
  ⟨subRealRespectsDenotesSame
      (mulRealComm leftValue.realPart rightValue.realPart)
      (mulRealComm leftValue.imaginaryPart rightValue.imaginaryPart),
    denotesSameRealTrans
      (addRealRespectsDenotesSame
        (mulRealComm leftValue.realPart rightValue.imaginaryPart)
        (mulRealComm leftValue.imaginaryPart rightValue.realPart))
      (addRealComm
        (mulReal rightValue.imaginaryPart leftValue.realPart)
        (mulReal rightValue.realPart leftValue.imaginaryPart))⟩

/-- **One is a right identity** for complex multiplication — the real part
collapses `re*1 - im*0` to `re - 0 ~ re`; the imaginary part collapses
`re*0 + im*1` to `0 + im ~ im`. -/
theorem mulComplexOneRight (value : ComplexReal) :
    DenotesSameComplex (mulComplex value oneComplex) value :=
  ⟨denotesSameRealTrans
      (subRealRespectsDenotesSame
        (mulRealOneRight value.realPart)
        (mulRealZeroRight value.imaginaryPart))
      (subRealZeroRightDenotesSame value.realPart),
    denotesSameRealTrans
      (addRealRespectsDenotesSame
        (mulRealZeroRight value.realPart)
        (mulRealOneRight value.imaginaryPart))
      (addRealZeroLeft value.imaginaryPart)⟩

end FX1Poly.ComputerAlgebra
