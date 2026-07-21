import FX1Poly.ComputerAlgebra.Number.RegularRealRing

/-! # ComplexReal — the Gaussian reals over `RegularReal`

The ℂ carrier: a pair of Bishop regular reals `(re, im)`.  `ComplexReal` is
`RegularReal × RegularReal`, its sameness the product setoid (both components
denote the same real), and its operations componentwise except `mulComplex`,
the Gauss product `(a+bi)(c+di) = (ac - bd) + (ad + bc) i`.

Everything here composes the ℝ layer:

* the setoid refl/symm/trans and every operation congruence ride the
  `RegularReal` setoid and congruences alone — no ring law;
* the conjugation laws (`conj∘conj`, `conj` over `+`, `conj` over `·`) ride the
  negation-passing lemmas — pointwise reals, no ring reassociation;
* the commutative-ring laws lift the `RegularReal` ring laws componentwise;
  commutativity, identities, and additive inverse close here, and associativity
  of `+` and associativity/distributivity of `·` use the ℝ slack-closure lemmas
  (`addRealAssoc`, `mulRealAssoc`, `mulRealLeftDistrib`).

Sameness is undecidable (inherited from `DenotesSameReal`), never `Eq` on the
approximation sequences, so no `funext`, no `Quot`, zero axioms throughout.

The modulus `|z| = sqrt(a^2 + b^2)` and the Heyting-field structure are the
metric layer, out of scope here — they require `sqrtReal`. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-- A complex regular real: a pair of Bishop reals. -/
structure ComplexReal where
  realPart : RegularReal
  imaginaryPart : RegularReal

/-- Sameness of complex reals: the product setoid, both components denote the
same Bishop real.  Undecidable, inherited from `DenotesSameReal`. -/
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

/-! ## Operation congruences — every operation respects the product setoid

Each rides the `RegularReal` setoid congruences alone; no ring law. -/

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
sub-products rides its own `mulRealRespectsDenotesSame`; the cross-index slack
lives inside that congruence. -/
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

/-! ## Conjugation laws (no ring reassociation needed) -/

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

/-! ## Commutative-ring laws

Commutativity, additive inverse, and the identities lift the componentwise
`RegularReal` ring laws.  Associativity of `+` and associativity/distributivity
of `·` use the ℝ slack-closure lemmas. -/

/-- Addition is commutative, componentwise `addRealComm`. -/
theorem addComplexComm (leftValue rightValue : ComplexReal) :
    DenotesSameComplex (addComplex leftValue rightValue)
      (addComplex rightValue leftValue) :=
  ⟨addRealComm leftValue.realPart rightValue.realPart,
    addRealComm leftValue.imaginaryPart rightValue.imaginaryPart⟩

/-- Zero is a right identity for complex addition, componentwise. -/
theorem addComplexZeroRight (value : ComplexReal) :
    DenotesSameComplex (addComplex value zeroComplex) value :=
  ⟨addRealZeroRight value.realPart, addRealZeroRight value.imaginaryPart⟩

/-- Addition is associative, componentwise `addRealAssoc`. -/
theorem addComplexAssoc (firstValue middleValue lastValue : ComplexReal) :
    DenotesSameComplex
      (addComplex (addComplex firstValue middleValue) lastValue)
      (addComplex firstValue (addComplex middleValue lastValue)) :=
  ⟨addRealAssoc firstValue.realPart middleValue.realPart lastValue.realPart,
    addRealAssoc firstValue.imaginaryPart middleValue.imaginaryPart
      lastValue.imaginaryPart⟩

/-- Zero is a left identity for complex addition, componentwise. -/
theorem addComplexZeroLeft (value : ComplexReal) :
    DenotesSameComplex (addComplex zeroComplex value) value :=
  ⟨addRealZeroLeft value.realPart, addRealZeroLeft value.imaginaryPart⟩

/-- Negation is a right inverse for complex addition, componentwise. -/
theorem addComplexNegRight (value : ComplexReal) :
    DenotesSameComplex (addComplex value (negComplex value)) zeroComplex :=
  ⟨addRealNegRight value.realPart, addRealNegRight value.imaginaryPart⟩

/-- Multiplication is commutative: the real part swaps both products under the
difference; the imaginary part swaps both products then commutes the sum. -/
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

/-- One is a right identity for complex multiplication: the real part collapses
`re*1 - im*0` to `re - 0 ~ re`; the imaginary part collapses `re*0 + im*1` to
`0 + im ~ im`. -/
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

/-- Left distributivity `z·(w + u) ~ z·w + z·u`, componentwise: the real part
distributes each `mulReal` over the addend sums (`mulRealLeftDistrib`) then
cross-pairs the two differences (`subRealCrossPairsDenotesSame`); the imaginary
part distributes then medial-swaps the four products. -/
theorem mulComplexLeftDistrib (leftValue middleValue rightValue : ComplexReal) :
    DenotesSameComplex
      (mulComplex leftValue (addComplex middleValue rightValue))
      (addComplex (mulComplex leftValue middleValue)
        (mulComplex leftValue rightValue)) :=
  ⟨denotesSameRealTrans
      (subRealRespectsDenotesSame
        (mulRealLeftDistrib leftValue.realPart middleValue.realPart
          rightValue.realPart)
        (mulRealLeftDistrib leftValue.imaginaryPart middleValue.imaginaryPart
          rightValue.imaginaryPart))
      (subRealCrossPairsDenotesSame
        (mulReal leftValue.realPart middleValue.realPart)
        (mulReal leftValue.realPart rightValue.realPart)
        (mulReal leftValue.imaginaryPart middleValue.imaginaryPart)
        (mulReal leftValue.imaginaryPart rightValue.imaginaryPart)),
    denotesSameRealTrans
      (addRealRespectsDenotesSame
        (mulRealLeftDistrib leftValue.realPart middleValue.imaginaryPart
          rightValue.imaginaryPart)
        (mulRealLeftDistrib leftValue.imaginaryPart middleValue.realPart
          rightValue.realPart))
      (addRealMedial
        (mulReal leftValue.realPart middleValue.imaginaryPart)
        (mulReal leftValue.realPart rightValue.imaginaryPart)
        (mulReal leftValue.imaginaryPart middleValue.realPart)
        (mulReal leftValue.imaginaryPart rightValue.realPart))⟩

/-- Multiplication is associative `(z·w)·u ~ z·(w·u)`: each component is an
eight-term Gauss cross-expansion.  Both sides expand (via `·` over
subtraction/addition and `mulRealAssoc`) into the same four signed triple
products; a purely additive reorder (medial and commutativity) reconciles the
two groupings. -/
theorem mulComplexAssoc (firstValue middleValue lastValue : ComplexReal) :
    DenotesSameComplex
      (mulComplex (mulComplex firstValue middleValue) lastValue)
      (mulComplex firstValue (mulComplex middleValue lastValue)) :=
  let firstReal := firstValue.realPart
  let firstImag := firstValue.imaginaryPart
  let middleReal := middleValue.realPart
  let middleImag := middleValue.imaginaryPart
  let lastReal := lastValue.realPart
  let lastImag := lastValue.imaginaryPart
  let realRealReal := mulReal firstReal (mulReal middleReal lastReal)
  let realRealImag := mulReal firstReal (mulReal middleReal lastImag)
  let realImagReal := mulReal firstReal (mulReal middleImag lastReal)
  let realImagImag := mulReal firstReal (mulReal middleImag lastImag)
  let imagRealReal := mulReal firstImag (mulReal middleReal lastReal)
  let imagRealImag := mulReal firstImag (mulReal middleReal lastImag)
  let imagImagReal := mulReal firstImag (mulReal middleImag lastReal)
  let imagImagImag := mulReal firstImag (mulReal middleImag lastImag)
  have realReorder :
      DenotesSameReal
        (subReal (subReal realRealReal imagImagReal)
          (addReal realImagImag imagRealImag))
        (subReal (subReal realRealReal realImagImag)
          (addReal imagRealImag imagImagReal)) :=
    denotesSameRealTrans
      (addRealRespectsDenotesSame
        (denotesSameRealRefl (subReal realRealReal imagImagReal))
        (negRealAddRealDenotesSame realImagImag imagRealImag))
      (denotesSameRealTrans
        (addRealMedial realRealReal (negReal imagImagReal)
          (negReal realImagImag) (negReal imagRealImag))
        (addRealRespectsDenotesSame
          (denotesSameRealRefl (addReal realRealReal (negReal realImagImag)))
          (denotesSameRealTrans
            (addRealComm (negReal imagImagReal) (negReal imagRealImag))
            (denotesSameRealSymm
              (negRealAddRealDenotesSame imagRealImag imagImagReal)))))
  have imagReorder :
      DenotesSameReal
        (addReal (subReal realRealImag imagImagImag)
          (addReal realImagReal imagRealReal))
        (addReal (addReal realRealImag realImagReal)
          (subReal imagRealReal imagImagImag)) :=
    denotesSameRealTrans
      (addRealMedial realRealImag (negReal imagImagImag) realImagReal
        imagRealReal)
      (addRealRespectsDenotesSame
        (denotesSameRealRefl (addReal realRealImag realImagReal))
        (addRealComm (negReal imagImagImag) imagRealReal))
  ⟨denotesSameRealTrans
      (subRealRespectsDenotesSame
        (denotesSameRealTrans
          (mulRealSubRealRightDenotesSame (mulReal firstReal middleReal)
            (mulReal firstImag middleImag) lastReal)
          (subRealRespectsDenotesSame
            (mulRealAssoc firstReal middleReal lastReal)
            (mulRealAssoc firstImag middleImag lastReal)))
        (denotesSameRealTrans
          (mulRealRightDistrib (mulReal firstReal middleImag)
            (mulReal firstImag middleReal) lastImag)
          (addRealRespectsDenotesSame
            (mulRealAssoc firstReal middleImag lastImag)
            (mulRealAssoc firstImag middleReal lastImag))))
      (denotesSameRealTrans realReorder
        (denotesSameRealSymm
          (subRealRespectsDenotesSame
            (mulRealSubRealDenotesSame firstReal
              (mulReal middleReal lastReal) (mulReal middleImag lastImag))
            (mulRealLeftDistrib firstImag (mulReal middleReal lastImag)
              (mulReal middleImag lastReal))))),
    denotesSameRealTrans
      (addRealRespectsDenotesSame
        (denotesSameRealTrans
          (mulRealSubRealRightDenotesSame (mulReal firstReal middleReal)
            (mulReal firstImag middleImag) lastImag)
          (subRealRespectsDenotesSame
            (mulRealAssoc firstReal middleReal lastImag)
            (mulRealAssoc firstImag middleImag lastImag)))
        (denotesSameRealTrans
          (mulRealRightDistrib (mulReal firstReal middleImag)
            (mulReal firstImag middleReal) lastReal)
          (addRealRespectsDenotesSame
            (mulRealAssoc firstReal middleImag lastReal)
            (mulRealAssoc firstImag middleReal lastReal))))
      (denotesSameRealTrans imagReorder
        (denotesSameRealSymm
          (addRealRespectsDenotesSame
            (mulRealLeftDistrib firstReal (mulReal middleReal lastImag)
              (mulReal middleImag lastReal))
            (mulRealSubRealDenotesSame firstImag
              (mulReal middleReal lastReal) (mulReal middleImag lastImag)))))⟩

/-! ## The commutative-ring certificate

One setoid-relative `CommutativeRingWitness` structure, instantiated on both ℝ
and ℂ.  Each field doubles as a completeness checklist for the ring corpus. -/

/-- A setoid-relative commutative ring: carrier, sameness relation, the
zero/one/add/mul/neg operations, the setoid trio, the three operation
congruences, the eight ring laws, and nontriviality (`0` is apart from `1`).
Leaner than the ℚ Heyting-field witness: no order, no decidability, no inverse —
ℂ is neither ordered nor decidable and not a field. -/
structure CommutativeRingWitness (carrier : Type) where
  denotesSame : carrier → carrier → Prop
  zero : carrier
  one : carrier
  add : carrier → carrier → carrier
  mul : carrier → carrier → carrier
  neg : carrier → carrier
  denotesSameIsReflexive : ∀ value : carrier, denotesSame value value
  denotesSameIsSymmetric :
    ∀ leftValue rightValue : carrier,
      denotesSame leftValue rightValue → denotesSame rightValue leftValue
  denotesSameIsTransitive :
    ∀ firstValue middleValue lastValue : carrier,
      denotesSame firstValue middleValue → denotesSame middleValue lastValue →
        denotesSame firstValue lastValue
  addRespectsDenotesSame :
    ∀ leftValue newLeftValue rightValue newRightValue : carrier,
      denotesSame leftValue newLeftValue → denotesSame rightValue newRightValue →
        denotesSame (add leftValue rightValue) (add newLeftValue newRightValue)
  mulRespectsDenotesSame :
    ∀ leftValue newLeftValue rightValue newRightValue : carrier,
      denotesSame leftValue newLeftValue → denotesSame rightValue newRightValue →
        denotesSame (mul leftValue rightValue) (mul newLeftValue newRightValue)
  negRespectsDenotesSame :
    ∀ leftValue rightValue : carrier,
      denotesSame leftValue rightValue → denotesSame (neg leftValue) (neg rightValue)
  addIsCommutative :
    ∀ leftSummand rightSummand : carrier,
      denotesSame (add leftSummand rightSummand) (add rightSummand leftSummand)
  addIsAssociative :
    ∀ firstSummand secondSummand thirdSummand : carrier,
      denotesSame (add (add firstSummand secondSummand) thirdSummand)
        (add firstSummand (add secondSummand thirdSummand))
  zeroIsRightAdditiveIdentity :
    ∀ value : carrier, denotesSame (add value zero) value
  negIsRightAdditiveInverse :
    ∀ value : carrier, denotesSame (add value (neg value)) zero
  mulIsCommutative :
    ∀ leftFactor rightFactor : carrier,
      denotesSame (mul leftFactor rightFactor) (mul rightFactor leftFactor)
  mulIsAssociative :
    ∀ leftFactor middleFactor rightFactor : carrier,
      denotesSame (mul (mul leftFactor middleFactor) rightFactor)
        (mul leftFactor (mul middleFactor rightFactor))
  oneIsRightMultiplicativeIdentity :
    ∀ value : carrier, denotesSame (mul value one) value
  mulDistributesOverAdd :
    ∀ factor leftSummand rightSummand : carrier,
      denotesSame (mul factor (add leftSummand rightSummand))
        (add (mul factor leftSummand) (mul factor rightSummand))
  zeroIsApartFromOne : Not (denotesSame zero one)

/-- Nontriviality of ℝ — the constant reals `0` and `1` reflect to the ℚ
constants, whose cross-products disagree as `ofNat` payloads. -/
theorem regularRealZeroIsApartFromOne :
    Not (DenotesSameReal (constantReal zeroRational) (constantReal oneRational)) :=
  fun sameReal =>
    Nat.noConfusion (Int.ofNat.inj (denotesSameAsOfConstantRealDenotesSame sameReal))

/-- The ℝ certificate: `RegularReal` with its corpus is a commutative ring up to
the Bishop setoid. -/
def regularRealCommutativeRingWitness : CommutativeRingWitness RegularReal where
  denotesSame := DenotesSameReal
  zero := constantReal zeroRational
  one := constantReal oneRational
  add := addReal
  mul := mulReal
  neg := negReal
  denotesSameIsReflexive := denotesSameRealRefl
  denotesSameIsSymmetric := fun _ _ areSame => denotesSameRealSymm areSame
  denotesSameIsTransitive := fun _ _ _ firstAgrees lastAgrees =>
    denotesSameRealTrans firstAgrees lastAgrees
  addRespectsDenotesSame := fun _ _ _ _ leftAgrees rightAgrees =>
    addRealRespectsDenotesSame leftAgrees rightAgrees
  mulRespectsDenotesSame := fun _ _ _ _ leftAgrees rightAgrees =>
    mulRealRespectsDenotesSame leftAgrees rightAgrees
  negRespectsDenotesSame := fun _ _ areSame => negRealRespectsDenotesSame areSame
  addIsCommutative := addRealComm
  addIsAssociative := addRealAssoc
  zeroIsRightAdditiveIdentity := addRealZeroRight
  negIsRightAdditiveInverse := addRealNegRight
  mulIsCommutative := mulRealComm
  mulIsAssociative := mulRealAssoc
  oneIsRightMultiplicativeIdentity := mulRealOneRight
  mulDistributesOverAdd := mulRealLeftDistrib
  zeroIsApartFromOne := regularRealZeroIsApartFromOne

/-- Nontriviality of ℂ — the real components of `0 + 0i` and `1 + 0i` are the
apart ℝ constants. -/
theorem complexRealZeroIsApartFromOne :
    Not (DenotesSameComplex zeroComplex oneComplex) :=
  fun sameComplex => regularRealZeroIsApartFromOne sameComplex.left

/-- The ℂ certificate: `ComplexReal` is a commutative ring up to the product
setoid — every field lifts a `RegularReal` ring law componentwise through the
Gauss product. -/
def complexCommutativeRingWitness : CommutativeRingWitness ComplexReal where
  denotesSame := DenotesSameComplex
  zero := zeroComplex
  one := oneComplex
  add := addComplex
  mul := mulComplex
  neg := negComplex
  denotesSameIsReflexive := denotesSameComplexRefl
  denotesSameIsSymmetric := fun _ _ areSame => denotesSameComplexSymm areSame
  denotesSameIsTransitive := fun _ _ _ firstAgrees lastAgrees =>
    denotesSameComplexTrans firstAgrees lastAgrees
  addRespectsDenotesSame := fun _ _ _ _ leftAgrees rightAgrees =>
    addComplexRespectsDenotesSame leftAgrees rightAgrees
  mulRespectsDenotesSame := fun _ _ _ _ leftAgrees rightAgrees =>
    mulComplexRespectsDenotesSame leftAgrees rightAgrees
  negRespectsDenotesSame := fun _ _ areSame =>
    negComplexRespectsDenotesSame areSame
  addIsCommutative := addComplexComm
  addIsAssociative := addComplexAssoc
  zeroIsRightAdditiveIdentity := addComplexZeroRight
  negIsRightAdditiveInverse := addComplexNegRight
  mulIsCommutative := mulComplexComm
  mulIsAssociative := mulComplexAssoc
  oneIsRightMultiplicativeIdentity := mulComplexOneRight
  mulDistributesOverAdd := mulComplexLeftDistrib
  zeroIsApartFromOne := complexRealZeroIsApartFromOne

end FX1Poly.ComputerAlgebra
