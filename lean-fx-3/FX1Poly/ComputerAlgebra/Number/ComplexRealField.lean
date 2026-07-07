import FX1Poly.ComputerAlgebra.Number.ComplexRealModulus

/-! # ComplexRealField — ℂ as an apartness-first Heyting field (NUM-C-2 field)

The Heyting-field structure on `ComplexReal`.  Sameness is undecidable, so
apartness is POSITIVE data: `z` apart from zero IS a positivity witness on the
nonnegative real `|z|^2`.  That single `Type`-valued object collapses the
apartness predicate, the inverse's input, and the field-law hypothesis into
one thing that `inverseReal` eats with zero conversion friction.

* `IsApartFromZeroComplex z := RealPositivityWitness (modulusSquared z)` —
  the honest apartness-first predicate (`|z|^2 > 0`);
* `inverseComplex z apart := conj z / |z|^2` — the conjugate scaled
  componentwise by the shipped real reciprocal `1/|z|^2`;
* `mulComplexInverseComplexDenotesOne` — the Heyting-field law
  `z * z^{-1} ~ 1`, pure ℝ-ring algebra over the shipped real field law
  `mulRealInverseDenotesOne`.  No new estimates: `|z|^2` is a bare ring term,
  so the whole node lands ahead of any √-metric analysis.

The categorical packaging `HeytingFieldWitness` EXTENDS `CommutativeRingWitness`
(the ring skeleton is reused verbatim), adding only the apartness predicate,
the dependent inverse, its setoid-respect, and the cancellation law.  Both ℝ
(riding the shipped `inverseRealOfApartness`) and ℂ are instances.

Honest wall: `inverseComplex` carries NO setoid congruence — its argument is
`Type`-valued positivity data, not setoid-stable across `z`.  This mirrors the
ℝ layer, which likewise ships no congruence for `inverseReal`; the field law is
the deliverable.  Zero axioms throughout. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-! ## Apartness from zero -/

/-- **`z` is apart from zero** — a positivity witness on `|z|^2`.  Inhabited
exactly when `|z|^2 > 0`, i.e. constructively `z # 0`.  `Type`-valued: the
inverse computes from the witness's margin index. -/
def IsApartFromZeroComplex (value : ComplexReal) : Type :=
  RealPositivityWitness (modulusSquared value)

/-- `|z|^2` respects the product setoid — componentwise square congruence. -/
theorem modulusSquaredRespectsDenotesSame {leftValue rightValue : ComplexReal}
    (areSame : DenotesSameComplex leftValue rightValue) :
    DenotesSameReal (modulusSquared leftValue) (modulusSquared rightValue) :=
  addRealRespectsDenotesSame
    (mulRealRespectsDenotesSame areSame.left areSame.left)
    (mulRealRespectsDenotesSame areSame.right areSame.right)

/-- Apartness from zero transports along the product setoid — the positivity
witness rides `|z|^2`'s congruence. -/
def isApartFromZeroComplexRespectsDenotesSame {leftValue rightValue : ComplexReal}
    (areSame : DenotesSameComplex leftValue rightValue)
    (apart : IsApartFromZeroComplex leftValue) : IsApartFromZeroComplex rightValue :=
  realPositivityWitnessCongr (modulusSquaredRespectsDenotesSame areSame) apart

/-! ## Smart constructors — apartness from a component apart from zero

The canonical apartness IS positivity of `|z|^2`; these BUILD it from the more
familiar "the real OR the imaginary part is apart from zero".  The one
estimate-bearing brick is `realPositivityWitnessAddNonNegRight` (positive +
nonnegative stays positive), a direct clone of the shipped
`realPositivityWitnessMulReal` tail pattern. -/

/-- **Positive + nonnegative stays positive** — the sole new estimate.  At the
doubled tail index `2*(2w+1)+1` the half margin of `leftValue` survives
(`tailStaysAboveHalfMargin`), and the nonnegative `rightValue` addend only grows
the sum, so the margin re-reads EXACTLY as the doubled margin there
(`reciprocalHalvesDenotesSame`). -/
def realPositivityWitnessAddNonNegRight {leftValue rightValue : RegularReal}
    (witness : RealPositivityWitness leftValue)
    (isRightNonNegative : IsNonNegativeReal rightValue) :
    RealPositivityWitness (addReal leftValue rightValue) :=
  let tailIndex := 2 * witness.marginIndex + 1
  let newMarginIndex := 2 * tailIndex + 1
  { marginIndex := newMarginIndex
    hasDoubledMargin :=
      have isDeep : tailIndex ≤ 2 * newMarginIndex + 1 :=
        natLeTrans (natSelfLeDoubleSelfSucc tailIndex)
          (natSelfLeDoubleSelfSucc newMarginIndex)
      have tail : LessEqualAs (reciprocalOfSucc tailIndex)
          (leftValue.approximation (2 * newMarginIndex + 1)) :=
        tailStaysAboveHalfMargin witness.hasDoubledMargin isDeep
      have grows : LessEqualAs (leftValue.approximation (2 * newMarginIndex + 1))
          (addExact (leftValue.approximation (2 * newMarginIndex + 1))
            (rightValue.approximation (2 * newMarginIndex + 1))) :=
        lessEqualAsSelfAddNonNegRight
          (leftValue.approximation (2 * newMarginIndex + 1))
          (isRightNonNegative (2 * newMarginIndex + 1))
      lessEqualAsCongrLeft (reciprocalHalvesDenotesSame tailIndex)
        (lessEqualAsTrans tail grows) }

/-- **A component apart from zero squares to a positive** — dispatch on the
apartness side; both feed `realPositivityWitnessMulReal`, the below-zero arm
folding the double negation `(-v)(-v) ~ v*v`. -/
def realPositivityWitnessOfSquareApart {value : RegularReal}
    (apart : RealApartnessWitness value (constantReal zeroRational)) :
    RealPositivityWitness (mulReal value value) :=
  match apart with
  | .inr isAboveZero =>
      realPositivityWitnessMulReal
        (realPositivityWitnessOfAboveZero isAboveZero)
        (realPositivityWitnessOfAboveZero isAboveZero)
  | .inl isBelowZero =>
      realPositivityWitnessCongr
        (denotesSameRealTrans
          (mulRealNegLeftDenotesSame value (negReal value))
          (denotesSameRealTrans
            (negRealRespectsDenotesSame (mulRealNegRightDenotesSame value value))
            (negRealNegRealDenotesSame (mulReal value value))))
        (realPositivityWitnessMulReal
          (negRealPositivityWitnessOfBelowZero isBelowZero)
          (negRealPositivityWitnessOfBelowZero isBelowZero))

/-- **`z` apart from zero from its real part apart** — `a^2 > 0` and `b^2 >= 0`. -/
def isApartFromZeroComplexOfRealPartApart {value : ComplexReal}
    (realApart : RealApartnessWitness value.realPart (constantReal zeroRational)) :
    IsApartFromZeroComplex value :=
  realPositivityWitnessAddNonNegRight
    (realPositivityWitnessOfSquareApart realApart)
    (mulRealSelfIsNonNegativeReal value.imaginaryPart)

/-- **`z` apart from zero from its imaginary part apart** — `b^2 > 0` and
`a^2 >= 0`, transported across `addRealComm` to reuse the right-summand brick. -/
def isApartFromZeroComplexOfImagPartApart {value : ComplexReal}
    (imagApart : RealApartnessWitness value.imaginaryPart (constantReal zeroRational)) :
    IsApartFromZeroComplex value :=
  realPositivityWitnessCongr
    (addRealComm (mulReal value.imaginaryPart value.imaginaryPart)
      (mulReal value.realPart value.realPart))
    (realPositivityWitnessAddNonNegRight
      (realPositivityWitnessOfSquareApart imagApart)
      (mulRealSelfIsNonNegativeReal value.realPart))

/-! ## The inverse -/

/-- **The complex inverse** `z^{-1} = conj z / |z|^2` — the conjugate scaled
componentwise by the real reciprocal `1/|z|^2` (shipped `inverseReal` on the
positivity witness).  No `sqrtReal`, no modulus metric. -/
def inverseComplex (value : ComplexReal) (apart : IsApartFromZeroComplex value) :
    ComplexReal :=
  { realPart := mulReal value.realPart (inverseReal apart)
    imaginaryPart := negReal (mulReal value.imaginaryPart (inverseReal apart)) }

/-! ## The Heyting-field law -/

/-- **The Heyting-field law** `z * z^{-1} ~ 1` on apartness.  The real part
collapses `a * (a r) - b * (-(b r))` to `(a^2 + b^2) * r = |z|^2 * (1/|z|^2) ~ 1`
via the shipped real field law; the imaginary part collapses the cross terms
`a * (-(b r)) + b * (a r)` to `(-X) + X ~ 0` with `X = a * (b r)`.  Pure
ℝ-ring algebra — no new estimates. -/
theorem mulComplexInverseComplexDenotesOne (value : ComplexReal)
    (apart : IsApartFromZeroComplex value) :
    DenotesSameComplex (mulComplex value (inverseComplex value apart)) oneComplex :=
  let realPartValue := value.realPart
  let imaginaryPartValue := value.imaginaryPart
  let reciprocal := inverseReal apart
  let crossProduct := mulReal realPartValue (mulReal imaginaryPartValue reciprocal)
  ⟨denotesSameRealTrans
      (addRealRespectsDenotesSame
        (denotesSameRealRefl
          (mulReal realPartValue (mulReal realPartValue reciprocal)))
        (denotesSameRealTrans
          (negRealRespectsDenotesSame
            (mulRealNegRightDenotesSame imaginaryPartValue
              (mulReal imaginaryPartValue reciprocal)))
          (negRealNegRealDenotesSame
            (mulReal imaginaryPartValue (mulReal imaginaryPartValue reciprocal)))))
      (denotesSameRealTrans
        (addRealRespectsDenotesSame
          (denotesSameRealSymm
            (mulRealAssoc realPartValue realPartValue reciprocal))
          (denotesSameRealSymm
            (mulRealAssoc imaginaryPartValue imaginaryPartValue reciprocal)))
        (denotesSameRealTrans
          (denotesSameRealSymm
            (mulRealRightDistrib (mulReal realPartValue realPartValue)
              (mulReal imaginaryPartValue imaginaryPartValue) reciprocal))
          (mulRealInverseDenotesOne apart))),
    denotesSameRealTrans
      (addRealRespectsDenotesSame
        (mulRealNegRightDenotesSame realPartValue
          (mulReal imaginaryPartValue reciprocal))
        (denotesSameRealTrans
          (denotesSameRealSymm
            (mulRealAssoc imaginaryPartValue realPartValue reciprocal))
          (denotesSameRealTrans
            (mulRealRespectsDenotesSame
              (mulRealComm imaginaryPartValue realPartValue)
              (denotesSameRealRefl reciprocal))
            (mulRealAssoc realPartValue imaginaryPartValue reciprocal))))
      (denotesSameRealTrans
        (addRealComm (negReal crossProduct) crossProduct)
        (addRealNegRight crossProduct))⟩

/-- **The left law** `z^{-1} * z ~ 1` — commute the product into the right
law. -/
theorem mulComplexInverseComplexLeftDenotesOne (value : ComplexReal)
    (apart : IsApartFromZeroComplex value) :
    DenotesSameComplex (mulComplex (inverseComplex value apart) value) oneComplex :=
  denotesSameComplexTrans
    (mulComplexComm (inverseComplex value apart) value)
    (mulComplexInverseComplexDenotesOne value apart)

/-! ## The apartness-first Heyting-field certificate

The categorical packaging: `CommutativeRingWitness` (§ComplexReal) plus the
field data.  The ring skeleton — setoid trio, congruences, eight ring laws,
nontriviality — is reused verbatim through `extends`; the field adds only the
POSITIVE apartness predicate, the DEPENDENT inverse, its setoid-respect, and
the multiplicative cancellation law.  `inv` is dependent on the apartness
witness (undecidable sameness forbids a total Prop-gated inverse). -/

/-- **A setoid-relative apartness-first Heyting field** — a commutative ring
with a positive apartness-from-zero predicate and a dependent
inverse-on-apartness satisfying `value * inv value apart ~ one`.  Genuinely
constructive: apartness is `Type`-valued data, the inverse consumes it. -/
structure HeytingFieldWitness (carrier : Type) extends CommutativeRingWitness carrier where
  isApartFromZero : carrier → Type
  inv : (value : carrier) → isApartFromZero value → carrier
  isApartFromZeroRespectsDenotesSame :
    ∀ leftValue rightValue : carrier,
      denotesSame leftValue rightValue →
        isApartFromZero leftValue → isApartFromZero rightValue
  mulInvCancelsOnApartness :
    ∀ (value : carrier) (isApart : isApartFromZero value),
      denotesSame (mul value (inv value isApart)) one

/-- **The ℝ certificate**: `RegularReal` is an apartness-first Heyting field —
apartness is a strict separation from zero, the inverse is the shipped
`inverseRealOfApartness`, the law is `mulRealInverseOfApartnessDenotesOne`.
Pure packaging, no new mathematics. -/
def regularRealHeytingFieldWitness : HeytingFieldWitness RegularReal where
  toCommutativeRingWitness := regularRealCommutativeRingWitness
  isApartFromZero := fun value =>
    RealApartnessWitness value (constantReal zeroRational)
  inv := fun _ isApart => inverseRealOfApartness isApart
  isApartFromZeroRespectsDenotesSame := fun _ _ areSame apart =>
    realApartnessWitnessCongr areSame
      (denotesSameRealRefl (constantReal zeroRational)) apart
  mulInvCancelsOnApartness := fun _ isApart =>
    mulRealInverseOfApartnessDenotesOne isApart

/-- **The ℂ certificate**: `ComplexReal` is an apartness-first Heyting field —
apartness is positivity of `|z|^2`, the inverse is `conj z / |z|^2`, the law is
`mulComplexInverseComplexDenotesOne`.  ℂ is a certified Heyting field. -/
def complexHeytingFieldWitness : HeytingFieldWitness ComplexReal where
  toCommutativeRingWitness := complexCommutativeRingWitness
  isApartFromZero := IsApartFromZeroComplex
  inv := inverseComplex
  isApartFromZeroRespectsDenotesSame := fun _ _ areSame apart =>
    isApartFromZeroComplexRespectsDenotesSame areSame apart
  mulInvCancelsOnApartness := mulComplexInverseComplexDenotesOne

end FX1Poly.ComputerAlgebra
