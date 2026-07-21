import FX1Poly.ComputerAlgebra.Number.RationalPair

/-! # The decidable ordered-Heyting-field certificate

The ℚ corpus — setoid, exact field operations, cross-multiplication order, gcd
normal form, inverse on apartness, Archimedean bound, mediant density — packaged
as one value.  The structure is setoid-relative: every law lands in `denotesSame`,
never in `Eq`, so the same shape serves any carrier with a decidable sameness and a
computable canonical form (ℚ here; fixed-point subrings by restriction).  The ℝ
rung deliberately does not fit: its setoid is undecidable and its order is
apartness-first (cotransitivity replaces totality and trichotomy), so ℝ gets a
separate apartness-first certificate.

Every field is a corpus theorem, so the witness doubles as a completeness
checklist for the ℚ corpus.  The one new fact is nontriviality (`0` is apart from
`1`), a constructor-disagreement one-liner mirroring the ℤ certificate. -/

namespace FX1Poly.ComputerAlgebra

/-- A decidable ordered Heyting field up to a setoid, as data: carrier, sameness,
operations, order, and every law as a proof field.  The fields beyond the ℤ
certificate: the setoid replaces `Eq` (with congruence obligations for every
operation), the multiplicative inverse cancels on apartness from zero, sameness
and order are decidable, a computable `normalForm` characterizes the setoid as
`Eq` on canonical representatives, and the order-theoretic legs carry computable
witnesses (the Archimedean bound and the strict between-point). -/
structure DecidableOrderedHeytingFieldWitness (carrier : Type) where
  denotesSame : carrier → carrier → Prop
  lessEqual : carrier → carrier → Prop
  lessThan : carrier → carrier → Prop
  zero : carrier
  one : carrier
  add : carrier → carrier → carrier
  mul : carrier → carrier → carrier
  neg : carrier → carrier
  inv : carrier → carrier
  natEmbed : Nat → carrier
  archimedeanWitness : carrier → Nat
  betweenPoint : carrier → carrier → carrier
  normalForm : carrier → carrier
  denotesSameIsReflexive : ∀ value : carrier, denotesSame value value
  denotesSameIsSymmetric :
    ∀ leftValue rightValue : carrier,
      denotesSame leftValue rightValue → denotesSame rightValue leftValue
  denotesSameIsTransitive :
    ∀ firstValue middleValue lastValue : carrier,
      denotesSame firstValue middleValue → denotesSame middleValue lastValue →
        denotesSame firstValue lastValue
  denotesSameIsDecidable :
    ∀ leftValue rightValue : carrier,
      Decidable (denotesSame leftValue rightValue)
  normalFormIsCanonical :
    ∀ leftValue rightValue : carrier,
      denotesSame leftValue rightValue ↔
        normalForm leftValue = normalForm rightValue
  addRespectsDenotesSame :
    ∀ leftValue newLeftValue rightValue newRightValue : carrier,
      denotesSame leftValue newLeftValue →
        denotesSame rightValue newRightValue →
          denotesSame (add leftValue rightValue) (add newLeftValue newRightValue)
  mulRespectsDenotesSame :
    ∀ leftValue newLeftValue rightValue newRightValue : carrier,
      denotesSame leftValue newLeftValue →
        denotesSame rightValue newRightValue →
          denotesSame (mul leftValue rightValue) (mul newLeftValue newRightValue)
  negRespectsDenotesSame :
    ∀ leftValue rightValue : carrier,
      denotesSame leftValue rightValue →
        denotesSame (neg leftValue) (neg rightValue)
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
  mulInvCancelsOnApartness :
    ∀ value : carrier, Not (denotesSame value zero) →
      denotesSame (mul value (inv value)) one
  zeroIsApartFromOne : Not (denotesSame zero one)
  lessEqualIsDecidable :
    ∀ leftValue rightValue : carrier,
      Decidable (lessEqual leftValue rightValue)
  lessEqualIsReflexive : ∀ value : carrier, lessEqual value value
  lessEqualIsTransitive :
    ∀ lowValue middleValue highValue : carrier,
      lessEqual lowValue middleValue → lessEqual middleValue highValue →
        lessEqual lowValue highValue
  lessEqualIsAntisymmetricUpToDenotesSame :
    ∀ leftValue rightValue : carrier,
      lessEqual leftValue rightValue → lessEqual rightValue leftValue →
        denotesSame leftValue rightValue
  lessEqualIsTotal :
    ∀ leftValue rightValue : carrier,
      lessEqual leftValue rightValue ∨ lessEqual rightValue leftValue
  lessEqualOfLessThan :
    ∀ leftValue rightValue : carrier,
      lessThan leftValue rightValue → lessEqual leftValue rightValue
  lessThanIsTrichotomous :
    ∀ leftValue rightValue : carrier,
      lessThan leftValue rightValue ∨ denotesSame leftValue rightValue ∨
        lessThan rightValue leftValue
  lessEqualRespectsDenotesSameLeft :
    ∀ leftValue newLeftValue rightValue : carrier,
      denotesSame leftValue newLeftValue → lessEqual leftValue rightValue →
        lessEqual newLeftValue rightValue
  lessEqualRespectsDenotesSameRight :
    ∀ leftValue rightValue newRightValue : carrier,
      denotesSame rightValue newRightValue → lessEqual leftValue rightValue →
        lessEqual leftValue newRightValue
  addRespectsLessEqual :
    ∀ lowValue highValue sharedAddend : carrier,
      lessEqual lowValue highValue →
        lessEqual (add lowValue sharedAddend) (add highValue sharedAddend)
  mulOfNonNegativesIsNonNegative :
    ∀ leftFactor rightFactor : carrier,
      lessEqual zero leftFactor → lessEqual zero rightFactor →
        lessEqual zero (mul leftFactor rightFactor)
  lessThanArchimedeanWitness :
    ∀ value : carrier, lessThan value (natEmbed (archimedeanWitness value))
  betweenPointLiesAbove :
    ∀ leftValue rightValue : carrier,
      lessThan leftValue rightValue →
        lessThan leftValue (betweenPoint leftValue rightValue)
  betweenPointLiesBelow :
    ∀ leftValue rightValue : carrier,
      lessThan leftValue rightValue →
        lessThan (betweenPoint leftValue rightValue) rightValue

open RationalPair in
/-- Nontriviality of ℚ — the cross-products `0·1` and `1·1` disagree as
constructor payloads, mirroring the ℤ certificate's one-liner. -/
theorem rationalZeroIsApartFromOne :
    Not (DenotesSameAs zeroRational oneRational) :=
  fun zeroDenotesOne => Nat.noConfusion (Int.ofNat.inj zeroDenotesOne)

open RationalPair in
/-- The ℚ certificate: `RationalPair` with its corpus is a decidable ordered
Heyting field up to the cross-multiplication setoid, with gcd-canonical normal
forms, a computable Archimedean bound, and the mediant as the computable
between-point.  Every field is a corpus theorem (eta-wrapped where the theorem
binds its subjects implicitly). -/
def rationalOrderedHeytingFieldWitness :
    DecidableOrderedHeytingFieldWitness RationalPair where
  denotesSame := DenotesSameAs
  lessEqual := LessEqualAs
  lessThan := LessThanAs
  zero := zeroRational
  one := oneRational
  add := addExact
  mul := mulExact
  neg := negExact
  inv := invExact
  natEmbed := fun naturalValue => rationalOfInt (Int.ofNat naturalValue)
  archimedeanWitness := archimedeanBound
  betweenPoint := mediant
  normalForm := normalize
  denotesSameIsReflexive := denotesSameAsRefl
  denotesSameIsSymmetric := fun _ _ areSame => denotesSameAsSymm areSame
  denotesSameIsTransitive := fun _ _ _ firstAgrees lastAgrees =>
    denotesSameAsTrans firstAgrees lastAgrees
  denotesSameIsDecidable := decideDenotesSameAs
  normalFormIsCanonical := denotesSameAsIffNormalizeEq
  addRespectsDenotesSame := fun _ _ _ _ leftAgrees rightAgrees =>
    addExactRespectsDenotesSameAs leftAgrees rightAgrees
  mulRespectsDenotesSame := fun _ _ _ _ leftAgrees rightAgrees =>
    mulExactRespectsDenotesSameAs leftAgrees rightAgrees
  negRespectsDenotesSame := fun _ _ areSame =>
    negExactRespectsDenotesSameAs areSame
  addIsCommutative := addExactComm
  addIsAssociative := addExactAssoc
  zeroIsRightAdditiveIdentity := addExactZeroRight
  negIsRightAdditiveInverse := addExactNegRight
  mulIsCommutative := mulExactComm
  mulIsAssociative := mulExactAssoc
  oneIsRightMultiplicativeIdentity := mulExactOneRight
  mulDistributesOverAdd := mulExactLeftDistrib
  mulInvCancelsOnApartness := fun _ isApart => mulExactInvRight isApart
  zeroIsApartFromOne := rationalZeroIsApartFromOne
  lessEqualIsDecidable := decideLessEqualAs
  lessEqualIsReflexive := lessEqualAsRefl
  lessEqualIsTransitive := fun _ _ _ isLowMiddle isMiddleHigh =>
    lessEqualAsTrans isLowMiddle isMiddleHigh
  lessEqualIsAntisymmetricUpToDenotesSame := fun _ _ isForward isBackward =>
    denotesSameAsOfLessEqualBoth isForward isBackward
  lessEqualIsTotal := lessEqualAsTotal
  lessEqualOfLessThan := fun _ _ isLessThan => lessEqualAsOfLessThan isLessThan
  lessThanIsTrichotomous := lessThanAsTrichotomy
  lessEqualRespectsDenotesSameLeft := fun _ _ _ areSame isLessEqual =>
    lessEqualAsCongrLeft areSame isLessEqual
  lessEqualRespectsDenotesSameRight := fun _ _ _ areSame isLessEqual =>
    lessEqualAsCongrRight areSame isLessEqual
  addRespectsLessEqual := fun _ _ sharedAddend isLessEqual =>
    addExactMonotoneLeft sharedAddend isLessEqual
  mulOfNonNegativesIsNonNegative := fun _ _ isLeftNonNegative isRightNonNegative =>
    mulExactIsNonNegative isLeftNonNegative isRightNonNegative
  lessThanArchimedeanWitness := lessThanArchimedeanBound
  betweenPointLiesAbove := fun _ _ isLessThan => mediantLiesAboveLeft isLessThan
  betweenPointLiesBelow := fun _ _ isLessThan => mediantLiesBelowRight isLessThan

end FX1Poly.ComputerAlgebra
