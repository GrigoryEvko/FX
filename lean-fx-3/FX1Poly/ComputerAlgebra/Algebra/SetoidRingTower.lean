import FX1Poly.ComputerAlgebra.Algebra.SetoidRingHom
import FX1Poly.ComputerAlgebra.Number.IntOrderedRingCertificate
import FX1Poly.ComputerAlgebra.Number.RationalOrderedFieldCertificate

/-! # SetoidRingTower — the ℕ → ℤ → ℚ → ℝ → ℂ diagram of setoid-rings (NUM-ALG-2)

This module turns the object-level number tower into a genuine categorical
DIAGRAM: the ring floors ℤ, ℚ, ℝ, ℂ as `CommutativeRingWitness` objects, and
the widening maps between them as `SetoidRingHom` arrows, each discharging all
five homomorphism obligations from the SHIPPED arithmetic.

* ℤ↪ℚ (`rationalOfInt`, `n ↦ n/1`) — `preservesMul`/`preservesZero`/
  `preservesOne` are `rfl`; `preservesAdd` is two `intMulOne` collapses;
  `respectsDenotesSame` is `congrArg` on the `Eq` source setoid.
* ℚ↪ℝ (`constantReal`) — `respectsDenotesSame` is the shipped
  `constantRealRespectsDenotesSame`; every preservation law holds by
  reflexivity, because `addReal`/`mulReal` of two CONSTANT sequences IS the
  constant sequence of the ℚ sum/product.
* ℝ↪ℂ (`complexOfReal`, `r ↦ r + 0i`) — real-part obligations reflexive, the
  imaginary-part Gauss collapse assembled from the shipped ℝ zero-laws.

The ℕ caveat (§6): ℕ has no additive inverse, so it is NOT an object of the
category of setoid-RINGS.  Honestly, ℕ↪ℤ is presented as a `SetoidSemiringHom`
into the underlying commutative SEMIRING of ℤ — the Grothendieck completion
step — never a faked ℕ negation.

`Init`-only, certificate-first, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-! ## ℤ as a `CommutativeRingWitness` (setoid = `Eq`) -/

/-- **The ℤ ring object.**  The integer commutative-ring laws are shipped as
`Int` corpus lemmas; the setoid is definitional equality, so its trio is
`rfl`/`Eq.symm`/`Eq.trans` and the operation congruences are `congrArg`
chains. -/
def intCommutativeRingWitness : CommutativeRingWitness Int where
  denotesSame := Eq
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  neg := Int.neg
  denotesSameIsReflexive := fun _ => rfl
  denotesSameIsSymmetric := fun _ _ areEqual => areEqual.symm
  denotesSameIsTransitive := fun _ _ _ firstEqual lastEqual =>
    firstEqual.trans lastEqual
  addRespectsDenotesSame :=
    fun _ newLeftValue rightValue _ leftEqual rightEqual =>
      (congrArg (· + rightValue) leftEqual).trans (congrArg (newLeftValue + ·) rightEqual)
  mulRespectsDenotesSame :=
    fun _ newLeftValue rightValue _ leftEqual rightEqual =>
      (congrArg (· * rightValue) leftEqual).trans (congrArg (newLeftValue * ·) rightEqual)
  negRespectsDenotesSame := fun _ _ areEqual => congrArg Int.neg areEqual
  addIsCommutative := intAddComm
  addIsAssociative := intAddAssoc
  zeroIsRightAdditiveIdentity := intAddZero
  negIsRightAdditiveInverse := intAddRightNeg
  mulIsCommutative := intMulComm
  mulIsAssociative := intMulAssoc
  oneIsRightMultiplicativeIdentity := intMulOne
  mulDistributesOverAdd := intLeftDistrib
  zeroIsApartFromOne := intZeroIsDistinctFromOne

/-! ## ℚ as a `CommutativeRingWitness` (forget order/decidability/inverse) -/

/-- **The ℚ ring object.**  The full ℚ field certificate forgets down to the
commutative-ring skeleton — every field is a shipped `RationalPair` corpus
lemma. -/
def rationalCommutativeRingWitness : CommutativeRingWitness RationalPair where
  denotesSame := DenotesSameAs
  zero := zeroRational
  one := oneRational
  add := addExact
  mul := mulExact
  neg := negExact
  denotesSameIsReflexive := denotesSameAsRefl
  denotesSameIsSymmetric := fun _ _ areSame => denotesSameAsSymm areSame
  denotesSameIsTransitive := fun _ _ _ firstAgrees lastAgrees =>
    denotesSameAsTrans firstAgrees lastAgrees
  addRespectsDenotesSame := fun _ _ _ _ leftAgrees rightAgrees =>
    addExactRespectsDenotesSameAs leftAgrees rightAgrees
  mulRespectsDenotesSame := fun _ _ _ _ leftAgrees rightAgrees =>
    mulExactRespectsDenotesSameAs leftAgrees rightAgrees
  negRespectsDenotesSame := fun _ _ areSame => negExactRespectsDenotesSameAs areSame
  addIsCommutative := addExactComm
  addIsAssociative := addExactAssoc
  zeroIsRightAdditiveIdentity := addExactZeroRight
  negIsRightAdditiveInverse := addExactNegRight
  mulIsCommutative := mulExactComm
  mulIsAssociative := mulExactAssoc
  oneIsRightMultiplicativeIdentity := mulExactOneRight
  mulDistributesOverAdd := mulExactLeftDistrib
  zeroIsApartFromOne := rationalZeroIsApartFromOne

/-! ## The commutative-semiring floor for ℕ

ℕ is a semiring, not a ring.  A minimal `CommutativeSemiringWitness` (the ring
witness minus negation) hosts ℕ as an object and receives every ring as a
forgetful image, so ℕ↪ℤ is an honest arrow without inventing a ℕ negation. -/

/-- **A setoid-relative commutative semiring** — a commutative ring witness
with the negation data dropped. -/
structure CommutativeSemiringWitness (carrier : Type) where
  denotesSame : carrier → carrier → Prop
  zero : carrier
  one : carrier
  add : carrier → carrier → carrier
  mul : carrier → carrier → carrier
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
  addIsCommutative :
    ∀ leftSummand rightSummand : carrier,
      denotesSame (add leftSummand rightSummand) (add rightSummand leftSummand)
  addIsAssociative :
    ∀ firstSummand secondSummand thirdSummand : carrier,
      denotesSame (add (add firstSummand secondSummand) thirdSummand)
        (add firstSummand (add secondSummand thirdSummand))
  zeroIsRightAdditiveIdentity :
    ∀ value : carrier, denotesSame (add value zero) value
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

/-- **Every commutative ring is a commutative semiring** — forget the
negation. -/
def commutativeSemiringWitnessOfRing {carrier : Type}
    (ring : CommutativeRingWitness carrier) : CommutativeSemiringWitness carrier where
  denotesSame := ring.denotesSame
  zero := ring.zero
  one := ring.one
  add := ring.add
  mul := ring.mul
  denotesSameIsReflexive := ring.denotesSameIsReflexive
  denotesSameIsSymmetric := ring.denotesSameIsSymmetric
  denotesSameIsTransitive := ring.denotesSameIsTransitive
  addRespectsDenotesSame := ring.addRespectsDenotesSame
  mulRespectsDenotesSame := ring.mulRespectsDenotesSame
  addIsCommutative := ring.addIsCommutative
  addIsAssociative := ring.addIsAssociative
  zeroIsRightAdditiveIdentity := ring.zeroIsRightAdditiveIdentity
  mulIsCommutative := ring.mulIsCommutative
  mulIsAssociative := ring.mulIsAssociative
  oneIsRightMultiplicativeIdentity := ring.oneIsRightMultiplicativeIdentity
  mulDistributesOverAdd := ring.mulDistributesOverAdd
  zeroIsApartFromOne := ring.zeroIsApartFromOne

/-- **The ℕ semiring object** — the `Nat` core lemmas, `Eq` setoid.  Note:
`mulIsAssociative` uses the SHIPPED `natMulAssoc` (§ IntMulAssociativity), which
is propext-clean; the stdlib `Nat.mul_assoc` leaks `propext`. -/
def natCommutativeSemiringWitness : CommutativeSemiringWitness Nat where
  denotesSame := Eq
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  denotesSameIsReflexive := fun _ => rfl
  denotesSameIsSymmetric := fun _ _ areEqual => areEqual.symm
  denotesSameIsTransitive := fun _ _ _ firstEqual lastEqual =>
    firstEqual.trans lastEqual
  addRespectsDenotesSame :=
    fun _ newLeftValue rightValue _ leftEqual rightEqual =>
      (congrArg (· + rightValue) leftEqual).trans (congrArg (newLeftValue + ·) rightEqual)
  mulRespectsDenotesSame :=
    fun _ newLeftValue rightValue _ leftEqual rightEqual =>
      (congrArg (· * rightValue) leftEqual).trans (congrArg (newLeftValue * ·) rightEqual)
  addIsCommutative := Nat.add_comm
  addIsAssociative := Nat.add_assoc
  zeroIsRightAdditiveIdentity := Nat.add_zero
  mulIsCommutative := Nat.mul_comm
  mulIsAssociative := natMulAssoc
  oneIsRightMultiplicativeIdentity := Nat.mul_one
  mulDistributesOverAdd := Nat.mul_add
  zeroIsApartFromOne := fun zeroEqualsOne => Nat.noConfusion zeroEqualsOne

/-- **A setoid-relative commutative-semiring homomorphism** — the same six
obligations as `SetoidRingHom`, over semiring witnesses. -/
structure SetoidSemiringHom {sourceCarrier targetCarrier : Type}
    (source : CommutativeSemiringWitness sourceCarrier)
    (target : CommutativeSemiringWitness targetCarrier) where
  map : sourceCarrier → targetCarrier
  respectsDenotesSame :
    ∀ leftValue rightValue : sourceCarrier,
      source.denotesSame leftValue rightValue →
        target.denotesSame (map leftValue) (map rightValue)
  preservesAdd :
    ∀ leftValue rightValue : sourceCarrier,
      target.denotesSame (map (source.add leftValue rightValue))
        (target.add (map leftValue) (map rightValue))
  preservesMul :
    ∀ leftValue rightValue : sourceCarrier,
      target.denotesSame (map (source.mul leftValue rightValue))
        (target.mul (map leftValue) (map rightValue))
  preservesZero : target.denotesSame (map source.zero) target.zero
  preservesOne : target.denotesSame (map source.one) target.one

/-! ## The four widenings -/

/-- **ℕ ↪ ℤ** as a semiring homomorphism — `Int.ofNat`.  `Int.add`/`Int.mul`
recurse so that `ofNat (m + n) = ofNat m + ofNat n` and the product analogue
hold by `rfl`; the constants map on the nose. -/
def embedNatToInt :
    SetoidSemiringHom natCommutativeSemiringWitness
      (commutativeSemiringWitnessOfRing intCommutativeRingWitness) where
  map := Int.ofNat
  respectsDenotesSame := fun _ _ areEqual => congrArg Int.ofNat areEqual
  preservesAdd := fun _ _ => rfl
  preservesMul := fun _ _ => rfl
  preservesZero := rfl
  preservesOne := rfl

/-- **ℤ ↪ ℚ** as a ring homomorphism — `rationalOfInt` (`n ↦ n/1`). -/
def embedIntToRat :
    SetoidRingHom intCommutativeRingWitness rationalCommutativeRingWitness where
  map := rationalOfInt
  respectsDenotesSame := fun _ rightValue areEqual =>
    congrArg (fun scalar => scalar * denominatorInt (rationalOfInt rightValue)) areEqual
  preservesAdd := fun leftValue rightValue =>
    (intMulOne (leftValue + rightValue)).trans
      ((congrArg (· + rightValue) (intMulOne leftValue).symm).trans
        ((congrArg (leftValue * 1 + ·) (intMulOne rightValue).symm).trans
          (intMulOne (leftValue * 1 + rightValue * 1)).symm))
  preservesMul := fun leftValue rightValue =>
    denotesSameAsRefl (rationalOfInt (leftValue * rightValue))
  preservesZero := denotesSameAsRefl zeroRational
  preservesOne := denotesSameAsRefl oneRational

/-- **ℚ ↪ ℝ** as a ring homomorphism — the constant Cauchy embedding
`constantReal`.  Additivity and multiplicativity are reflexivity: the sum /
product of two constant sequences IS the constant sequence of the ℚ sum /
product. -/
def embedRatToReal :
    SetoidRingHom rationalCommutativeRingWitness regularRealCommutativeRingWitness where
  map := constantReal
  respectsDenotesSame := fun _ _ areSame => constantRealRespectsDenotesSame areSame
  preservesAdd := fun leftValue rightValue =>
    denotesSameRealRefl (constantReal (addExact leftValue rightValue))
  preservesMul := fun leftValue rightValue =>
    denotesSameRealRefl (constantReal (mulExact leftValue rightValue))
  preservesZero := denotesSameRealRefl (constantReal zeroRational)
  preservesOne := denotesSameRealRefl (constantReal oneRational)

/-- **The ℝ ↪ ℂ embedding** `r ↦ r + 0i`. -/
def complexOfReal (value : RegularReal) : ComplexReal :=
  { realPart := value, imaginaryPart := constantReal zeroRational }

/-- **ℝ ↪ ℂ** as a ring homomorphism.  Real-part obligations are reflexive; the
imaginary-part Gauss collapse `a·0 + 0·b ~ 0` and the real-part `a·b − 0·0 ~
a·b` are assembled from the shipped ℝ zero-laws. -/
def embedRealToComplex :
    SetoidRingHom regularRealCommutativeRingWitness complexCommutativeRingWitness where
  map := complexOfReal
  respectsDenotesSame := fun _ _ areSame =>
    ⟨areSame, denotesSameRealRefl (constantReal zeroRational)⟩
  preservesAdd := fun leftValue rightValue =>
    ⟨denotesSameRealRefl (addReal leftValue rightValue),
      denotesSameRealSymm (addRealZeroRight (constantReal zeroRational))⟩
  preservesMul := fun leftValue rightValue =>
    ⟨denotesSameRealSymm
        (denotesSameRealTrans
          (subRealRespectsDenotesSame
            (denotesSameRealRefl (mulReal leftValue rightValue))
            (mulRealZeroRight (constantReal zeroRational)))
          (subRealZeroRightDenotesSame (mulReal leftValue rightValue))),
      denotesSameRealSymm
        (denotesSameRealTrans
          (addRealRespectsDenotesSame (mulRealZeroRight leftValue)
            (mulRealZeroLeft rightValue))
          (addRealZeroRight (constantReal zeroRational)))⟩
  preservesZero :=
    ⟨denotesSameRealRefl (constantReal zeroRational),
      denotesSameRealRefl (constantReal zeroRational)⟩
  preservesOne :=
    ⟨denotesSameRealRefl (constantReal oneRational),
      denotesSameRealRefl (constantReal zeroRational)⟩

/-! ## Composite widenings — the diagram composes

The index poset `ℤ < ℚ < ℝ < ℂ` is thin, so functoriality is automatic: every
composite widening is a `composeRingHom` chain, no commuting-square debt. -/

/-- ℤ ↪ ℝ, the composite through ℚ. -/
def embedIntToReal :
    SetoidRingHom intCommutativeRingWitness regularRealCommutativeRingWitness :=
  composeRingHom embedRatToReal embedIntToRat

/-- ℚ ↪ ℂ, the composite through ℝ. -/
def embedRatToComplex :
    SetoidRingHom rationalCommutativeRingWitness complexCommutativeRingWitness :=
  composeRingHom embedRealToComplex embedRatToReal

/-- ℤ ↪ ℂ, the composite through ℝ. -/
def embedIntToComplex :
    SetoidRingHom intCommutativeRingWitness complexCommutativeRingWitness :=
  composeRingHom embedRealToComplex embedIntToReal

end FX1Poly.ComputerAlgebra
