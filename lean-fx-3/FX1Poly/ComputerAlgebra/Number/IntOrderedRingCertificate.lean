import FX1Poly.ComputerAlgebra.Number.IntArithmeticCore
import FX1Poly.ComputerAlgebra.Number.IntAddAssociativity
import FX1Poly.ComputerAlgebra.Number.IntMulAssociativity
import FX1Poly.ComputerAlgebra.Number.IntDistributivity
import FX1Poly.ComputerAlgebra.Number.IntSubNatNat
import FX1Poly.ComputerAlgebra.Number.IntOrderCore
import FX1Poly.ComputerAlgebra.Number.IntOrderAlgebra

/-! # The ordered-commutative-ring certificate (NUM-Z-PACK)

The hand-rolled `Int` corpus — built lemma by lemma for the floating-point arc —
packaged as ONE value: a linearly ordered commutative ring witness.  The structure
is the ℤ rung's certificate in the zero-axiom number tower and the reuse target for
the later rungs (ℚ instantiates it on gcd-normal forms, where the setoid collapses
to `Eq`).

Nothing here is new mathematics: every field is a shipped theorem, so the witness
doubles as a completeness checklist for the corpus.  The one genuinely new fact is
nontriviality (`0 ≠ 1`), a constructor-disagreement one-liner. -/

namespace FX1Poly.ComputerAlgebra

/-- **A linearly ordered commutative ring, as data**: carrier, operations, order,
and every law as a proof field.  Stated over `Eq` — rungs whose sameness is a
proper setoid (ℤ[1/β], ℝ) get separate congruence packages; this structure serves
the rungs with canonical normal forms. -/
structure OrderedCommutativeRingWitness (carrier : Type) where
  zero : carrier
  one : carrier
  add : carrier → carrier → carrier
  mul : carrier → carrier → carrier
  neg : carrier → carrier
  lessEqual : carrier → carrier → Prop
  addIsCommutative :
    ∀ leftSummand rightSummand : carrier,
      add leftSummand rightSummand = add rightSummand leftSummand
  addIsAssociative :
    ∀ firstSummand secondSummand thirdSummand : carrier,
      add (add firstSummand secondSummand) thirdSummand =
        add firstSummand (add secondSummand thirdSummand)
  zeroIsRightAdditiveIdentity : ∀ value : carrier, add value zero = value
  negIsLeftAdditiveInverse : ∀ value : carrier, add (neg value) value = zero
  mulIsCommutative :
    ∀ leftFactor rightFactor : carrier,
      mul leftFactor rightFactor = mul rightFactor leftFactor
  mulIsAssociative :
    ∀ leftFactor middleFactor rightFactor : carrier,
      mul (mul leftFactor middleFactor) rightFactor =
        mul leftFactor (mul middleFactor rightFactor)
  oneIsRightMultiplicativeIdentity : ∀ value : carrier, mul value one = value
  mulDistributesOverAdd :
    ∀ factor leftSummand rightSummand : carrier,
      mul factor (add leftSummand rightSummand) =
        add (mul factor leftSummand) (mul factor rightSummand)
  lessEqualIsReflexive : ∀ value : carrier, lessEqual value value
  lessEqualIsTransitive :
    ∀ lowValue middleValue highValue : carrier,
      lessEqual lowValue middleValue → lessEqual middleValue highValue →
        lessEqual lowValue highValue
  lessEqualIsAntisymmetric :
    ∀ leftValue rightValue : carrier,
      lessEqual leftValue rightValue → lessEqual rightValue leftValue →
        leftValue = rightValue
  lessEqualIsTotal :
    ∀ leftValue rightValue : carrier,
      lessEqual leftValue rightValue ∨ lessEqual rightValue leftValue
  addRespectsLessEqual :
    ∀ lowValue highValue sharedAddend : carrier,
      lessEqual lowValue highValue →
        lessEqual (add lowValue sharedAddend) (add highValue sharedAddend)
  mulOfNonNegativesIsNonNegative :
    ∀ leftFactor rightFactor : carrier,
      lessEqual zero leftFactor → lessEqual zero rightFactor →
        lessEqual zero (mul leftFactor rightFactor)
  zeroIsDistinctFromOne : zero ≠ one

/-- Nontriviality of `Int` — the two `ofNat` payloads disagree as constructors. -/
theorem intZeroIsDistinctFromOne : (0 : Int) ≠ 1 :=
  fun zeroEqualsOne => Nat.noConfusion (Int.ofNat.inj zeroEqualsOne)

/-- **The ℤ certificate**: `Int` with its shipped hand-rolled corpus is a linearly
ordered commutative ring.  Every field IS a corpus theorem (eta-wrapped where the
theorem binds its subjects implicitly). -/
def intOrderedCommutativeRingWitness : OrderedCommutativeRingWitness Int where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  neg := Int.neg
  lessEqual := (· ≤ ·)
  addIsCommutative := intAddComm
  addIsAssociative := intAddAssoc
  zeroIsRightAdditiveIdentity := intAddZero
  negIsLeftAdditiveInverse := intAddLeftNeg
  mulIsCommutative := intMulComm
  mulIsAssociative := intMulAssoc
  oneIsRightMultiplicativeIdentity := intMulOne
  mulDistributesOverAdd := intLeftDistrib
  lessEqualIsReflexive := intLessEqualRefl
  lessEqualIsTransitive := fun _ _ _ isLowMiddle isMiddleHigh =>
    intLessEqualTrans isLowMiddle isMiddleHigh
  lessEqualIsAntisymmetric := fun _ _ isForward isBackward =>
    intLessEqualAntisymm isForward isBackward
  lessEqualIsTotal := intLessEqualTotal
  addRespectsLessEqual := fun _ _ sharedAddend isLessEqual =>
    intAddLeAddRight isLessEqual sharedAddend
  mulOfNonNegativesIsNonNegative := fun _ _ isLeftNonNegative isRightNonNegative =>
    intMulNonNeg isLeftNonNegative isRightNonNegative
  zeroIsDistinctFromOne := intZeroIsDistinctFromOne

end FX1Poly.ComputerAlgebra
