import FX1Poly.ComputerAlgebra.Number.NatEuclideanDivision
import FX1Poly.ComputerAlgebra.Number.IntMulAssociativity

/-! # Modular reduction (`mod 2^n`) over the structural divider

Init's remainder value (`Nat.mod`) is computed by well-founded recursion, and its
characterisation lemmas (`Nat.mod_eq_of_lt`, `Nat.mod_self`, `Nat.add_mod`, `Nat.mul_mod`)
leak `propext`. This module re-derives the modular-reduction surface on top of the
fuel-structural counting divider `natDivModCounting` (`NatEuclideanDivision`), with
`natRemainder d m := (natDivModCounting d m).snd`; from its reconstruction, bound, and
quotient-uniqueness certificates:

* `natRemainderUnique` — the Euclidean remainder is pinned by any in-bound decomposition;
  the base identities and homomorphism steps follow from it.
* `natRemainderOfLt`, `natRemainderSelf` — the two base identities.
* `natRemainderAddMultiple` — invariance under adding a multiple of the modulus.
* `natRemainderAddPush`, `natRemainderMulPush` — the modular add/mul homomorphism steps
  (`natRemainder (natRemainder a + b) = natRemainder (a + b)`) underlying the `mod 2^n`
  ring laws.
* `natAddSubCancelLeft`, `natAddSubOfLe` — additive-inverse plumbing for the `2^n - a`
  complement (Init's `Nat.add_sub_cancel*` leak `propext`).

Init-only, certificate-first, structural, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The clean remainder and quotient -/

/-- The Euclidean remainder from the structural counting divider. -/
def natRemainder (dividend divisor : Nat) : Nat :=
  (natDivModCounting dividend divisor).snd

/-- The Euclidean quotient from the structural counting divider. -/
def natQuotient (dividend divisor : Nat) : Nat :=
  (natDivModCounting dividend divisor).fst

/-- Reconstruction lifted to the named remainder/quotient. -/
theorem natRemainderReconstructs (dividend divisor : Nat) :
    dividend = divisor * natQuotient dividend divisor + natRemainder dividend divisor :=
  natDivModCountingReconstructs dividend divisor

/-- The remainder stays below a positive modulus. -/
theorem natRemainderIsBounded {dividend divisor : Nat} (isPositive : 0 < divisor) :
    natRemainder dividend divisor < divisor :=
  natDivModCountingRemainderIsBounded dividend divisor isPositive

/-! ## The uniqueness crux -/

/-- Remainder uniqueness: any in-bound decomposition pins the Euclidean remainder. Init's
`Nat.mod_unique`-flavoured facts leak `propext`; this uses the quotient-uniqueness
certificate plus additive left-cancellation. -/
theorem natRemainderUnique {dividend divisor quotient remainder : Nat}
    (isBounded : remainder < divisor)
    (decomposition : dividend = divisor * quotient + remainder) :
    natRemainder dividend divisor = remainder :=
  let positiveDivisor : 0 < divisor := Nat.lt_of_le_of_lt (Nat.zero_le remainder) isBounded
  let remainderBound : natRemainder dividend divisor < divisor :=
    natRemainderIsBounded positiveDivisor
  let decompositionsAgree :
      divisor * natQuotient dividend divisor + natRemainder dividend divisor =
        divisor * quotient + remainder :=
    (natRemainderReconstructs dividend divisor).symm.trans decomposition
  let quotientsAgree : natQuotient dividend divisor = quotient :=
    natEuclideanQuotientUnique remainderBound isBounded decompositionsAgree
  let sharedAddendForm :
      divisor * quotient + natRemainder dividend divisor =
        divisor * quotient + remainder :=
    (congrArg (fun scaledQuotient => divisor * scaledQuotient + natRemainder dividend divisor)
      quotientsAgree).symm.trans decompositionsAgree
  natAddLeftCancel sharedAddendForm

/-! ## Base identities -/

/-- A value already below the modulus is its own remainder. -/
theorem natRemainderOfLt {value divisor : Nat} (isBounded : value < divisor) :
    natRemainder value divisor = value :=
  natRemainderUnique isBounded
    ((congrArg (· + value) (Nat.mul_zero divisor)).trans (Nat.zero_add value)).symm

/-- The modulus reduces to zero. -/
theorem natRemainderSelf {divisor : Nat} (isPositive : 0 < divisor) :
    natRemainder divisor divisor = 0 :=
  natRemainderUnique isPositive
    ((Nat.add_zero divisor).symm.trans (congrArg (· + 0) (Nat.mul_one divisor).symm))

/-! ## The homomorphism steps -/

/-- Adding a multiple of the modulus leaves the remainder unchanged. -/
theorem natRemainderAddMultiple (base divisor multiple : Nat) (isPositive : 0 < divisor) :
    natRemainder (base + divisor * multiple) divisor = natRemainder base divisor :=
  let quotient := natQuotient base divisor
  let remainder := natRemainder base divisor
  let reconstruction : base = divisor * quotient + remainder :=
    natRemainderReconstructs base divisor
  let bound : remainder < divisor := natRemainderIsBounded isPositive
  natRemainderUnique bound
    ((congrArg (· + divisor * multiple) reconstruction).trans
      ((Nat.add_right_comm (divisor * quotient) remainder (divisor * multiple)).trans
        (congrArg (· + remainder) (Nat.left_distrib divisor quotient multiple).symm)))

/-- Modular add step: reducing the left summand before adding is invisible to the outer
reduction. -/
theorem natRemainderAddPush (leftValue rightValue divisor : Nat) (isPositive : 0 < divisor) :
    natRemainder (natRemainder leftValue divisor + rightValue) divisor =
      natRemainder (leftValue + rightValue) divisor :=
  let quotient := natQuotient leftValue divisor
  let remainder := natRemainder leftValue divisor
  let reconstruction : leftValue = divisor * quotient + remainder :=
    natRemainderReconstructs leftValue divisor
  let rearrange :
      leftValue + rightValue = (remainder + rightValue) + divisor * quotient :=
    (congrArg (· + rightValue) reconstruction).trans
      ((Nat.add_assoc (divisor * quotient) remainder rightValue).trans
        (Nat.add_comm (divisor * quotient) (remainder + rightValue)))
  (natRemainderAddMultiple (remainder + rightValue) divisor quotient isPositive).symm.trans
    (congrArg (fun summed => natRemainder summed divisor) rearrange.symm)

/-- Modular mul step: reducing the left factor before multiplying is invisible to the
outer reduction. -/
theorem natRemainderMulPush (leftValue rightValue divisor : Nat) (isPositive : 0 < divisor) :
    natRemainder (natRemainder leftValue divisor * rightValue) divisor =
      natRemainder (leftValue * rightValue) divisor :=
  let quotient := natQuotient leftValue divisor
  let remainder := natRemainder leftValue divisor
  let reconstruction : leftValue = divisor * quotient + remainder :=
    natRemainderReconstructs leftValue divisor
  let rearrange :
      leftValue * rightValue = remainder * rightValue + divisor * (quotient * rightValue) :=
    (congrArg (· * rightValue) reconstruction).trans
      ((natRightDistrib (divisor * quotient) remainder rightValue).trans
        ((congrArg (· + remainder * rightValue) (natMulAssoc divisor quotient rightValue)).trans
          (Nat.add_comm (divisor * (quotient * rightValue)) (remainder * rightValue))))
  (natRemainderAddMultiple (remainder * rightValue) divisor (quotient * rightValue)
      isPositive).symm.trans
    (congrArg (fun scaled => natRemainder scaled divisor) rearrange.symm)

/-! ## Additive-inverse plumbing -/

/-- `(value + addend) - value = addend` — the propext-clean replacement for
Init's `Nat.add_sub_cancel_left`. -/
theorem natAddSubCancelLeft : ∀ value addend : Nat, (value + addend) - value = addend
  | 0, addend => Nat.zero_add addend
  | value + 1, addend =>
      (congrArg (· - (value + 1)) (Nat.succ_add value addend)).trans
        ((Nat.succ_sub_succ (value + addend) value).trans (natAddSubCancelLeft value addend))

/-- `smaller + (larger - smaller) = larger` when `smaller ≤ larger`. -/
theorem natAddSubOfLe {smaller larger : Nat} (isLe : smaller ≤ larger) :
    smaller + (larger - smaller) = larger :=
  match Nat.le.dest isLe with
  | ⟨witness, equation⟩ =>
      let subEquation : larger - smaller = witness :=
        (congrArg (· - smaller) equation).symm.trans (natAddSubCancelLeft smaller witness)
      (congrArg (smaller + ·) subEquation).trans equation

end FX1Poly.ComputerAlgebra
