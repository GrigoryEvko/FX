import FX1Poly.ComputerAlgebra.FixedWidth.Views
import FX1Poly.ComputerAlgebra.Bits.BitVecRing

/-! # FixedWidth/ViewsRing — the `uN` / `iN` views as commutative-ring witnesses

`FixedWidth/Views` builds the two nominal facades `UIntN` / `SIntN` over the one
`BitVec` carrier and notes (its own docstring) that "a single
`bitVecCommutativeRingWitness` backs both".  This file DELIVERS that: it lifts
the shipped `bitVecCommutativeRingWitness` corpus through the one-field wrappers
into two `CommutativeRingWitness` objects, giving the `iN` / `uN` views the same
categorical-witness-object status every number-tower rung (ℤ, ℚ, ℝ, ℂ) already
has.

The lift is pure packaging: the setoid is genuine `Eq` (the wrapper keeps
equality structural), so the setoid trio is `rfl` / `.symm` / `.trans`, the three
operation congruences are `congrArg` chains, and each of the eight ring laws
transports the corresponding `BitVec` law through the wrapper injectivity lemma
(`sIntNEqOfBitsEq` / `uIntNEqOfBitsEq`) — the `.bits` of `⟨x⟩` is defeq `x`, so
the shipped hypothesis lands exactly on the goal.

Like `BitVecRing`, both witnesses are indexed by `width + 1` (POSITIVE width):
`BitVec 0` is the trivial ring `0 = 1`, satisfying every law EXCEPT
nontriviality, so the `+1` is forced there alone (via `Nat.one_lt_two_pow`).

`SIntN` already ships `SIntN.neg`; `UIntN` does not, so its two's-complement
negation `UIntN.neg` is supplied here as a one-line prerequisite (identical
delegation to `bitVecNeg`, wrap-by-default).

`Init`-only, certificate-first, genuine-`Eq`, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Prerequisite: unsigned two's-complement negation

`Views` gives `UIntN` its `add` / `mul` / `sub` but no `neg`; the ring witness
needs one.  Two's-complement negation is bit-identical across the u/i split, so
this delegates to the same `bitVecNeg` `SIntN.neg` uses. -/

/-- Unsigned negation (two's-complement complement, wraps `mod 2^n`). -/
def UIntN.neg {width : Nat} (value : UIntN width) : UIntN width :=
  ⟨bitVecNeg value.bits⟩

/-! ## The eight signed ring laws (generic over the width)

Each law is the corresponding `BitVecRing` law transported through
`sIntNEqOfBitsEq`; the wrapped op's `.bits` is defeq to the bare `BitVec` op, so
the shipped equality is exactly the required bits-equality. -/

/-- Signed additive commutativity. -/
theorem sIntNAddComm {width : Nat} (left right : SIntN width) :
    SIntN.add left right = SIntN.add right left :=
  sIntNEqOfBitsEq (bitVecAddComm left.bits right.bits)

/-- Signed multiplicative commutativity. -/
theorem sIntNMulComm {width : Nat} (left right : SIntN width) :
    SIntN.mul left right = SIntN.mul right left :=
  sIntNEqOfBitsEq (bitVecMulComm left.bits right.bits)

/-- Signed additive associativity. -/
theorem sIntNAddAssoc {width : Nat} (left middle right : SIntN width) :
    SIntN.add (SIntN.add left middle) right = SIntN.add left (SIntN.add middle right) :=
  sIntNEqOfBitsEq (bitVecAddAssoc left.bits middle.bits right.bits)

/-- Signed multiplicative associativity. -/
theorem sIntNMulAssoc {width : Nat} (left middle right : SIntN width) :
    SIntN.mul (SIntN.mul left middle) right = SIntN.mul left (SIntN.mul middle right) :=
  sIntNEqOfBitsEq (bitVecMulAssoc left.bits middle.bits right.bits)

/-- Signed right additive identity. -/
theorem sIntNAddZeroRight {width : Nat} (value : SIntN width) :
    SIntN.add value SIntN.zero = value :=
  sIntNEqOfBitsEq (bitVecAddZeroRight value.bits)

/-- Signed right additive inverse. -/
theorem sIntNAddNegRight {width : Nat} (value : SIntN width) :
    SIntN.add value (SIntN.neg value) = SIntN.zero :=
  sIntNEqOfBitsEq (bitVecAddNegRight value.bits)

/-- Signed left distributivity. -/
theorem sIntNMulDistribLeft {width : Nat} (factor left right : SIntN width) :
    SIntN.mul factor (SIntN.add left right) =
      SIntN.add (SIntN.mul factor left) (SIntN.mul factor right) :=
  sIntNEqOfBitsEq (bitVecMulDistribLeft factor.bits left.bits right.bits)

/-- Signed right multiplicative identity (needs `1 < 2^width` so the unit is
nonzero). -/
theorem sIntNMulOneRight {width : Nat} (isWide : 1 < 2 ^ width) (value : SIntN width) :
    SIntN.mul value SIntN.one = value :=
  sIntNEqOfBitsEq (bitVecMulOneRight isWide value.bits)

/-- Signed nontriviality: `0` and `1` are distinct once the modulus exceeds `1`. -/
theorem sIntNZeroApartOne {width : Nat} (isWide : 1 < 2 ^ width) :
    ¬ (SIntN.zero (width := width) = SIntN.one) :=
  fun sameConstant => bitVecZeroApartOne isWide (congrArg SIntN.bits sameConstant)

/-! ## The eight unsigned ring laws (generic over the width)

Identical transport through `uIntNEqOfBitsEq`; the u/i split is invisible to the
ring structure (two's-complement arithmetic is bit-identical to unsigned
`mod 2^n`), so both families lift the SAME `BitVec` corpus. -/

/-- Unsigned additive commutativity. -/
theorem uIntNAddComm {width : Nat} (left right : UIntN width) :
    UIntN.add left right = UIntN.add right left :=
  uIntNEqOfBitsEq (bitVecAddComm left.bits right.bits)

/-- Unsigned multiplicative commutativity. -/
theorem uIntNMulComm {width : Nat} (left right : UIntN width) :
    UIntN.mul left right = UIntN.mul right left :=
  uIntNEqOfBitsEq (bitVecMulComm left.bits right.bits)

/-- Unsigned additive associativity. -/
theorem uIntNAddAssoc {width : Nat} (left middle right : UIntN width) :
    UIntN.add (UIntN.add left middle) right = UIntN.add left (UIntN.add middle right) :=
  uIntNEqOfBitsEq (bitVecAddAssoc left.bits middle.bits right.bits)

/-- Unsigned multiplicative associativity. -/
theorem uIntNMulAssoc {width : Nat} (left middle right : UIntN width) :
    UIntN.mul (UIntN.mul left middle) right = UIntN.mul left (UIntN.mul middle right) :=
  uIntNEqOfBitsEq (bitVecMulAssoc left.bits middle.bits right.bits)

/-- Unsigned right additive identity. -/
theorem uIntNAddZeroRight {width : Nat} (value : UIntN width) :
    UIntN.add value UIntN.zero = value :=
  uIntNEqOfBitsEq (bitVecAddZeroRight value.bits)

/-- Unsigned right additive inverse. -/
theorem uIntNAddNegRight {width : Nat} (value : UIntN width) :
    UIntN.add value (UIntN.neg value) = UIntN.zero :=
  uIntNEqOfBitsEq (bitVecAddNegRight value.bits)

/-- Unsigned left distributivity. -/
theorem uIntNMulDistribLeft {width : Nat} (factor left right : UIntN width) :
    UIntN.mul factor (UIntN.add left right) =
      UIntN.add (UIntN.mul factor left) (UIntN.mul factor right) :=
  uIntNEqOfBitsEq (bitVecMulDistribLeft factor.bits left.bits right.bits)

/-- Unsigned right multiplicative identity (needs `1 < 2^width` so the unit is
nonzero). -/
theorem uIntNMulOneRight {width : Nat} (isWide : 1 < 2 ^ width) (value : UIntN width) :
    UIntN.mul value UIntN.one = value :=
  uIntNEqOfBitsEq (bitVecMulOneRight isWide value.bits)

/-- Unsigned nontriviality: `0` and `1` are distinct once the modulus exceeds `1`. -/
theorem uIntNZeroApartOne {width : Nat} (isWide : 1 < 2 ^ width) :
    ¬ (UIntN.zero (width := width) = UIntN.one) :=
  fun sameConstant => bitVecZeroApartOne isWide (congrArg UIntN.bits sameConstant)

/-! ## The commutative-ring witnesses -/

/-- **`i(width+1)` as a commutative ring** — the signed fixed-width view packaged
as the shipped `CommutativeRingWitness`, genuine `Eq` setoid, every law lifted
from `bitVecCommutativeRingWitness`.  The `+1` guarantees `1 < 2^(width+1)`,
hence nontriviality. -/
def sIntNCommutativeRingWitness (width : Nat) :
    CommutativeRingWitness (SIntN (width + 1)) :=
  let isWide : 1 < 2 ^ (width + 1) :=
    Nat.one_lt_two_pow (fun succEqZero => Nat.noConfusion succEqZero)
  { denotesSame := Eq
    zero := SIntN.zero
    one := SIntN.one
    add := SIntN.add
    mul := SIntN.mul
    neg := SIntN.neg
    denotesSameIsReflexive := fun _ => rfl
    denotesSameIsSymmetric := fun _ _ areEqual => areEqual.symm
    denotesSameIsTransitive := fun _ _ _ firstEqual lastEqual => firstEqual.trans lastEqual
    addRespectsDenotesSame := fun leftValue newLeftValue rightValue newRightValue
        leftEqual rightEqual =>
      (congrArg (fun chosen => SIntN.add chosen rightValue) leftEqual).trans
        (congrArg (SIntN.add newLeftValue) rightEqual)
    mulRespectsDenotesSame := fun leftValue newLeftValue rightValue newRightValue
        leftEqual rightEqual =>
      (congrArg (fun chosen => SIntN.mul chosen rightValue) leftEqual).trans
        (congrArg (SIntN.mul newLeftValue) rightEqual)
    negRespectsDenotesSame := fun _ _ areEqual => congrArg SIntN.neg areEqual
    addIsCommutative := sIntNAddComm
    addIsAssociative := sIntNAddAssoc
    zeroIsRightAdditiveIdentity := sIntNAddZeroRight
    negIsRightAdditiveInverse := sIntNAddNegRight
    mulIsCommutative := sIntNMulComm
    mulIsAssociative := sIntNMulAssoc
    oneIsRightMultiplicativeIdentity := sIntNMulOneRight isWide
    mulDistributesOverAdd := sIntNMulDistribLeft
    zeroIsApartFromOne := sIntNZeroApartOne isWide }

/-- **`u(width+1)` as a commutative ring** — the unsigned fixed-width view
packaged as the shipped `CommutativeRingWitness`, sharing the SAME `BitVec` ring
corpus as its signed twin (two's-complement is bit-identical to unsigned
`mod 2^n`).  The `+1` guarantees nontriviality. -/
def uIntNCommutativeRingWitness (width : Nat) :
    CommutativeRingWitness (UIntN (width + 1)) :=
  let isWide : 1 < 2 ^ (width + 1) :=
    Nat.one_lt_two_pow (fun succEqZero => Nat.noConfusion succEqZero)
  { denotesSame := Eq
    zero := UIntN.zero
    one := UIntN.one
    add := UIntN.add
    mul := UIntN.mul
    neg := UIntN.neg
    denotesSameIsReflexive := fun _ => rfl
    denotesSameIsSymmetric := fun _ _ areEqual => areEqual.symm
    denotesSameIsTransitive := fun _ _ _ firstEqual lastEqual => firstEqual.trans lastEqual
    addRespectsDenotesSame := fun leftValue newLeftValue rightValue newRightValue
        leftEqual rightEqual =>
      (congrArg (fun chosen => UIntN.add chosen rightValue) leftEqual).trans
        (congrArg (UIntN.add newLeftValue) rightEqual)
    mulRespectsDenotesSame := fun leftValue newLeftValue rightValue newRightValue
        leftEqual rightEqual =>
      (congrArg (fun chosen => UIntN.mul chosen rightValue) leftEqual).trans
        (congrArg (UIntN.mul newLeftValue) rightEqual)
    negRespectsDenotesSame := fun _ _ areEqual => congrArg UIntN.neg areEqual
    addIsCommutative := uIntNAddComm
    addIsAssociative := uIntNAddAssoc
    zeroIsRightAdditiveIdentity := uIntNAddZeroRight
    negIsRightAdditiveInverse := uIntNAddNegRight
    mulIsCommutative := uIntNMulComm
    mulIsAssociative := uIntNMulAssoc
    oneIsRightMultiplicativeIdentity := uIntNMulOneRight isWide
    mulDistributesOverAdd := uIntNMulDistribLeft
    zeroIsApartFromOne := uIntNZeroApartOne isWide }

end FX1Poly.ComputerAlgebra
