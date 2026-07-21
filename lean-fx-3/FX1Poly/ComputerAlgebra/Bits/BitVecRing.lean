import FX1Poly.ComputerAlgebra.Bits.BitVec
import FX1Poly.ComputerAlgebra.Number.ComplexReal

/-! # BitVecRing — `BitVec (width+1)` as the commutative ring `Z / 2^(width+1) Z`

Fixed-width machine integers form a commutative ring under the modular arithmetic of
`Bits/BitVec`, packaged as the `CommutativeRingWitness` (`ComplexReal`) shared with
the number tower's ℤ, ℚ, ℝ, ℂ.

The setoid is genuine `Eq`, not a coarsening: the carrier is core `BitVec`,
`toNat`-extensional and decidable, so the setoid trio is `rfl` / `.symm` / `.trans`
and the three operation congruences are `congrArg` chains. Each ring law reduces via
`BitVec.eq_of_toNat_eq` to a `natRemainder` identity discharged by the
`NatModularReduction` homomorphism steps.

The witness is indexed by `width + 1`: `BitVec 0` is the trivial ring `0 = 1`,
satisfying every law except nontriviality (`zeroIsApartFromOne`). As
`SetoidRingTower` excludes ℕ from rings at negation, width 0 is excluded from
nontrivial rings at apartness, so the `+1` is forced there alone.

`Init`-only, certificate-first, genuine-`Eq`, zero axioms. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The eight ring laws (generic over the width) -/

/-- Additive commutativity. -/
theorem bitVecAddComm {width : Nat} (left right : BitVec width) :
    bitVecAdd left right = bitVecAdd right left :=
  BitVec.eq_of_toNat_eq
    ((bitVecAddToNat left right).trans
      ((congrArg (fun summed => natRemainder summed (2 ^ width))
          (Nat.add_comm left.toNat right.toNat)).trans
        (bitVecAddToNat right left).symm))

/-- Multiplicative commutativity. -/
theorem bitVecMulComm {width : Nat} (left right : BitVec width) :
    bitVecMul left right = bitVecMul right left :=
  BitVec.eq_of_toNat_eq
    ((bitVecMulToNat left right).trans
      ((congrArg (fun scaled => natRemainder scaled (2 ^ width))
          (Nat.mul_comm left.toNat right.toNat)).trans
        (bitVecMulToNat right left).symm))

/-- Additive associativity — both groupings normalise to `natRemainder ((a+b)+c)`. -/
theorem bitVecAddAssoc {width : Nat} (left middle right : BitVec width) :
    bitVecAdd (bitVecAdd left middle) right = bitVecAdd left (bitVecAdd middle right) :=
  let positive : 0 < 2 ^ width := Nat.two_pow_pos width
  let leftNorm :
      (bitVecAdd (bitVecAdd left middle) right).toNat =
        natRemainder ((left.toNat + middle.toNat) + right.toNat) (2 ^ width) :=
    (bitVecAddToNat (bitVecAdd left middle) right).trans
      ((congrArg (fun inner => natRemainder (inner + right.toNat) (2 ^ width))
          (bitVecAddToNat left middle)).trans
        (natRemainderAddPush (left.toNat + middle.toNat) right.toNat (2 ^ width) positive))
  let rightNorm :
      (bitVecAdd left (bitVecAdd middle right)).toNat =
        natRemainder ((left.toNat + middle.toNat) + right.toNat) (2 ^ width) :=
    (bitVecAddToNat left (bitVecAdd middle right)).trans
      ((congrArg (fun inner => natRemainder (left.toNat + inner) (2 ^ width))
          (bitVecAddToNat middle right)).trans
        ((congrArg (fun summed => natRemainder summed (2 ^ width))
            (Nat.add_comm left.toNat
              (natRemainder (middle.toNat + right.toNat) (2 ^ width)))).trans
          ((natRemainderAddPush (middle.toNat + right.toNat) left.toNat (2 ^ width) positive).trans
            (congrArg (fun summed => natRemainder summed (2 ^ width))
              ((Nat.add_comm (middle.toNat + right.toNat) left.toNat).trans
                (Nat.add_assoc left.toNat middle.toNat right.toNat).symm)))))
  BitVec.eq_of_toNat_eq (leftNorm.trans rightNorm.symm)

/-- Multiplicative associativity — both groupings normalise to `natRemainder ((a*b)*c)`. -/
theorem bitVecMulAssoc {width : Nat} (left middle right : BitVec width) :
    bitVecMul (bitVecMul left middle) right = bitVecMul left (bitVecMul middle right) :=
  let positive : 0 < 2 ^ width := Nat.two_pow_pos width
  let leftNorm :
      (bitVecMul (bitVecMul left middle) right).toNat =
        natRemainder ((left.toNat * middle.toNat) * right.toNat) (2 ^ width) :=
    (bitVecMulToNat (bitVecMul left middle) right).trans
      ((congrArg (fun inner => natRemainder (inner * right.toNat) (2 ^ width))
          (bitVecMulToNat left middle)).trans
        (natRemainderMulPush (left.toNat * middle.toNat) right.toNat (2 ^ width) positive))
  let rightNorm :
      (bitVecMul left (bitVecMul middle right)).toNat =
        natRemainder ((left.toNat * middle.toNat) * right.toNat) (2 ^ width) :=
    (bitVecMulToNat left (bitVecMul middle right)).trans
      ((congrArg (fun inner => natRemainder (left.toNat * inner) (2 ^ width))
          (bitVecMulToNat middle right)).trans
        ((congrArg (fun scaled => natRemainder scaled (2 ^ width))
            (Nat.mul_comm left.toNat
              (natRemainder (middle.toNat * right.toNat) (2 ^ width)))).trans
          ((natRemainderMulPush (middle.toNat * right.toNat) left.toNat (2 ^ width) positive).trans
            (congrArg (fun scaled => natRemainder scaled (2 ^ width))
              ((Nat.mul_comm (middle.toNat * right.toNat) left.toNat).trans
                (natMulAssoc left.toNat middle.toNat right.toNat).symm)))))
  BitVec.eq_of_toNat_eq (leftNorm.trans rightNorm.symm)

/-- Right additive identity — `0` reduces out and `value < 2^width` is its own remainder. -/
theorem bitVecAddZeroRight {width : Nat} (value : BitVec width) :
    bitVecAdd value bitVecZero = value :=
  BitVec.eq_of_toNat_eq
    ((bitVecAddToNat value bitVecZero).trans
      ((congrArg (fun summed => natRemainder summed (2 ^ width))
          ((congrArg (value.toNat + ·) bitVecZeroToNat).trans (Nat.add_zero value.toNat))).trans
        (natRemainderOfLt value.isLt)))

/-- Right additive inverse — `value + (2^width - value) = 2^width` reduces to `0`. -/
theorem bitVecAddNegRight {width : Nat} (value : BitVec width) :
    bitVecAdd value (bitVecNeg value) = bitVecZero :=
  let positive : 0 < 2 ^ width := Nat.two_pow_pos width
  BitVec.eq_of_toNat_eq
    ((bitVecAddToNat value (bitVecNeg value)).trans
      (((congrArg (fun complemented => natRemainder (value.toNat + complemented) (2 ^ width))
            (bitVecNegToNat value)).trans
        ((congrArg (fun summed => natRemainder summed (2 ^ width))
            (Nat.add_comm value.toNat
              (natRemainder (2 ^ width - value.toNat) (2 ^ width)))).trans
          ((natRemainderAddPush (2 ^ width - value.toNat) value.toNat (2 ^ width) positive).trans
            ((congrArg (fun summed => natRemainder summed (2 ^ width))
                ((Nat.add_comm (2 ^ width - value.toNat) value.toNat).trans
                  (natAddSubOfLe (Nat.le_of_lt value.isLt)))).trans
              (natRemainderSelf positive))))).trans
        bitVecZeroToNat.symm))

/-- Left distributivity — both sides normalise to
`natRemainder (factor*left + factor*right)`. -/
theorem bitVecMulDistribLeft {width : Nat} (factor left right : BitVec width) :
    bitVecMul factor (bitVecAdd left right) =
      bitVecAdd (bitVecMul factor left) (bitVecMul factor right) :=
  let positive : 0 < 2 ^ width := Nat.two_pow_pos width
  let leftNorm :
      (bitVecMul factor (bitVecAdd left right)).toNat =
        natRemainder (factor.toNat * left.toNat + factor.toNat * right.toNat) (2 ^ width) :=
    (bitVecMulToNat factor (bitVecAdd left right)).trans
      ((congrArg (fun inner => natRemainder (factor.toNat * inner) (2 ^ width))
          (bitVecAddToNat left right)).trans
        ((congrArg (fun scaled => natRemainder scaled (2 ^ width))
            (Nat.mul_comm factor.toNat
              (natRemainder (left.toNat + right.toNat) (2 ^ width)))).trans
          ((natRemainderMulPush (left.toNat + right.toNat) factor.toNat (2 ^ width) positive).trans
            (congrArg (fun scaled => natRemainder scaled (2 ^ width))
              ((Nat.mul_comm (left.toNat + right.toNat) factor.toNat).trans
                (Nat.left_distrib factor.toNat left.toNat right.toNat))))))
  let rightNorm :
      (bitVecAdd (bitVecMul factor left) (bitVecMul factor right)).toNat =
        natRemainder (factor.toNat * left.toNat + factor.toNat * right.toNat) (2 ^ width) :=
    (bitVecAddToNat (bitVecMul factor left) (bitVecMul factor right)).trans
      ((congrArg (fun inner => natRemainder (inner + (bitVecMul factor right).toNat) (2 ^ width))
          (bitVecMulToNat factor left)).trans
        ((natRemainderAddPush (factor.toNat * left.toNat) (bitVecMul factor right).toNat
            (2 ^ width) positive).trans
          ((congrArg
              (fun inner => natRemainder (factor.toNat * left.toNat + inner) (2 ^ width))
              (bitVecMulToNat factor right)).trans
            ((congrArg (fun summed => natRemainder summed (2 ^ width))
                (Nat.add_comm (factor.toNat * left.toNat)
                  (natRemainder (factor.toNat * right.toNat) (2 ^ width)))).trans
              ((natRemainderAddPush (factor.toNat * right.toNat) (factor.toNat * left.toNat)
                  (2 ^ width) positive).trans
                (congrArg (fun summed => natRemainder summed (2 ^ width))
                  (Nat.add_comm (factor.toNat * right.toNat) (factor.toNat * left.toNat))))))))
  BitVec.eq_of_toNat_eq (leftNorm.trans rightNorm.symm)

/-! ## Unit and nontriviality (positive width) -/

/-- On a width whose modulus exceeds `1`, the unit vector reads back as `1`. -/
theorem bitVecOneToNat {width : Nat} (isWide : 1 < 2 ^ width) :
    (bitVecOne (width := width)).toNat = 1 :=
  (bitVecOfNatModToNat 1).trans (natRemainderOfLt isWide)

/-- Right multiplicative identity (needs `1 < 2^width` so the unit is nonzero). -/
theorem bitVecMulOneRight {width : Nat} (isWide : 1 < 2 ^ width) (value : BitVec width) :
    bitVecMul value bitVecOne = value :=
  BitVec.eq_of_toNat_eq
    ((bitVecMulToNat value bitVecOne).trans
      ((congrArg (fun oneNat => natRemainder (value.toNat * oneNat) (2 ^ width))
          (bitVecOneToNat isWide)).trans
        ((congrArg (fun scaled => natRemainder scaled (2 ^ width))
            (Nat.mul_one value.toNat)).trans
          (natRemainderOfLt value.isLt))))

/-- Nontriviality: `0` and `1` are distinct once the modulus exceeds `1`. -/
theorem bitVecZeroApartOne {width : Nat} (isWide : 1 < 2 ^ width) :
    ¬ (bitVecZero (width := width) = bitVecOne) :=
  fun sameConstant =>
    Nat.noConfusion
      (bitVecZeroToNat.symm.trans
        ((congrArg BitVec.toNat sameConstant).trans (bitVecOneToNat isWide)))

/-! ## The commutative-ring witness -/

/-- `Z / 2^(width+1) Z` as a commutative ring: genuine `Eq` setoid over core
`BitVec (width+1)`, all eight laws discharged from the modular-reduction corpus. The
`+1` guarantees `1 < 2^(width+1)`, hence nontriviality. -/
def bitVecCommutativeRingWitness (width : Nat) :
    CommutativeRingWitness (BitVec (width + 1)) :=
  let isWide : 1 < 2 ^ (width + 1) :=
    Nat.one_lt_two_pow (fun succEqZero => Nat.noConfusion succEqZero)
  { denotesSame := Eq
    zero := bitVecZero
    one := bitVecOne
    add := bitVecAdd
    mul := bitVecMul
    neg := bitVecNeg
    denotesSameIsReflexive := fun _ => rfl
    denotesSameIsSymmetric := fun _ _ areEqual => areEqual.symm
    denotesSameIsTransitive := fun _ _ _ firstEqual lastEqual => firstEqual.trans lastEqual
    addRespectsDenotesSame := fun leftValue newLeftValue rightValue newRightValue
        leftEqual rightEqual =>
      (congrArg (fun chosen => bitVecAdd chosen rightValue) leftEqual).trans
        (congrArg (bitVecAdd newLeftValue) rightEqual)
    mulRespectsDenotesSame := fun leftValue newLeftValue rightValue newRightValue
        leftEqual rightEqual =>
      (congrArg (fun chosen => bitVecMul chosen rightValue) leftEqual).trans
        (congrArg (bitVecMul newLeftValue) rightEqual)
    negRespectsDenotesSame := fun _ _ areEqual => congrArg bitVecNeg areEqual
    addIsCommutative := bitVecAddComm
    addIsAssociative := bitVecAddAssoc
    zeroIsRightAdditiveIdentity := bitVecAddZeroRight
    negIsRightAdditiveInverse := bitVecAddNegRight
    mulIsCommutative := bitVecMulComm
    mulIsAssociative := bitVecMulAssoc
    oneIsRightMultiplicativeIdentity := bitVecMulOneRight isWide
    mulDistributesOverAdd := bitVecMulDistribLeft
    zeroIsApartFromOne := bitVecZeroApartOne isWide }

end FX1Poly.ComputerAlgebra
