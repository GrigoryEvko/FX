import FX1Poly.ComputerAlgebra.Bits.BitVec

/-! # BitVecBitwiseLaws — symmetric-fold laws of the structural bitwise logic

The bitwise operations of `Bits/BitVec` (`bitVecAnd` / `bitVecOr` / `bitVecXor`) are a
structural per-bit fold over `Bool` (`bitwiseFold`) avoiding the propext-dependent
`Nat.land` / `Nat.testBit`. This file proves the laws whose per-bit truth table is
symmetric or self-annihilating, so they follow from the fold without a
bit-decomposition theorem:

* commutativity of `and` / `or` / `xor`, since each combiner is symmetric on `Bool`
  (`bitwiseFoldSymm`);
* xor self-annihilation `x ⊕ x = 0`, since `b != b` is constantly `false`;
* the and-annihilator `x AND 0 = 0` in both orders, since `and b false` is constantly
  `false` (`bitwiseFoldAndZero`).

These are the additive-group half of the §18.6 Boolean-ring reading of a machine word
(xor as self-inverse addition, and as idempotent multiplication) plus the
multiplicative annihilator. The remaining laws — associativity, idempotence,
distributivity, and `x ⊕ 0 = x` — require the per-bit readback and the
bit-decomposition `value mod 2^w = Σ bitWeight (bitAtNat value p) p`.

`Init`-only, structural, genuine `Eq` (core `BitVec`, no setoid), zero axioms. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The symmetric-fold lemma -/

/-- A symmetric bit-combiner yields a `bitwiseFold` independent of operand order,
swapping each per-bit contribution via `isSymmetric`. -/
theorem bitwiseFoldSymm (combine : Bool → Bool → Bool)
    (isSymmetric : ∀ leftBit rightBit : Bool, combine leftBit rightBit = combine rightBit leftBit)
    (left right count : Nat) :
    bitwiseFold combine left right count = bitwiseFold combine right left count := by
  induction count with
  | zero => rfl
  | succ position ih =>
      simp only [bitwiseFold]
      rw [ih, isSymmetric (bitAtNat left position) (bitAtNat right position)]

/-! ## Commutativity of and / or / xor -/

/-- Bitwise AND is commutative: `Bool.and` is symmetric per bit. -/
theorem bitVecAndComm {width : Nat} (left right : BitVec width) :
    bitVecAnd left right = bitVecAnd right left :=
  congrArg bitVecOfNatMod
    (bitwiseFoldSymm and (fun leftBit rightBit => by cases leftBit <;> cases rightBit <;> rfl)
      left.toNat right.toNat width)

/-- Bitwise OR is commutative: `Bool.or` is symmetric per bit. -/
theorem bitVecOrComm {width : Nat} (left right : BitVec width) :
    bitVecOr left right = bitVecOr right left :=
  congrArg bitVecOfNatMod
    (bitwiseFoldSymm or (fun leftBit rightBit => by cases leftBit <;> cases rightBit <;> rfl)
      left.toNat right.toNat width)

/-- Bitwise XOR is commutative: the combiner `b₁ != b₂` is symmetric per bit. -/
theorem bitVecXorComm {width : Nat} (left right : BitVec width) :
    bitVecXor left right = bitVecXor right left :=
  congrArg bitVecOfNatMod
    (bitwiseFoldSymm (fun leftBit rightBit => leftBit != rightBit)
      (fun leftBit rightBit => by cases leftBit <;> cases rightBit <;> rfl)
      left.toNat right.toNat width)

/-! ## XOR self-annihilation -/

/-- An absent bit contributes nothing: `bitWeight false position = 0`. -/
theorem bitWeightOfFalse (position : Nat) : bitWeight false position = 0 := rfl

/-- XOR of a value with itself folds to `0`: every combiner `b != b` is `false`. -/
theorem bitwiseFoldXorSelf (value count : Nat) :
    bitwiseFold (fun leftBit rightBit => leftBit != rightBit) value value count = 0 := by
  induction count with
  | zero => rfl
  | succ position ih =>
      simp only [bitwiseFold]
      rw [ih]
      have selfBne : (bitAtNat value position != bitAtNat value position) = false := by
        cases bitAtNat value position <;> rfl
      rw [selfBne, bitWeightOfFalse]

/-- XOR self-annihilation `x ⊕ x = 0`, the additive self-inverse of the Boolean-ring
reading, via `bitwiseFoldXorSelf`. -/
theorem bitVecXorSelf {width : Nat} (value : BitVec width) :
    bitVecXor value value = bitVecZero := by
  apply BitVec.eq_of_toNat_eq
  rw [bitVecZeroToNat]
  unfold bitVecXor
  rw [bitVecOfNatModToNat, bitwiseFoldXorSelf, natRemainderOfLt (Nat.two_pow_pos width)]

/-! ## AND with the zero word -/

/-- `0 >>> position = 0`, by induction through `Nat.shiftRight_succ`. -/
theorem natShiftRightZero (position : Nat) : (0 : Nat) >>> position = 0 := by
  induction position with
  | zero => rfl
  | succ predecessor ih => rw [Nat.shiftRight_succ, ih]

/-- Every bit of `0` is `false`: `bitAtNat 0 position = false` via `natShiftRightZero`. -/
theorem bitAtNatZero (position : Nat) : bitAtNat 0 position = false := by
  show (! (natRemainder ((0 : Nat) >>> position) 2 == 0)) = false
  rw [natShiftRightZero position]
  rfl

/-- The `and`-fold against the all-zero operand is `0`: every contribution
`and b false = false` weighs `0`. -/
theorem bitwiseFoldAndZero (value count : Nat) :
    bitwiseFold and value 0 count = 0 := by
  induction count with
  | zero => rfl
  | succ position ih =>
      show bitwiseFold and value 0 position
            + bitWeight (and (bitAtNat value position) (bitAtNat 0 position)) position = 0
      rw [ih, bitAtNatZero position]
      have hAndFalse : and (bitAtNat value position) false = false := by
        cases bitAtNat value position <;> rfl
      rw [hAndFalse, bitWeightOfFalse]

/-- AND right-annihilator `value AND 0 = 0`, the absorbing element of the Boolean-ring
multiplication, via `bitwiseFoldAndZero`. -/
theorem bitVecAndZeroRight {width : Nat} (value : BitVec width) :
    bitVecAnd value bitVecZero = bitVecZero := by
  apply BitVec.eq_of_toNat_eq
  rw [bitVecZeroToNat]
  unfold bitVecAnd
  rw [bitVecOfNatModToNat, bitVecZeroToNat, bitwiseFoldAndZero,
      natRemainderOfLt (Nat.two_pow_pos width)]

/-- AND left-annihilator `0 AND value = 0`, mirroring `bitVecAndZeroRight` via
`bitVecAndComm`. -/
theorem bitVecAndZeroLeft {width : Nat} (value : BitVec width) :
    bitVecAnd bitVecZero value = bitVecZero :=
  (bitVecAndComm bitVecZero value).trans (bitVecAndZeroRight value)

/-! ## Groundings -/

/-- Commutativity at width 4: `and` / `or` / `xor` of two words agree in either
order. -/
theorem bitVecBitwiseCommGrounding (left right : BitVec 4) :
    bitVecAnd left right = bitVecAnd right left
      ∧ bitVecOr left right = bitVecOr right left
      ∧ bitVecXor left right = bitVecXor right left :=
  ⟨bitVecAndComm left right, bitVecOrComm left right, bitVecXorComm left right⟩

/-- Self-annihilation at a concrete width: an 8-bit word XOR'd with itself is zero. -/
theorem bitVecXorSelfGrounding (value : BitVec 8) : bitVecXor value value = bitVecZero :=
  bitVecXorSelf value

/-- Annihilator at width 8: a word AND the zero word is zero, in either order. -/
theorem bitVecAndZeroGrounding (value : BitVec 8) :
    bitVecAnd value bitVecZero = bitVecZero ∧ bitVecAnd bitVecZero value = bitVecZero :=
  ⟨bitVecAndZeroRight value, bitVecAndZeroLeft value⟩

end FX1Poly.ComputerAlgebra
