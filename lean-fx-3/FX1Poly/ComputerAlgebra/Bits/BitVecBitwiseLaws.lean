import FX1Poly.ComputerAlgebra.Bits.BitVec

/-! # BitVecBitwiseLaws — the symmetric-fold laws of the structural bitwise logic

The bitwise surface of `Bits/BitVec` (`bitVecAnd` / `bitVecOr` / `bitVecXor`) is a
structural per-bit fold over `Bool` (`bitwiseFold`), deliberately built to avoid
the propext-poisoned `Nat.land` / `Nat.testBit`.  This file harvests the laws that
follow from that fold WITHOUT a bit-decomposition theorem — exactly the ones whose
per-bit truth-table is symmetric or self-annihilating:

* **commutativity** of `and` / `or` / `xor` — each combiner is symmetric on `Bool`,
  so swapping the operands leaves every per-bit contribution fixed
  (`bitwiseFoldSymm`);
* **xor self-annihilation** `x ⊕ x = 0` — the per-bit combiner `b != b` is
  constantly `false`, so every bit contributes `0`;
* **and-annihilator** `x AND 0 = 0` (both orders) — the combiner `and b false` is
  constantly `false`, the same constant-`0`-fold shape (`bitwiseFoldAndZero`), so
  the zero word is the multiplicative absorbing element.

Together these are the additive-group half of the §18.6 Boolean-ring reading of a
machine word (xor = addition, self-inverse; and = idempotent multiplication) plus
the multiplicative annihilator.  The remaining multiplicative laws — associativity /
idempotence / distributivity, and the `or`/`xor` identity `x ⊕ 0 = x` (which unlike
the annihilator PRESERVES the operand's bits) — all need the per-bit READBACK
`bitAtNat (bitwiseFold combine a b w) q = combine (bitAtNat a q) (bitAtNat b q)` and
thence the bit-decomposition `value mod 2^w = Σ bitWeight (bitAtNat value p) p`; that
is a separate multi-lemma arc and is deferred.

`Init`-only, structural, GENUINE `Eq` (core `BitVec`, no setoid), zero axioms:
`natBle`-free (Bool truth tables only), no `List.append`, no `Nat.le` lemma. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The symmetric-fold lemma -/

/-- If a bit-combiner is symmetric on `Bool`, the `bitwiseFold` is independent of
operand order.  Structural induction on the bit `count`; each step swaps the
per-bit contribution via `isSymmetric` and recurses through the inductive
hypothesis. -/
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

/-- **Bitwise AND is commutative** — `Bool.and` is symmetric per bit. -/
theorem bitVecAndComm {width : Nat} (left right : BitVec width) :
    bitVecAnd left right = bitVecAnd right left :=
  congrArg bitVecOfNatMod
    (bitwiseFoldSymm and (fun leftBit rightBit => by cases leftBit <;> cases rightBit <;> rfl)
      left.toNat right.toNat width)

/-- **Bitwise OR is commutative** — `Bool.or` is symmetric per bit. -/
theorem bitVecOrComm {width : Nat} (left right : BitVec width) :
    bitVecOr left right = bitVecOr right left :=
  congrArg bitVecOfNatMod
    (bitwiseFoldSymm or (fun leftBit rightBit => by cases leftBit <;> cases rightBit <;> rfl)
      left.toNat right.toNat width)

/-- **Bitwise XOR is commutative** — the combiner `b₁ != b₂` is symmetric per bit. -/
theorem bitVecXorComm {width : Nat} (left right : BitVec width) :
    bitVecXor left right = bitVecXor right left :=
  congrArg bitVecOfNatMod
    (bitwiseFoldSymm (fun leftBit rightBit => leftBit != rightBit)
      (fun leftBit rightBit => by cases leftBit <;> cases rightBit <;> rfl)
      left.toNat right.toNat width)

/-! ## XOR self-annihilation -/

/-- An absent bit contributes nothing: `bitWeight false position = 0` (the `else`
branch, by definitional reduction of the `false` guard). -/
theorem bitWeightOfFalse (position : Nat) : bitWeight false position = 0 := rfl

/-- The XOR fold of a value with itself is `0`: every bit's combiner is `b != b`,
which is constantly `false`, so each `bitWeight` contribution is `0`.  Structural
induction on the bit `count`. -/
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

/-- ★ **XOR self-annihilation** `x ⊕ x = 0` — the additive self-inverse law of the
Boolean-ring reading (xor is a `Bool`-graded addition; a value is its own additive
inverse).  Reduces through `toNat` to `bitwiseFoldXorSelf`. -/
theorem bitVecXorSelf {width : Nat} (value : BitVec width) :
    bitVecXor value value = bitVecZero := by
  apply BitVec.eq_of_toNat_eq
  rw [bitVecZeroToNat]
  unfold bitVecXor
  rw [bitVecOfNatModToNat, bitwiseFoldXorSelf, natRemainderOfLt (Nat.two_pow_pos width)]

/-! ## AND with the zero word — the multiplicative annihilator -/

/-- Shifting `0` right by any amount stays `0`.  Structural induction on the shift `position` through
`Nat.shiftRight_succ` (`n >>> (k+1) = (n >>> k) / 2`), the recursive `0 / 2 = 0` closing each step. -/
theorem natShiftRightZero (position : Nat) : (0 : Nat) >>> position = 0 := by
  induction position with
  | zero => rfl
  | succ predecessor ih => rw [Nat.shiftRight_succ, ih]

/-- Every bit of the natural `0` is `false`: `bitAtNat 0 position = false` — the access
`natRemainder (0 >>> position) 2` reduces to `natRemainder 0 2 = 0` via `natShiftRightZero`. -/
theorem bitAtNatZero (position : Nat) : bitAtNat 0 position = false := by
  show (! (natRemainder ((0 : Nat) >>> position) 2 == 0)) = false
  rw [natShiftRightZero position]
  rfl

/-- The `and`-fold against the all-zero operand is constantly `0`: every per-bit contribution is
`and (bitAtNat value position) false = false`, weighing `0`.  Structural induction on the bit `count`. -/
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

/-- ★ **AND annihilator (right)** `value AND 0 = 0` — the `0` is the multiplicative absorbing element of
the Boolean-ring reading (`and` is the multiplication).  Reduces through `toNat` to `bitwiseFoldAndZero`. -/
theorem bitVecAndZeroRight {width : Nat} (value : BitVec width) :
    bitVecAnd value bitVecZero = bitVecZero := by
  apply BitVec.eq_of_toNat_eq
  rw [bitVecZeroToNat]
  unfold bitVecAnd
  rw [bitVecOfNatModToNat, bitVecZeroToNat, bitwiseFoldAndZero,
      natRemainderOfLt (Nat.two_pow_pos width)]

/-- ★ **AND annihilator (left)** `0 AND value = 0` — the mirror of `bitVecAndZeroRight` through the shipped
commutativity `bitVecAndComm`. -/
theorem bitVecAndZeroLeft {width : Nat} (value : BitVec width) :
    bitVecAnd bitVecZero value = bitVecZero :=
  (bitVecAndComm bitVecZero value).trans (bitVecAndZeroRight value)

/-! ## Groundings -/

/-- ★ **Commutativity in action** — `and`/`or`/`xor` of two concrete 4-bit words
agree in either order (decided by the shipped commutativity laws, no per-bit
computation supplied). -/
theorem bitVecBitwiseCommGrounding (left right : BitVec 4) :
    bitVecAnd left right = bitVecAnd right left
      ∧ bitVecOr left right = bitVecOr right left
      ∧ bitVecXor left right = bitVecXor right left :=
  ⟨bitVecAndComm left right, bitVecOrComm left right, bitVecXorComm left right⟩

/-- ★ **Self-annihilation in action** — the all-ones 8-bit word XOR'd with itself is
zero, the additive-inverse witness at a concrete width. -/
theorem bitVecXorSelfGrounding (value : BitVec 8) : bitVecXor value value = bitVecZero :=
  bitVecXorSelf value

/-- ★ **Annihilator in action** — any 8-bit word AND'd with the zero word is zero, in either order:
the multiplicative-absorbing witness at a concrete width. -/
theorem bitVecAndZeroGrounding (value : BitVec 8) :
    bitVecAnd value bitVecZero = bitVecZero ∧ bitVecAnd bitVecZero value = bitVecZero :=
  ⟨bitVecAndZeroRight value, bitVecAndZeroLeft value⟩

end FX1Poly.ComputerAlgebra
