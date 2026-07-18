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
  constantly `false`, so every bit contributes `0`.

Together these are the additive-group half of the §18.6 Boolean-ring reading of a
machine word (xor = addition, self-inverse; and = idempotent multiplication) — the
associativity / idempotence / distributivity half needs the bit-decomposition
`value mod 2^w = Σ bitWeight (bitAtNat value p) p` and is deferred.

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

end FX1Poly.ComputerAlgebra
