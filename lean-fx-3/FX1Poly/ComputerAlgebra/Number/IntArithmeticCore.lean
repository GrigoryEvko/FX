/-! # The zero-axiom Int kit — commutative core

Most of Init's Int lemma corpus leaks `propext` on the current toolchain. The clean
survivors (`Int.add_zero`, `Int.one_mul`, `Int.mul_zero`, `Int.neg_neg`, `Int.neg_zero`,
`Int.sub_eq_add_neg`) are re-exported under the kit's uniform names; the dirty symbolic
facts are hand-rolled over a clean `Nat` backing.

This module supplies the commutative core — additive and multiplicative identities and
commutativity. Each proof is a full-enumeration constructor split closing by `rfl` or one
`congrArg` over a clean `Nat` lemma. Associativity, distributivity, and the order kit (which
need `Int.subNatNat` case analysis) live in sibling modules. Free of `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, and `omega`; per-declaration gated in
the audit twin. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Clean Init survivors, re-exported under the kit's uniform names -/

/-- `value + 0 = value`. -/
theorem intAddZero (value : Int) : value + 0 = value := Int.add_zero value

/-- `1 * value = value`. -/
theorem intOneMul (value : Int) : 1 * value = value := Int.one_mul value

/-- `value * 0 = 0`. -/
theorem intMulZero (value : Int) : value * 0 = 0 := Int.mul_zero value

/-- Negation is an involution. -/
theorem intNegNeg (value : Int) : - - value = value := Int.neg_neg value

/-- `-0 = 0`. -/
theorem intNegZero : -(0 : Int) = 0 := Int.neg_zero

/-- Subtraction unfolds to addition of the negation. -/
theorem intSubEqAddNeg (left right : Int) : left - right = left + -right :=
  Int.sub_eq_add_neg

/-! ## Hand-rolled replacements for the propext-leaking Init corpus -/

/-- `0 + value = value`. The `negSucc` arm is definitional: `subNatNat 0 (n+1)` computes to
`negSucc n`. -/
theorem intZeroAdd : ∀ value : Int, 0 + value = value
  | .ofNat valueNat => congrArg Int.ofNat (Nat.zero_add valueNat)
  | .negSucc _ => rfl

/-- Addition commutes. The cross-sign `Int.add` arms produce the same `subNatNat` call and
close by `rfl`; the same-sign arms are `congrArg` over `Nat.add_comm`. -/
theorem intAddComm : ∀ left right : Int, left + right = right + left
  | .ofNat leftNat, .ofNat rightNat => congrArg Int.ofNat (Nat.add_comm leftNat rightNat)
  | .ofNat _, .negSucc _ => rfl
  | .negSucc _, .ofNat _ => rfl
  | .negSucc leftNat, .negSucc rightNat =>
      congrArg (fun sumNat => Int.negSucc (sumNat + 1)) (Nat.add_comm leftNat rightNat)

/-- Multiplication commutes — one `congrArg` over `Nat.mul_comm` at each arm's sign carrier
(`ofNat` or `negOfNat`). -/
theorem intMulComm : ∀ left right : Int, left * right = right * left
  | .ofNat leftNat, .ofNat rightNat => congrArg Int.ofNat (Nat.mul_comm leftNat rightNat)
  | .ofNat leftNat, .negSucc rightNat =>
      congrArg Int.negOfNat (Nat.mul_comm leftNat (rightNat + 1))
  | .negSucc leftNat, .ofNat rightNat =>
      congrArg Int.negOfNat (Nat.mul_comm (leftNat + 1) rightNat)
  | .negSucc leftNat, .negSucc rightNat =>
      congrArg Int.ofNat (Nat.mul_comm (leftNat + 1) (rightNat + 1))

/-- `value * 1 = value`. `n * 1` is definitionally `0 + n` (`Nat.mul` recurses on its second
argument), so each arm is `congrArg` over `Nat.zero_add`. -/
theorem intMulOne : ∀ value : Int, value * 1 = value
  | .ofNat valueNat => congrArg Int.ofNat (Nat.zero_add valueNat)
  | .negSucc valueNat => congrArg Int.negOfNat (Nat.zero_add (valueNat + 1))

/-- `0 * value = 0` — `congrArg` over `Nat.zero_mul`, with `negOfNat 0 = 0` definitional. -/
theorem intZeroMul : ∀ value : Int, 0 * value = 0
  | .ofNat valueNat => congrArg Int.ofNat (Nat.zero_mul valueNat)
  | .negSucc valueNat => congrArg Int.negOfNat (Nat.zero_mul (valueNat + 1))

end FX1Poly.ComputerAlgebra
