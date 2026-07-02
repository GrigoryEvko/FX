/-! # FX1Poly/ComputerAlgebra/Number/IntArithmeticCore — the zero-axiom Int kit, commutative core
    (FLOAT-1 brick 1)

`ComputerAlgebra/Number/` is the hand-rolled replacement for Init's Int lemma corpus, which is
almost entirely propext-dirty on this toolchain (v4.29.1).  Probe ledger (2026-07-02, `#print
axioms` over the ~50 lemmas the FloatingPoint carrier needs):

  * CLEAN Init survivors (re-exported below under the kit's uniform names): `Int.add_zero`,
    `Int.one_mul`, `Int.mul_zero`, `Int.neg_neg`, `Int.neg_zero`, `Int.sub_eq_add_neg`,
    `Int.lt_iff_add_one_le`, and the decision procedures `Int.decEq` / `Int.decLt` / `Int.decLe`
    (hand-written structural — usable directly as instances).
  * PROPEXT-DIRTY (every symbolic fact): `Int.add_comm`, `Int.add_assoc`, `Int.zero_add`,
    `Int.mul_comm`, `Int.mul_assoc`, `Int.mul_one`, `Int.zero_mul`, `Int.add_mul`, `Int.mul_add`,
    `Int.neg_add`, `Int.neg_mul`, `Int.mul_neg`, `Int.add_left_neg`, the whole order corpus
    (`le_refl`/`le_trans`/`le_antisymm`/`mul_le_mul_*`/`mul_pos`/`mul_nonneg`/`le_total`), and
    the division corpus (`ediv_add_emod`/`emod_nonneg`/`emod_lt_of_pos`/`pow_*`).
  * The Nat backing needed for hand-rolls is CLEAN: `Nat.add_comm`, `Nat.add_assoc`,
    `Nat.mul_comm`, `Nat.zero_add`, `Nat.zero_mul`, `Nat.mul_one`, `Nat.succ_add`,
    `Nat.add_succ`, `Nat.mul_succ`, `Nat.succ_mul`, `Nat.succ_sub_succ`, and the order kit
    (`le_refl`/`le_trans`/`le_antisymm`/`le_total`/`add_le_add_left`/`add_le_add_right`).
    (Dirty Nat stragglers: `Nat.sub_add_cancel`, `Nat.add_sub_cancel`, `Nat.sub_sub`.)

This brick ships the COMMUTATIVE CORE: additive/multiplicative identities and commutativity —
every proof is a two- or four-way constructor split closing by `rfl` or a single `congrArg` over
a clean Nat lemma (the cross-sign `Int.add` arms are literally definitionally symmetric).  The
associativity/distributivity/order kit (which needs the `Int.subNatNat` case analysis) is the
next brick.

## Zero-axiom

Full-enumeration constructor matches (no wildcards), `congrArg` over clean Nat lemmas, `rfl`
where `Int.add`/`Int.mul` arms are definitionally symmetric.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/Number/IntArithmeticCore.lean`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Clean Init survivors, re-exported under the kit's uniform names -/

/-- `value + 0 = value` — clean in Init, re-exported for the uniform kit surface. -/
theorem intAddZero (value : Int) : value + 0 = value := Int.add_zero value

/-- `1 * value = value` — clean in Init, re-exported. -/
theorem intOneMul (value : Int) : 1 * value = value := Int.one_mul value

/-- `value * 0 = 0` — clean in Init, re-exported. -/
theorem intMulZero (value : Int) : value * 0 = 0 := Int.mul_zero value

/-- Negation is an involution — clean in Init, re-exported. -/
theorem intNegNeg (value : Int) : - - value = value := Int.neg_neg value

/-- `-0 = 0` — clean in Init, re-exported. -/
theorem intNegZero : -(0 : Int) = 0 := Int.neg_zero

/-- Subtraction unfolds to addition of the negation — clean in Init, re-exported. -/
theorem intSubEqAddNeg (left right : Int) : left - right = left + -right :=
  Int.sub_eq_add_neg

/-! ## Hand-rolled replacements for the propext-dirty Init corpus -/

/-- `0 + value = value` (Init's `Int.zero_add` is propext-dirty).  The `negSucc` arm is
definitional: `subNatNat 0 (n+1)` computes straight to `negSucc n`. -/
theorem intZeroAdd : ∀ value : Int, 0 + value = value
  | .ofNat valueNat => congrArg Int.ofNat (Nat.zero_add valueNat)
  | .negSucc _ => rfl

/-- Addition commutes (Init's `Int.add_comm` is propext-dirty).  The two cross-sign arms of
`Int.add` produce the SAME `subNatNat` call, so they close by `rfl`; the same-sign arms are
`congrArg` over `Nat.add_comm`. -/
theorem intAddComm : ∀ left right : Int, left + right = right + left
  | .ofNat leftNat, .ofNat rightNat => congrArg Int.ofNat (Nat.add_comm leftNat rightNat)
  | .ofNat _, .negSucc _ => rfl
  | .negSucc _, .ofNat _ => rfl
  | .negSucc leftNat, .negSucc rightNat =>
      congrArg (fun sumNat => Int.negSucc (sumNat + 1)) (Nat.add_comm leftNat rightNat)

/-- Multiplication commutes (Init's `Int.mul_comm` is propext-dirty).  Every arm is a single
`congrArg` over `Nat.mul_comm` at the arm's sign carrier (`ofNat` / `negOfNat`). -/
theorem intMulComm : ∀ left right : Int, left * right = right * left
  | .ofNat leftNat, .ofNat rightNat => congrArg Int.ofNat (Nat.mul_comm leftNat rightNat)
  | .ofNat leftNat, .negSucc rightNat =>
      congrArg Int.negOfNat (Nat.mul_comm leftNat (rightNat + 1))
  | .negSucc leftNat, .ofNat rightNat =>
      congrArg Int.negOfNat (Nat.mul_comm (leftNat + 1) rightNat)
  | .negSucc leftNat, .negSucc rightNat =>
      congrArg Int.ofNat (Nat.mul_comm (leftNat + 1) (rightNat + 1))

/-- `value * 1 = value` (Init's `Int.mul_one` is propext-dirty).  `n * 1` is DEFINITIONALLY
`0 + n` (`Nat.mul` recurses on its second argument), so each arm is `congrArg` over
`Nat.zero_add`, with `negOfNat (n+1) = negSucc n` closing definitionally. -/
theorem intMulOne : ∀ value : Int, value * 1 = value
  | .ofNat valueNat => congrArg Int.ofNat (Nat.zero_add valueNat)
  | .negSucc valueNat => congrArg Int.negOfNat (Nat.zero_add (valueNat + 1))

/-- `0 * value = 0` (Init's `Int.zero_mul` is propext-dirty).  Each arm is `congrArg` over
`Nat.zero_mul`, with `negOfNat 0 = 0` closing definitionally. -/
theorem intZeroMul : ∀ value : Int, 0 * value = 0
  | .ofNat valueNat => congrArg Int.ofNat (Nat.zero_mul valueNat)
  | .negSucc valueNat => congrArg Int.negOfNat (Nat.zero_mul (valueNat + 1))

end FX1Poly.ComputerAlgebra
