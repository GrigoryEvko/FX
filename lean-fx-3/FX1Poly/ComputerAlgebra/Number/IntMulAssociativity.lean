import FX1Poly.ComputerAlgebra.Number.IntArithmeticCore

/-! # FX1Poly/ComputerAlgebra/Number/IntMulAssociativity — hand-rolled mul associativity
    (FLOAT-1 brick 5)

Init's `Nat.mul_assoc` and `Int.mul_assoc` are propext-dirty (probed 2026-07-02, v4.29.1);
this module hand-rolls both.  Three pieces:

  * `natMulAssoc` — the Nat backing.  Structural recursion on the RIGHT factor (Nat.mul
    recurses on its second argument, so `x * (r + 1)` is definitionally `x * r + x`); the
    step case is one `Nat.left_distrib` (clean) after the inductive hypothesis.
  * The four MIXED-SIGN MUL HELPERS (`intOfNatMulNegOfNat` / `intNegOfNatMulOfNat` /
    `intNegOfNatMulNegSucc` / `intNegSuccMulNegOfNat`): the `Int.mul` arms produce
    `negOfNat`, so re-associating a triple product needs multiplication characterized on
    `negOfNat` operands.  Each is a two-case split; the `negOfNat 0` arms either close by
    `rfl` (`factor * 0` is definitionally `0`) or need one `Nat.zero_mul` fixup on each
    side (`0 * factor` is NOT definitional).
  * `intMulAssoc` — the eight-way constructor bash.  Every case lands on a shared
    `ofNat`/`negOfNat` form through the helpers, closing with `congrArg` over
    `natMulAssoc`.

## Zero-axiom

Structural recursion + `congrArg`/`Eq.trans` chains over clean Nat lemmas
(`Nat.left_distrib`, `Nat.zero_mul`).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/Number/IntMulAssociativity.lean`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The Nat backing -/

/-- **Nat multiplication associativity** (Init's `Nat.mul_assoc` is propext-dirty).
Recursion on the right factor: `x * (r + 1)` is definitionally `x * r + x`, so the step
case is the inductive hypothesis under `(· + leftFactor * middleFactor)` followed by one
`Nat.left_distrib`. -/
theorem natMulAssoc : ∀ leftFactor middleFactor rightFactor : Nat,
    leftFactor * middleFactor * rightFactor = leftFactor * (middleFactor * rightFactor)
  | _, _, 0 => rfl
  | leftFactor, middleFactor, rightFactor + 1 =>
      (congrArg (· + leftFactor * middleFactor)
          (natMulAssoc leftFactor middleFactor rightFactor)).trans
        (Nat.left_distrib leftFactor (middleFactor * rightFactor) middleFactor).symm

/-! ## The mixed-sign mul helpers -/

/-- `ofNat * negOfNat` multiplies into the `negOfNat` — both arms definitional
(`factor * 0` reduces to `0`, so the zero arm is two spellings of `ofNat 0`). -/
theorem intOfNatMulNegOfNat : ∀ factorValue tailValue : Nat,
    Int.ofNat factorValue * Int.negOfNat tailValue = Int.negOfNat (factorValue * tailValue)
  | _, 0 => rfl
  | _, _ + 1 => rfl

/-- `negOfNat * ofNat` multiplies into the `negOfNat`.  The zero arm needs `Nat.zero_mul`
on each side (`0 * factor` is not definitional). -/
theorem intNegOfNatMulOfNat : ∀ headValue factorValue : Nat,
    Int.negOfNat headValue * Int.ofNat factorValue = Int.negOfNat (headValue * factorValue)
  | 0, factorValue =>
      (congrArg Int.ofNat (Nat.zero_mul factorValue)).trans
        (congrArg Int.negOfNat (Nat.zero_mul factorValue)).symm
  | _ + 1, _ => rfl

/-- `negOfNat * negSucc` is a NONNEGATIVE product.  The zero arm needs `Nat.zero_mul` on
each side. -/
theorem intNegOfNatMulNegSucc : ∀ headValue tailPredecessor : Nat,
    Int.negOfNat headValue * Int.negSucc tailPredecessor =
      Int.ofNat (headValue * (tailPredecessor + 1))
  | 0, tailPredecessor =>
      (congrArg Int.negOfNat (Nat.zero_mul (tailPredecessor + 1))).trans
        (congrArg Int.ofNat (Nat.zero_mul (tailPredecessor + 1))).symm
  | _ + 1, _ => rfl

/-- `negSucc * negOfNat` is a NONNEGATIVE product — both arms definitional
(`factor * 0` reduces to `0`). -/
theorem intNegSuccMulNegOfNat : ∀ headPredecessor tailValue : Nat,
    Int.negSucc headPredecessor * Int.negOfNat tailValue =
      Int.ofNat ((headPredecessor + 1) * tailValue)
  | _, 0 => rfl
  | _, _ + 1 => rfl

/-! ## Associativity -/

/-- **Int multiplication associativity** (Init's `Int.mul_assoc` is propext-dirty).
Eight-way constructor bash: every mixed case collapses through the mixed-sign mul helpers
onto a shared `ofNat`/`negOfNat` form, closing with `congrArg` over `natMulAssoc`. -/
theorem intMulAssoc : ∀ leftFactor middleFactor rightFactor : Int,
    leftFactor * middleFactor * rightFactor = leftFactor * (middleFactor * rightFactor)
  | .ofNat leftNat, .ofNat middleNat, .ofNat rightNat =>
      congrArg Int.ofNat (natMulAssoc leftNat middleNat rightNat)
  | .ofNat leftNat, .ofNat middleNat, .negSucc rightPredecessor =>
      (congrArg Int.negOfNat (natMulAssoc leftNat middleNat (rightPredecessor + 1))).trans
        (intOfNatMulNegOfNat leftNat (middleNat * (rightPredecessor + 1))).symm
  | .ofNat leftNat, .negSucc middlePredecessor, .ofNat rightNat =>
      (intNegOfNatMulOfNat (leftNat * (middlePredecessor + 1)) rightNat).trans
        ((congrArg Int.negOfNat (natMulAssoc leftNat (middlePredecessor + 1) rightNat)).trans
          (intOfNatMulNegOfNat leftNat ((middlePredecessor + 1) * rightNat)).symm)
  | .ofNat leftNat, .negSucc middlePredecessor, .negSucc rightPredecessor =>
      (intNegOfNatMulNegSucc (leftNat * (middlePredecessor + 1)) rightPredecessor).trans
        (congrArg Int.ofNat
          (natMulAssoc leftNat (middlePredecessor + 1) (rightPredecessor + 1)))
  | .negSucc leftPredecessor, .ofNat middleNat, .ofNat rightNat =>
      (intNegOfNatMulOfNat ((leftPredecessor + 1) * middleNat) rightNat).trans
        (congrArg Int.negOfNat (natMulAssoc (leftPredecessor + 1) middleNat rightNat))
  | .negSucc leftPredecessor, .ofNat middleNat, .negSucc rightPredecessor =>
      (intNegOfNatMulNegSucc ((leftPredecessor + 1) * middleNat) rightPredecessor).trans
        ((congrArg Int.ofNat
            (natMulAssoc (leftPredecessor + 1) middleNat (rightPredecessor + 1))).trans
          (intNegSuccMulNegOfNat leftPredecessor
            (middleNat * (rightPredecessor + 1))).symm)
  | .negSucc leftPredecessor, .negSucc middlePredecessor, .ofNat rightNat =>
      (congrArg Int.ofNat
          (natMulAssoc (leftPredecessor + 1) (middlePredecessor + 1) rightNat)).trans
        (intNegSuccMulNegOfNat leftPredecessor ((middlePredecessor + 1) * rightNat)).symm
  | .negSucc leftPredecessor, .negSucc middlePredecessor, .negSucc rightPredecessor =>
      congrArg Int.negOfNat
        (natMulAssoc (leftPredecessor + 1) (middlePredecessor + 1) (rightPredecessor + 1))

end FX1Poly.ComputerAlgebra
