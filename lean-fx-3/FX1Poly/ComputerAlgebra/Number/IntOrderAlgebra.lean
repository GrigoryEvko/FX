import FX1Poly.ComputerAlgebra.Number.IntOrderCore

/-! # FX1Poly/ComputerAlgebra/Number/IntOrderAlgebra — order meets algebra
    (FLOAT-1 brick 8)

Init's `Int.le_total` / `Int.add_le_add_left` / `Int.mul_nonneg` / `Int.mul_pos` are
propext-dirty; this module hand-rolls the order/algebra interaction over the brick-7
additive-witness interface:

  * The three SIGN-CASE `≤` builders (`intOfNatLeOfNat` / `intNegSuccLeOfNat` /
    `intNegSuccLeNegSucc`): each converts a clean Nat witness (`Nat.le.dest`) into the
    brick-7 intro form; the negSucc/negSucc case lands on `intSubNatNatRightSurplus`,
    and negSucc-below-ofNat is one `NonNeg` constructor.
  * `intLessEqualTotal` — the four-way constructor bash over `Nat.le_total` (clean).
  * Add-monotonicity (`intAddLeAddLeft` / `intAddLeAddRight`) — the witness is
    UNCHANGED by translation; one associativity step.
  * `intMulNonNeg` / `intMulPos` — destruct both operands to `ofNat` carriers; the
    product witness is Nat multiplication, with `intMulPos` peeling the explicit `1 +`
    successor shape through two `Nat.add_comm` shuffles (`x * (n + 1)` and `x + (m + 1)`
    are definitional).

## Zero-axiom

Witness arithmetic (`congrArg`/`Eq.trans`) over the brick-1..7 kit and clean Nat facts
(`Nat.le.dest`, `Nat.le_total`, `Nat.add_comm`).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/Number/IntOrderAlgebra.lean`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The sign-case builders -/

/-- `≤` between `ofNat`s from the Nat order — `Nat.le.dest`'s witness IS the Int
witness (`ofNat` addition is definitional). -/
theorem intOfNatLeOfNat {lowNat highNat : Nat} (isLessEqual : lowNat ≤ highNat) :
    Int.ofNat lowNat ≤ Int.ofNat highNat :=
  match Nat.le.dest isLessEqual with
  | ⟨difference, differenceEquation⟩ =>
      intLessEqualOfEqRight (intLessEqualIntro (Int.ofNat lowNat) difference)
        (congrArg Int.ofNat differenceEquation)

/-- Every `negSucc` sits below every `ofNat` — the difference computes to an `ofNat`,
so the proof is one `NonNeg` constructor. -/
theorem intNegSuccLeOfNat (lowPredecessor highNat : Nat) :
    Int.negSucc lowPredecessor ≤ Int.ofNat highNat :=
  show Int.NonNeg (Int.ofNat highNat + -(Int.negSucc lowPredecessor)) from
    Int.NonNeg.mk (highNat + (lowPredecessor + 1))

/-- `≤` between `negSucc`s REVERSES the Nat order.  The witness lands on
`intSubNatNatRightSurplus` after two payload shuffles. -/
theorem intNegSuccLeNegSucc {lowNat highNat : Nat} (isLessEqual : lowNat ≤ highNat) :
    Int.negSucc highNat ≤ Int.negSucc lowNat :=
  match Nat.le.dest isLessEqual with
  | ⟨difference, differenceEquation⟩ =>
      intLessEqualOfEqRight (intLessEqualIntro (Int.negSucc highNat) difference)
        ((congrArg (fun shiftedValue => Int.subNatNat difference (shiftedValue + 1))
            differenceEquation.symm).trans
          ((congrArg (fun sumValue => Int.subNatNat difference (sumValue + 1))
              (Nat.add_comm lowNat difference)).trans
            (intSubNatNatRightSurplus lowNat difference)))

/-- Totality (Init's `Int.le_total` is propext-dirty) — four-way bash over the clean
`Nat.le_total`. -/
theorem intLessEqualTotal : ∀ leftValue rightValue : Int,
    leftValue ≤ rightValue ∨ rightValue ≤ leftValue
  | .ofNat leftNat, .ofNat rightNat =>
      match Nat.le_total leftNat rightNat with
      | .inl isLeftBelow => .inl (intOfNatLeOfNat isLeftBelow)
      | .inr isRightBelow => .inr (intOfNatLeOfNat isRightBelow)
  | .ofNat leftNat, .negSucc rightPredecessor =>
      .inr (intNegSuccLeOfNat rightPredecessor leftNat)
  | .negSucc leftPredecessor, .ofNat rightNat =>
      .inl (intNegSuccLeOfNat leftPredecessor rightNat)
  | .negSucc leftPredecessor, .negSucc rightPredecessor =>
      match Nat.le_total rightPredecessor leftPredecessor with
      | .inl isRightBelow => .inl (intNegSuccLeNegSucc isRightBelow)
      | .inr isLeftBelow => .inr (intNegSuccLeNegSucc isLeftBelow)

/-! ## Nonnegativity plumbing -/

/-- `0 ≤ ofNat` — the difference computes straight to the constructor. -/
theorem intZeroLeOfNat (value : Nat) : (0 : Int) ≤ Int.ofNat value := Int.NonNeg.mk value

/-- A nonnegative Int IS an `ofNat` — brick-7 destruction with the `0 +` collapsed. -/
theorem intZeroLeDest {value : Int} (isNonNegative : (0 : Int) ≤ value) :
    ∃ witness : Nat, value = Int.ofNat witness :=
  match intLessEqualDest isNonNegative with
  | ⟨witness, witnessEquation⟩ =>
      ⟨witness, witnessEquation.trans (intZeroAdd (Int.ofNat witness))⟩

/-- `<` weakens to `≤` — chain the one-step witness through transitivity. -/
theorem intLessEqualOfLessThan {lowValue highValue : Int}
    (isLessThan : lowValue < highValue) : lowValue ≤ highValue :=
  intLessEqualTrans (intLessEqualIntro lowValue 1)
    (show lowValue + Int.ofNat 1 ≤ highValue from isLessThan)

/-! ## Monotonicity of addition -/

/-- Adding on the left preserves `≤` (Init's `Int.add_le_add_left` is propext-dirty) —
the witness is unchanged, re-parenthesized by one associativity step. -/
theorem intAddLeAddLeft {lowValue highValue : Int} (isLessEqual : lowValue ≤ highValue)
    (leftAddend : Int) : leftAddend + lowValue ≤ leftAddend + highValue :=
  match intLessEqualDest isLessEqual with
  | ⟨difference, differenceEquation⟩ =>
      intLessEqualOfEqRight (intLessEqualIntro (leftAddend + lowValue) difference)
        ((intAddAssoc leftAddend lowValue (Int.ofNat difference)).trans
          (congrArg (leftAddend + ·) differenceEquation.symm))

/-- Adding on the right preserves `≤` — corollary through `intAddComm`. -/
theorem intAddLeAddRight {lowValue highValue : Int} (isLessEqual : lowValue ≤ highValue)
    (rightAddend : Int) : lowValue + rightAddend ≤ highValue + rightAddend :=
  intLessEqualOfEqLeft (intAddComm lowValue rightAddend)
    (intLessEqualOfEqRight (intAddLeAddLeft isLessEqual rightAddend)
      (intAddComm rightAddend highValue))

/-! ## Positivity of multiplication -/

/-- Products of nonnegatives are nonnegative (Init's `Int.mul_nonneg` is
propext-dirty) — both factors are `ofNat` carriers, so the product witness is the Nat
product. -/
theorem intMulNonNeg {leftFactor rightFactor : Int}
    (isLeftNonNegative : (0 : Int) ≤ leftFactor)
    (isRightNonNegative : (0 : Int) ≤ rightFactor) :
    (0 : Int) ≤ leftFactor * rightFactor :=
  match intZeroLeDest isLeftNonNegative, intZeroLeDest isRightNonNegative with
  | ⟨leftWitness, leftEquation⟩, ⟨rightWitness, rightEquation⟩ =>
      intLessEqualOfEqRight (intZeroLeOfNat (leftWitness * rightWitness))
        ((congrArg (· * Int.ofNat rightWitness) leftEquation.symm).trans
          (congrArg (leftFactor * ·) rightEquation.symm))

/-- Products of positives are positive (Init's `Int.mul_pos` is propext-dirty).  Both
factors destruct to explicit successors `ofNat (1 + witness)`; the product's own
`1 + _` shape is peeled by two `Nat.add_comm` shuffles (`x * (n + 1)` and `x + (m + 1)`
are definitional). -/
theorem intMulPos {leftFactor rightFactor : Int}
    (isLeftPositive : (0 : Int) < leftFactor) (isRightPositive : (0 : Int) < rightFactor) :
    (0 : Int) < leftFactor * rightFactor :=
  match intLessEqualDest (show (0 : Int) + 1 ≤ leftFactor from isLeftPositive),
        intLessEqualDest (show (0 : Int) + 1 ≤ rightFactor from isRightPositive) with
  | ⟨leftWitness, leftEquation⟩, ⟨rightWitness, rightEquation⟩ =>
      let leftCarrier : leftFactor = Int.ofNat (1 + leftWitness) := leftEquation
      let rightCarrier : rightFactor = Int.ofNat (1 + rightWitness) := rightEquation
      let productAsSucc : (1 + leftWitness) * (1 + rightWitness) =
          1 + ((1 + leftWitness) * rightWitness + leftWitness) :=
        (congrArg ((1 + leftWitness) * ·) (Nat.add_comm 1 rightWitness)).trans
          ((congrArg ((1 + leftWitness) * rightWitness + ·)
              (Nat.add_comm 1 leftWitness)).trans
            (Nat.add_comm ((1 + leftWitness) * rightWitness + leftWitness) 1))
      show (0 : Int) + 1 ≤ leftFactor * rightFactor from
        intLessEqualOfEqRight
          (intLessEqualIntro ((0 : Int) + 1)
            ((1 + leftWitness) * rightWitness + leftWitness))
          ((congrArg Int.ofNat productAsSucc.symm).trans
            ((congrArg (· * Int.ofNat (1 + rightWitness)) leftCarrier.symm).trans
              (congrArg (leftFactor * ·) rightCarrier.symm)))

end FX1Poly.ComputerAlgebra
