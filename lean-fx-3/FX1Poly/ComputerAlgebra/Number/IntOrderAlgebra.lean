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

/-! ## The strict-order kit (NUM-Q-6d)

Every `<` fact rides the DEFINITIONAL `a < b ≡ a + 1 ≤ b` pin: endpoint rewrites
shift the `+ 1` by one `congrArg`, strict addition-monotonicity re-parenthesizes
the weak one, and the mixed transitivities thread the successor through
`intLessEqualTrans`. -/

/-- Rewrite the left endpoint of a `<` — the `+ 1` rides the equality. -/
theorem intLessThanOfEqLeft {leftValue middleValue rightValue : Int}
    (areEqual : leftValue = middleValue) (isLessThan : middleValue < rightValue) :
    leftValue < rightValue :=
  show leftValue + 1 ≤ rightValue from
    intLessEqualOfEqLeft (congrArg (· + 1) areEqual)
      (show middleValue + 1 ≤ rightValue from isLessThan)

/-- Rewrite the right endpoint of a `<`. -/
theorem intLessThanOfEqRight {leftValue middleValue rightValue : Int}
    (isLessThan : leftValue < middleValue) (areEqual : middleValue = rightValue) :
    leftValue < rightValue :=
  show leftValue + 1 ≤ rightValue from
    intLessEqualOfEqRight (show leftValue + 1 ≤ middleValue from isLessThan) areEqual

/-- Every value sits strictly below its successor — reflexivity through the pin. -/
theorem intLessThanAddOne (value : Int) : value < value + 1 :=
  intLessEqualRefl (value + 1)

/-- Weak-then-strict transitivity — shift the weak bound by one on both sides. -/
theorem intLessThanOfLessEqualOfLessThan {lowValue middleValue highValue : Int}
    (isLessEqual : lowValue ≤ middleValue) (isLessThan : middleValue < highValue) :
    lowValue < highValue :=
  show lowValue + 1 ≤ highValue from
    intLessEqualTrans (intAddLeAddRight isLessEqual 1)
      (show middleValue + 1 ≤ highValue from isLessThan)

/-- Strict-then-weak transitivity — the successor is already on the left. -/
theorem intLessThanOfLessThanOfLessEqual {lowValue middleValue highValue : Int}
    (isLessThan : lowValue < middleValue) (isLessEqual : middleValue ≤ highValue) :
    lowValue < highValue :=
  show lowValue + 1 ≤ highValue from
    intLessEqualTrans (show lowValue + 1 ≤ middleValue from isLessThan) isLessEqual

/-- Adding on the left preserves `<` — the weak law plus one associativity step to
re-seat the `+ 1`. -/
theorem intAddLessThanAddLeft {lowValue highValue : Int}
    (isLessThan : lowValue < highValue) (leftAddend : Int) :
    leftAddend + lowValue < leftAddend + highValue :=
  show leftAddend + lowValue + 1 ≤ leftAddend + highValue from
    intLessEqualOfEqLeft (intAddAssoc leftAddend lowValue 1)
      (intAddLeAddLeft (show lowValue + 1 ≤ highValue from isLessThan) leftAddend)

/-- Adding on the right preserves `<` — corollary through `intAddComm`. -/
theorem intAddLessThanAddRight {lowValue highValue : Int}
    (isLessThan : lowValue < highValue) (rightAddend : Int) :
    lowValue + rightAddend < highValue + rightAddend :=
  intLessThanOfEqLeft (intAddComm lowValue rightAddend)
    (intLessThanOfEqRight (intAddLessThanAddLeft isLessThan rightAddend)
      (intAddComm rightAddend highValue))

/-- **Irreflexivity of `<`** — destruct the witness of `value + 1 ≤ value`:
left-cancelling `value` forces `0 = gap + 1`, a constructor disagreement. -/
theorem intLessThanIrrefl (value : Int) : Not (value < value) :=
  fun isBelowSelf =>
    match intLessEqualDest (show value + 1 ≤ value from isBelowSelf) with
    | ⟨gapWitness, gapEquation⟩ =>
        Nat.noConfusion (Int.ofNat.inj (intAddLeftCancel
          (((intAddZero value).trans gapEquation).trans
            ((intAddAssoc value 1 (Int.ofNat gapWitness)).trans
              (congrArg (value + ·)
                (intAddComm 1 (Int.ofNat gapWitness)))))))

/-- A refuted weak bound flips to a strict bound the other way — totality
gives the reverse weak bound, and the equal case re-derives the refuted one. -/
theorem intLessThanOfNotLessEqual {leftValue rightValue : Int}
    (isNotLessEqual : Not (leftValue ≤ rightValue)) : rightValue < leftValue :=
  match intLessEqualTotal leftValue rightValue with
  | .inl isLessEqual => absurd isLessEqual isNotLessEqual
  | .inr isReverse =>
      match intLtOrEqOfLe isReverse with
      | .inl isStrict => isStrict
      | .inr areEqual =>
          absurd
            (intLessEqualOfEqLeft areEqual.symm (intLessEqualRefl rightValue))
            isNotLessEqual

/-- Cancel a shared LEFT addend in a `≤` — re-associate the witness equation
and cancel the shared addend in the resulting equality. -/
theorem intAddLeftCancelLessEqual {sharedAddend lowValue highValue : Int}
    (isLessEqual : sharedAddend + lowValue ≤ sharedAddend + highValue) :
    lowValue ≤ highValue :=
  match intLessEqualDest isLessEqual with
  | ⟨gapWitness, gapEquation⟩ =>
      intLessEqualOfEqRight (intLessEqualIntro lowValue gapWitness)
        (intAddLeftCancel
          (gapEquation.trans
            (intAddAssoc sharedAddend lowValue (Int.ofNat gapWitness)))).symm

/-- Every value sits weakly below its magnitude read back as an `ofNat` —
nonnegatives ARE their magnitude; negatives sit below every `ofNat`. -/
theorem intSelfLessEqualOfNatNatAbs : ∀ value : Int, value ≤ Int.ofNat value.natAbs
  | .ofNat naturalPart => intLessEqualRefl (Int.ofNat naturalPart)
  | .negSucc magnitudePredecessor =>
      intNegSuccLeOfNat magnitudePredecessor (magnitudePredecessor + 1)

/-- Every value sits STRICTLY below its magnitude's successor — the integer-side
heart of the Archimedean property. -/
theorem intLessThanOfNatNatAbsSucc (value : Int) :
    value < Int.ofNat (value.natAbs + 1) :=
  intLessThanOfLessEqualOfLessThan (intSelfLessEqualOfNatNatAbs value)
    (intLessThanAddOne (Int.ofNat value.natAbs))

/-- The mirrored magnitude bound: the NEGATION also sits weakly below the
magnitude read back as an `ofNat` — together with
`intSelfLessEqualOfNatNatAbs` this is the two-sided `|value| ≤ natAbs value`
without an absolute value.  All three arms are definitional up to the shipped
`negSucc`-below-`ofNat` builder. -/
theorem intNegSelfLessEqualOfNatNatAbs :
    ∀ value : Int, -value ≤ Int.ofNat value.natAbs
  | .ofNat 0 => intLessEqualRefl (Int.ofNat 0)
  | .ofNat (naturalPredecessor + 1) =>
      intNegSuccLeOfNat naturalPredecessor (naturalPredecessor + 1)
  | .negSucc magnitudePredecessor =>
      intLessEqualRefl (Int.ofNat (magnitudePredecessor + 1))

end FX1Poly.ComputerAlgebra
