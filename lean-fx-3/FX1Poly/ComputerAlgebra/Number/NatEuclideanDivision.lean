/-! # FX1Poly/ComputerAlgebra/Number/NatEuclideanDivision — the structural counting divider
    (FLOAT-1 brick 9)

Init's `Nat.div` is WellFounded-based and its correctness corpus (`Nat.div_add_mod`,
`Int.ediv_add_emod`) is propext-dirty (probed 2026-07-02), so the rounding-certificate
layer cannot use it.  This module rebuilds Euclidean division ZERO-AXIOM by the COUNTING
recursion: instead of repeated subtraction (which needs well-founded recursion), walk the
dividend up one unit at a time, bumping the quotient whenever the remainder is about to
reach the divisor.  Structural on the dividend — O(dividend) as a program, which is
irrelevant here: this layer is CERTIFICATE-FIRST, and the certificate checker is just
multiplication + addition + comparison.

  * `natDivModStep` — one counting step, written with `cond` so the Bool scrutinee is
    exposed for `congrArg` transport (no match-motive surgery).
  * `natDivModCountingReconstructs` — `dividend = divisor * quotient + remainder`, with
    NO positivity hypothesis (at divisor `0` the counter degenerates to `(0, dividend)`,
    which still reconstructs).
  * `natDivModCountingRemainderIsBounded` — `remainder < divisor` for positive divisors.
  * `natLtOfLeOfNe` — the strictness upgrade (Init's `Nat.lt_of_le_of_ne` route is
    simp-based); one `Nat.le.dest` witness split.
  * `natEuclideanDivisionExists` — the packaged existence certificate.

## Zero-axiom

Structural recursion on the dividend, `cond`-transport by `congrArg` over
`Nat.eq_of_beq_eq_true` / `Nat.ne_of_beq_eq_false` (both clean), witness arithmetic over
`Nat.le.dest` / `Nat.le.intro` / `Nat.succ_add`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/Number/NatEuclideanDivision.lean`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The counter -/

/-- One counting step: consume one unit of dividend.  When the incremented remainder
reaches the divisor, roll it into the quotient.  Written with `cond` so the Bool
scrutinee stays exposed for `congrArg` transport in the correctness proofs. -/
def natDivModStep (divisor quotient remainder : Nat) : Nat × Nat :=
  cond ((remainder + 1).beq divisor) (quotient + 1, 0) (quotient, remainder + 1)

/-- Euclidean division by counting — structural on the dividend (no well-founded
recursion, no fuel).  Returns `(quotient, remainder)`. -/
def natDivModCounting : Nat → Nat → Nat × Nat
  | 0, _ => (0, 0)
  | dividend + 1, divisor =>
      natDivModStep divisor (natDivModCounting dividend divisor).fst
        (natDivModCounting dividend divisor).snd

/-! ## The strictness upgrade -/

/-- `≤` plus `≠` gives `<` — one witness split: a zero difference contradicts the
disequality, a successor difference re-associates into the strict witness. -/
theorem natLtOfLeOfNe {lowValue highValue : Nat} (isLessEqual : lowValue ≤ highValue)
    (isNotEqual : lowValue ≠ highValue) : lowValue < highValue :=
  match Nat.le.dest isLessEqual with
  | ⟨0, differenceEquation⟩ => absurd differenceEquation isNotEqual
  | ⟨difference + 1, differenceEquation⟩ =>
      Nat.le.intro ((Nat.succ_add lowValue difference).trans differenceEquation)

/-! ## Step correctness -/

/-- One step adds exactly one unit to the reconstruction `divisor * quotient +
remainder`.  Both `cond` arms are transported by `congrArg` over the Bool equation; the
roll-over arm converts the bumped quotient back through `remainder + 1 = divisor`. -/
theorem natDivModStepReconstructs (divisor quotient remainder : Nat) :
    divisor * (natDivModStep divisor quotient remainder).fst +
      (natDivModStep divisor quotient remainder).snd =
      divisor * quotient + (remainder + 1) :=
  match beqEquation : (remainder + 1).beq divisor with
  | true =>
      let stepEquation : natDivModStep divisor quotient remainder = (quotient + 1, 0) :=
        congrArg
          (fun conditionBool => cond conditionBool (quotient + 1, 0) (quotient, remainder + 1))
          beqEquation
      (congrArg (fun stepPair => divisor * stepPair.fst + stepPair.snd) stepEquation).trans
        (congrArg (divisor * quotient + ·) (Nat.eq_of_beq_eq_true beqEquation).symm)
  | false =>
      let stepEquation :
          natDivModStep divisor quotient remainder = (quotient, remainder + 1) :=
        congrArg
          (fun conditionBool => cond conditionBool (quotient + 1, 0) (quotient, remainder + 1))
          beqEquation
      congrArg (fun stepPair => divisor * stepPair.fst + stepPair.snd) stepEquation

/-- One step keeps the remainder below a positive divisor: the roll-over arm resets to
`0`, the counting arm stays strict because the Bool said the bound was not yet hit. -/
theorem natDivModStepRemainderIsBounded (divisor quotient remainder : Nat)
    (isPositive : 0 < divisor) (isBounded : remainder < divisor) :
    (natDivModStep divisor quotient remainder).snd < divisor :=
  match beqEquation : (remainder + 1).beq divisor with
  | true =>
      let sndEquation : (natDivModStep divisor quotient remainder).snd = 0 :=
        congrArg Prod.snd
          (congrArg
            (fun conditionBool =>
              cond conditionBool (quotient + 1, 0) (quotient, remainder + 1))
            beqEquation)
      sndEquation.symm ▸ isPositive
  | false =>
      let sndEquation :
          (natDivModStep divisor quotient remainder).snd = remainder + 1 :=
        congrArg Prod.snd
          (congrArg
            (fun conditionBool =>
              cond conditionBool (quotient + 1, 0) (quotient, remainder + 1))
            beqEquation)
      sndEquation.symm ▸ natLtOfLeOfNe isBounded (Nat.ne_of_beq_eq_false beqEquation)

/-! ## Divider correctness -/

/-- **Reconstruction**: `dividend = divisor * quotient + remainder` — no positivity
hypothesis (a zero divisor degenerates to `(0, dividend)`, which still reconstructs). -/
theorem natDivModCountingReconstructs : ∀ dividend divisor : Nat,
    dividend = divisor * (natDivModCounting dividend divisor).fst +
      (natDivModCounting dividend divisor).snd
  | 0, _ => rfl
  | dividend + 1, divisor =>
      (congrArg (· + 1) (natDivModCountingReconstructs dividend divisor)).trans
        (natDivModStepReconstructs divisor (natDivModCounting dividend divisor).fst
          (natDivModCounting dividend divisor).snd).symm

/-- **Remainder bound**: the remainder stays below a positive divisor. -/
theorem natDivModCountingRemainderIsBounded : ∀ dividend divisor : Nat, 0 < divisor →
    (natDivModCounting dividend divisor).snd < divisor
  | 0, _, isPositive => isPositive
  | dividend + 1, divisor, isPositive =>
      natDivModStepRemainderIsBounded divisor (natDivModCounting dividend divisor).fst
        (natDivModCounting dividend divisor).snd isPositive
        (natDivModCountingRemainderIsBounded dividend divisor isPositive)

/-- The packaged Euclidean-division existence certificate (Init's `Nat.div_add_mod` is
propext-dirty; this is its zero-axiom replacement). -/
theorem natEuclideanDivisionExists (dividend divisor : Nat) (isPositive : 0 < divisor) :
    ∃ quotient remainder : Nat,
      dividend = divisor * quotient + remainder ∧ remainder < divisor :=
  ⟨(natDivModCounting dividend divisor).fst, (natDivModCounting dividend divisor).snd,
    natDivModCountingReconstructs dividend divisor,
    natDivModCountingRemainderIsBounded dividend divisor isPositive⟩

/-! ## The order supplement — witness bookkeeping for the fuel bound

The normalization loop's termination bound needs three small `≤` facts (transitivity,
successor cancellation, the ≤-0 collapse) plus the shrink bound "an exact quotient by a
divisor ≥ 2 is strictly smaller than the dividend".  All are `Nat.le.dest`/`Nat.le.intro`
witness bookkeeping — no Init order corpus. -/

/-- Transitivity by witness addition (Init's `Nat.le_trans` is avoided on principle —
this is two destructs and one reassociation). -/
theorem natLeTrans {lowValue middleValue highValue : Nat}
    (isLowMiddle : lowValue ≤ middleValue) (isMiddleHigh : middleValue ≤ highValue) :
    lowValue ≤ highValue :=
  match Nat.le.dest isLowMiddle, Nat.le.dest isMiddleHigh with
  | ⟨firstWitness, firstEquation⟩, ⟨secondWitness, secondEquation⟩ =>
      Nat.le.intro
        ((Nat.add_assoc lowValue firstWitness secondWitness).symm.trans
          ((congrArg (· + secondWitness) firstEquation).trans secondEquation))

/-- Successor cancellation on `≤` — destruct, reshuffle the successor out through
`Nat.succ_add`, and constructor-inject. -/
theorem natLeOfSuccLeSucc {lowValue highValue : Nat}
    (isSuccLeSucc : lowValue + 1 ≤ highValue + 1) : lowValue ≤ highValue :=
  match Nat.le.dest isSuccLeSucc with
  | ⟨differenceWitness, witnessEquation⟩ =>
      Nat.le.intro
        (Nat.succ.inj
          ((Nat.succ_add lowValue differenceWitness).symm.trans witnessEquation))

/-- Nothing sits below zero — both `Nat.le` constructors are impossible at a successor
under index `0`. -/
theorem natEqZeroOfLeZero : ∀ {value : Nat}, value ≤ 0 → value = 0
  | 0, _ => rfl
  | _ + 1, isLeZero => nomatch isLeZero

/-- **The shrink bound**: an exact NONZERO quotient by a divisor ≥ 2 is strictly below
the dividend.  Destruct the divisor bound to `divisorExtra + 2`; then
`quotient * (divisorExtra + 2)` is DEFINITIONALLY
`quotient * divisorExtra + quotient + quotient`, and the strictness witness is one
additive shuffle away. -/
theorem natExactQuotientSuccBound {divisor dividend quotientPredecessor : Nat}
    (isDivisorAtLeastTwo : 2 ≤ divisor)
    (factorizes : dividend = divisor * (quotientPredecessor + 1)) :
    (quotientPredecessor + 1) + 1 ≤ dividend :=
  match Nat.le.dest isDivisorAtLeastTwo with
  | ⟨divisorExtra, divisorEquation⟩ =>
    let quotient := quotientPredecessor + 1
    have dividendExpands :
        dividend = quotient * divisorExtra + quotient + quotient :=
      factorizes.trans
        ((Nat.mul_comm divisor quotient).trans
          ((congrArg (quotient * ·) divisorEquation.symm).trans
            (congrArg (quotient * ·) (Nat.add_comm 2 divisorExtra))))
    Nat.le.intro
      ((Nat.add_comm (quotient + 1)
          (quotient * divisorExtra + quotientPredecessor)).trans
        ((congrArg (· + 1)
            ((Nat.add_assoc (quotient * divisorExtra) quotientPredecessor
                quotient).trans
              ((congrArg (quotient * divisorExtra + ·)
                  (Nat.add_comm quotientPredecessor quotient)).trans
                (Nat.add_assoc (quotient * divisorExtra) quotient
                  quotientPredecessor).symm))).trans
          dividendExpands.symm))

/-- **The fuel bound**: an exact quotient by a divisor ≥ 2 of a dividend within
`fuel + 1` fits within `fuel` — zero quotients trivially, successor quotients through
the shrink bound. -/
theorem natExactQuotientWithinFuel {divisor dividend fuel : Nat}
    (isDivisorAtLeastTwo : 2 ≤ divisor) (isWithinSuccFuel : dividend ≤ fuel + 1) :
    ∀ quotient : Nat, dividend = divisor * quotient → quotient ≤ fuel
  | 0, _ => Nat.le.intro (Nat.zero_add fuel)
  | quotientPredecessor + 1, factorizes =>
      natLeOfSuccLeSucc
        (natLeTrans
          (natExactQuotientSuccBound isDivisorAtLeastTwo factorizes)
          isWithinSuccFuel)

end FX1Poly.ComputerAlgebra
