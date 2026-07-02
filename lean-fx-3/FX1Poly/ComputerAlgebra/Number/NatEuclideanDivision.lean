import FX1Poly.ComputerAlgebra.Number.IntMulAssociativity

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
  * `natEuclideanQuotientUnique` — quotient uniqueness of in-bound decompositions.
  * `natDivModCountingQuotientScales` — quotient invariance under common scaling of
    dividend and divisor (the cross-scale bridge rounding monotonicity rides).
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

/-- Division by `1` is the identity — every counting step rolls the remainder over,
so the quotient tracks the dividend exactly.  The degenerate divisor the rounding
modes hit when the target scale needs no division. -/
theorem natDivModCountingByOne : ∀ dividend : Nat,
    natDivModCounting dividend 1 = (dividend, 0)
  | 0 => rfl
  | dividend + 1 =>
      have stepTransported :
          natDivModStep 1 (natDivModCounting dividend 1).fst
              (natDivModCounting dividend 1).snd =
            natDivModStep 1 (dividend, 0).fst (dividend, 0).snd :=
        congrArg
          (fun divModPair => natDivModStep 1 divModPair.fst divModPair.snd)
          (natDivModCountingByOne dividend)
      stepTransported

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

/-! ## Quotient monotonicity — the rounding-monotonicity crux

The counting quotient never shrinks as the dividend grows (same divisor).  This is
what makes truncation monotone: a larger magnitude can only roll over MORE units into
the quotient. -/

/-- One step never shrinks the quotient — the roll-over arm bumps it by one, the
counting arm keeps it.  Both `cond` arms are transported by `congrArg` over the Bool
equation, the established scrutinee idiom. -/
theorem natDivModStepQuotientGrows (divisor quotient remainder : Nat) :
    quotient ≤ (natDivModStep divisor quotient remainder).fst :=
  match beqEquation : (remainder + 1).beq divisor with
  | true =>
      let fstEquation :
          (natDivModStep divisor quotient remainder).fst = quotient + 1 :=
        congrArg Prod.fst
          (congrArg
            (fun conditionBool =>
              cond conditionBool (quotient + 1, 0) (quotient, remainder + 1))
            beqEquation)
      fstEquation.symm ▸ Nat.le.step Nat.le.refl
  | false =>
      let fstEquation :
          (natDivModStep divisor quotient remainder).fst = quotient :=
        congrArg Prod.fst
          (congrArg
            (fun conditionBool =>
              cond conditionBool (quotient + 1, 0) (quotient, remainder + 1))
            beqEquation)
      fstEquation.symm ▸ Nat.le.refl

/-- **The counting quotient is monotone in the dividend** — structural on the `≤`
derivation: each extra dividend unit runs one more step, and a step never shrinks the
quotient. -/
theorem natDivModCountingQuotientIsMonotone (divisor : Nat) :
    ∀ {lowDividend highDividend : Nat}, lowDividend ≤ highDividend →
      (natDivModCounting lowDividend divisor).fst ≤
        (natDivModCounting highDividend divisor).fst
  | _, _, .refl => Nat.le.refl
  | _, .succ highPredecessor, .step remainingBound =>
      natLeTrans
        (natDivModCountingQuotientIsMonotone divisor remainingBound)
        (natDivModStepQuotientGrows divisor
          (natDivModCounting highPredecessor divisor).fst
          (natDivModCounting highPredecessor divisor).snd)

/-! ## The uniqueness supplement — totality, cancellation, scaled bounds

Euclidean UNIQUENESS (below) closes the scaling-invariance route the rounding-
monotonicity certificate needs.  Its proof bill is the usual hand-rolled kit: `≤`
totality, additive cancellation, right distributivity, and strict multiplicative
scaling — all `Nat.le.dest`/`Nat.le.intro` witness bookkeeping over the clean core
lemmas (`Nat.add_comm`/`Nat.add_assoc`/`Nat.mul_comm`/`Nat.left_distrib`/
`Nat.succ_mul`/`Nat.zero_mul`). -/

/-- Zero sits below everything — structural on the bound. -/
theorem natZeroLe : ∀ value : Nat, 0 ≤ value
  | 0 => Nat.le.refl
  | value + 1 => Nat.le.step (natZeroLe value)

/-- Successor congruence on `≤` — the witness survives, shuffled through
`Nat.succ_add`. -/
theorem natSuccLeSuccOfLe {lowValue highValue : Nat}
    (isLessEqual : lowValue ≤ highValue) : lowValue + 1 ≤ highValue + 1 :=
  match Nat.le.dest isLessEqual with
  | ⟨differenceWitness, differenceEquation⟩ =>
      Nat.le.intro
        ((Nat.succ_add lowValue differenceWitness).trans
          (congrArg (· + 1) differenceEquation))

/-- **Totality of `≤`** — double structural descent (Init's `Nat.le_total` is avoided
on principle with the rest of the order corpus). -/
theorem natLeTotal : ∀ leftValue rightValue : Nat,
    leftValue ≤ rightValue ∨ rightValue ≤ leftValue
  | 0, rightValue => .inl (natZeroLe rightValue)
  | leftValue + 1, 0 => .inr (natZeroLe (leftValue + 1))
  | leftValue + 1, rightValue + 1 =>
      match natLeTotal leftValue rightValue with
      | .inl isLeftBelow => .inl (natSuccLeSuccOfLe isLeftBelow)
      | .inr isRightBelow => .inr (natSuccLeSuccOfLe isRightBelow)

/-- Right-addend cancellation — structural on the shared addend (`Nat.add` recurses
on its right argument, so each layer strips one `succ` by injection). -/
theorem natAddRightCancel : ∀ {sharedAddend firstValue secondValue : Nat},
    firstValue + sharedAddend = secondValue + sharedAddend → firstValue = secondValue
  | 0, _, _, sumsAgree => sumsAgree
  | _ + 1, _, _, sumsAgree => natAddRightCancel (Nat.succ.inj sumsAgree)

/-- Left-addend cancellation — commute both sides onto the right-addend form. -/
theorem natAddLeftCancel {sharedAddend firstValue secondValue : Nat}
    (sumsAgree : sharedAddend + firstValue = sharedAddend + secondValue) :
    firstValue = secondValue :=
  natAddRightCancel
    ((Nat.add_comm firstValue sharedAddend).trans
      (sumsAgree.trans (Nat.add_comm sharedAddend secondValue)))

/-- A successor never bounds itself — the destructed witness forces `succ = 0`,
refuted by `noConfusion`. -/
theorem natSuccNeverLeSelf {value : Nat} (isSuccLeSelf : value + 1 ≤ value) : False :=
  match Nat.le.dest isSuccLeSelf with
  | ⟨differenceWitness, differenceEquation⟩ =>
      Nat.noConfusion
        ((Nat.add_comm 1 differenceWitness).symm.trans
          (natAddLeftCancel
            (show value + (1 + differenceWitness) = value + 0 from
              (Nat.add_assoc value 1 differenceWitness).symm.trans
                differenceEquation)))

/-- Right distributivity, hand-rolled (Init's `Nat.right_distrib` is propext-dirty):
commute onto `Nat.left_distrib` and commute each product back. -/
theorem natRightDistrib (leftAddend rightAddend factor : Nat) :
    (leftAddend + rightAddend) * factor =
      leftAddend * factor + rightAddend * factor :=
  (Nat.mul_comm (leftAddend + rightAddend) factor).trans
    ((Nat.left_distrib factor leftAddend rightAddend).trans
      ((congrArg (· + factor * rightAddend) (Nat.mul_comm factor leftAddend)).trans
        (congrArg (leftAddend * factor + ·) (Nat.mul_comm factor rightAddend))))

/-- Strict scaling: a strict bound survives multiplication by a POSITIVE factor — the
strict unit rides the factor's own positivity witness through one long reassociation
onto the scaled difference. -/
theorem natMulLtMulRight {lowValue highValue factor : Nat}
    (isStrict : lowValue < highValue) (isFactorPositive : 0 < factor) :
    lowValue * factor < highValue * factor :=
  match Nat.le.dest isStrict, Nat.le.dest isFactorPositive with
  | ⟨strictWitness, strictEquation⟩, ⟨factorWitness, factorEquation⟩ =>
      Nat.le.intro
        ((Nat.add_assoc (lowValue * factor) 1
            (factorWitness + strictWitness * factor)).trans
          ((congrArg (lowValue * factor + ·)
              (Nat.add_assoc 1 factorWitness (strictWitness * factor)).symm).trans
            ((congrArg
                (fun sumCarrier =>
                  lowValue * factor + (sumCarrier + strictWitness * factor))
                factorEquation).trans
              ((Nat.add_assoc (lowValue * factor) factor
                  (strictWitness * factor)).symm.trans
                ((congrArg (· + strictWitness * factor)
                    (Nat.succ_mul lowValue factor).symm).trans
                  ((natRightDistrib (lowValue + 1) strictWitness factor).symm.trans
                    (congrArg (· * factor) strictEquation)))))))

/-- A product of positives is positive — scale `0 < left` by the right factor and
patch `0 * right` down to `0` (`Nat.zero_mul` is clean). -/
theorem natMulPosOfPos {leftFactor rightFactor : Nat}
    (isLeftPositive : 0 < leftFactor) (isRightPositive : 0 < rightFactor) :
    0 < leftFactor * rightFactor :=
  match Nat.le.dest (natMulLtMulRight isLeftPositive isRightPositive) with
  | ⟨differenceWitness, differenceEquation⟩ =>
      Nat.le.intro
        ((congrArg (fun productCarrier => (productCarrier + 1) + differenceWitness)
            (Nat.zero_mul rightFactor).symm).trans
          differenceEquation)

/-! ## Euclidean uniqueness — the decomposition pins its quotient

Any two decompositions `divisor * quotient + remainder` of the same value with both
remainders below the divisor share their quotient.  This is what transports divider
facts ACROSS scales: the scaled base decomposition and the scaled divider run are
both Euclidean at divisor `divisor * scale`, so their quotients coincide. -/

/-- The ordered half: if the left quotient is at most the right, the decompositions
force them equal — a positive gap would park `divisor * gap + rightRemainder` inside
`leftRemainder`, overshooting its bound. -/
theorem natEuclideanQuotientEqOfLe
    {divisor leftQuotient leftRemainder rightQuotient rightRemainder : Nat}
    (isLeftBounded : leftRemainder < divisor)
    (decompositionsAgree :
      divisor * leftQuotient + leftRemainder =
        divisor * rightQuotient + rightRemainder)
    (isLeftAtMostRight : leftQuotient ≤ rightQuotient) :
    leftQuotient = rightQuotient :=
  match Nat.le.dest isLeftAtMostRight with
  | ⟨0, quotientEquation⟩ => quotientEquation
  | ⟨quotientGap + 1, quotientEquation⟩ =>
      let rightExpanded :
          divisor * rightQuotient + rightRemainder =
            divisor * leftQuotient +
              (divisor * (quotientGap + 1) + rightRemainder) :=
        (congrArg
            (fun quotientCarrier => divisor * quotientCarrier + rightRemainder)
            quotientEquation.symm).trans
          ((congrArg (· + rightRemainder)
              (Nat.left_distrib divisor leftQuotient (quotientGap + 1))).trans
            (Nat.add_assoc (divisor * leftQuotient)
              (divisor * (quotientGap + 1)) rightRemainder))
      let cancelledRemainder :
          leftRemainder = divisor * (quotientGap + 1) + rightRemainder :=
        natAddLeftCancel (decompositionsAgree.trans rightExpanded)
      let divisorIsBelowLeftRemainder : divisor ≤ leftRemainder :=
        Nat.le.intro
          (((Nat.add_assoc divisor (divisor * quotientGap)
                rightRemainder).symm.trans
              (congrArg (· + rightRemainder)
                (Nat.add_comm divisor (divisor * quotientGap)))).trans
            cancelledRemainder.symm)
      (natSuccNeverLeSelf
        (natLeTrans isLeftBounded divisorIsBelowLeftRemainder)).elim

/-- **Euclidean uniqueness**: decompositions with in-bound remainders share their
quotient — totality picks an ordered side and the ordered half closes both. -/
theorem natEuclideanQuotientUnique
    {divisor leftQuotient leftRemainder rightQuotient rightRemainder : Nat}
    (isLeftBounded : leftRemainder < divisor)
    (isRightBounded : rightRemainder < divisor)
    (decompositionsAgree :
      divisor * leftQuotient + leftRemainder =
        divisor * rightQuotient + rightRemainder) :
    leftQuotient = rightQuotient :=
  match natLeTotal leftQuotient rightQuotient with
  | .inl isLeftAtMostRight =>
      natEuclideanQuotientEqOfLe isLeftBounded decompositionsAgree
        isLeftAtMostRight
  | .inr isRightAtMostLeft =>
      (natEuclideanQuotientEqOfLe isRightBounded decompositionsAgree.symm
        isRightAtMostLeft).symm

/-! ## Scaling invariance — the cross-scale quotient bridge

Rounding monotonicity compares two operands pumped to DIFFERENT scales, so their
truncation divisors differ by a common factor.  Scaling invariance brings both onto
one divisor: the counting quotient of `dividend * scale` by `divisor * scale` IS the
counting quotient of `dividend` by `divisor` — by Euclidean uniqueness against the
scaled base decomposition. -/

/-- **Quotient scaling invariance** — scale the base reconstruction, regroup the
scaled divisor through `natMulAssoc`/`Nat.mul_comm`, and let Euclidean uniqueness
identify the quotients. -/
theorem natDivModCountingQuotientScales (dividend : Nat) {divisor scaleFactor : Nat}
    (isDivisorPositive : 0 < divisor) (isScalePositive : 0 < scaleFactor) :
    (natDivModCounting (dividend * scaleFactor) (divisor * scaleFactor)).fst =
      (natDivModCounting dividend divisor).fst :=
  let scaledDivisorRegrouped :
      divisor * (natDivModCounting dividend divisor).fst * scaleFactor =
        divisor * scaleFactor * (natDivModCounting dividend divisor).fst :=
    (natMulAssoc divisor (natDivModCounting dividend divisor).fst scaleFactor).trans
      ((congrArg (divisor * ·)
          (Nat.mul_comm (natDivModCounting dividend divisor).fst scaleFactor)).trans
        (natMulAssoc divisor scaleFactor
          (natDivModCounting dividend divisor).fst).symm)
  let scaledBaseDecomposition :
      dividend * scaleFactor =
        divisor * scaleFactor * (natDivModCounting dividend divisor).fst +
          (natDivModCounting dividend divisor).snd * scaleFactor :=
    (congrArg (· * scaleFactor)
        (natDivModCountingReconstructs dividend divisor)).trans
      ((natRightDistrib (divisor * (natDivModCounting dividend divisor).fst)
          (natDivModCounting dividend divisor).snd scaleFactor).trans
        (congrArg (· + (natDivModCounting dividend divisor).snd * scaleFactor)
          scaledDivisorRegrouped))
  natEuclideanQuotientUnique
    (natDivModCountingRemainderIsBounded (dividend * scaleFactor)
      (divisor * scaleFactor) (natMulPosOfPos isDivisorPositive isScalePositive))
    (natMulLtMulRight
      (natDivModCountingRemainderIsBounded dividend divisor isDivisorPositive)
      isScalePositive)
    ((natDivModCountingReconstructs (dividend * scaleFactor)
        (divisor * scaleFactor)).symm.trans
      scaledBaseDecomposition)

/-! ## Round-nearest-ties-even: the Nat layer (FLOAT-3e)

The nearest quotient corrects the counting divider's output by comparing the
DOUBLED remainder against the divisor (no division by two anywhere): keep the
quotient below the midpoint, bump above it, and break exact ties toward the even
quotient.  `Nat.blt`/`Nat.ble` are structural `Bool` programs (axiom-clean), so the
corrector computes by kernel reduction; the two bridges below convert its branch
flags back into order facts. -/

/-- Order-to-`Bool` bridge: `Nat.ble` answers `true` on every true `≤`. -/
theorem natBleEqTrueOfLe : ∀ {lowValue highValue : Nat},
    lowValue ≤ highValue → Nat.ble lowValue highValue = true
  | 0, _, _ => rfl
  | _ + 1, 0, isImpossible => nomatch isImpossible
  | lowValue + 1, highValue + 1, isLessEqual =>
      natBleEqTrueOfLe (lowValue := lowValue) (highValue := highValue)
        (Nat.le_of_succ_le_succ isLessEqual)

/-- `Bool`-to-order bridge: a false `Nat.blt` flips the comparison.  Total order
splits the candidates; a strictly-above witness (successor gap) would force the
flag `true`. -/
theorem natLeOfBltEqFalse {lowValue highValue : Nat}
    (isNotBelow : Nat.blt lowValue highValue = false) : highValue ≤ lowValue :=
  match natLeTotal highValue lowValue with
  | .inl isBelow => isBelow
  | .inr isAbove =>
      match Nat.le.dest isAbove with
      | ⟨0, gapEquation⟩ => gapEquation ▸ Nat.le.refl
      | ⟨gapPredecessor + 1, gapEquation⟩ =>
          Bool.noConfusion
            (isNotBelow.symm.trans
              (natBleEqTrueOfLe
                (Nat.le.intro
                  ((Nat.succ_add lowValue gapPredecessor).trans gapEquation))))

/-- Structural parity — two-step recursion, computes by kernel reduction. -/
def natIsEven : Nat → Bool
  | 0 => true
  | 1 => false
  | value + 2 => natIsEven value

/-- **The nearest-ties-even corrector** on a Euclidean decomposition
`dividend = divisor * quotient + remainder`: keep below the midpoint
(`2·remainder < divisor`), bump above it (`divisor < 2·remainder`), and at the
exact midpoint keep iff the quotient is even. -/
def natNearestCorrectedQuotient (divisor quotient remainder : Nat) : Nat :=
  cond (Nat.blt divisor (2 * remainder)) (quotient + 1)
    (cond (Nat.blt (2 * remainder) divisor) quotient
      (cond (natIsEven quotient) quotient (quotient + 1)))

/-- The corrector only ever keeps or bumps — the four-flag cond nest collapses to
a binary disjunction, one `congrArg` telescope per branch. -/
theorem natNearestCorrectedQuotientIsKeptOrBumped
    (divisor quotient remainder : Nat) :
    natNearestCorrectedQuotient divisor quotient remainder = quotient ∨
      natNearestCorrectedQuotient divisor quotient remainder = quotient + 1 :=
  match bumpEquation : Nat.blt divisor (2 * remainder) with
  | true =>
      .inr (congrArg
        (fun bumpFlag => cond bumpFlag (quotient + 1)
          (cond (Nat.blt (2 * remainder) divisor) quotient
            (cond (natIsEven quotient) quotient (quotient + 1))))
        bumpEquation)
  | false =>
      match keepEquation : Nat.blt (2 * remainder) divisor with
      | true =>
          .inl ((congrArg
            (fun bumpFlag => cond bumpFlag (quotient + 1)
              (cond (Nat.blt (2 * remainder) divisor) quotient
                (cond (natIsEven quotient) quotient (quotient + 1))))
            bumpEquation).trans
            (congrArg
              (fun keepFlag => cond keepFlag quotient
                (cond (natIsEven quotient) quotient (quotient + 1)))
              keepEquation))
      | false =>
          match parityEquation : natIsEven quotient with
          | true =>
              .inl ((congrArg
                (fun bumpFlag => cond bumpFlag (quotient + 1)
                  (cond (Nat.blt (2 * remainder) divisor) quotient
                    (cond (natIsEven quotient) quotient (quotient + 1))))
                bumpEquation).trans
                ((congrArg
                  (fun keepFlag => cond keepFlag quotient
                    (cond (natIsEven quotient) quotient (quotient + 1)))
                  keepEquation).trans
                  (congrArg
                    (fun parityFlag => cond parityFlag quotient (quotient + 1))
                    parityEquation)))
          | false =>
              .inr ((congrArg
                (fun bumpFlag => cond bumpFlag (quotient + 1)
                  (cond (Nat.blt (2 * remainder) divisor) quotient
                    (cond (natIsEven quotient) quotient (quotient + 1))))
                bumpEquation).trans
                ((congrArg
                  (fun keepFlag => cond keepFlag quotient
                    (cond (natIsEven quotient) quotient (quotient + 1)))
                  keepEquation).trans
                  (congrArg
                    (fun parityFlag => cond parityFlag quotient (quotient + 1))
                    parityEquation)))

/-- **Round-nearest-ties-even on magnitudes** — the corrector applied to the
counting divider's output. -/
def natNearestEvenQuotient (divisor dividend : Nat) : Nat :=
  natNearestCorrectedQuotient divisor (natDivModCounting dividend divisor).fst
    (natDivModCounting dividend divisor).snd

/-! ## The doubled half-ulp certificates (FLOAT-3e)

The defining property of the nearest quotient, stated WITHOUT division by two: the
doubled corrected multiple stays within one divisor of the doubled dividend, on both
sides.  Everything is `Nat.le.dest`/`Nat.le.intro` witness algebra over the
reconstruction `dividend = divisor * quotient + remainder`. -/

/-- Strict weakens to weak — shuffle the successor into the gap witness. -/
theorem natLeOfLt {lowValue highValue : Nat} (isLessThan : lowValue < highValue) :
    lowValue ≤ highValue :=
  match Nat.le.dest isLessThan with
  | ⟨gapWitness, gapEquation⟩ =>
      Nat.le.intro ((Nat.add_assoc lowValue 1 gapWitness).symm.trans gapEquation)

/-- Rewrite the left endpoint of a `≤` — witness-based, motive-free. -/
theorem natLeOfEqLeft {leftValue middleValue rightValue : Nat}
    (areEqual : leftValue = middleValue) (isLessEqual : middleValue ≤ rightValue) :
    leftValue ≤ rightValue :=
  match Nat.le.dest isLessEqual with
  | ⟨gapWitness, gapEquation⟩ =>
      Nat.le.intro ((congrArg (· + gapWitness) areEqual).trans gapEquation)

/-- Rewrite the right endpoint of a `≤` — witness-based, motive-free. -/
theorem natLeOfEqRight {leftValue middleValue rightValue : Nat}
    (isLessEqual : leftValue ≤ middleValue) (areEqual : middleValue = rightValue) :
    leftValue ≤ rightValue :=
  match Nat.le.dest isLessEqual with
  | ⟨gapWitness, gapEquation⟩ => Nat.le.intro (gapEquation.trans areEqual)

/-- Adding on the left preserves `≤`. -/
theorem natAddLeAddLeft {lowValue highValue : Nat}
    (isLessEqual : lowValue ≤ highValue) (leftAddend : Nat) :
    leftAddend + lowValue ≤ leftAddend + highValue :=
  match Nat.le.dest isLessEqual with
  | ⟨gapWitness, gapEquation⟩ =>
      Nat.le.intro ((Nat.add_assoc leftAddend lowValue gapWitness).trans
        (congrArg (leftAddend + ·) gapEquation))

/-- Adding on the right preserves `≤`. -/
theorem natAddLeAddRight {lowValue highValue : Nat}
    (isLessEqual : lowValue ≤ highValue) (rightAddend : Nat) :
    lowValue + rightAddend ≤ highValue + rightAddend :=
  match Nat.le.dest isLessEqual with
  | ⟨gapWitness, gapEquation⟩ =>
      Nat.le.intro ((Nat.add_assoc lowValue rightAddend gapWitness).trans
        ((congrArg (lowValue + ·) (Nat.add_comm rightAddend gapWitness)).trans
          ((Nat.add_assoc lowValue gapWitness rightAddend).symm.trans
            (congrArg (· + rightAddend) gapEquation))))

/-- Past the midpoint the corrector bumps. -/
theorem natNearestCorrectedQuotientAtBump {divisor quotient remainder : Nat}
    (isPastMidpoint : Nat.blt divisor (2 * remainder) = true) :
    natNearestCorrectedQuotient divisor quotient remainder = quotient + 1 :=
  congrArg
    (fun bumpFlag => cond bumpFlag (quotient + 1)
      (cond (Nat.blt (2 * remainder) divisor) quotient
        (cond (natIsEven quotient) quotient (quotient + 1))))
    isPastMidpoint

/-- Before the midpoint the corrector keeps. -/
theorem natNearestCorrectedQuotientAtKeep {divisor quotient remainder : Nat}
    (isNotPastMidpoint : Nat.blt divisor (2 * remainder) = false)
    (isBeforeMidpoint : Nat.blt (2 * remainder) divisor = true) :
    natNearestCorrectedQuotient divisor quotient remainder = quotient :=
  (congrArg
    (fun bumpFlag => cond bumpFlag (quotient + 1)
      (cond (Nat.blt (2 * remainder) divisor) quotient
        (cond (natIsEven quotient) quotient (quotient + 1))))
    isNotPastMidpoint).trans
    (congrArg
      (fun keepFlag => cond keepFlag quotient
        (cond (natIsEven quotient) quotient (quotient + 1)))
      isBeforeMidpoint)

/-- At the exact midpoint an even quotient keeps. -/
theorem natNearestCorrectedQuotientAtTieEven {divisor quotient remainder : Nat}
    (isNotPastMidpoint : Nat.blt divisor (2 * remainder) = false)
    (isNotBeforeMidpoint : Nat.blt (2 * remainder) divisor = false)
    (hasEvenQuotient : natIsEven quotient = true) :
    natNearestCorrectedQuotient divisor quotient remainder = quotient :=
  (congrArg
    (fun bumpFlag => cond bumpFlag (quotient + 1)
      (cond (Nat.blt (2 * remainder) divisor) quotient
        (cond (natIsEven quotient) quotient (quotient + 1))))
    isNotPastMidpoint).trans
    ((congrArg
      (fun keepFlag => cond keepFlag quotient
        (cond (natIsEven quotient) quotient (quotient + 1)))
      isNotBeforeMidpoint).trans
      (congrArg (fun parityFlag => cond parityFlag quotient (quotient + 1))
        hasEvenQuotient))

/-- At the exact midpoint an odd quotient bumps. -/
theorem natNearestCorrectedQuotientAtTieOdd {divisor quotient remainder : Nat}
    (isNotPastMidpoint : Nat.blt divisor (2 * remainder) = false)
    (isNotBeforeMidpoint : Nat.blt (2 * remainder) divisor = false)
    (hasOddQuotient : natIsEven quotient = false) :
    natNearestCorrectedQuotient divisor quotient remainder = quotient + 1 :=
  (congrArg
    (fun bumpFlag => cond bumpFlag (quotient + 1)
      (cond (Nat.blt (2 * remainder) divisor) quotient
        (cond (natIsEven quotient) quotient (quotient + 1))))
    isNotPastMidpoint).trans
    ((congrArg
      (fun keepFlag => cond keepFlag quotient
        (cond (natIsEven quotient) quotient (quotient + 1)))
      isNotBeforeMidpoint).trans
      (congrArg (fun parityFlag => cond parityFlag quotient (quotient + 1))
        hasOddQuotient))

/-- The KEPT multiple's doubled bound below — unconditional. -/
theorem natKeptQuotientMulTwiceIsBelow {divisor quotient remainder dividend : Nat}
    (reconstructionHolds : dividend = divisor * quotient + remainder) :
    2 * (divisor * quotient) ≤ 2 * dividend + divisor :=
  Nat.le.intro
    ((Nat.add_assoc (2 * (divisor * quotient)) (2 * remainder) divisor).symm.trans
      ((congrArg (· + divisor)
        (Nat.left_distrib 2 (divisor * quotient) remainder).symm).trans
        (congrArg (fun total => 2 * total + divisor) reconstructionHolds.symm)))

/-- The BUMPED multiple's doubled bound below — needs the midpoint at or past
(`divisor ≤ 2·remainder`). -/
theorem natBumpedQuotientMulTwiceIsBelow {divisor quotient remainder dividend : Nat}
    (isMidpointAtOrPast : divisor ≤ 2 * remainder)
    (reconstructionHolds : dividend = divisor * quotient + remainder) :
    2 * (divisor * (quotient + 1)) ≤ 2 * dividend + divisor :=
  have twoDividendSplits : 2 * dividend = 2 * (divisor * quotient) + 2 * remainder :=
    (congrArg (2 * ·) reconstructionHolds).trans
      (Nat.left_distrib 2 (divisor * quotient) remainder)
  have mulOneCollapses : divisor * 1 = divisor := Nat.zero_add divisor
  have bumpedProductSplits : divisor * (quotient + 1) = divisor * quotient + divisor :=
    (Nat.left_distrib divisor quotient 1).trans
      (congrArg (divisor * quotient + ·) mulOneCollapses)
  have twoBumpedSplits :
      2 * (divisor * (quotient + 1)) = 2 * (divisor * quotient) + 2 * divisor :=
    (congrArg (2 * ·) bumpedProductSplits).trans
      (Nat.left_distrib 2 (divisor * quotient) divisor)
  have twoDivisorSplits : 2 * divisor = divisor + divisor :=
    (Nat.mul_comm 2 divisor).trans (congrArg (· + divisor) mulOneCollapses)
  natLeOfEqLeft twoBumpedSplits
    (natLeOfEqRight
      (natAddLeAddLeft
        (natLeOfEqLeft twoDivisorSplits (natAddLeAddRight isMidpointAtOrPast divisor))
        (2 * (divisor * quotient)))
      ((Nat.add_assoc (2 * (divisor * quotient)) (2 * remainder) divisor).symm.trans
        (congrArg (· + divisor) twoDividendSplits.symm)))

/-- The KEPT multiple's doubled bound above — needs the midpoint at or before
(`2·remainder ≤ divisor`). -/
theorem natKeptQuotientMulTwiceIsAbove {divisor quotient remainder dividend : Nat}
    (isMidpointAtOrBefore : 2 * remainder ≤ divisor)
    (reconstructionHolds : dividend = divisor * quotient + remainder) :
    2 * dividend ≤ 2 * (divisor * quotient) + divisor :=
  have twoDividendSplits : 2 * dividend = 2 * (divisor * quotient) + 2 * remainder :=
    (congrArg (2 * ·) reconstructionHolds).trans
      (Nat.left_distrib 2 (divisor * quotient) remainder)
  match Nat.le.dest isMidpointAtOrBefore with
  | ⟨gapWitness, gapEquation⟩ =>
      Nat.le.intro
        ((congrArg (· + gapWitness) twoDividendSplits).trans
          ((Nat.add_assoc (2 * (divisor * quotient)) (2 * remainder) gapWitness).trans
            (congrArg (2 * (divisor * quotient) + ·) gapEquation)))

/-- The BUMPED multiple's doubled bound above — needs only the remainder bound. -/
theorem natBumpedQuotientMulTwiceIsAbove {divisor quotient remainder dividend : Nat}
    (isRemainderBounded : remainder < divisor)
    (reconstructionHolds : dividend = divisor * quotient + remainder) :
    2 * dividend ≤ 2 * (divisor * (quotient + 1)) + divisor :=
  have twoDividendSplits : 2 * dividend = 2 * (divisor * quotient) + 2 * remainder :=
    (congrArg (2 * ·) reconstructionHolds).trans
      (Nat.left_distrib 2 (divisor * quotient) remainder)
  have mulOneCollapses : divisor * 1 = divisor := Nat.zero_add divisor
  have bumpedProductSplits : divisor * (quotient + 1) = divisor * quotient + divisor :=
    (Nat.left_distrib divisor quotient 1).trans
      (congrArg (divisor * quotient + ·) mulOneCollapses)
  have twoBumpedSplits :
      2 * (divisor * (quotient + 1)) = 2 * (divisor * quotient) + 2 * divisor :=
    (congrArg (2 * ·) bumpedProductSplits).trans
      (Nat.left_distrib 2 (divisor * quotient) divisor)
  have twoDivisorSplits : 2 * divisor = divisor + divisor :=
    (Nat.mul_comm 2 divisor).trans (congrArg (· + divisor) mulOneCollapses)
  have remainderMulOneCollapses : remainder * 1 = remainder := Nat.zero_add remainder
  have twoRemainderSplits : 2 * remainder = remainder + remainder :=
    (Nat.mul_comm 2 remainder).trans
      (congrArg (· + remainder) remainderMulOneCollapses)
  have remainderLeDivisor : remainder ≤ divisor := natLeOfLt isRemainderBounded
  have twoRemainderLeTwoDivisor : 2 * remainder ≤ 2 * divisor :=
    natLeOfEqLeft twoRemainderSplits
      (natLeOfEqRight
        (natLeTrans (natAddLeAddRight remainderLeDivisor remainder)
          (natAddLeAddLeft remainderLeDivisor divisor))
        twoDivisorSplits.symm)
  natLeOfEqLeft twoDividendSplits
    (natLeTrans
      (natAddLeAddLeft twoRemainderLeTwoDivisor (2 * (divisor * quotient)))
      (natLeOfEqRight
        (Nat.le_add_right (2 * (divisor * quotient) + 2 * divisor) divisor)
        (congrArg (· + divisor) twoBumpedSplits.symm)))

/-- **The doubled half-ulp bound, below**: the corrected multiple never exceeds the
dividend by more than half a divisor — stated doubled.  Dispatch over the three
flags; each branch is its positional bound transported along the branch equation. -/
theorem natNearestCorrectedQuotientMulTwiceIsBelow
    {divisor quotient remainder dividend : Nat}
    (reconstructionHolds : dividend = divisor * quotient + remainder) :
    2 * (divisor * natNearestCorrectedQuotient divisor quotient remainder) ≤
      2 * dividend + divisor :=
  match bumpEquation : Nat.blt divisor (2 * remainder) with
  | true =>
      natLeOfEqLeft
        (congrArg (fun quotientValue => 2 * (divisor * quotientValue))
          (natNearestCorrectedQuotientAtBump bumpEquation))
        (natBumpedQuotientMulTwiceIsBelow
          (natLeOfLt (Nat.le_of_ble_eq_true bumpEquation)) reconstructionHolds)
  | false =>
      match keepEquation : Nat.blt (2 * remainder) divisor with
      | true =>
          natLeOfEqLeft
            (congrArg (fun quotientValue => 2 * (divisor * quotientValue))
              (natNearestCorrectedQuotientAtKeep bumpEquation keepEquation))
            (natKeptQuotientMulTwiceIsBelow reconstructionHolds)
      | false =>
          match parityEquation : natIsEven quotient with
          | true =>
              natLeOfEqLeft
                (congrArg (fun quotientValue => 2 * (divisor * quotientValue))
                  (natNearestCorrectedQuotientAtTieEven bumpEquation keepEquation
                    parityEquation))
                (natKeptQuotientMulTwiceIsBelow reconstructionHolds)
          | false =>
              natLeOfEqLeft
                (congrArg (fun quotientValue => 2 * (divisor * quotientValue))
                  (natNearestCorrectedQuotientAtTieOdd bumpEquation keepEquation
                    parityEquation))
                (natBumpedQuotientMulTwiceIsBelow
                  (natLeOfBltEqFalse keepEquation) reconstructionHolds)

/-- **The doubled half-ulp bound, above**: the dividend never exceeds the corrected
multiple by more than half a divisor — stated doubled. -/
theorem natNearestCorrectedQuotientMulTwiceIsAbove
    {divisor quotient remainder dividend : Nat}
    (isRemainderBounded : remainder < divisor)
    (reconstructionHolds : dividend = divisor * quotient + remainder) :
    2 * dividend ≤
      2 * (divisor * natNearestCorrectedQuotient divisor quotient remainder) +
        divisor :=
  match bumpEquation : Nat.blt divisor (2 * remainder) with
  | true =>
      natLeOfEqRight
        (natBumpedQuotientMulTwiceIsAbove isRemainderBounded reconstructionHolds)
        (congrArg (fun quotientValue => 2 * (divisor * quotientValue) + divisor)
          (natNearestCorrectedQuotientAtBump bumpEquation).symm)
  | false =>
      match keepEquation : Nat.blt (2 * remainder) divisor with
      | true =>
          natLeOfEqRight
            (natKeptQuotientMulTwiceIsAbove
              (natLeOfLt (Nat.le_of_ble_eq_true keepEquation)) reconstructionHolds)
            (congrArg (fun quotientValue => 2 * (divisor * quotientValue) + divisor)
              (natNearestCorrectedQuotientAtKeep bumpEquation keepEquation).symm)
      | false =>
          match parityEquation : natIsEven quotient with
          | true =>
              natLeOfEqRight
                (natKeptQuotientMulTwiceIsAbove
                  (natLeOfBltEqFalse bumpEquation) reconstructionHolds)
                (congrArg
                  (fun quotientValue => 2 * (divisor * quotientValue) + divisor)
                  (natNearestCorrectedQuotientAtTieEven bumpEquation keepEquation
                    parityEquation).symm)
          | false =>
              natLeOfEqRight
                (natBumpedQuotientMulTwiceIsAbove isRemainderBounded
                  reconstructionHolds)
                (congrArg
                  (fun quotientValue => 2 * (divisor * quotientValue) + divisor)
                  (natNearestCorrectedQuotientAtTieOdd bumpEquation keepEquation
                    parityEquation).symm)

/-- The doubled half-ulp bound below, at the counting divider's output — needs no
positivity (the kept branch is unconditional and the bump branch is flag-driven). -/
theorem natNearestEvenQuotientMulTwiceIsBelow (divisor dividend : Nat) :
    2 * (divisor * natNearestEvenQuotient divisor dividend) ≤
      2 * dividend + divisor :=
  natNearestCorrectedQuotientMulTwiceIsBelow
    (natDivModCountingReconstructs dividend divisor)

/-- The doubled half-ulp bound above, at the counting divider's output. -/
theorem natNearestEvenQuotientMulTwiceIsAbove {divisor : Nat}
    (isDivisorPositive : 0 < divisor) (dividend : Nat) :
    2 * dividend ≤
      2 * (divisor * natNearestEvenQuotient divisor dividend) + divisor :=
  natNearestCorrectedQuotientMulTwiceIsAbove
    (natDivModCountingRemainderIsBounded dividend divisor isDivisorPositive)
    (natDivModCountingReconstructs dividend divisor)

/-! ## Faithfulness support: the midpoint certificate

Faithful rounding — the nearest quotient IS the floor or the ceiling — needs one
refinement of the kept-or-bumped disjunction: a bump only ever fires AT OR PAST the
midpoint (`divisor ≤ 2 * remainder`), which for a positive divisor forces a nonzero
remainder, which is exactly when the bumped quotient coincides with the ceiling. -/

/-- A positive `Nat`'s equality test against zero computes to `false`. -/
theorem natBeqZeroEqFalseOfPos : ∀ {value : Nat}, 0 < value → Nat.beq value 0 = false
  | _ + 1, _ => rfl
  | 0, isPositive => nomatch isPositive

/-- Half of a positive double is positive. -/
theorem natPosOfDoublePos : ∀ {value : Nat}, 0 < 2 * value → 0 < value
  | valuePredecessor + 1, _ => natSuccLeSuccOfLe (natZeroLe valuePredecessor)
  | 0, isPositive => nomatch isPositive

/-- **Kept, or bumped with the midpoint certificate** — the faithfulness refinement
of the kept-or-bumped disjunction: the corrector keeps the quotient, or bumps it
carrying the witness that the remainder sits at or past the midpoint.  Same
three-flag dispatch; the bump branch weakens its strict flag, the tie branch reads
the certificate off the OTHER flag. -/
theorem natNearestCorrectedQuotientIsKeptOrBumpedWithMidpointCertificate
    (divisor quotient remainder : Nat) :
    natNearestCorrectedQuotient divisor quotient remainder = quotient ∨
      (natNearestCorrectedQuotient divisor quotient remainder = quotient + 1 ∧
        divisor ≤ 2 * remainder) :=
  match bumpEquation : Nat.blt divisor (2 * remainder) with
  | true =>
      .inr ⟨natNearestCorrectedQuotientAtBump bumpEquation,
        natLeOfLt (Nat.le_of_ble_eq_true bumpEquation)⟩
  | false =>
      match keepEquation : Nat.blt (2 * remainder) divisor with
      | true => .inl (natNearestCorrectedQuotientAtKeep bumpEquation keepEquation)
      | false =>
          match parityEquation : natIsEven quotient with
          | true =>
              .inl (natNearestCorrectedQuotientAtTieEven bumpEquation keepEquation
                parityEquation)
          | false =>
              .inr ⟨natNearestCorrectedQuotientAtTieOdd bumpEquation keepEquation
                parityEquation,
                natLeOfBltEqFalse keepEquation⟩

/-- The composed nearest quotient is the counting quotient or its successor — the
latter only with the midpoint certificate on the counting remainder. -/
theorem natNearestEvenQuotientIsKeptOrBumpedWithMidpointCertificate
    (divisor dividend : Nat) :
    natNearestEvenQuotient divisor dividend =
        (natDivModCounting dividend divisor).fst ∨
      (natNearestEvenQuotient divisor dividend =
          (natDivModCounting dividend divisor).fst + 1 ∧
        divisor ≤ 2 * (natDivModCounting dividend divisor).snd) :=
  natNearestCorrectedQuotientIsKeptOrBumpedWithMidpointCertificate divisor
    (natDivModCounting dividend divisor).fst
    (natDivModCounting dividend divisor).snd

end FX1Poly.ComputerAlgebra
