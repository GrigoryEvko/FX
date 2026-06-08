import FX1Poly.Typed.TypedChurchNumeralAddition

/-! # FX1Poly/Typed/TypedChurchNumeralMultiplication
    — the term model computes MULTIPLICATION: `(ℕ, +, ×)` is faithfully modelled

`TypedChurchNumeralAddition` (#1029) showed the FX term model COMPUTES addition (the Church-addition
body `m A f (n A f x) ↝* f^(m+n) x`).  This file does the same for MULTIPLICATION, completing the
arithmetic: together with `CHURCH-NAT-FAITHFUL-GENERAL` (#1006, the numerals are distinct) and #1029,
the term model is a faithful model of the commutative semiring `(ℕ, +, ×)` — distinct numerals
(faithfulness) plus both operations reduce to the correct numeral (adequacy).

Church multiplication is `mult = λm.λn.λA.λf.λx. m A (n A f) x`: the body iterates the `n`-fold step
`(n A f)` a total of `m` times over `x`.  Since `(n A f)` is "apply `f` `n` times", iterating it `m`
times applies `f` a total of `m·n` times — the multiplicative identity `f^(m·n) x = (f^n)^m x`.  This
file mechanizes exactly that body computation, for GENERAL `m`, `n` and a SYMBOLIC step `f` / base `x`:

  * `churchMultiplicationStepIterate` — the multiplicative induction: iterating the term `(n A f)`
    `countOuter` times over a base reduces to `f^(countOuter · n)` over that base.  Structural
    induction on `countOuter`; each successor peels one outer copy of `(n A f)`, reduces it by the
    shipped general iteration computation (#1009 — `(n A f)` applied to anything is `f^n` of it), and
    folds the new `n` applications onto the inductive `countOuter · n` via `iteratedApplication_add`
    (#1029) and `Nat.succ_mul` / `Nat.add_comm` (both propext-free).
  * **`churchMultiplicationBodyComputes` (★)** — the headline: the Church-multiplication body
    `m A (n A f) x ↝* f^(m·n) x`, for every `m`, `n` and any closed `A`, `f`, `x`.  Built from the
    shipped general compute (the outer `m`-iterator over the step `(n A f)`) glued to
    `churchMultiplicationStepIterate`.
  * `churchTwoTimesThreeComputes` — the concrete smoke `2 × 3 = 6`: `2 A (3 A f) x ↝* f^6 x`.

## Honest scope boundary

As with addition (#1029), this computes the BODY of Church multiplication (`m A (n A f) x`) — the entire
arithmetic content (the reason `mult` is correct).  It does not separately β-reduce the five
administrative redexes of the standalone combinator `mult = λm.λn.λA.λf.λx. …` applied to its arguments
(closed-term substitution bookkeeping, no arithmetic).  The body computation here, parametric in
`m`/`n`, is the faithful statement that Church multiplication computes `m · n`.

## Zero-axiom verification

`churchMultiplicationStepIterate` is structural induction reusing `Step.appArgCong` (the argument
congruence), the shipped general compute, `iteratedApplication_add`, `StepStar.congAt`,
`StepStar.trans_compose`, and `Nat.zero_mul` / `Nat.succ_mul` / `Nat.add_comm` (all propext-free); the
headline and smoke thread those.  No `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, or
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core StepStar

/-- **The multiplicative induction.**  Iterating the `n`-fold step term `(n A f)` over a base
`countOuter` times reduces to `f` applied `countOuter · n` times over that base:
`iteratedApplication countOuter (n A f) x ↝* iteratedApplication (countOuter · n) f x`.

Structural induction on `countOuter`.  The successor case peels one outer `(n A f)` (the iterate's
definitional unfolding), lifts the inductive hypothesis into its argument position
(`StepStar.congAt` + `Step.appArgCong`), reduces that outer `(n A f) (f^(m·n) x)` by the shipped
general iteration computation (#1009) to `f^n (f^(m·n) x)`, and folds the counts via
`iteratedApplication_add` (#1029) with `Nat.succ_mul` / `Nat.add_comm` aligning `n + m·n = (m+1)·n`. -/
theorem churchMultiplicationStepIterate (countOuter countInner : Nat)
    (typeA handlerF baseX : RawTerm 0) :
    StepStar
      (iteratedApplication countOuter
        (appCell (appCell (churchNumeralLambda countInner) typeA) handlerF) baseX)
      (iteratedApplication (countOuter * countInner) handlerF baseX) := by
  induction countOuter with
  | zero =>
      rw [Nat.zero_mul]
      exact StepStar.refl _
  | succ priorOuter priorIH =>
      have liftIH : StepStar
          (appCell (appCell (appCell (churchNumeralLambda countInner) typeA) handlerF)
            (iteratedApplication priorOuter
              (appCell (appCell (churchNumeralLambda countInner) typeA) handlerF) baseX))
          (appCell (appCell (appCell (churchNumeralLambda countInner) typeA) handlerF)
            (iteratedApplication (priorOuter * countInner) handlerF baseX)) :=
        StepStar.congAt
          (fun hole =>
            appCell (appCell (appCell (churchNumeralLambda countInner) typeA) handlerF) hole)
          (fun argStep => Step.appArgCong _ argStep)
          priorIH
      have applyN : StepStar
          (appCell (appCell (appCell (churchNumeralLambda countInner) typeA) handlerF)
            (iteratedApplication (priorOuter * countInner) handlerF baseX))
          (iteratedApplication countInner handlerF
            (iteratedApplication (priorOuter * countInner) handlerF baseX)) :=
        churchNumeral_appliedReducesToIterate_general countInner typeA handlerF
          (iteratedApplication (priorOuter * countInner) handlerF baseX)
      have combine : iteratedApplication countInner handlerF
            (iteratedApplication (priorOuter * countInner) handlerF baseX)
          = iteratedApplication ((priorOuter + 1) * countInner) handlerF baseX := by
        rw [← iteratedApplication_add countInner (priorOuter * countInner) handlerF baseX,
          Nat.succ_mul, Nat.add_comm countInner (priorOuter * countInner)]
      show StepStar
        (appCell (appCell (appCell (churchNumeralLambda countInner) typeA) handlerF)
          (iteratedApplication priorOuter
            (appCell (appCell (churchNumeralLambda countInner) typeA) handlerF) baseX)) _
      exact combine ▸ StepStar.trans_compose liftIH applyN

/-- ★ **The Church-multiplication body computes `f^(m·n) x`.**  For every `countLeft`, `countRight` and
any closed `typeA`, `handlerF`, `baseX`, the Church-multiplication body `m A (n A f) x` β-reduces to the
`(m·n)`-fold iterate of `f` over `x`:
`(churchNumeral m) A ((churchNumeral n) A f) x ↝* iteratedApplication (m·n) f x` (= `f^(m·n) x`).

The reason Church multiplication is correct: iterating the `n`-fold step `m` times applies `f` a total
of `m·n` times.  Proof: reduce the outer `m`-iterator over the step `(n A f)` to
`iteratedApplication m (n A f) x` (shipped general compute #1009), then collapse that to `f^(m·n) x`
by `churchMultiplicationStepIterate`. -/
theorem churchMultiplicationBodyComputes (countLeft countRight : Nat)
    (typeA handlerF baseX : RawTerm 0) :
    StepStar
      (appCell (appCell (appCell (churchNumeralLambda countLeft) typeA)
        (appCell (appCell (churchNumeralLambda countRight) typeA) handlerF)) baseX)
      (iteratedApplication (countLeft * countRight) handlerF baseX) := by
  have outerReduces : StepStar
      (appCell (appCell (appCell (churchNumeralLambda countLeft) typeA)
        (appCell (appCell (churchNumeralLambda countRight) typeA) handlerF)) baseX)
      (iteratedApplication countLeft
        (appCell (appCell (churchNumeralLambda countRight) typeA) handlerF) baseX) :=
    churchNumeral_appliedReducesToIterate_general countLeft typeA
      (appCell (appCell (churchNumeralLambda countRight) typeA) handlerF) baseX
  exact StepStar.trans_compose outerReduces
    (churchMultiplicationStepIterate countLeft countRight typeA handlerF baseX)

/-- **The concrete smoke `2 × 3 = 6`.**  `2 A (3 A f) x ↝* f^6 x` — Church multiplication computes the
correct numeral on a concrete instance, by instantiating `churchMultiplicationBodyComputes` at
`countLeft = 2`, `countRight = 3` (`2 * 3` reduces to `6`). -/
theorem churchTwoTimesThreeComputes (typeA handlerF baseX : RawTerm 0) :
    StepStar
      (appCell (appCell (appCell (churchNumeralLambda 2) typeA)
        (appCell (appCell (churchNumeralLambda 3) typeA) handlerF)) baseX)
      (iteratedApplication 6 handlerF baseX) :=
  churchMultiplicationBodyComputes 2 3 typeA handlerF baseX

end FX1Poly.Typed
