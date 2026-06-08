import FX1Poly.Typed.TypedChurchNumeralComputeGeneral

/-! # FX1Poly/Typed/TypedChurchNumeralAddition
    — the term model COMPUTES arithmetic: Church addition reduces correctly

The Church-numeral arc established that `ℕ` injects into the FX term model as the distinct numerals
`churchNumeralLambda n` (`CHURCH-NAT-FAITHFUL-GENERAL` #1006: `m ≠ n → churchNumeral m ≢ churchNumeral
n`), that each numeral is typed at the Church Nat type (#1007), and that each numeral applied to
`(A, f, x)` β-reduces to its iterate `f^n x` (`churchNumeral_appliedReducesToIterate_general` #1009).
What it never showed is that the term model COMPUTES with those numerals — that arithmetic operations
reduce to the right answer.  This file closes that gap for ADDITION.

Church addition is `plus = λm.λn.λA.λf.λx. m A f (n A f x)`: its body composes the two iterators, and the
computational content — the reason `plus` is CORRECT — is that composing an `m`-fold and an `n`-fold
iterator yields an `(m+n)`-fold iterator.  This file mechanizes exactly that body computation, for
GENERAL `m`, `n` and a SYMBOLIC step `f` / base `x`:

  * `iteratedApplication_add` — the arithmetic heart: `f^(m+n) x = f^m (f^n x)` (the iterate
    decomposes additively).  Pure structural induction on `m`.
  * `Step.appArgCong` — the argument-position single-step congruence for an application cell (steps the
    argument with the function fixed), the one congruence the body computation needs.
  * **`churchAdditionBodyComputes` (★)** — the headline: the Church-addition body
    `m A f (n A f x) ↝* f^(m+n) x`, for every `m`, `n` and any closed `A`, `f`, `x`.  Built from the
    shipped general iteration computation (#1009) applied TWICE — once to reduce the inner `n A f x` to
    `f^n x`, once to reduce the outer `m A f (·)` to `f^m (·)` — glued by `StepStar.congAt` (lift the
    inner reduction into the argument position) and closed by `iteratedApplication_add`.
  * `churchTwoPlusThreeComputes` — the concrete smoke `2 + 3 = 5`: `2 A f (3 A f x) ↝* f^5 x`.

Together with #1006 (`ℕ` injects faithfully) this gives both directions of "the term model IS a model
of `(ℕ, +)`": the numerals are distinct (faithfulness) AND addition computes the correct successor
(adequacy of the addition operation).

## Honest scope boundary

This computes the BODY of Church addition (`m A f (n A f x)`), which is the entire computational content
— the reason `plus` is correct.  It does not separately β-reduce the five administrative redexes of the
standalone combinator `plus = λm.λn.λA.λf.λx. …` applied to its arguments (those substitutions of closed
terms for the five binders add no arithmetic content, only de Bruijn bookkeeping of the kind already
exercised by the symbolic S-rule #1024).  The body computation here, parametric in `m`/`n`, is the
faithful statement that Church addition computes `m + n`.

## Zero-axiom verification

`iteratedApplication_add` is structural induction with `Nat.zero_add` / `Nat.succ_add` (both
propext-free) and the iterate's definitional unfolding; `Step.appArgCong` is one `Step.cong` over the
`gen_app` children; the headline threads the shipped general-compute, `StepStar.congAt`,
`StepStar.trans_compose`, and the arithmetic lemma.  No `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core StepStar

/-- **The arithmetic heart of Church addition.**  The iterate decomposes additively:
`f^(m+n) x = f^m (f^n x)` — applying `f` a total of `m + n` times is applying it `m` times to the
result of applying it `n` times.  Structural induction on `countLeft`; the iterate's successor
equation `iteratedApplication (k+1) f base = appCell f (iteratedApplication k f base)` is definitional,
and `Nat.zero_add` / `Nat.succ_add` align the index. -/
theorem iteratedApplication_add {scope : Nat} (countLeft countRight : Nat)
    (stepFn base : RawTerm scope) :
    iteratedApplication (countLeft + countRight) stepFn base
      = iteratedApplication countLeft stepFn (iteratedApplication countRight stepFn base) := by
  induction countLeft with
  | zero =>
      show iteratedApplication (0 + countRight) stepFn base = iteratedApplication countRight stepFn base
      rw [Nat.zero_add]
  | succ priorLeft priorIH =>
      rw [Nat.succ_add]
      show appCell stepFn (iteratedApplication (priorLeft + countRight) stepFn base)
        = appCell stepFn (iteratedApplication priorLeft stepFn (iteratedApplication countRight stepFn base))
      rw [priorIH]

/-- **The argument-position single-step congruence for an application cell.**  When the argument of
`appCell func arg` reduces, the whole application reduces (the function fixed).  Reaches past the head
child via `StepChildren.there func (StepChildren.here …)`.  The one congruence the Church-addition body
computation needs (to reduce the inner numeral application sitting in the outer numeral's argument
position). -/
theorem Step.appArgCong {scope : Nat} (func : RawTerm scope) {arg arg' : RawTerm scope}
    (argStep : Step arg arg') : Step (appCell func arg) (appCell func arg') :=
  Step.cong .gen_app ()
    (StepChildren.there (parentScope := scope) (headShift := 0) func
      (StepChildren.here (parentScope := scope) (headShift := 0) (restShifts := []) .childNil argStep))

/-- ★ **The Church-addition body computes `f^(m+n) x`.**  For every `countLeft`, `countRight` and any
closed `typeA`, `handlerF`, `baseX`, the Church-addition body `m A f (n A f x)` β-reduces to the
`(m+n)`-fold iterate of `f` over `x`:
`(churchNumeral m) A f ((churchNumeral n) A f x) ↝* iteratedApplication (m+n) f x` (= `f^(m+n) x`).

The reason Church addition is correct: composing the two polymorphic iterators adds their counts.
Proof: reduce the inner `(churchNumeral n) A f x ↝* f^n x` (shipped general compute #1009), lift that
into the argument position of the outer application (`StepStar.congAt` + `Step.appArgCong`), reduce the
outer `(churchNumeral m) A f (f^n x) ↝* f^m (f^n x)` (general compute again, base `= f^n x`), and close
by `iteratedApplication_add`. -/
theorem churchAdditionBodyComputes (countLeft countRight : Nat) (typeA handlerF baseX : RawTerm 0) :
    StepStar
      (appCell (appCell (appCell (churchNumeralLambda countLeft) typeA) handlerF)
        (appCell (appCell (appCell (churchNumeralLambda countRight) typeA) handlerF) baseX))
      (iteratedApplication (countLeft + countRight) handlerF baseX) := by
  have innerReduces : StepStar
      (appCell (appCell (appCell (churchNumeralLambda countRight) typeA) handlerF) baseX)
      (iteratedApplication countRight handlerF baseX) :=
    churchNumeral_appliedReducesToIterate_general countRight typeA handlerF baseX
  have liftedInner : StepStar
      (appCell (appCell (appCell (churchNumeralLambda countLeft) typeA) handlerF)
        (appCell (appCell (appCell (churchNumeralLambda countRight) typeA) handlerF) baseX))
      (appCell (appCell (appCell (churchNumeralLambda countLeft) typeA) handlerF)
        (iteratedApplication countRight handlerF baseX)) :=
    StepStar.congAt
      (fun hole => appCell (appCell (appCell (churchNumeralLambda countLeft) typeA) handlerF) hole)
      (fun argStep => Step.appArgCong _ argStep)
      innerReduces
  have outerReduces : StepStar
      (appCell (appCell (appCell (churchNumeralLambda countLeft) typeA) handlerF)
        (iteratedApplication countRight handlerF baseX))
      (iteratedApplication countLeft handlerF (iteratedApplication countRight handlerF baseX)) :=
    churchNumeral_appliedReducesToIterate_general countLeft typeA handlerF
      (iteratedApplication countRight handlerF baseX)
  have combine : iteratedApplication countLeft handlerF (iteratedApplication countRight handlerF baseX)
      = iteratedApplication (countLeft + countRight) handlerF baseX :=
    (iteratedApplication_add countLeft countRight handlerF baseX).symm
  exact combine ▸ StepStar.trans_compose liftedInner outerReduces

/-- **The concrete smoke `2 + 3 = 5`.**  `2 A f (3 A f x) ↝* f^5 x` — Church addition computes the
correct numeral on a concrete instance, by instantiating `churchAdditionBodyComputes` at
`countLeft = 2`, `countRight = 3` (`2 + 3` reduces to `5`). -/
theorem churchTwoPlusThreeComputes (typeA handlerF baseX : RawTerm 0) :
    StepStar
      (appCell (appCell (appCell (churchNumeralLambda 2) typeA) handlerF)
        (appCell (appCell (appCell (churchNumeralLambda 3) typeA) handlerF) baseX))
      (iteratedApplication 5 handlerF baseX) :=
  churchAdditionBodyComputes 2 3 typeA handlerF baseX

end FX1Poly.Typed
