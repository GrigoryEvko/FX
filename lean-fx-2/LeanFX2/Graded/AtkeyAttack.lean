import LeanFX2.Graded.Instances.Usage

/-! # Graded/AtkeyAttack — verified rejection of Atkey 2018's broken Lam rule

Closes kernel-sprint D5.5.  Witnesses why FX adopts the Wood/Atkey
2022 corrected Lam rule with explicit context division.

## The attack term

Atkey 2018's original Lam rule (without context division) admits:

```
fn higher_order(f: i64 -> i64) : i64 -> i64 = fn(x) => f (f x)
```

Here `f` is declared linear (own/grade 1).  The outer function
captures `f` in an inner `fn(x) => ...` lambda whose intended
multiplicity is omega (the closure can be invoked any number
of times).  Inside that inner closure, `f` is APPLIED TWICE
(`f (f x)`), violating linearity — `f` should be consumed
exactly once.

Atkey 2018's broken rule failed to require that `f`'s grade
inside the omega-closure be `1/omega = 0`, so the attack term
type-checked.

## The Wood/Atkey 2022 correction

The corrected Lam rule introduces context division `Gamma/p`:

```
Gamma/p, x :_r A |- body : B
-------------------------------------- Lam (corrected)
Gamma |-_p \(x:_r A). body : (x :_r A) -> B
```

Where `Gamma/p` divides every binding's grade by the lambda's
multiplicity `p`.  For a captured variable at grade `pi`
inside an omega-multiplicity closure, the division is
`pi/omega`:

* `1/omega = 0` — linear variable becomes ghost (not usable)
* `omega/omega = omega` — unrestricted stays unrestricted

The 1/omega = 0 entry is what defeats the attack: `f` at grade 1
captured in an omega-closure has *no available grade* in the
body, so applying `f` (which requires grade >= 1) fails the
grade check.

## What this file ships

* `OuterLamGrade` = omega (the captured-multiplicity-omega closure)
* `InnerVarGrade` = one (the linearly-typed captured variable)
* Computation: `divides one omega = zero`
* A tiny syntax tree for the actual inner attack body `f (f x)`
* Recursive grade accounting proving the body requires two uses of
  the captured linear function, hence grade omega
* The rejection theorem: the corrected Lam rule makes the captured
  function available at zero inside an omega closure, while the
  actual body requires omega.

This is intentionally not the full FX surface elaborator.  It is the
smallest syntactic model that names the historical attack term and
checks the precise grade computation that any full elaborator must
reproduce.

## Dependencies

* `Graded/Instances/Usage.lean` — UsageGrade + divides

## Downstream consumers

* `Graded/Rules.lean` — uses `divides` in Lam rule
* `Graded/AtkeyAttackTerm.lean` (v1.1) — full syntactic model
-/

namespace LeanFX2.Graded.Instances

open UsageGrade

/-! ## The arithmetic core -/

/-- The grade of the outer function's BODY when it returns the
inner closure.  In the attack term, the inner closure is omega-
multiplicity (callable any number of times). -/
def OuterLamGrade : UsageGrade := UsageGrade.omega

/-- The grade declared for the captured variable `f`.  Linear:
must be consumed exactly once across all uses. -/
def InnerVarGrade : UsageGrade := UsageGrade.one

/-! ## The Wood/Atkey 2022 division check

Inside the inner closure, the available grade for `f` is
`InnerVarGrade / OuterLamGrade = 1 / omega = 0`.  Applying `f`
requires grade `>= 1`, but only `0` is available — so the body
fails to grade-check and the term is rejected. -/

/-- Available grade of the linear `f` INSIDE the omega-closure.
By Wood/Atkey 2022 division, this is `1 / omega = 0`. -/
def AvailableGradeInClosure : UsageGrade :=
  UsageGrade.divides InnerVarGrade OuterLamGrade

/-- The exact arithmetic underlying the rejection: a linear
variable becomes ghost when captured by an omega-multiplicity
closure. -/
theorem AvailableGradeInClosure.eqZero :
    AvailableGradeInClosure = UsageGrade.zero := rfl

/-! ## The application requirement

Applying `f : i64 -> i64` requires `f` to be USED, which costs
at least grade `one`.  The check fails because available `zero`
is strictly less than required `one` (under the subsumption
preorder `0 < 1 < omega`). -/

/-- The grade required to apply `f` once inside the body. -/
def UsageRequiredForApply : UsageGrade := UsageGrade.one

/-- Bottom-line: the attack term's grade requirement (`one`)
exceeds available (`zero`).  Encoded as a non-`le` predicate
on the underlying preorder.  Discharged by full enumeration:
`UsageGrade.le one zero` reduces to `False`, so its negation
is `True`. -/
theorem AtkeyAttack.rejected :
    ¬ UsageGrade.le UsageRequiredForApply AvailableGradeInClosure := by
  intro absurdLe
  -- AvailableGradeInClosure reduces to .zero, UsageRequiredForApply
  -- reduces to .one; le .one .zero is False by definition
  exact absurdLe.elim

/-! ## Bonus: applying twice (the doubled f f x case)

The attack applies `f` twice in the body: `f (f x)`.  This
costs `add one one = omega` in usage.  Even if the available
grade were `one` (which it isn't — it's `zero`), the doubled
application would still fail: `omega ≰ one`. -/

/-- Sum of two `f`-applications: `1 + 1 = omega`. -/
def UsageRequiredForDoubleApply : UsageGrade :=
  UsageGrade.add UsageGrade.one UsageGrade.one

/-- The doubled-apply requirement is `omega`. -/
theorem UsageRequiredForDoubleApply.eqOmega :
    UsageRequiredForDoubleApply = UsageGrade.omega := rfl

/-- Even if `f` were captured at grade `one` (no division), the
doubled application would still fail: omega does not subsume
one in the subsumption preorder. -/
theorem AtkeyAttack.rejected_even_without_division :
    ¬ UsageGrade.le UsageRequiredForDoubleApply UsageGrade.one := by
  intro absurdLe
  -- UsageRequiredForDoubleApply = omega; le omega one = False by def
  exact absurdLe.elim

/-! ## Minimal syntax for the historical attack body

The full FX surface term is:

```text
fn higher_order(f) = fn(x) => f(f(x))
```

For the Wood/Atkey check, the only relevant inner-body structure is
the syntax tree `f (f x)`: the captured function `f` appears twice,
and the newly-bound argument `x` appears once.  The following
three-constructor syntax records exactly that fragment and computes
usage grades structurally.
-/

/-- Minimal expression syntax for the inner body of the Atkey attack.
It distinguishes only the captured function, the lambda argument, and
application. -/
inductive AttackExpr : Type
  | capturedFunction : AttackExpr
  | argumentValue : AttackExpr
  | applyExpr (functionExpr argumentExpr : AttackExpr) : AttackExpr
  deriving DecidableEq, Repr

namespace AttackExpr

/-- Usage of the captured outer function in an attack expression. -/
def capturedFunctionUsage : AttackExpr → UsageGrade
  | .capturedFunction => UsageGrade.one
  | .argumentValue => UsageGrade.zero
  | .applyExpr functionExpr argumentExpr =>
      UsageGrade.add
        (capturedFunctionUsage functionExpr)
        (capturedFunctionUsage argumentExpr)

/-- Usage of the inner lambda argument in an attack expression. -/
def argumentUsage : AttackExpr → UsageGrade
  | .capturedFunction => UsageGrade.zero
  | .argumentValue => UsageGrade.one
  | .applyExpr functionExpr argumentExpr =>
      UsageGrade.add
        (argumentUsage functionExpr)
        (argumentUsage argumentExpr)

end AttackExpr

/-- The actual Atkey 2018 inner body: `f (f x)`. -/
def HigherOrderAttackBody : AttackExpr :=
  AttackExpr.applyExpr
    AttackExpr.capturedFunction
    (AttackExpr.applyExpr AttackExpr.capturedFunction AttackExpr.argumentValue)

/-- The actual body uses the captured function twice, so its captured
function usage is omega. -/
theorem HigherOrderAttackBody.capturedFunctionUsage_eqOmega :
    AttackExpr.capturedFunctionUsage HigherOrderAttackBody = UsageGrade.omega := rfl

/-- The actual body uses the inner argument once. -/
theorem HigherOrderAttackBody.argumentUsage_eqOne :
    AttackExpr.argumentUsage HigherOrderAttackBody = UsageGrade.one := rfl

/-- Corrected Wood/Atkey availability for a linear captured function
inside an omega-multiplicity closure: `one / omega = zero`. -/
def CorrectedLamAvailableCapturedFunctionGrade : UsageGrade :=
  UsageGrade.divides InnerVarGrade OuterLamGrade

/-- The corrected Lam rule makes the captured linear function
unavailable inside the omega closure. -/
theorem CorrectedLamAvailableCapturedFunctionGrade.eqZero :
    CorrectedLamAvailableCapturedFunctionGrade = UsageGrade.zero := rfl

/-- Syntactic rejection of the historical Atkey body.

The recursive grade accounting for `f (f x)` requires omega usage of
the captured function, but the corrected Lam rule provides only zero
usage for a linear variable captured by an omega closure. -/
theorem HigherOrderAttackBody.rejectedByCorrectedLam :
    ¬ UsageGrade.le
        (AttackExpr.capturedFunctionUsage HigherOrderAttackBody)
        CorrectedLamAvailableCapturedFunctionGrade := by
  intro impossibleLe
  exact impossibleLe.elim

/-! ## Concrete witnesses

The arithmetic above translates the attack rejection from
"complicated grade-checker bookkeeping" to a syntactic finite-table
computation over `f (f x)`.  The Wood/Atkey 2022 correction is the
`divides` table plus the recursive usage accounting above; without
context division, the captured function would be checked at grade one
and the omega-closure capture bug reappears. -/

end LeanFX2.Graded.Instances
