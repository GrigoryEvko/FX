/-! # FX1Poly/Modal/GradedLambdaTerm — the shared graded λ-calculus carrier (de Bruijn) + substitution

The minimal graded λ-calculus `GradedLambda` (var / lam / app, de Bruijn) together with its de Bruijn
substitution substrate (`shift` / `substAt`).  This is the SHARED carrier: both the generic
graded-typing engine (`HasGradeOver R` over any `OrderedGradeSemiring`, `GradedTypingGeneric`) and the
usage-specific discipline (`UsageDiscipline`'s occurrence check + Atkey corpus) range over it.  Carrying
it in its own module keeps the generic engine free of any usage-specific import — the generic chain
imports this carrier, never the usage discipline.

## Zero-axiom verification

A plain inductive plus two structural-recursion de Bruijn operations: `shift` increments every free
index `≥ cutoff`; `substAt` replaces one index (shifting the replacement under each binder), with
`substAt 0` the β-substitution `b[0 := a]`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- A minimal graded λ-calculus (de Bruijn indices): the shared carrier on which both the generic
graded-typing judgment and the usage discipline range.  Distinct from the kernel's `RawTerm` — this is
the focused object of study for the graded dimensions' metatheory. -/
inductive GradedLambda where
  | var : Nat → GradedLambda
  | lam : GradedLambda → GradedLambda
  | app : GradedLambda → GradedLambda → GradedLambda
  deriving DecidableEq, Repr

/-- de Bruijn lift: increment every free index `≥ cutoff`. -/
def GradedLambda.shift (cutoff : Nat) : GradedLambda → GradedLambda
  | .var index => if index < cutoff then .var index else .var (index + 1)
  | .lam body => .lam (GradedLambda.shift (cutoff + 1) body)
  | .app function argument =>
      .app (GradedLambda.shift cutoff function) (GradedLambda.shift cutoff argument)

/-- de Bruijn substitution: replace variable `index` by `replacement`, decrementing higher indices
(shifting `replacement` under each binder).  `substAt 0` is the β-substitution `b[0 := a]`. -/
def GradedLambda.substAt (index : Nat) (replacement : GradedLambda) : GradedLambda → GradedLambda
  | .var varIndex =>
      if varIndex < index then .var varIndex
      else if varIndex = index then replacement
      else .var (varIndex - 1)
  | .lam body =>
      .lam (GradedLambda.substAt (index + 1) (GradedLambda.shift 0 replacement) body)
  | .app function argument =>
      .app (GradedLambda.substAt index replacement function)
        (GradedLambda.substAt index replacement argument)

end FX1Poly.Modal
