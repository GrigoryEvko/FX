import FX1Poly.Core.Rewriting.Normalize.WeakHeadNormalPreservation

/-! # FX1Poly/Core/WeakHeadNormalRootStability
    — a weak-head-normal term keeps its root generator along arbitrary multi-step reduction

`WeakHeadNormalPreservation` shows weak-head-normality is preserved by a single step
(`weakHeadNormalPreservedByStep`) and `ReducibleTypeForwardClosure` shows the root generator is preserved
by a single step out of a weak-head-normal term (`Step.rootGenerator_eq_of_weakHeadNormal`).  Composed along
a `StepStar`, the two give the multi-step fact this file ships:

`WeakHeadStep.rootGeneratorStableAlongStepStar`: if `start` is weak-head normal (no `WeakHeadStep`) and
`StepStar start finish`, then `start.rootGenerator = finish.rootGenerator`.

The point: a weak-head-normal term can only reduce INTERNALLY (in proper, non-principal positions), and an
internal step never changes the head generator.  So however far a weak-head-normal term reduces, its head
stays fixed.  This is the structural engine behind "a weak-head-normal data member is a VALUE or NEUTRAL":
its reachable value (from the canonical-forms disjunct) has a constructor head, the root is stable, so the
weak-head-normal term already wears that constructor head — and a nullary constructor head pins the term to
the value cell itself.  That classification is exactly the lift-back the native data-eliminator
fundamental-theorem rows need (the eliminator over a weak-head-normal scrutinee either fires its ι on a
value, or is neutral).

The proof mirrors `ReducibleType.neutralPreservedAlongStepStar` (which threads the same two lemmas to keep a
type weak-head-normal non-Π), but concludes the raw root EQUALITY rather than the `≠ piTyCode` survival —
a strictly more reusable statement (the data classification needs the actual head, not just its non-Π-ness).

## Zero-axiom verification

Induction on the `StepStar` chain; each leading step both preserves weak-head-normality
(`WeakHeadStep.weakHeadNormalPreservedByStep`, refreshing the induction hypothesis' guard) and fixes the root
(`Step.rootGenerator_eq_of_weakHeadNormal`), composed by `Eq.trans`.  No `funext`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Swept per declaration by
`#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Tier0.Syntax

/-- **A weak-head-normal term keeps its root generator along `StepStar`.**  If `start` admits no weak-head
step and reduces (in any number of steps) to `finish`, then `start` and `finish` share a root generator —
every step out of a weak-head-normal term is an internal congruence (`Step.rootGenerator_eq_of_weakHeadNormal`)
that leaves a reduct still weak-head-normal (`WeakHeadStep.weakHeadNormalPreservedByStep`), so the head never
moves.  The multi-step engine behind the data-eliminator value/neutral classification. -/
theorem WeakHeadStep.rootGeneratorStableAlongStepStar {scope : Nat} :
    ∀ {start finish : RawTerm scope}, StepStar start finish →
      (∀ reduct : RawTerm scope, ¬ WeakHeadStep start reduct) →
      start.rootGenerator = finish.rootGenerator := by
  intro start finish chain
  induction chain with
  | refl _ => intro _noWeakHeadStep; rfl
  | trans firstStep _restChain restStable =>
      intro noWeakHeadStep
      have intermediateNoWeakHeadStep :=
        WeakHeadStep.weakHeadNormalPreservedByStep noWeakHeadStep firstStep
      have rootEquation := Step.rootGenerator_eq_of_weakHeadNormal noWeakHeadStep firstStep
      exact rootEquation.symm.trans (restStable intermediateNoWeakHeadStep)

end FX1Poly.Core
