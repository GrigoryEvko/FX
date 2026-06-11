import FX1Poly.Modal.GradedCostSemantics

/-! # FX1Poly/Modal/GradedCostRelation
    — the cost-indexed reducibility relation at the complexity N-semiring (COST-2 brick 1)

The grade→cost tie's load-bearing object: a Tait-style reducibility
relation indexed by a COST BUDGET, at the §6.3 Dim-13 complexity
N-semiring.  This is the calf/Danielsson/dlPCF construction's first
brick on the GradedLambda substrate:

  * `CostReducible resultType budget subject` — at base type, the
    subject reaches a normal form within `budget` steps; at a graded
    arrow, applying to any `argumentBudget`-reducible argument yields
    a `budget + binderGrade·argumentBudget + 1`-reducible result.
    THE ARROW BUDGET IS THE APP SCALING: the §6.1 coeffect law
    `grades(f a) = grades(f) + r·grades(a)` mirrored into cost
    accounting, plus one unit for the β-step itself — this is where
    the grade semiring and the cost model interlock.
  * `CostReducible.monotone` — budget weakening (the relation is
    upward closed in the budget), the load-bearing structural law.
  * `CostReducible.headExpansion` — backward closure under one step
    at budget `+1`: the cost-indexed CR3, the engine the fundamental
    theorem's β-case will consume.
  * `CostReducible.applicationBudget` — the App interlock is
    DEFINITIONAL (the arrow case is exactly the application law).
  * Honesty smokes, BOTH directions: at binder grade ONE the identity
    is cost-reducible with the budget algebra computing on a genuine
    β-chain (`identityLambda_costReducible_atLinearGrade`); at binder
    grade ZERO it is NOT (`identityLambda_notCostReducible_atZeroGrade`)
    — the relation genuinely demands sufficient grades; underclaiming
    is rejected, so the budget index carries real content.

## The named open core (the next bricks)

The FUNDAMENTAL THEOREM — `HasGradeOver fxComplexitySemiring []
grades t T → CostReducible T (weight grades |t|) t` for a suitable
grade-weighted budget — is NOT claimed here.  Its λ-arm needs the
cost-indexed substitution lemma (closing-environment machinery with
budget bookkeeping through `substAt`), the genuinely hard
calf/dlPCF step; the var/app arms then follow from `monotone` +
`applicationBudget`.  Until it lands, the §6.3 Dim-13 grade→cost
READING stays a hypothesis; what THIS module proves is that the
budget-indexed relation is coherent, strategy-sound (the chains are
genuine `ReducesInSteps`), and grade-sensitive in both directions.

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Modal

/-- **The cost-indexed reducibility relation** at the complexity
N-semiring.  Base: bounded normalization.  Arrow: the graded
application law — the budget of an application is the function's
budget plus the binder grade TIMES the argument's budget plus one
β-step. -/
def CostReducible :
    GTypeOver fxComplexitySemiring → Nat → GradedLambda → Prop
  | .base, budget, subject =>
      ∃ (value : GradedLambda) (steps : Nat),
        GradedLambda.ReducesInSteps subject steps value
          ∧ GradedLambda.IsNormalForm value ∧ steps ≤ budget
  | .arrow binderGrade domain codomain, budget, subject =>
      ∀ (argumentBudget : Nat) (argument : GradedLambda),
        CostReducible domain argumentBudget argument →
          CostReducible codomain
            (budget + Nat.mul binderGrade argumentBudget + 1)
            (.app subject argument)

/-- The base-type payoff, read off the definition: a base-reducible
subject reaches a normal form within its budget — bounded
normalization. -/
theorem CostReducible.extractBoundedNormalization {budget : Nat}
    {subject : GradedLambda}
    (reducible : CostReducible .base budget subject) :
    ∃ (value : GradedLambda) (steps : Nat),
      GradedLambda.ReducesInSteps subject steps value
        ∧ GradedLambda.IsNormalForm value ∧ steps ≤ budget :=
  reducible

/-- A normal form is base-reducible at budget ZERO (the zero-step
chain). -/
theorem CostReducible.ofNormalForm {value : GradedLambda}
    (valueNF : GradedLambda.IsNormalForm value) :
    CostReducible .base 0 value :=
  ⟨value, 0, GradedLambda.ReducesInSteps.refl value, valueNF,
    Nat.le_refl 0⟩

/-- **Budget weakening** — the relation is upward closed in the
budget.  Base: relax the step bound.  Arrow: weaken the recursive
codomain budget pointwise. -/
theorem CostReducible.monotone :
    (resultType : GTypeOver fxComplexitySemiring) →
      {smallBudget largeBudget : Nat} → smallBudget ≤ largeBudget →
      {subject : GradedLambda} →
      CostReducible resultType smallBudget subject →
      CostReducible resultType largeBudget subject
  | .base, _, _, budgetLe, _, reducibleSmall => by
      obtain ⟨value, steps, chain, valueNF, stepsLe⟩ := reducibleSmall
      exact ⟨value, steps, chain, valueNF, Nat.le_trans stepsLe budgetLe⟩
  | .arrow binderGrade domain codomain, _, _, budgetLe, _,
      reducibleSmall =>
      fun argumentBudget argument argReducible =>
        CostReducible.monotone codomain
          (Nat.add_le_add_right
            (Nat.add_le_add_right budgetLe
              (Nat.mul binderGrade argumentBudget))
            1)
          (reducibleSmall argumentBudget argument argReducible)

/-- **Head expansion** (the cost-indexed CR3): one backward step
costs one budget unit.  Base: prepend the step to the chain.  Arrow:
the step lifts through the application head (`congAppLeft`) and the
budget shuffle is associativity-commutativity of `+`. -/
theorem CostReducible.headExpansion :
    (resultType : GTypeOver fxComplexitySemiring) → {budget : Nat} →
      {source reduct : GradedLambda} →
      GradedLambda.Reduces source reduct →
      CostReducible resultType budget reduct →
      CostReducible resultType (budget + 1) source
  | .base, _, _, _, step, reducibleReduct => by
      obtain ⟨value, steps, chain, valueNF, stepsLe⟩ := reducibleReduct
      exact ⟨value, steps + 1,
        GradedLambda.ReducesInSteps.head step chain, valueNF,
        Nat.add_le_add_right stepsLe 1⟩
  | .arrow binderGrade domain codomain, budget, source, reduct, step,
      reducibleReduct =>
      fun argumentBudget argument argReducible =>
        CostReducible.monotone codomain
          (Nat.le_of_eq (congrArg (· + 1)
            (Nat.add_right_comm budget
              (Nat.mul binderGrade argumentBudget) 1)))
          (CostReducible.headExpansion codomain
            (GradedLambda.Reduces.congAppLeft source reduct argument step)
            (reducibleReduct argumentBudget argument argReducible))

/-- **The App interlock is definitional**: applying a
`budget`-reducible function at a graded arrow to an
`argumentBudget`-reducible argument is reducible at
`budget + binderGrade·argumentBudget + 1` — the §6.1 App-scaling law
read as cost accounting.  This is the arrow case of the relation, so
the proof is the identity. -/
theorem CostReducible.applicationBudget
    {binderGrade : Nat}
    {domain codomain : GTypeOver fxComplexitySemiring}
    {budget argumentBudget : Nat} {function argument : GradedLambda}
    (functionReducible :
      CostReducible (.arrow binderGrade domain codomain) budget function)
    (argumentReducible : CostReducible domain argumentBudget argument) :
    CostReducible codomain (budget + binderGrade * argumentBudget + 1)
      (.app function argument) :=
  functionReducible argumentBudget argument argumentReducible

/-! ## Honesty smokes — the budget index has content in BOTH directions -/

/-- At binder grade ONE (the honest usage of the identity), the
identity lambda is cost-reducible at budget zero: applying it to any
`j`-reducible argument costs at most `0 + 1·j + 1` steps — the β-step
plus the argument's own normalization, and the budget algebra computes
exactly that. -/
theorem identityLambda_costReducible_atLinearGrade :
    CostReducible (.arrow (1 : Nat) .base .base) 0 (.lam (.var 0)) :=
  fun argumentBudget argument argReducible => by
    obtain ⟨value, steps, chain, valueNF, stepsLe⟩ := argReducible
    refine ⟨value, steps + 1,
      GradedLambda.ReducesInSteps.head
        (GradedLambda.Reduces.beta (.var 0) argument) chain,
      valueNF, ?stepBound⟩
    show steps + 1 ≤ 0 + 1 * argumentBudget + 1
    rw [Nat.zero_add, Nat.one_mul]
    exact Nat.add_le_add_right stepsLe 1

/-- At binder grade ZERO the identity is NOT cost-reducible at budget
zero: grade 0 claims the argument is never used, so the budget
`0 + 0·j + 1 = 1` cannot pay for normalizing an argument that needs a
step of its own AFTER the β-step.  Witness: the one-step redex
`(λx.x)(λx.x)` as argument — every reduction of the applied term needs
at least two steps to reach a normal form.  The relation REJECTS
grade underclaiming: the budget index is genuinely grade-sensitive. -/
theorem identityLambda_notCostReducible_atZeroGrade :
    ¬ CostReducible (.arrow (0 : Nat) .base .base) 0 (.lam (.var 0)) := by
  intro reducible
  have argReducible :
      CostReducible .base 1 (.app (.lam (.var 0)) (.lam (.var 0))) :=
    ⟨.lam (.var 0), 1, GradedLambda.identityRedex_costsOneStep,
      GradedLambda.lam_isNormalForm (GradedLambda.var_isNormalForm 0),
      Nat.le_refl 1⟩
  have appliedAtOne :
      CostReducible .base 1
        (.app (.lam (.var 0)) (.app (.lam (.var 0)) (.lam (.var 0)))) :=
    reducible 1 (.app (.lam (.var 0)) (.lam (.var 0))) argReducible
  obtain ⟨value, steps, chain, valueNF, stepsLe⟩ := appliedAtOne
  cases chain with
  | refl _ =>
      exact valueNF
        (GradedLambda.Reduces.beta (.var 0)
          (.app (.lam (.var 0)) (.lam (.var 0))))
  | head firstStep rest =>
      cases rest with
      | refl _ =>
          cases firstStep with
          | beta body argument =>
              exact valueNF
                (GradedLambda.Reduces.beta (.var 0) (.lam (.var 0)))
          | congAppLeft function function' argument functionStep =>
              cases functionStep with
              | congLam _ _ varStep => exact nomatch varStep
          | congAppRight function argument argument' argumentStep =>
              cases argumentStep with
              | beta innerBody innerArgument =>
                  exact valueNF
                    (GradedLambda.Reduces.beta (.var 0) (.lam (.var 0)))
              | congAppLeft _ _ _ innerFunctionStep =>
                  cases innerFunctionStep with
                  | congLam _ _ varStep => exact nomatch varStep
              | congAppRight _ _ _ innerArgumentStep =>
                  cases innerArgumentStep with
                  | congLam _ _ varStep => exact nomatch varStep
      | head secondStep _ =>
          exact nomatch Nat.le_of_succ_le_succ stepsLe

end FX1Poly.Modal
