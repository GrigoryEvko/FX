import FX1Poly.Modal.GradedCostRelation
import FX1Poly.Modal.GradedReductionSubstitution
import FX1Poly.Modal.GradedTypingGeneric

/-! # FX1Poly/Modal/GradedCostFundamental
    — ★ the COST-2 fundamental theorem: complexity grades bound evaluation cost

The §6.3 Dim-13 grade→cost tie, PROVED.  `HasGradeOver.costFundamental`:
every term graded by the generic judgment at the complexity N-semiring is
`CostReducible` at the budget

    `weightedBudget grades budgetAssignment + intrinsicWeight`

— the §6.2 grade vector contracted against the per-variable environment
budgets (the inner product: a variable consumed at grade `r` contributes
`r ·` its substitution's own normalization budget), plus a term-intrinsic
weight covering the term's own β-steps.  The grade SCALING in the budget
is structural, not accidental: the arrow case of `CostReducible` is the
§6.1 App law `grades(f a) = grades(f) + r·grades(a)` read as cost, and the
fundamental theorem threads exactly that algebra through every arm.

  * `weightedBudget` — the grade-vector/budget-assignment inner product,
    with its linearity laws (`_zero` / `_single_of_lookup` / `_add` /
    `_scale`) mirroring the §6.2 vector operations the three typing rules
    use (`single` / `add` / `scale`).
  * `CostReducibleSubstitution` + `cons` — the closing-substitution
    environment, each variable's image cost-reducible at its assigned
    budget (the cost-indexed twin of `ReducibleSubstitution`).
  * `HasGradeOver.costFundamental` — the fundamental theorem.  The
    quantifier order is load-bearing: the intrinsic weight is chosen
    BEFORE the environment (`∃ weight, ∀ substitution …`), which is what
    lets the λ-arm reuse one body weight for every future argument.  The
    λ-arm is the cost-indexed substitution step: the β-reduct is rewritten
    into the extended environment by the σ-algebra composition
    `substAt_zero_applySubstitution_lift`, head-expanded at `+1`, and the
    budget shuffle is pure semiring algebra.
  * `HasGradeOver.closedCostReducible` / `closedBaseNormalizesWithinBudget`
    — closed corollaries: every closed well-graded term is cost-reducible;
    at base type it reaches a normal form within a budget.
  * Smokes: the linear identity is cost-reducible at its grade-ONE arrow
    via the theorem, and the K combinator is cost-reducible at a type
    whose inner arrow has grade ZERO — the zero-grade arrow IS inhabited
    by genuinely-discarding functions, in contrast to
    `identityLambda_notCostReducible_atZeroGrade` (grade underclaiming by
    a USING function is rejected; honest discarding is admitted).

## Honest scope

The budgets are ∃-strategy: `CostReducible` at base demands SOME reduction
chain within budget (the optimal, discard-early path), matching the
relation's β-counting cost model — not every strategy is bounded (a
discarded argument's internal redexes cost nothing on the optimal path).
The intrinsic weight is existential and derivation-dependent (the
judgment is a `Prop`, so no weight function can be computed from it); the
GRADE-weighted environment scaling is the structural, quantitative part.

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Modal

/-! ## The grade/budget inner product and its linearity laws -/

/-- Middle-four exchange for `Nat` addition (hand-rolled from the clean
`Nat.add_assoc`/`Nat.add_comm`; the shuffle engine of the budget algebra). -/
theorem natAddMiddleExchange (firstTerm secondTerm thirdTerm fourthTerm : Nat) :
    firstTerm + secondTerm + (thirdTerm + fourthTerm)
      = firstTerm + thirdTerm + (secondTerm + fourthTerm) := by
  rw [Nat.add_assoc firstTerm secondTerm (thirdTerm + fourthTerm),
    Nat.add_assoc firstTerm thirdTerm (secondTerm + fourthTerm),
    ← Nat.add_assoc secondTerm thirdTerm fourthTerm,
    Nat.add_comm secondTerm thirdTerm,
    Nat.add_assoc thirdTerm secondTerm fourthTerm]

/-- **The grade/budget inner product**: contract a complexity grade vector
against a per-variable budget assignment — `Σ gradeᵢ · assignment i`.  A
variable consumed at grade `r` contributes `r ·` its budget; an erased
(grade-0) variable contributes nothing.  (Explicit `Nat.mul`: the carrier
is definitionally `Nat` but not for typeclass synthesis.) -/
def weightedBudget : GradeVectorOver fxComplexitySemiring → (Nat → Nat) → Nat
  | .nil, _ => 0
  | .cons headGrade restGrades, assignment =>
      Nat.mul headGrade (assignment 0)
        + weightedBudget restGrades (fun position => assignment (position + 1))

/-- The all-zero grade vector contracts to budget zero (erased bindings are
free). -/
theorem weightedBudget_zero :
    ∀ (scope : Nat) (assignment : Nat → Nat),
      weightedBudget (GradeVectorOver.zero fxComplexitySemiring scope) assignment = 0
  | 0, _ => rfl
  | scope + 1, assignment => by
      show Nat.mul fxComplexitySemiring.zero (assignment 0)
          + weightedBudget (GradeVectorOver.zero fxComplexitySemiring scope)
              (fun position => assignment (position + 1)) = 0
      rw [weightedBudget_zero scope]
      exact Nat.zero_mul (assignment 0)

/-- The var-rule singleton contracts to exactly the looked-up variable's
budget (`1 · assignment index`, zeros elsewhere) — the var arm's budget law.
The in-range premise is carried by the lookup success. -/
theorem weightedBudget_single_of_lookup :
    ∀ (typeContext : List (GTypeOver fxComplexitySemiring)) (index : Nat)
      (varType : GTypeOver fxComplexitySemiring) (assignment : Nat → Nat),
      GTypeOver.lookup typeContext index = some varType →
      weightedBudget
        (GradeVectorOver.single fxComplexitySemiring typeContext.length index
          fxComplexitySemiring.one) assignment = assignment index
  | [], index, _, _, lookupEq => nomatch index, lookupEq
  | _ :: restTypes, 0, _, assignment, _ => by
      show Nat.mul fxComplexitySemiring.one (assignment 0)
          + weightedBudget (GradeVectorOver.zero fxComplexitySemiring restTypes.length)
              (fun position => assignment (position + 1)) = assignment 0
      rw [weightedBudget_zero restTypes.length]
      exact Nat.one_mul (assignment 0)
  | _ :: restTypes, position + 1, varType, assignment, lookupEq => by
      show Nat.mul fxComplexitySemiring.zero (assignment 0)
          + weightedBudget
              (GradeVectorOver.single fxComplexitySemiring restTypes.length position
                fxComplexitySemiring.one)
              (fun innerPosition => assignment (innerPosition + 1)) = assignment (position + 1)
      rw [weightedBudget_single_of_lookup restTypes position varType
            (fun innerPosition => assignment (innerPosition + 1)) lookupEq]
      exact (congrArg (· + assignment (position + 1))
        (Nat.zero_mul (assignment 0))).trans (Nat.zero_add (assignment (position + 1)))

/-- The inner product is additive in the grade vector (pointwise `add`
distributes out; the App rule's `+`).  Stated over equal-length vectors —
the §6.2 length invariant every derivation maintains. -/
theorem weightedBudget_add :
    ∀ (firstGrades secondGrades : GradeVectorOver fxComplexitySemiring)
      (assignment : Nat → Nat), firstGrades.length = secondGrades.length →
      weightedBudget (GradeVectorOver.add firstGrades secondGrades) assignment
        = weightedBudget firstGrades assignment + weightedBudget secondGrades assignment
  | .nil, .nil, _, _ => rfl
  | .nil, .cons _ _, _, lengthEq => nomatch lengthEq
  | .cons _ _, .nil, _, lengthEq => nomatch lengthEq
  | .cons firstHead firstRest, .cons secondHead secondRest, assignment, lengthEq => by
      show Nat.mul (fxComplexitySemiring.add firstHead secondHead) (assignment 0)
          + weightedBudget (GradeVectorOver.add firstRest secondRest)
              (fun position => assignment (position + 1))
        = (Nat.mul firstHead (assignment 0)
            + weightedBudget firstRest (fun position => assignment (position + 1)))
          + (Nat.mul secondHead (assignment 0)
            + weightedBudget secondRest (fun position => assignment (position + 1)))
      rw [weightedBudget_add firstRest secondRest
            (fun position => assignment (position + 1)) (Nat.succ.inj lengthEq)]
      exact (congrArg
          (· + (weightedBudget firstRest (fun position => assignment (position + 1))
            + weightedBudget secondRest (fun position => assignment (position + 1))))
          (natRightDistrib firstHead secondHead (assignment 0))).trans
        (natAddMiddleExchange (Nat.mul firstHead (assignment 0))
          (Nat.mul secondHead (assignment 0))
          (weightedBudget firstRest (fun position => assignment (position + 1)))
          (weightedBudget secondRest (fun position => assignment (position + 1))))

/-- The inner product is homogeneous in the grade vector (scalar `scale`
factors out; the App rule's `r ·`). -/
theorem weightedBudget_scale :
    ∀ (scaleGrade : fxComplexitySemiring.Carrier)
      (someGrades : GradeVectorOver fxComplexitySemiring) (assignment : Nat → Nat),
      weightedBudget (GradeVectorOver.scale scaleGrade someGrades) assignment
        = Nat.mul scaleGrade (weightedBudget someGrades assignment)
  | _, .nil, _ => rfl
  | scaleGrade, .cons headGrade restGrades, assignment => by
      show Nat.mul (fxComplexitySemiring.mul scaleGrade headGrade) (assignment 0)
          + weightedBudget (GradeVectorOver.scale scaleGrade restGrades)
              (fun position => assignment (position + 1))
        = Nat.mul scaleGrade (Nat.mul headGrade (assignment 0)
            + weightedBudget restGrades (fun position => assignment (position + 1)))
      rw [weightedBudget_scale scaleGrade restGrades (fun position => assignment (position + 1))]
      exact (congrArg
          (· + Nat.mul scaleGrade
            (weightedBudget restGrades (fun position => assignment (position + 1))))
          (natMulAssoc scaleGrade headGrade (assignment 0))).trans
        (Nat.left_distrib scaleGrade (Nat.mul headGrade (assignment 0))
          (weightedBudget restGrades (fun position => assignment (position + 1)))).symm

/-! ## The cost-reducible closing environment -/

/-- Extend a budget assignment under a binder: position `0` gets the new
binding's budget, the rest shift up (the budget twin of `consSubstitution`). -/
def consBudgetAssignment (headBudget : Nat) (tailAssignment : Nat → Nat) : Nat → Nat
  | 0 => headBudget
  | position + 1 => tailAssignment position

/-- A substitution is cost-reducible at a context and budget assignment when
every variable's image is cost-reducible at its declared type and assigned
budget — the cost-indexed closing environment of the fundamental theorem. -/
def CostReducibleSubstitution (typeContext : List (GTypeOver fxComplexitySemiring))
    (budgetAssignment : Nat → Nat) (substitution : TermSubstitution) : Prop :=
  ∀ (index : Nat) (varType : GTypeOver fxComplexitySemiring),
    GTypeOver.lookup typeContext index = some varType →
    CostReducible varType (budgetAssignment index) (substitution index)

/-- Extend a cost-reducible substitution under a binder (the λ-arm's
environment extension, with the argument's budget threaded). -/
theorem CostReducibleSubstitution.cons {domain : GTypeOver fxComplexitySemiring}
    {head : GradedLambda} {headBudget : Nat}
    {typeContext : List (GTypeOver fxComplexitySemiring)}
    {budgetAssignment : Nat → Nat} {tail : TermSubstitution}
    (headReducible : CostReducible domain headBudget head)
    (tailReducible : CostReducibleSubstitution typeContext budgetAssignment tail) :
    CostReducibleSubstitution (domain :: typeContext)
      (consBudgetAssignment headBudget budgetAssignment) (consSubstitution head tail) := by
  intro index varType lookupEq
  cases index with
  | zero =>
      have domainEq : domain = varType := Option.some.inj lookupEq
      rw [← domainEq]
      exact headReducible
  | succ predecessor => exact tailReducible predecessor varType lookupEq

/-! ## ★ The fundamental theorem -/

/-- ★ **The COST-2 fundamental theorem — complexity grades bound evaluation
cost.**  A term graded at the complexity N-semiring, closed by a
cost-reducible substitution, is cost-reducible at the GRADE-WEIGHTED budget
`weightedBudget grades budgetAssignment + intrinsicWeight`: the grade vector
contracted against the environment's budgets, plus a term-intrinsic weight.

The quantifier order (`∃ weight` BEFORE `∀ substitution`) is the λ-arm's
crux: the lambda must commit to one body weight that works for every future
argument, which the inductive hypothesis supplies precisely because its own
weight is environment-independent.  The λ-arm rewrites the β-reduct into the
extended environment via the σ-algebra composition
`substAt_zero_applySubstitution_lift`, head-expands at `+1`, and shuffles
`(r·j + W) + w + 1 = (W + w) + r·j + 1`; the app arm distributes
`r·(Wₐ + wₐ)` and re-associates through the middle-four exchange. -/
theorem HasGradeOver.costFundamental
    {typeContext : List (GTypeOver fxComplexitySemiring)}
    {grades : GradeVectorOver fxComplexitySemiring} {term : GradedLambda}
    {resultType : GTypeOver fxComplexitySemiring}
    (typed : HasGradeOver fxComplexitySemiring typeContext grades term resultType) :
    ∃ (intrinsicWeight : Nat),
      ∀ (substitution : TermSubstitution) (budgetAssignment : Nat → Nat),
        CostReducibleSubstitution typeContext budgetAssignment substitution →
        CostReducible resultType
          (weightedBudget grades budgetAssignment + intrinsicWeight)
          (GradedLambda.applySubstitution substitution term) := by
  induction typed with
  | var typeContext index varType lookupOk =>
      refine ⟨0, fun substitution budgetAssignment envReducible => ?_⟩
      exact CostReducible.monotone varType
        (Nat.le_of_eq
          (weightedBudget_single_of_lookup typeContext index varType
            budgetAssignment lookupOk).symm)
        (envReducible index varType lookupOk)
  | lam typeContext binderGrade domain codomain outerGrades body bodyTyped bodyIH =>
      obtain ⟨bodyWeight, bodyFundamental⟩ := bodyIH
      refine ⟨bodyWeight, fun substitution budgetAssignment envReducible => ?_⟩
      intro argumentBudget argument argumentReducible
      have bodyReducible := bodyFundamental (consSubstitution argument substitution)
        (consBudgetAssignment argumentBudget budgetAssignment)
        (CostReducibleSubstitution.cons argumentReducible envReducible)
      rw [← substAt_zero_applySubstitution_lift body argument substitution] at bodyReducible
      have expanded := CostReducible.headExpansion codomain
        (GradedLambda.Reduces.beta
          (GradedLambda.applySubstitution (liftSubstitution substitution) body) argument)
        bodyReducible
      exact CostReducible.monotone codomain
        (Nat.le_of_eq (congrArg (· + 1)
          ((Nat.add_assoc (Nat.mul binderGrade argumentBudget)
              (weightedBudget outerGrades budgetAssignment) bodyWeight).trans
            (Nat.add_comm (Nat.mul binderGrade argumentBudget)
              (weightedBudget outerGrades budgetAssignment + bodyWeight)))))
        expanded
  | app typeContext binderGrade domain codomain functionGrades argumentGrades function
      argument functionTyped argumentTyped functionIH argumentIH =>
      obtain ⟨functionWeight, functionFundamental⟩ := functionIH
      obtain ⟨argumentWeight, argumentFundamental⟩ := argumentIH
      refine ⟨functionWeight + Nat.mul binderGrade argumentWeight + 1,
        fun substitution budgetAssignment envReducible => ?_⟩
      have combinedWeighted :
          weightedBudget
              (GradeVectorOver.add functionGrades
                (GradeVectorOver.scale binderGrade argumentGrades)) budgetAssignment
            = weightedBudget functionGrades budgetAssignment
              + Nat.mul binderGrade (weightedBudget argumentGrades budgetAssignment) := by
        rw [weightedBudget_add functionGrades
              (GradeVectorOver.scale binderGrade argumentGrades) budgetAssignment
              (by rw [GradeVectorOver.scale_length]
                  exact (hasGradeOver_length functionTyped).trans
                    (hasGradeOver_length argumentTyped).symm),
          weightedBudget_scale binderGrade argumentGrades budgetAssignment]
      exact CostReducible.monotone codomain
        (Nat.le_of_eq
          ((congrArg
              (fun scaledArgument =>
                weightedBudget functionGrades budgetAssignment + functionWeight
                  + scaledArgument + 1)
              (Nat.left_distrib binderGrade
                (weightedBudget argumentGrades budgetAssignment) argumentWeight)).trans
            ((congrArg (· + 1)
              (natAddMiddleExchange (weightedBudget functionGrades budgetAssignment)
                functionWeight
                (Nat.mul binderGrade (weightedBudget argumentGrades budgetAssignment))
                (Nat.mul binderGrade argumentWeight))).trans
              ((Nat.add_assoc
                  (weightedBudget functionGrades budgetAssignment
                    + Nat.mul binderGrade (weightedBudget argumentGrades budgetAssignment))
                  (functionWeight + Nat.mul binderGrade argumentWeight) 1).trans
                (congrArg (· + (functionWeight + Nat.mul binderGrade argumentWeight + 1))
                  combinedWeighted.symm)))))
        (CostReducible.applicationBudget
          (functionFundamental substitution budgetAssignment envReducible)
          (argumentFundamental substitution budgetAssignment envReducible))

/-! ## Closed corollaries -/

/-- Every CLOSED well-graded term is cost-reducible at some budget (the
fundamental theorem at the empty environment + identity substitution). -/
theorem HasGradeOver.closedCostReducible {grades : GradeVectorOver fxComplexitySemiring}
    {term : GradedLambda} {resultType : GTypeOver fxComplexitySemiring}
    (typed : HasGradeOver fxComplexitySemiring [] grades term resultType) :
    ∃ (budget : Nat), CostReducible resultType budget term := by
  obtain ⟨intrinsicWeight, fundamental⟩ := typed.costFundamental
  have emptyEnvReducible :
      CostReducibleSubstitution [] (fun _ => 0) (fun index => GradedLambda.var index) :=
    fun index _ lookupEq => nomatch index, lookupEq
  have reducible := fundamental (fun index => GradedLambda.var index) (fun _ => 0)
    emptyEnvReducible
  rw [GradedLambda.applySubstitution_id] at reducible
  exact ⟨weightedBudget grades (fun _ => 0) + intrinsicWeight, reducible⟩

/-- **Closed base-type bounded normalization**: every closed term graded at
base type reaches a normal form within a budget — the §6.3 Dim-13 payoff
read at ground type. -/
theorem HasGradeOver.closedBaseNormalizesWithinBudget
    {grades : GradeVectorOver fxComplexitySemiring} {term : GradedLambda}
    (typed : HasGradeOver fxComplexitySemiring [] grades term .base) :
    ∃ (budget : Nat) (value : GradedLambda) (steps : Nat),
      GradedLambda.ReducesInSteps term steps value
        ∧ GradedLambda.IsNormalForm value ∧ steps ≤ budget := by
  obtain ⟨budget, reducible⟩ := typed.closedCostReducible
  obtain ⟨value, steps, chain, valueNF, stepsLe⟩ := reducible
  exact ⟨budget, value, steps, chain, valueNF, stepsLe⟩

/-! ## Non-vacuity smokes — the theorem lands on the brick-1 frontier -/

/-- The linear identity is cost-reducible at its grade-ONE arrow VIA THE
FUNDAMENTAL THEOREM (brick 1 proved this by hand; now it falls out of the
typing derivation). -/
theorem linearIdentityCostReducibleViaFundamental :
    ∃ (budget : Nat),
      CostReducible (.arrow fxComplexitySemiring.one .base .base) budget
        (.lam (.var 0)) :=
  (linearIdentityOver_typed fxComplexitySemiring).closedCostReducible

/-- The K combinator is cost-reducible at a type whose INNER arrow has grade
ZERO: the zero-grade arrow is inhabited by genuinely-discarding functions.
The contrast pin to `identityLambda_notCostReducible_atZeroGrade`: a
function that USES its argument cannot underclaim grade zero, but a function
that truly discards passes — the relation tracks actual consumption. -/
theorem kCombinatorCostReducibleViaFundamental :
    ∃ (budget : Nat),
      CostReducible
        (.arrow fxComplexitySemiring.one .base
          (.arrow fxComplexitySemiring.zero .base .base)) budget
        (.lam (.lam (.var 1))) :=
  (kCombinatorOver_typed fxComplexitySemiring).closedCostReducible

end FX1Poly.Modal
