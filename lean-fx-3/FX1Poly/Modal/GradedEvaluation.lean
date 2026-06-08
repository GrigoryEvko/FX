import FX1Poly.Modal.GradedProgress
import FX1Poly.Modal.GradedSubjectReductionGeneric

/-! # FX1Poly/Modal/GradedEvaluation — full-β subject reduction + the evaluation theorem

The capstone of the generic graded calculus's type-safety story (`HasGradeOver R`).  Firing-prior
work shipped ROOT-β subject reduction (`hasGradeOver_betaPreservation`, grades preserved exactly) and
PROGRESS + canonical forms (`GradedProgress.lean`).  This file lifts SR from root-β to the FULL
congruence-closed β-reduction `GradedLambda.Reduces` (β at any position), closes it under
`ReducesStar`, and combines preservation + progress + SN into the headline:

  **every CLOSED well-typed term β-reduces to a `.lam` value** (`closedReducesToLam`).

That is "well-typed graded programs evaluate to values", generic over every graded dimension `R`.  It
composes the whole metatheory:

  * PRESERVATION — `hasGradeOver_reducesPreservation` (full-β SR, grades-exact) + its `ReducesStar`
    closure `hasGradeOver_reducesStarPreservation`.
  * PROGRESS — `closedWellTypedProgress` / `closedNormalFormIsLam` (`GradedProgress.lean`).
  * TERMINATION — `HasGradeOver.stronglyNormalizing` (SN via grade erasure, #878).

The grade-EXACT preservation is what makes the full-β lift clean: root β preserves the grade vector
literally (`hasGradeOver_betaPreservation`), so each congruence arm rebuilds with the SAME grades —
`congLam` hands the body `cons binderGrade grades` via `invertLam`, the induction hypothesis returns
the very same vector, and the `lam` rule reassembles at the identical arrow.  No existential
grade-vector reshape is needed.

Declarations:

  * **`hasGradeOver_reducesPreservation`** — full-β SR: `HasGradeOver R ctx grades term T` and
    `Reduces term term'` give `HasGradeOver R ctx grades term' T` (same grades, same type).  Induction
    on the `Reduces` derivation: `beta` is root SR, the three congruence arms invert + recurse +
    reassemble.
  * **`hasGradeOver_reducesStarPreservation`** — the `ReducesStar` (reflexive-transitive) closure.
  * **`closedReducesToLam`** — ★ EVALUATION: a closed well-typed term reduces to a `.lam`.
    Well-founded recursion on the SN accessibility (`HasGradeOver.stronglyNormalizing`): at the current
    term, `stepOrNormal` either gives a step (retype the reduct by SR, recurse on the strictly-smaller
    reduct, prepend the step) or a normal form (canonical forms makes it a `.lam`, reached in zero
    steps).

## Zero-axiom verification

Induction on the `GradedLambda.Reduces` / `ReflTransClosure` derivations and on the `Acc` accessibility
(motive a `∃`/typing-threading statement, propext-clean), the shipped inversions + constructors
(`invertLam` / `invertApp` / `HasGradeOver.lam` / `HasGradeOver.app`), the root-β SR
(`hasGradeOver_betaPreservation`), progress (`stepOrNormal`), and canonical forms
(`closedNormalFormIsLam`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
or `omega` (every declaration probed with `#print axioms` before landing).  Per-declaration audit-gated
in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

open FX1Poly.Core (ReflTransClosure)

/-- **Full-β subject reduction (grades-exact).**  Typing is preserved under ANY single `Reduces` step
(β at any position), with the grade vector and type literally unchanged.  Induction on the `Reduces`
derivation: `beta` is the shipped root-β SR; each congruence arm inverts the typing, recurses on the
reduced child (the induction hypothesis returns the same grades, by exactness), and reassembles. -/
theorem hasGradeOver_reducesPreservation {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) {term term' : GradedLambda}
    (step : GradedLambda.Reduces term term') :
    ∀ {ctx : List (GTypeOver R)} {grades : GradeVectorOver R} {resultType : GTypeOver R},
      HasGradeOver R ctx grades term resultType → HasGradeOver R ctx grades term' resultType := by
  induction step with
  | beta body argTerm =>
      intro ctx grades resultType typed
      exact hasGradeOver_betaPreservation lawful typed
  | congLam body body' _ bodyIH =>
      intro ctx grades resultType typed
      obtain ⟨binderGrade, domain, codomain, arrowEq, bodyTyped⟩ := HasGradeOver.invertLam typed
      subst arrowEq
      exact HasGradeOver.lam ctx binderGrade domain codomain grades body' (bodyIH bodyTyped)
  | congAppLeft function function' argTerm _ functionIH =>
      intro ctx grades resultType typed
      obtain ⟨binderGrade, domain, functionGrades, argumentGrades, functionTyped, argTyped,
        gradesEq⟩ := HasGradeOver.invertApp typed
      subst gradesEq
      exact HasGradeOver.app ctx binderGrade domain resultType functionGrades argumentGrades
        function' argTerm (functionIH functionTyped) argTyped
  | congAppRight function argTerm argTerm' _ argumentIH =>
      intro ctx grades resultType typed
      obtain ⟨binderGrade, domain, functionGrades, argumentGrades, functionTyped, argTyped,
        gradesEq⟩ := HasGradeOver.invertApp typed
      subst gradesEq
      exact HasGradeOver.app ctx binderGrade domain resultType functionGrades argumentGrades
        function argTerm' functionTyped (argumentIH argTyped)

/-- **Multi-step full-β subject reduction.**  Typing is preserved along any `ReducesStar` chain — the
reflexive-transitive closure of `hasGradeOver_reducesPreservation`. -/
theorem hasGradeOver_reducesStarPreservation {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) {ctx : List (GTypeOver R)}
    {term term' : GradedLambda} (star : GradedLambda.ReducesStar term term') :
    ∀ {grades : GradeVectorOver R} {resultType : GTypeOver R},
      HasGradeOver R ctx grades term resultType → HasGradeOver R ctx grades term' resultType := by
  induction star with
  | refl _ => intro grades resultType typed; exact typed
  | head first _ restIH =>
      intro grades resultType typed
      exact restIH (hasGradeOver_reducesPreservation lawful first typed)

/-- ★ **Evaluation.**  Every CLOSED well-typed term β-reduces to a `.lam` value.  Well-typed graded
programs evaluate — they neither diverge (SN) nor get stuck (progress).  Proof by well-founded
recursion on the SN accessibility: at the current term, progress (`stepOrNormal`) either yields a step
— retype the reduct by full-β SR (grades exact), recurse on the strictly-smaller reduct, prepend the
step — or a normal form, which canonical forms (`closedNormalFormIsLam`) makes a `.lam` reached in zero
steps.  Generic over every graded dimension `R`. -/
theorem closedReducesToLam {R : OrderedGradeSemiring} (lawful : IsLawfulOrderedGradeSemiring R)
    {grades : GradeVectorOver R} {term : GradedLambda} {resultType : GTypeOver R}
    (typed : HasGradeOver R [] grades term resultType) :
    ∃ body, GradedLambda.ReducesStar term (.lam body) := by
  have general : ∀ (current : GradedLambda), GradedLambda.IsStronglyNormalizing current →
      ∀ {currentGrades : GradeVectorOver R} {currentType : GTypeOver R},
        HasGradeOver R [] currentGrades current currentType →
          ∃ body, GradedLambda.ReducesStar current (.lam body) := by
    intro current accessible
    induction accessible with
    | intro current _ reductIH =>
        intro currentGrades currentType currentTyped
        cases GradedLambda.stepOrNormal current with
        | inr normal =>
            obtain ⟨body, currentEq⟩ := closedNormalFormIsLam current currentTyped normal
            refine ⟨body, ?_⟩
            rw [currentEq]
            exact ReflTransClosure.refl _
        | inl stepWitness =>
            obtain ⟨reduct, step⟩ := stepWitness
            obtain ⟨body, reductStar⟩ :=
              reductIH reduct step (hasGradeOver_reducesPreservation lawful step currentTyped)
            exact ⟨body, ReflTransClosure.head step reductStar⟩
  exact general term typed.stronglyNormalizing typed

/-- Usage-dimension smoke: the linear identity `λx.x` evaluates to a `.lam` (in zero steps). -/
theorem usageLinearIdentity_reducesToLam :
    ∃ body, GradedLambda.ReducesStar (.lam (.var 0)) (.lam body) :=
  closedReducesToLam fxUsageSemiring_isLawful usageLinearIdentity_typedViaGeneric

end FX1Poly.Modal
