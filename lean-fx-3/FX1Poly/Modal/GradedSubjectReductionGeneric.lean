import FX1Poly.Modal.GradedSubstitutionGeneric

/-! # FX1Poly/Modal/GradedSubjectReductionGeneric — generic substitution + β SR (all graded dimensions)

The SUBSTITUTION lemma and β subject reduction are the SAME argument for every dimension — they thread
the `substInto` grade-algebra through the typing derivation.  This file ships them ONCE, generic over
any `OrderedGradeSemiring`, completing the generic reduction metatheory (weakening and the substInto
grade-algebra).

  * `hasGradeOver_substitution` — **graded substitution**: substituting `argTerm` (typed at grade vector
    `argGrades` in the context with the cut binding removed) for the variable at `cutDepth` in `subject`
    preserves typing, with the grade vector transformed by `substInto cutDepth argGrades`.  By induction
    on the derivation: the var case trichotomizes below / at / above the cut (via `substInto_single_lt`/
    `_self`/`_gt`); the λ-case threads via `substInto_succ_cons` and front-weakening
    (`hasGradeOver_weakening` at cut 0); the App-case via `substInto_appGrade`.
  * `hasGradeOver_betaPreservation` — **β subject reduction**: `(λ.body) arg ↝ body[0 := arg]` preserves
    typing AND the grade vector EXACTLY.  Invert App + Lam (`HasGradeOver.invertApp`/`invertLam`), then
    the substitution lemma at cut 0, where `substInto 0 argGrades (cons binderGrade functionGrades)` is
    definitionally `functionGrades + binderGrade · argGrades` = the redex's grade.  This is the generic
    statement that the corrected Wood/Atkey App scaling makes the judgment sound under reduction — for
    EVERY dimension, not just usage.

The witness `securityBeta_smoke` exercises β subject reduction in the SECURITY dimension: the security
identity applied to itself reduces with its security grade vector preserved, with no security-specific SR
proof — the orthogonal-composition thesis at the subject-reduction layer.

The lawful bundle is threaded throughout (the substitution lemma consumes the `substInto_*`
lemmas and weakening, all of which take `lawful`); the derivation-structural skeleton (the
var-trichotomy, the λ/App threading) is identical to the usage dimension's concrete proof.

## Zero-axiom verification

`hasGradeOver_substitution` is a derivation induction; the var case computes `substAt` with `if_pos`/
`if_neg` and relocates the grade with the `substInto_single_*` lemmas; the λ/App cases rewrite
with `substInto_succ_cons`/`substInto_appGrade` and reassemble via the constructors.
`hasGradeOver_betaPreservation` inverts + `injection`s the arrow equality + substitutes at cut 0.  The
Nat lemmas (`Nat.lt_trichotomy`, `Nat.succ_pred_eq_of_pos`, `Nat.lt_irrefl`, `Nat.ne_of_gt`, …) and
`Option.some.inj` are the same propext-free lemmas the usage dimension uses.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega` (every declaration probed with `#print axioms`
before landing).  Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- **Graded substitution**: substituting `argTerm` (typed at grade vector `argGrades` in the context
with the cut binding removed) for the variable at `cutDepth` in `subject` preserves typing, with the
grade vector transformed by `substInto cutDepth argGrades`.  By induction on the derivation: the var
case trichotomizes below / at / above the cut; the λ-case threads via `substInto_succ_cons` and
front-weakening (`hasGradeOver_weakening` at cut 0); the App-case via `substInto_appGrade`. -/
theorem hasGradeOver_substitution {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) {ctx : List (GTypeOver R)}
    {bodyGrades : GradeVectorOver R} {subject : GradedLambda} {codomain : GTypeOver R}
    (subjectTyped : HasGradeOver R ctx bodyGrades subject codomain) :
    ∀ (cutDepth : Nat) (domain : GTypeOver R) (argTerm : GradedLambda)
      (argGrades : GradeVectorOver R),
      GTypeOver.lookup ctx cutDepth = some domain →
      HasGradeOver R (removeTypeAtOver cutDepth ctx) argGrades argTerm domain →
      HasGradeOver R (removeTypeAtOver cutDepth ctx)
        (GradeVectorOver.substInto cutDepth argGrades bodyGrades)
        (GradedLambda.substAt cutDepth argTerm subject) codomain := by
  induction subjectTyped with
  | var ctx index varType lookupOk =>
      intro cutDepth domain argTerm argGrades domainLookup argTyped
      have cutLt : cutDepth < ctx.length := lookup_some_ltOver ctx cutDepth domain domainLookup
      have argLen : argGrades.length = (removeTypeAtOver cutDepth ctx).length :=
        hasGradeOver_length argTyped
      have ctxLenEq : (removeTypeAtOver cutDepth ctx).length + 1 = ctx.length :=
        removeTypeAtOver_length cutDepth ctx cutLt
      have cutLeRl : cutDepth ≤ (removeTypeAtOver cutDepth ctx).length := by
        have h := cutLt; rw [← ctxLenEq] at h; exact Nat.le_of_lt_succ h
      rcases Nat.lt_trichotomy index cutDepth with idxLt | idxEq | idxGt
      · have termEq : GradedLambda.substAt cutDepth argTerm (GradedLambda.var index) =
            GradedLambda.var index := by
          show (if index < cutDepth then GradedLambda.var index
                else if index = cutDepth then argTerm else GradedLambda.var (index - 1)) =
            GradedLambda.var index
          rw [if_pos idxLt]
        rw [termEq, show ctx.length = (removeTypeAtOver cutDepth ctx).length + 1 from ctxLenEq.symm,
            GradeVectorOver.substInto_single_lt lawful cutDepth index
              (removeTypeAtOver cutDepth ctx).length argGrades idxLt cutLeRl argLen]
        exact HasGradeOver.var (removeTypeAtOver cutDepth ctx) index varType
          (by rw [lookup_removeTypeAtOver_lt cutDepth index ctx idxLt]; exact lookupOk)
      · subst index
        have termEq : GradedLambda.substAt cutDepth argTerm (GradedLambda.var cutDepth) = argTerm := by
          show (if cutDepth < cutDepth then GradedLambda.var cutDepth
                else if cutDepth = cutDepth then argTerm else GradedLambda.var (cutDepth - 1)) = argTerm
          rw [if_neg (Nat.lt_irrefl cutDepth), if_pos rfl]
        have typeEq : varType = domain := Option.some.inj (lookupOk.symm.trans domainLookup)
        rw [termEq, show ctx.length = (removeTypeAtOver cutDepth ctx).length + 1 from ctxLenEq.symm,
            GradeVectorOver.substInto_single_self lawful cutDepth
              (removeTypeAtOver cutDepth ctx).length argGrades cutLeRl argLen, typeEq]
        exact argTyped
      · have pos : 0 < index := Nat.lt_of_le_of_lt (Nat.zero_le cutDepth) idxGt
        obtain ⟨predIndex, hpred⟩ : ∃ predIndex, index = predIndex + 1 :=
          ⟨index - 1, (Nat.succ_pred_eq_of_pos pos).symm⟩
        subst hpred
        have cutLePred : cutDepth ≤ predIndex := Nat.le_of_lt_succ idxGt
        have predLt : predIndex < (removeTypeAtOver cutDepth ctx).length := by
          have h := lookup_some_ltOver ctx (predIndex + 1) varType lookupOk
          rw [← ctxLenEq] at h; exact Nat.lt_of_succ_lt_succ h
        have termEq : GradedLambda.substAt cutDepth argTerm (GradedLambda.var (predIndex + 1)) =
            GradedLambda.var predIndex := by
          show (if predIndex + 1 < cutDepth then GradedLambda.var (predIndex + 1)
                else if predIndex + 1 = cutDepth then argTerm
                else GradedLambda.var (predIndex + 1 - 1)) = GradedLambda.var (predIndex + 1 - 1)
          rw [if_neg (Nat.not_lt.mpr (Nat.le_of_lt idxGt)), if_neg (Nat.ne_of_gt idxGt)]
        rw [termEq, show ctx.length = (removeTypeAtOver cutDepth ctx).length + 1 from ctxLenEq.symm,
            GradeVectorOver.substInto_single_gt lawful cutDepth predIndex
              (removeTypeAtOver cutDepth ctx).length argGrades cutLePred predLt argLen]
        exact HasGradeOver.var (removeTypeAtOver cutDepth ctx) predIndex varType
          (by rw [lookup_removeTypeAtOver_ge cutDepth predIndex ctx cutLePred]; exact lookupOk)
  | lam ctx binderGrade dom cod outerGrades innerBody _ innerIH =>
      intro cutDepth domain argTerm argGrades domainLookup argTyped
      show HasGradeOver R (removeTypeAtOver cutDepth ctx)
        (GradeVectorOver.substInto cutDepth argGrades outerGrades)
        (GradedLambda.lam (GradedLambda.substAt (cutDepth + 1) (GradedLambda.shift 0 argTerm) innerBody))
        (GTypeOver.arrow binderGrade dom cod)
      apply HasGradeOver.lam (removeTypeAtOver cutDepth ctx) binderGrade dom cod
        (GradeVectorOver.substInto cutDepth argGrades outerGrades)
        (GradedLambda.substAt (cutDepth + 1) (GradedLambda.shift 0 argTerm) innerBody)
      rw [← GradeVectorOver.substInto_succ_cons lawful cutDepth binderGrade argGrades outerGrades]
      exact innerIH (cutDepth + 1) domain (GradedLambda.shift 0 argTerm)
        (GradeVectorOver.cons R.zero argGrades) domainLookup
        (hasGradeOver_weakening lawful argTyped 0 dom (Nat.zero_le _))
  | app ctx binderGrade dom cod functionGrades argumentGrades function argument
      functionTyped argumentTyped functionIH argumentIH =>
      intro cutDepth domain argTerm argGrades domainLookup argTyped
      have lenEq : functionGrades.length = argumentGrades.length := by
        rw [hasGradeOver_length functionTyped, hasGradeOver_length argumentTyped]
      show HasGradeOver R (removeTypeAtOver cutDepth ctx)
        (GradeVectorOver.substInto cutDepth argGrades
          (GradeVectorOver.add functionGrades (GradeVectorOver.scale binderGrade argumentGrades)))
        (GradedLambda.app (GradedLambda.substAt cutDepth argTerm function)
          (GradedLambda.substAt cutDepth argTerm argument)) cod
      rw [GradeVectorOver.substInto_appGrade lawful cutDepth binderGrade argGrades functionGrades
            argumentGrades lenEq]
      exact HasGradeOver.app (removeTypeAtOver cutDepth ctx) binderGrade dom cod
        (GradeVectorOver.substInto cutDepth argGrades functionGrades)
        (GradeVectorOver.substInto cutDepth argGrades argumentGrades)
        (GradedLambda.substAt cutDepth argTerm function)
        (GradedLambda.substAt cutDepth argTerm argument)
        (functionIH cutDepth domain argTerm argGrades domainLookup argTyped)
        (argumentIH cutDepth domain argTerm argGrades domainLookup argTyped)

/-- **β subject reduction**: the type-coupled graded judgment is preserved under β, with the grade
vector preserved EXACTLY — the generic statement that the corrected Wood/Atkey App scaling makes the
judgment sound under reduction, for every dimension.  `(λ.body) arg ↝ body[0 := arg]`: invert App +
Lam, then the substitution lemma at cut 0, where `substInto 0 argGrades (cons binderGrade
functionGrades)` is definitionally `functionGrades + binderGrade · argGrades` = the redex's grade. -/
theorem hasGradeOver_betaPreservation {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) {ctx : List (GTypeOver R)}
    {grades : GradeVectorOver R} {body argTerm : GradedLambda} {resultType : GTypeOver R}
    (typed : HasGradeOver R ctx grades (.app (.lam body) argTerm) resultType) :
    HasGradeOver R ctx grades (GradedLambda.substAt 0 argTerm body) resultType := by
  obtain ⟨binderGrade, domain, functionGrades, argGrades, functionTyped, argTyped, gradesEq⟩ :=
    HasGradeOver.invertApp typed
  obtain ⟨binderGrade', dom', cod', arrowEq, bodyTyped⟩ := HasGradeOver.invertLam functionTyped
  injection arrowEq with bgEq domEq codEq
  subst bgEq; subst domEq; subst codEq
  rw [gradesEq]
  exact hasGradeOver_substitution lawful bodyTyped 0 domain argTerm argGrades rfl argTyped

/-- **β subject reduction in the SECURITY dimension.**  The security identity applied to itself
reduces with its security grade vector preserved — no security-specific SR proof, the shared
`hasGradeOver_betaPreservation` at `fxSecuritySemiring`.  The orthogonal-composition thesis at the
subject-reduction layer. -/
theorem securityBeta_smoke
    (typed : HasGradeOver fxSecuritySemiring [] GradeVectorOver.nil
      (.app (.lam (.var 0)) (.lam (.var 0)))
      (.arrow fxSecuritySemiring.one GTypeOver.base GTypeOver.base)) :
    HasGradeOver fxSecuritySemiring [] GradeVectorOver.nil
      (GradedLambda.substAt 0 (.lam (.var 0)) (.var 0))
      (.arrow fxSecuritySemiring.one GTypeOver.base GTypeOver.base) :=
  hasGradeOver_betaPreservation fxSecuritySemiring_isLawful typed

end FX1Poly.Modal
