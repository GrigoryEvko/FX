import FX1Poly.Modal.GradedLinearTime
import FX1Poly.Modal.GradedSubjectReductionGeneric

/-! # FX1Poly/Modal/GradedLinearTimeBound
    — ★ COST-2a: strict-linear terms normalize in fewer than `size` steps, under ANY strategy

The linear-time theorem.  Strict-linear subject reduction (weakening +
substitution mirrored from the generic graded metatheory with the binder
grade pinned to `one`, the judgment-free `substInto`/`insertAt` vector
algebra reused verbatim), the per-step size decrease, and the assembly:

  * `HasStrictLinearGrade.weakening` / `.substitution` /
    `.betaPreservation` — the strict mirrors of the generic graded
    metatheory (#903/#905); grades are preserved EXACTLY under β.
  * `HasStrictLinearGrade.subjectReduction` — full one-step SR
    (β via the substitution lemma; congruences rebuild).
  * `HasStrictLinearGrade.stepDecreasesSize` — EVERY `Reduces` step on
    a strict-linear term strictly decreases size (β via brick 2's
    `betaShrinks`; congruences via the inversion + IH).
  * ★ `HasStrictLinearGrade.linearTime` — `steps < size`: every
    `ReducesInSteps` chain from a strict-linear term — under ANY
    strategy, to ANY target — is shorter than the term's size.  Linear
    terms evaluate in linear time.  (COST-1's `costBound_isSound` bounds
    chains by the computed bound; this theorem bounds them by the SIZE,
    read off the grades through `countBound`.)
  * The β-NON-SHRINK witnesses: the SAME syntactic duplicator redex is
    graded at binder grade ZERO (affine 0-scaling leak) or OMEGA
    (genuine duplication) depending on the function type, and its
    β-reduct has size EQUAL to the redex (11 = 11) — strict decrease
    fails outside the strict fragment in both gradings, so the
    strictness hypothesis is exactly right.

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Modal

/-! ## Strict inversions -/

/-- Strict inversion for a lambda: the arrow's binder grade is `one` and
the body is strictly typed under the extended context. -/
theorem HasStrictLinearGrade.invertLam {typeContext : List (GTypeOver fxUsageSemiring)}
    {grades : GradeVectorOver fxUsageSemiring} {body : GradedLambda}
    {resultType : GTypeOver fxUsageSemiring}
    (typed : HasStrictLinearGrade typeContext grades (.lam body) resultType) :
    ∃ (domain codomain : GTypeOver fxUsageSemiring),
      resultType = .arrow fxUsageSemiring.one domain codomain ∧
        HasStrictLinearGrade (domain :: typeContext)
          (GradeVectorOver.cons fxUsageSemiring.one grades) body codomain := by
  cases typed with
  | lam _ domain codomain _ _ bodyTyped => exact ⟨domain, codomain, rfl, bodyTyped⟩

/-- Strict inversion for an application: function at a grade-`one` arrow,
grades the strict App combination. -/
theorem HasStrictLinearGrade.invertApp {typeContext : List (GTypeOver fxUsageSemiring)}
    {grades : GradeVectorOver fxUsageSemiring} {function argument : GradedLambda}
    {resultType : GTypeOver fxUsageSemiring}
    (typed : HasStrictLinearGrade typeContext grades (.app function argument) resultType) :
    ∃ (domain : GTypeOver fxUsageSemiring)
      (functionGrades argumentGrades : GradeVectorOver fxUsageSemiring),
      HasStrictLinearGrade typeContext functionGrades function
        (.arrow fxUsageSemiring.one domain resultType) ∧
        HasStrictLinearGrade typeContext argumentGrades argument domain ∧
          grades = GradeVectorOver.add functionGrades
            (GradeVectorOver.scale fxUsageSemiring.one argumentGrades) := by
  cases typed with
  | app _ domain codomain functionGrades argumentGrades _ _ functionTyped argumentTyped =>
      exact ⟨domain, functionGrades, argumentGrades, functionTyped, argumentTyped, rfl⟩

/-! ## Strict weakening and substitution (mirrors of #903/#905, binder grade pinned) -/

/-- Strict weakening: inserting an unused (`zero`-graded) binding
preserves strict-linear typing (the mirror of `hasGradeOver_weakening`;
the vector algebra is reused verbatim). -/
theorem HasStrictLinearGrade.weakening {typeContext : List (GTypeOver fxUsageSemiring)}
    {grades : GradeVectorOver fxUsageSemiring} {term : GradedLambda}
    {resultType : GTypeOver fxUsageSemiring}
    (typed : HasStrictLinearGrade typeContext grades term resultType) :
    ∀ (cutDepth : Nat) (newBinding : GTypeOver fxUsageSemiring),
      cutDepth ≤ typeContext.length →
      HasStrictLinearGrade (insertTypeAtOver cutDepth newBinding typeContext)
        (GradeVectorOver.insertAt cutDepth fxUsageSemiring.zero grades)
        (GradedLambda.shift cutDepth term) resultType := by
  induction typed with
  | var typeContext index varType lookupOk =>
      intro cutDepth newBinding cutLe
      rcases Nat.lt_or_ge index cutDepth with indexLtCut | indexGeCut
      · have shiftEq : GradedLambda.shift cutDepth (GradedLambda.var index) =
            GradedLambda.var index := by
          show (if index < cutDepth then GradedLambda.var index
            else GradedLambda.var (index + 1)) = GradedLambda.var index
          rw [if_pos indexLtCut]
        rw [shiftEq,
            GradeVectorOver.single_insertAt_lt fxUsageSemiring.one cutDepth
              typeContext.length index indexLtCut (Nat.lt_of_lt_of_le indexLtCut cutLe),
            ← length_insertTypeAtOver cutDepth newBinding typeContext]
        exact HasStrictLinearGrade.var (insertTypeAtOver cutDepth newBinding typeContext)
          index varType
          (by rw [lookup_insertTypeAtOver_lt newBinding cutDepth index typeContext
                indexLtCut cutLe]
              exact lookupOk)
      · have shiftEq : GradedLambda.shift cutDepth (GradedLambda.var index)
            = GradedLambda.var (index + 1) := by
          show (if index < cutDepth then GradedLambda.var index
            else GradedLambda.var (index + 1)) = GradedLambda.var (index + 1)
          rw [if_neg (Nat.not_lt.mpr indexGeCut)]
        rw [shiftEq,
            GradeVectorOver.single_insertAt_ge fxUsageSemiring.one cutDepth
              typeContext.length index indexGeCut
              (lookup_some_ltOver typeContext index varType lookupOk),
            ← length_insertTypeAtOver cutDepth newBinding typeContext]
        exact HasStrictLinearGrade.var (insertTypeAtOver cutDepth newBinding typeContext)
          (index + 1) varType
          (by rw [lookup_insertTypeAtOver_ge newBinding cutDepth index typeContext indexGeCut]
              exact lookupOk)
  | lam typeContext domain codomain outerGrades body _ bodyIH =>
      intro cutDepth newBinding cutLe
      show HasStrictLinearGrade (insertTypeAtOver cutDepth newBinding typeContext)
        (GradeVectorOver.insertAt cutDepth fxUsageSemiring.zero outerGrades)
        (GradedLambda.lam (GradedLambda.shift (cutDepth + 1) body))
        (GTypeOver.arrow fxUsageSemiring.one domain codomain)
      exact HasStrictLinearGrade.lam (insertTypeAtOver cutDepth newBinding typeContext)
        domain codomain (GradeVectorOver.insertAt cutDepth fxUsageSemiring.zero outerGrades)
        (GradedLambda.shift (cutDepth + 1) body)
        (bodyIH (cutDepth + 1) newBinding (Nat.succ_le_succ cutLe))
  | app typeContext domain codomain functionGrades argumentGrades function argument
      functionTyped argumentTyped functionIH argumentIH =>
      intro cutDepth newBinding cutLe
      have lenScale : (GradeVectorOver.scale fxUsageSemiring.one argumentGrades).length =
          typeContext.length := by
        rw [GradeVectorOver.scale_length]
        exact hasGradeOver_length argumentTyped.toGraded
      have gradeEq : GradeVectorOver.insertAt cutDepth fxUsageSemiring.zero
          (GradeVectorOver.add functionGrades
            (GradeVectorOver.scale fxUsageSemiring.one argumentGrades)) =
            GradeVectorOver.add
              (GradeVectorOver.insertAt cutDepth fxUsageSemiring.zero functionGrades)
              (GradeVectorOver.scale fxUsageSemiring.one
                (GradeVectorOver.insertAt cutDepth fxUsageSemiring.zero argumentGrades)) := by
        rw [GradeVectorOver.insertAt_add fxUsageSemiring_isLawful cutDepth functionGrades
              (GradeVectorOver.scale fxUsageSemiring.one argumentGrades)
              (by rw [hasGradeOver_length functionTyped.toGraded, lenScale]),
            GradeVectorOver.insertAt_scale fxUsageSemiring_isLawful]
      show HasStrictLinearGrade (insertTypeAtOver cutDepth newBinding typeContext)
        (GradeVectorOver.insertAt cutDepth fxUsageSemiring.zero
          (GradeVectorOver.add functionGrades
            (GradeVectorOver.scale fxUsageSemiring.one argumentGrades)))
        (GradedLambda.app (GradedLambda.shift cutDepth function)
          (GradedLambda.shift cutDepth argument)) codomain
      rw [gradeEq]
      exact HasStrictLinearGrade.app (insertTypeAtOver cutDepth newBinding typeContext)
        domain codomain
        (GradeVectorOver.insertAt cutDepth fxUsageSemiring.zero functionGrades)
        (GradeVectorOver.insertAt cutDepth fxUsageSemiring.zero argumentGrades)
        (GradedLambda.shift cutDepth function) (GradedLambda.shift cutDepth argument)
        (functionIH cutDepth newBinding cutLe) (argumentIH cutDepth newBinding cutLe)

/-- Strict substitution (the mirror of `hasGradeOver_substitution` with
the binder grade pinned to `one`): substituting a strictly-typed
argument for the cut variable preserves strict-linear typing, the grade
vector transformed by the same `substInto` algebra. -/
theorem HasStrictLinearGrade.substitution {ctx : List (GTypeOver fxUsageSemiring)}
    {bodyGrades : GradeVectorOver fxUsageSemiring} {subject : GradedLambda}
    {codomain : GTypeOver fxUsageSemiring}
    (subjectTyped : HasStrictLinearGrade ctx bodyGrades subject codomain) :
    ∀ (cutDepth : Nat) (domain : GTypeOver fxUsageSemiring) (argTerm : GradedLambda)
      (argGrades : GradeVectorOver fxUsageSemiring),
      GTypeOver.lookup ctx cutDepth = some domain →
      HasStrictLinearGrade (removeTypeAtOver cutDepth ctx) argGrades argTerm domain →
      HasStrictLinearGrade (removeTypeAtOver cutDepth ctx)
        (GradeVectorOver.substInto cutDepth argGrades bodyGrades)
        (GradedLambda.substAt cutDepth argTerm subject) codomain := by
  induction subjectTyped with
  | var ctx index varType lookupOk =>
      intro cutDepth domain argTerm argGrades domainLookup argTyped
      have cutLt : cutDepth < ctx.length := lookup_some_ltOver ctx cutDepth domain domainLookup
      have argLen : argGrades.length = (removeTypeAtOver cutDepth ctx).length :=
        hasGradeOver_length argTyped.toGraded
      have ctxLenEq : (removeTypeAtOver cutDepth ctx).length + 1 = ctx.length :=
        removeTypeAtOver_length cutDepth ctx cutLt
      have cutLeRl : cutDepth ≤ (removeTypeAtOver cutDepth ctx).length := by
        have cutLtShifted := cutLt
        rw [← ctxLenEq] at cutLtShifted
        exact Nat.le_of_lt_succ cutLtShifted
      rcases Nat.lt_trichotomy index cutDepth with idxLt | idxEq | idxGt
      · have termEq : GradedLambda.substAt cutDepth argTerm (GradedLambda.var index) =
            GradedLambda.var index := by
          show (if index < cutDepth then GradedLambda.var index
                else if index = cutDepth then argTerm else GradedLambda.var (index - 1)) =
            GradedLambda.var index
          rw [if_pos idxLt]
        rw [termEq,
            show ctx.length = (removeTypeAtOver cutDepth ctx).length + 1 from ctxLenEq.symm,
            GradeVectorOver.substInto_single_lt fxUsageSemiring_isLawful cutDepth index
              (removeTypeAtOver cutDepth ctx).length argGrades idxLt cutLeRl argLen]
        exact HasStrictLinearGrade.var (removeTypeAtOver cutDepth ctx) index varType
          (by rw [lookup_removeTypeAtOver_lt cutDepth index ctx idxLt]; exact lookupOk)
      · subst idxEq
        have termEq : GradedLambda.substAt index argTerm (GradedLambda.var index) = argTerm := by
          show (if index < index then GradedLambda.var index
                else if index = index then argTerm else GradedLambda.var (index - 1)) = argTerm
          rw [if_neg (Nat.lt_irrefl index), if_pos rfl]
        have typeEq : varType = domain := Option.some.inj (lookupOk.symm.trans domainLookup)
        rw [termEq,
            show ctx.length = (removeTypeAtOver index ctx).length + 1 from ctxLenEq.symm,
            GradeVectorOver.substInto_single_self fxUsageSemiring_isLawful index
              (removeTypeAtOver index ctx).length argGrades cutLeRl argLen, typeEq]
        exact argTyped
      · have indexPos : 0 < index := Nat.lt_of_le_of_lt (Nat.zero_le cutDepth) idxGt
        obtain ⟨predIndex, predEq⟩ : ∃ predIndex, index = predIndex + 1 :=
          ⟨index - 1, (Nat.succ_pred_eq_of_pos indexPos).symm⟩
        subst predEq
        have cutLePred : cutDepth ≤ predIndex := Nat.le_of_lt_succ idxGt
        have predLt : predIndex < (removeTypeAtOver cutDepth ctx).length := by
          have boundShifted := lookup_some_ltOver ctx (predIndex + 1) varType lookupOk
          rw [← ctxLenEq] at boundShifted
          exact Nat.lt_of_succ_lt_succ boundShifted
        have termEq : GradedLambda.substAt cutDepth argTerm (GradedLambda.var (predIndex + 1)) =
            GradedLambda.var predIndex := by
          show (if predIndex + 1 < cutDepth then GradedLambda.var (predIndex + 1)
                else if predIndex + 1 = cutDepth then argTerm
                else GradedLambda.var (predIndex + 1 - 1)) = GradedLambda.var (predIndex + 1 - 1)
          rw [if_neg (Nat.not_lt.mpr (Nat.le_of_lt idxGt)), if_neg (Nat.ne_of_gt idxGt)]
        rw [termEq,
            show ctx.length = (removeTypeAtOver cutDepth ctx).length + 1 from ctxLenEq.symm,
            GradeVectorOver.substInto_single_gt fxUsageSemiring_isLawful cutDepth predIndex
              (removeTypeAtOver cutDepth ctx).length argGrades cutLePred predLt argLen]
        exact HasStrictLinearGrade.var (removeTypeAtOver cutDepth ctx) predIndex varType
          (by rw [lookup_removeTypeAtOver_ge cutDepth predIndex ctx cutLePred]; exact lookupOk)
  | lam ctx dom cod outerGrades innerBody _ innerIH =>
      intro cutDepth domain argTerm argGrades domainLookup argTyped
      show HasStrictLinearGrade (removeTypeAtOver cutDepth ctx)
        (GradeVectorOver.substInto cutDepth argGrades outerGrades)
        (GradedLambda.lam
          (GradedLambda.substAt (cutDepth + 1) (GradedLambda.shift 0 argTerm) innerBody))
        (GTypeOver.arrow fxUsageSemiring.one dom cod)
      apply HasStrictLinearGrade.lam (removeTypeAtOver cutDepth ctx) dom cod
        (GradeVectorOver.substInto cutDepth argGrades outerGrades)
        (GradedLambda.substAt (cutDepth + 1) (GradedLambda.shift 0 argTerm) innerBody)
      rw [← GradeVectorOver.substInto_succ_cons fxUsageSemiring_isLawful cutDepth
            fxUsageSemiring.one argGrades outerGrades]
      exact innerIH (cutDepth + 1) domain (GradedLambda.shift 0 argTerm)
        (GradeVectorOver.cons fxUsageSemiring.zero argGrades) domainLookup
        (argTyped.weakening 0 dom (Nat.zero_le _))
  | app ctx dom cod functionGrades argumentGrades function argument
      functionTyped argumentTyped functionIH argumentIH =>
      intro cutDepth domain argTerm argGrades domainLookup argTyped
      have lenEq : functionGrades.length = argumentGrades.length := by
        rw [hasGradeOver_length functionTyped.toGraded,
          hasGradeOver_length argumentTyped.toGraded]
      show HasStrictLinearGrade (removeTypeAtOver cutDepth ctx)
        (GradeVectorOver.substInto cutDepth argGrades
          (GradeVectorOver.add functionGrades
            (GradeVectorOver.scale fxUsageSemiring.one argumentGrades)))
        (GradedLambda.app (GradedLambda.substAt cutDepth argTerm function)
          (GradedLambda.substAt cutDepth argTerm argument)) cod
      rw [GradeVectorOver.substInto_appGrade fxUsageSemiring_isLawful cutDepth
            fxUsageSemiring.one argGrades functionGrades argumentGrades lenEq]
      exact HasStrictLinearGrade.app (removeTypeAtOver cutDepth ctx) dom cod
        (GradeVectorOver.substInto cutDepth argGrades functionGrades)
        (GradeVectorOver.substInto cutDepth argGrades argumentGrades)
        (GradedLambda.substAt cutDepth argTerm function)
        (GradedLambda.substAt cutDepth argTerm argument)
        (functionIH cutDepth domain argTerm argGrades domainLookup argTyped)
        (argumentIH cutDepth domain argTerm argGrades domainLookup argTyped)

/-- Strict β-preservation: the β-reduct of a strict-linear redex is
strict-linear at the SAME grades (the strict App grade is definitionally
the `substInto 0` of the body's `cons one` vector). -/
theorem HasStrictLinearGrade.betaPreservation {ctx : List (GTypeOver fxUsageSemiring)}
    {grades : GradeVectorOver fxUsageSemiring} {body argTerm : GradedLambda}
    {resultType : GTypeOver fxUsageSemiring}
    (typed : HasStrictLinearGrade ctx grades (.app (.lam body) argTerm) resultType) :
    HasStrictLinearGrade ctx grades (GradedLambda.substAt 0 argTerm body) resultType := by
  obtain ⟨domain, functionGrades, argGrades, functionTyped, argTyped, gradesEq⟩ :=
    typed.invertApp
  obtain ⟨dom', cod', arrowEq, bodyTyped⟩ := functionTyped.invertLam
  injection arrowEq with binderEq domEq codEq
  subst domEq; subst codEq
  rw [gradesEq]
  exact bodyTyped.substitution 0 domain argTerm argGrades rfl argTyped

/-! ## One-step subject reduction and the per-step size decrease -/

/-- Strict-linear SR: one `Reduces` step preserves strict-linear typing
at the SAME grades (β preserves exactly; congruences rebuild). -/
theorem HasStrictLinearGrade.subjectReduction :
    ∀ {source reduct : GradedLambda}, GradedLambda.Reduces source reduct →
      ∀ {ctx : List (GTypeOver fxUsageSemiring)}
        {grades : GradeVectorOver fxUsageSemiring}
        {resultType : GTypeOver fxUsageSemiring},
        HasStrictLinearGrade ctx grades source resultType →
        HasStrictLinearGrade ctx grades reduct resultType := by
  intro source reduct step
  induction step with
  | beta body argument =>
      intro ctx grades resultType typed
      exact typed.betaPreservation
  | congLam body body' bodyStep bodyIH =>
      intro ctx grades resultType typed
      cases typed with
      | lam _ domain codomain _ _ bodyTyped =>
          exact HasStrictLinearGrade.lam ctx domain codomain grades body'
            (bodyIH bodyTyped)
  | congAppLeft function function' argument functionStep functionIH =>
      intro ctx grades resultType typed
      cases typed with
      | app _ domain _ functionGrades argumentGrades _ _ functionTyped argumentTyped =>
          exact HasStrictLinearGrade.app ctx domain resultType functionGrades argumentGrades
            function' argument (functionIH functionTyped) argumentTyped
  | congAppRight function argument argument' argumentStep argumentIH =>
      intro ctx grades resultType typed
      cases typed with
      | app _ domain _ functionGrades argumentGrades _ _ functionTyped argumentTyped =>
          exact HasStrictLinearGrade.app ctx domain resultType functionGrades argumentGrades
            function argument' functionTyped (argumentIH argumentTyped)

/-- EVERY `Reduces` step on a strict-linear term strictly decreases its
size: β via `betaShrinks`, congruences via the inversion and the IH. -/
theorem HasStrictLinearGrade.stepDecreasesSize :
    ∀ {source reduct : GradedLambda}, GradedLambda.Reduces source reduct →
      ∀ {ctx : List (GTypeOver fxUsageSemiring)}
        {grades : GradeVectorOver fxUsageSemiring}
        {resultType : GTypeOver fxUsageSemiring},
        HasStrictLinearGrade ctx grades source resultType →
        reduct.size < source.size := by
  intro source reduct step
  induction step with
  | beta body argument =>
      intro ctx grades resultType typed
      exact typed.betaShrinks
  | congLam body body' bodyStep bodyIH =>
      intro ctx grades resultType typed
      cases typed with
      | lam _ _ _ _ _ bodyTyped =>
          exact Nat.succ_lt_succ (bodyIH bodyTyped)
  | congAppLeft function function' argument functionStep functionIH =>
      intro ctx grades resultType typed
      cases typed with
      | app _ _ _ _ _ _ _ functionTyped _ =>
          exact Nat.succ_lt_succ
            (Nat.add_lt_add_right (functionIH functionTyped) argument.size)
  | congAppRight function argument argument' argumentStep argumentIH =>
      intro ctx grades resultType typed
      cases typed with
      | app _ _ _ _ _ _ _ _ argumentTyped =>
          exact Nat.succ_lt_succ
            (Nat.add_lt_add_left (argumentIH argumentTyped) function.size)

/-! ## ★ The linear-time bound -/

/-- ★ **COST-2a — linear terms evaluate in linear time, under ANY
strategy**: every step-counted reduction chain from a strict-linear term
(to ANY target, not only normal forms) is strictly shorter than the
term's size.  Each step strictly decreases the size (the grade-`one`
binder promise bounds every β-redex's duplication through `countBound`),
and subject reduction keeps the invariant along the chain. -/
theorem HasStrictLinearGrade.linearTime {ctx : List (GTypeOver fxUsageSemiring)}
    {grades : GradeVectorOver fxUsageSemiring} {term : GradedLambda}
    {resultType : GTypeOver fxUsageSemiring}
    (typed : HasStrictLinearGrade ctx grades term resultType) :
    ∀ {steps : Nat} {target : GradedLambda},
      GradedLambda.ReducesInSteps term steps target → steps < term.size := by
  intro steps target chain
  induction chain with
  | refl term => exact term.size_pos
  | head step rest restIH =>
      exact Nat.lt_of_lt_of_le
        (Nat.succ_lt_succ (restIH (typed.subjectReduction step)))
        (typed.stepDecreasesSize step)

/-- The end-to-end smoke: the strictly-linear identity application
normalizes within its size bound — `1` step, size `5`. -/
theorem identityApplication_linearTime :
    (1 : Nat) < (GradedLambda.app (.lam (.var 0)) (.lam (.var 0))).size :=
  (HasStrictLinearGrade.app [] (.arrow fxUsageSemiring.one .base .base)
      (.arrow fxUsageSemiring.one .base .base)
      GradeVectorOver.nil GradeVectorOver.nil (.lam (.var 0)) (.lam (.var 0))
      (HasStrictLinearGrade.lam [] (.arrow fxUsageSemiring.one .base .base)
        (.arrow fxUsageSemiring.one .base .base) GradeVectorOver.nil (.var 0)
        (HasStrictLinearGrade.var [.arrow fxUsageSemiring.one .base .base] 0
          (.arrow fxUsageSemiring.one .base .base) rfl))
      (HasStrictLinearGrade.lam [] .base .base GradeVectorOver.nil (.var 0)
        (HasStrictLinearGrade.var [.base] 0 .base rfl))).linearTime
    GradedLambda.identityRedex_costsOneStep

/-! ## The β-NON-SHRINK witnesses — strictness is exactly right

The SAME syntactic duplicator redex `(λx. (f x) x) ((λz.z) y)` carries
binder grade ZERO (the affine 0-scaling leak, brick 2) or OMEGA (genuine
duplication) depending on `f`'s type — and in BOTH gradings its β-reduct
has size EQUAL to the redex (11 = 11): the strict size decrease fails
outside the strict fragment. -/

/-- The size-4 argument `(λz. z) y` the duplicator copies. -/
def duplicatedArgument : GradedLambda := .app (.lam (.var 0)) (.var 1)

/-- **β does NOT shrink the duplicator redex**: the reduct's size equals
the redex's (both `11`) — the strict decrease genuinely needs the
`count ≤ 1` promise only the strict fragment provides. -/
theorem duplicatorRedex_betaDoesNotShrink :
    ¬ (GradedLambda.substAt 0 duplicatedArgument affineDuplicatorBody).size
        < (GradedLambda.app (.lam affineDuplicatorBody) duplicatedArgument).size :=
  fun shrink => Nat.lt_irrefl 11 shrink

/-- The duplicating-at-omega function type `base -ω→ base -ω→ base`. -/
def omegaFunctionType : GTypeOver fxUsageSemiring :=
  .arrow UsageGrade.omega .base (.arrow UsageGrade.omega .base .base)

/-- The OMEGA twin of the brick-2 affine leak: the SAME duplicator
lambda types at binder grade OMEGA over an `ω`-arrow function — genuine
duplication, graded honestly as unrestricted. -/
theorem omegaDuplicatorLam_typedAtGradeOmega :
    HasGradeOver fxUsageSemiring [omegaFunctionType, .base]
      (GradeVectorOver.cons UsageGrade.one (GradeVectorOver.cons UsageGrade.zero
        GradeVectorOver.nil))
      (.lam affineDuplicatorBody) (.arrow UsageGrade.omega .base .base) :=
  HasGradeOver.lam [omegaFunctionType, .base] UsageGrade.omega .base .base
    (GradeVectorOver.cons UsageGrade.one (GradeVectorOver.cons UsageGrade.zero
      GradeVectorOver.nil))
    affineDuplicatorBody
    (HasGradeOver.app (.base :: [omegaFunctionType, .base]) UsageGrade.omega
      .base .base
      (GradeVectorOver.add
        (GradeVectorOver.single fxUsageSemiring 3 1 fxUsageSemiring.one)
        (GradeVectorOver.scale UsageGrade.omega
          (GradeVectorOver.single fxUsageSemiring 3 0 fxUsageSemiring.one)))
      (GradeVectorOver.single fxUsageSemiring 3 0 fxUsageSemiring.one)
      (.app (.var 1) (.var 0)) (.var 0)
      (HasGradeOver.app (.base :: [omegaFunctionType, .base]) UsageGrade.omega
        .base (.arrow UsageGrade.omega .base .base)
        (GradeVectorOver.single fxUsageSemiring 3 1 fxUsageSemiring.one)
        (GradeVectorOver.single fxUsageSemiring 3 0 fxUsageSemiring.one)
        (.var 1) (.var 0)
        (HasGradeOver.var (.base :: [omegaFunctionType, .base]) 1 omegaFunctionType rfl)
        (HasGradeOver.var (.base :: [omegaFunctionType, .base]) 0 .base rfl))
      (HasGradeOver.var (.base :: [omegaFunctionType, .base]) 0 .base rfl))

end FX1Poly.Modal
