import FX1Poly.Modal.GradedNormalization
import FX1Poly.Modal.GradeErasureGeneric

/-! # FX1Poly/Modal/GradedProgress — PROGRESS / canonical forms for the generic graded engine

The second half of type safety for the generic graded calculus `HasGradeOver R`
(`GradedTypingGeneric.lean`).  PRESERVATION is the shipped β subject reduction
(`hasGradeOver_betaPreservation`, #905/#906); PROGRESS is here: a closed well-typed term is never
STUCK — it either β-reduces or is a `.lam` value.  The two together are the standard "well-typed
programs don't go wrong" pairing, and they hold generically over EVERY graded dimension `R` at once.

The load-bearing structural fact is **canonical forms**: a CLOSED (typed in the empty context `[]`)
normal form is a `.lam`.  In the pure λ-fragment a normal form is either a `.lam` or a neutral spine
`(var i) a₁ … aₙ`; the neutral case has a free head variable, which cannot typecheck in `[]` — so a
closed normal form is always a `.lam`.  There are NO closed stuck neutrals.

Where this sits in the safety story for the graded engine:

  * PRESERVATION — `hasGradeOver_betaPreservation` (β SR, grade vector preserved exactly).
  * PROGRESS — `closedWellTypedProgress` (this file): closed well-typed ⟹ reduces or is a `.lam`.
  * TERMINATION — `HasGradeOver.stronglyNormalizing` (SN via grade erasure, #878).
  * EXCLUSION — `selfApplicationLambda_untypableOver` (`λx.xx` / `Ω` untypable, the occurs-check):
    the non-normalizing terms are not even typable.

Declarations:

  * **`closedNormalFormIsLam`** — CANONICAL FORMS: a closed (typed in `[]`) normal form is a `.lam`.
    Structural induction on the term; the `var` case dies because `GTypeOver.lookup [] index = none`
    (no closed variable), and the `app` case dies because its function part would be a closed normal
    form, hence (by the induction hypothesis) a `.lam`, making the application a β-redex — contradicting
    normality.
  * **`closedWellTypedProgress`** — PROGRESS: a closed well-typed term either β-reduces (with an
    explicit reduct) or is a `.lam` value.  `GradedLambda.stepOrNormal` splits step-or-normal; the
    normal branch is closed by canonical forms.
  * **`closedBaseTypeAlwaysSteps`** — a closed well-typed term of BASE type always β-reduces: base has
    no closed values, because the only closed values are `.lam`s and a `.lam` is typed at an arrow,
    never at `base`.  (The pure graded STLC over an uninterpreted base has no closed base-type values.)

## Zero-axiom verification

Structural `induction` on `GradedLambda` (a plain inductive), the shipped inversions
(`invertVar` / `invertApp` / `invertLam`, themselves `cases` + `rfl`), `cases` on the definitional
context lookup `GTypeOver.lookup [] _ = some _` and on the `base = arrow` clash (both constructor
discriminations on plain inductives, propext-clean), and `GradedLambda.stepOrNormal` (structural
recursion).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`
(every declaration probed with `#print axioms` before landing).  Per-declaration audit-gated in
`FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- **Canonical forms.**  A CLOSED (typed in the empty context `[]`) normal form is a `.lam`.  There
are no closed stuck neutrals: a `var` cannot typecheck in `[]` (`GTypeOver.lookup [] _ = none`), and a
top-level application's function part would itself be a closed normal form — hence a `.lam` by the
induction hypothesis — making the whole term a β-redex, contradicting normality. -/
theorem closedNormalFormIsLam {R : OrderedGradeSemiring} (term : GradedLambda) :
    ∀ {grades : GradeVectorOver R} {resultType : GTypeOver R},
      HasGradeOver R [] grades term resultType → GradedLambda.IsNormalForm term →
        ∃ body, term = .lam body := by
  induction term with
  | var index =>
      intro grades resultType typed _
      obtain ⟨lookupOk, _⟩ := HasGradeOver.invertVar typed
      -- lookupOk : GTypeOver.lookup [] index = some resultType, but the lookup is `none`.
      cases lookupOk
  | lam body _ =>
      intro grades resultType _ _
      exact ⟨body, rfl⟩
  | app function argument functionIH _ =>
      intro grades resultType typed normal
      obtain ⟨functionBinderGrade, functionDomain, functionGrades, argumentGrades,
        functionTyped, _, _⟩ := HasGradeOver.invertApp typed
      have functionNF : GradedLambda.IsNormalForm function := by
        intro reduct step
        exact normal (GradedLambda.Reduces.congAppLeft function reduct argument step)
      obtain ⟨functionBody, functionEq⟩ := functionIH functionTyped functionNF
      subst functionEq
      -- function = .lam functionBody, so `.app (.lam functionBody) argument` is a β-redex.
      exact (normal (GradedLambda.Reduces.beta functionBody argument)).elim

/-- **Progress.**  A closed well-typed term either β-reduces (with an explicit reduct) or is a `.lam`
value — it is never stuck.  Combined with the β subject reduction (`hasGradeOver_betaPreservation`),
this is the full "well-typed graded programs don't go wrong" guarantee, generic over every dimension. -/
theorem closedWellTypedProgress {R : OrderedGradeSemiring} {grades : GradeVectorOver R}
    {term : GradedLambda} {resultType : GTypeOver R}
    (typed : HasGradeOver R [] grades term resultType) :
    (∃ reduct, GradedLambda.Reduces term reduct) ∨ (∃ body, term = .lam body) := by
  cases GradedLambda.stepOrNormal term with
  | inl stepWitness => exact Or.inl ⟨stepWitness.1, stepWitness.2⟩
  | inr normal => exact Or.inr (closedNormalFormIsLam term typed normal)

/-- A closed well-typed term of BASE type always β-reduces — the base type has no closed values.  The
only closed values are `.lam`s, and a `.lam` is typed at an arrow, never at `base`; so progress's
value branch is impossible and the term must step. -/
theorem closedBaseTypeAlwaysSteps {R : OrderedGradeSemiring} {grades : GradeVectorOver R}
    {term : GradedLambda} (typed : HasGradeOver R [] grades term GTypeOver.base) :
    ∃ reduct, GradedLambda.Reduces term reduct := by
  cases closedWellTypedProgress typed with
  | inl steps => exact steps
  | inr isLam =>
      obtain ⟨body, termEq⟩ := isLam
      subst termEq
      obtain ⟨binderGrade, domain, codomain, baseEq, _⟩ := HasGradeOver.invertLam typed
      -- baseEq : GTypeOver.base = .arrow binderGrade domain codomain — a constructor clash.
      cases baseEq

/-- Usage-dimension smoke: the linear identity `λx.x` is already a value (progress's right disjunct). -/
theorem usageLinearIdentity_isValue :
    (∃ reduct, GradedLambda.Reduces (.lam (.var 0)) reduct) ∨
      (∃ body, (GradedLambda.lam (.var 0)) = .lam body) :=
  closedWellTypedProgress usageLinearIdentity_typedViaGeneric

end FX1Poly.Modal
