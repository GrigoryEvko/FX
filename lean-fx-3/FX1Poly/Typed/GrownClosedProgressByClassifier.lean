import FX1Poly.Typed.GrownCanonicalFormsByClassifier

/-! # FX1Poly/Typed/GrownClosedProgressByClassifier — closed PROGRESS refined by classifier
    (five-layer-defense L4, §27.3: progress read at the Π / universe classifier)

`GrownTypeSafety.closedProgress` is the GENERAL progress statement: a closed grown-typed term is a canonical
value (`IsGrownCanonicalHead` AND normal) or it steps — but it does not read the classifier, so the value disjunct
is the coarse "one of six canonical heads".  `GrownCanonicalFormsByClassifier` sharpens the NORMAL case per
classifier (`closedNormalFunctionIsLambda` — a normal Π-typed term is a λ; `closedNormalTypeIsFormer` — a normal
universe-typed term is a type former).  This file completes the matrix: the PROGRESS statement read at the
classifier, the missing "closed + per-classifier + progress" cell.

  * `HasTypeDescPi.closedFunctionStepsOrIsLambda` — **progress at a function type.**  A closed grown-typed term of
    Π type (`piTyCodeCell …`) either takes a `Step` or IS a λ, with its body extracted (`∃ body, subject =
    lamCell body`).  This is the operational "a function-typed term is applicable-or-reduces" fact: the function
    position of any closed application either makes progress or is already the λ a β-redex needs.  The dependent
    analogue of the simply-typed graded `closedWellTypedProgress` (`Modal.GradedProgress`), sharpened past
    "canonical value" to the exact λ shape.

  * `HasTypeDescPi.closedTypeStepsOrIsFormer` — **progress at a universe.**  A closed grown-typed TYPE (classifier
    a universe `universeCodeCell levelExpr flag`) either takes a `Step` or its head is a type FORMER
    (`gen_piTyCode` / `gen_sigmaTyCode` / `gen_universeCode` / `gen_listCode` / `gen_optionCode` / `gen_unitCode`) —
    never a stuck λ.  The type-level progress fact: a closed type expression reduces or is already a syntactic
    former.

Both dispatch on decidable normality: a NORMAL subject is pinned by the per-classifier canonical-forms lemma
(`closedNormalFunctionIsLambda` / `closedNormalTypeIsFormer`); a NON-normal subject steps by
`exists_step_of_not_isStepNormalForm`.  No subject reduction, no SN, no closedness-of-the-codomain hypothesis —
so, unlike `closedTypeSafetyOfSubjectReductionStar` (which carries the classifier down a reduction chain and is
gated on the SN-055 master dispatcher / GrownCtxConv-5), these are UNCONDITIONAL.  They are the one-step progress
refinements, not the iterated evaluation statement.

## Why unconditional (no GrownCtxConv-5 / §5 dependence)

The classifier is read only at the ALREADY-normal subject, where `closedNormalFunctionIsLambda` /
`closedNormalTypeIsFormer` invert directly over the closed-canonical-forms recursor plus the classifier-mismatch
inversions — no reduction step is typed, so no subject reduction (hence no grown context-conversion `piElim`
arm, #842) is invoked.  The non-normal case only asserts that a step EXISTS, claiming nothing about its type.
This is exactly the closed analogue of the graded progress capstone, which is likewise SR-free.

## Zero-axiom verification

`by_cases` on the decidable `RawTerm.isStepNormalForm` + the shipped zero-axiom per-classifier canonical-forms
lemmas + `exists_step_of_not_isStepNormalForm`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega` (verified by `#print axioms` in scratch before landing).  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Progress at a function type (unconditional).**  A closed grown-typed term whose classifier is a Π type
either takes a `Step` or IS a λ (with body extracted).  Dispatches on decidable normality: a normal Π-typed
subject is a λ by `closedNormalFunctionIsLambda`; a non-normal subject steps by
`exists_step_of_not_isStepNormalForm`.  The per-classifier progress refinement of `closedProgress`: the value
disjunct is pinned to the exact λ shape, the operational form the function position of an application consumes. -/
theorem HasTypeDescPi.closedFunctionStepsOrIsLambda {profile : PolyProfile} {subject : RawTerm 0}
    {outerDomain : RawTerm 0} {outerCodomain : RawTerm 1}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (piTyCodeCell outerDomain outerCodomain)) :
    (∃ reduct : RawTerm 0, Step subject reduct) ∨
      (∃ (domainAnn : RawTerm 0) (body : RawTerm 1), subject = lamCell domainAnn body) := by
  by_cases isNormal : RawTerm.isStepNormalForm subject
  · exact Or.inr (HasTypeDescPi.closedNormalFunctionIsLambda typed isNormal)
  · exact Or.inl (exists_step_of_not_isStepNormalForm isNormal)

/-- **Progress at a universe (unconditional).**  A closed grown-typed TYPE (classifier a universe) either takes a
`Step` or its head is a type FORMER (`gen_piTyCode` / `gen_sigmaTyCode` / `gen_universeCode` / `gen_listCode` /
`gen_optionCode` / `gen_unitCode`).  Dispatches on decidable normality: a normal universe-typed subject is a
former by `closedNormalTypeIsFormer`; a non-normal subject steps.  The type-level progress refinement of
`closedProgress`: a closed type expression reduces or is already a syntactic former — never a stuck λ. -/
theorem HasTypeDescPi.closedTypeStepsOrIsFormer {profile : PolyProfile} {subject : RawTerm 0}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (universeCodeCell levelExpr flag)) :
    (∃ reduct : RawTerm 0, Step subject reduct) ∨
    (RawTerm.headGenerator subject = Generator.gen_piTyCode ∨
     RawTerm.headGenerator subject = Generator.gen_sigmaTyCode ∨
     RawTerm.headGenerator subject = Generator.gen_universeCode ∨
     RawTerm.headGenerator subject = Generator.gen_listCode ∨
     RawTerm.headGenerator subject = Generator.gen_optionCode ∨
     RawTerm.headGenerator subject = Generator.gen_unitCode) := by
  by_cases isNormal : RawTerm.isStepNormalForm subject
  · exact Or.inr (HasTypeDescPi.closedNormalTypeIsFormer typed isNormal)
  · exact Or.inl (exists_step_of_not_isStepNormalForm isNormal)

end FX1Poly.Typed
