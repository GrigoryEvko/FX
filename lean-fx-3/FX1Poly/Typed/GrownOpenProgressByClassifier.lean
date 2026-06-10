import FX1Poly.Typed.GrownOpenCanonicalFormsByClassifier

/-! # FX1Poly/Typed/GrownOpenProgressByClassifier — OPEN progress refined by classifier
    (five-layer-defense L4, §27.3: the last cell of the progress/canonical-forms matrix)

The grown-engine preservation matrix is {closed,open} × {general,per-classifier} × {canonical-forms,progress}.
Seven of the eight cells ship: `closedNormalSubjectHead` / `closedProgress` (closed general),
`closedNormal{Function,Type}…` / `closed{Function,Type}Steps…` (closed per-classifier, the latter pair from the
previous firing), `openNormalSubjectCanonicalOrNeutral` / `openProgress` (open general),
`openNormal{Function,Type}…OrNeutral` (open per-classifier canonical forms).  This file ships the eighth and last:
OPEN progress refined by classifier.

  * `HasTypeDescPi.openFunctionStepsOrIsLambdaOrNeutral` — a grown-typed term of Π type (`piTyCodeCell …`) in ANY
    well-formed context either takes a `Step`, OR is a λ (body extracted), OR is `Core.IsNeutral`.  The open
    generalization of the previous firing's `closedFunctionStepsOrIsLambda`, admitting the neutral leaf that
    variables introduce.

  * `HasTypeDescPi.openTypeStepsOrIsFormerOrNeutral` — a grown-typed TYPE (universe classifier) in ANY well-formed
    context either takes a `Step`, OR has a type-former head (`gen_piTyCode` / `gen_sigmaTyCode` /
    `gen_universeCode` / `gen_listCode` / `gen_optionCode`), OR is `Core.IsNeutral`.  The open generalization of
    `closedTypeStepsOrIsFormer`.

Both dispatch on decidable normality: a NORMAL subject is pinned by the open per-classifier canonical-forms lemma
(`openNormalFunctionIsLambdaOrNeutral` / `openNormalTypeIsFormerOrNeutral`, which read the classifier and admit the
neutral disjunct); a NON-normal subject steps by `exists_step_of_not_isStepNormalForm`.

## The 3-way disjunction IS the η-long readback case split

`(steps) ∨ (canonical-form-headed-by-the-classifier's-former) ∨ (neutral)` is exactly what a type-directed NbE /
η-long readback (`TY-CONV-quote` / `η-M15` line) branches on at each node: if the term reduces, reduce; otherwise
at a function type descend into the λ body (or η-expand a neutral), at a universe descend into the type former (or
stop at the neutral).  The closed firing-112 statements are the empty-context specializations where the neutral
disjunct is vacuous; these open forms carry the neutral leaf the readback recursion actually needs in non-empty
contexts.

## Why unconditional (no GrownCtxConv-5 / §5 dependence)

As with the closed twin, the classifier is read only at the already-NORMAL subject (via the open per-classifier
canonical-forms lemmas, which invert over the open canonical-forms recursor plus the context-general
classifier-mismatch inversions) — no reduction step is typed, so no subject reduction (hence no grown
context-conversion `piElim` arm, #842) is invoked.  The non-normal case asserts only that a step EXISTS.

## Zero-axiom verification

`by_cases` on the decidable `RawTerm.isStepNormalForm` + the shipped zero-axiom open per-classifier
canonical-forms lemmas + `exists_step_of_not_isStepNormalForm`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega` (verified by `#print axioms` in scratch before landing).  Per-declaration
gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Open progress at a function type (unconditional).**  A grown-typed term of Π type in any well-formed context
either takes a `Step`, OR is a λ (body extracted), OR is `Core.IsNeutral`.  Dispatches on decidable normality: a
normal Π-typed subject is a λ-or-neutral by `openNormalFunctionIsLambdaOrNeutral`; a non-normal subject steps by
`exists_step_of_not_isStepNormalForm`.  The open generalization of `closedFunctionStepsOrIsLambda` — the function
case of the η-long readback dichotomy (reduce / recurse-into-λ / η-expand-neutral). -/
theorem HasTypeDescPi.openFunctionStepsOrIsLambdaOrNeutral {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject : RawTerm scope}
    {outerDomain : RawTerm scope} {outerCodomain : RawTerm (scope + 1)}
    (typed : HasTypeDescPi profile context subject (piTyCodeCell outerDomain outerCodomain))
    (wellFormed : WfContextDesc context) :
    (∃ reduct : RawTerm scope, Step subject reduct) ∨
    (∃ (domainAnn : RawTerm scope) (body : RawTerm (scope + 1)), subject = lamCell domainAnn body) ∨
      IsNeutral subject := by
  by_cases isNormal : RawTerm.isStepNormalForm subject
  · exact Or.inr (HasTypeDescPi.openNormalFunctionIsLambdaOrNeutral typed wellFormed isNormal)
  · exact Or.inl (exists_step_of_not_isStepNormalForm isNormal)

/-- **Open progress at a universe (unconditional).**  A grown-typed TYPE (universe classifier) in any well-formed
context either takes a `Step`, OR has a type-former head (`gen_piTyCode` / `gen_sigmaTyCode` / `gen_universeCode` /
`gen_listCode` / `gen_optionCode` / `gen_unitCode`), OR is `Core.IsNeutral`.  Dispatches on decidable normality: a
normal universe-typed subject is a former-or-neutral by `openNormalTypeIsFormerOrNeutral`; a non-normal subject
steps.  The open generalization of `closedTypeStepsOrIsFormer` — the universe case of the η-long readback
dichotomy (reduce / descend-into-former / stop-at-neutral). -/
theorem HasTypeDescPi.openTypeStepsOrIsFormerOrNeutral {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (typed : HasTypeDescPi profile context subject (universeCodeCell levelExpr flag))
    (wellFormed : WfContextDesc context) :
    (∃ reduct : RawTerm scope, Step subject reduct) ∨
    (RawTerm.headGenerator subject = Generator.gen_piTyCode ∨
     RawTerm.headGenerator subject = Generator.gen_sigmaTyCode ∨
     RawTerm.headGenerator subject = Generator.gen_universeCode ∨
     RawTerm.headGenerator subject = Generator.gen_listCode ∨
     RawTerm.headGenerator subject = Generator.gen_optionCode ∨
     RawTerm.headGenerator subject = Generator.gen_unitCode) ∨ IsNeutral subject := by
  by_cases isNormal : RawTerm.isStepNormalForm subject
  · exact Or.inr (HasTypeDescPi.openNormalTypeIsFormerOrNeutral typed wellFormed isNormal)
  · exact Or.inl (exists_step_of_not_isStepNormalForm isNormal)

end FX1Poly.Typed
