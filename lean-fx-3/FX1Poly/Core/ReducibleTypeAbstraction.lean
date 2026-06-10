import FX1Poly.Core.ReducibleTypeArrowCandidate
import FX1Poly.Core.HeadExpansionClosure

/-! # Foundation/PolyCell/Core/ReducibleTypeAbstraction
    — the dependent-arrow candidate's introduction (λ) and elimination (app)

These are the two fundamental-theorem cases for the dependent function space, at the candidate level —
the genuine Tait content of the `piIntro`/`piElim` typing rules, both free of conversion-invariance:

  * **`application`** (the `piElim` / app case): a member of the dependent-arrow candidate, applied to
    a reducible argument, lands in that argument's codomain candidate.  This is *definitionally* what
    `DependentArrowCandidate` says — the elimination is immediate.
  * **`abstraction`** (the `piIntro` / λ case — the classical hard Tait case): `λ body` is a member of
    the dependent-arrow candidate whenever, for every reducible argument, the body's substitution
    instance `subst0 body argument` is in that argument's codomain candidate.  The β-redex
    `app (λ body) argument` head-expands to `subst0 body argument` (`HeadStep.beta`, the empty-spine
    instance of `HeadExpansionClosed`), so closure of the codomain candidate under head expansion
    carries membership back across the redex.  The argument must be strongly normalizing — supplied by
    the domain candidate's CR1 at the call site (`domainArgumentsSN`).

Together they classify `λ`/app for the dependent arrow `ReducibleType.piType` produces: the fundamental
theorem's Π cases reduce to these two, threading the codomain candidate's head-expansion closure from
`ReducibleType.headExpansionClosed` and the domain SN from the domain candidate's CR1.

## Zero-axiom verification

`application` is the unfolding of `DependentArrowCandidate`; `abstraction` is the empty-spine instance
of the shipped `HeadExpansionClosed` (where `applySpineApp head [] = head` definitionally).  No
induction, no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept
per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **Dependent-arrow elimination (the `piElim` / app case).**  Applying a member of the dependent-arrow
candidate to a reducible argument lands in that argument's codomain candidate — the defining property of
`DependentArrowCandidate`. -/
theorem DependentArrowCandidate.application {scope : Nat}
    {domainCandidate : RawTerm scope → Prop}
    {codomainCandidate : RawTerm scope → (RawTerm scope → Prop)}
    {functionTerm argument : RawTerm scope}
    (functionReducible :
      DependentArrowCandidate domainCandidate codomainCandidate functionTerm)
    (argumentReducible : domainCandidate argument) :
    codomainCandidate argument
      (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil))) :=
  functionReducible argument argumentReducible

/-- **Dependent-arrow introduction (the `piIntro` / λ case).**  `λ body` is a member of the
dependent-arrow candidate when, for every reducible argument, the body's substitution instance is in
that argument's codomain candidate: the β-redex `app (λ body) argument` head-expands to
`subst0 body argument`, and the codomain candidate's head-expansion closure carries membership back.
The argument's strong normalization (from the domain candidate's CR1) feeds the closure. -/
theorem DependentArrowCandidate.abstraction {scope : Nat}
    {domainCandidate : RawTerm scope → Prop}
    {codomainCandidate : RawTerm scope → (RawTerm scope → Prop)}
    {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)}
    (domainAnnSN : IsStronglyNormalizing domainAnn)
    (domainArgumentsSN :
      ∀ argument : RawTerm scope, domainCandidate argument → IsStronglyNormalizing argument)
    (codomainClosed :
      ∀ argument : RawTerm scope, domainCandidate argument →
        HeadExpansionClosed (codomainCandidate argument))
    (bodyReducible :
      ∀ argument : RawTerm scope, domainCandidate argument →
        codomainCandidate argument (RawTerm.subst0 body argument)) :
    DependentArrowCandidate domainCandidate codomainCandidate
      (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil))) := by
  intro argument argumentReducible
  have codomainHeadExpansionClosed :
      ∀ {redexDomainAnn : RawTerm scope} {redexBody : RawTerm (scope + 1)}
        {redexArgument : RawTerm scope} {spine : List (RawTerm scope)},
        IsStronglyNormalizing redexDomainAnn →
        IsStronglyNormalizing redexArgument →
        codomainCandidate argument
          (RawTerm.applySpineApp (RawTerm.subst0 redexBody redexArgument) spine) →
        codomainCandidate argument
          (RawTerm.applySpineApp
            (.mkGen .gen_app ()
              (.childCons
                (.mkGen .gen_lam ()
                  (.childCons redexDomainAnn (.childCons redexBody .childNil)))
                (.childCons redexArgument .childNil)))
            spine) :=
    codomainClosed argument argumentReducible
  exact codomainHeadExpansionClosed (redexDomainAnn := domainAnn) (redexBody := body)
    (redexArgument := argument) (spine := ([] : List (RawTerm scope)))
    domainAnnSN
    (domainArgumentsSN argument argumentReducible)
    (bodyReducible argument argumentReducible)

end FX1Poly.Core
