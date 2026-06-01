import FX1Poly.Core.ReducibleTypeAbstraction
import FX1Poly.Core.ReducibilityCandidateArrow

/-! # FX1Poly/Core/ArrowCandidateMembership
    — introduction (λ) and elimination (app) for the NON-dependent arrow candidate `IsArrowReducible`

`ReducibleTypeAbstraction` ships `DependentArrowCandidate.application` / `.abstraction` — the Π membership
operations for the DEPENDENT arrow candidate (`codomainCandidate` a per-argument family).  This file
specializes them to the NON-dependent arrow candidate `IsArrowReducible domainCandidate codomainCandidate`
(`ReducibilityCandidateArrow`), the candidate `CandidateInterpretation`'s `InterpretsType.piType` arm
produces.  That arm is the choice-free Girard interpretation: the codomain is interpreted in a candidate
ENVIRONMENT extended by the DOMAIN'S candidate — a SINGLE `codomainCandidate`, not a per-argument-value
family — so the fundamental theorem built over `InterpretsType` never forms `∀ argument ∃ candidate` and
never needs choice.  These two operations are that fundamental theorem's `piIntro` / `piElim` cases AT THE
CANDIDATE LEVEL.

The specialization is by definitional β: `DependentArrowCandidate domainCandidate (fun _argument =>
codomainCandidate)` unfolds to `fun functionTerm => ∀ argument, domainCandidate argument → codomainCandidate
(app functionTerm argument)`, which IS `IsArrowReducible domainCandidate codomainCandidate` — so the
dependent operations at the CONSTANT family `fun _argument => codomainCandidate` retype directly as the
non-dependent ones (the per-argument `HeadExpansionClosed`/`codomainCandidate argument` premises collapse to
single argument-independent ones).

## The two operations

  * `IsArrowReducible.application` (`piElim` / app) — a member of the arrow candidate, applied to a
    `domainCandidate`-reducible argument, lands in `codomainCandidate`.  Immediate (the dependent
    elimination at the constant family).
  * `IsArrowReducible.abstraction` (`piIntro` / λ — the classical hard Tait case) — `λ body` is in the
    arrow candidate when `subst0 body argument` is in `codomainCandidate` for every reducible argument, the
    domain arguments are strongly normalizing (domain CR1), and `codomainCandidate` is closed under head
    expansion (so the β-redex `app (λ body) argument ↝ subst0 body argument` carries membership back).  Here
    the codomain closure is a SINGLE `HeadExpansionClosed codomainCandidate` — no per-argument family.

## Zero-axiom verification

Each is the constant-family (`fun _argument => codomainCandidate`) instance of the shipped
`DependentArrowCandidate.application` / `.abstraction`, retyped by the `IsArrowReducible ≡
DependentArrowCandidate _ (fun _ => _)` definitional β.  No new induction, no `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration by `#audit_namespace
FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **Non-dependent arrow elimination (the `piElim` / app case).**  Applying a member of the arrow candidate
`IsArrowReducible domainCandidate codomainCandidate` to a `domainCandidate`-reducible argument lands in
`codomainCandidate`.  The constant-family instance of `DependentArrowCandidate.application` — the input
`functionReducible : IsArrowReducible …` retypes as `DependentArrowCandidate … (fun _argument =>
codomainCandidate) …` by definitional β, and the output `(fun _argument => codomainCandidate) argument _`
β-reduces to `codomainCandidate _`. -/
theorem IsArrowReducible.application {scope : Nat}
    {domainCandidate codomainCandidate : RawTerm scope → Prop}
    {functionTerm argument : RawTerm scope}
    (functionReducible : IsArrowReducible domainCandidate codomainCandidate functionTerm)
    (argumentReducible : domainCandidate argument) :
    codomainCandidate
      (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil))) :=
  DependentArrowCandidate.application
    (codomainCandidate := fun _argument => codomainCandidate)
    functionReducible argumentReducible

/-- **Non-dependent arrow introduction (the `piIntro` / λ case — the classical hard Tait case).**  `λ body`
is a member of the arrow candidate `IsArrowReducible domainCandidate codomainCandidate` when, for every
`domainCandidate`-reducible argument, `subst0 body argument` is in `codomainCandidate`, the domain arguments
are strongly normalizing (the domain candidate's CR1), and `codomainCandidate` is closed under head
expansion.  The β-redex `app (λ body) argument` head-expands to `subst0 body argument`, and
`codomainCandidate`'s head-expansion closure carries membership back across it.

The constant-family instance of `DependentArrowCandidate.abstraction`: the per-argument premises
`∀ argument, domainCandidate argument → HeadExpansionClosed (codomainCandidate argument)` and
`∀ argument, domainCandidate argument → codomainCandidate argument (subst0 body argument)` collapse — at the
family `fun _argument => codomainCandidate` — to the single `HeadExpansionClosed codomainCandidate` and the
argument-independent `bodyReducible`.  No choice, because the codomain candidate does not vary with the
argument value (the no-large-elimination System-F fact `CandidateInterpretation` rests on). -/
theorem IsArrowReducible.abstraction {scope : Nat}
    {domainCandidate codomainCandidate : RawTerm scope → Prop}
    {body : RawTerm (scope + 1)}
    (domainArgumentsSN : ∀ argument : RawTerm scope, domainCandidate argument →
      IsStronglyNormalizing argument)
    (codomainClosed : HeadExpansionClosed codomainCandidate)
    (bodyReducible : ∀ argument : RawTerm scope, domainCandidate argument →
      codomainCandidate (RawTerm.subst0 body argument)) :
    IsArrowReducible domainCandidate codomainCandidate
      (.mkGen .gen_lam () (.childCons body .childNil)) :=
  DependentArrowCandidate.abstraction
    (codomainCandidate := fun _argument => codomainCandidate)
    domainArgumentsSN
    (fun _argument _argumentInDomain => codomainClosed)
    bodyReducible

end FX1Poly.Core
