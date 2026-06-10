import FX1Poly.Core.StratifiedReducibleTypeHeadExpansion
import FX1Poly.Core.StratifiedReducibleMember
import FX1Poly.Core.ReducibleTypeAbstraction

/-! # Foundation/PolyCell/Core/StratifiedReducibleMemberAbstraction
    — semantic Π introduction (the last membership rule) over the stratified relation

The stratified port of `IsReducibleMember.abstraction`: `lam body` is a reducible member of the Π-type
when, for every reducible argument, the body's substitution instance lies in that argument's codomain
candidate.  This is the fundamental theorem's `piIntro` arm.  It is the LAST of the four structural
membership rules (after `application`, `castAlongConv`, `stronglyNormalizing`), completing the toolkit the
fundamental theorem's structural cases consume.

The β-redex `app (lam body) argument` head-expands (weak-head) to `subst0 body argument`, which the body's
induction hypothesis (`bodyReducible`) places in the codomain candidate; the codomain candidate's
head-expansion closure — supplied by `ReducibleTypeAt.headExpansionClosed` (shipped) — pulls membership back
to the redex.  The dependent-arrow assembly is `DependentArrowCandidate.abstraction`, reused unchanged
because `DependentArrowCandidate domainCandidate codomainCandidate` is DEFINITIONALLY the stratified
`piType` candidate `IsDependentArrowReducible domainCandidate codomainCandidate` (both unfold to
`fun functionTerm => ∀ argument, domainCandidate argument → codomainCandidate argument (app functionTerm
argument)`).

`ReducibleTypeAt.piType` is the reusable `ReducibleTypeStep.piType` constructor lifted through the `Nat`
recursion (the Π-formation builder the abstraction's type witness and the eventual formation rules need).

## Zero-axiom verification

`ReducibleTypeAt.piType` is `cases level` + the `piType` constructor; `abstraction` is the existential
package over it and `DependentArrowCandidate.abstraction` (fed the codomain's `headExpansionClosed`).  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration by
`#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **The dependent function-space former, level-indexed.**  `ReducibleTypeStep.piType` through the `Nat`
recursion of `ReducibleTypeAt` (both cases by defeq).  Builds a reducible Π-type from a reducible domain
and a per-argument reducible codomain; the candidate is the dependent-arrow candidate. -/
theorem ReducibleTypeAt.piType {scope : Nat} {level : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainCandidate : RawTerm scope → Prop}
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (domainReducible : ReducibleTypeAt level domainCode domainCandidate)
    (codomainReducible : ∀ argument : RawTerm scope, domainCandidate argument →
      ReducibleTypeAt level (RawTerm.subst0 codomainCode argument) (codomainCandidate argument)) :
    ReducibleTypeAt level
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
      (IsDependentArrowReducible domainCandidate codomainCandidate) := by
  cases level with
  | zero => exact ReducibleTypeStep.piType codomainCandidate domainReducible codomainReducible
  | succ predLevel => exact ReducibleTypeStep.piType codomainCandidate domainReducible codomainReducible

/-- **Semantic Π introduction (`piIntro` / λ).**  `lam body` is a reducible member of the Π-type when, for
every reducible argument, the body's substitution instance lies in that argument's codomain candidate.  The
domain reducibility supplies the Π-type's candidate; the codomain reducibility supplies its
head-expansion closure (`ReducibleTypeAt.headExpansionClosed`), which `DependentArrowCandidate.abstraction`
threads to discharge the β-redex `app (lam body) argument ↝ subst0 body argument`.  The argument's strong
normalization is supplied at the call site (the fundamental theorem's domain CR1). -/
theorem IsReducibleMemberAt.abstraction {scope : Nat} {level : Nat}
    {domainAnn domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    {domainCandidate : RawTerm scope → Prop}
    {codomainCandidate : RawTerm scope → (RawTerm scope → Prop)}
    (domainReducible : ReducibleTypeAt level domainCode domainCandidate)
    (domainAnnSN : IsStronglyNormalizing domainAnn)
    (domainArgumentsSN : ∀ argument : RawTerm scope, domainCandidate argument →
      IsStronglyNormalizing argument)
    (codomainReducible : ∀ argument : RawTerm scope, domainCandidate argument →
      ReducibleTypeAt level (RawTerm.subst0 codomainCode argument) (codomainCandidate argument))
    (bodyReducible : ∀ argument : RawTerm scope, domainCandidate argument →
      codomainCandidate argument (RawTerm.subst0 body argument)) :
    IsReducibleMemberAt level
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
      (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil))) :=
  ⟨IsDependentArrowReducible domainCandidate codomainCandidate,
   ReducibleTypeAt.piType codomainCandidate domainReducible codomainReducible,
   DependentArrowCandidate.abstraction domainAnnSN domainArgumentsSN
     (fun argument argumentInDomain =>
       (codomainReducible argument argumentInDomain).headExpansionClosed)
     bodyReducible⟩

/-- **Choice-free dependent Π-FORMATION via the canonical codomain.**  `ReducibleTypeAt.piType` specialized
to the FIXED canonical codomain function `fun argument => IsReducibleMemberAt level (subst0 codomainCode
argument)`: the per-argument codomain-reducibility premise is discharged from mere per-argument EXISTENCE
(`IsReducibleTypeAt`) by `IsReducibleTypeAt.reducibleMemberCandidate` (PathA-3).  No candidate is extracted
per argument, so no choice is used — this is the brick that dissolves the dependent fundamental theorem's
Π-formation choice wall. -/
theorem ReducibleTypeAt.piTypeCanonical {scope : Nat} {level : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainCandidate : RawTerm scope → Prop}
    (domainReducible : ReducibleTypeAt level domainCode domainCandidate)
    (codomainExists : ∀ argument : RawTerm scope, domainCandidate argument →
      IsReducibleTypeAt level (RawTerm.subst0 codomainCode argument)) :
    ReducibleTypeAt level
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
      (IsDependentArrowReducible domainCandidate
        (fun argument => IsReducibleMemberAt level (RawTerm.subst0 codomainCode argument))) :=
  ReducibleTypeAt.piType
    (fun argument => IsReducibleMemberAt level (RawTerm.subst0 codomainCode argument))
    domainReducible
    (fun argument argumentInDomain => (codomainExists argument argumentInDomain).reducibleMemberCandidate)

/-- **Choice-free dependent Π-INTRODUCTION via the canonical codomain.**  `IsReducibleMemberAt.abstraction`
specialized to the canonical codomain: the body lands in `IsReducibleMemberAt level (subst0 codomainCode
argument)` for every reducible argument (its fundamental-theorem IH), and the codomain-reducibility premise
is again discharged from existence by `IsReducibleTypeAt.reducibleMemberCandidate`.  The dependent
generalization of `abstractionNonDependent` (the `codomainCode := weaken B` special case), choice-free. -/
theorem IsReducibleMemberAt.abstractionCanonical {scope : Nat} {level : Nat}
    {domainAnn domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    {domainCandidate : RawTerm scope → Prop}
    (domainReducible : ReducibleTypeAt level domainCode domainCandidate)
    (domainAnnSN : IsStronglyNormalizing domainAnn)
    (domainArgumentsSN : ∀ argument : RawTerm scope, domainCandidate argument →
      IsStronglyNormalizing argument)
    (codomainExists : ∀ argument : RawTerm scope, domainCandidate argument →
      IsReducibleTypeAt level (RawTerm.subst0 codomainCode argument))
    (bodyReducible : ∀ argument : RawTerm scope, domainCandidate argument →
      IsReducibleMemberAt level (RawTerm.subst0 codomainCode argument) (RawTerm.subst0 body argument)) :
    IsReducibleMemberAt level
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
      (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil))) :=
  IsReducibleMemberAt.abstraction domainReducible domainAnnSN domainArgumentsSN
    (fun argument argumentInDomain => (codomainExists argument argumentInDomain).reducibleMemberCandidate)
    bodyReducible

end FX1Poly.Core
