import FX1Poly.Core.StratifiedReducibleMemberAbstraction
import FX1Poly.Core.DependentArrowReducibilityCandidate
import FX1Poly.Core.ReducibilityCandidateArrow
import FX1Poly.Core.RawTermSubst0Commute

/-! # FX1Poly/Core/StratifiedReducibleMemberNonDependent
    — the non-dependent (simply-typed) arrow: choice-free Π-introduction/formation for the
      no-large-elimination fragment

`ReducibleTypeAt.piType` and `IsReducibleMemberAt.abstraction` (`StratifiedReducibleMemberAbstraction`) build the
DEPENDENT function space: the codomain candidate `codomainCandidate argument` is a PER-ARGUMENT family, so the
fundamental theorem's `piIntro` / Π-formation arms must supply, for every reducible argument, that argument's
codomain candidate.  The only handle the typing premise gives is `∀ argument, ∃ candidate, ReducibleTypeAt …`,
and turning `∀ argument ∃ candidate` into a function needs choice (banned).  That is the candidate-congruence
wall — and it is an artifact of OVER-GENERALITY, not a real obstruction for Milestone A.

The wall DISSOLVES for the no-large-elimination fragment Milestone A targets.  With no large elimination a type's
reducibility candidate never depends on a term value (the System-F fact: type formers do not compute on terms),
so the codomain candidate is CONSTANT across arguments and no choice is needed.  The cleanest manifestly-constant
instance is the NON-DEPENDENT arrow `A → B`, whose codomain `B : RawTerm scope` occupies the Π binder slot as
`RawTerm.weaken B : RawTerm (scope + 1)`.  Then `RawTerm.subst0 (RawTerm.weaken B) argument = B` for EVERY
`argument` (`RawTerm.weaken_subst_singleton` — singleton substitution cancels the weakening), so the
per-argument codomain premise of `piType` / `abstraction` collapses to a SINGLE argument-independent
reducibility of `B`.  This `subst0 (weaken B) argument = B` cancellation IS the reducibility-substitution engine;
the constant codomain candidate makes the dependent-arrow candidate `IsDependentArrowReducible domainCandidate
(fun _argument => codomainCandidate)` DEFINITIONALLY the non-dependent `IsArrowReducible domainCandidate
codomainCandidate` (the `fun _argument => codomainCandidate` applied to any argument β-reduces away).

## The two bricks

  * `ReducibleTypeAt.arrowType` — the simple-arrow type former: from a reducible domain `A` and a reducible
    codomain `B`, the arrow code `gen_piTyCode (A, weaken B)` is a reducible type at the non-dependent arrow
    candidate `IsArrowReducible`.  `piType` at the constant codomain family; the per-argument codomain premise is
    discharged by the `weaken_subst_singleton` cancellation; the dependent candidate is reconciled to the
    non-dependent one by definitional β-equality.
  * `IsReducibleMemberAt.abstractionNonDependent` — the simple-arrow λ introduction (the no-large-elim `piIntro`
    arm): `lam body` is a reducible member of `A → B` when, for every reducible argument, the body's substitution
    instance lands in `B`'s candidate.  `abstraction` at the constant codomain family; its conclusion carries no
    candidate (the membership packs it existentially), so the match is syntactic and the only work is discharging
    the per-argument codomain premise by the same cancellation.

The DEPENDENT `piIntro` (per-argument codomain) is RETAINED unchanged for post-Milestone-A large elimination —
that case needs the recursive type-interpretation (realizability) pivot, not choice.  This file ships exactly
the fragment Milestone A consumes, choice-free.

## Zero-axiom verification

Both bricks reduce to the shipped `piType` / `abstraction` at a constant codomain family, then `rw
[RawTerm.subst0, RawTerm.weaken_subst_singleton]` to collapse the per-argument codomain premise to a single
reducibility.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per
declaration by `#audit_namespace FX1Poly.Core` in `FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **The non-dependent (simply-typed) arrow type former.**  From a reducible domain `A` (candidate
`domainCandidate`) and a reducible codomain `B` (candidate `codomainCandidate`), the simple-arrow code
`gen_piTyCode (A, weaken B)` is a reducible type whose candidate is the non-dependent arrow candidate
`IsArrowReducible domainCandidate codomainCandidate`.

This is `ReducibleTypeAt.piType` instantiated at the CONSTANT codomain family `fun _argument => codomainCandidate`
— sound precisely because the codomain `B` is `weaken`'d, so `RawTerm.subst0 (weaken B) argument = B`
(`weaken_subst_singleton`) is argument-INDEPENDENT and the per-argument codomain reducibility premise collapses
to the single `codomainReducible`.  The resulting `piType` candidate `IsDependentArrowReducible domainCandidate
(fun _argument => codomainCandidate)` is definitionally `IsArrowReducible domainCandidate codomainCandidate`
(the constant family β-reduces), so `exact` reconciles them with no transport. -/
theorem ReducibleTypeAt.arrowType {scope : Nat} {level : Nat}
    {domainCode codomainCodeBase : RawTerm scope}
    {domainCandidate codomainCandidate : RawTerm scope → Prop}
    (domainReducible : ReducibleTypeAt level domainCode domainCandidate)
    (codomainReducible : ReducibleTypeAt level codomainCodeBase codomainCandidate) :
    ReducibleTypeAt level
      (.mkGen .gen_piTyCode ()
        (.childCons domainCode (.childCons (RawTerm.weaken codomainCodeBase) .childNil)))
      (IsArrowReducible domainCandidate codomainCandidate) := by
  have viaPi :
      ReducibleTypeAt level
        (.mkGen .gen_piTyCode ()
          (.childCons domainCode (.childCons (RawTerm.weaken codomainCodeBase) .childNil)))
        (IsDependentArrowReducible domainCandidate (fun _argument => codomainCandidate)) :=
    ReducibleTypeAt.piType (codomainCandidate := fun _argument => codomainCandidate)
      domainReducible
      (by
        intro argument _argumentInDomain
        rw [RawTerm.subst0, RawTerm.weaken_subst_singleton]
        exact codomainReducible)
  exact viaPi

/-- **The non-dependent (simply-typed) λ introduction — the no-large-elimination `piIntro` arm.**  `lam body`
is a reducible member of the simple arrow `A → B` (code `gen_piTyCode (A, weaken B)`) when the domain `A` is a
reducible type, every domain-reducible argument is strongly normalizing (the domain CR1 the β-redex needs), the
codomain `B` is a reducible type, and the body's substitution instance `subst0 body argument` lands in `B`'s
candidate for every reducible argument.

`IsReducibleMemberAt.abstraction` instantiated at the CONSTANT codomain family `fun _argument =>
codomainCandidate`.  The conclusion of `abstraction` carries no candidate (it is packed existentially inside
`IsReducibleMemberAt`), so the goal matches syntactically; the only proof obligation is the per-argument codomain
reducibility, discharged — as in `arrowType` — by `subst0 (weaken B) argument = B` (`weaken_subst_singleton`)
collapsing it to the single `codomainReducible`.  The body premise `bodyReducible` transfers directly: the
constant family applied to any argument β-reduces to `codomainCandidate`. -/
theorem IsReducibleMemberAt.abstractionNonDependent {scope : Nat} {level : Nat}
    {domainCode codomainCodeBase : RawTerm scope} {body : RawTerm (scope + 1)}
    {domainCandidate codomainCandidate : RawTerm scope → Prop}
    (domainReducible : ReducibleTypeAt level domainCode domainCandidate)
    (domainArgumentsSN : ∀ argument : RawTerm scope, domainCandidate argument →
      IsStronglyNormalizing argument)
    (codomainReducible : ReducibleTypeAt level codomainCodeBase codomainCandidate)
    (bodyReducible : ∀ argument : RawTerm scope, domainCandidate argument →
      codomainCandidate (RawTerm.subst0 body argument)) :
    IsReducibleMemberAt level
      (.mkGen .gen_piTyCode ()
        (.childCons domainCode (.childCons (RawTerm.weaken codomainCodeBase) .childNil)))
      (.mkGen .gen_lam () (.childCons body .childNil)) := by
  refine IsReducibleMemberAt.abstraction
    (codomainCandidate := fun _argument => codomainCandidate)
    domainReducible domainArgumentsSN ?codomainConstReducible bodyReducible
  intro argument _argumentInDomain
  rw [RawTerm.subst0, RawTerm.weaken_subst_singleton]
  exact codomainReducible

end FX1Poly.Core
