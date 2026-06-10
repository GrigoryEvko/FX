import FX1Poly.Typed.DenoteKeyedHeadExpansion
import FX1Poly.Core.ReducibleTypeAbstraction

/-! # FX1Poly/Typed/DenoteKeyedAbstractionMember
    — the denote fundamental theorem's Π-INTRODUCTION (λ) member arm (SN-D2; toward SN-043/#672)

The classical hard Tait case of the fundamental theorem, ported onto the denote relation: `λ body` is a
denote-reducible MEMBER of `Π domainCode codomainCode`.  It is the introduction twin of the shipped
`applicationMemberAtDenote` (Π-elimination), and the consumer of SN-D1
(`ReducibleTypeAtDenote.headExpansionClosed`, `DenoteKeyedHeadExpansion`).

The denote `piType` candidate is `fun functionTerm => ∀ argument, domainCandidate argument →
codomainCandidate argument (app functionTerm argument)`, which is DEFINITIONALLY
`DependentArrowCandidate domainCandidate codomainCandidate` (`ReducibleTypeArrowCandidate.lean:48`).  So
membership of `λ body` in that candidate is exactly `DependentArrowCandidate.abstraction`
(`ReducibleTypeAbstraction.lean:56`), the empty-spine instance of head-expansion closure: the β-redex
`app (λ body) argument` head-expands to `subst0 body argument`, and the codomain candidate's
head-expansion closure carries membership of `subst0 body argument` back across the redex.

The three premises `DependentArrowCandidate.abstraction` requires are supplied as follows:
  * `domainArgumentsSN` (domain CR1: domain members are SN) — taken as an EXPLICIT premise here, deferring
    the bounded denote CR1 discharge to BRICK 5 (the level-bounded `isReducibilityCandidate` variant); the
    fundamental theorem supplies it from the domain's reducibility at the ambient classifier level.  This
    keeps SN-D2 a pure assembly with no new SN-extraction obligation.
  * `codomainClosed` (head-expansion closure of each codomain candidate) — discharged per reducible
    argument by SN-D1 `ReducibleTypeAtDenote.headExpansionClosed` applied to the codomain's reducibility.
  * `bodyReducible` (each body substitution instance lands in the codomain candidate) — the fundamental
    theorem's IH for the body under the extended environment.

The Π type itself is denote-reducible with the dependent-arrow candidate directly via the `piType`
constructor (`ReducibleTypeStepDenote.piType`) fed the domain and per-argument codomain reducibilities, so
the member witness `IsReducibleMemberAtDenote` assembles in one anonymous constructor.

## Zero-axiom verification

A single anonymous-constructor term: the type-reducibility component is the `piType` constructor (its
candidate `fun f => ∀ arg, …` is defeq to `DependentArrowCandidate …`, unfolded during elaboration), the
membership component is `DependentArrowCandidate.abstraction` fed SN-D1's head-expansion closure.  No
induction, no `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The denote Π-introduction (λ) member arm.**  `λ body` is a denote-reducible member of
`Π domainCode codomainCode`, given: the domain is reducible with candidate `domainCandidate`; the
substituted codomain `subst0 codomainCode argument` is reducible with candidate `codomainCandidate argument`
for every reducible argument; the domain candidate's members are strongly normalizing (domain CR1, an
explicit premise the fundamental theorem discharges from the ambient classifier level); and each body
instance `subst0 body argument` lies in `codomainCandidate argument` (the body IH).  The Π type is reducible
with the dependent-arrow candidate via the `piType` constructor; membership of `λ body` is
`DependentArrowCandidate.abstraction`, whose codomain head-expansion-closure premise is SN-D1
`ReducibleTypeAtDenote.headExpansionClosed`. -/
theorem abstractionMemberAtDenote {scope : Nat} (env : Nat → Nat) (level : Nat)
    {domainAnn domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainCandidate : RawTerm scope → Prop}
    {codomainCandidate : RawTerm scope → (RawTerm scope → Prop)}
    {body : RawTerm (scope + 1)}
    (domainReducible : ReducibleTypeAtDenote env level domainCode domainCandidate)
    (domainAnnSN : IsStronglyNormalizing domainAnn)
    (codomainReducible : ∀ argument : RawTerm scope, domainCandidate argument →
        ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
          (codomainCandidate argument))
    (domainArgumentsSN : ∀ argument : RawTerm scope, domainCandidate argument →
        IsStronglyNormalizing argument)
    (bodyReducible : ∀ argument : RawTerm scope, domainCandidate argument →
        codomainCandidate argument (RawTerm.subst0 body argument)) :
    IsReducibleMemberAtDenote env level
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
      (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil))) :=
  ⟨DependentArrowCandidate domainCandidate codomainCandidate,
    ReducibleTypeStepDenote.piType codomainCandidate domainReducible codomainReducible,
    DependentArrowCandidate.abstraction domainAnnSN domainArgumentsSN
      (fun argument argumentReducible =>
        (codomainReducible argument argumentReducible).headExpansionClosed)
      bodyReducible⟩

end FX1Poly.Typed
