import FX1Poly.Typed.DenoteKeyedHeadExpansion
import FX1Poly.Core.ReducibleTypeAbstraction

/-! Scratch SN-D2: the denote lambda/piIntro MEMBER arm.  `lam body` is a denote-reducible member of
`Π domainCode codomainCode` whenever the domain is reducible (with candidate), the codomain is reducible
per reducible argument (yields head-expansion-closure via SN-D1), the domain candidate's members are SN
(domain CR1, taken as an explicit premise → deferred to BRICK 5), and the body's substitution instance is in
the codomain candidate (the FT IH).  Assembled from the generic `DependentArrowCandidate.abstraction` fed
SN-D1's `ReducibleTypeAtDenote.headExpansionClosed`. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe
open StepStar

theorem abstractionMemberAtDenote {scope : Nat} (env : Nat → Nat) (level : Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainCandidate : RawTerm scope → Prop}
    {codomainCandidate : RawTerm scope → (RawTerm scope → Prop)}
    {body : RawTerm (scope + 1)}
    (domainReducible : ReducibleTypeAtDenote env level domainCode domainCandidate)
    (codomainReducible : ∀ argument : RawTerm scope, domainCandidate argument →
        ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
          (codomainCandidate argument))
    (domainArgumentsSN : ∀ argument : RawTerm scope, domainCandidate argument →
        IsStronglyNormalizing argument)
    (bodyReducible : ∀ argument : RawTerm scope, domainCandidate argument →
        codomainCandidate argument (RawTerm.subst0 body argument)) :
    IsReducibleMemberAtDenote env level
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
      (.mkGen .gen_lam () (.childCons body .childNil)) :=
  ⟨DependentArrowCandidate domainCandidate codomainCandidate,
    ReducibleTypeStepDenote.piType codomainCandidate domainReducible codomainReducible,
    DependentArrowCandidate.abstraction domainArgumentsSN
      (fun argument argumentReducible =>
        (codomainReducible argument argumentReducible).headExpansionClosed)
      bodyReducible⟩

end FX1Poly.Typed

#print axioms FX1Poly.Typed.abstractionMemberAtDenote
