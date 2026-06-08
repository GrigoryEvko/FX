import FX1Poly.Typed.DenoteKeyedLevelIrrelevance

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- Member-stability for a uniform-domain Π TYPE: if the domain is reducible with a single level-uniform
candidate and the codomain is reducible (under domain membership) with a level-uniform candidate function,
then the Π type's own candidate is level-uniform, so its members are level-stable. Extends the member-stable
#672 fragment from neutral/uniform LEAF types to the Π FORMER (the non-universe-domain case the cumulativity
obstruction does NOT block). -/
theorem uniformDomainPiType_memberStableAcrossDenoteLevels {scope : Nat} (env : Nat → Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainCandidate : RawTerm scope → Prop)
    (domainReducible : ∀ level : Nat, ReducibleTypeAtDenote env level domainCode domainCandidate)
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (codomainReducible : ∀ (level : Nat) (argument : RawTerm scope), domainCandidate argument →
      ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
        (codomainCandidate argument))
    {term : RawTerm scope} {sourceLevel : Nat}
    (memberAtSource : IsReducibleMemberAtDenote env sourceLevel
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) term)
    (targetLevel : Nat) :
    IsReducibleMemberAtDenote env targetLevel
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) term :=
  uniformType_memberStableAcrossDenoteLevels env
    (fun level => ReducibleTypeStepDenote.piType codomainCandidate (domainReducible level)
      (fun argument argumentInDomain => codomainReducible level argument argumentInDomain))
    memberAtSource targetLevel

#print axioms FX1Poly.Typed.uniformDomainPiType_memberStableAcrossDenoteLevels

/-- Neutral-domain Π member-stability (witnessing instance): a neutral domain has the literally-uniform
candidate IsStronglyNormalizing, so the uniform-domain Π member-stability applies. -/
theorem neutralDomainPiType_memberStableAcrossDenoteLevels {scope : Nat} (env : Nat → Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep domainCode reduct)
    (notPiType : domainCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : domainCode.rootGenerator ≠ Generator.gen_universeCode)
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (codomainReducible : ∀ (level : Nat) (argument : RawTerm scope), IsStronglyNormalizing argument →
      ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
        (codomainCandidate argument))
    {term : RawTerm scope} {sourceLevel : Nat}
    (memberAtSource : IsReducibleMemberAtDenote env sourceLevel
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) term)
    (targetLevel : Nat) :
    IsReducibleMemberAtDenote env targetLevel
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) term :=
  uniformDomainPiType_memberStableAcrossDenoteLevels env IsStronglyNormalizing
    (fun _level => ReducibleTypeStepDenote.neutral noWeakHeadStep notPiType notUniverse)
    codomainCandidate codomainReducible memberAtSource targetLevel

#print axioms FX1Poly.Typed.neutralDomainPiType_memberStableAcrossDenoteLevels
