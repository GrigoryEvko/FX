import FX1Poly.Typed.DenoteKeyedUniformPiCandidate

/-! Probe: the ABOVE-THRESHOLD version of uniform-component member-stability —
    the genuine handler for threshold-drift composite domains (Type@0 → Type@0),
    whose components are uniform only ABOVE their universe codes' decoded level.
    Bounded versions of uniformType_memberStableAcrossDenoteLevels +
    uniformDomainPi_hasUniformCandidate. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

theorem uniformType_memberStableAboveThreshold {scope : Nat} (env : Nat → Nat) (threshold : Nat)
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (uniformReducible : ∀ level : Nat, threshold < level →
      ReducibleTypeAtDenote env level typeCode candidate)
    {term : RawTerm scope} {sourceLevel : Nat} (sourceAbove : threshold < sourceLevel)
    (memberAtSource : IsReducibleMemberAtDenote env sourceLevel typeCode term)
    (targetLevel : Nat) (targetAbove : threshold < targetLevel) :
    IsReducibleMemberAtDenote env targetLevel typeCode term := by
  obtain ⟨sourceCandidate, sourceReducible, memberInSource⟩ := memberAtSource
  have candidatesAgree :=
    ReducibleTypeAtDenote.deterministic sourceReducible (uniformReducible sourceLevel sourceAbove)
  exact ⟨candidate, uniformReducible targetLevel targetAbove, (candidatesAgree term).mp memberInSource⟩

theorem uniformDomainPi_hasUniformCandidateAboveThreshold {scope : Nat} (env : Nat → Nat) (threshold : Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainCandidate : RawTerm scope → Prop)
    (domainReducible : ∀ level : Nat, threshold < level →
      ReducibleTypeAtDenote env level domainCode domainCandidate)
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (codomainReducible : ∀ (level : Nat), threshold < level → ∀ (argument : RawTerm scope),
      domainCandidate argument →
      ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
        (codomainCandidate argument)) :
    ∀ level : Nat, threshold < level → ReducibleTypeAtDenote env level
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
      (fun functionTerm => ∀ argument : RawTerm scope, domainCandidate argument →
        codomainCandidate argument
          (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil)))) :=
  fun level levelAbove => ReducibleTypeStepDenote.piType codomainCandidate
    (domainReducible level levelAbove)
    (fun argument argumentInDomain => codomainReducible level levelAbove argument argumentInDomain)

theorem uniformDomainPi_memberStableAboveThreshold {scope : Nat} (env : Nat → Nat) (threshold : Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainCandidate : RawTerm scope → Prop)
    (domainReducible : ∀ level : Nat, threshold < level →
      ReducibleTypeAtDenote env level domainCode domainCandidate)
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (codomainReducible : ∀ (level : Nat), threshold < level → ∀ (argument : RawTerm scope),
      domainCandidate argument →
      ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
        (codomainCandidate argument))
    {term : RawTerm scope} {sourceLevel : Nat} (sourceAbove : threshold < sourceLevel)
    (memberAtSource : IsReducibleMemberAtDenote env sourceLevel
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) term)
    (targetLevel : Nat) (targetAbove : threshold < targetLevel) :
    IsReducibleMemberAtDenote env targetLevel
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) term :=
  uniformType_memberStableAboveThreshold env threshold
    (uniformDomainPi_hasUniformCandidateAboveThreshold env threshold domainCandidate domainReducible
      codomainCandidate codomainReducible)
    sourceAbove memberAtSource targetLevel targetAbove

end FX1Poly.Typed

#print axioms FX1Poly.Typed.uniformType_memberStableAboveThreshold
#print axioms FX1Poly.Typed.uniformDomainPi_hasUniformCandidateAboveThreshold
#print axioms FX1Poly.Typed.uniformDomainPi_memberStableAboveThreshold
