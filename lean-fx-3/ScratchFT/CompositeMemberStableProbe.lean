import FX1Poly.Typed.DenoteKeyedGeneralDomainPiArm

/-! Scratch probe: the COMPOSITE domain arm of #752 — `Π dom. cod` member-stability to outerLevel from the
    components' (all-levels, both-directions) member-stability. The genuine #672 recursive heart.

    Argument: a function member `f` at sourceLevel maps source-dom-members to source-cod-members. For an
    outer-dom-member `arg`: pull it back to a source-dom-member (dom stability, outer→source), apply `f`'s
    source property, push the result forward to an outer-cod-member (cod stability, source→outer). -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

theorem compositeDomainMemberStableToOuter {scope : Nat} (env : Nat → Nat) (outerLevel : Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {piCandidateOuter : RawTerm scope → Prop}
    (piReducibleAtOuter : ReducibleTypeAtDenote env outerLevel
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) piCandidateOuter)
    (domainStable : ∀ (sourceLevel targetLevel : Nat) (argument : RawTerm scope),
        IsReducibleMemberAtDenote env sourceLevel domainCode argument →
        IsReducibleMemberAtDenote env targetLevel domainCode argument)
    (codomainStable : ∀ (argument : RawTerm scope) (sourceLevel targetLevel : Nat) (image : RawTerm scope),
        IsReducibleMemberAtDenote env sourceLevel (RawTerm.subst0 codomainCode argument) image →
        IsReducibleMemberAtDenote env targetLevel (RawTerm.subst0 codomainCode argument) image)
    (sourceLevel : Nat) (functionTerm : RawTerm scope)
    (memberAtSource : IsReducibleMemberAtDenote env sourceLevel
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) functionTerm) :
    IsReducibleMemberAtDenote env outerLevel
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) functionTerm := by
  obtain ⟨piCandidateSource, piReducibleSource, functionInSource⟩ := memberAtSource
  obtain ⟨domainCandidateSource, codomainCandidateSource, domainReducibleSource,
    codomainReducibleSource, piShapeSource⟩ := ReducibleTypeAtDenote.piTypeInversion piReducibleSource
  obtain ⟨domainCandidateOuter, codomainCandidateOuter, domainReducibleOuter,
    codomainReducibleOuter, piShapeOuter⟩ := ReducibleTypeAtDenote.piTypeInversion piReducibleAtOuter
  -- f's source property: maps source-domain-members to source-codomain-members
  have functionSourceProperty := (piShapeSource functionTerm).mp functionInSource
  refine ⟨piCandidateOuter, piReducibleAtOuter, (piShapeOuter functionTerm).mpr ?_⟩
  intro argument argumentInDomainOuter
  -- arg is an outer-domain-member; pull back to a source-domain-member
  have argumentMemberOuter : IsReducibleMemberAtDenote env outerLevel domainCode argument :=
    ⟨domainCandidateOuter, domainReducibleOuter, argumentInDomainOuter⟩
  obtain ⟨domainCandidateBack, domainReducibleBack, argumentInDomainBack⟩ :=
    domainStable outerLevel sourceLevel argument argumentMemberOuter
  have argumentInDomainSource : domainCandidateSource argument :=
    (ReducibleTypeAtDenote.deterministic domainReducibleBack domainReducibleSource argument).mp
      argumentInDomainBack
  -- apply f's source property, then push the codomain image forward to outerLevel
  have imageMemberSource : IsReducibleMemberAtDenote env sourceLevel
      (RawTerm.subst0 codomainCode argument)
      (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil))) :=
    ⟨codomainCandidateSource argument, codomainReducibleSource argument argumentInDomainSource,
      functionSourceProperty argument argumentInDomainSource⟩
  obtain ⟨codomainCandidateForward, codomainReducibleForward, imageInForward⟩ :=
    codomainStable argument sourceLevel outerLevel _ imageMemberSource
  exact (ReducibleTypeAtDenote.deterministic codomainReducibleForward
    (codomainReducibleOuter argument argumentInDomainOuter) _).mp imageInForward

#print axioms compositeDomainMemberStableToOuter

end FX1Poly.Typed
