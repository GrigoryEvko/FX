import FX1Poly.Typed.DenoteKeyedFundamentalMotive
import FX1Poly.Typed.DenoteKeyedAbstractionUnderSubst
import FX1Poly.Typed.DenoteKeyedCanonicalMemberCandidate
import FX1Poly.Typed.HasTypeDescPi

/-! Scratch SN-D5c: the FT piIntro (λ) binder arm. THE crux. Canonical-candidate approach:
use `IsReducibleMemberAtDenote env level (subst …)` as BOTH domain and codomain candidate — then (a) the
env-cons arg-membership is direct (the candidate IS the membership predicate), and (b) bodyReducible is direct
(codomain candidate = the body IH's target, no deterministic). The A2-bridge-applied domain/codomain IHs + CR1
are clean caller premises; the body IH is direct (bodyConclusion). New content: canonical-candidate threading +
ReducibleEnvAtDenote.cons + abstractionMemberUnderClosingSubstitution (SN-D3). -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

theorem fundamentalPiIntroAtDenote {profile : PolyProfile} {scope : Nat} (env : Nat → Nat) (level : Nat)
    (context : TypingContext profile scope)
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    (domainReducibleAtLevel : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsReducibleTypeAtDenote env level (RawTerm.subst substitution domainCode))
    (domainArgumentsSN : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        ∀ argument : RawTerm targetScope,
          IsReducibleMemberAtDenote env level (RawTerm.subst substitution domainCode) argument →
          IsStronglyNormalizing argument)
    (codomainReducibleAtLevel : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        ∀ argument : RawTerm targetScope,
          IsReducibleMemberAtDenote env level (RawTerm.subst substitution domainCode) argument →
          IsReducibleTypeAtDenote env level
            (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode))
    (bodyConclusion :
        FundamentalConclusionAtDenote env level (context.cons domainCode) body codomainCode) :
    FundamentalConclusionAtDenote env level context (lamCell body)
      (piTyCodeCell domainCode codomainCode) := by
  intro targetScope substitution envReducible
  exact abstractionMemberUnderClosingSubstitution
    (domainCandidate := IsReducibleMemberAtDenote env level (RawTerm.subst substitution domainCode))
    (codomainCandidate := fun argument =>
      IsReducibleMemberAtDenote env level
        (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode))
    env level
    (domainReducibleAtLevel substitution envReducible).reducibleMemberCandidate
    (fun argument argumentMember =>
      (codomainReducibleAtLevel substitution envReducible argument argumentMember).reducibleMemberCandidate)
    (domainArgumentsSN substitution envReducible)
    (fun argument argumentMember =>
      bodyConclusion (RawTermSubst.cons argument substitution)
        (ReducibleEnvAtDenote.cons envReducible argumentMember))

end FX1Poly.Typed

#print axioms FX1Poly.Typed.fundamentalPiIntroAtDenote
