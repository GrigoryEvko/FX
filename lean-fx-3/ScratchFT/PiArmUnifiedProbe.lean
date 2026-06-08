import FX1Poly.Typed.DenoteKeyedGeneralDomainPiArm
import FX1Poly.Typed.DenoteKeyedCanonicalMemberCandidate

/-! Scratch probe: the UNIFIED piArm — reduce the whole ofReducibleTypeStepDenote piArm (every domain shape)
    to member-stability of the domain to the single fixed outerLevel (= the lowerAt family index). -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- The unified piArm: the backbone invokes `ofReducibleTypeStepDenote` at `lowerAt = denoteBelowFamily env
    outerLevel`, so its domain step `domainReducible` IS `ReducibleTypeAtDenote env outerLevel`. The whole piArm
    then reduces to member-stability of the domain to that single `outerLevel` — assembled per output level, with
    the codomain existence derived by determinism against `domainReducible` (no shape-casing). -/
theorem piArmFromMemberStabilityToOuterLevel {scope : Nat} (env : Nat → Nat) (outerLevel : Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainCandidate : RawTerm scope → Prop}
    (domainReducible : ReducibleTypeAtDenote env outerLevel domainCode domainCandidate)
    (domainAllLevel : IsReducibleTypeAtAllDenoteLevels env domainCode)
    (memberStableToOuter : ∀ (sourceLevel : Nat) (argument : RawTerm scope),
        IsReducibleMemberAtDenote env sourceLevel domainCode argument →
        IsReducibleMemberAtDenote env outerLevel domainCode argument)
    (codomainInductiveHypothesis : ∀ argument : RawTerm scope, domainCandidate argument →
        IsReducibleTypeAtAllDenoteLevels env (RawTerm.subst0 codomainCode argument)) :
    IsReducibleTypeAtAllDenoteLevels env
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) := by
  intro outputLevel
  refine ⟨_, ReducibleTypeStepDenote.piType
    (fun argument => IsReducibleMemberAtDenote env outputLevel (RawTerm.subst0 codomainCode argument))
    (domainAllLevel outputLevel).reducibleMemberCandidate
    (fun argument argumentInDomain => ?_)⟩
  obtain ⟨candidateOuter, reducibleOuter, candidateOuterArgument⟩ :=
    memberStableToOuter outputLevel argument argumentInDomain
  have domainCandidateArgument : domainCandidate argument :=
    (ReducibleTypeAtDenote.deterministic reducibleOuter domainReducible argument).mp candidateOuterArgument
  exact (codomainInductiveHypothesis argument domainCandidateArgument outputLevel).reducibleMemberCandidate

#print axioms piArmFromMemberStabilityToOuterLevel

end FX1Poly.Typed
