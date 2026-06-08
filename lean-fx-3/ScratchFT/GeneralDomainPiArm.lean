import FX1Poly.Typed.DenoteKeyedPiFormationFromExistence

/-! Probe: the GENERAL domain piArm modulo domain member-stability. The backbone's
    domain IH gives per-level candidates (∀ level, ∃ cand_level); the piType assembly
    needs them to collapse, which is exactly domain member-stability. This covers
    member-stable COMPOSITE domains (Nat → Nat, etc.) the shipped uniform/neutral/
    universe instances cannot (they need a single uniform candidate as DATA). The
    residual after it: threshold-drift domains (containing universe codes). -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

theorem generalDomainPi_reducibleFromMemberStability {scope : Nat} (env : Nat → Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainAllLevel : IsReducibleTypeAtAllDenoteLevels env domainCode)
    (domainMemberStable : ∀ (sourceLevel targetLevel : Nat) (argument : RawTerm scope),
      IsReducibleMemberAtDenote env sourceLevel domainCode argument →
      IsReducibleMemberAtDenote env targetLevel domainCode argument)
    (codomainExistence : ∀ argument : RawTerm scope,
      (∀ memberLevel : Nat, IsReducibleMemberAtDenote env memberLevel domainCode argument) →
      IsReducibleTypeAtAllDenoteLevels env (RawTerm.subst0 codomainCode argument)) :
    IsReducibleTypeAtAllDenoteLevels env
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) :=
  fun level => ⟨_, ReducibleTypeStepDenote.piType
    (fun argument => IsReducibleMemberAtDenote env level (RawTerm.subst0 codomainCode argument))
    ((domainAllLevel level).reducibleMemberCandidate)
    (fun argument argumentInDomain =>
      (codomainExistence argument
        (fun memberLevel => domainMemberStable level memberLevel argument argumentInDomain)
        level).reducibleMemberCandidate)⟩

/-- Sanity: the shipped uniform-candidate piArm is the member-stable instance (a single
    uniform candidate gives member-stability via determinism). -/
theorem uniformDomainPi_viaMemberStability {scope : Nat} (env : Nat → Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainCandidate : RawTerm scope → Prop)
    (domainReducible : ∀ level : Nat, ReducibleTypeAtDenote env level domainCode domainCandidate)
    (codomainExistence : ∀ argument : RawTerm scope, domainCandidate argument →
      IsReducibleTypeAtAllDenoteLevels env (RawTerm.subst0 codomainCode argument)) :
    IsReducibleTypeAtAllDenoteLevels env
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) :=
  generalDomainPi_reducibleFromMemberStability env
    (fun level => ⟨domainCandidate, domainReducible level⟩)
    (fun sourceLevel targetLevel argument memberAtSource => by
      obtain ⟨sourceCandidate, sourceReducible, memberInSource⟩ := memberAtSource
      exact ⟨domainCandidate, domainReducible targetLevel,
        (ReducibleTypeAtDenote.deterministic sourceReducible (domainReducible sourceLevel)
          argument).mp memberInSource⟩)
    (fun argument memberAtAllLevels =>
      codomainExistence argument (by
        obtain ⟨someCandidate, someReducible, memberInSome⟩ := memberAtAllLevels 0
        exact (ReducibleTypeAtDenote.deterministic someReducible (domainReducible 0)
          argument).mp memberInSome))

end FX1Poly.Typed

#print axioms FX1Poly.Typed.generalDomainPi_reducibleFromMemberStability
#print axioms FX1Poly.Typed.uniformDomainPi_viaMemberStability
