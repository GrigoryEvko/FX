import FX1Poly.Typed.DenoteKeyedLevelIrrelevance
import FX1Poly.Typed.DenoteKeyedCanonicalMemberCandidate

/-! Scratch: the denote Π-formation arm FROM CODOMAIN EXISTENCE — the route-D-friendly piArm. Where the shipped
`uniformDomainPi_reducibleAtEveryDenoteLevel` takes the codomain candidate as DATA, this takes only the codomain
IH's EXISTENCE (`IsReducibleTypeAtAllDenoteLevels`) and extracts the per-level candidate choice-freely via the
canonical-member-candidate engine. This is what the FT's Π-formation arm actually has (an IH that gives
existence, not a chosen candidate). The domain-membership gating matches because the domain candidate is uniform
across levels. -/

namespace FX1Poly.Typed
open FX1Poly.Core
open StepStar

/-- Uniform-candidate-domain Π-formation from codomain EXISTENCE (choice-free). At each level the canonical
member-predicate of the closed codomain is its candidate (`reducibleMemberCandidate`), so the per-arg codomain
obligation is discharged from mere existence — no `Classical.choice`. -/
theorem uniformDomainPi_reducibleFromCodomainExistence {scope : Nat} (env : Nat → Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainCandidate : RawTerm scope → Prop)
    (domainReducible : ∀ level : Nat, ReducibleTypeAtDenote env level domainCode domainCandidate)
    (codomainExistence : ∀ argument : RawTerm scope, domainCandidate argument →
      IsReducibleTypeAtAllDenoteLevels env (RawTerm.subst0 codomainCode argument)) :
    IsReducibleTypeAtAllDenoteLevels env
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) :=
  fun level => ⟨_, ReducibleTypeStepDenote.piType
    (fun argument => IsReducibleMemberAtDenote env level (RawTerm.subst0 codomainCode argument))
    (domainReducible level)
    (fun argument argumentInDomain =>
      (codomainExistence argument argumentInDomain level).reducibleMemberCandidate)⟩

/-- Neutral-domain Π-formation from codomain EXISTENCE (the witnessing instance — a type variable or stuck
application as domain). -/
theorem neutralDomainPi_reducibleFromCodomainExistence {scope : Nat} (env : Nat → Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep domainCode reduct)
    (notPiType : domainCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : domainCode.rootGenerator ≠ Generator.gen_universeCode)
    (codomainExistence : ∀ argument : RawTerm scope, IsStronglyNormalizing argument →
      IsReducibleTypeAtAllDenoteLevels env (RawTerm.subst0 codomainCode argument)) :
    IsReducibleTypeAtAllDenoteLevels env
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) :=
  uniformDomainPi_reducibleFromCodomainExistence env IsStronglyNormalizing
    (fun _level => ReducibleTypeStepDenote.neutral noWeakHeadStep notPiType notUniverse)
    codomainExistence

end FX1Poly.Typed

#print axioms FX1Poly.Typed.uniformDomainPi_reducibleFromCodomainExistence
#print axioms FX1Poly.Typed.neutralDomainPi_reducibleFromCodomainExistence
