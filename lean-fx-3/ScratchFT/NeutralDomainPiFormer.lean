import FX1Poly.Typed.DenoteKeyedPiFormerAtLevel

/-! Probe: the neutral-domain instance using the neutral ctor directly (no extra import). -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

theorem neutralDomainPiFormerReducibleAtLevel {scope : Nat} (env : Nat → Nat) (level : Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep domainCode reduct)
    (notPiType : domainCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : domainCode.rootGenerator ≠ Generator.gen_universeCode)
    (codomainReducible : ∀ argument : RawTerm scope,
      IsReducibleMemberAtDenote env level domainCode argument →
      IsReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)) :
    IsReducibleTypeAtDenote env level
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) :=
  piFormerReducibleAtLevel env level
    ⟨IsStronglyNormalizing, ReducibleTypeStepDenote.neutral noWeakHeadStep notPiType notUniverse⟩
    codomainReducible

end FX1Poly.Typed

#print axioms FX1Poly.Typed.neutralDomainPiFormerReducibleAtLevel
