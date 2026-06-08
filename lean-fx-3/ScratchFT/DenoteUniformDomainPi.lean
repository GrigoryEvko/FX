import FX1Poly.Typed.DenoteKeyedLevelIrrelevance

/-! Scratch A2 (non-universe half of the piArm): the uniform-candidate-domain piArm. A1 closed the
universe-domain Π (candidate uniform ABOVE `denote e env`, degenerate below). The complement: any domain that
is reducible with ONE candidate at EVERY level (neutral types — candidate `IsStronglyNormalizing` via the
`neutral` arm — and data/former domains whose candidate is globally uniform) gives a Π reducible at every
denote level.  Choice-free: the codomain candidate is supplied as data (the FT-side existential extraction is a
separate, route-D concern). -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Uniform-candidate-domain piArm.**  If the domain `domainCode` is reducible with a SINGLE candidate
`domainCandidate` at every denote level, and the codomain is reducible (under domain membership) at every
level with codomain-candidate function `codomainCandidate`, then `Π domainCode codomainCode` is reducible at
every denote level.  At each level the `piType` constructor assembles the dependent arrow directly — the
uniform domain candidate means the codomain obligation is the same shape at every level. -/
theorem uniformDomainPi_reducibleAtEveryDenoteLevel {scope : Nat} (env : Nat → Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainCandidate : RawTerm scope → Prop)
    (domainReducible : ∀ level : Nat, ReducibleTypeAtDenote env level domainCode domainCandidate)
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (codomainReducible : ∀ (level : Nat) (argument : RawTerm scope), domainCandidate argument →
      ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
        (codomainCandidate argument)) :
    IsReducibleTypeAtAllDenoteLevels env
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) :=
  fun level => ⟨_, ReducibleTypeStepDenote.piType codomainCandidate (domainReducible level)
    (fun argument argumentInDomain => codomainReducible level argument argumentInDomain)⟩

/-- **Neutral-domain piArm (the witnessing instance).**  A weak-head-normal non-Π non-universe DOMAIN has the
literally-uniform candidate `IsStronglyNormalizing` at every level (the `neutral` arm), so the
uniform-candidate piArm applies.  The denote analogue of the fuel `piTypeOfNeutralDomain` — domains that are
type variables / stuck applications. -/
theorem neutralDomainPi_reducibleAtEveryDenoteLevel {scope : Nat} (env : Nat → Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep domainCode reduct)
    (notPiType : domainCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : domainCode.rootGenerator ≠ Generator.gen_universeCode)
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (codomainReducible : ∀ (level : Nat) (argument : RawTerm scope), IsStronglyNormalizing argument →
      ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
        (codomainCandidate argument)) :
    IsReducibleTypeAtAllDenoteLevels env
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) :=
  uniformDomainPi_reducibleAtEveryDenoteLevel env IsStronglyNormalizing
    (fun _level => ReducibleTypeStepDenote.neutral noWeakHeadStep notPiType notUniverse)
    codomainCandidate codomainReducible

end FX1Poly.Typed

#print axioms FX1Poly.Typed.uniformDomainPi_reducibleAtEveryDenoteLevel
#print axioms FX1Poly.Typed.neutralDomainPi_reducibleAtEveryDenoteLevel
