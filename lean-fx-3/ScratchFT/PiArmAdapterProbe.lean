import FX1Poly.Typed.DenoteKeyedGeneralDomainPiArm

/-! Scratch probe: the uniform/neutral piArm ADAPTER — bridging the existential-candidate
    codomain IH that `ofReducibleTypeStepDenote`'s piArm supplies to the concrete-candidate
    form the shipped instances consume, via `ReducibleTypeAtDenote.deterministic`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- Adapter: from a UNIFORM domain candidate (reducible at every level with one candidate) and the
    existential-candidate codomain IH (the shape `ofReducibleTypeStepDenote`'s piArm supplies), the Π
    is reducible at every denote level.  Reconciles the codomain IH's `domainCandidate`-keying with the
    member-stability lemma's all-level-member gate via determinism at level 0. -/
theorem uniformDomainPiArmFromInductiveHypotheses {scope : Nat} (env : Nat → Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainCandidate : RawTerm scope → Prop}
    (domainUniform : ∀ level : Nat, ReducibleTypeAtDenote env level domainCode domainCandidate)
    (codomainInductiveHypothesis : ∀ argument : RawTerm scope, domainCandidate argument →
      IsReducibleTypeAtAllDenoteLevels env (RawTerm.subst0 codomainCode argument)) :
    IsReducibleTypeAtAllDenoteLevels env
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) :=
  generalDomainPi_reducibleFromMemberStability env
    (fun level => ⟨domainCandidate, domainUniform level⟩)
    (fun _sourceLevel targetLevel _argument memberAtSource =>
      uniformType_memberStableAcrossDenoteLevels env domainUniform memberAtSource targetLevel)
    (fun argument memberAllLevels => by
      obtain ⟨sourceCandidate, sourceReducible, memberInSource⟩ := memberAllLevels 0
      exact codomainInductiveHypothesis argument
        ((ReducibleTypeAtDenote.deterministic sourceReducible (domainUniform 0) argument).mp
          memberInSource))

/-- Neutral instance of the adapter: the domain is weak-head-normal non-Π non-universe (uniform
    candidate `IsStronglyNormalizing`), so the adapter applies with the existential-candidate codomain IH
    keyed on argument strong-normalization. -/
theorem neutralDomainPiArmFromInductiveHypotheses {scope : Nat} (env : Nat → Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep domainCode reduct)
    (notPiType : domainCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : domainCode.rootGenerator ≠ Generator.gen_universeCode)
    (codomainInductiveHypothesis : ∀ argument : RawTerm scope, IsStronglyNormalizing argument →
      IsReducibleTypeAtAllDenoteLevels env (RawTerm.subst0 codomainCode argument)) :
    IsReducibleTypeAtAllDenoteLevels env
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) :=
  uniformDomainPiArmFromInductiveHypotheses env
    (fun _level => ReducibleTypeStepDenote.neutral noWeakHeadStep notPiType notUniverse)
    codomainInductiveHypothesis

end FX1Poly.Typed

#print axioms FX1Poly.Typed.uniformDomainPiArmFromInductiveHypotheses
#print axioms FX1Poly.Typed.neutralDomainPiArmFromInductiveHypotheses
