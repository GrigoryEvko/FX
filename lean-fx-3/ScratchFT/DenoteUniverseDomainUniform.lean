import FX1Poly.Typed.DenoteKeyedUniverseDomainPi

/-! Scratch: STRENGTHEN last tick's `universeDomainPi_reducibleAtAllDenoteLevels` from the per-level
`∀ level, ∃ candidate` form to the UNIFORM-candidate `∃ candidate, ∀ level` form.  This is the #672-relevant
shape: member-stability across levels needs ONE candidate that works at every level (a member of THAT candidate
is then a member at every level by definition).  The proof already builds a level-independent candidate (the
dependent-arrow predicate over the fixed decode-set domain candidate), so the existential pulls outside the
universal for free. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe
open StepStar

theorem universeDomainPi_uniformCandidateAtAllDenoteLevels {scope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) {codomainCode : RawTerm (scope + 1)}
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (codomainReducible : ∀ (level : Nat), LevelExpr.denote levelExpr env < level →
      ∀ argument : RawTerm scope,
        (IsStronglyNormalizing argument ∧
          IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) argument) →
          ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
            (codomainCandidate argument)) :
    ∃ candidate : RawTerm scope → Prop, ∀ (level : Nat), LevelExpr.denote levelExpr env < level →
      ReducibleTypeAtDenote env level
        (.mkGen .gen_piTyCode () (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
          (.childCons codomainCode .childNil)))
        candidate := by
  refine ⟨fun functionTerm => ∀ argument : RawTerm scope,
    (IsStronglyNormalizing argument ∧
      IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) argument) →
      codomainCandidate argument
        (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil))), ?_⟩
  intro level levelAbove
  exact ReducibleTypeStepDenote.piType codomainCandidate
    (universeMembership_levelIrrelevant env level levelExpr flag levelAbove)
    (fun argument argumentInDomain => codomainReducible level levelAbove argument argumentInDomain)

/-- Inline draft of the denote-keyed member predicate (will live in DenoteKeyedReducibility). -/
def IsReducibleMemberAtDenoteDraft {scope : Nat} (env : Nat → Nat) (level : Nat)
    (typeCode term : RawTerm scope) : Prop :=
  ∃ candidate : RawTerm scope → Prop, ReducibleTypeAtDenote env level typeCode candidate ∧ candidate term

/-- Member-stability for the universe-domain Π: a member at one level above `denote e env` is a member at
every level above it.  Via the uniform candidate + determinism (the candidate at the source level agrees with
the uniform candidate, so the member sits in the uniform candidate, which is reducible at every target level). -/
theorem universeDomainPi_memberStableDraft {scope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) {codomainCode : RawTerm (scope + 1)}
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (codomainReducible : ∀ (level : Nat), LevelExpr.denote levelExpr env < level →
      ∀ argument : RawTerm scope,
        (IsStronglyNormalizing argument ∧
          IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) argument) →
          ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
            (codomainCandidate argument))
    {functionTerm : RawTerm scope}
    {sourceLevel : Nat} (sourceLevelAbove : LevelExpr.denote levelExpr env < sourceLevel)
    (memberAtSource : IsReducibleMemberAtDenoteDraft env sourceLevel
      (.mkGen .gen_piTyCode () (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
        (.childCons codomainCode .childNil))) functionTerm)
    {targetLevel : Nat} (targetLevelAbove : LevelExpr.denote levelExpr env < targetLevel) :
    IsReducibleMemberAtDenoteDraft env targetLevel
      (.mkGen .gen_piTyCode () (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
        (.childCons codomainCode .childNil))) functionTerm := by
  obtain ⟨uniformCandidate, uniformReducible⟩ :=
    universeDomainPi_uniformCandidateAtAllDenoteLevels env levelExpr flag codomainCandidate codomainReducible
  obtain ⟨sourceCandidate, sourceReducible, memberInSource⟩ := memberAtSource
  have candidatesAgree :=
    ReducibleTypeAtDenote.deterministic sourceReducible (uniformReducible sourceLevel sourceLevelAbove)
  exact ⟨uniformCandidate, uniformReducible targetLevel targetLevelAbove,
    (candidatesAgree functionTerm).mp memberInSource⟩

end FX1Poly.Typed

#print axioms FX1Poly.Typed.universeDomainPi_uniformCandidateAtAllDenoteLevels
#print axioms FX1Poly.Typed.universeDomainPi_memberStableDraft
