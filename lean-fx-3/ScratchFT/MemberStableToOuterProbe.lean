import FX1Poly.Typed.DenoteKeyedUniverseDomainPiArm
import FX1Poly.Typed.DenoteKeyedGeneralDomainPiArm

/-! Scratch probe: the concrete memberStableToOuter instances the unified piArm
    (piArmFromMemberStabilityToOuterLevel) consumes — neutral + universe domains. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

-- Neutral domain: member-stability to outerLevel is the fixed-target instance of the shipped neutral
-- member-stability (the neutral candidate is SN at every level).
theorem neutralDomainMemberStableToOuter {scope : Nat} (env : Nat → Nat) (outerLevel : Nat)
    {domainCode : RawTerm scope}
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep domainCode reduct)
    (notPiType : domainCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : domainCode.rootGenerator ≠ Generator.gen_universeCode)
    (sourceLevel : Nat) (argument : RawTerm scope)
    (memberAtSource : IsReducibleMemberAtDenote env sourceLevel domainCode argument) :
    IsReducibleMemberAtDenote env outerLevel domainCode argument :=
  neutralType_memberStableAcrossDenoteLevels env noWeakHeadStep notPiType notUniverse
    memberAtSource outerLevel

-- Universe domain Type@inner: member-stability to outerLevel, gated on inner < outerLevel. A member at any
-- sourceLevel forces inner < sourceLevel (else the candidate is empty), decodes to SN ∧ reducible-at-inner,
-- and that same decoded predicate is the candidate at outerLevel (also above inner).
theorem universeDomainMemberStableToOuter {scope : Nat} (env : Nat → Nat) (outerLevel : Nat)
    (innerLevelExpr : LevelExpr) (innerFlag : UniverseFlag)
    (innerBelowOuter : LevelExpr.denote innerLevelExpr env < outerLevel)
    (sourceLevel : Nat) (argument : RawTerm scope)
    (memberAtSource : IsReducibleMemberAtDenote env sourceLevel
      (.mkGen .gen_universeCode (innerLevelExpr, innerFlag) .childNil) argument) :
    IsReducibleMemberAtDenote env outerLevel
      (.mkGen .gen_universeCode (innerLevelExpr, innerFlag) .childNil) argument := by
  obtain ⟨sourceCandidate, sourceReducible, candidateArgument⟩ := memberAtSource
  -- pin the source candidate to the universe predicate at sourceLevel (via determinism)
  have universeArgument : universeDenotePredicate env (denoteBelowFamily env sourceLevel)
      innerLevelExpr argument :=
    (ReducibleTypeAtDenote.deterministic sourceReducible
      (ReducibleTypeStepDenote.universeCode innerLevelExpr innerFlag) argument).mp candidateArgument
  -- a member forces inner < sourceLevel (else the predicate is empty)
  by_cases innerBelowSource : LevelExpr.denote innerLevelExpr env < sourceLevel
  · rw [universeDenotePredicate_belowFamily_aboveThreshold env sourceLevel innerLevelExpr innerBelowSource]
      at universeArgument
    -- universeArgument : SN argument ∧ IsReducibleTypeAtDenote env (denote inner env) argument
    refine ⟨universeDenotePredicate env (denoteBelowFamily env outerLevel) innerLevelExpr,
      ReducibleTypeStepDenote.universeCode innerLevelExpr innerFlag, ?_⟩
    rw [universeDenotePredicate_belowFamily_aboveThreshold env outerLevel innerLevelExpr innerBelowOuter]
    exact universeArgument
  · exact absurd universeArgument (universeDenotePredicate_belowFamily_empty env sourceLevel innerLevelExpr
      (Nat.not_lt.mp innerBelowSource) argument)

#print axioms neutralDomainMemberStableToOuter
#print axioms universeDomainMemberStableToOuter

end FX1Poly.Typed
