import FX1Poly.Typed.DenoteKeyedUniverseDomainPiArm
import FX1Poly.Typed.DenoteKeyedReducibilitySmoke

/-! Scratch probe: RIGOROUSLY confirm a universe-code Type@inner is NOT all-levels member-stable — so it canNOT
    satisfy the composite arm's domainStable/codomainStable premise. This pins the #672 residual: threshold-drift
    composites (Π/Σ with universe-code COMPONENTS) are NOT closed by compositeDomainMemberStableToOuter. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

theorem universeCodeNotAllLevelsMemberStable {scope : Nat} (env : Nat → Nat)
    (innerLevelExpr : LevelExpr) (innerFlag : UniverseFlag) (index : Fin scope) :
    ¬ (∀ (sourceLevel targetLevel : Nat) (argument : RawTerm scope),
        IsReducibleMemberAtDenote env sourceLevel
          (.mkGen .gen_universeCode (innerLevelExpr, innerFlag) .childNil) argument →
        IsReducibleMemberAtDenote env targetLevel
          (.mkGen .gen_universeCode (innerLevelExpr, innerFlag) .childNil) argument) := by
  intro stability
  -- var index is a reducible member of Type@inner at the level just above inner (decode aboveThreshold)
  have memberHigh : IsReducibleMemberAtDenote env (LevelExpr.denote innerLevelExpr env + 1)
      (.mkGen .gen_universeCode (innerLevelExpr, innerFlag) .childNil)
      (.mkGen .gen_var index .childNil) := by
    refine ⟨universeDenotePredicate env
      (denoteBelowFamily env (LevelExpr.denote innerLevelExpr env + 1)) innerLevelExpr,
      ReducibleTypeStepDenote.universeCode innerLevelExpr innerFlag, ?_⟩
    rw [universeDenotePredicate_belowFamily_aboveThreshold env (LevelExpr.denote innerLevelExpr env + 1)
      innerLevelExpr (Nat.lt_succ_self _)]
    exact ⟨isStronglyNormalizing_of_noStep (fun _reduct step => noStep_var index step),
      smoke_neutralVariable_isReducibleAtDenote env (LevelExpr.denote innerLevelExpr env) index⟩
  -- stability would carry it down to level 0, where the candidate is empty
  obtain ⟨candidateZero, reducibleZero, candidateVar⟩ :=
    stability (LevelExpr.denote innerLevelExpr env + 1) 0 (.mkGen .gen_var index .childNil) memberHigh
  have universeZero : universeDenotePredicate env (denoteBelowFamily env 0) innerLevelExpr
      (.mkGen .gen_var index .childNil) :=
    (ReducibleTypeAtDenote.deterministic reducibleZero
      (ReducibleTypeStepDenote.universeCode innerLevelExpr innerFlag) _).mp candidateVar
  exact universeDenotePredicate_belowFamily_empty env 0 innerLevelExpr (Nat.zero_le _)
    (.mkGen .gen_var index .childNil) universeZero

#print axioms universeCodeNotAllLevelsMemberStable

end FX1Poly.Typed
