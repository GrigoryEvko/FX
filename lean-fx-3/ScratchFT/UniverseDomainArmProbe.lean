import FX1Poly.Typed.DenoteKeyedUniverseDomainPi
import FX1Poly.Typed.DenoteKeyedCanonicalMemberCandidate

/-! Scratch probe: the universeCode arm of the ofReducibleTypeStepDenote piArm case-split — the
    threshold-gated universe-domain arm. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

theorem universeDenotePredicate_belowFamily_aboveThreshold {scope : Nat} (env : Nat → Nat)
    (outerLevel : Nat) (innerLevelExpr : LevelExpr)
    (innerBelow : LevelExpr.denote innerLevelExpr env < outerLevel)
    (typeCode : RawTerm scope) :
    universeDenotePredicate env (denoteBelowFamily env outerLevel) innerLevelExpr typeCode
      = (IsStronglyNormalizing typeCode ∧
          IsReducibleTypeAtDenote env (LevelExpr.denote innerLevelExpr env) typeCode) := by
  unfold universeDenotePredicate IsReducibleTypeAtDenote
  rw [denoteBelowFamily_eq_reducible env outerLevel (LevelExpr.denote innerLevelExpr env) innerBelow]

theorem universeDenotePredicate_belowFamily_empty {scope : Nat} (env : Nat → Nat)
    (outerLevel : Nat) (innerLevelExpr : LevelExpr)
    (innerAtOrAbove : outerLevel ≤ LevelExpr.denote innerLevelExpr env)
    (typeCode : RawTerm scope) :
    ¬ universeDenotePredicate env (denoteBelowFamily env outerLevel) innerLevelExpr typeCode := by
  intro membership
  obtain ⟨_strongNormalizing, _candidate, candidateMember⟩ := membership
  rw [denoteBelowFamily_eq_empty_of_ge env outerLevel (LevelExpr.denote innerLevelExpr env)
    innerAtOrAbove] at candidateMember
  exact candidateMember

/-- The universeCode arm of the ofReducibleTypeStepDenote piArm: when the domain is a universe code
    `Type@innerLevelExpr` strictly below the outer classifier's level, the dependent Π is reducible at every
    denote level — fed by the backbone's existential-candidate codomain IH (keyed on the universe membership). -/
theorem universeDomainPiArmFromInductiveHypotheses {scope : Nat} (env : Nat → Nat) (outerLevel : Nat)
    (innerLevelExpr : LevelExpr) (innerFlag : UniverseFlag) {codomainCode : RawTerm (scope + 1)}
    (innerBelowOuter : LevelExpr.denote innerLevelExpr env < outerLevel)
    (codomainInductiveHypothesis : ∀ argument : RawTerm scope,
        universeDenotePredicate env (denoteBelowFamily env outerLevel) innerLevelExpr argument →
        IsReducibleTypeAtAllDenoteLevels env (RawTerm.subst0 codomainCode argument)) :
    IsReducibleTypeAtAllDenoteLevels env
      (.mkGen .gen_piTyCode ()
        (.childCons (.mkGen .gen_universeCode (innerLevelExpr, innerFlag) .childNil)
          (.childCons codomainCode .childNil))) := by
  intro outputLevel
  refine ⟨_, ReducibleTypeStepDenote.piType
    (fun argument => IsReducibleMemberAtDenote env outputLevel (RawTerm.subst0 codomainCode argument))
    (ReducibleTypeStepDenote.universeCode innerLevelExpr innerFlag)
    (fun argument argumentInDomain => ?_)⟩
  by_cases aboveAtOutput : LevelExpr.denote innerLevelExpr env < outputLevel
  · have backboneMembership :
        universeDenotePredicate env (denoteBelowFamily env outerLevel) innerLevelExpr argument := by
      rw [universeDenotePredicate_belowFamily_aboveThreshold env outerLevel innerLevelExpr innerBelowOuter]
      rw [universeDenotePredicate_belowFamily_aboveThreshold env outputLevel innerLevelExpr aboveAtOutput]
        at argumentInDomain
      exact argumentInDomain
    exact (codomainInductiveHypothesis argument backboneMembership outputLevel).reducibleMemberCandidate
  · exact absurd argumentInDomain (universeDenotePredicate_belowFamily_empty env outputLevel innerLevelExpr
      (Nat.not_lt.mp aboveAtOutput) argument)

#print axioms universeDenotePredicate_belowFamily_aboveThreshold
#print axioms universeDenotePredicate_belowFamily_empty
#print axioms universeDomainPiArmFromInductiveHypotheses

end FX1Poly.Typed
