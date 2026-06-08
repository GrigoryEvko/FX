import FX1Poly.Typed.DenoteKeyedUniverseDomainPi
import FX1Poly.Typed.DenoteKeyedLevelIrrelevance

/-! Scratch A1: extend the universe-domain Π from `∀ level > denote e env` to ALL levels (the
`IsReducibleTypeAtAllDenoteLevels` shape the backbone's piArm consumes). High levels: last tick's theorem.
Low levels (`level ≤ denote e env`): the domain `Type@e` candidate is EMPTY there
(`denoteBelowFamily_eq_empty_of_ge`), so `piType` fires vacuously. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe
open StepStar

theorem universeDomainPi_reducibleAtEveryDenoteLevel {scope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) {codomainCode : RawTerm (scope + 1)}
    (codomainCandidate : RawTerm scope → (RawTerm scope → Prop))
    (codomainReducible : ∀ (level : Nat), LevelExpr.denote levelExpr env < level →
      ∀ argument : RawTerm scope,
        (IsStronglyNormalizing argument ∧
          IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) argument) →
          ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
            (codomainCandidate argument)) :
    IsReducibleTypeAtAllDenoteLevels env
      (.mkGen .gen_piTyCode () (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
        (.childCons codomainCode .childNil))) := by
  intro level
  by_cases levelAbove : LevelExpr.denote levelExpr env < level
  · exact universeDomainPi_reducibleAtAllDenoteLevels env levelExpr flag codomainCandidate
      codomainReducible level levelAbove
  · have levelLe : level ≤ LevelExpr.denote levelExpr env := Nat.not_lt.mp levelAbove
    refine ⟨_, ReducibleTypeStepDenote.piType (fun _ => IsStronglyNormalizing)
      (ReducibleTypeStepDenote.universeCode levelExpr flag) (fun argument argInDomain => ?_)⟩
    obtain ⟨_argSN, _cand, hcand⟩ := argInDomain
    rw [denoteBelowFamily_eq_empty_of_ge env level (LevelExpr.denote levelExpr env) levelLe] at hcand
    exact hcand.elim

end FX1Poly.Typed

#print axioms FX1Poly.Typed.universeDomainPi_reducibleAtEveryDenoteLevel
