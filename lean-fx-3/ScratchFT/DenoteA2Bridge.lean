import FX1Poly.Typed.DenoteKeyedLevelIrrelevance

/-! Scratch SN-D5-A2bridge: universe-membership → ambient-level reducibility, the shared conv+piIntro residual.
From `X : Type@levelExpr` at ambient `level` (with denote levelExpr env < level), conclude X reducible AT level.
Unpacking: the universe membership's candidate is `universeDenotePredicate` (via candidateIffUniverse), whose ∃
conjunct gives X reducible in `denoteBelowFamily env level (denote levelExpr env)` = `ReducibleTypeAtDenote env
(denote levelExpr env)` (via denoteBelowFamily_eq_reducible, needs the levelAbove bound). Then
`ofReducibleTypeStepDenote` (parametric over the composite-domain piArm at the decoded level) lifts to all levels
⟹ at `level`. Parametric over EXACTLY the ofReducibleTypeStepDenote piArm — the one shared A2 residual. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe
open StepStar

theorem universeMemberReducibleAtLevel {scope : Nat} {env : Nat → Nat} {level : Nat}
    {levelExpr : LevelExpr} {flag : UniverseFlag} {X : RawTerm scope}
    (piArm : ∀ {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
        {domainCandidate : RawTerm scope → Prop}
        (codomainCandidate : RawTerm scope → (RawTerm scope → Prop)),
        ReducibleTypeStepDenote env (denoteBelowFamily env (LevelExpr.denote levelExpr env))
          domainCode domainCandidate →
        (∀ argument : RawTerm scope, domainCandidate argument →
          ReducibleTypeStepDenote env (denoteBelowFamily env (LevelExpr.denote levelExpr env))
            (RawTerm.subst0 codomainCode argument) (codomainCandidate argument)) →
        IsReducibleTypeAtAllDenoteLevels env domainCode →
        (∀ argument : RawTerm scope, domainCandidate argument →
          IsReducibleTypeAtAllDenoteLevels env (RawTerm.subst0 codomainCode argument)) →
        IsReducibleTypeAtAllDenoteLevels env
          (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))))
    (memberOfUniverse : IsReducibleMemberAtDenote env level
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil) X)
    (levelAbove : LevelExpr.denote levelExpr env < level) :
    IsReducibleTypeAtDenote env level X := by
  obtain ⟨cand, reducibleUniv, candX⟩ := memberOfUniverse
  have candIff := ReducibleTypeStepDenote.candidateIffUniverse reducibleUniv
    (levelExpr := levelExpr) (flag := flag) rfl
  have univX := (candIff X).mp candX
  obtain ⟨_snX, decodeCandidate, denoteReducibleX⟩ := univX
  rw [denoteBelowFamily_eq_reducible env level (LevelExpr.denote levelExpr env) levelAbove]
    at denoteReducibleX
  exact IsReducibleTypeAtAllDenoteLevels.ofReducibleTypeStepDenote piArm denoteReducibleX level

end FX1Poly.Typed

#print axioms FX1Poly.Typed.universeMemberReducibleAtLevel
