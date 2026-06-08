import FX1Poly.Typed.DenoteKeyedGenFormationPiArm
import FX1Poly.Typed.DenoteKeyedSingleLevelPi

/-! Scratch probe: discharge genFormationPi's `piReducibleAsType` premise from the children's reducibility AT THE
    DECODED OUTPUT LEVEL, via the single-level toolkit. Reduces the hard-to-supply piReducibleAsType to the
    primitive children's reducibility the FT recursion naturally supplies. Drift-free (single level). -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

theorem piReducibleAsTypeFromComponentReducibility {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (level : Nat) (context : TypingContext profile scope)
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)} (levelExpr : LevelExpr)
    (domainReducibleAtDecoded : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) (RawTerm.subst substitution domain))
    (codomainReducibleAtDecoded : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        ∀ argument : RawTerm targetScope,
          IsReducibleMemberAtDenote env (LevelExpr.denote levelExpr env)
            (RawTerm.subst substitution domain) argument →
          IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env)
            (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) codomain) argument)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env)
          (RawTerm.subst substitution (piTyCodeCell domain codomain)) := by
  intro _targetScope substitution envReducible
  rw [subst_piTyCodeCell]
  exact piReducibleAtLevelFromComponents env (LevelExpr.denote levelExpr env)
    (domainReducibleAtDecoded substitution envReducible)
    (codomainReducibleAtDecoded substitution envReducible)

#print axioms piReducibleAsTypeFromComponentReducibility

end FX1Poly.Typed
