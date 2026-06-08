import FX1Poly.Typed.BoundedUniverseInversion
import FX1Poly.Typed.DenoteKeyedBoundedGenFormationPiArm
import FX1Poly.Typed.BoundedGrownFundamental

/-! Probe (NEVER committed): OB-2b — universe-typed subject is reducible-as-type under a reducible env.
    FT → subst_universeCodeCell → OB-2a belowBound → decode → cumulativity. -/

namespace FX1Poly.Typed.Spike
open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

theorem subjectReducibleAsTypeUnderEnv {profile : PolyProfile} {scope targetScope : Nat}
    {env : Nat → Nat} {bound : Nat} {restContext : TypingContext profile scope}
    {bindingType : RawTerm scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (descPiDeriv : HasTypeDescPi profile restContext bindingType (universeCodeCell levelExpr flag))
    (budget : BoundExceedsPi env bound descPiDeriv)
    {substitution : RawTermSubst scope (targetScope + 1)}
    (envReducible : ReducibleEnvAtBounded env bound restContext substitution) :
    IsReducibleTypeAtBounded env bound (RawTerm.subst substitution bindingType) := by
  have member := HasTypeDescPi.fundamentalAtBoundedSucc env bound descPiDeriv budget substitution envReducible
  rw [subst_universeCodeCell] at member
  obtain ⟨candidate, candidateReducible, candidateMember⟩ := member
  have belowBound := belowBound_of_reducibleUniverse candidateReducible
  exact isReducibleBounded_cumulative
    (universeMemberReducibleAsTypeAtDecodedLevelBounded
      ⟨candidate, candidateReducible, candidateMember⟩ belowBound)
    (Nat.le_of_lt belowBound)

end FX1Poly.Typed.Spike

#print axioms FX1Poly.Typed.Spike.subjectReducibleAsTypeUnderEnv
