import FX1Poly.Typed.DenoteKeyedUniverseFormationMember

/-! Scratch: universeFormation member arm under a closing substitution. The universe codes are closed
(childNil), so subst σ leaves them fixed (probe: rfl), reducing to universeFormationMemberAtDenote. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe
open StepStar

-- Probe: subst leaves a closed universe code fixed.
example {scope targetScope : Nat} (σ : RawTermSubst scope targetScope)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    RawTerm.subst σ (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
      = (.mkGen .gen_universeCode (levelExpr, flag) .childNil : RawTerm targetScope) := by
  rfl

theorem universeFormationMemberUnderClosingSubstitution {scope targetScope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) (level : Nat)
    (levelAbove : LevelExpr.denote (LevelExpr.lsucc levelExpr) env < level)
    (substitution : RawTermSubst scope targetScope) :
    IsReducibleMemberAtDenote env level
      (RawTerm.subst substitution
        (.mkGen .gen_universeCode (LevelExpr.lsucc levelExpr, flag) .childNil))
      (RawTerm.subst substitution
        (.mkGen .gen_universeCode (levelExpr, flag) .childNil)) := by
  show IsReducibleMemberAtDenote env level
    (.mkGen .gen_universeCode (LevelExpr.lsucc levelExpr, flag) .childNil)
    (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
  exact universeFormationMemberAtDenote env levelExpr flag level levelAbove

end FX1Poly.Typed

#print axioms FX1Poly.Typed.universeFormationMemberUnderClosingSubstitution
