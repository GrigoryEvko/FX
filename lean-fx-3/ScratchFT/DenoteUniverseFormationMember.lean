import FX1Poly.Typed.DenoteKeyedReducibility

/-! Scratch D-leaf: the denote universeFormation member — `Type@e` is a denote-reducible MEMBER of
`Type@(lsucc e)`. This is the semantic content of the denote fundamental theorem's universeFormation arm (and
the denote-layer universe hierarchy / no-Type-in-Type): the classifier `Type@(lsucc e)`'s candidate (above its
decoded level) is `SN ∧ reducible-at-denote(lsucc e)`, and `Type@e` is SN (a normal form) and reducible at
every denote level (`universeCode_isReducibleAtDenote`). -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe
open StepStar

theorem universeFormationMemberAtDenote {scope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) (level : Nat)
    (levelAbove : LevelExpr.denote (LevelExpr.lsucc levelExpr) env < level) :
    IsReducibleMemberAtDenote (scope := scope) env level
      (.mkGen .gen_universeCode (LevelExpr.lsucc levelExpr, flag) .childNil)
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil) :=
  ⟨fun member => IsStronglyNormalizing member ∧
      IsReducibleTypeAtDenote env (LevelExpr.denote (LevelExpr.lsucc levelExpr) env) member,
    universeMembership_levelIrrelevant env level (LevelExpr.lsucc levelExpr) flag levelAbove,
    isStronglyNormalizing_of_noStep (fun _target => noStep_universeCode (levelExpr, flag)),
    universeCode_isReducibleAtDenote env (LevelExpr.denote (LevelExpr.lsucc levelExpr) env) levelExpr flag⟩

end FX1Poly.Typed

#print axioms FX1Poly.Typed.universeFormationMemberAtDenote
