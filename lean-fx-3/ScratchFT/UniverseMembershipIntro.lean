import FX1Poly.Typed.DenoteKeyedUniverseFormationMember
import FX1Poly.Typed.DenoteKeyedFundamentalMotive

/-! Probe: the GENERAL universe-membership introduction over the denote relation
    + its FT-shaped consumer (the type-former arm modulo route-A reducibility). -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

theorem universeMembershipIntroAtDenote {scope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) (level : Nat) (typeCode : RawTerm scope)
    (levelAbove : LevelExpr.denote levelExpr env < level)
    (typeCodeSN : IsStronglyNormalizing typeCode)
    (typeCodeReducible : IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) typeCode) :
    IsReducibleMemberAtDenote env level
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
      typeCode :=
  ⟨fun member => IsStronglyNormalizing member ∧
      IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) member,
    universeMembership_levelIrrelevant env level levelExpr flag levelAbove,
    typeCodeSN,
    typeCodeReducible⟩

/-- The existing universeFormation member arm is the closed-universe-code instance. -/
theorem universeFormationMemberAtDenote_viaIntro {scope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) (level : Nat)
    (levelAbove : LevelExpr.denote (LevelExpr.lsucc levelExpr) env < level) :
    IsReducibleMemberAtDenote (scope := scope) env level
      (.mkGen .gen_universeCode (LevelExpr.lsucc levelExpr, flag) .childNil)
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil) :=
  universeMembershipIntroAtDenote env (LevelExpr.lsucc levelExpr) flag level
    (.mkGen .gen_universeCode (levelExpr, flag) .childNil) levelAbove
    (isStronglyNormalizing_of_noStep (fun _target => noStep_universeCode (levelExpr, flag)))
    (universeCode_isReducibleAtDenote env (LevelExpr.denote (LevelExpr.lsucc levelExpr) env) levelExpr flag)

/-- FT-shaped: a former that is a denote-reducible SN type at its decoded level under every
    closing substitution satisfies the FT conclusion at its universe classifier. The type-former
    FT arm (universeFormation / piFormation / genFormationPi) MODULO route-A reducibility. -/
theorem fundamentalTypeFormerAtDenote {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (level : Nat) (context : TypingContext profile scope) (typeFormer : RawTerm scope)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (levelAbove : LevelExpr.denote levelExpr env < level)
    (formerReducible : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsStronglyNormalizing (RawTerm.subst substitution typeFormer) ∧
        IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env)
          (RawTerm.subst substitution typeFormer)) :
    FundamentalConclusionAtDenote env level context typeFormer (universeCodeCell levelExpr flag) := by
  intro _targetScope substitution envReducible
  obtain ⟨formerSN, formerRed⟩ := formerReducible substitution envReducible
  show IsReducibleMemberAtDenote env level
    (.mkGen .gen_universeCode (levelExpr, flag) .childNil) (RawTerm.subst substitution typeFormer)
  exact universeMembershipIntroAtDenote env levelExpr flag level
    (RawTerm.subst substitution typeFormer) levelAbove formerSN formerRed

end FX1Poly.Typed

#print axioms FX1Poly.Typed.universeMembershipIntroAtDenote
#print axioms FX1Poly.Typed.universeFormationMemberAtDenote_viaIntro
#print axioms FX1Poly.Typed.fundamentalTypeFormerAtDenote
