import FX1Poly.Typed.DenoteKeyedGenFormationPiArm
import FX1Poly.Typed.DenoteKeyedSingleLevelPi

/-! Scratch probe: discharge genFormationPi's `piReducibleAsType` for the FULLY-UNIFORM Π fragment
    (domain and codomain both classified at the SAME universe `levelExpr`) directly from the children's
    universe-MEMBERSHIPS — no level lift, no #752 piArm. Composes the shipped connector
    `piReducibleAsTypeFromComponentReducibility` with `universeMemberReducibleAsTypeAtDecodedLevel`
    on BOTH children. The two memberships are at `Type@levelExpr` (the Π's own output universe), so each
    decodes to reducibility AT `denote levelExpr env` with no cumulativity lift. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

theorem piReducibleAsTypeFromUniformLevelMember {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (level : Nat) (context : TypingContext profile scope)
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)} (levelExpr : LevelExpr)
    (domainFlag codomainFlag : UniverseFlag)
    (levelAbove : LevelExpr.denote levelExpr env < level)
    (domainMember : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsReducibleMemberAtDenote env level
          (universeCodeCell levelExpr domainFlag) (RawTerm.subst substitution domain))
    (codomainMember : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        ∀ argument : RawTerm targetScope,
          IsReducibleMemberAtDenote env (LevelExpr.denote levelExpr env)
            (RawTerm.subst substitution domain) argument →
          IsReducibleMemberAtDenote env level
            (universeCodeCell levelExpr codomainFlag)
            (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) codomain) argument)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env)
          (RawTerm.subst substitution (piTyCodeCell domain codomain)) :=
  piReducibleAsTypeFromComponentReducibility env level context levelExpr
    (fun substitution envReducible =>
      universeMemberReducibleAsTypeAtDecodedLevel (domainMember substitution envReducible) levelAbove)
    (fun substitution envReducible argument argumentMember =>
      universeMemberReducibleAsTypeAtDecodedLevel
        (codomainMember substitution envReducible argument argumentMember) levelAbove)

#print axioms piReducibleAsTypeFromUniformLevelMember

end FX1Poly.Typed
