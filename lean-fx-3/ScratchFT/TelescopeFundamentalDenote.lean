import FX1Poly.Typed.DenoteKeyedTelescopeReducible
import FX1Poly.Typed.DenoteKeyedFundamentalMotive
import FX1Poly.Typed.HasTypeSubstitution

/-! Probe: the denote telescope FT companion (nil + cons arms) — the structural
    counterpart of the fuel `fundamentalTelescopeNilAtAll`/`fundamentalTelescopeConsAtAll`,
    single-level (no `∀ level` over the head, no level vector). Step 1 of the
    genFormationPi arm: DescTelescopePi + per-child FundamentalConclusionAtDenote
    ⟹ TelescopeReducibleAtDenote (the children reducible). -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

theorem fundamentalTelescopeNilAtDenote {baseScope targetScope currentDepth : Nat}
    (env : Nat → Nat) (level : Nat) {flag : UniverseFlag}
    {substitution : RawTermSubst (baseScope + currentDepth) targetScope} :
    TelescopeReducibleAtDenote env level flag currentDepth 0 substitution []
      (.childNil : RawTermChildren (consecutiveShifts currentDepth 0) baseScope) :=
  True.intro

theorem fundamentalTelescopeConsAtDenote {profile : PolyProfile}
    {baseScope targetScope currentDepth count : Nat} (env : Nat → Nat) (level : Nat)
    {context : TypingContext profile (baseScope + currentDepth)}
    {head : RawTerm (baseScope + currentDepth)}
    {restLevels : List LevelExpr} {flag : UniverseFlag}
    {rest : RawTermChildren (consecutiveShifts (currentDepth + 1) count) baseScope}
    {headLevel : LevelExpr}
    {substitution : RawTermSubst (baseScope + currentDepth) targetScope}
    (reducibleEnv : ReducibleEnvAtDenote env level context substitution)
    (headFundamental :
      FundamentalConclusionAtDenote env level context head (universeCodeCell headLevel flag))
    (tailReducible :
      ∀ (argument : RawTerm targetScope),
        IsReducibleMemberAtDenote env level (RawTerm.subst substitution head) argument →
        TelescopeReducibleAtDenote env level flag (currentDepth + 1) count
          (RawTermSubst.cons argument substitution) restLevels rest) :
    TelescopeReducibleAtDenote env level flag currentDepth (count + 1) substitution
      (headLevel :: restLevels) (.childCons head rest) :=
  ⟨by have headMember := headFundamental substitution reducibleEnv
      rwa [subst_universeCodeCell] at headMember,
    fun argument argumentMember => tailReducible argument argumentMember⟩

end FX1Poly.Typed

#print axioms FX1Poly.Typed.fundamentalTelescopeNilAtDenote
#print axioms FX1Poly.Typed.fundamentalTelescopeConsAtDenote
