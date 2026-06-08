import FX1Poly.Typed.DenoteKeyedReducibleEnv
import FX1Poly.Typed.DenoteKeyedUniverseFormationMember

/-! Scratch SN-D4: the denote FT motive + the two LEAF member arms (var, universeFormation).
Motive = under a denote-reducible closing-substitution env at a uniform `level`, the substituted subject is a
denote-reducible member of the substituted classifier (single uniform `level` — the denote route's
level-irrelevance lets one ambient level suffice, no per-variable level vector). var = lookupReducible;
universeFormation = universeFormationMemberUnderClosingSubstitution (carries the levelAbove side condition). -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

def FundamentalConclusionAtDenote {profile : PolyProfile} {scope : Nat} (env : Nat → Nat) (level : Nat)
    (context : TypingContext profile scope) (subject classifier : RawTerm scope) : Prop :=
  ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
    ReducibleEnvAtDenote env level context substitution →
    IsReducibleMemberAtDenote env level
      (RawTerm.subst substitution classifier) (RawTerm.subst substitution subject)

theorem fundamentalVarAtDenote {profile : PolyProfile} {scope : Nat} (env : Nat → Nat) (level : Nat)
    (context : TypingContext profile scope) (index : Fin scope) :
    FundamentalConclusionAtDenote env level context (variableCell index) (context.lookup index) := by
  intro targetScope substitution envReducible
  exact ReducibleEnvAtDenote.lookupReducible envReducible index

theorem fundamentalUniverseFormationAtDenote {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (level : Nat) (context : TypingContext profile scope) (levelExpr : LevelExpr) (flag : UniverseFlag)
    (levelAbove : LevelExpr.denote (LevelExpr.lsucc levelExpr) env < level) :
    FundamentalConclusionAtDenote env level context
      (universeCodeCell levelExpr flag) (universeCodeCell levelExpr.lsucc flag) := by
  intro targetScope substitution _envReducible
  exact universeFormationMemberUnderClosingSubstitution env levelExpr flag level levelAbove substitution

end FX1Poly.Typed

#print axioms FX1Poly.Typed.fundamentalVarAtDenote
#print axioms FX1Poly.Typed.fundamentalUniverseFormationAtDenote
