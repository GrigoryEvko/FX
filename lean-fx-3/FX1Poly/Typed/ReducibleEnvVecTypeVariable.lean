import FX1Poly.Typed.ReducibleEnvVec
import FX1Poly.Typed.CellSubstitution
import FX1Poly.Core.StratifiedReducibleUniverseDecode
import FX1Poly.Core.StratifiedReducibleMemberNeutral

/-! # FX1Poly/Typed/ReducibleEnvVecTypeVariable
    — the TYPE fundamental-theorem's `var` arm: a type variable is a reducible type one tower-rung down

The dependent fundamental theorem is two interlocking judgments — a TERM half (`subject` is a reducible
member of `classifier`) and a TYPE half (when `classifier` is a universe code, `subject` is a reducible
TYPE).  The term half's `var` arm is `ReducibleEnvVec.lookupReducible` (the substitute is a reducible member
at the variable's own tower level).  This file ships the TYPE half's `var` arm: when a context variable's
looked-up type is a universe code `Type@levelExpr` — i.e. the variable is a TYPE variable — the closing
substitution sends it to a reducible TYPE, at the level ONE BELOW its environment level.

The "one below" is the Tarski universe semantics (`tarskiDecode`): membership in `Type@e` at fuel `L + 1`
is exactly reducible-type-hood at fuel `L`.  The environment hands the type variable to a member of
`universeCodeCell levelExpr flag` at `levels index`; pinning `levels index = predLevel + 1` and decoding
yields its reducibility as a type at `predLevel`.  This is precisely the shape the fundamental theorem's
`conv` and `piIntro` arms consume to obtain a TYPE premise's reducibility at a type-variable leaf without
re-running the term induction — the structure the `ReducibleEnvAt` design note calls "the universe arm
carries each type variable's candidate one level down".

## Zero-axiom verification

`lookupReducible` is the environment projection; the three rewrites are the universe-code substitution
identity (`subst_universeCodeCell`, `rfl`), the looked-up-type hypothesis, and the level-pinning hypothesis;
`tarskiDecode` is the propext-free universe-membership inversion.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Foundation FX1Poly.Universe

/-- **The TYPE fundamental theorem's `var` arm.**  A per-variable-level reducible environment sends a TYPE
variable — one whose looked-up type is the universe code `Type@levelExpr` — to a reducible TYPE, at the level
one rung below the variable's environment level (`tarskiDecode` of the environment's universe membership).
The type-half companion to `ReducibleEnvVec.lookupReducible`; consumed by the dependent fundamental theorem's
`conv` / `piIntro` arms to discharge a type-premise leaf without bumping the term induction. -/
theorem ReducibleEnvVec.typeVariableReducible {profile : PolyProfile} {scope targetScope : Nat}
    {levels : Fin scope → Nat} {context : TypingContext profile scope}
    {substitution : RawTermSubst scope targetScope}
    (envReducible : ReducibleEnvVec levels context substitution) (index : Fin scope)
    {predLevel : Nat} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (lookupIsUniverse : context.lookup index = universeCodeCell levelExpr flag)
    (levelIsSucc : levels index = predLevel + 1) :
    IsReducibleTypeAt predLevel (substitution index) := by
  have member := envReducible.lookupReducible index
  rw [lookupIsUniverse, subst_universeCodeCell, levelIsSucc] at member
  exact member.tarskiDecode

/-- **A syntactic TYPE variable is an all-level reducible member of its universe.**  A variable `var index`
whose type is the universe code `Type@levelExpr` is a reducible member of that universe at EVERY positive level
`predLevel + 1` — because the universe code is a reducible TYPE at every level (`IsReducibleTypeAt.universeCode`,
level-polymorphic), and a variable inhabits any reducible type (`IsReducibleMemberAt.variable`).

This is the SYNTACTIC fact (no closing substitution) behind why a type variable could in principle serve as a
former DOMAIN: a Π/Σ former needs its domain reducible at TWO consecutive fuel levels (`predLevel + 1` and
`predLevel + 2`, per `IsReducibleMemberAt.piFormerOfChildMemberships`), and a type variable supplies BOTH (it is
all-level).  The current per-variable-level environment (`ReducibleEnvVec`) pins each variable to its ONE env
level `levels index`, so it does NOT expose this all-level membership under a closing substitution — that is the
documented all-level-vs-per-level environment crux the dependent former arm runs into.  This lemma records that
the obstruction is purely the ENVIRONMENT design (a type variable is intrinsically level-polymorphic), not an
intrinsic single-level limitation of variables: an all-level environment for type-variable entries would
discharge the dependent former DOMAIN directly through this membership. -/
theorem typeVariableAllLevelMember {scope : Nat} (index : Fin (scope + 1))
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ∀ predLevel : Nat,
      IsReducibleMemberAt (predLevel + 1)
        (universeCodeCell levelExpr flag : RawTerm (scope + 1)) (variableCell index) := by
  intro predLevel
  obtain ⟨_candidate, reducible⟩ := IsReducibleTypeAt.universeCode (predLevel + 1) levelExpr flag
  exact IsReducibleMemberAt.variable reducible index

end FX1Poly.Typed
