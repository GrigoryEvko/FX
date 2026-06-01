import FX1Poly.Typed.ReducibleEnvVec
import FX1Poly.Typed.HasTypeSubstitution
import FX1Poly.Core.StratifiedReducibleUniverseDecode

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

end FX1Poly.Typed
