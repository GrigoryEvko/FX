import FX1Poly.Typed.FundamentalAtAllLeafArms
import FX1Poly.Typed.ReducibleEnvVec
import FX1Poly.Typed.ReducibleSemanticRules

/-! # FX1Poly/Typed/FundamentalLevelIndexed
    — the decoupled-`subjectLevel` fundamental-theorem conclusion (Route 2: dependent FT, var-level wall).

The dependent fundamental theorem's recursor needs a single `motive_1`, but the existing conclusion shapes
force a level mismatch that blocks the dependent binder:

* `IsFundamentalConclusionAtVector` fixes the conclusion at a uniform `predLevel+1`, DECOUPLED from the
  per-variable environment levels.  `var` is reducible only at its OWN stored level `contextLevels index`,
  so the var arm closes only when `contextLevels index = predLevel+1` — false for arbitrary level vectors,
  hence unprovable in general.
* `IsFundamentalConclusionAtUniformVector` fixes everything at `predLevel+1`, validating `var` but NOT the
  fully dependent formation telescope, whose codomain wants the bound argument ONE LEVEL LOWER (`tarskiDecode`:
  a universe member at `L` decodes to a reducible type at `L-1`, so the domain's members sit at `predLevel`
  while the conclusion is at `predLevel+1`).

The fix is the per-tower-rung indexing the committed `ReducibleEnvVec` (Abel/Adjedj MLTT logical relation)
already supports: conclude at a SEPARATE `subjectLevel` parameter rather than a uniform `predLevel+1`.  Then
`var index` concludes at exactly `contextLevels index` (its own environment level) — a DIRECT
`ReducibleEnvVec.lookupReducible`, no level-equality side condition — while the elimination/formation arms
that preserve the level thread it unchanged, and the binder (next) installs the bound argument one rung
lower via `ReducibleEnvVec.cons` / `levelCons`.

This file ships the conclusion predicate and the three LEVEL-PRESERVING arms (`var`, `universeFormation`,
`piElim`), establishing the design is viable (it composes — `piElim` chains two sub-conclusions at the same
`subjectLevel` via `applicationUnderSubst`).  The level-CHANGING arms (`conv` and the binder/`genFormation`,
which carry the `tarskiDecode` `+1`/`-1`) are the remaining Route-2 work.

* `FundamentalConclusionLevelIndexed` — subject reducible at `subjectLevel` under a `ReducibleEnvVec` at
  `contextLevels`.
* `fundamentalVarLevelIndexed` — the var arm, off-by-one-free by construction (conclusion = the var's own
  level).
* `fundamentalUniverseFormationLevelIndexed` — `Type@e ∈ Type@(lsucc e)` at `predLevel+1`.
* `fundamentalPiElimLevelIndexed` — application preserves `subjectLevel` (the level is a uniform fuel).

## Zero-axiom verification

`var` is `ReducibleEnvVec.lookupReducible`; `universeFormation` is `IsReducibleMemberAt.universeFormation`
after `subst_universeCodeCell`; `piElim` is `IsReducibleMemberAt.applicationUnderSubst` on the two
sub-conclusions.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The decoupled-level fundamental-theorem conclusion.**  Under a closing substitution and a
per-variable-level reducible environment (`ReducibleEnvVec contextLevels`, each variable at its OWN rung
level), the subject is a reducible member of its classifier at `subjectLevel` — a parameter SEPARATE from
the environment's level vector.  Decoupling the conclusion level from a uniform value is what lets the `var`
arm conclude at its own environment level and the binder thread the codomain one rung lower. -/
def FundamentalConclusionLevelIndexed {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (subjectLevel : Nat)
    (context : TypingContext profile scope) (subject classifier : RawTerm scope) : Prop :=
  ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1)),
    ReducibleEnvVec contextLevels context substitution →
    IsReducibleMemberAt subjectLevel (RawTerm.subst substitution classifier)
      (RawTerm.subst substitution subject)

/-- **The `var` arm, off-by-one-free by construction.**  A variable concludes at exactly its own
context-level `contextLevels index` — precisely the level the per-variable environment stores it at — so the
arm is a direct `ReducibleEnvVec.lookupReducible`, with no level-equality side condition.  This is the
resolution of the vector-shape `var` wall. -/
theorem fundamentalVarLevelIndexed {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (context : TypingContext profile scope) (index : Fin scope) :
    FundamentalConclusionLevelIndexed contextLevels (contextLevels index) context
      (variableCell index) (context.lookup index) :=
  fun _substitution env => ReducibleEnvVec.lookupReducible env index

/-- **The `universeFormation` arm.**  `Type@e` is a reducible member of `Type@(lsucc e)` at `predLevel+1`;
the universe code is closed, so the arm holds at any context-level vector. -/
theorem fundamentalUniverseFormationLevelIndexed {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (predLevel : Nat)
    (context : TypingContext profile scope) (levelExpr : LevelExpr) (flag : UniverseFlag) :
    FundamentalConclusionLevelIndexed contextLevels (predLevel + 1) context
      (universeCodeCell levelExpr flag) (universeCodeCell levelExpr.lsucc flag) := by
  intro _targetScope substitution _env
  rw [subst_universeCodeCell, subst_universeCodeCell]
  exact IsReducibleMemberAt.universeFormation predLevel levelExpr flag

/-- **The `piElim` (application) arm.**  Application preserves the (uniform) `subjectLevel`:
`applicationUnderSubst` takes the function (a member of the Π-code) and the argument (a member of the domain)
at the SAME level and produces the application at that level — the level is a uniform fuel, not a per-type
universe level.  No level change here; the level decrease is confined to the binder.  This composition is
what shows the decoupled-level conclusion is a viable recursor motive. -/
theorem fundamentalPiElimLevelIndexed {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (subjectLevel : Nat)
    {context : TypingContext profile scope}
    {functionTerm argument domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (functionFundamental : FundamentalConclusionLevelIndexed contextLevels subjectLevel context functionTerm
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))))
    (argumentFundamental : FundamentalConclusionLevelIndexed contextLevels subjectLevel context argument
      domainCode) :
    FundamentalConclusionLevelIndexed contextLevels subjectLevel context
      (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil)))
      (RawTerm.subst0 codomainCode argument) := by
  intro _targetScope substitution env
  exact IsReducibleMemberAt.applicationUnderSubst substitution
    (functionFundamental substitution env) (argumentFundamental substitution env)

end FX1Poly.Typed
