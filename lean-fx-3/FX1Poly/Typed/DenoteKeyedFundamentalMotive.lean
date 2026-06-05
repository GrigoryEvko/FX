import FX1Poly.Typed.DenoteKeyedReducibleEnv
import FX1Poly.Typed.DenoteKeyedUniverseFormationMember

/-! # FX1Poly/Typed/DenoteKeyedFundamentalMotive
    — the denote fundamental theorem's conclusion motive + the two LEAF member arms (SN-D4; toward SN-043/#672)

**OFF-PATH CROSSCHECK (supersession map, 2026-06-05): the UNBOUNDED denote fundamental-theorem assembly (SN-D5,
#744/#750/#752/#753) toward SN-043 via the all-level/#672 route — SUPERSEDED by the BFT BOUNDED route
(`DenoteKeyedBoundedReducibility`, OB-5 `closedStronglyNormalizing` / `stronglyNormalizingOfWfContext`), which
closed SN-043 without completing this unbounded FT.  Verified off-path: this FT-assembly is NOT imported by any
`*Bounded` file (the unbounded CORE `DenoteKeyedReducibility` IS shared/load-bearing; this assembly is not).
Retained as a crosscheck, not critical-path.**

The denote analogue of `FundamentalConclusionLevelIndexed` (`FundamentalLevelIndexed.lean:60`): the conclusion
shape of the denote fundamental theorem, plus the two genuine LEAF arms (no induction hypothesis) — `var` and
`universeFormation`.  The recursive arms (`conv`, `piIntro`, `piElim`, `genFormationPi`) carry sub-derivation
IHs / telescope premises and belong to the FT induction assembly (SN-D5).

## The motive — single uniform level

`FundamentalConclusionAtDenote env level context subject classifier`: under a closing substitution and a
denote-reducible environment `ReducibleEnvAtDenote env level context`, the substituted subject is a
denote-reducible member of the substituted classifier, all at ONE uniform ambient `level`.

The decisive simplification over the per-level fuel route (`FundamentalConclusionLevelIndexed`, which threaded a
PER-VARIABLE `contextLevels : Fin scope → Nat` vector plus a separate `subjectLevel`): the denote relation is
LEVEL-IRRELEVANT — a type's candidate is the same decode-set at every level above its decoded universe level —
so a single ambient `level` suffices for the whole judgment, the binder `cons` threading the SAME `level`
(`ReducibleEnvAtDenote.cons` extends at the same level).  This is exactly the structural advantage the
denote re-basing was built to capture: no level vector, no per-rung drift.  The ambient `level` must be taken
above every decoded universe level appearing in the judgment — the `levelAbove` side conditions surface that
obligation locally (here on the `universeFormation` arm); the FT (SN-D5) discharges them by running at a
large-enough ambient level (`ClassifierLevelMeasure.denote_lt_lsucc`).

## The leaf arms

  * `fundamentalVarAtDenote` — a variable concludes directly via `ReducibleEnvAtDenote.lookupReducible`: the
    environment delivers each variable as a denote-reducible member of its looked-up (closed) type, and
    `subst substitution (variableCell index)` is `substitution index` definitionally, so the lookup output IS
    the goal (no rewrite).
  * `fundamentalUniverseFormationAtDenote` — `Type@e` is a denote-reducible member of `Type@(lsucc e)` (the
    member side of no-Type-in-Type), reusing `universeFormationMemberUnderClosingSubstitution`; it carries the
    `levelAbove : denote (lsucc levelExpr) env < level` side condition (the ambient level above the decoded
    classifier level), since the universe code is closed the environment is unused.

## Zero-axiom verification

`var` is `ReducibleEnvAtDenote.lookupReducible` (defeq on the substituted variable); `universeFormation` is a
direct `universeFormationMemberUnderClosingSubstitution`.  No induction, no `funext`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The denote fundamental-theorem conclusion (single uniform level).**  Under a closing substitution and a
denote-reducible environment at the uniform ambient `level`, the substituted subject is a denote-reducible
member of the substituted classifier.  Single `level` (not a per-variable vector): the denote relation's
level-irrelevance lets one ambient level carry the whole judgment, the binder threading the same level. -/
def FundamentalConclusionAtDenote {profile : PolyProfile} {scope : Nat} (env : Nat → Nat) (level : Nat)
    (context : TypingContext profile scope) (subject classifier : RawTerm scope) : Prop :=
  ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
    ReducibleEnvAtDenote env level context substitution →
    IsReducibleMemberAtDenote env level
      (RawTerm.subst substitution classifier) (RawTerm.subst substitution subject)

/-- **The denote `var` arm (leaf).**  A variable is a denote-reducible member of its looked-up type directly
from the environment: `ReducibleEnvAtDenote.lookupReducible` delivers exactly this, and
`subst substitution (variableCell index)` is `substitution index` definitionally, so the lookup IS the goal. -/
theorem fundamentalVarAtDenote {profile : PolyProfile} {scope : Nat} (env : Nat → Nat) (level : Nat)
    (context : TypingContext profile scope) (index : Fin scope) :
    FundamentalConclusionAtDenote env level context (variableCell index) (context.lookup index) := by
  intro _targetScope substitution envReducible
  exact ReducibleEnvAtDenote.lookupReducible envReducible index

/-- **The denote `universeFormation` arm (leaf).**  `Type@levelExpr` is a denote-reducible member of
`Type@(lsucc levelExpr)` — the member side of no-Type-in-Type, under the closing substitution.  Reuses
`universeFormationMemberUnderClosingSubstitution`; carries the `levelAbove` side condition (ambient level above
the decoded classifier level), discharged by the FT at a large-enough ambient level.  The universe code is
closed, so the environment is unused. -/
theorem fundamentalUniverseFormationAtDenote {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (level : Nat) (context : TypingContext profile scope) (levelExpr : LevelExpr) (flag : UniverseFlag)
    (levelAbove : LevelExpr.denote (LevelExpr.lsucc levelExpr) env < level) :
    FundamentalConclusionAtDenote env level context
      (universeCodeCell levelExpr flag) (universeCodeCell levelExpr.lsucc flag) := by
  intro _targetScope substitution _envReducible
  exact universeFormationMemberUnderClosingSubstitution env levelExpr flag level levelAbove substitution

end FX1Poly.Typed
