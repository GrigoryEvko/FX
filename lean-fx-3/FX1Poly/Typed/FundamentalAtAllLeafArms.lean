import FX1Poly.Typed.ReducibleEnvAtAllLevels
import FX1Poly.Typed.ReducibleSemanticRules
import FX1Poly.Core.StratifiedReducibleUniverseDecode

/-! # FX1Poly/Typed/FundamentalAtAllLeafArms
    — the non-telescope arms of the dependent fundamental theorem, over the ∀-level (Kripke) environment

The dependent fundamental theorem assembles over `ReducibleEnvAtAllLevels` (the ∀-level Kripke environment
that dissolves the type-variable off-by-one — see `ReducibleEnvAtAllLevels`).  Its conclusion shape is:

  `FundamentalConclusionAtAll context subject classifier := ∀ targetScope (σ : RawTermSubst scope
      (targetScope+1)) (env : ReducibleEnvAtAllLevels context σ) (predLevel), IsReducibleMemberAt (predLevel+1)
      (σ classifier) (σ subject)`.

This file ships the three NON-recursive / non-telescope arm bodies as standalone, directly-reusable lemmas,
each validated to close over the ∀-level environment:

  * `fundamentalVarAtAll` — the `var` arm.  THE arm the ∀-level environment was built to unblock: a fixed-level
    environment cannot match `var`'s demanded `predLevel+1` against a type variable bound at a different level
    (the universe candidate changes per fuel level, no monotonic cast).  Over `ReducibleEnvAtAllLevels` it is
    immediate: instantiate the all-levels family at the conclusion level (`lookupReducible predLevel`), then
    `subst σ (variableCell index) = σ index` (`subst_var_reduces`).
  * `fundamentalUniverseFormationAtAll` — the `universeFormation` arm: `Type@e : Type@(lsucc e)` at every
    `predLevel+1`, by `IsReducibleMemberAt.universeFormation` after distributing the substitution over the two
    universe codes (`subst_universeCodeCell`).
  * `fundamentalConvAtAll` — the `conv` arm: run the reclassifier's induction hypothesis ONE LEVEL UP
    (`predLevel+1`), `tarskiDecode` its universe membership to a reducible type at `predLevel+1`, and transport
    the subject's membership across the substituted conversion (`castAlongConvUnderSubst`).  The ∀-level
    environment is passed to both induction hypotheses at their respective levels — exactly what the all-levels
    family delivers.

The remaining `genFormation` arm (and the Π-layer `piIntro`) consume a premise telescope; over the ∀-level
environment that needs an all-levels telescope-reducibility predicate (the `cons` extension requires the bound
argument at all levels), a larger separate development.  These three leaf arms confirm the ∀-level environment
closes the dependent fundamental theorem's leaf/conv fragment with zero axioms.

## Zero-axiom verification

`var` = `lookupReducible` + `subst_var_reduces` (`rw`); `universeFormation` = `IsReducibleMemberAt.universeFormation`
+ `subst_universeCodeCell` (`rw`); `conv` = `castAlongConvUnderSubst` ∘ `tarskiDecode` ∘ `subst_universeCodeCell`,
all on shipped zero-axiom lemmas.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The dependent fundamental theorem's conclusion shape over the ∀-level environment.**  A subject is, for
every closing substitution into a non-empty scope and every all-levels reducible environment, a reducible
member of its classifier at each level `predLevel+1`. -/
def FundamentalConclusionAtAll {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (subject classifier : RawTerm scope) : Prop :=
  ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
    (_env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat),
    IsReducibleMemberAt (predLevel + 1) (RawTerm.subst substitution classifier)
      (RawTerm.subst substitution subject)

/-- **The `var` arm over the ∀-level environment** — the off-by-one-free variable case.  Instantiate the
all-levels environment family at the conclusion level and rewrite the substituted variable cell to its
substituent. -/
theorem fundamentalVarAtAll {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (index : Fin scope) :
    FundamentalConclusionAtAll context (variableCell index) (context.lookup index) := by
  intro _targetScope substitution env predLevel
  -- `subst σ (variableCell index) = σ index` definitionally (the var fold branch), so the all-levels
  -- environment lookup at the conclusion level is the goal up to defeq.
  exact env.lookupReducible predLevel index

/-- **The `universeFormation` arm over the ∀-level environment.**  `Type@e` is a reducible member of
`Type@(lsucc e)` at every `predLevel+1`; the substitution distributes over both universe codes. -/
theorem fundamentalUniverseFormationAtAll {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (levelExpr : LevelExpr) (flag : UniverseFlag) :
    FundamentalConclusionAtAll context (universeCodeCell levelExpr flag)
      (universeCodeCell levelExpr.lsucc flag) := by
  intro _targetScope substitution _env predLevel
  rw [subst_universeCodeCell, subst_universeCodeCell]
  exact IsReducibleMemberAt.universeFormation predLevel levelExpr flag

/-- **The `conv` arm over the ∀-level environment.**  Given the subject's induction hypothesis (a reducible
member of the source classifier) and the reclassifier's induction hypothesis (the reclassifier is a member of
a universe), run the reclassifier IH one level up, `tarskiDecode` it to a reducible type at `predLevel+1`, and
transport the subject's membership across the substituted conversion. -/
theorem fundamentalConvAtAll {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier reclassifier : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (subjectFundamental : FundamentalConclusionAtAll context subject classifier)
    (reclassifierFundamental :
      FundamentalConclusionAtAll context reclassifier (universeCodeCell levelExpr flag))
    (converts : Conv classifier reclassifier) :
    FundamentalConclusionAtAll context subject reclassifier := by
  intro _targetScope substitution env predLevel
  have reclassifierMember := reclassifierFundamental substitution env (predLevel + 1)
  rw [subst_universeCodeCell] at reclassifierMember
  obtain ⟨_candidate, reclassifierReducible⟩ := reclassifierMember.tarskiDecode
  exact IsReducibleMemberAt.castAlongConvUnderSubst substitution
    (subjectFundamental substitution env predLevel) reclassifierReducible converts

end FX1Poly.Typed
