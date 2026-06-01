import FX1Poly.Typed.ReducibleEnvAtAllLevels
import FX1Poly.Typed.ReducibleSemanticRules
import FX1Poly.Typed.FormerChildrenReducible
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

The remaining recursive `genFormation` and `piIntro` companions cross binders: their recursor premises must
use the per-variable-level environment bridge for the freshly bound argument, while the outer theorem remains
stated over the ∀-level environment.  These leaf arms confirm the ∀-level environment closes the
non-binder/conv fragment with zero axioms.

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

/-- **The `piElim` (application) arm over the ∀-level environment.**  Given the function's induction
hypothesis (a reducible member of the Π-type) and the argument's induction hypothesis (a reducible member of
the domain), the application is a reducible member of the instantiated codomain.  Non-binder, like `conv`:
run both induction hypotheses at the conclusion level and apply `applicationUnderSubst` (which distributes the
substitution over the Π and application cells and β-commutes the dependent codomain classifier). -/
theorem fundamentalPiElimAtAll {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {functionTerm argument domainCode : RawTerm scope}
    {codomainCode : RawTerm (scope + 1)}
    (functionFundamental : FundamentalConclusionAtAll context functionTerm
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))))
    (argumentFundamental : FundamentalConclusionAtAll context argument domainCode) :
    FundamentalConclusionAtAll context
      (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil)))
      (RawTerm.subst0 codomainCode argument) := by
  intro _targetScope substitution env predLevel
  exact IsReducibleMemberAt.applicationUnderSubst substitution
    (functionFundamental substitution env predLevel) (argumentFundamental substitution env predLevel)

/-- **The `piIntro` (lambda) arm over the ∀-level conclusion, factored at the real binder boundary.**  The
domain premise is still an ordinary `FundamentalConclusionAtAll`: run it one level up and `tarskiDecode` to
obtain the reducible domain type at the conclusion level.  The two binder-recursive premises are stated in
the EXACT semantic shape `abstractionCanonicalUnderSubst` needs: for every domain-reducible argument, the
instantiated codomain is a reducible type and the instantiated body is a reducible member of it.

This theorem deliberately does not manufacture those two premises from `FundamentalConclusionAtAll` for the
extended context.  That is the remaining mutual-recursion/environment problem.  What it does ship is the
complete, zero-axiom `piIntro` dispatch once that recursive companion has produced the codomain/body semantic
obligations. -/
theorem fundamentalPiIntroAtAll {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    {domainLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental :
      FundamentalConclusionAtAll context domainCode (universeCodeCell domainLevel flag))
    (codomainReducibleUnderArgument :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat)
        {domainCandidate : RawTerm (targetScope + 1) → Prop},
        ReducibleTypeAt (predLevel + 1) (RawTerm.subst substitution domainCode) domainCandidate →
        ∀ argument : RawTerm (targetScope + 1), domainCandidate argument →
          IsReducibleTypeAt (predLevel + 1)
            (RawTerm.subst0
              (RawTerm.subst (RawTermSubst.lift substitution) codomainCode) argument))
    (bodyReducibleUnderArgument :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat)
        {domainCandidate : RawTerm (targetScope + 1) → Prop},
        ReducibleTypeAt (predLevel + 1) (RawTerm.subst substitution domainCode) domainCandidate →
        ∀ argument : RawTerm (targetScope + 1), domainCandidate argument →
          IsReducibleMemberAt (predLevel + 1)
            (RawTerm.subst0
              (RawTerm.subst (RawTermSubst.lift substitution) codomainCode) argument)
            (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) body) argument)) :
    FundamentalConclusionAtAll context (lamCell body) (piTyCodeCell domainCode codomainCode) := by
  intro _targetScope substitution env predLevel
  have domainMember := domainFundamental substitution env (predLevel + 1)
  rw [subst_universeCodeCell] at domainMember
  obtain ⟨domainCandidate, domainReducible⟩ := domainMember.tarskiDecode
  refine IsReducibleMemberAt.abstractionCanonicalUnderSubst substitution domainReducible
    (fun _argument argumentInDomain =>
      domainReducible.isReducibilityCandidate.stronglyNormalizing argumentInDomain)
    ?codomainExists ?bodyReducible
  · intro argument argumentInDomain
    exact codomainReducibleUnderArgument substitution env predLevel domainReducible
      argument argumentInDomain
  · intro argument argumentInDomain
    exact bodyReducibleUnderArgument substitution env predLevel domainReducible
      argument argumentInDomain

/-- **The Π-formation arm over the ∀-level conclusion, factored through the two-child former bundle.**  Once
the premise-telescope companion has produced `FormerChildrenReducible` for the substituted domain/codomain
children, the Π former's universe membership is exactly `FormerChildrenReducible.toPiMember`, after the
classifier substitution on the universe code reduces by `subst_universeCodeCell`. -/
theorem fundamentalPiFormationAtAll {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (childrenReducible :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat),
        FormerChildrenReducible predLevel flag substitution domainCode codomainCode
          domainLevel codomainLevel) :
    FundamentalConclusionAtAll context (piTyCodeCell domainCode codomainCode)
      (universeCodeCell formerLevel flag) := by
  intro _targetScope substitution env predLevel
  rw [subst_universeCodeCell]
  exact (childrenReducible substitution env predLevel).toPiMember

/-- **The Π-formation arm over the ∀-level conclusion, using the level-exact two-child bundle.**  This is
the dispatch-level sibling of `fundamentalPiFormationAtAll`: the premise companion need only provide the two
codomain-under-argument levels consumed by `FormerChildrenReducibleAtDispatchLevels.toPiMember`, not the
older all-`memberLevel` codomain premise. -/
theorem fundamentalPiFormationAtDispatchLevelsAtAll {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (childrenReducible :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat),
        FormerChildrenReducibleAtDispatchLevels predLevel flag substitution domainCode codomainCode
          domainLevel codomainLevel) :
    FundamentalConclusionAtAll context (piTyCodeCell domainCode codomainCode)
      (universeCodeCell formerLevel flag) := by
  intro _targetScope substitution env predLevel
  rw [subst_universeCodeCell]
  exact (childrenReducible substitution env predLevel).toPiMember

/-- **The Σ-formation arm over the ∀-level conclusion, factored through the two-child former bundle.**  The
Σ/data-former twin of `fundamentalPiFormationAtAll`: the premise telescope supplies the same child bundle,
and `FormerChildrenReducible.toSigmaMember` performs the semantic dispatch. -/
theorem fundamentalSigmaFormationAtAll {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (childrenReducible :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat),
        FormerChildrenReducible predLevel flag substitution domainCode codomainCode
          domainLevel codomainLevel) :
    FundamentalConclusionAtAll context
      (.mkGen .gen_sigmaTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
      (universeCodeCell formerLevel flag) := by
  intro _targetScope substitution env predLevel
  rw [subst_universeCodeCell]
  exact (childrenReducible substitution env predLevel).toSigmaMember

/-- **The Σ-formation arm over the ∀-level conclusion, using the level-exact two-child bundle.**  The data
former counterpart of `fundamentalPiFormationAtDispatchLevelsAtAll`. -/
theorem fundamentalSigmaFormationAtDispatchLevelsAtAll {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (childrenReducible :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat),
        FormerChildrenReducibleAtDispatchLevels predLevel flag substitution domainCode codomainCode
          domainLevel codomainLevel) :
    FundamentalConclusionAtAll context
      (.mkGen .gen_sigmaTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
      (universeCodeCell formerLevel flag) := by
  intro _targetScope substitution env predLevel
  rw [subst_universeCodeCell]
  exact (childrenReducible substitution env predLevel).toSigmaMember

end FX1Poly.Typed
