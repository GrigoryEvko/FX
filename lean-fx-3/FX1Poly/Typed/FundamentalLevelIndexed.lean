import FX1Poly.Typed.FundamentalAtAllLeafArms
import FX1Poly.Typed.ReducibleEnvVec
import FX1Poly.Typed.ReducibleSemanticRules
import FX1Poly.Typed.PiFormerMembership
import FX1Poly.Typed.FormerChildrenReducible
import FX1Poly.Typed.DescTelescopeInversion
import FX1Poly.Typed.FundamentalAtAllVectorPremises

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

/-- **The `conv` arm (level-changing: carries the `tarskiDecode` +1).**  The subject is a member of its
classifier at `subjectLevel`; the reclassifier is a universe member, so running its fundamental ONE LEVEL UP
(`subjectLevel + 1`) and `tarskiDecode`-ing drops it to a reducible TYPE at `subjectLevel`; then
`castAlongConvUnderSubst` transports the subject's membership across the substituted conversion onto the
reclassifier, at the same `subjectLevel`.  Mirrors `fundamentalConvAtAll` with the level decoupled. -/
theorem fundamentalConvLevelIndexed {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (subjectLevel : Nat)
    {context : TypingContext profile scope} {subject classifier reclassifier : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (subjectFundamental : FundamentalConclusionLevelIndexed contextLevels subjectLevel context subject
      classifier)
    (reclassifierFundamental : FundamentalConclusionLevelIndexed contextLevels (subjectLevel + 1) context
      reclassifier (universeCodeCell levelExpr flag))
    (converts : Conv classifier reclassifier) :
    FundamentalConclusionLevelIndexed contextLevels subjectLevel context subject reclassifier := by
  intro _targetScope substitution env
  have reclassifierMember := reclassifierFundamental substitution env
  rw [subst_universeCodeCell] at reclassifierMember
  obtain ⟨_candidate, reclassifierReducible⟩ := reclassifierMember.tarskiDecode
  exact IsReducibleMemberAt.castAlongConvUnderSubst substitution
    (subjectFundamental substitution env) reclassifierReducible converts

/-- **The `piIntro` (dependent λ-introduction) arm — the binder, the level-indexed FT's crux.**
`abstractionCanonicalUnderSubst` is UNIFORM-level: the domain/codomain reducible TYPES and the body reducible
MEMBER all sit at the lam's level `predLevel + 1`, and the bound argument lands at `predLevel + 1` via
`ReducibleEnvVec.cons` / `levelCons (predLevel + 1)`.  The level must be POSITIVE (`predLevel + 1`) because
the domain candidate's `isReducibilityCandidate` (CR1: domain members are strongly normalizing) only holds at
a positive level.  The domain/codomain are universe members at `predLevel + 1 + 1` (decoded down one by
`tarskiDecode`); the body is a member at `predLevel + 1`.  The `subst_cons_eq_subst0_lift` keystone reshapes
the `cons`-substitution output into the `subst0 (subst (lift …) …) argument` shape the rule demands.  This
arm closing is what breaks the dependent-binder wall in the level-indexed design. -/
theorem fundamentalPiIntroLevelIndexed {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (predLevel : Nat)
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental : FundamentalConclusionLevelIndexed contextLevels (predLevel + 1 + 1) context
      domainCode (universeCodeCell domainLevel flag))
    (codomainFundamental : FundamentalConclusionLevelIndexed (levelCons (predLevel + 1) contextLevels)
      (predLevel + 1 + 1) (context.cons domainCode) codomainCode (universeCodeCell codomainLevel flag))
    (bodyFundamental : FundamentalConclusionLevelIndexed (levelCons (predLevel + 1) contextLevels)
      (predLevel + 1) (context.cons domainCode) body codomainCode) :
    FundamentalConclusionLevelIndexed contextLevels (predLevel + 1) context (lamCell body)
      (piTyCodeCell domainCode codomainCode) := by
  intro _targetScope substitution env
  have domainMember := domainFundamental substitution env
  rw [subst_universeCodeCell] at domainMember
  obtain ⟨domainCandidate, domainReducible⟩ := domainMember.tarskiDecode
  refine IsReducibleMemberAt.abstractionCanonicalUnderSubst substitution domainReducible
    (fun _argument argumentInDomain =>
      domainReducible.isReducibilityCandidate.stronglyNormalizing argumentInDomain)
    (fun argument argumentInDomain => ?_) (fun argument argumentInDomain => ?_)
  · rw [← RawTerm.subst_cons_eq_subst0_lift _ argument substitution]
    have codomainMember := codomainFundamental (RawTermSubst.cons argument substitution)
      (ReducibleEnvVec.cons env ⟨domainCandidate, domainReducible, argumentInDomain⟩)
    rw [subst_universeCodeCell] at codomainMember
    exact codomainMember.tarskiDecode
  · rw [← RawTerm.subst_cons_eq_subst0_lift _ argument substitution,
      ← RawTerm.subst_cons_eq_subst0_lift _ argument substitution]
    exact bodyFundamental (RawTermSubst.cons argument substitution)
      (ReducibleEnvVec.cons env ⟨domainCandidate, domainReducible, argumentInDomain⟩)

/-- **The Π type-FORMER arm of the level-indexed FT** (the dependent type-former, level-indexed).
Consumes the domain fundamental QUANTIFIED over an arbitrary positive `aboveLevel` (used at
`predLevel+1` and `predLevel+2` — the latter only to mine a fresh variable inhabitant of the domain
candidate) and the codomain fundamental QUANTIFIED over the fresh binder's head level (instantiated
at `predLevel` and `predLevel+1` — the two argument levels Π-formation actually consumes), and
produces the Π code's membership in `universeCodeCell formerLevel flag` at `predLevel+1`.  The level-
indexed twin of `IsReducibleMemberAt.piFormerOfChildMembershipsAtRequiredLevels`; the quantified head
level is precisely what `ReducibleEnvVec.cons` threads (each codomain instantiation cons-extends the
env at the matching `levelCons headLevel contextLevels`).  `codomainLevel` is pinned at the rule
call because it appears only in the (yet-placeholder) codomain hypotheses, not the conclusion. -/
theorem fundamentalPiFormationLevelIndexed {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (predLevel : Nat)
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental : ∀ aboveLevel : Nat,
      FundamentalConclusionLevelIndexed contextLevels (aboveLevel + 1) context domainCode
        (universeCodeCell domainLevel flag))
    (codomainFundamental : ∀ headLevel : Nat,
      FundamentalConclusionLevelIndexed (levelCons headLevel contextLevels) (predLevel + 1)
        (context.cons domainCode) codomainCode (universeCodeCell codomainLevel flag)) :
    FundamentalConclusionLevelIndexed contextLevels (predLevel + 1) context
      (piTyCodeCell domainCode codomainCode) (universeCodeCell formerLevel flag) := by
  intro _targetScope substitution env
  rw [subst_universeCodeCell]
  have domainMember := domainFundamental predLevel substitution env
  rw [subst_universeCodeCell] at domainMember
  have domainMemberAbove := domainFundamental (predLevel + 1) substitution env
  rw [subst_universeCodeCell] at domainMemberAbove
  refine IsReducibleMemberAt.piFormerOfChildMembershipsAtRequiredLevels
    (codomainLevel := codomainLevel) domainMember
    domainMemberAbove (fun argument argumentInDomain => ?_) (fun argument argumentInDomain => ?_)
  · have codomainMember := codomainFundamental predLevel
      (RawTermSubst.cons argument substitution) (ReducibleEnvVec.cons env argumentInDomain)
    rwa [subst_universeCodeCell] at codomainMember
  · have codomainMember := codomainFundamental (predLevel + 1)
      (RawTermSubst.cons argument substitution) (ReducibleEnvVec.cons env argumentInDomain)
    rwa [subst_universeCodeCell] at codomainMember

/-- **The Σ type-FORMER arm of the level-indexed FT.**  The data-former twin: Σ formation is
classified in its universe by STRONG NORMALIZATION alone (`sigmaFormerOfChildMembershipsAtRequiredLevel`,
the `dataFormerInUniverse` route), so it needs only the domain fundamental (at `predLevel+1` /
`predLevel+2`) and the codomain fundamental at the single head level `predLevel+1` — no codomain at
the lower argument level, no `codomainExists`.  Otherwise identical to the Π former arm. -/
theorem fundamentalSigmaFormationLevelIndexed {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (predLevel : Nat)
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (domainFundamental : ∀ aboveLevel : Nat,
      FundamentalConclusionLevelIndexed contextLevels (aboveLevel + 1) context domainCode
        (universeCodeCell domainLevel flag))
    (codomainFundamental :
      FundamentalConclusionLevelIndexed (levelCons (predLevel + 1) contextLevels) (predLevel + 1)
        (context.cons domainCode) codomainCode (universeCodeCell codomainLevel flag)) :
    FundamentalConclusionLevelIndexed contextLevels (predLevel + 1) context
      (sigmaTyCodeCell domainCode codomainCode) (universeCodeCell formerLevel flag) := by
  intro _targetScope substitution env
  rw [subst_universeCodeCell]
  have domainMember := domainFundamental predLevel substitution env
  rw [subst_universeCodeCell] at domainMember
  have domainMemberAbove := domainFundamental (predLevel + 1) substitution env
  rw [subst_universeCodeCell] at domainMemberAbove
  refine IsReducibleMemberAt.sigmaFormerOfChildMembershipsAtRequiredLevel
    (codomainLevel := codomainLevel) domainMember
    domainMemberAbove (fun argument argumentInDomain => ?_)
  have codomainMember := codomainFundamental
    (RawTermSubst.cons argument substitution) (ReducibleEnvVec.cons env argumentInDomain)
  rwa [subst_universeCodeCell] at codomainMember

/-- **The generic `genFormation`/`genFormationPi` former arm of the level-indexed FT.**  Over any former
with a `typingRuleDescOf` row (currently Π / Σ), given the premise telescope and its telescope-reducibility
IH in level-indexed shape (`∀ substitution, env-at-contextLevels, shapeEq → TelescopeReducible …`), the
former cell `mkGen generator payload children` is a reducible member of its output universe
`rule.outputType scope levels flag` at `predLevel+1`.  Dispatches on the generator (`by_cases` to
`gen_piTyCode`/`gen_sigmaTyCode`, the only `typingRuleDescOf` rows), inverts the two-child spine via
`DescTelescopePi.twoChildLevels`, and reads the `FormerChildrenReducible` bundle off the telescope relation
through the shipped `ofTelescopeReducible` + `toPiMember`/`toSigmaMember`.  This is the level-indexed twin
of the committed `HasTypeDescPi.fundamentalVectorFromFormation` genFormationPi arm — the SAME dispatch with
the decoupled-`subjectLevel` (`FundamentalConclusionLevelIndexed`) wrapper in place of the vector wrapper
(`IsFundamentalConclusionAtVector`); `TelescopeReducible`'s `headMember` is already all-level-quantified, so
no per-child level coordination is needed here.  This is the FORMER half of the `HasTypeDescPi.rec` /
`HasTypeDesc.rec` assembly; the remaining assembly work is the motive that threads `subjectLevel`/
`contextLevels` and the telescope motive_2 that produces this arm's `telescopeFundamental` IH from the per-
child `FundamentalConclusionLevelIndexed` IHs. -/
theorem fundamentalGenFormationFormerLevelIndexed {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (predLevel : Nat)
    {context : TypingContext profile scope}
    {generator : Generator} (payload : generator.payload scope)
    {children : RawTermChildren generator.binderShifts scope}
    {levels : List LevelExpr} {flag : UniverseFlag} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule)
    (premises : DescTelescopePi profile (currentDepth := 0) context levels flag children)
    (telescopeFundamental :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvVec contextLevels context substitution)
        (shapeEq : generator.binderShifts = consecutiveShifts 0 levels.length),
        TelescopeReducible flag 0 levels.length substitution levels (shapeEq ▸ children)) :
    FundamentalConclusionLevelIndexed contextLevels (predLevel + 1) context
      (.mkGen generator payload children) (rule.outputType scope levels flag) := by
  intro _targetScope substitution env
  by_cases isPiFormer : generator = .gen_piTyCode
  · subst isPiFormer
    obtain rfl : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
    match children with
    | .childCons _domainCode (.childCons _codomainCode .childNil) =>
        obtain ⟨_domainLevel, _codomainLevel, levelsShape⟩ := DescTelescopePi.twoChildLevels premises
        subst levelsShape
        dsimp only [universeFormerOutput]
        rw [subst_universeCodeCell]
        exact (FormerChildrenReducible.ofTelescopeReducible predLevel
          (telescopeFundamental substitution env Generator.gen_piTyCode_binderShifts_eq)).toPiMember
  · by_cases isSigmaFormer : generator = .gen_sigmaTyCode
    · subst isSigmaFormer
      obtain rfl : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
      match children with
      | .childCons _domainCode (.childCons _codomainCode .childNil) =>
          obtain ⟨_domainLevel, _codomainLevel, levelsShape⟩ := DescTelescopePi.twoChildLevels premises
          subst levelsShape
          dsimp only [universeFormerOutput]
          rw [subst_universeCodeCell]
          exact (FormerChildrenReducible.ofTelescopeReducible predLevel
            (telescopeFundamental substitution env Generator.gen_sigmaTyCode_binderShifts_eq)).toSigmaMember
    · exfalso
      unfold typingRuleDescOf at isFormation
      rw [if_neg isPiFormer, if_neg isSigmaFormer] at isFormation
      contradiction

/-- **The vector fundamental conclusion IS the level-indexed conclusion, universally quantified over the
env's level vector and a positive conclusion level.**  `IsFundamentalConclusionAtVector` fixes the conclusion
at `predLevel+1` while quantifying over an ARBITRARY env level vector — so, by unfolding, it is exactly the
family of `FundamentalConclusionLevelIndexed` instances at every `(envLevels, predLevel+1)`.  The precise
connector between the committed vector machinery (`HasTypeDescPi.fundamentalVectorFromFormation`, which
discharges the grown arms at the vector motive) and the decoupled-`subjectLevel` arms above.  It also makes
explicit WHY `var` is unprovable at the vector conclusion: that would force membership at `predLevel+1` for
EVERY `predLevel`, whereas a variable is reducible only at its env-fixed level `contextLevels index`. -/
theorem isFundamentalConclusionAtVector_iff_forall_levelIndexed {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope} :
    IsFundamentalConclusionAtVector context subject classifier ↔
      ∀ (envLevels : Fin scope → Nat) (predLevel : Nat),
        FundamentalConclusionLevelIndexed envLevels (predLevel + 1) context subject classifier := by
  constructor
  · intro vectorConclusion envLevels predLevel _targetScope substitution env
    exact vectorConclusion substitution predLevel env
  · intro perVectorConclusion _targetScope substitution envLevels predLevel env
    exact perVectorConclusion envLevels predLevel substitution env

/-- **Forward projection** (the usable half): a vector fundamental conclusion yields the level-indexed
conclusion at any chosen env level vector and positive conclusion level — so a grown arm proved at the
committed vector motive can be read as a level-indexed conclusion wherever the decoupled-`subjectLevel`
machinery expects one. -/
theorem IsFundamentalConclusionAtVector.toLevelIndexed {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (vectorConclusion : IsFundamentalConclusionAtVector context subject classifier)
    (envLevels : Fin scope → Nat) (predLevel : Nat) :
    FundamentalConclusionLevelIndexed envLevels (predLevel + 1) context subject classifier :=
  fun substitution env => vectorConclusion substitution predLevel env

end FX1Poly.Typed
