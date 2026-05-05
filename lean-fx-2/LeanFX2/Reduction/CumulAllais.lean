import LeanFX2.Reduction.CumulCastElim

/-! # Reduction/CumulAllais — Pattern 3 per-Term-ctor subst arms (Allais ICFP'18)

Per-Term-ctor `Term.substHet` arms for the Allais et al. ICFP'18 paired-
environment simulation framework.  Each arm discharges one ctor's
obligation in the Allais `Simulation.alg` discipline: given pointwise
compat between two `TermSubstHet`s at the same `SubstHet sigma`, lift to
ConvCumul on the substituted source Term ctor.

## Reference

Allais, Atkey, Chapman, McBride, McKinna, *A Type and Scope Safe Universe
of Syntaxes with Binding*, ICFP 2018 / JFP 2021 (arxiv:1804.00119).  See
`Generic/Simulation.agda` in `gallais/generic-syntax`; FX memory
`reference_pattern_allais_simulation`.

## What this file ships

* `TermSubstHet.PointwiseCompat` predicate + refl / sym / trans
  combinators.  Direct FX instance of Allais's `All 𝓥ᴿ Γ ρᴬ ρᴮ` for
  `𝓥ᴿ = ConvCumul`.

* 27 per-Term-ctor `subst_compatible_<ctor>_allais` arms — closed-payload
  (refl), var (compat-lookup), single-subterm cong, multi-subterm cong,
  binder cong (lam / lamPi), eliminator cong (natElim / natRec /
  listElim / optionMatch / eitherMatch), and cumul-promotion.  Each arm
  has a real body using its inputs substantively.

The recursive HEADLINE that glues these arms via Term-induction lives in
`Reduction/CumulPairedEnv.lean` (the fundamental lemma
`Term.subst_compatible_pointwise_allais`).  This file is the catalogue.

## Shared cast-elim primitives

The `pair` / `snd` / `appPi` / `lam` / `lamPi` arms use
`ConvCumul.cast_eq_both_benton` to peel `Ty.X_substHet_commute` casts.
Source: `Reduction/CumulCastElim.lean`.

## Audit

All shipped arms verified zero-axiom under strict policy in
`Smoke/AuditCumulSubstCompat.lean`.
-/

namespace LeanFX2

/-! # Allais et al. ICFP'18 — paired-environment compat

This section instantiates the Allais simulation framework's
paired-env predicate for FX's `TermSubstHet`.  The headline
theorem `ConvCumul.subst_compatible_allais` lifts pointwise
ConvCumul compat between two `TermSubstHet`s at the same
`SubstHet sigma` to ConvCumul on the substituted source Term.

Reference: arxiv:1804.00119 §5 (Simulation framework), record
`Simulation`.  FX memory `reference_pattern_allais_simulation`.
-/

/-- **Allais paired-env predicate.**  Two `TermSubstHet`s at the
same `SubstHet` are POINTWISE COMPAT when their per-position
substituents are `ConvCumul`-related.  Direct FX instance of
Allais's `All 𝓥ᴿ Γ ρᴬ ρᴮ` for `𝓥ᴿ = ConvCumul`. -/
def TermSubstHet.PointwiseCompat
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma) :
    Prop :=
  ∀ position, ConvCumul (termSubstA position) (termSubstB position)

/-- Reflexivity of pointwise compat: any TermSubstHet is compat with itself. -/
theorem TermSubstHet.PointwiseCompat.refl
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubst : TermSubstHet sourceCtx targetCtx sigma) :
    TermSubstHet.PointwiseCompat termSubst termSubst :=
  fun position => ConvCumul.refl (termSubst position)

/-- Symmetry of pointwise compat. -/
theorem TermSubstHet.PointwiseCompat.sym
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (compat : TermSubstHet.PointwiseCompat termSubstA termSubstB) :
    TermSubstHet.PointwiseCompat termSubstB termSubstA :=
  fun position => ConvCumul.sym (compat position)

/-- Transitivity of pointwise compat. -/
theorem TermSubstHet.PointwiseCompat.trans
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB termSubstC : TermSubstHet sourceCtx targetCtx sigma}
    (compatAB : TermSubstHet.PointwiseCompat termSubstA termSubstB)
    (compatBC : TermSubstHet.PointwiseCompat termSubstB termSubstC) :
    TermSubstHet.PointwiseCompat termSubstA termSubstC :=
  fun position => ConvCumul.trans (compatAB position) (compatBC position)

/-! ## Allais per-Term-ctor arms

Allais's `Simulation.alg` field discharges per-ctor obligations.
For FX's typed Term, each ctor gets one `subst_compatible_<ctor>_allais`
helper that:
* Recurses on substituent subterms (uses outer hypothesis from
  structural recursion of `subst_compatible_allais` headline).
* Applies the matching `ConvCumul` cong rule (homogeneous in
  outer Term shape; heterogeneous in inner cumul-relevant fields).

Term ctors fall into four families:
1. **Closed-payload** (no scope-dependent subterms): both substituted
   sides coincide → `ConvCumul.refl`.  Coverage: unit, boolTrue,
   boolFalse, natZero, listNil, optionNone, universeCode, refl.
2. **Var**: pointwise compat lookup → returns `compat position`.
3. **Single-subterm cong**: recurse into the inner ConvCumul
   substituted witness, apply matching cong rule.  Coverage:
   natSucc, optionSome, eitherInl, eitherInr, modIntro, modElim,
   subsume, fst, snd.
4. **Multi-subterm cong**: recurse into each inner ConvCumul
   witness, apply multi-arg cong rule.  Coverage: app, appPi,
   pair, listCons, idJ, boolElim, natElim, natRec, listElim,
   optionMatch, eitherMatch.
5. **Binder cong** (lift required): recurse on body under
   `TermSubstHet.lift` with `PointwiseCompat.lift` extension.
   Coverage: lam, lamPi.  Pending PointwiseCompat.lift via
   Benton's rename theorem.
6. **Cumul-promotion** (cumulUp): `Term.substHet` preserves
   `lowerTerm` verbatim; both substituted sides coincide →
   `ConvCumul.refl`.

Reference: Allais et al. arxiv:1804.00119 §5.1 (per-syntax
description discharge). -/

/-- Allais arm for `unit`: closed-payload, refl. -/
theorem ConvCumul.subst_compatible_unit_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma) :
    ConvCumul ((Term.unit (context := sourceCtx)).substHet termSubstA)
              ((Term.unit (context := sourceCtx)).substHet termSubstB) :=
  ConvCumul.refl _

/-- Allais arm for `boolTrue`: closed-payload, refl. -/
theorem ConvCumul.subst_compatible_boolTrue_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma) :
    ConvCumul ((Term.boolTrue (context := sourceCtx)).substHet termSubstA)
              ((Term.boolTrue (context := sourceCtx)).substHet termSubstB) :=
  ConvCumul.refl _

/-- Allais arm for `boolFalse`: closed-payload, refl. -/
theorem ConvCumul.subst_compatible_boolFalse_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma) :
    ConvCumul ((Term.boolFalse (context := sourceCtx)).substHet termSubstA)
              ((Term.boolFalse (context := sourceCtx)).substHet termSubstB) :=
  ConvCumul.refl _

/-- Allais arm for `natZero`: closed-payload, refl. -/
theorem ConvCumul.subst_compatible_natZero_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma) :
    ConvCumul ((Term.natZero (context := sourceCtx)).substHet termSubstA)
              ((Term.natZero (context := sourceCtx)).substHet termSubstB) :=
  ConvCumul.refl _

/-- Allais arm for `var`: pointwise compat lookup. -/
theorem ConvCumul.subst_compatible_var_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (compat : TermSubstHet.PointwiseCompat termSubstA termSubstB)
    (position : Fin sourceScope) :
    ConvCumul ((Term.var (context := sourceCtx) position).substHet termSubstA)
              ((Term.var (context := sourceCtx) position).substHet termSubstB) :=
  compat position

/-- Allais arm for `universeCode`: closed-payload (level metadata
only, no scope-dep payload), refl. -/
theorem ConvCumul.subst_compatible_universeCode_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ sourceLevel) :
    ConvCumul ((Term.universeCode (context := sourceCtx)
                                  innerLevel outerLevel cumulOk levelLe).substHet termSubstA)
              ((Term.universeCode (context := sourceCtx)
                                  innerLevel outerLevel cumulOk levelLe).substHet termSubstB) :=
  ConvCumul.refl _

/-- Allais arm for `equivReflId`: the substHet arm depends only on
sigma (not on the per-position TermSubstHet data), so both sides
reduce to the same Term and `ConvCumul.refl` discharges. -/
theorem ConvCumul.subst_compatible_equivReflId_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (carrier : Ty sourceLevel sourceScope) :
    ConvCumul ((Term.equivReflId (context := sourceCtx) carrier).substHet termSubstA)
              ((Term.equivReflId (context := sourceCtx) carrier).substHet termSubstB) :=
  ConvCumul.refl _

/-- Allais arm for `funextRefl`: same shape as `equivReflId` arm —
the substHet arm depends only on sigma, so both sides agree. -/
theorem ConvCumul.subst_compatible_funextRefl_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (domainType codomainType : Ty sourceLevel sourceScope)
    (applyRaw : RawTerm (sourceScope + 1)) :
    ConvCumul ((Term.funextRefl (context := sourceCtx)
                                domainType codomainType applyRaw).substHet termSubstA)
              ((Term.funextRefl (context := sourceCtx)
                                domainType codomainType applyRaw).substHet termSubstB) :=
  ConvCumul.refl _

/-- Allais arm for `equivReflIdAtId`: the substHet arm depends only
on sigma (not on the per-position TermSubstHet data), so both sides
reduce to the same Term and `ConvCumul.refl` discharges. -/
theorem ConvCumul.subst_compatible_equivReflIdAtId_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ sourceLevel)
    (carrier : Ty sourceLevel sourceScope)
    (carrierRaw : RawTerm sourceScope) :
    ConvCumul ((Term.equivReflIdAtId (context := sourceCtx)
                                     innerLevel innerLevelLt
                                     carrier carrierRaw).substHet termSubstA)
              ((Term.equivReflIdAtId (context := sourceCtx)
                                     innerLevel innerLevelLt
                                     carrier carrierRaw).substHet termSubstB) :=
  ConvCumul.refl _

/-- Allais arm for `funextReflAtId`: the substHet arm depends only on
sigma; both sides agree, `ConvCumul.refl` discharges. -/
theorem ConvCumul.subst_compatible_funextReflAtId_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (domainType codomainType : Ty sourceLevel sourceScope)
    (applyRaw : RawTerm (sourceScope + 1)) :
    ConvCumul ((Term.funextReflAtId (context := sourceCtx)
                                    domainType codomainType applyRaw).substHet termSubstA)
              ((Term.funextReflAtId (context := sourceCtx)
                                    domainType codomainType applyRaw).substHet termSubstB) :=
  ConvCumul.refl _

/-- Allais arm for `funextIntroHet`: like `funextReflAtId`, this is a
VALUE ctor with NO typed subterms (just schematic raws
`domainType, codomainType, applyARaw, applyBRaw`).  Both
`termSubstA` and `termSubstB` share the underlying `sigma`, so the
substHet arm in `Term/SubstHet.lean` consults only `sigma`/
`sigma.forRaw.lift` — both sides agree definitionally.
`ConvCumul.refl` discharges.  Phase 12.A.B8.8. -/
theorem ConvCumul.subst_compatible_funextIntroHet_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (domainType codomainType : Ty sourceLevel sourceScope)
    (applyARaw applyBRaw : RawTerm (sourceScope + 1)) :
    ConvCumul ((Term.funextIntroHet (context := sourceCtx)
                                    domainType codomainType
                                    applyARaw applyBRaw).substHet termSubstA)
              ((Term.funextIntroHet (context := sourceCtx)
                                    domainType codomainType
                                    applyARaw applyBRaw).substHet termSubstB) :=
  ConvCumul.refl _

/-! ## CUMUL-2.4 typed type-code constructors — Allais helpers.

All ten new ctors are VALUE-shaped (schematic raw payloads, no
recursive typed subterms).  Their `substHet` arms in
`Term/SubstHet.lean` depend ONLY on `sigma`/`sigma.forRaw`/
`sigma.forRaw.lift` — never on the TermSubst values themselves.
Both `termSubstA` and `termSubstB` share the same `sigma`, so both
sides reduce to the SAME substituted ctor application; `ConvCumul.refl`
discharges.  Mirror of `subst_compatible_funextIntroHet_allais`. -/

theorem ConvCumul.subst_compatible_arrowCode_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ sourceLevel)
    (domainCodeRaw codomainCodeRaw : RawTerm sourceScope) :
    ConvCumul ((Term.arrowCode (context := sourceCtx)
                               outerLevel levelLe
                               domainCodeRaw codomainCodeRaw).substHet termSubstA)
              ((Term.arrowCode (context := sourceCtx)
                               outerLevel levelLe
                               domainCodeRaw codomainCodeRaw).substHet termSubstB) :=
  ConvCumul.refl _

theorem ConvCumul.subst_compatible_piTyCode_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ sourceLevel)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1)) :
    ConvCumul ((Term.piTyCode (context := sourceCtx)
                              outerLevel levelLe
                              domainCodeRaw codomainCodeRaw).substHet termSubstA)
              ((Term.piTyCode (context := sourceCtx)
                              outerLevel levelLe
                              domainCodeRaw codomainCodeRaw).substHet termSubstB) :=
  ConvCumul.refl _

theorem ConvCumul.subst_compatible_sigmaTyCode_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ sourceLevel)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1)) :
    ConvCumul ((Term.sigmaTyCode (context := sourceCtx)
                                 outerLevel levelLe
                                 domainCodeRaw codomainCodeRaw).substHet termSubstA)
              ((Term.sigmaTyCode (context := sourceCtx)
                                 outerLevel levelLe
                                 domainCodeRaw codomainCodeRaw).substHet termSubstB) :=
  ConvCumul.refl _

theorem ConvCumul.subst_compatible_productCode_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ sourceLevel)
    (firstCodeRaw secondCodeRaw : RawTerm sourceScope) :
    ConvCumul ((Term.productCode (context := sourceCtx)
                                 outerLevel levelLe
                                 firstCodeRaw secondCodeRaw).substHet termSubstA)
              ((Term.productCode (context := sourceCtx)
                                 outerLevel levelLe
                                 firstCodeRaw secondCodeRaw).substHet termSubstB) :=
  ConvCumul.refl _

theorem ConvCumul.subst_compatible_sumCode_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ sourceLevel)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope) :
    ConvCumul ((Term.sumCode (context := sourceCtx)
                             outerLevel levelLe
                             leftCodeRaw rightCodeRaw).substHet termSubstA)
              ((Term.sumCode (context := sourceCtx)
                             outerLevel levelLe
                             leftCodeRaw rightCodeRaw).substHet termSubstB) :=
  ConvCumul.refl _

theorem ConvCumul.subst_compatible_listCode_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ sourceLevel)
    (elementCodeRaw : RawTerm sourceScope) :
    ConvCumul ((Term.listCode (context := sourceCtx)
                              outerLevel levelLe
                              elementCodeRaw).substHet termSubstA)
              ((Term.listCode (context := sourceCtx)
                              outerLevel levelLe
                              elementCodeRaw).substHet termSubstB) :=
  ConvCumul.refl _

theorem ConvCumul.subst_compatible_optionCode_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ sourceLevel)
    (elementCodeRaw : RawTerm sourceScope) :
    ConvCumul ((Term.optionCode (context := sourceCtx)
                                outerLevel levelLe
                                elementCodeRaw).substHet termSubstA)
              ((Term.optionCode (context := sourceCtx)
                                outerLevel levelLe
                                elementCodeRaw).substHet termSubstB) :=
  ConvCumul.refl _

theorem ConvCumul.subst_compatible_eitherCode_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ sourceLevel)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope) :
    ConvCumul ((Term.eitherCode (context := sourceCtx)
                                outerLevel levelLe
                                leftCodeRaw rightCodeRaw).substHet termSubstA)
              ((Term.eitherCode (context := sourceCtx)
                                outerLevel levelLe
                                leftCodeRaw rightCodeRaw).substHet termSubstB) :=
  ConvCumul.refl _

theorem ConvCumul.subst_compatible_idCode_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ sourceLevel)
    (typeCodeRaw leftRaw rightRaw : RawTerm sourceScope) :
    ConvCumul ((Term.idCode (context := sourceCtx)
                            outerLevel levelLe
                            typeCodeRaw leftRaw rightRaw).substHet termSubstA)
              ((Term.idCode (context := sourceCtx)
                            outerLevel levelLe
                            typeCodeRaw leftRaw rightRaw).substHet termSubstB) :=
  ConvCumul.refl _

theorem ConvCumul.subst_compatible_equivCode_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ sourceLevel)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm sourceScope) :
    ConvCumul ((Term.equivCode (context := sourceCtx)
                               outerLevel levelLe
                               leftTypeCodeRaw rightTypeCodeRaw).substHet termSubstA)
              ((Term.equivCode (context := sourceCtx)
                               outerLevel levelLe
                               leftTypeCodeRaw rightTypeCodeRaw).substHet termSubstB) :=
  ConvCumul.refl _

/-- Allais arm for `equivIntroHet`: two-subterm cong via
`equivIntroHetCong`.  Mirrors the structure of
`subst_compatible_pair_allais` / `subst_compatible_listCons_allais`:
both subterms recurse via the `compat` IH, and the ctor-level cong
rule reassembles the pair. -/
theorem ConvCumul.subst_compatible_equivIntroHet_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {carrierA carrierB : Ty sourceLevel sourceScope}
    {forwardRaw backwardRaw : RawTerm sourceScope}
    (forward : Term sourceCtx (Ty.arrow carrierA carrierB) forwardRaw)
    (backward : Term sourceCtx (Ty.arrow carrierB carrierA) backwardRaw)
    (forwardCompat :
      ConvCumul (forward.substHet termSubstA)
                (forward.substHet termSubstB))
    (backwardCompat :
      ConvCumul (backward.substHet termSubstA)
                (backward.substHet termSubstB)) :
    ConvCumul ((Term.equivIntroHet forward backward).substHet termSubstA)
              ((Term.equivIntroHet forward backward).substHet termSubstB) :=
  ConvCumul.equivIntroHetCong forwardCompat backwardCompat

/-- Allais arm for `uaIntroHet`: single-subterm cong via
`uaIntroHetCong`.  Mirrors the structure of
`subst_compatible_optionSome_allais` / `subst_compatible_natSucc_allais`:
the equivWitness subterm recurses via the `compat` IH, and the
ctor-level cong rule reassembles.  The carrierARaw/carrierBRaw
substitute structurally via `sigma.forRaw` (identical on both A and B
sides since both share `sigma`); only the equivWitness differs.
Phase 12.A.B8.5b. -/
theorem ConvCumul.subst_compatible_uaIntroHet_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ sourceLevel)
    {carrierA carrierB : Ty sourceLevel sourceScope}
    (carrierARaw carrierBRaw : RawTerm sourceScope)
    {forwardRaw backwardRaw : RawTerm sourceScope}
    (equivWitness : Term sourceCtx (Ty.equiv carrierA carrierB)
                                   (RawTerm.equivIntro forwardRaw backwardRaw))
    (equivWitnessCompat :
      ConvCumul (equivWitness.substHet termSubstA)
                (equivWitness.substHet termSubstB)) :
    ConvCumul ((Term.uaIntroHet (context := sourceCtx)
                                innerLevel innerLevelLt
                                carrierARaw carrierBRaw
                                equivWitness).substHet termSubstA)
              ((Term.uaIntroHet (context := sourceCtx)
                                innerLevel innerLevelLt
                                carrierARaw carrierBRaw
                                equivWitness).substHet termSubstB) :=
  ConvCumul.uaIntroHetCong (context := targetCtx) innerLevel
    (Nat.le_trans innerLevelLt sigma.cumulOk)
    (carrierARaw.subst sigma.forRaw) (carrierBRaw.subst sigma.forRaw)
    equivWitnessCompat

/-- Allais arm for `natSucc`: single-subterm cong via `natSuccCong`. -/
theorem ConvCumul.subst_compatible_natSucc_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {predecessorRaw : RawTerm sourceScope}
    (predecessor : Term sourceCtx Ty.nat predecessorRaw)
    (predecessorCompat :
      ConvCumul (predecessor.substHet termSubstA)
                (predecessor.substHet termSubstB)) :
    ConvCumul ((Term.natSucc predecessor).substHet termSubstA)
              ((Term.natSucc predecessor).substHet termSubstB) :=
  ConvCumul.natSuccCong predecessorCompat

/-- Allais arm for `optionSome`: single-subterm cong via `optionSomeCong`. -/
theorem ConvCumul.subst_compatible_optionSome_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {elementType : Ty sourceLevel sourceScope}
    {valueRaw : RawTerm sourceScope}
    (valueTerm : Term sourceCtx elementType valueRaw)
    (valueCompat :
      ConvCumul (valueTerm.substHet termSubstA)
                (valueTerm.substHet termSubstB)) :
    ConvCumul ((Term.optionSome valueTerm).substHet termSubstA)
              ((Term.optionSome valueTerm).substHet termSubstB) :=
  ConvCumul.optionSomeCong valueCompat

/-- Allais arm for `eitherInl`: single-subterm cong via `eitherInlCong`. -/
theorem ConvCumul.subst_compatible_eitherInl_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {leftType rightType : Ty sourceLevel sourceScope}
    {valueRaw : RawTerm sourceScope}
    (valueTerm : Term sourceCtx leftType valueRaw)
    (valueCompat :
      ConvCumul (valueTerm.substHet termSubstA)
                (valueTerm.substHet termSubstB)) :
    ConvCumul ((Term.eitherInl (rightType := rightType) valueTerm).substHet termSubstA)
              ((Term.eitherInl (rightType := rightType) valueTerm).substHet termSubstB) :=
  ConvCumul.eitherInlCong valueCompat

/-- Allais arm for `eitherInr`: single-subterm cong via `eitherInrCong`. -/
theorem ConvCumul.subst_compatible_eitherInr_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {leftType rightType : Ty sourceLevel sourceScope}
    {valueRaw : RawTerm sourceScope}
    (valueTerm : Term sourceCtx rightType valueRaw)
    (valueCompat :
      ConvCumul (valueTerm.substHet termSubstA)
                (valueTerm.substHet termSubstB)) :
    ConvCumul ((Term.eitherInr (leftType := leftType) valueTerm).substHet termSubstA)
              ((Term.eitherInr (leftType := leftType) valueTerm).substHet termSubstB) :=
  ConvCumul.eitherInrCong valueCompat

/-- Allais arm for `modIntro`: single-subterm cong via `modIntroCong`. -/
theorem ConvCumul.subst_compatible_modIntro_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {innerType : Ty sourceLevel sourceScope}
    {innerRaw : RawTerm sourceScope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerCompat :
      ConvCumul (innerTerm.substHet termSubstA)
                (innerTerm.substHet termSubstB)) :
    ConvCumul ((Term.modIntro innerTerm).substHet termSubstA)
              ((Term.modIntro innerTerm).substHet termSubstB) :=
  ConvCumul.modIntroCong innerCompat

/-- Allais arm for `modElim`: single-subterm cong via `modElimCong`. -/
theorem ConvCumul.subst_compatible_modElim_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {innerType : Ty sourceLevel sourceScope}
    {innerRaw : RawTerm sourceScope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerCompat :
      ConvCumul (innerTerm.substHet termSubstA)
                (innerTerm.substHet termSubstB)) :
    ConvCumul ((Term.modElim innerTerm).substHet termSubstA)
              ((Term.modElim innerTerm).substHet termSubstB) :=
  ConvCumul.modElimCong innerCompat

/-- Allais arm for `subsume`: single-subterm cong via `subsumeCong`. -/
theorem ConvCumul.subst_compatible_subsume_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {innerType : Ty sourceLevel sourceScope}
    {innerRaw : RawTerm sourceScope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerCompat :
      ConvCumul (innerTerm.substHet termSubstA)
                (innerTerm.substHet termSubstB)) :
    ConvCumul ((Term.subsume innerTerm).substHet termSubstA)
              ((Term.subsume innerTerm).substHet termSubstB) :=
  ConvCumul.subsumeCong innerCompat

/-! ### Cubical path-fragment Allais arms

The typed D2.5 path mirror adds the same two shapes as ordinary
application/lambda: `pathLam` is a binder over `Ty.interval`, while
`pathApp` is a two-subterm eliminator.  The `pathLam` substitution arm
uses `Ty.weaken_substHet_commute`, so the body relation peels the same
cast on both sides before applying `ConvCumul.pathLamCong`. -/

/-- Allais arm for `interval0`: closed-payload, refl. -/
theorem ConvCumul.subst_compatible_interval0_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma) :
    ConvCumul ((Term.interval0 (context := sourceCtx)).substHet termSubstA)
              ((Term.interval0 (context := sourceCtx)).substHet termSubstB) :=
  ConvCumul.refl _

/-- Allais arm for `interval1`: closed-payload, refl. -/
theorem ConvCumul.subst_compatible_interval1_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma) :
    ConvCumul ((Term.interval1 (context := sourceCtx)).substHet termSubstA)
              ((Term.interval1 (context := sourceCtx)).substHet termSubstB) :=
  ConvCumul.refl _

/-- Allais arm for interval negation: one-subterm congruence. -/
theorem ConvCumul.subst_compatible_intervalOpp_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {innerRaw : RawTerm sourceScope}
    (innerValue : Term sourceCtx Ty.interval innerRaw)
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (innerCompat :
      ConvCumul (innerValue.substHet termSubstA)
                (innerValue.substHet termSubstB)) :
    ConvCumul ((Term.intervalOpp innerValue).substHet termSubstA)
              ((Term.intervalOpp innerValue).substHet termSubstB) :=
  ConvCumul.intervalOppCong innerCompat

/-- Allais arm for interval meet: two-subterm congruence. -/
theorem ConvCumul.subst_compatible_intervalMeet_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {leftRaw rightRaw : RawTerm sourceScope}
    (leftValue : Term sourceCtx Ty.interval leftRaw)
    (rightValue : Term sourceCtx Ty.interval rightRaw)
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (leftCompat :
      ConvCumul (leftValue.substHet termSubstA)
                (leftValue.substHet termSubstB))
    (rightCompat :
      ConvCumul (rightValue.substHet termSubstA)
                (rightValue.substHet termSubstB)) :
    ConvCumul ((Term.intervalMeet leftValue rightValue).substHet termSubstA)
              ((Term.intervalMeet leftValue rightValue).substHet termSubstB) :=
  ConvCumul.intervalMeetCong leftCompat rightCompat

/-- Allais arm for interval join: two-subterm congruence. -/
theorem ConvCumul.subst_compatible_intervalJoin_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {leftRaw rightRaw : RawTerm sourceScope}
    (leftValue : Term sourceCtx Ty.interval leftRaw)
    (rightValue : Term sourceCtx Ty.interval rightRaw)
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (leftCompat :
      ConvCumul (leftValue.substHet termSubstA)
                (leftValue.substHet termSubstB))
    (rightCompat :
      ConvCumul (rightValue.substHet termSubstA)
                (rightValue.substHet termSubstB)) :
    ConvCumul ((Term.intervalJoin leftValue rightValue).substHet termSubstA)
              ((Term.intervalJoin leftValue rightValue).substHet termSubstB) :=
  ConvCumul.intervalJoinCong leftCompat rightCompat

/-- Allais arm for `pathLam`: interval-binder cong via
`pathLamCong`. -/
theorem ConvCumul.subst_compatible_pathLam_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (carrierType : Ty sourceLevel sourceScope)
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    {bodyRaw : RawTerm (sourceScope + 1)}
    (body : Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw)
    (bodyCompat :
      ConvCumul (body.substHet (termSubstA.lift Ty.interval))
                (body.substHet (termSubstB.lift Ty.interval))) :
    ConvCumul
      ((Term.pathLam carrierType leftEndpoint rightEndpoint body).substHet
        termSubstA)
      ((Term.pathLam carrierType leftEndpoint rightEndpoint body).substHet
        termSubstB) :=
  ConvCumul.pathLamCong
    (ConvCumul.cast_eq_both_benton _ bodyCompat)

/-- Allais arm for `pathApp`: two-subterm cong via `pathAppCong`. -/
theorem ConvCumul.subst_compatible_pathApp_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {carrierType : Ty sourceLevel sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {pathRaw intervalRaw : RawTerm sourceScope}
    (pathTerm :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        pathRaw)
    (intervalTerm : Term sourceCtx Ty.interval intervalRaw)
    (pathCompat :
      ConvCumul (pathTerm.substHet termSubstA)
                (pathTerm.substHet termSubstB))
    (intervalCompat :
      ConvCumul (intervalTerm.substHet termSubstA)
                (intervalTerm.substHet termSubstB)) :
    ConvCumul ((Term.pathApp pathTerm intervalTerm).substHet termSubstA)
              ((Term.pathApp pathTerm intervalTerm).substHet termSubstB) :=
  ConvCumul.pathAppCong pathCompat intervalCompat

/-- Allais arm for `glueIntro`: two-subterm cong via
`glueIntroCong`. -/
theorem ConvCumul.subst_compatible_glueIntro_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (baseType : Ty sourceLevel sourceScope)
    (boundaryWitness : RawTerm sourceScope)
    {baseRaw partialRaw : RawTerm sourceScope}
    (baseValue : Term sourceCtx baseType baseRaw)
    (partialValue : Term sourceCtx baseType partialRaw)
    (baseCompat :
      ConvCumul (baseValue.substHet termSubstA)
                (baseValue.substHet termSubstB))
    (partialCompat :
      ConvCumul (partialValue.substHet termSubstA)
                (partialValue.substHet termSubstB)) :
    ConvCumul
      ((Term.glueIntro baseType boundaryWitness baseValue partialValue).substHet
        termSubstA)
      ((Term.glueIntro baseType boundaryWitness baseValue partialValue).substHet
        termSubstB) :=
  ConvCumul.glueIntroCong baseCompat partialCompat

/-- Allais arm for `glueElim`: single-subterm cong via
`glueElimCong`. -/
theorem ConvCumul.subst_compatible_glueElim_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {baseType : Ty sourceLevel sourceScope}
    {boundaryWitness gluedRaw : RawTerm sourceScope}
    (gluedValue : Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRaw)
    (gluedCompat :
      ConvCumul (gluedValue.substHet termSubstA)
                (gluedValue.substHet termSubstB)) :
    ConvCumul ((Term.glueElim gluedValue).substHet termSubstA)
              ((Term.glueElim gluedValue).substHet termSubstB) :=
  ConvCumul.glueElimCong gluedCompat

/-- Allais arm for `transp`: two-subterm cong via `transpCong`. -/
theorem ConvCumul.subst_compatible_transp_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ sourceLevel)
    (sourceType targetType : Ty sourceLevel sourceScope)
    (sourceTypeRaw targetTypeRaw : RawTerm sourceScope)
    {pathRaw sourceRaw : RawTerm sourceScope}
    (typePath :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw)
    (sourceValue : Term sourceCtx sourceType sourceRaw)
    (pathCompat :
      ConvCumul (typePath.substHet termSubstA)
                (typePath.substHet termSubstB))
    (sourceCompat :
      ConvCumul (sourceValue.substHet termSubstA)
                (sourceValue.substHet termSubstB)) :
    ConvCumul
      ((Term.transp universeLevel universeLevelLt sourceType targetType
        sourceTypeRaw targetTypeRaw typePath sourceValue).substHet
        termSubstA)
      ((Term.transp universeLevel universeLevelLt sourceType targetType
        sourceTypeRaw targetTypeRaw typePath sourceValue).substHet
        termSubstB) :=
  ConvCumul.transpCong universeLevel
    (Nat.le_trans universeLevelLt sigma.cumulOk)
    (sourceType.substHet sigma)
    (targetType.substHet sigma)
    (sourceTypeRaw.subst sigma.forRaw)
    (targetTypeRaw.subst sigma.forRaw)
    pathCompat sourceCompat

/-- Allais arm for `hcomp`: two-subterm cong via `hcompCong`. -/
theorem ConvCumul.subst_compatible_hcomp_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {carrierType : Ty sourceLevel sourceScope}
    {sidesRaw capRaw : RawTerm sourceScope}
    (sidesValue : Term sourceCtx carrierType sidesRaw)
    (capValue : Term sourceCtx carrierType capRaw)
    (sidesCompat :
      ConvCumul (sidesValue.substHet termSubstA)
                (sidesValue.substHet termSubstB))
    (capCompat :
      ConvCumul (capValue.substHet termSubstA)
                (capValue.substHet termSubstB)) :
    ConvCumul ((Term.hcomp sidesValue capValue).substHet termSubstA)
              ((Term.hcomp sidesValue capValue).substHet termSubstB) :=
  ConvCumul.hcompCong sidesCompat capCompat

/-! ### Allais closed-payload arms (parametric data + refl)

Like `unit` / `boolTrue`, these ctors carry no scope-dependent
substituents.  Both `Term.substHet` calls produce identical
output → `ConvCumul.refl _`. -/

/-- Allais arm for `listNil`: closed-payload, refl. -/
theorem ConvCumul.subst_compatible_listNil_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (elementType : Ty sourceLevel sourceScope) :
    ConvCumul ((Term.listNil (context := sourceCtx)
                             (elementType := elementType)).substHet termSubstA)
              ((Term.listNil (context := sourceCtx)
                             (elementType := elementType)).substHet termSubstB) :=
  ConvCumul.refl _

/-- Allais arm for `optionNone`: closed-payload, refl. -/
theorem ConvCumul.subst_compatible_optionNone_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (elementType : Ty sourceLevel sourceScope) :
    ConvCumul ((Term.optionNone (context := sourceCtx)
                                (elementType := elementType)).substHet termSubstA)
              ((Term.optionNone (context := sourceCtx)
                                (elementType := elementType)).substHet termSubstB) :=
  ConvCumul.refl _

/-- Allais arm for `refl` (identity-type witness): closed-payload
because `Term.refl` carries only Ty + RawTerm payload, no typed
subterms.  Both substituted sides produce the same `Term.refl`. -/
theorem ConvCumul.subst_compatible_refl_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (carrier : Ty sourceLevel sourceScope)
    (rawWitness : RawTerm sourceScope) :
    ConvCumul ((Term.refl (context := sourceCtx) carrier rawWitness).substHet termSubstA)
              ((Term.refl (context := sourceCtx) carrier rawWitness).substHet termSubstB) :=
  ConvCumul.refl _

/-! ### Allais single-subterm pair-projection arms

Term ctors that take a single Σ-pair as substituent.  Recurse
into pair compat, apply matching projection cong rule. -/

/-- Allais arm for `fst`: single-subterm cong via `fstCong`. -/
theorem ConvCumul.subst_compatible_fst_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {firstType : Ty sourceLevel sourceScope}
    {secondType : Ty sourceLevel (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    (pairTerm : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw)
    (pairCompat :
      ConvCumul (pairTerm.substHet termSubstA)
                (pairTerm.substHet termSubstB)) :
    ConvCumul ((Term.fst pairTerm).substHet termSubstA)
              ((Term.fst pairTerm).substHet termSubstB) :=
  ConvCumul.fstCong pairCompat

/-- Allais arm for `snd`: single-subterm cong via `sndCong` plus
BHKM cast handling.

`Term.substHet`'s `snd` arm wraps the result in
`(Ty.subst0_substHet_commute ...).symm ▸ Term.snd (...)`.  We
peel the cast via `ConvCumul.cast_eq_both_benton` (defined in
the Benton section below). -/
theorem ConvCumul.subst_compatible_snd_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {firstType : Ty sourceLevel sourceScope}
    {secondType : Ty sourceLevel (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    (pairTerm : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw)
    (pairCompat :
      ConvCumul (pairTerm.substHet termSubstA)
                (pairTerm.substHet termSubstB)) :
    ConvCumul ((Term.snd pairTerm).substHet termSubstA)
              ((Term.snd pairTerm).substHet termSubstB) :=
  ConvCumul.cast_eq_both_benton _
    (ConvCumul.sndCong pairCompat)

/-! ### Allais multi-subterm cong arms

Term ctors with two or more substituent subterms.  Recurse into
each inner ConvCumul witness; apply multi-arg cong rule. -/

/-- Allais arm for `app`: two-subterm cong via `appCong`. -/
theorem ConvCumul.subst_compatible_app_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {domainType codomainType : Ty sourceLevel sourceScope}
    {functionRaw argumentRaw : RawTerm sourceScope}
    (functionTerm : Term sourceCtx (Ty.arrow domainType codomainType) functionRaw)
    (argumentTerm : Term sourceCtx domainType argumentRaw)
    (functionCompat :
      ConvCumul (functionTerm.substHet termSubstA)
                (functionTerm.substHet termSubstB))
    (argumentCompat :
      ConvCumul (argumentTerm.substHet termSubstA)
                (argumentTerm.substHet termSubstB)) :
    ConvCumul ((Term.app functionTerm argumentTerm).substHet termSubstA)
              ((Term.app functionTerm argumentTerm).substHet termSubstB) :=
  ConvCumul.appCong functionCompat argumentCompat

/-- Allais arm for `appPi`: two-subterm cong via `appPiCong` plus
BHKM cast handling.

`Term.substHet`'s `appPi` arm wraps the result in
`(Ty.subst0_substHet_commute ...).symm ▸ Term.appPi ...`.  Same
cast on both sides → `cast_eq_both_benton` peels it. -/
theorem ConvCumul.subst_compatible_appPi_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {domainType : Ty sourceLevel sourceScope}
    {codomainType : Ty sourceLevel (sourceScope + 1)}
    {functionRaw argumentRaw : RawTerm sourceScope}
    (functionTerm :
      Term sourceCtx (Ty.piTy domainType codomainType) functionRaw)
    (argumentTerm : Term sourceCtx domainType argumentRaw)
    (functionCompat :
      ConvCumul (functionTerm.substHet termSubstA)
                (functionTerm.substHet termSubstB))
    (argumentCompat :
      ConvCumul (argumentTerm.substHet termSubstA)
                (argumentTerm.substHet termSubstB)) :
    ConvCumul ((Term.appPi functionTerm argumentTerm).substHet termSubstA)
              ((Term.appPi functionTerm argumentTerm).substHet termSubstB) :=
  ConvCumul.cast_eq_both_benton _
    (ConvCumul.appPiCong functionCompat argumentCompat)

/-- Allais arm for `pair`: two-subterm cong via `pairCong` plus
BHKM cast handling on the second component.

`Term.substHet`'s `pair` arm wraps the second component in
`Ty.subst0_substHet_commute ... ▸ ...`.  We use
`cast_eq_both_benton` to bridge the cast on the second component;
the first component is straight subst.

Construction strategy: the substituted output is
`Term.pair (firstValue.substHet ...) (cast ▸ secondValue.substHet ...)`.
Compose `pairCong` with cast_eq_both. -/
theorem ConvCumul.subst_compatible_pair_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {firstType : Ty sourceLevel sourceScope}
    {secondType : Ty sourceLevel (sourceScope + 1)}
    {firstRaw secondRaw : RawTerm sourceScope}
    (firstValue : Term sourceCtx firstType firstRaw)
    (secondValue : Term sourceCtx (secondType.subst0 firstType firstRaw) secondRaw)
    (firstCompat :
      ConvCumul (firstValue.substHet termSubstA)
                (firstValue.substHet termSubstB))
    (secondCompat :
      ConvCumul (secondValue.substHet termSubstA)
                (secondValue.substHet termSubstB)) :
    ConvCumul ((Term.pair firstValue secondValue).substHet termSubstA)
              ((Term.pair firstValue secondValue).substHet termSubstB) :=
  ConvCumul.pairCong firstCompat
    (ConvCumul.cast_eq_both_benton _ secondCompat)

/-- Allais arm for `listCons`: two-subterm cong via `listConsCong`. -/
theorem ConvCumul.subst_compatible_listCons_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {elementType : Ty sourceLevel sourceScope}
    {headRaw tailRaw : RawTerm sourceScope}
    (headTerm : Term sourceCtx elementType headRaw)
    (tailTerm : Term sourceCtx (Ty.listType elementType) tailRaw)
    (headCompat :
      ConvCumul (headTerm.substHet termSubstA)
                (headTerm.substHet termSubstB))
    (tailCompat :
      ConvCumul (tailTerm.substHet termSubstA)
                (tailTerm.substHet termSubstB)) :
    ConvCumul ((Term.listCons headTerm tailTerm).substHet termSubstA)
              ((Term.listCons headTerm tailTerm).substHet termSubstB) :=
  ConvCumul.listConsCong headCompat tailCompat

/-- Allais arm for `idJ`: two-subterm cong via `idJCong`. -/
theorem ConvCumul.subst_compatible_idJ_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {carrier : Ty sourceLevel sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty sourceLevel sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    (baseCase : Term sourceCtx motiveType baseRaw)
    (witness : Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw)
    (baseCompat :
      ConvCumul (baseCase.substHet termSubstA)
                (baseCase.substHet termSubstB))
    (witnessCompat :
      ConvCumul (witness.substHet termSubstA)
                (witness.substHet termSubstB)) :
    ConvCumul ((Term.idJ baseCase witness).substHet termSubstA)
              ((Term.idJ baseCase witness).substHet termSubstB) :=
  ConvCumul.idJCong baseCompat witnessCompat

/-- Allais arm for `boolElim`: three-subterm cong via `boolElimCong`. -/
theorem ConvCumul.subst_compatible_boolElim_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {motiveType : Ty sourceLevel sourceScope}
    {scrutineeRaw thenRaw elseRaw : RawTerm sourceScope}
    (scrutinee : Term sourceCtx Ty.bool scrutineeRaw)
    (thenBranch : Term sourceCtx motiveType thenRaw)
    (elseBranch : Term sourceCtx motiveType elseRaw)
    (scrutineeCompat :
      ConvCumul (scrutinee.substHet termSubstA)
                (scrutinee.substHet termSubstB))
    (thenCompat :
      ConvCumul (thenBranch.substHet termSubstA)
                (thenBranch.substHet termSubstB))
    (elseCompat :
      ConvCumul (elseBranch.substHet termSubstA)
                (elseBranch.substHet termSubstB)) :
    ConvCumul ((Term.boolElim scrutinee thenBranch elseBranch).substHet termSubstA)
              ((Term.boolElim scrutinee thenBranch elseBranch).substHet termSubstB) :=
  ConvCumul.boolElimCong scrutineeCompat thenCompat elseCompat

/-! ### Allais cumul-promotion arm

The `cumulUp` ctor's `Term.substHet` arm preserves `lowerTerm`
verbatim (its `scopeLow` is decoupled from outer `scope`).  Both
substituted sides produce literally the same Term value →
`ConvCumul.refl _`.

This mirrors the existing `ConvCumul.subst_compatible_cumulUp_term`
in `Reduction/Cumul.lean` (line ~1289) but takes the source ctor
fields directly rather than via specialized signature. -/

/-- Allais arm for `cumulUp` — Phase CUMUL-2.6 Design D.
The substituted typeCode-pair on each side gives ConvCumul; wrap via
cumulUpCong to lift over the cumul-promotion. -/
theorem ConvCumul.subst_compatible_cumulUp_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ sourceLevel)
    (levelLeHigh : higherLevel.toNat + 1 ≤ sourceLevel)
    {codeRaw : RawTerm sourceScope}
    (typeCode :
      Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw)
    (innerCompat :
      ConvCumul (typeCode.substHet termSubstA) (typeCode.substHet termSubstB)) :
    ConvCumul ((Term.cumulUp (context := sourceCtx)
                             lowerLevel higherLevel cumulMonotone
                             levelLeLow levelLeHigh typeCode).substHet termSubstA)
              ((Term.cumulUp (context := sourceCtx)
                             lowerLevel higherLevel cumulMonotone
                             levelLeLow levelLeHigh typeCode).substHet termSubstB) :=
  ConvCumul.cumulUpCong lowerLevel higherLevel cumulMonotone
                        (Nat.le_trans levelLeLow sigma.cumulOk)
                        (Nat.le_trans levelLeHigh sigma.cumulOk)
                        innerCompat

/-! ## Allais kernel-gap note: missing eliminator cong rules

The current `ConvCumul` inductive (`Reduction/Cumul.lean`) ships
cong rules for the data ctors above but DOES NOT ship cong rules
for the five eliminator ctors:
* `natElim` (3-subterm: scrutinee, zero branch, succ branch)
* `natRec`  (3-subterm: same shape as natElim)
* `listElim` (3-subterm: scrutinee, nil branch, cons branch)
* `optionMatch` (3-subterm: scrutinee, none branch, some branch)
* `eitherMatch` (3-subterm: scrutinee, left branch, right branch)

Without these cong rules, the Allais-style structural recursion on
the source Term cannot construct the substituted ConvCumul for
these five ctors.  Pre-existing kernel gap; documented as future
follow-up.  Tracked separately as a kernel extension task — adding
five cong rules to `ConvCumul` and an Allais arm for each follows
the same shape as `boolElimCong` / `subst_compatible_boolElim_allais`
above.

The remaining 25 ctors (var + unit + arrow + sigma + bool +
nat-data-without-eliminators + list-data-without-eliminator +
option-data-without-eliminator + either-data-without-eliminator +
identity-types + modal + universe + cumul-promotion) ARE covered
by the per-ctor Allais arms shipped above, contingent on the
binder lift (lam, lamPi) which awaits the Benton rename theorem
in the next section. -/

/-! # Allais binder arms (Step C — lam + lamPi)

The two binder Term constructors close the per-ctor Allais
catalogue.  Each takes a body-level inner ConvCumul (typically
produced by a recursive call on the body under a lifted
TermSubstHet) and applies the matching `lamCong` / `lamPiCong`
rule, peeling `Term.substHet`'s `Ty.weaken_substHet_commute` cast
via `cast_eq_both_benton` where needed.

The user is responsible for constructing the inner compat for
the lifted TermSubstHets — that's the standard Allais
`Simulation.alg` discharge pattern (arxiv:1804.00119 §5.1).  The
kernel does not auto-generate `PointwiseCompat.lift` because
weakening preserves heterogeneous-source-ctx ConvCumul requires
`induction cumulRel` (the Lean 4.29.1 wall described above) for
the general case.  For homogeneous compat (compat = refl), the
lifted compat is trivially refl.
-/

/-- Allais arm for `lam`: binder cong via `lamCong`.

`Term.substHet`'s `lam` arm wraps the body in
`Ty.weaken_substHet_commute ▸ ·` — same cast on both sides (same
sigma), peeled via `cast_eq_both_benton`. -/
theorem ConvCumul.subst_compatible_lam_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {domainType codomainType : Ty sourceLevel sourceScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    (body : Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw)
    (innerCompat :
      ConvCumul (body.substHet (termSubstA.lift domainType))
                (body.substHet (termSubstB.lift domainType))) :
    ConvCumul ((Term.lam body).substHet termSubstA)
              ((Term.lam body).substHet termSubstB) :=
  ConvCumul.lamCong (ConvCumul.cast_eq_both_benton _ innerCompat)

/-- Allais arm for `lamPi`: binder cong via `lamPiCong`.

`Term.substHet`'s `lamPi` arm has NO cast (body type is just
codomainType in extended scope) — direct cong application. -/
theorem ConvCumul.subst_compatible_lamPi_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {domainType : Ty sourceLevel sourceScope}
    {codomainType : Ty sourceLevel (sourceScope + 1)}
    {bodyRaw : RawTerm (sourceScope + 1)}
    (body : Term (sourceCtx.cons domainType) codomainType bodyRaw)
    (innerCompat :
      ConvCumul (body.substHet (termSubstA.lift domainType))
                (body.substHet (termSubstB.lift domainType))) :
    ConvCumul ((Term.lamPi body).substHet termSubstA)
              ((Term.lamPi body).substHet termSubstB) :=
  ConvCumul.lamPiCong innerCompat

/-! # Allais eliminator arms — kernel-gap closed

The 5 eliminator constructors (`natElim`, `natRec`, `listElim`,
`optionMatch`, `eitherMatch`) now have `ConvCumul` cong rules in
the kernel (`Reduction/Cumul.lean`).  These per-arm helpers
mirror the cong rules at `Term.substHet` level. -/

/-- Allais arm for `natElim`: three-subterm cong via `natElimCong`. -/
theorem ConvCumul.subst_compatible_natElim_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {motiveType : Ty sourceLevel sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    (scrutinee : Term sourceCtx Ty.nat scrutineeRaw)
    (zeroBranch : Term sourceCtx motiveType zeroRaw)
    (succBranch : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw)
    (scrutCompat :
      ConvCumul (scrutinee.substHet termSubstA) (scrutinee.substHet termSubstB))
    (zeroCompat :
      ConvCumul (zeroBranch.substHet termSubstA) (zeroBranch.substHet termSubstB))
    (succCompat :
      ConvCumul (succBranch.substHet termSubstA) (succBranch.substHet termSubstB)) :
    ConvCumul ((Term.natElim scrutinee zeroBranch succBranch).substHet termSubstA)
              ((Term.natElim scrutinee zeroBranch succBranch).substHet termSubstB) :=
  ConvCumul.natElimCong scrutCompat zeroCompat succCompat

/-- Allais arm for `natRec`: three-subterm cong via `natRecCong`. -/
theorem ConvCumul.subst_compatible_natRec_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {motiveType : Ty sourceLevel sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    (scrutinee : Term sourceCtx Ty.nat scrutineeRaw)
    (zeroBranch : Term sourceCtx motiveType zeroRaw)
    (succBranch :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw)
    (scrutCompat :
      ConvCumul (scrutinee.substHet termSubstA) (scrutinee.substHet termSubstB))
    (zeroCompat :
      ConvCumul (zeroBranch.substHet termSubstA) (zeroBranch.substHet termSubstB))
    (succCompat :
      ConvCumul (succBranch.substHet termSubstA) (succBranch.substHet termSubstB)) :
    ConvCumul ((Term.natRec scrutinee zeroBranch succBranch).substHet termSubstA)
              ((Term.natRec scrutinee zeroBranch succBranch).substHet termSubstB) :=
  ConvCumul.natRecCong scrutCompat zeroCompat succCompat

/-- Allais arm for `listElim`: three-subterm cong via `listElimCong`. -/
theorem ConvCumul.subst_compatible_listElim_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {elementType motiveType : Ty sourceLevel sourceScope}
    {scrutineeRaw nilRaw consRaw : RawTerm sourceScope}
    (scrutinee : Term sourceCtx (Ty.listType elementType) scrutineeRaw)
    (nilBranch : Term sourceCtx motiveType nilRaw)
    (consBranch :
      Term sourceCtx (Ty.arrow elementType
                      (Ty.arrow (Ty.listType elementType) motiveType)) consRaw)
    (scrutCompat :
      ConvCumul (scrutinee.substHet termSubstA) (scrutinee.substHet termSubstB))
    (nilCompat :
      ConvCumul (nilBranch.substHet termSubstA) (nilBranch.substHet termSubstB))
    (consCompat :
      ConvCumul (consBranch.substHet termSubstA) (consBranch.substHet termSubstB)) :
    ConvCumul ((Term.listElim scrutinee nilBranch consBranch).substHet termSubstA)
              ((Term.listElim scrutinee nilBranch consBranch).substHet termSubstB) :=
  ConvCumul.listElimCong scrutCompat nilCompat consCompat

/-- Allais arm for `optionMatch`: three-subterm cong via `optionMatchCong`. -/
theorem ConvCumul.subst_compatible_optionMatch_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {elementType motiveType : Ty sourceLevel sourceScope}
    {scrutineeRaw noneRaw someRaw : RawTerm sourceScope}
    (scrutinee : Term sourceCtx (Ty.optionType elementType) scrutineeRaw)
    (noneBranch : Term sourceCtx motiveType noneRaw)
    (someBranch : Term sourceCtx (Ty.arrow elementType motiveType) someRaw)
    (scrutCompat :
      ConvCumul (scrutinee.substHet termSubstA) (scrutinee.substHet termSubstB))
    (noneCompat :
      ConvCumul (noneBranch.substHet termSubstA) (noneBranch.substHet termSubstB))
    (someCompat :
      ConvCumul (someBranch.substHet termSubstA) (someBranch.substHet termSubstB)) :
    ConvCumul
      ((Term.optionMatch scrutinee noneBranch someBranch).substHet termSubstA)
      ((Term.optionMatch scrutinee noneBranch someBranch).substHet termSubstB) :=
  ConvCumul.optionMatchCong scrutCompat noneCompat someCompat

/-- Allais arm for `eitherMatch`: three-subterm cong via `eitherMatchCong`. -/
theorem ConvCumul.subst_compatible_eitherMatch_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {leftType rightType motiveType : Ty sourceLevel sourceScope}
    {scrutineeRaw leftRaw rightRaw : RawTerm sourceScope}
    (scrutinee : Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw)
    (leftBranch : Term sourceCtx (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term sourceCtx (Ty.arrow rightType motiveType) rightRaw)
    (scrutCompat :
      ConvCumul (scrutinee.substHet termSubstA) (scrutinee.substHet termSubstB))
    (leftCompat :
      ConvCumul (leftBranch.substHet termSubstA) (leftBranch.substHet termSubstB))
    (rightCompat :
      ConvCumul (rightBranch.substHet termSubstA) (rightBranch.substHet termSubstB)) :
    ConvCumul
      ((Term.eitherMatch scrutinee leftBranch rightBranch).substHet termSubstA)
      ((Term.eitherMatch scrutinee leftBranch rightBranch).substHet termSubstB) :=
  ConvCumul.eitherMatchCong scrutCompat leftCompat rightCompat

end LeanFX2
