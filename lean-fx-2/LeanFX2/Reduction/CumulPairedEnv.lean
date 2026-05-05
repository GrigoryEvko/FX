import LeanFX2.Reduction.CumulAllais
import LeanFX2.Reduction.ConvCumulHomo

/-! # Reduction/CumulPairedEnv — Pattern 3 paired-env infrastructure (Allais)

The FOUNDATIONAL infrastructure for the Allais ICFP'18 paired-environment
simulation framework, plus the Pattern 3 fundamental lemma instantiated
at identity simulation.

## What this file ships

* `TermSubstHet.PointwiseCompatHomo` predicate — paired-env compat at
  `ConvCumulHomo` level.  Combinators (refl / sym / trans /
  toPointwiseCompat) and the load-bearing `lift` lemma for binder cases.

* `Term.subst_compatible_pointwise_allais` — the Pattern 3 fundamental
  lemma.  Outer Term-induction dispatching to the per-Term-ctor Allais
  arms in `Reduction/CumulAllais.lean`.

* `ConvCumul.subst_compatible_paired_allais` — the identity-simulation
  headline.  `cumulRel = .refl` case of the FULL Pattern 3 headline.

The FULL HEADLINE (`ConvCumulHomo.subst_compatible_paired_allais`) lives
in `Reduction/CumulSubstCompat.lean` because it integrates everything
shipped here with the `ConvCumulHomo` cumulRel induction.

## Why Homo-typed compat is the right shape

`PointwiseCompat` (general form, in `CumulAllais.lean`) quantifies
`ConvCumul (termSubstA pos) (termSubstB pos)` per position.  The lift
lemma needs to RENAME each per-position witness via `Term.weaken`.
Renaming a full `ConvCumul` witness hits the heterogeneous-Prop wall:
`viaUp`'s `lowerTerm` lives at decoupled `scopeLow`, so a single outer
renaming is ill-typed for it.

`PointwiseCompatHomo` restricts each per-position witness to
`ConvCumulHomo` (the homogeneous fragment, no `viaUp`).  Homo IS
preserved under typed renaming (see
`ConvCumulHomo.rename_compatible_benton` in `Reduction/ConvCumulHomo.lean`),
so the lift lemma ships zero-axiom.

For substituents at the SAME outer target context (which is the case for
any well-typed `TermSubstHet` instance), the per-position witnesses can
always be expressed as `ConvCumulHomo` — `viaUp`-style witnesses would
require the substituents at different scopes, which the typing of
`TermSubstHet` rules out.  So `PointwiseCompatHomo` is no less expressive
than `PointwiseCompat` in the well-typed setting.

## Reference

Allais, Atkey, Chapman, McBride, McKinna, *A Type and Scope Safe Universe
of Syntaxes with Binding*, ICFP 2018 / JFP 2021 (arxiv:1804.00119) §5
(Simulation framework), record `Simulation`.  FX memory
`reference_pattern_allais_simulation`.

## Audit

All shipped declarations verified zero-axiom under strict policy in
`Smoke/AuditCumulSubstCompat.lean`.
-/

namespace LeanFX2

/-! # Pattern 3 (Allais paired-env) — Homo-typed compat + lift

This section ships the FOUNDATIONAL infrastructure for Pattern 3
proper: a paired-environment compat predicate `PointwiseCompatHomo`
where each per-position relation is `ConvCumulHomo` (not `ConvCumul`),
and a `lift` lemma that propagates compat through binders.

## Why Homo-typed compat is the right shape

`PointwiseCompat termSubstA termSubstB` (defined above, line 177)
quantifies `ConvCumul (termSubstA pos) (termSubstB pos)` per position.
The lift lemma needs to RENAME each per-position witness via
`Term.weaken` (= `Term.rename (TermRenaming.weakenStep _ _)`).
Renaming a full `ConvCumul` witness hits the heterogeneous-Prop wall:
`viaUp`'s `lowerTerm` lives at decoupled `scopeLow`, so a single
outer renaming is ill-typed for it.

`PointwiseCompatHomo` restricts each per-position witness to
`ConvCumulHomo` (the homogeneous fragment, no `viaUp`).  Homo IS
preserved under typed renaming (see `ConvCumulHomo.rename_compatible_benton`,
ConvCumulHomo.lean line 522), so the lift lemma ships zero-axiom.

For substituents at the SAME outer target context (which is the case
for any well-typed `TermSubstHet` instance), the per-position
witnesses can always be expressed as `ConvCumulHomo` — `viaUp`-style
witnesses would require the substituents at different scopes, which
the typing of `TermSubstHet` rules out.  So `PointwiseCompatHomo`
is no less expressive than `PointwiseCompat` in the well-typed
setting.

## Conversion + combinators

`PointwiseCompatHomo.toPointwiseCompat` lifts to the ConvCumul-typed
form via per-position `ConvCumulHomo.toCumul`.  This bridges to the
existing per-Term-ctor Allais arms (which consume `ConvCumul` per
subterm).

Refl / sym / trans mirror `PointwiseCompat`'s combinators but at
ConvCumulHomo level. -/

/-- **Pattern 3 paired-env compat (Homo-typed)**.  Stronger than
`PointwiseCompat`: each per-position relation is `ConvCumulHomo`,
restricted to the homogeneous fragment.

Required for the lift lemma since `ConvCumulHomo` IS preserved by
typed renaming whereas full `ConvCumul` is not (viaUp's heterogeneous
endpoint scopes block a uniform rename theorem). -/
def TermSubstHet.PointwiseCompatHomo
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma) :
    Prop :=
  ∀ position, ConvCumulHomo (termSubstA position) (termSubstB position)

/-- Reflexivity: any `TermSubstHet` is Homo-compat with itself. -/
theorem TermSubstHet.PointwiseCompatHomo.refl
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubst : TermSubstHet sourceCtx targetCtx sigma) :
    TermSubstHet.PointwiseCompatHomo termSubst termSubst :=
  fun position => ConvCumulHomo.refl (termSubst position)

/-- Symmetry of Homo-compat. -/
theorem TermSubstHet.PointwiseCompatHomo.sym
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (compat : TermSubstHet.PointwiseCompatHomo termSubstA termSubstB) :
    TermSubstHet.PointwiseCompatHomo termSubstB termSubstA :=
  fun position => ConvCumulHomo.sym (compat position)

/-- Transitivity of Homo-compat. -/
theorem TermSubstHet.PointwiseCompatHomo.trans
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB termSubstC : TermSubstHet sourceCtx targetCtx sigma}
    (compatAB : TermSubstHet.PointwiseCompatHomo termSubstA termSubstB)
    (compatBC : TermSubstHet.PointwiseCompatHomo termSubstB termSubstC) :
    TermSubstHet.PointwiseCompatHomo termSubstA termSubstC :=
  fun position => ConvCumulHomo.trans (compatAB position) (compatBC position)

/-- **Bridge**: Homo-compat ⇒ general PointwiseCompat (over ConvCumul).
Per-position via `ConvCumulHomo.toCumul`.  Used to feed the Homo-compat
into the existing per-Term-ctor Allais arms (which consume
`PointwiseCompat` for the var arm). -/
theorem TermSubstHet.PointwiseCompatHomo.toPointwiseCompat
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (compat : TermSubstHet.PointwiseCompatHomo termSubstA termSubstB) :
    TermSubstHet.PointwiseCompat termSubstA termSubstB :=
  fun position => (compat position).toCumul

/-- **The lift lemma** — load-bearing for Pattern 3 binder cases.

Given Homo-compat between two `TermSubstHet`s at `(sourceCtx, targetCtx, sigma)`,
produce Homo-compat between their lifts at `(sourceCtx.cons T, targetCtx.cons (T.substHet sigma), sigma.lift)`.

Architecture (per `TermSubstHet.lift` definition, Term/SubstHet.lean line 86):

* Position `⟨0, _⟩`: both lifts produce the SAME expression
  `(Ty.weaken_substHet_commute sigma T).symm ▸ Term.var ⟨0, _⟩`
  (no termSubst dependence) → `ConvCumulHomo.refl _`.

* Position `⟨k+1, h⟩`: both lifts apply the SAME cast around
  `Term.weaken (T.substHet sigma) (termSubstX ⟨k, _⟩)`.  Apply
  `ConvCumulHomo.rename_compatible_benton` to `compat ⟨k, _⟩` with
  the canonical weakening `TermRenaming.weakenStep`, then peel the
  cast via `cast_eq_both`.

`Term.weaken` unfolds to `Term.rename (TermRenaming.weakenStep _ _)`
(Term/Rename.lean line 240), so the rename theorem applies directly. -/
theorem TermSubstHet.PointwiseCompatHomo.lift
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (compat : TermSubstHet.PointwiseCompatHomo termSubstA termSubstB)
    (newSourceType : Ty sourceLevel sourceScope) :
    TermSubstHet.PointwiseCompatHomo
        (termSubstA.lift newSourceType)
        (termSubstB.lift newSourceType)
  | ⟨0, _⟩ =>
      -- Both lifts produce the same expression at position 0;
      -- ConvCumulHomo.refl on a single Term value, no compat needed.
      ConvCumulHomo.refl _
  | ⟨k + 1, hPos⟩ =>
      -- Both lifts apply the SAME cast (Ty.weaken_substHet_commute)
      -- around Term.weaken (newSourceType.substHet sigma) (termSubstX ⟨k, _⟩).
      -- compat ⟨k, _⟩ : ConvCumulHomo (termSubstA k) (termSubstB k).
      -- rename_compatible_benton lifts to ConvCumulHomo of weakened forms.
      -- cast_eq_both peels the equal-on-both-sides cast.
      ConvCumulHomo.cast_eq_both _
        (ConvCumulHomo.rename_compatible_benton
          (compat ⟨k, Nat.lt_of_succ_lt_succ hPos⟩)
          (TermRenaming.weakenStep targetCtx (newSourceType.substHet sigma)))

/-! # Pattern 3 fundamental lemma — Term-induction with per-arm dispatch

The fundamental lemma of Pattern 3 (Allais's `sim` field, ICFP'18
arxiv:1804.00119 §5.1).  Given any `Term` in source ctx and a
`PointwiseCompatHomo`-related pair of `TermSubstHet`s, the
substituted forms on the two sides are `ConvCumul`-related.

By structural recursion on `term`, dispatching to the per-Term-ctor
Allais arm helpers shipped above (lines 258-1629).  Each ctor case
recurses on its subterms with the same `compat` (or `compat.lift`
for binders) and feeds the inner ConvCumul witnesses to the matching
per-arm helper.

This is the OUTER induction structure that dissolves the
heterogeneous-Prop wall (memory `reference_pattern_allais_simulation`):
* Source side fixed by Term-induction → `compat` consumed pointwise.
* Target side determined by Term shape under substitution → no
  cross-source unification problem.
* `viaUp` cannot fire here because the recursion is on Term
  (homogeneous source), not on `ConvCumul` (heterogeneous wall). -/

/-- **Pattern 3 fundamental lemma**: `Term.substHet` is compatible
with pointwise-Homo-compat substitutions.  Outer Term-induction
dispatching to per-arm Allais helpers. -/
def Term.subst_compatible_pointwise_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (compat : TermSubstHet.PointwiseCompatHomo termSubstA termSubstB) :
    ∀ {someType : Ty sourceLevel sourceScope} {someRaw : RawTerm sourceScope}
      (term : Term sourceCtx someType someRaw),
      ConvCumul (term.substHet termSubstA) (term.substHet termSubstB)
  | _, _, .var pos =>
      ConvCumul.subst_compatible_var_allais compat.toPointwiseCompat pos
  | _, _, .unit =>
      ConvCumul.subst_compatible_unit_allais _ _
  | _, _, .boolTrue =>
      ConvCumul.subst_compatible_boolTrue_allais _ _
  | _, _, .boolFalse =>
      ConvCumul.subst_compatible_boolFalse_allais _ _
  | _, _, .natZero =>
      ConvCumul.subst_compatible_natZero_allais _ _
  | _, _, .listNil =>
      ConvCumul.subst_compatible_listNil_allais _ _ _
  | _, _, .optionNone =>
      ConvCumul.subst_compatible_optionNone_allais _ _ _
  | _, _, .interval0 =>
      ConvCumul.subst_compatible_interval0_allais _ _
  | _, _, .interval1 =>
      ConvCumul.subst_compatible_interval1_allais _ _
  | _, _, .universeCode innerLevel outerLevel cumulOk levelLe =>
      ConvCumul.subst_compatible_universeCode_allais _ _
        innerLevel outerLevel cumulOk levelLe
  | _, _, .refl carrier rawWitness =>
      ConvCumul.subst_compatible_refl_allais _ _ carrier rawWitness
  | _, _, .natSucc predecessor =>
      ConvCumul.subst_compatible_natSucc_allais predecessor
        (Term.subst_compatible_pointwise_allais compat predecessor)
  | _, _, .optionSome valueTerm =>
      ConvCumul.subst_compatible_optionSome_allais valueTerm
        (Term.subst_compatible_pointwise_allais compat valueTerm)
  | _, _, .eitherInl valueTerm =>
      ConvCumul.subst_compatible_eitherInl_allais valueTerm
        (Term.subst_compatible_pointwise_allais compat valueTerm)
  | _, _, .eitherInr valueTerm =>
      ConvCumul.subst_compatible_eitherInr_allais valueTerm
        (Term.subst_compatible_pointwise_allais compat valueTerm)
  | _, _, .modIntro inner =>
      ConvCumul.subst_compatible_modIntro_allais inner
        (Term.subst_compatible_pointwise_allais compat inner)
  | _, _, .modElim inner =>
      ConvCumul.subst_compatible_modElim_allais inner
        (Term.subst_compatible_pointwise_allais compat inner)
  | _, _, .subsume inner =>
      ConvCumul.subst_compatible_subsume_allais inner
        (Term.subst_compatible_pointwise_allais compat inner)
  | _, _, .pathLam carrierType leftEndpoint rightEndpoint body =>
      ConvCumul.subst_compatible_pathLam_allais
        carrierType leftEndpoint rightEndpoint body
        (Term.subst_compatible_pointwise_allais
          (compat.lift Ty.interval) body)
  | _, _, .pathApp pathTerm intervalTerm =>
      ConvCumul.subst_compatible_pathApp_allais pathTerm intervalTerm
        (Term.subst_compatible_pointwise_allais compat pathTerm)
        (Term.subst_compatible_pointwise_allais compat intervalTerm)
  | _, _, .fst pairTerm =>
      ConvCumul.subst_compatible_fst_allais pairTerm
        (Term.subst_compatible_pointwise_allais compat pairTerm)
  | _, _, .snd pairTerm =>
      ConvCumul.subst_compatible_snd_allais pairTerm
        (Term.subst_compatible_pointwise_allais compat pairTerm)
  | _, _, .app functionTerm argumentTerm =>
      ConvCumul.subst_compatible_app_allais functionTerm argumentTerm
        (Term.subst_compatible_pointwise_allais compat functionTerm)
        (Term.subst_compatible_pointwise_allais compat argumentTerm)
  | _, _, .appPi functionTerm argumentTerm =>
      ConvCumul.subst_compatible_appPi_allais functionTerm argumentTerm
        (Term.subst_compatible_pointwise_allais compat functionTerm)
        (Term.subst_compatible_pointwise_allais compat argumentTerm)
  | _, _, .pair firstValue secondValue =>
      ConvCumul.subst_compatible_pair_allais firstValue secondValue
        (Term.subst_compatible_pointwise_allais compat firstValue)
        (Term.subst_compatible_pointwise_allais compat secondValue)
  | _, _, .listCons headTerm tailTerm =>
      ConvCumul.subst_compatible_listCons_allais headTerm tailTerm
        (Term.subst_compatible_pointwise_allais compat headTerm)
        (Term.subst_compatible_pointwise_allais compat tailTerm)
  | _, _, .idJ baseCase witness =>
      ConvCumul.subst_compatible_idJ_allais baseCase witness
        (Term.subst_compatible_pointwise_allais compat baseCase)
        (Term.subst_compatible_pointwise_allais compat witness)
  | _, _, .boolElim scrutinee thenBranch elseBranch =>
      ConvCumul.subst_compatible_boolElim_allais scrutinee thenBranch elseBranch
        (Term.subst_compatible_pointwise_allais compat scrutinee)
        (Term.subst_compatible_pointwise_allais compat thenBranch)
        (Term.subst_compatible_pointwise_allais compat elseBranch)
  | _, _, .natElim scrutinee zeroBranch succBranch =>
      ConvCumul.subst_compatible_natElim_allais scrutinee zeroBranch succBranch
        (Term.subst_compatible_pointwise_allais compat scrutinee)
        (Term.subst_compatible_pointwise_allais compat zeroBranch)
        (Term.subst_compatible_pointwise_allais compat succBranch)
  | _, _, .natRec scrutinee zeroBranch succBranch =>
      ConvCumul.subst_compatible_natRec_allais scrutinee zeroBranch succBranch
        (Term.subst_compatible_pointwise_allais compat scrutinee)
        (Term.subst_compatible_pointwise_allais compat zeroBranch)
        (Term.subst_compatible_pointwise_allais compat succBranch)
  | _, _, .listElim scrutinee nilBranch consBranch =>
      ConvCumul.subst_compatible_listElim_allais scrutinee nilBranch consBranch
        (Term.subst_compatible_pointwise_allais compat scrutinee)
        (Term.subst_compatible_pointwise_allais compat nilBranch)
        (Term.subst_compatible_pointwise_allais compat consBranch)
  | _, _, .optionMatch scrutinee noneBranch someBranch =>
      ConvCumul.subst_compatible_optionMatch_allais scrutinee noneBranch someBranch
        (Term.subst_compatible_pointwise_allais compat scrutinee)
        (Term.subst_compatible_pointwise_allais compat noneBranch)
        (Term.subst_compatible_pointwise_allais compat someBranch)
  | _, _, .eitherMatch scrutinee leftBranch rightBranch =>
      ConvCumul.subst_compatible_eitherMatch_allais scrutinee leftBranch rightBranch
        (Term.subst_compatible_pointwise_allais compat scrutinee)
        (Term.subst_compatible_pointwise_allais compat leftBranch)
        (Term.subst_compatible_pointwise_allais compat rightBranch)
  | _, _, .lam body =>
      ConvCumul.subst_compatible_lam_allais body
        (Term.subst_compatible_pointwise_allais (compat.lift _) body)
  | _, _, .lamPi body =>
      ConvCumul.subst_compatible_lamPi_allais body
        (Term.subst_compatible_pointwise_allais (compat.lift _) body)
  | _, _, .cumulUp lowerLevel higherLevel cumulMonotone
                   levelLeLow levelLeHigh typeCode =>
      -- Phase CUMUL-2.6 Design D: recurse on inner typeCode via the
      -- pointwise allais dispatcher (compat is the paired-env's
      -- per-position compatibility).  Wrap via cumulUpCong (Allais
      -- arm).
      ConvCumul.subst_compatible_cumulUp_allais _ _
        lowerLevel higherLevel cumulMonotone
        levelLeLow levelLeHigh typeCode
        (Term.subst_compatible_pointwise_allais compat typeCode)
  | _, _, .equivReflId carrier =>
      ConvCumul.subst_compatible_equivReflId_allais _ _ carrier
  | _, _, .funextRefl domainType codomainType applyRaw =>
      ConvCumul.subst_compatible_funextRefl_allais _ _
        domainType codomainType applyRaw
  | _, _, .equivReflIdAtId innerLevel innerLevelLt carrier carrierRaw =>
      ConvCumul.subst_compatible_equivReflIdAtId_allais _ _
        innerLevel innerLevelLt carrier carrierRaw
  | _, _, .funextReflAtId domainType codomainType applyRaw =>
      ConvCumul.subst_compatible_funextReflAtId_allais _ _
        domainType codomainType applyRaw
  | _, _, .equivIntroHet forward backward =>
      ConvCumul.subst_compatible_equivIntroHet_allais
        forward backward
        (Term.subst_compatible_pointwise_allais compat forward)
        (Term.subst_compatible_pointwise_allais compat backward)
  | _, _, .uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw
                      equivWitness =>
      ConvCumul.subst_compatible_uaIntroHet_allais
        innerLevel innerLevelLt carrierARaw carrierBRaw
        equivWitness
        (Term.subst_compatible_pointwise_allais compat equivWitness)
  -- Phase 12.A.B8.8 (heterogeneous funext-intro at Id-of-arrow):
  -- VALUE ctor, NO typed subterms — same precedent as funextReflAtId.
  -- Both substHet sides depend only on `sigma`, ConvCumul.refl
  -- discharges via the helper.
  | _, _, .funextIntroHet domainType codomainType applyARaw applyBRaw =>
      ConvCumul.subst_compatible_funextIntroHet_allais _ _
        domainType codomainType applyARaw applyBRaw
  -- CUMUL-2.4 typed type-code constructors (VALUE-shaped).  Dispatch
  -- to the matching helper; both substHet sides depend only on
  -- `sigma`, so `ConvCumul.refl` discharges via the helper.
  | _, _, .arrowCode outerLevel levelLe domainCodeRaw codomainCodeRaw =>
      ConvCumul.subst_compatible_arrowCode_allais _ _
        outerLevel levelLe domainCodeRaw codomainCodeRaw
  | _, _, .piTyCode outerLevel levelLe domainCodeRaw codomainCodeRaw =>
      ConvCumul.subst_compatible_piTyCode_allais _ _
        outerLevel levelLe domainCodeRaw codomainCodeRaw
  | _, _, .sigmaTyCode outerLevel levelLe domainCodeRaw codomainCodeRaw =>
      ConvCumul.subst_compatible_sigmaTyCode_allais _ _
        outerLevel levelLe domainCodeRaw codomainCodeRaw
  | _, _, .productCode outerLevel levelLe firstCodeRaw secondCodeRaw =>
      ConvCumul.subst_compatible_productCode_allais _ _
        outerLevel levelLe firstCodeRaw secondCodeRaw
  | _, _, .sumCode outerLevel levelLe leftCodeRaw rightCodeRaw =>
      ConvCumul.subst_compatible_sumCode_allais _ _
        outerLevel levelLe leftCodeRaw rightCodeRaw
  | _, _, .listCode outerLevel levelLe elementCodeRaw =>
      ConvCumul.subst_compatible_listCode_allais _ _
        outerLevel levelLe elementCodeRaw
  | _, _, .optionCode outerLevel levelLe elementCodeRaw =>
      ConvCumul.subst_compatible_optionCode_allais _ _
        outerLevel levelLe elementCodeRaw
  | _, _, .eitherCode outerLevel levelLe leftCodeRaw rightCodeRaw =>
      ConvCumul.subst_compatible_eitherCode_allais _ _
        outerLevel levelLe leftCodeRaw rightCodeRaw
  | _, _, .idCode outerLevel levelLe typeCodeRaw leftRaw rightRaw =>
      ConvCumul.subst_compatible_idCode_allais _ _
        outerLevel levelLe typeCodeRaw leftRaw rightRaw
  | _, _, .equivCode outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw =>
      ConvCumul.subst_compatible_equivCode_allais _ _
        outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw

/-! # Pattern 3 headline — ConvCumulHomo + paired-env compat → ConvCumul

The full Allais ICFP'18 headline (memory `reference_pattern_allais_simulation`).

Architecture: structural induction on `cumulRel : ConvCumulHomo a b`
with the per-cumulRel-ctor decomposition:

* `refl t`: fundamental lemma (Term-induction on `t` with `compat`).
* `sym inner`: recurse on `inner` with `compat.sym`, apply `ConvCumul.sym`.
* `trans rel1 rel2`: recurse on `rel1` with `compat.refl-of-σA` to get
  `ConvCumul (a.substHet σA) (m.substHet σA)`; recurse on `rel2` with
  `compat` to get `ConvCumul (m.substHet σA) (b.substHet σB)`; trans.
* cong rules (22 + 5 eliminator + cumulUpCong = 28): recurse on inner
  ConvCumulHomo subwitnesses with `compat`, apply matching `ConvCumul.{X}Cong`
  rule, peel casts via `cast_eq_both_benton` / `cast_eq_indep` as needed.

The wall is sidestepped because:
* Outer induction is on `ConvCumulHomo` (no viaUp ctor present).
* All ctor cases match canonically without index-unification problems.
* Per-position renaming inside `compat.lift` works on `ConvCumulHomo`
  (which IS preserved by typed renaming).

Result type: `ConvCumul` (not `ConvCumulHomo`) because some cases
(notably cumulUpCong) need the lower side at decoupled scopeLow,
which fits ConvCumul's full ctor set but not ConvCumulHomo's
homogeneous-only fragment after substitution.  Caveat: the inner
`lowerRel` of cumulUpCong remains untouched — substHet preserves
lowerTerm verbatim. -/

/-- **Pattern 3 fundamental headline (Allais sim at identity simulation)**:
for any source Term and paired-env Homo-compat, the substituted
forms on each side are ConvCumul-related.  This is the `cumulRel = .refl`
case of the full headline. -/
theorem ConvCumul.subst_compatible_paired_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {someType : Ty sourceLevel sourceScope}
    {someRaw : RawTerm sourceScope}
    (term : Term sourceCtx someType someRaw)
    (compat : TermSubstHet.PointwiseCompatHomo termSubstA termSubstB) :
    ConvCumul (term.substHet termSubstA) (term.substHet termSubstB) :=
  Term.subst_compatible_pointwise_allais compat term

end LeanFX2
