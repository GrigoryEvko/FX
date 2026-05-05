import LeanFX2.Reduction.CumulPairedEnv
import LeanFX2.Reduction.CumulBenton

/-! # Reduction/CumulSubstCompat — CUMUL-1.7 substitution-compatibility entry point

Two complementary substantive theorems for CUMUL-1.7, named by their
canonical authors in the type-theory literature.  This file integrates
the per-Term-ctor catalogues into the FULL Pattern 3 HEADLINE and ships
the public CUMUL-1.7 entry point `ConvCumul.subst_compatible`.

## Architecture: split across five files

The substantive work is decomposed by author/pattern:

* `Reduction/CumulCastElim.lean` — BHKM cast-elim primitives shared by
  both Benton (rename-side) and Allais (subst-side) per-ctor arms.

* `Reduction/CumulBenton.lean` — Benton-Hur-Kennedy-McBride JAR'12
  per-Term-ctor RENAME arms (Pattern 2).  ~32 helpers covering
  closed-payload, single-subterm, multi-subterm, binder, and eliminator
  ctors with `Term.rename`.

* `Reduction/CumulAllais.lean` — Allais et al. ICFP'18 per-Term-ctor
  SUBST arms (Pattern 3).  ~32 helpers covering the same ctor families
  with `Term.substHet` plus the `PointwiseCompat` predicate and
  combinators (refl / sym / trans).

* `Reduction/CumulPairedEnv.lean` — Pattern 3 paired-env infrastructure:
  `PointwiseCompatHomo` predicate at `ConvCumulHomo` level, the lift
  lemma for binder cases, the `Term.subst_compatible_pointwise_allais`
  fundamental lemma (Term-induction dispatching to per-arm helpers), and
  the identity-simulation headline
  `ConvCumul.subst_compatible_paired_allais`.

* `Reduction/CumulSubstCompat.lean` (this file) — the FULL HEADLINE
  `ConvCumulHomo.subst_compatible_paired_allais` (cumulRel induction
  over 26 ConvCumulHomo ctor cases) and the public CUMUL-1.7 entry
  point `ConvCumul.subst_compatible`, plus the HONEST STATUS docstring
  enumerating what is and is NOT shipped.

## Allais et al. (ICFP'18 / JFP'21) — paired-environment compat

**Source.** Allais, Atkey, Chapman, McBride, McKinna, *A Type and Scope
Safe Universe of Syntaxes with Binding*, ICFP'18 (arxiv:1804.00119).
See `Generic/Simulation.agda` in `gallais/generic-syntax`; FX memory
`reference_pattern_allais_simulation`.

The Allais simulation framework parameterises the substitution-respect
theorem over two relations: `𝓥ᴿ` on values, `𝓒ᴿ` on computations.  The
core construct is the paired-environment predicate `All 𝓥ᴿ Γ ρᴬ ρᴮ` —
pointwise relation across two distinct substitutions.  The simulation
theorem does structural recursion on the WELL-SCOPED TERM (homogeneous
in scope), with per-ctor obligations discharged via the user's
relations.

Specialized to FX: `TermSubstHet.PointwiseCompat termSubstA termSubstB`
(in `CumulAllais.lean`) is the FX instance of `All 𝓥ᴿ` for
`𝓥ᴿ = ConvCumul` on substituents at a shared `SubstHet sigma`.  The
homogeneous-level FULL HEADLINE
`ConvCumulHomo.subst_compatible_paired_allais` in this file lifts paired-
env Homo-compat through any `ConvCumulHomo` cumulRel.

## Benton-Hur-Kennedy-McBride (JAR'12) — single-substitution lift

**Source.** Benton, Hur, Kennedy, McBride, *Strongly Typed Term
Representations in Coq*, JAR 2012.  FX memory
`reference_pattern_bhkm_ladder`.

BHKM's renaming-first 4-lemma ladder (RcR / ScR / RcS / ScS) gives the
typed substitution-fusion infrastructure.  The conv-respect corollary
`ActScS_conv` lifts an existing `ConvCumul firstTerm secondTerm` through
a SINGLE `termSubst` to `ConvCumul (firstTerm.substHet termSubst)
(secondTerm.substHet termSubst)`.

The FX per-ctor catalogue (`Reduction/CumulBenton.lean`) supplies the
rename-side ladder used inside Pattern 3's binder-lift lemma in
`CumulPairedEnv.lean`.

## Sidesteps the Lean 4.29.1 walls

1. **Heterogeneous-induction wall** (`induction cumulRel` fails on
   indices that occur multiply): the FULL HEADLINE recurses on
   `ConvCumulHomo` (no viaUp ctor present).  All 26 ctor cases match
   canonically without index-unification problems.
2. **Dep-pattern matcher rejection** on `viaUp`'s lowerLevel ≠
   higherLevel: by construction `ConvCumulHomo` excludes `viaUp`, and
   the homogeneous-level restriction below ensures `cumulUpCong`
   produces the right ctxHigh level.
3. **WF-recursion propext**: the fundamental lemma uses structural
   recursion on Term (a Type-valued inductive), not WF on a Prop.

## Audit

Every shipped theorem in this file (and its sibling files
`CumulCastElim` / `CumulBenton` / `CumulAllais` / `CumulPairedEnv`) is
verified zero-axiom via `#print axioms` in
`Smoke/AuditCumulSubstCompat.lean`.
-/

namespace LeanFX2

/-! # Pattern 3 FULL HEADLINE — ConvCumulHomo + paired-env compat → ConvCumul

Restricted to homogeneous level (`sourceLevel = targetLevel = level`).
The level restriction is forced by `cumulUpCong`'s output ctxHigh
constraint: ConvCumul.cumulUpCong requires ctxHigh at exactly
`higherLevel.toNat + 1`, and after substHet the ctxHigh is at
targetLevel.  These coincide only when sourceLevel = targetLevel
(= higherLevel.toNat + 1 for the cumulUpCong ctor of ConvCumulHomo).

For homogeneous-level subst, this is the FULL Pattern 3 result —
all 26 ConvCumulHomo ctor cases discharged via outer cumulRel
induction with paired-env compat propagation. -/

/-- **Pattern 3 FULL HEADLINE** at homogeneous level: ConvCumulHomo
witnesses lift to ConvCumul under paired-env Homo-compat between
two TermSubstHets at the same homogeneous SubstHet.

Outer induction on cumulRel (ConvCumulHomo): 26 ctor cases.
* `refl t` → fundamental lemma on `t` with compat.
* `sym _ ih` → recurse with `compat.sym`, apply `ConvCumul.sym`.
* `trans _ _ ih1 ih2` → ih1 with compat to bridge through middle
  via σB, then ih2 with refl-compat at σB.
* 22 cong rules + cumulUpCong → recurse on inner subwitnesses
  with `compat` (or `compat.lift` for binders), apply matching
  ConvCumul cong rule with cast handling. -/
theorem ConvCumulHomo.subst_compatible_paired_allais
    {mode : Mode}
    {level : Nat} {sourceScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {firstType secondType : Ty level sourceScope}
    {firstRaw secondRaw : RawTerm sourceScope}
    {firstTerm : Term sourceCtx firstType firstRaw}
    {secondTerm : Term sourceCtx secondType secondRaw}
    (cumulRel : ConvCumulHomo firstTerm secondTerm) :
    ∀ {targetScope : Nat}
      {targetCtx : Ctx mode level targetScope}
      {sigma : SubstHet level level sourceScope targetScope}
      {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
      (_compat : TermSubstHet.PointwiseCompatHomo termSubstA termSubstB),
      ConvCumul (firstTerm.substHet termSubstA) (secondTerm.substHet termSubstB) := by
  induction cumulRel with
  | refl t =>
      intros _ _ _ _ _ compat
      exact Term.subst_compatible_pointwise_allais compat t
  | sym _ ih =>
      intros _ _ _ _ _ compat
      exact ConvCumul.sym (ih compat.sym)
  | trans _ _ ih1 ih2 =>
      intros _ _ _ _ _ compat
      exact ConvCumul.trans (ih1 compat) (ih2 (TermSubstHet.PointwiseCompatHomo.refl _))
  | lamCong _ ih =>
      intros _ _ _ _ _ compat
      exact ConvCumul.lamCong
        (ConvCumul.cast_eq_indep_benton _ _ (ih (compat.lift _)))
  | lamPiCong _ ih =>
      intros _ _ _ _ _ compat
      exact ConvCumul.lamPiCong (ih (compat.lift _))
  | appCong _ _ ihFn ihArg =>
      intros _ _ _ _ _ compat
      exact ConvCumul.appCong (ihFn compat) (ihArg compat)
  | appPiCong _ _ ihFn ihArg =>
      intros _ _ _ _ _ compat
      exact ConvCumul.cast_eq_indep_benton _ _
        (ConvCumul.appPiCong (ihFn compat) (ihArg compat))
  | pairCong _ _ ihFst ihSnd =>
      intros _ _ _ _ _ compat
      exact ConvCumul.pairCong (ihFst compat)
        (ConvCumul.cast_eq_indep_benton _ _ (ihSnd compat))
  | fstCong _ ih =>
      intros _ _ _ _ _ compat
      exact ConvCumul.fstCong (ih compat)
  | sndCong _ ih =>
      intros _ _ _ _ _ compat
      exact ConvCumul.cast_eq_indep_benton _ _ (ConvCumul.sndCong (ih compat))
  | natSuccCong _ ih =>
      intros _ _ _ _ _ compat
      exact ConvCumul.natSuccCong (ih compat)
  | optionSomeCong _ ih =>
      intros _ _ _ _ _ compat
      exact ConvCumul.optionSomeCong (ih compat)
  | eitherInlCong _ ih =>
      intros _ _ _ _ _ compat
      exact ConvCumul.eitherInlCong (ih compat)
  | eitherInrCong _ ih =>
      intros _ _ _ _ _ compat
      exact ConvCumul.eitherInrCong (ih compat)
  | modIntroCong _ ih =>
      intros _ _ _ _ _ compat
      exact ConvCumul.modIntroCong (ih compat)
  | modElimCong _ ih =>
      intros _ _ _ _ _ compat
      exact ConvCumul.modElimCong (ih compat)
  | subsumeCong _ ih =>
      intros _ _ _ _ _ compat
      exact ConvCumul.subsumeCong (ih compat)
  | listConsCong _ _ ihHead ihTail =>
      intros _ _ _ _ _ compat
      exact ConvCumul.listConsCong (ihHead compat) (ihTail compat)
  | idJCong _ _ ihBase ihWitness =>
      intros _ _ _ _ _ compat
      exact ConvCumul.idJCong (ihBase compat) (ihWitness compat)
  | boolElimCong _ _ _ ihScrut ihThen ihElse =>
      intros _ _ _ _ _ compat
      exact ConvCumul.boolElimCong (ihScrut compat) (ihThen compat) (ihElse compat)
  | natElimCong _ _ _ ihScrut ihZero ihSucc =>
      intros _ _ _ _ _ compat
      exact ConvCumul.natElimCong (ihScrut compat) (ihZero compat) (ihSucc compat)
  | natRecCong _ _ _ ihScrut ihZero ihSucc =>
      intros _ _ _ _ _ compat
      exact ConvCumul.natRecCong (ihScrut compat) (ihZero compat) (ihSucc compat)
  | listElimCong _ _ _ ihScrut ihNil ihCons =>
      intros _ _ _ _ _ compat
      exact ConvCumul.listElimCong (ihScrut compat) (ihNil compat) (ihCons compat)
  | optionMatchCong _ _ _ ihScrut ihNone ihSome =>
      intros _ _ _ _ _ compat
      exact ConvCumul.optionMatchCong (ihScrut compat) (ihNone compat) (ihSome compat)
  | eitherMatchCong _ _ _ ihScrut ihLeft ihRight =>
      intros _ _ _ _ _ compat
      exact ConvCumul.eitherMatchCong (ihScrut compat) (ihLeft compat) (ihRight compat)
  | cumulUpCong lowerLevel higherLevel cumulMonotone
                levelLeLow levelLeHigh _ ih =>
      intros _ _ _ _ _ compat
      -- Phase CUMUL-2.6 Design D: Term.substHet's cumulUp arm recurses
      -- on inner typeCode (single context throughout).  IH provides
      -- the substituted inner ConvCumul; cumulUpCong rebuilds at
      -- target ctx.  Homogeneous level: sigma is `SubstHet level level`
      -- so level witnesses transport via `Nat.le_refl`.
      have innerSubstd := ih compat
      exact ConvCumul.cumulUpCong lowerLevel higherLevel cumulMonotone
              levelLeLow levelLeHigh
              innerSubstd

/-! # `ConvCumul.subst_compatible`

`ConvCumulHomo` (homogeneous fragment, no `viaUp` ctor) is closed
under typed heterogeneous-scope substitution at homogeneous level:
applying a single `TermSubstHet sigma` to both sides of a homogeneous
ConvCumul relation yields a `ConvCumul`-related pair.

Body: `ConvCumulHomo.subst_compatible_paired_allais` (Pattern 3 /
Allais ICFP'18 paired-env simulation) instantiated at `refl`-compat
(sigma vs sigma).  The viaUp ctor is covered by separate shims in
`ConvCumulHomo.lean` (`ConvCumul.subst_compatible_viaUp`). -/
theorem ConvCumul.subst_compatible
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : SubstHet level level sourceScope targetScope}
    {firstType secondType : Ty level sourceScope}
    {firstRaw secondRaw : RawTerm sourceScope}
    {firstTerm : Term sourceCtx firstType firstRaw}
    {secondTerm : Term sourceCtx secondType secondRaw}
    (cumulRel : ConvCumulHomo firstTerm secondTerm)
    (termSubst : TermSubstHet sourceCtx targetCtx sigma) :
    ConvCumul (firstTerm.substHet termSubst) (secondTerm.substHet termSubst) :=
  ConvCumulHomo.subst_compatible_paired_allais cumulRel
    (TermSubstHet.PointwiseCompatHomo.refl termSubst)

/-! # HONEST STATUS — what is NOT shipped

This file is the substantive zero-axiom CATALOGUE of per-Term-ctor
helpers for both Pattern 2 (Benton single-rename) and Pattern 3
(Allais paired-env subst) styles.  But the RECURSIVE HEADLINES
that glue these per-arm helpers into uniform statements

```
∀ sourceTerm, ConvCumul (sourceTerm.substHet sigmaA)
                        (sourceTerm.substHet sigmaB)
```

```
∀ firstTerm secondTerm, ConvCumul firstTerm secondTerm →
    ConvCumul (firstTerm.substHet sigma) (secondTerm.substHet sigma)
```

are NOT SHIPPED.  Both hit the heterogeneous-Prop induction wall
in Lean 4.29.1: `induction cumulRel` and `cases cumulRel` both
fail at `viaUp` arm because viaUp's outputs sit at INDEPENDENT
`scopeLow` (decoupled from outer `scope` by Phase 12.A.B1.5).
The dep-pattern matcher cannot decide propositional
`lowerLevel = higherLevel` to unify viaUp at homogeneous levels,
so neither tactic-mode `induction`, term-mode `match`, nor
`recOn` with non-trivial motive succeeds.

A previous draft of this file shipped a `subst_compatible_joint`
theorem that was just `ConvCumul.trans` renamed — that was a
deception and has been removed.  Trans is already directly
available from `Reduction/Cumul.lean`; renaming it does not
constitute closing CUMUL-1.7.

## What this file genuinely ships (zero-axiom)

* 4 PointwiseCompat predicate + combinators
* 3 BHKM cast-elim primitives
* 27 per-Term-ctor Allais arms (subst-side, paired-env)
  including the lam + lamPi binder arms that take user-supplied
  body-level inner ConvCumul.
* 27 per-Term-ctor Benton arms (rename-side, single-rename)
  including lam + lamPi.
* 5 ConvCumul cong-rule eliminator arms — DEFERRED
  (kernel gap: ConvCumul lacks `natElimCong`, `natRecCong`,
  `listElimCong`, `optionMatchCong`, `eitherMatchCong`)

## What CUMUL-1.7 still needs

1. The general `subst_compatible_allais` recursive headline
   (structural recursion on sourceTerm, dispatching to the per-arm
   helpers; binder cases need `PointwiseCompat.lift`).
2. `PointwiseCompat.lift` itself — needs Pattern 2 weakening which
   hits the viaUp wall.
3. The general `subst_compatible_benton` recursive headline
   (structural recursion on cumulRel — directly walled).
4. Closing the 5 eliminator cong rules in `Reduction/Cumul.lean`.

The honest path forward, per memory
`reference_cumul_subst_pattern_decision`, is to either:
* Refine `ConvCumul` to constrain viaUp's scopeLow = scope
  (kernel modification; partial undo of Phase 12.A.B1.5 decoupling)
* Add a level-equating witness on viaUp (kernel modification)
* Accept the per-arm catalogue as the API for now and revisit
  the recursive headlines after future kernel work

CUMUL-1.7 PARENT TASK #1400 IS NOT YET CLOSED.  The per-arm
catalogue is real progress but not sufficient for closure. -/


end LeanFX2
