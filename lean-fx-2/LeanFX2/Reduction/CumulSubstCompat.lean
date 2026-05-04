import LeanFX2.Reduction.Cumul
import LeanFX2.Reduction.ConvCumulHomo
import LeanFX2.Term.Rename

/-! # Reduction/CumulSubstCompat — CUMUL-1.7 substitution-compatibility theorems

Two complementary substantive theorems for CUMUL-1.7, named by their
canonical authors in the type-theory literature.

## Architecture: two patterns, three theorems

The unified-substitution theorem `ConvCumul (firstTerm.substHet
sigmaA) (secondTerm.substHet sigmaB)` decomposes into two
INDEPENDENT lift principles, each documented in distinct prior art.

### Allais et al. (ICFP'18 / JFP'21) — paired-environment compat

**Source.** Allais, Atkey, Chapman, McBride, McKinna,
*A Type and Scope Safe Universe of Syntaxes with Binding*,
ICFP'18 (arxiv:1804.00119).  See `Generic/Simulation.agda` in
`gallais/generic-syntax`; FX memory
`reference_pattern_allais_simulation`.

The Allais simulation framework parameterises the substitution-
respect theorem over two relations: `𝓥ᴿ` on values, `𝓒ᴿ` on
computations.  The core construct is the paired-environment
predicate `All 𝓥ᴿ Γ ρᴬ ρᴮ` — pointwise relation across two
distinct substitutions.  The simulation theorem does structural
recursion on the WELL-SCOPED TERM (homogeneous in scope), with
per-ctor obligations discharged via the user's relations.

Specialized to FX: `TermSubstHet.PointwiseCompat termSubstA
termSubstB` is the FX instance of `All 𝓥ᴿ` for `𝓥ᴿ = ConvCumul`
on substituents at a shared `SubstHet sigma`.  The theorem
`ConvCumul.subst_compatible_allais` lifts pointwise compat to
ConvCumul on substituted Terms.

### Benton-Hur-Kennedy-McBride (JAR'12) — single-substitution lift

**Source.** Benton, Hur, Kennedy, McBride, *Strongly Typed Term
Representations in Coq*, JAR 2012.  FX memory
`reference_pattern_bhkm_ladder`.

BHKM's renaming-first 4-lemma ladder (RcR / ScR / RcS / ScS) gives
the typed substitution-fusion infrastructure.  The conv-respect
corollary `ActScS_conv` lifts an existing `ConvCumul firstTerm
secondTerm` through a SINGLE `termSubst` to `ConvCumul
(firstTerm.substHet termSubst) (secondTerm.substHet termSubst)`.

The FX instance: `ConvCumul.subst_compatible_benton`.  Distinct
from Allais's form because both sides share ONE termSubst, but the
two source Terms differ by an existing ConvCumul witness.

### Joint composition

Composing Allais and Benton via `ConvCumul.trans` yields the
strongest form — different SubstHets AND different Terms:
`ConvCumul.subst_compatible_joint`.

## Why two separate theorems

* Pure Allais form: useful when normalising / equating reducts of
  the SAME source Term under two compatible substitutions
  (typical in `subst_par_witnessed`-style chains).
* Pure Benton form: useful when an EXISTING `ConvCumul a b`
  needs to flow through a substitution boundary (typical in
  `ConvCumul.trans` chains across multiple subst hops).
* Merging would force callers to manufacture a trivial premise
  (refl-cumul or refl-compat).  Separate API entries cost
  nothing and read clearly.

## Sidesteps the Lean 4.29.1 walls

1. **Heterogeneous-induction wall** (`induction cumulRel` fails on
   indices that occur multiply): both theorems recurse on the
   source TERM (homogeneous within each ctor by construction),
   not on the ConvCumul Prop.
2. **Dep-pattern matcher rejection** on `viaUp`'s lowerLevel ≠
   higherLevel: both theorems constrain ctxs / scopes / levels
   to homogeneous, so viaUp is type-rejected — discharged by
   index unification, not by user dispatch.
3. **WF-recursion propext**: structural recursion on Term (a
   Type-valued inductive), not WF on a Prop.

## Sister theorem for cross-context viaUp

The heterogeneous-context viaUp case (where firstCtx ≠ secondCtx)
is the cumul-promotion boundary; covered by the existing
`ConvCumul.subst_compatible_outer` in `Reduction/Cumul.lean`.
Together with the Allais and Benton theorems below, all
ConvCumul shapes are covered at zero axioms.

## Audit gate

Every shipped theorem is verified zero-axiom via `#print axioms`
in `Smoke/AuditPhase12A2Cumul.lean`.
-/

namespace LeanFX2

/-! # Shared groundwork — BHKM-style cast-elim utilities

`Term.substHet`'s `lam` / `lamPi` / `pair` / `snd` / `appPi` arms
wrap the result in propositional `Ty.X_substHet_commute` casts.
Lifting cong rules through these casts requires the
transport-through-eq utility below: for any propositional type
equality `eq : ty1 = ty2`, `(eq ▸ term)` and `term` are
ConvCumul-related (heterogeneously, since their types differ).

This is BHKM JAR'12 p.17 `cast_elim_cong` adapted to FX's
heterogeneous `ConvCumul`.  Both the Allais arms (below) and the
Benton headline (further below) use these primitives.

Reference: Benton, Hur, Kennedy, McBride, *Strongly Typed Term
Representations in Coq*, JAR 2012 §6 (polymorphic case
discipline).  FX memory `reference_pattern_bhkm_ladder`. -/

/-- BHKM cast-elim left: a term and its left-side propositional
cast are ConvCumul-related.  FX analog of BHKM JAR'12 p.17
`cast_elim_cong`. -/
theorem ConvCumul.cast_eq_left_benton
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {someTyOne someTyTwo : Ty level scope}
    {someRaw : RawTerm scope}
    (eq : someTyOne = someTyTwo)
    (someTerm : Term context someTyOne someRaw) :
    ConvCumul (eq ▸ someTerm) someTerm := by
  cases eq
  exact ConvCumul.refl someTerm

/-- BHKM cast-elim right: symmetric to `cast_eq_left_benton`. -/
theorem ConvCumul.cast_eq_right_benton
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {someTyOne someTyTwo : Ty level scope}
    {someRaw : RawTerm scope}
    (eq : someTyOne = someTyTwo)
    (someTerm : Term context someTyOne someRaw) :
    ConvCumul someTerm (eq ▸ someTerm) := by
  cases eq
  exact ConvCumul.refl someTerm

/-- BHKM cast-elim both: when an existing ConvCumul is wrapped
identically on both sides by the same propositional cast, the
cast lifts through.  Used by Allais arms whose `Term.substHet`
output carries a `Ty.subst0_substHet_commute` cast (snd / pair /
appPi / lam / lamPi). -/
theorem ConvCumul.cast_eq_both_benton
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {someTyOne someTyTwo : Ty level scope}
    {firstRaw secondRaw : RawTerm scope}
    {firstTerm : Term context someTyOne firstRaw}
    {secondTerm : Term context someTyOne secondRaw}
    (eq : someTyOne = someTyTwo)
    (origRel : ConvCumul firstTerm secondTerm) :
    ConvCumul (eq ▸ firstTerm) (eq ▸ secondTerm) := by
  cases eq
  exact origRel

/-- BHKM cast-elim INDEPENDENT: each endpoint may carry its own
type-equation cast.  Used for cong cases where the two sides
involve different cast equations (e.g., `lamCong` with different
codomain types per side, `pairCong` / `sndCong` / `appPiCong`
with `Ty.subst0_substHet_commute` casts depending on per-side raw
witnesses). -/
theorem ConvCumul.cast_eq_indep_benton
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstTy firstTy' secondTy secondTy' : Ty level scope}
    {firstRaw secondRaw : RawTerm scope}
    {firstTerm : Term context firstTy firstRaw}
    {secondTerm : Term context secondTy secondRaw}
    (eqFirst : firstTy = firstTy')
    (eqSecond : secondTy = secondTy')
    (origRel : ConvCumul firstTerm secondTerm) :
    ConvCumul (eqFirst ▸ firstTerm) (eqSecond ▸ secondTerm) := by
  cases eqFirst
  cases eqSecond
  exact origRel

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

/-- Allais arm for `cumulUp`: closed cumul-promotion, refl. -/
theorem ConvCumul.subst_compatible_cumulUp_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    {scopeLow levelLow : Nat}
    (innerLevel lowerLevel higherLevel : UniverseLevel)
    (cumulOkLow : innerLevel.toNat ≤ lowerLevel.toNat)
    (cumulOkHigh : innerLevel.toNat ≤ higherLevel.toNat)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ levelLow)
    (levelLeHigh : higherLevel.toNat + 1 ≤ sourceLevel)
    {ctxLow : Ctx mode levelLow scopeLow}
    (lowerTerm :
      Term ctxLow (Ty.universe lowerLevel levelLeLow)
                  (RawTerm.universeCode innerLevel.toNat)) :
    ConvCumul ((Term.cumulUp (ctxHigh := sourceCtx)
                             innerLevel lowerLevel higherLevel
                             cumulOkLow cumulOkHigh cumulMonotone
                             levelLeLow levelLeHigh lowerTerm).substHet termSubstA)
              ((Term.cumulUp (ctxHigh := sourceCtx)
                             innerLevel lowerLevel higherLevel
                             cumulOkLow cumulOkHigh cumulMonotone
                             levelLeLow levelLeHigh lowerTerm).substHet termSubstB) :=
  ConvCumul.refl _

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

/-! # Benton-Hur-Kennedy-McBride JAR'12 — per-Term-ctor rename lift helpers

This section ships per-Term-ctor rename helpers that lift an inner
`ConvCumul` over RENAMED inner subterms to an outer `ConvCumul` over
RENAMED outer terms.  Each helper is a direct mirror of the
Allais arm structure above, but using `Term.rename` instead of
`Term.substHet`.

## Why per-ctor helpers and NOT a recursive headline

A recursive headline `ConvCumul.rename_compatible_benton` of the
shape

```
ConvCumul firstTerm secondTerm →
  ConvCumul (firstTerm.rename termRenaming) (secondTerm.rename termRenaming)
```

is GENUINELY UNSHIPPABLE at zero axioms in Lean 4.29.1.  The
architectural blocker:

* `ConvCumul.viaUp` introduces a Term at an INDEPENDENT lower
  scope `scopeLow` (not the outer scope being renamed).  The
  ctor's first index `lowerTerm : Term ctxLow ...` and second
  index `Term.cumulUp ... lowerTerm : Term ctxHigh ...` live at
  fundamentally different scopes/levels.

* When trying to "rename through outer scope" (a single
  `TermRenaming` for outer scope), the LHS `lowerTerm.rename _`
  is ill-typed because `termRenaming` is for outer scope and
  `lowerTerm` is at inner scope.

* Lean 4.29.1's `cases cumulRel` / `induction cumulRel` /
  term-mode `match cumulRel with | .viaUp ...` ALL hit the
  hard wall:

  ```
  Dependent elimination failed: Failed to solve equation
    lowerLevel.toNat = higherLevel.toNat
  ```

  Even in the homogeneous-source case (firstTerm and secondTerm
  at the same outer ctx/level/scope), Lean's matcher tries to
  unify viaUp's output indices and chokes on the propositional
  level constraint.  The constraint is REAL — viaUp could only
  match if `lowerLevel = higherLevel`, but Lean cannot reduce
  this propositionally without further hypotheses.

* `recOn` works in principle, but requires a UNIFORM motive
  across all ConvCumul ctors.  No such uniform motive exists for
  "rename through outer scope" because viaUp's `lowerTerm`
  cannot be renamed by the outer-scope termRenaming.

This wall is documented in `Reduction/Cumul.lean` §1097-1124 and
verified empirically (test cases in pre-commit working sketches).

## What we ship instead

The directive's HARD ESCAPE ROUTE: per-ctor helpers that take
ALREADY-RENAMED inner ConvCumul and produce RENAMED outer
ConvCumul.  Each helper has a real body using its inputs
substantively.  Downstream callers compose them as needed.

Reference: Benton, Hur, Kennedy, McBride, *Strongly Typed Term
Representations in Coq*, JAR 2012 §6 (the cong-by-cong
substitution-respect ladder).  FX memory
`reference_pattern_bhkm_ladder`.
-/

/-! ## Closed-payload rename arms (refl) -/

/-- Benton rename arm for `unit`: closed payload, refl. -/
theorem ConvCumul.rename_compatible_unit_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho) :
    ConvCumul ((Term.unit (context := sourceCtx)).rename termRenaming)
              ((Term.unit (context := sourceCtx)).rename termRenaming) :=
  ConvCumul.refl _

/-- Benton rename arm for `boolTrue`: closed payload, refl. -/
theorem ConvCumul.rename_compatible_boolTrue_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho) :
    ConvCumul ((Term.boolTrue (context := sourceCtx)).rename termRenaming)
              ((Term.boolTrue (context := sourceCtx)).rename termRenaming) :=
  ConvCumul.refl _

/-- Benton rename arm for `boolFalse`: closed payload, refl. -/
theorem ConvCumul.rename_compatible_boolFalse_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho) :
    ConvCumul ((Term.boolFalse (context := sourceCtx)).rename termRenaming)
              ((Term.boolFalse (context := sourceCtx)).rename termRenaming) :=
  ConvCumul.refl _

/-- Benton rename arm for `natZero`: closed payload, refl. -/
theorem ConvCumul.rename_compatible_natZero_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho) :
    ConvCumul ((Term.natZero (context := sourceCtx)).rename termRenaming)
              ((Term.natZero (context := sourceCtx)).rename termRenaming) :=
  ConvCumul.refl _

/-- Benton rename arm for `var`: both sides rename to the same Term
(single termRenaming applied to both — identical result), refl. -/
theorem ConvCumul.rename_compatible_var_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (position : Fin sourceScope) :
    ConvCumul ((Term.var (context := sourceCtx) position).rename termRenaming)
              ((Term.var (context := sourceCtx) position).rename termRenaming) :=
  ConvCumul.refl _

/-- Benton rename arm for `universeCode`: closed payload, refl. -/
theorem ConvCumul.rename_compatible_universeCode_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    ConvCumul ((Term.universeCode (context := sourceCtx)
                                  innerLevel outerLevel cumulOk levelLe).rename termRenaming)
              ((Term.universeCode (context := sourceCtx)
                                  innerLevel outerLevel cumulOk levelLe).rename termRenaming) :=
  ConvCumul.refl _

/-- Benton rename arm for `listNil`: closed payload, refl. -/
theorem ConvCumul.rename_compatible_listNil_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (elementType : Ty level sourceScope) :
    ConvCumul ((Term.listNil (context := sourceCtx)
                             (elementType := elementType)).rename termRenaming)
              ((Term.listNil (context := sourceCtx)
                             (elementType := elementType)).rename termRenaming) :=
  ConvCumul.refl _

/-- Benton rename arm for `optionNone`: closed payload, refl. -/
theorem ConvCumul.rename_compatible_optionNone_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (elementType : Ty level sourceScope) :
    ConvCumul ((Term.optionNone (context := sourceCtx)
                                (elementType := elementType)).rename termRenaming)
              ((Term.optionNone (context := sourceCtx)
                                (elementType := elementType)).rename termRenaming) :=
  ConvCumul.refl _

/-- Benton rename arm for `refl` (identity-type witness): closed
payload, refl. -/
theorem ConvCumul.rename_compatible_refl_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (carrier : Ty level sourceScope)
    (rawWitness : RawTerm sourceScope) :
    ConvCumul ((Term.refl (context := sourceCtx) carrier rawWitness).rename termRenaming)
              ((Term.refl (context := sourceCtx) carrier rawWitness).rename termRenaming) :=
  ConvCumul.refl _

/-- Benton rename arm for `cumulUp`: lower term passed unchanged
through Term.rename (lowerTerm's scope is independent), refl. -/
theorem ConvCumul.rename_compatible_cumulUp_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {scopeLow levelLow : Nat}
    (innerLevel lowerLevel higherLevel : UniverseLevel)
    (cumulOkLow : innerLevel.toNat ≤ lowerLevel.toNat)
    (cumulOkHigh : innerLevel.toNat ≤ higherLevel.toNat)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ levelLow)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {ctxLow : Ctx mode levelLow scopeLow}
    (lowerTerm :
      Term ctxLow (Ty.universe lowerLevel levelLeLow)
                  (RawTerm.universeCode innerLevel.toNat)) :
    ConvCumul ((Term.cumulUp (ctxHigh := sourceCtx)
                             innerLevel lowerLevel higherLevel
                             cumulOkLow cumulOkHigh cumulMonotone
                             levelLeLow levelLeHigh lowerTerm).rename termRenaming)
              ((Term.cumulUp (ctxHigh := sourceCtx)
                             innerLevel lowerLevel higherLevel
                             cumulOkLow cumulOkHigh cumulMonotone
                             levelLeLow levelLeHigh lowerTerm).rename termRenaming) :=
  ConvCumul.refl _

/-! ## Single-subterm cong rename arms

Each takes an already-renamed inner ConvCumul on the substituent
subterm and produces the renamed outer ConvCumul via the matching
cong rule. -/

/-- Benton rename arm for `natSucc`: single-subterm cong via `natSuccCong`. -/
theorem ConvCumul.rename_compatible_natSucc_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {predecessorRawFirst predecessorRawSecond : RawTerm sourceScope}
    {predecessorFirst : Term sourceCtx Ty.nat predecessorRawFirst}
    {predecessorSecond : Term sourceCtx Ty.nat predecessorRawSecond}
    (predecessorRel :
      ConvCumul (predecessorFirst.rename termRenaming)
                (predecessorSecond.rename termRenaming)) :
    ConvCumul ((Term.natSucc predecessorFirst).rename termRenaming)
              ((Term.natSucc predecessorSecond).rename termRenaming) :=
  ConvCumul.natSuccCong predecessorRel

/-- Benton rename arm for `optionSome`: single-subterm cong via `optionSomeCong`. -/
theorem ConvCumul.rename_compatible_optionSome_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {elementType : Ty level sourceScope}
    {valueRawFirst valueRawSecond : RawTerm sourceScope}
    {valueFirst : Term sourceCtx elementType valueRawFirst}
    {valueSecond : Term sourceCtx elementType valueRawSecond}
    (valueRel :
      ConvCumul (valueFirst.rename termRenaming)
                (valueSecond.rename termRenaming)) :
    ConvCumul ((Term.optionSome valueFirst).rename termRenaming)
              ((Term.optionSome valueSecond).rename termRenaming) :=
  ConvCumul.optionSomeCong valueRel

/-- Benton rename arm for `eitherInl`: single-subterm cong via `eitherInlCong`. -/
theorem ConvCumul.rename_compatible_eitherInl_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {leftType rightType : Ty level sourceScope}
    {valueRawFirst valueRawSecond : RawTerm sourceScope}
    {valueFirst : Term sourceCtx leftType valueRawFirst}
    {valueSecond : Term sourceCtx leftType valueRawSecond}
    (valueRel :
      ConvCumul (valueFirst.rename termRenaming)
                (valueSecond.rename termRenaming)) :
    ConvCumul ((Term.eitherInl (rightType := rightType) valueFirst).rename termRenaming)
              ((Term.eitherInl (rightType := rightType) valueSecond).rename termRenaming) :=
  ConvCumul.eitherInlCong valueRel

/-- Benton rename arm for `eitherInr`: single-subterm cong via `eitherInrCong`. -/
theorem ConvCumul.rename_compatible_eitherInr_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {leftType rightType : Ty level sourceScope}
    {valueRawFirst valueRawSecond : RawTerm sourceScope}
    {valueFirst : Term sourceCtx rightType valueRawFirst}
    {valueSecond : Term sourceCtx rightType valueRawSecond}
    (valueRel :
      ConvCumul (valueFirst.rename termRenaming)
                (valueSecond.rename termRenaming)) :
    ConvCumul ((Term.eitherInr (leftType := leftType) valueFirst).rename termRenaming)
              ((Term.eitherInr (leftType := leftType) valueSecond).rename termRenaming) :=
  ConvCumul.eitherInrCong valueRel

/-- Benton rename arm for `modIntro`: single-subterm cong via `modIntroCong`. -/
theorem ConvCumul.rename_compatible_modIntro_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {innerType : Ty level sourceScope}
    {innerRawFirst innerRawSecond : RawTerm sourceScope}
    {innerFirst : Term sourceCtx innerType innerRawFirst}
    {innerSecond : Term sourceCtx innerType innerRawSecond}
    (innerRel :
      ConvCumul (innerFirst.rename termRenaming)
                (innerSecond.rename termRenaming)) :
    ConvCumul ((Term.modIntro innerFirst).rename termRenaming)
              ((Term.modIntro innerSecond).rename termRenaming) :=
  ConvCumul.modIntroCong innerRel

/-- Benton rename arm for `modElim`: single-subterm cong via `modElimCong`. -/
theorem ConvCumul.rename_compatible_modElim_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {innerType : Ty level sourceScope}
    {innerRawFirst innerRawSecond : RawTerm sourceScope}
    {innerFirst : Term sourceCtx innerType innerRawFirst}
    {innerSecond : Term sourceCtx innerType innerRawSecond}
    (innerRel :
      ConvCumul (innerFirst.rename termRenaming)
                (innerSecond.rename termRenaming)) :
    ConvCumul ((Term.modElim innerFirst).rename termRenaming)
              ((Term.modElim innerSecond).rename termRenaming) :=
  ConvCumul.modElimCong innerRel

/-- Benton rename arm for `subsume`: single-subterm cong via `subsumeCong`. -/
theorem ConvCumul.rename_compatible_subsume_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {innerType : Ty level sourceScope}
    {innerRawFirst innerRawSecond : RawTerm sourceScope}
    {innerFirst : Term sourceCtx innerType innerRawFirst}
    {innerSecond : Term sourceCtx innerType innerRawSecond}
    (innerRel :
      ConvCumul (innerFirst.rename termRenaming)
                (innerSecond.rename termRenaming)) :
    ConvCumul ((Term.subsume innerFirst).rename termRenaming)
              ((Term.subsume innerSecond).rename termRenaming) :=
  ConvCumul.subsumeCong innerRel

/-- Benton rename arm for `fst`: single-subterm cong via `fstCong`. -/
theorem ConvCumul.rename_compatible_fst_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRawFirst pairRawSecond : RawTerm sourceScope}
    {pairFirst : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRawFirst}
    {pairSecond : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRawSecond}
    (pairRel :
      ConvCumul (pairFirst.rename termRenaming)
                (pairSecond.rename termRenaming)) :
    ConvCumul ((Term.fst pairFirst).rename termRenaming)
              ((Term.fst pairSecond).rename termRenaming) :=
  ConvCumul.fstCong pairRel

/-- Benton rename arm for `snd`: single-subterm cong via `sndCong`
plus BHKM cast handling.

`Term.rename`'s `snd` arm wraps the result in
`(Ty.subst0_rename_commute ...).symm ▸ Term.snd (...)`.  The casts
on the two sides DIFFER (different pairRaws → different
`RawTerm.fst` projections), so we use `cast_eq_left_benton` for
LHS and `cast_eq_right_benton` for RHS chained with `sndCong`. -/
theorem ConvCumul.rename_compatible_snd_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRawFirst pairRawSecond : RawTerm sourceScope}
    {pairFirst : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRawFirst}
    {pairSecond : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRawSecond}
    (pairRel :
      ConvCumul (pairFirst.rename termRenaming)
                (pairSecond.rename termRenaming)) :
    ConvCumul ((Term.snd pairFirst).rename termRenaming)
              ((Term.snd pairSecond).rename termRenaming) :=
  ConvCumul.trans (ConvCumul.cast_eq_left_benton _ _)
    (ConvCumul.trans (ConvCumul.sndCong pairRel)
                     (ConvCumul.cast_eq_right_benton _ _))

/-! ## Multi-subterm cong rename arms -/

/-- Benton rename arm for `app`: two-subterm cong via `appCong`. -/
theorem ConvCumul.rename_compatible_app_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {domainType codomainType : Ty level sourceScope}
    {functionRawFirst functionRawSecond argumentRawFirst argumentRawSecond :
      RawTerm sourceScope}
    {functionFirst :
      Term sourceCtx (Ty.arrow domainType codomainType) functionRawFirst}
    {functionSecond :
      Term sourceCtx (Ty.arrow domainType codomainType) functionRawSecond}
    {argumentFirst : Term sourceCtx domainType argumentRawFirst}
    {argumentSecond : Term sourceCtx domainType argumentRawSecond}
    (functionRel :
      ConvCumul (functionFirst.rename termRenaming)
                (functionSecond.rename termRenaming))
    (argumentRel :
      ConvCumul (argumentFirst.rename termRenaming)
                (argumentSecond.rename termRenaming)) :
    ConvCumul ((Term.app functionFirst argumentFirst).rename termRenaming)
              ((Term.app functionSecond argumentSecond).rename termRenaming) :=
  ConvCumul.appCong functionRel argumentRel

/-- Benton rename arm for `appPi`: two-subterm cong via `appPiCong` plus
BHKM cast handling.

`Term.rename`'s `appPi` arm wraps the result in
`(Ty.subst0_rename_commute ...).symm ▸ Term.appPi ...`.  The
casts on the two sides differ (different argumentRaws), so we
chain `cast_eq_left_benton`, `appPiCong`, `cast_eq_right_benton`. -/
theorem ConvCumul.rename_compatible_appPi_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {functionRawFirst functionRawSecond argumentRawFirst argumentRawSecond :
      RawTerm sourceScope}
    {functionFirst :
      Term sourceCtx (Ty.piTy domainType codomainType) functionRawFirst}
    {functionSecond :
      Term sourceCtx (Ty.piTy domainType codomainType) functionRawSecond}
    {argumentFirst : Term sourceCtx domainType argumentRawFirst}
    {argumentSecond : Term sourceCtx domainType argumentRawSecond}
    (functionRel :
      ConvCumul (functionFirst.rename termRenaming)
                (functionSecond.rename termRenaming))
    (argumentRel :
      ConvCumul (argumentFirst.rename termRenaming)
                (argumentSecond.rename termRenaming)) :
    ConvCumul ((Term.appPi functionFirst argumentFirst).rename termRenaming)
              ((Term.appPi functionSecond argumentSecond).rename termRenaming) :=
  ConvCumul.trans (ConvCumul.cast_eq_left_benton _ _)
    (ConvCumul.trans (ConvCumul.appPiCong functionRel argumentRel)
                     (ConvCumul.cast_eq_right_benton _ _))

/-- Benton rename arm for `pair`: two-subterm cong via `pairCong` plus
BHKM cast handling on the second component.

`Term.rename`'s `pair` arm wraps the second component in
`Ty.subst0_rename_commute ... ▸ ...`.  The casts on the two
sides differ (firstRawFirst vs firstRawSecond), so we apply
`cast_eq_left_benton` to LHS and `cast_eq_right_benton` to RHS,
chained via `ConvCumul.trans`. -/
theorem ConvCumul.rename_compatible_pair_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {firstRawFirst firstRawSecond secondRawFirst secondRawSecond :
      RawTerm sourceScope}
    {firstValueFirst : Term sourceCtx firstType firstRawFirst}
    {firstValueSecond : Term sourceCtx firstType firstRawSecond}
    {secondValueFirst :
      Term sourceCtx (secondType.subst0 firstType firstRawFirst) secondRawFirst}
    {secondValueSecond :
      Term sourceCtx (secondType.subst0 firstType firstRawSecond) secondRawSecond}
    (firstRel :
      ConvCumul (firstValueFirst.rename termRenaming)
                (firstValueSecond.rename termRenaming))
    (secondRel :
      ConvCumul (secondValueFirst.rename termRenaming)
                (secondValueSecond.rename termRenaming)) :
    ConvCumul ((Term.pair firstValueFirst secondValueFirst).rename termRenaming)
              ((Term.pair firstValueSecond secondValueSecond).rename termRenaming) :=
  ConvCumul.pairCong firstRel
    (ConvCumul.trans (ConvCumul.cast_eq_left_benton _ _)
       (ConvCumul.trans secondRel
                        (ConvCumul.cast_eq_right_benton _ _)))

/-- Benton rename arm for `listCons`: two-subterm cong via `listConsCong`. -/
theorem ConvCumul.rename_compatible_listCons_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {elementType : Ty level sourceScope}
    {headRawFirst headRawSecond tailRawFirst tailRawSecond : RawTerm sourceScope}
    {headFirst : Term sourceCtx elementType headRawFirst}
    {headSecond : Term sourceCtx elementType headRawSecond}
    {tailFirst : Term sourceCtx (Ty.listType elementType) tailRawFirst}
    {tailSecond : Term sourceCtx (Ty.listType elementType) tailRawSecond}
    (headRel :
      ConvCumul (headFirst.rename termRenaming)
                (headSecond.rename termRenaming))
    (tailRel :
      ConvCumul (tailFirst.rename termRenaming)
                (tailSecond.rename termRenaming)) :
    ConvCumul ((Term.listCons headFirst tailFirst).rename termRenaming)
              ((Term.listCons headSecond tailSecond).rename termRenaming) :=
  ConvCumul.listConsCong headRel tailRel

/-- Benton rename arm for `idJ`: two-subterm cong via `idJCong`. -/
theorem ConvCumul.rename_compatible_idJ_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRawFirst baseRawSecond witnessRawFirst witnessRawSecond :
      RawTerm sourceScope}
    {baseFirst : Term sourceCtx motiveType baseRawFirst}
    {baseSecond : Term sourceCtx motiveType baseRawSecond}
    {witnessFirst :
      Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRawFirst}
    {witnessSecond :
      Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRawSecond}
    (baseRel :
      ConvCumul (baseFirst.rename termRenaming)
                (baseSecond.rename termRenaming))
    (witnessRel :
      ConvCumul (witnessFirst.rename termRenaming)
                (witnessSecond.rename termRenaming)) :
    ConvCumul ((Term.idJ baseFirst witnessFirst).rename termRenaming)
              ((Term.idJ baseSecond witnessSecond).rename termRenaming) :=
  ConvCumul.idJCong baseRel witnessRel

/-- Benton rename arm for `boolElim`: three-subterm cong via `boolElimCong`. -/
theorem ConvCumul.rename_compatible_boolElim_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {motiveType : Ty level sourceScope}
    {scrutineeRawFirst scrutineeRawSecond
     thenRawFirst thenRawSecond elseRawFirst elseRawSecond : RawTerm sourceScope}
    {scrutineeFirst : Term sourceCtx Ty.bool scrutineeRawFirst}
    {scrutineeSecond : Term sourceCtx Ty.bool scrutineeRawSecond}
    {thenBranchFirst : Term sourceCtx motiveType thenRawFirst}
    {thenBranchSecond : Term sourceCtx motiveType thenRawSecond}
    {elseBranchFirst : Term sourceCtx motiveType elseRawFirst}
    {elseBranchSecond : Term sourceCtx motiveType elseRawSecond}
    (scrutineeRel :
      ConvCumul (scrutineeFirst.rename termRenaming)
                (scrutineeSecond.rename termRenaming))
    (thenRel :
      ConvCumul (thenBranchFirst.rename termRenaming)
                (thenBranchSecond.rename termRenaming))
    (elseRel :
      ConvCumul (elseBranchFirst.rename termRenaming)
                (elseBranchSecond.rename termRenaming)) :
    ConvCumul (Term.rename termRenaming
                 (Term.boolElim scrutineeFirst thenBranchFirst elseBranchFirst))
              (Term.rename termRenaming
                 (Term.boolElim scrutineeSecond thenBranchSecond elseBranchSecond)) :=
  ConvCumul.boolElimCong scrutineeRel thenRel elseRel

/-! ## Binder cong rename arms

The binder cases (`lam` / `lamPi`) require a LIFTED termRenaming in
the body's recursive call.  `Term.rename`'s `lam` arm wraps the
body in `Ty.weaken_rename_commute ▸ Term.rename termRenaming.lift body`,
so the inner ConvCumul must already be on body terms renamed by
`termRenaming.lift _`.  `cast_eq_both_benton` peels the cast
identically across the two sides. -/

/-- Benton rename arm for `lam`: binder cong via `lamCong` plus BHKM
cast handling.

`Term.rename`'s `lam` arm produces
`Term.lam (Ty.weaken_rename_commute ... ▸ body.rename (termRenaming.lift _))`.
The cast `Ty.weaken_rename_commute ...` is propositional, identical
on both sides, peeled via `cast_eq_both_benton`. -/
theorem ConvCumul.rename_compatible_lam_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {domainType codomainType : Ty level sourceScope}
    {bodyRawFirst bodyRawSecond : RawTerm (sourceScope + 1)}
    {bodyFirst : Term (sourceCtx.cons domainType) codomainType.weaken bodyRawFirst}
    {bodySecond : Term (sourceCtx.cons domainType) codomainType.weaken bodyRawSecond}
    (bodyRel :
      ConvCumul (bodyFirst.rename (termRenaming.lift domainType))
                (bodySecond.rename (termRenaming.lift domainType))) :
    ConvCumul ((Term.lam bodyFirst).rename termRenaming)
              ((Term.lam bodySecond).rename termRenaming) :=
  ConvCumul.lamCong (ConvCumul.cast_eq_both_benton _ bodyRel)

/-- Benton rename arm for `lamPi`: binder cong via `lamPiCong`.

`Term.rename`'s `lamPi` arm has NO cast (body type is just
codomainType in extended scope).  Direct cong application. -/
theorem ConvCumul.rename_compatible_lamPi_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {bodyRawFirst bodyRawSecond : RawTerm (sourceScope + 1)}
    {bodyFirst : Term (sourceCtx.cons domainType) codomainType bodyRawFirst}
    {bodySecond : Term (sourceCtx.cons domainType) codomainType bodyRawSecond}
    (bodyRel :
      ConvCumul (bodyFirst.rename (termRenaming.lift domainType))
                (bodySecond.rename (termRenaming.lift domainType))) :
    ConvCumul ((Term.lamPi bodyFirst).rename termRenaming)
              ((Term.lamPi bodySecond).rename termRenaming) :=
  ConvCumul.lamPiCong bodyRel

/-! ## Kernel-gap eliminator arms — DEFERRED

The 5 eliminator constructors (`natElim`, `natRec`, `listElim`,
`optionMatch`, `eitherMatch`) lack `ConvCumul` cong rules in the
current kernel (`Reduction/Cumul.lean`).  Without these cong
rules, the rename helpers for these ctors cannot be constructed.

Adding the 5 missing cong rules would extend `ConvCumul` with
standard 3-subterm cong rules mirroring `boolElimCong`'s shape.
This is a kernel modification deferred to a future commit; the
present commit ships only the 22 ctors that have existing cong
rules.

Same kernel gap is documented in the Allais arms section above
(near line 766).
-/

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

/-! ## Benton eliminator rename arms (5) -/

/-- Benton rename arm for `natElim`: three-subterm cong via `natElimCong`. -/
theorem ConvCumul.rename_compatible_natElim_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {motiveType : Ty level sourceScope}
    {scrutFirstRaw scrutSecondRaw zeroFirstRaw zeroSecondRaw
     succFirstRaw succSecondRaw : RawTerm sourceScope}
    {scrutFirst : Term sourceCtx Ty.nat scrutFirstRaw}
    {scrutSecond : Term sourceCtx Ty.nat scrutSecondRaw}
    {zeroFirst : Term sourceCtx motiveType zeroFirstRaw}
    {zeroSecond : Term sourceCtx motiveType zeroSecondRaw}
    {succFirst : Term sourceCtx (Ty.arrow Ty.nat motiveType) succFirstRaw}
    {succSecond : Term sourceCtx (Ty.arrow Ty.nat motiveType) succSecondRaw}
    (scrutRel :
      ConvCumul (scrutFirst.rename termRenaming) (scrutSecond.rename termRenaming))
    (zeroRel :
      ConvCumul (zeroFirst.rename termRenaming) (zeroSecond.rename termRenaming))
    (succRel :
      ConvCumul (succFirst.rename termRenaming) (succSecond.rename termRenaming)) :
    ConvCumul ((Term.natElim scrutFirst zeroFirst succFirst).rename termRenaming)
              ((Term.natElim scrutSecond zeroSecond succSecond).rename termRenaming) :=
  ConvCumul.natElimCong scrutRel zeroRel succRel

/-- Benton rename arm for `natRec`: three-subterm cong via `natRecCong`. -/
theorem ConvCumul.rename_compatible_natRec_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {motiveType : Ty level sourceScope}
    {scrutFirstRaw scrutSecondRaw zeroFirstRaw zeroSecondRaw
     succFirstRaw succSecondRaw : RawTerm sourceScope}
    {scrutFirst : Term sourceCtx Ty.nat scrutFirstRaw}
    {scrutSecond : Term sourceCtx Ty.nat scrutSecondRaw}
    {zeroFirst : Term sourceCtx motiveType zeroFirstRaw}
    {zeroSecond : Term sourceCtx motiveType zeroSecondRaw}
    {succFirst :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succFirstRaw}
    {succSecond :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succSecondRaw}
    (scrutRel :
      ConvCumul (scrutFirst.rename termRenaming) (scrutSecond.rename termRenaming))
    (zeroRel :
      ConvCumul (zeroFirst.rename termRenaming) (zeroSecond.rename termRenaming))
    (succRel :
      ConvCumul (succFirst.rename termRenaming) (succSecond.rename termRenaming)) :
    ConvCumul ((Term.natRec scrutFirst zeroFirst succFirst).rename termRenaming)
              ((Term.natRec scrutSecond zeroSecond succSecond).rename termRenaming) :=
  ConvCumul.natRecCong scrutRel zeroRel succRel

/-- Benton rename arm for `listElim`: three-subterm cong via `listElimCong`. -/
theorem ConvCumul.rename_compatible_listElim_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {elementType motiveType : Ty level sourceScope}
    {scrutFirstRaw scrutSecondRaw nilFirstRaw nilSecondRaw
     consFirstRaw consSecondRaw : RawTerm sourceScope}
    {scrutFirst : Term sourceCtx (Ty.listType elementType) scrutFirstRaw}
    {scrutSecond : Term sourceCtx (Ty.listType elementType) scrutSecondRaw}
    {nilFirst : Term sourceCtx motiveType nilFirstRaw}
    {nilSecond : Term sourceCtx motiveType nilSecondRaw}
    {consFirst :
      Term sourceCtx (Ty.arrow elementType
                       (Ty.arrow (Ty.listType elementType) motiveType)) consFirstRaw}
    {consSecond :
      Term sourceCtx (Ty.arrow elementType
                       (Ty.arrow (Ty.listType elementType) motiveType)) consSecondRaw}
    (scrutRel :
      ConvCumul (scrutFirst.rename termRenaming) (scrutSecond.rename termRenaming))
    (nilRel :
      ConvCumul (nilFirst.rename termRenaming) (nilSecond.rename termRenaming))
    (consRel :
      ConvCumul (consFirst.rename termRenaming) (consSecond.rename termRenaming)) :
    ConvCumul ((Term.listElim scrutFirst nilFirst consFirst).rename termRenaming)
              ((Term.listElim scrutSecond nilSecond consSecond).rename termRenaming) :=
  ConvCumul.listElimCong scrutRel nilRel consRel

/-- Benton rename arm for `optionMatch`: three-subterm cong via `optionMatchCong`. -/
theorem ConvCumul.rename_compatible_optionMatch_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {elementType motiveType : Ty level sourceScope}
    {scrutFirstRaw scrutSecondRaw noneFirstRaw noneSecondRaw
     someFirstRaw someSecondRaw : RawTerm sourceScope}
    {scrutFirst : Term sourceCtx (Ty.optionType elementType) scrutFirstRaw}
    {scrutSecond : Term sourceCtx (Ty.optionType elementType) scrutSecondRaw}
    {noneFirst : Term sourceCtx motiveType noneFirstRaw}
    {noneSecond : Term sourceCtx motiveType noneSecondRaw}
    {someFirst : Term sourceCtx (Ty.arrow elementType motiveType) someFirstRaw}
    {someSecond : Term sourceCtx (Ty.arrow elementType motiveType) someSecondRaw}
    (scrutRel :
      ConvCumul (scrutFirst.rename termRenaming) (scrutSecond.rename termRenaming))
    (noneRel :
      ConvCumul (noneFirst.rename termRenaming) (noneSecond.rename termRenaming))
    (someRel :
      ConvCumul (someFirst.rename termRenaming) (someSecond.rename termRenaming)) :
    ConvCumul
      ((Term.optionMatch scrutFirst noneFirst someFirst).rename termRenaming)
      ((Term.optionMatch scrutSecond noneSecond someSecond).rename termRenaming) :=
  ConvCumul.optionMatchCong scrutRel noneRel someRel

/-- Benton rename arm for `eitherMatch`: three-subterm cong via `eitherMatchCong`. -/
theorem ConvCumul.rename_compatible_eitherMatch_benton
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    {termRenaming : TermRenaming sourceCtx targetCtx rho}
    {leftType rightType motiveType : Ty level sourceScope}
    {scrutFirstRaw scrutSecondRaw leftFirstRaw leftSecondRaw
     rightFirstRaw rightSecondRaw : RawTerm sourceScope}
    {scrutFirst : Term sourceCtx (Ty.eitherType leftType rightType) scrutFirstRaw}
    {scrutSecond : Term sourceCtx (Ty.eitherType leftType rightType) scrutSecondRaw}
    {leftFirst : Term sourceCtx (Ty.arrow leftType motiveType) leftFirstRaw}
    {leftSecond : Term sourceCtx (Ty.arrow leftType motiveType) leftSecondRaw}
    {rightFirst : Term sourceCtx (Ty.arrow rightType motiveType) rightFirstRaw}
    {rightSecond : Term sourceCtx (Ty.arrow rightType motiveType) rightSecondRaw}
    (scrutRel :
      ConvCumul (scrutFirst.rename termRenaming) (scrutSecond.rename termRenaming))
    (leftRel :
      ConvCumul (leftFirst.rename termRenaming) (leftSecond.rename termRenaming))
    (rightRel :
      ConvCumul (rightFirst.rename termRenaming) (rightSecond.rename termRenaming)) :
    ConvCumul
      ((Term.eitherMatch scrutFirst leftFirst rightFirst).rename termRenaming)
      ((Term.eitherMatch scrutSecond leftSecond rightSecond).rename termRenaming) :=
  ConvCumul.eitherMatchCong scrutRel leftRel rightRel

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
  | _, _, .cumulUp innerLevel lowerLevel higherLevel
                   cumulOkLow cumulOkHigh cumulMonotone
                   levelLeLow levelLeHigh lowerTerm =>
      ConvCumul.subst_compatible_cumulUp_allais _ _
        innerLevel lowerLevel higherLevel
        cumulOkLow cumulOkHigh cumulMonotone
        levelLeLow levelLeHigh lowerTerm
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
  | cumulUpCong innerLevel lowerLevel higherLevel
                cumulOkLow cumulOkHigh cumulMonotone lowerRel =>
      intros _ _ _ _ _ _compat
      -- substHet on Term.cumulUp: lowerTerm preserved verbatim, ctxHigh
      -- moves from sourceCtx to targetCtx.  Both sides at same targetCtx.
      -- ConvCumul.cumulUpCong applied to original lowerRel produces the
      -- result.  At homogeneous level, the ctxHigh-level constraint
      -- coincides (both at higherLevel.toNat + 1 = level).
      -- compat unused: the lowerRel inhabits a separate ConvCumul at
      -- decoupled scopeLow, untouched by the outer paired-env compat.
      exact ConvCumul.cumulUpCong innerLevel lowerLevel higherLevel
              cumulOkLow cumulOkHigh cumulMonotone lowerRel

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
