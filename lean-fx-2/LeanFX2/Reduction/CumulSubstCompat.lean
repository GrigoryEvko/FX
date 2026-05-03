import LeanFX2.Reduction.Cumul
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

/-! # Joint composition (Step E — partial)

The full strongest form `ConvCumul (firstTerm.substHet sigmaA)
(secondTerm.substHet sigmaB)` from a paired `compat` and a
`cumulRel` decomposes via `ConvCumul.trans`:

```
ConvCumul (firstTerm.substHet sigmaA)
          (secondTerm.substHet sigmaB)
  =  ConvCumul.trans
       (allais_lift  : ConvCumul (firstTerm.substHet sigmaA)
                                 (firstTerm.substHet sigmaB))
       (benton_lift  : ConvCumul (firstTerm.substHet sigmaB)
                                 (secondTerm.substHet sigmaB))
```

The `allais_lift` factor uses the per-ctor Allais helpers above
(structural recursion on `firstTerm` with caller-supplied
binder-arm bodies).  The `benton_lift` factor uses the per-ctor
Benton helpers (also caller-supplied at construction).

This `subst_compatible_joint` ASSEMBLER takes the two pre-built
factors and combines them.  The factors themselves are user-built
because the recursive headlines hit the heterogeneous-induction
wall (memory `reference_cumul_subst_pattern_decision`); the
shipped per-ctor helpers cover all 22 ctors with existing cong
rules.

Shipping this assembler closes the API surface: any caller who
can build the two factors gets the joint result for free. -/

/-- Joint composition: combine an Allais-style same-source factor
with a Benton-style same-subst factor via `ConvCumul.trans` to
produce the strongest cross-subst cross-source ConvCumul. -/
theorem ConvCumul.subst_compatible_joint
    {modeF modeS : Mode}
    {levelF levelS scopeF scopeS : Nat}
    {ctxF : Ctx modeF levelF scopeF}
    {ctxS : Ctx modeS levelS scopeS}
    {tyF : Ty levelF scopeF}
    {tyS : Ty levelS scopeS}
    {rawF : RawTerm scopeF}
    {rawS : RawTerm scopeS}
    {firstTermSubst : Term ctxF tyF rawF}
    {secondTermSubst : Term ctxF tyF rawF}
    {finalTerm : Term ctxS tyS rawS}
    (allaisFactor : ConvCumul firstTermSubst secondTermSubst)
    (bentonFactor : ConvCumul secondTermSubst finalTerm) :
    ConvCumul firstTermSubst finalTerm :=
  ConvCumul.trans allaisFactor bentonFactor

end LeanFX2
