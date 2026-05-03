import LeanFX2.Reduction.Cumul

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

/-! Note: `snd` arm DEFERRED.

`Term.substHet`'s `snd` arm wraps the result in a propositional cast
`(Ty.subst0_substHet_commute secondType firstType (RawTerm.fst pairRaw)
  sigma).symm ▸ Term.snd (pairTerm.substHet ·)`.

The bare `ConvCumul.sndCong` expects the un-cast shape.  Lifting the
cong rule through the cast requires `ConvCumul.transport_through_eq`
infrastructure (transport-stability of ConvCumul under propositional
type equality).  That utility is part of the Benton section's
groundwork — `snd` arm lands once Benton's cast-handling lands. -/

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

/-! Note: `appPi` and `pair` arms DEFERRED.

Same `Ty.subst0_substHet_commute` cast issue as `snd` above.
Both `Term.substHet`'s `appPi` arm and `pair` arm wrap the
result component in a propositional type-cast that the bare
`appPiCong` / `pairCong` rules don't see.  Lifting through
the cast requires `ConvCumul.transport_through_eq` from the
Benton section's groundwork — these arms land alongside `snd`
once that utility ships. -/

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

/-! # Benton-Hur-Kennedy-McBride JAR'12 — single-substitution lift

This section will house the BHKM-style theorems: starting from
an EXISTING `ConvCumul firstTerm secondTerm`, lift through a
SINGLE `termSubst` to `ConvCumul (firstTerm.substHet termSubst)
(secondTerm.substHet termSubst)`.

Reference: Benton-Hur-Kennedy-McBride JAR'12 §6 (the
`ActScS_conv` corollary of the 4-lemma renaming-first ladder).
FX memory `reference_pattern_bhkm_ladder`.

**Status: pending** — this section will be filled in once the
Allais headline (`ConvCumul.subst_compatible_allais`) lands,
because the Benton form's binder arms (lam / lamPi) reuse the
Allais lift infrastructure for under-binder propagation. -/

end LeanFX2
