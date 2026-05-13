import LeanFX2.Reduction.CumulAllais.EnvRelation

/-! # LeanFX2.Reduction.CumulAllais.ClosedArms

Per-Term-ctor Allais arms for the closed-payload + var + early
identity-type/equiv-refl/funext-refl ctors.  Each arm discharges
one ctor's obligation in the Allais `Simulation.alg` discipline.

Term ctors covered here fall into:

* **Closed-payload** (no scope-dependent subterms): both substituted
  sides coincide → `ConvCumul.refl`.  Coverage: unit, boolTrue,
  boolFalse, natZero, universeCode.
* **Var**: pointwise compat lookup → returns `compat position`.
* **Identity-type / equiv / funext closed schematics**: substHet
  arms depend only on sigma, both sides agree definitionally →
  `ConvCumul.refl`.  Coverage: equivReflId, funextRefl,
  equivReflIdAtId, funextReflAtId, funextIntroHet.

Reference: Allais et al. arxiv:1804.00119 §5.1.

## Root status

Layer 3 cumulativity-via-Allais helper. -/

namespace LeanFX2

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

end LeanFX2
