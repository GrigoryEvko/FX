import LeanFX2.Term.Subst
import LeanFX2.Foundation.SubstHet

/-! # Term/SubstHet — heterogeneous (level-polymorphic) typed Term substitution

`Term.substHet` lifts a `SubstHet sourceLevel targetLevel sourceScope
targetScope` to typed Term substitution that crosses universe levels.
The raw index of the result is automatically `raw.subst sigma.forRaw`
(type-index propagation through Term ctors).

## Why this exists

The single-level `Term.subst` (in `Term/Subst.lean`) handles
substitutions within a single universe level — sufficient for the
overwhelming majority of cases.  But for `Term.cumulUp`-related code
that crosses universe levels (lower-side at `lowerLevel + 1`,
upper-side at `higherLevel + 1` with `lowerLevel ≤ higherLevel`),
the lower-side recursive substitution requires a heterogeneous
substitution.

## TermSubstHet

A `TermSubstHet sourceCtx targetCtx sigma` is the typed companion to a
`SubstHet sourceLevel targetLevel sourceScope targetScope`: for each
variable position `i` in source, it provides a Term in target whose
type is the substHet'd source-type and whose raw index is
`sigma.forRaw i`.

## Architecture

Term.substHet is structurally identical to Term.subst modulo level
threading:
* All Ty.subst calls become Ty.substHet (via the foundation lemmas
  in Foundation/SubstHet.lean)
* The result's universe level is targetLevel (the SubstHet's target)
* Cumul-related casts use Ty.weaken_substHet_commute and
  Ty.subst0_substHet_commute (the heterogeneous foundation lemmas)

## Bridges to/from Term.subst

* `TermSubstHet.fromTermSubst` — same-level Subst → SubstHet
* `Term.substHet_fromSubst` — substHet on fromSubst-derived SubstHet
   agrees with subst (at same level)

## Cumul-related uses

* `Term.cumulUp`'s subst arm (in this file) uses Term.substHet to
   handle the lower-side recursion when scope > 0 in Phase 12.A.B1.4.
* `ConvCumul.subst_compatible` (in Reduction/Cumul.lean) uses
   Term.substHet to formulate the general subst-compat statement.

## Audit gates

`Smoke/AuditPhase12AB13TermSubstHet.lean` runs `#print axioms` on
every declaration in this file.  All zero-axiom under strict policy.

## P-4 cumul-Subst-mismatch sidestep

The P-4 wall (`feedback_lean_cumul_subst_mismatch`) is sidestepped by
SubstHet's design: substituents in `forTy` already live at
`targetLevel`, so the user is responsible for constructing them at
the right level (using `Ty.lift_level` or `Ty.substHet_cumul` if
needed).
-/

namespace LeanFX2

/-! ## TermSubstHet -/

/-- A heterogeneous typed substitution: for each source position, a Term
in target whose type is the substHet'd source-type and whose raw is
`sigma.forRaw i`.  The two contexts may live at different universe
levels — `sourceCtx` at `sourceLevel`, `targetCtx` at `targetLevel`. -/
def TermSubstHet {mode : Mode}
    {sourceLevel targetLevel : Nat}
    {sourceScope targetScope : Nat}
    (sourceCtx : Ctx mode sourceLevel sourceScope)
    (targetCtx : Ctx mode targetLevel targetScope)
    (sigma : SubstHet sourceLevel targetLevel sourceScope targetScope) : Type :=
  ∀ position,
    Term targetCtx ((varType sourceCtx position).substHet sigma) (sigma.forRaw position)

/-- Lift a TermSubstHet under a binder.  Position 0 gets the new var
(after a cast through Ty.weaken_substHet_commute); higher positions
get the old TermSubstHet values weakened by the new binding. -/
def TermSubstHet.lift {mode : Mode}
    {sourceLevel targetLevel : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstHet : TermSubstHet sourceCtx targetCtx sigma)
    (newSourceType : Ty sourceLevel sourceScope) :
    TermSubstHet (sourceCtx.cons newSourceType)
                 (targetCtx.cons (newSourceType.substHet sigma))
                 sigma.lift
  | ⟨0, _⟩ =>
      (Ty.weaken_substHet_commute sigma newSourceType).symm ▸
        Term.var ⟨0, Nat.zero_lt_succ _⟩
  | ⟨k + 1, h⟩ =>
      (Ty.weaken_substHet_commute sigma
        (varType sourceCtx ⟨k, Nat.lt_of_succ_lt_succ h⟩)).symm ▸
        Term.weaken (newSourceType.substHet sigma)
                    (termSubstHet ⟨k, Nat.lt_of_succ_lt_succ h⟩)

/-! ## Term.substHet -/

/-- Apply a heterogeneous typed substitution to a typed term.  Mirrors
Term.subst but with cross-level substitution, using the SubstHet
foundation lemmas for casts. -/
def Term.substHet {mode : Mode}
    {sourceLevel targetLevel : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstHet : TermSubstHet sourceCtx targetCtx sigma) :
    ∀ {someType : Ty sourceLevel sourceScope} {raw : RawTerm sourceScope},
      Term sourceCtx someType raw →
      Term targetCtx (someType.substHet sigma) (raw.subst sigma.forRaw)
  -- Variable: termSubstHet directly provides the substituted Term.
  | _, _, .var position => termSubstHet position
  -- Unit: trivial.
  | _, _, .unit => Term.unit
  -- Non-dep arrow lam: cast body via Ty.weaken_substHet_commute.
  | _, _, .lam (codomainType := codomainType) body =>
      Term.lam (Ty.weaken_substHet_commute sigma codomainType ▸
                Term.substHet (termSubstHet.lift _) body)
  | _, _, .app fn arg =>
      Term.app (Term.substHet termSubstHet fn) (Term.substHet termSubstHet arg)
  -- Dep Π lam: body type is just codomainType; direct.
  | _, _, .lamPi body =>
      Term.lamPi (Term.substHet (termSubstHet.lift _) body)
  -- Dep Π app: cast result via Ty.subst0_substHet_commute.symm.
  | _, _, .appPi (codomainType := codomainType) (domainType := domainType)
                 (argumentRaw := argumentRaw) fn arg =>
      (Ty.subst0_substHet_commute codomainType domainType argumentRaw sigma).symm ▸
        Term.appPi (Term.substHet termSubstHet fn) (Term.substHet termSubstHet arg)
  -- Σ pair: cast second component via Ty.subst0_substHet_commute (forward).
  | _, _, .pair (secondType := secondType) (firstType := firstType)
                (firstRaw := firstRaw) fv sv =>
      Term.pair (Term.substHet termSubstHet fv)
                (Ty.subst0_substHet_commute secondType firstType firstRaw sigma ▸
                  Term.substHet termSubstHet sv)
  | _, _, .fst pairTerm => Term.fst (Term.substHet termSubstHet pairTerm)
  -- Σ snd: cast result via Ty.subst0_substHet_commute.symm.
  | _, _, .snd (secondType := secondType) (firstType := firstType)
               (pairRaw := pairRaw) pairTerm =>
      (Ty.subst0_substHet_commute secondType firstType
        (RawTerm.fst pairRaw) sigma).symm ▸
        Term.snd (Term.substHet termSubstHet pairTerm)
  -- Booleans.
  | _, _, .boolTrue => Term.boolTrue
  | _, _, .boolFalse => Term.boolFalse
  | _, _, .boolElim scrutinee thenBranch elseBranch =>
      Term.boolElim (Term.substHet termSubstHet scrutinee)
                    (Term.substHet termSubstHet thenBranch)
                    (Term.substHet termSubstHet elseBranch)
  -- Naturals.
  | _, _, .natZero => Term.natZero
  | _, _, .natSucc predecessor =>
      Term.natSucc (Term.substHet termSubstHet predecessor)
  | _, _, .natElim scrutinee zeroBranch succBranch =>
      Term.natElim (Term.substHet termSubstHet scrutinee)
                   (Term.substHet termSubstHet zeroBranch)
                   (Term.substHet termSubstHet succBranch)
  | _, _, .natRec scrutinee zeroBranch succBranch =>
      Term.natRec (Term.substHet termSubstHet scrutinee)
                  (Term.substHet termSubstHet zeroBranch)
                  (Term.substHet termSubstHet succBranch)
  -- Lists.
  | _, _, .listNil => Term.listNil
  | _, _, .listCons headTerm tailTerm =>
      Term.listCons (Term.substHet termSubstHet headTerm)
                    (Term.substHet termSubstHet tailTerm)
  | _, _, .listElim scrutinee nilBranch consBranch =>
      Term.listElim (Term.substHet termSubstHet scrutinee)
                    (Term.substHet termSubstHet nilBranch)
                    (Term.substHet termSubstHet consBranch)
  -- Options.
  | _, _, .optionNone => Term.optionNone
  | _, _, .optionSome valueTerm =>
      Term.optionSome (Term.substHet termSubstHet valueTerm)
  | _, _, .optionMatch scrutinee noneBranch someBranch =>
      Term.optionMatch (Term.substHet termSubstHet scrutinee)
                       (Term.substHet termSubstHet noneBranch)
                       (Term.substHet termSubstHet someBranch)
  -- Eithers.
  | _, _, .eitherInl valueTerm =>
      Term.eitherInl (Term.substHet termSubstHet valueTerm)
  | _, _, .eitherInr valueTerm =>
      Term.eitherInr (Term.substHet termSubstHet valueTerm)
  | _, _, .eitherMatch scrutinee leftBranch rightBranch =>
      Term.eitherMatch (Term.substHet termSubstHet scrutinee)
                       (Term.substHet termSubstHet leftBranch)
                       (Term.substHet termSubstHet rightBranch)
  -- Identity types.
  | _, _, .refl carrier rawWitness =>
      Term.refl (carrier.substHet sigma) (rawWitness.subst sigma.forRaw)
  | _, _, .idJ baseCase witness =>
      Term.idJ (Term.substHet termSubstHet baseCase)
               (Term.substHet termSubstHet witness)
  -- Modal: Layer 1 scaffolding.
  | _, _, .modIntro innerTerm =>
      Term.modIntro (Term.substHet termSubstHet innerTerm)
  | _, _, .modElim innerTerm =>
      Term.modElim (Term.substHet termSubstHet innerTerm)
  | _, _, .subsume innerTerm =>
      Term.subsume (Term.substHet termSubstHet innerTerm)
  -- Universe-code: the outer level shifts via Nat.le_trans on the levelLe
  -- proof.  Both `Ty.universe outerLevel levelLe` (lifted via Nat.le_trans
  -- with sigma.cumulOk) and `RawTerm.universeCode innerLevel.toNat`
  -- substitute to themselves (no scope-dependent payload), so we
  -- rebuild the ctor at the target level + scope using the lifted
  -- levelLe proof.
  | _, _, .universeCode innerLevel outerLevel cumulOk levelLe =>
      Term.universeCode innerLevel outerLevel cumulOk
                        (Nat.le_trans levelLe sigma.cumulOk)
  -- Cumul-up (REAL cumul ctor): the inner Term lives at scope 0 in
  -- the v12.A.2 architecture, so it carries no positions to substitute.
  -- We pass `lowerTerm` through unchanged and reconstruct cumulUp at
  -- the new target scope/level.  Both the universe-code raw form and
  -- `Ty.universe ...` substitute to themselves (no scope-dependent
  -- payload).  The level shift on the OUTER side requires composing
  -- levelLeHigh with sigma.cumulOk via Nat.le_trans.
  | _, _, .cumulUp innerLevel lowerLevel higherLevel
                   cumulOkLow cumulOkHigh cumulMonotone
                   levelLeLow levelLeHigh lowerTerm =>
      Term.cumulUp (ctxHigh := targetCtx)
                   innerLevel lowerLevel higherLevel
                   cumulOkLow cumulOkHigh cumulMonotone
                   levelLeLow (Nat.le_trans levelLeHigh sigma.cumulOk)
                   lowerTerm
  -- HoTT canonical identity equivalence (Phase 12.A.B8.1): carrier
  -- substitutes via `sigma`; the raw-side identity-lambda shape is
  -- constant (substituent var-0 of an identity-lift is itself).
  | _, _, .equivReflId carrier =>
      Term.equivReflId (carrier.substHet sigma)
  -- HoTT canonical funext refl-fragment witness (Phase 12.A.B8.2):
  -- mirror the homogeneous Subst arm, swapping in `Ty.weaken_substHet_commute`.
  | _, _, .funextRefl domainType codomainType applyRaw =>
      show Term targetCtx
        (Ty.piTy (domainType.substHet sigma)
          (Ty.id (codomainType.weaken.substHet sigma.lift)
            (applyRaw.subst sigma.forRaw.lift)
            (applyRaw.subst sigma.forRaw.lift)))
        (RawTerm.lam (RawTerm.refl (applyRaw.subst sigma.forRaw.lift))) from
      let codomainEqInverse :
          (codomainType.substHet sigma).weaken =
            codomainType.weaken.substHet sigma.lift :=
        (Ty.weaken_substHet_commute sigma codomainType).symm
      codomainEqInverse ▸
        Term.funextRefl (domainType.substHet sigma)
                        (codomainType.substHet sigma)
                        (applyRaw.subst sigma.forRaw.lift)

/-! ## Bridge: TermSubst → TermSubstHet (kernel piece for Pattern 2 ⇔ 3 bridge)

Same-level `TermSubst` lifts to `TermSubstHet` along
`SubstHet.fromSubst`.  Per-position cast through `Ty.substHet_fromSubst`
realigns the Ty index from `someTy.subst sigma` to
`someTy.substHet (SubstHet.fromSubst sigma)` (propositionally equal,
not definitional — the universe arm differs by `Nat.le_trans levelLe
(Nat.le_refl _)` vs `levelLe`, equal via Subsingleton.elim).

Used by `Reduction/CumulPattern23Bridge.lean` to express Pattern 2's
single-σ result as a paired-env Pattern 3 instance at refl-compat. -/

/-- Lift a same-level `TermSubst` to a `TermSubstHet` along
`SubstHet.fromSubst`.  Per position, cast through `Ty.substHet_fromSubst`
to realign the Ty index. -/
def TermSubstHet.fromTermSubst {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma) :
    TermSubstHet sourceCtx targetCtx (SubstHet.fromSubst sigma) :=
  fun position =>
    (Ty.substHet_fromSubst sigma (varType sourceCtx position)).symm ▸
      termSubst position

end LeanFX2
