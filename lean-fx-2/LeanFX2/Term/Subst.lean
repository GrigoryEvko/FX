import LeanFX2.Term.Rename

/-! # Term/Subst — typed substitution on Term.

`Term.subst` lifts a joint `Subst` (forTy + forRaw) to typed Term
substitution.  The raw index of the result is automatically
`raw.subst sigma.forRaw` (type-index propagation through Term ctors).

## TermSubst

A `TermSubst sourceCtx targetCtx sigma` is the typed companion to a
`Subst level sourceScope targetScope`: for each variable position `i`
in source, it provides a Term in target whose type is the substituted
source-type and whose raw index is `sigma.forRaw i`.

Unlike TermRenaming (a Prop predicate), TermSubst is a Type because
it carries Term *values* — the substituted terms themselves.

Two operations:
* `TermSubst.lift termSubst newSourceType` — extend under one binder
* `TermSubst.singleton argTerm` — singleton substitution for β-reduction

## Cast discipline

The non-trivial cases of Term.subst use the Phase 1.G.1 + 1.G.2
foundation lemmas:

* `lam` / `lamPi` — `Ty.weaken_subst_commute` for body's weakened codomain
* `appPi` — `Ty.subst0_subst_commute.symm` for β-redex result type
* `pair` — `Ty.subst0_subst_commute` for the second component
* `snd` — `Ty.subst0_subst_commute.symm` for the projection result
* `var` — no cast; `termSubst position` directly returns the right type

`TermSubst.lift` itself uses `Ty.weaken_subst_commute` for both Fin.zero
and Fin.succ cases.  `TermSubst.singleton` uses `Ty.weaken_subst_singleton`
to discharge the cast at every position.

All zero-axiom — Eq.rec on Term-valued motive (verified via Smoke).
-/

namespace LeanFX2

/-! ## TermSubst -/

/-- A typed substitution: for each source position, a Term in target
whose type is the substituted source-type and whose raw is `sigma.forRaw i`. -/
def TermSubst {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    (sourceCtx : Ctx mode level sourceScope)
    (targetCtx : Ctx mode level targetScope)
    (sigma : Subst level sourceScope targetScope) : Type :=
  ∀ position,
    Term targetCtx ((varType sourceCtx position).subst sigma) (sigma.forRaw position)

/-- Lift a TermSubst under a binder.  Position 0 gets the new var
(after a cast through Ty.weaken_subst_commute); higher positions get
the old TermSubst values weakened by the new binding. -/
def TermSubst.lift {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (newSourceType : Ty level sourceScope) :
    TermSubst (sourceCtx.cons newSourceType)
              (targetCtx.cons (newSourceType.subst sigma))
              sigma.lift
  | ⟨0, _⟩ =>
      (Ty.weaken_subst_commute sigma newSourceType).symm ▸
        Term.var ⟨0, Nat.zero_lt_succ _⟩
  | ⟨k + 1, h⟩ =>
      (Ty.weaken_subst_commute sigma
        (varType sourceCtx ⟨k, Nat.lt_of_succ_lt_succ h⟩)).symm ▸
        Term.weaken (newSourceType.subst sigma)
                    (termSubst ⟨k, Nat.lt_of_succ_lt_succ h⟩)

/-- Singleton TermSubst for β-reduction: position 0 gets `argTerm`,
positions k+1 get `Term.var k`.  Both cases use `Ty.weaken_subst_singleton`
to discharge the type cast (weakened then substituted-by-singleton
returns to the original type). -/
def TermSubst.singleton {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {substituent : Ty level scope} {argRaw : RawTerm scope}
    (argTerm : Term sourceCtx substituent argRaw) :
    TermSubst (sourceCtx.cons substituent) sourceCtx
              (Subst.singleton substituent argRaw)
  | ⟨0, _⟩ =>
      (Ty.weaken_subst_singleton substituent substituent argRaw).symm ▸ argTerm
  | ⟨k + 1, h⟩ =>
      (Ty.weaken_subst_singleton (varType sourceCtx ⟨k, Nat.lt_of_succ_lt_succ h⟩)
        substituent argRaw).symm ▸
          Term.var ⟨k, Nat.lt_of_succ_lt_succ h⟩

/-! ## Term.subst -/

/-- Apply a typed substitution to a typed term.  29-case structural
recursion mirroring Term.rename's pattern, with substitution-side
casts via Ty.weaken_subst_commute and Ty.subst0_subst_commute. -/
def Term.subst {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma) :
    ∀ {someType : Ty level sourceScope} {raw : RawTerm sourceScope},
      Term sourceCtx someType raw →
      Term targetCtx (someType.subst sigma) (raw.subst sigma.forRaw)
  -- Variable: termSubst directly provides the substituted Term.
  | _, _, .var position => termSubst position
  -- Unit: trivial.
  | _, _, .unit => Term.unit
  -- Non-dep arrow lam: cast body via Ty.weaken_subst_commute.
  | _, _, .lam (codomainType := codomainType) body =>
      Term.lam (Ty.weaken_subst_commute sigma codomainType ▸
                Term.subst (termSubst.lift _) body)
  | _, _, .app fn arg =>
      Term.app (Term.subst termSubst fn) (Term.subst termSubst arg)
  -- Dep Π lam: body type is just codomainType; direct.
  | _, _, .lamPi body =>
      Term.lamPi (Term.subst (termSubst.lift _) body)
  -- Dep Π app: cast result via Ty.subst0_subst_commute.symm.
  | _, _, .appPi (codomainType := codomainType) (domainType := domainType)
                 (argumentRaw := argumentRaw) fn arg =>
      (Ty.subst0_subst_commute codomainType domainType argumentRaw sigma).symm ▸
        Term.appPi (Term.subst termSubst fn) (Term.subst termSubst arg)
  -- Σ pair: cast second component via Ty.subst0_subst_commute (forward).
  | _, _, .pair (secondType := secondType) (firstType := firstType)
                (firstRaw := firstRaw) fv sv =>
      Term.pair (Term.subst termSubst fv)
                (Ty.subst0_subst_commute secondType firstType firstRaw sigma ▸
                  Term.subst termSubst sv)
  | _, _, .fst pairTerm => Term.fst (Term.subst termSubst pairTerm)
  -- Σ snd: cast result via Ty.subst0_subst_commute.symm.
  | _, _, .snd (secondType := secondType) (firstType := firstType)
               (pairRaw := pairRaw) pairTerm =>
      (Ty.subst0_subst_commute secondType firstType
        (RawTerm.fst pairRaw) sigma).symm ▸
        Term.snd (Term.subst termSubst pairTerm)
  -- Booleans.
  | _, _, .boolTrue => Term.boolTrue
  | _, _, .boolFalse => Term.boolFalse
  | _, _, .boolElim scrutinee thenBranch elseBranch =>
      Term.boolElim (Term.subst termSubst scrutinee)
                    (Term.subst termSubst thenBranch)
                    (Term.subst termSubst elseBranch)
  -- Naturals.
  | _, _, .natZero => Term.natZero
  | _, _, .natSucc predecessor =>
      Term.natSucc (Term.subst termSubst predecessor)
  | _, _, .natElim scrutinee zeroBranch succBranch =>
      Term.natElim (Term.subst termSubst scrutinee)
                   (Term.subst termSubst zeroBranch)
                   (Term.subst termSubst succBranch)
  | _, _, .natRec scrutinee zeroBranch succBranch =>
      Term.natRec (Term.subst termSubst scrutinee)
                  (Term.subst termSubst zeroBranch)
                  (Term.subst termSubst succBranch)
  -- Lists.
  | _, _, .listNil => Term.listNil
  | _, _, .listCons headTerm tailTerm =>
      Term.listCons (Term.subst termSubst headTerm)
                    (Term.subst termSubst tailTerm)
  | _, _, .listElim scrutinee nilBranch consBranch =>
      Term.listElim (Term.subst termSubst scrutinee)
                    (Term.subst termSubst nilBranch)
                    (Term.subst termSubst consBranch)
  -- Options.
  | _, _, .optionNone => Term.optionNone
  | _, _, .optionSome valueTerm =>
      Term.optionSome (Term.subst termSubst valueTerm)
  | _, _, .optionMatch scrutinee noneBranch someBranch =>
      Term.optionMatch (Term.subst termSubst scrutinee)
                       (Term.subst termSubst noneBranch)
                       (Term.subst termSubst someBranch)
  -- Eithers.
  | _, _, .eitherInl valueTerm =>
      Term.eitherInl (Term.subst termSubst valueTerm)
  | _, _, .eitherInr valueTerm =>
      Term.eitherInr (Term.subst termSubst valueTerm)
  | _, _, .eitherMatch scrutinee leftBranch rightBranch =>
      Term.eitherMatch (Term.subst termSubst scrutinee)
                       (Term.subst termSubst leftBranch)
                       (Term.subst termSubst rightBranch)
  -- Identity types.
  | _, _, .refl carrier rawWitness =>
      Term.refl (carrier.subst sigma) (rawWitness.subst sigma.forRaw)
  | _, _, .idJ baseCase witness =>
      Term.idJ (Term.subst termSubst baseCase)
               (Term.subst termSubst witness)
  -- Modal: Layer 1 scaffolding.
  | _, _, .modIntro innerTerm =>
      Term.modIntro (Term.subst termSubst innerTerm)
  | _, _, .modElim innerTerm =>
      Term.modElim (Term.subst termSubst innerTerm)
  | _, _, .subsume innerTerm =>
      Term.subsume (Term.subst termSubst innerTerm)

/-! ## Term.subst0 — single-variable β-substitution -/

/-- Single-variable substitution: substitute `argTerm` for var 0 in
`bodyTerm`.  This is the load-bearing operation for β-reduction:
`Term.app (Term.lam body) arg → Term.subst0 body arg`. -/
@[reducible] def Term.subst0 {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {substituent : Ty level scope} {argRaw : RawTerm scope}
    {codomainType : Ty level (scope + 1)} {bodyRaw : RawTerm (scope + 1)}
    (bodyTerm : Term (sourceCtx.cons substituent) codomainType bodyRaw)
    (argTerm : Term sourceCtx substituent argRaw) :
    Term sourceCtx (codomainType.subst0 substituent argRaw)
                   (bodyRaw.subst0 argRaw) :=
  Term.subst (TermSubst.singleton argTerm) bodyTerm

end LeanFX2
