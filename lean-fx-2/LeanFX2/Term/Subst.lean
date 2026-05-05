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
  | _, _, .idStrictRefl carrier rawWitness =>
      Term.idStrictRefl
        (carrier.subst sigma) (rawWitness.subst sigma.forRaw)
  | _, _, .idStrictRec baseCase witness =>
      Term.idStrictRec (Term.subst termSubst baseCase)
                       (Term.subst termSubst witness)
  -- Modal: Layer 1 scaffolding.
  | _, _, .modIntro innerTerm =>
      Term.modIntro (Term.subst termSubst innerTerm)
  | _, _, .modElim innerTerm =>
      Term.modElim (Term.subst termSubst innerTerm)
  | _, _, .subsume innerTerm =>
      Term.subsume (Term.subst termSubst innerTerm)
  -- Cubical path fragment.
  | _, _, .interval0 => Term.interval0
  | _, _, .interval1 => Term.interval1
  | _, _, .intervalOpp innerValue =>
      Term.intervalOpp (Term.subst termSubst innerValue)
  | _, _, .intervalMeet leftValue rightValue =>
      Term.intervalMeet (Term.subst termSubst leftValue)
                        (Term.subst termSubst rightValue)
  | _, _, .intervalJoin leftValue rightValue =>
      Term.intervalJoin (Term.subst termSubst leftValue)
                        (Term.subst termSubst rightValue)
  | _, _, .pathLam carrierType leftEndpoint rightEndpoint body =>
      Term.pathLam (carrierType.subst sigma)
        (leftEndpoint.subst sigma.forRaw)
        (rightEndpoint.subst sigma.forRaw)
        (Ty.weaken_subst_commute sigma carrierType ▸
          Term.subst (termSubst.lift Ty.interval) body)
  | _, _, .pathApp pathTerm intervalTerm =>
      Term.pathApp (Term.subst termSubst pathTerm)
                   (Term.subst termSubst intervalTerm)
  | _, _, .glueIntro baseType boundaryWitness baseValue partialValue =>
      Term.glueIntro (baseType.subst sigma)
        (boundaryWitness.subst sigma.forRaw)
        (Term.subst termSubst baseValue)
        (Term.subst termSubst partialValue)
  | _, _, .glueElim gluedValue =>
      Term.glueElim (Term.subst termSubst gluedValue)
  | _, _, .transp universeLevel universeLevelLt sourceType targetType
      sourceTypeRaw targetTypeRaw typePath sourceValue =>
      Term.transp universeLevel universeLevelLt
        (sourceType.subst sigma)
        (targetType.subst sigma)
        (sourceTypeRaw.subst sigma.forRaw)
        (targetTypeRaw.subst sigma.forRaw)
        (Term.subst termSubst typePath)
        (Term.subst termSubst sourceValue)
  | _, _, .hcomp sidesValue capValue =>
      Term.hcomp (Term.subst termSubst sidesValue)
                 (Term.subst termSubst capValue)
  | _, _, .recordIntro firstField =>
      Term.recordIntro (Term.subst termSubst firstField)
  | _, _, .recordProj recordValue =>
      Term.recordProj (Term.subst termSubst recordValue)
  | _, _, .refineIntro predicate baseValue predicateProof =>
      Term.refineIntro (predicate.subst sigma.forRaw.lift)
        (Term.subst termSubst baseValue)
        (Term.subst termSubst predicateProof)
  | _, _, .refineElim refinedValue =>
      Term.refineElim (Term.subst termSubst refinedValue)
  -- Universe-code: scope-polymorphic.  Both `Ty.universe outerLevel
  -- levelLe` and `RawTerm.universeCode innerLevel.toNat` substitute to
  -- themselves (no scope-dependent payload), so rebuilding the ctor
  -- at the target scope matches the expected types definitionally.
  | _, _, .universeCode innerLevel outerLevel cumulOk levelLe =>
      Term.universeCode innerLevel outerLevel cumulOk levelLe
  -- Cumul-up (REAL cumul ctor) — Phase CUMUL-2.6 Design D.  Single
  -- context throughout, schematic codeRaw, output wrapped in
  -- cumulUpMarker.  The inner typed source term lives at the SAME
  -- scope/context as the outer; recursively substitute the inner
  -- typeCode and reconstruct the cumulUp ctor at the target scope.
  -- Output raw becomes `RawTerm.cumulUpMarker (codeRaw.subst sigma.forRaw)`,
  -- definitionally `(RawTerm.cumulUpMarker codeRaw).subst sigma.forRaw`.
  | _, _, .cumulUp lowerLevel higherLevel
                   cumulMonotone levelLeLow levelLeHigh typeCode =>
      Term.cumulUp (context := targetCtx)
                   lowerLevel higherLevel cumulMonotone
                   levelLeLow levelLeHigh
                   (Term.subst termSubst typeCode)
  -- HoTT canonical identity equivalence (Phase 12.A.B8.1): carrier
  -- substitutes via `sigma`; the raw-side identity-lambda shape is
  -- constant, with `RawTerm.var 0` substituting through identity-lift
  -- back to itself.
  | _, _, .equivReflId carrier =>
      Term.equivReflId (carrier.subst sigma)
  -- HoTT heterogeneous-carrier equivalence introduction (Phase 12.A.B8.5):
  -- carrierA + carrierB substitute via `sigma`; the two subterms
  -- `forward`, `backward` substitute structurally.  No `weaken`-commute
  -- cast needed because `Ty.equiv` and `Ty.arrow` are non-binder
  -- carriers whose substitution doesn't introduce a scope shift.
  | _, _, .equivIntroHet forward backward =>
      Term.equivIntroHet (Term.subst termSubst forward)
                         (Term.subst termSubst backward)
  | _, _, .equivApp equivTerm argumentTerm =>
      Term.equivApp (Term.subst termSubst equivTerm)
                    (Term.subst termSubst argumentTerm)
  -- HoTT canonical funext refl-fragment witness (Phase 12.A.B8.2):
  -- carrier types substitute via `sigma`; the schematic `applyRaw`
  -- payload (at scope+1) substitutes via `sigma.forRaw.lift`.  The
  -- result type involves `codomainType.weaken.id ...`; we cast via
  -- `Ty.weaken_subst_commute` like the `lam` arm.
  | _, _, .funextRefl domainType codomainType applyRaw =>
      show Term targetCtx
        (Ty.piTy (domainType.subst sigma)
          (Ty.id (codomainType.weaken.subst sigma.lift)
            (applyRaw.subst sigma.forRaw.lift)
            (applyRaw.subst sigma.forRaw.lift)))
        (RawTerm.lam (RawTerm.refl (applyRaw.subst sigma.forRaw.lift))) from
      let codomainEqInverse :
          (codomainType.subst sigma).weaken =
            codomainType.weaken.subst sigma.lift :=
        (Ty.weaken_subst_commute sigma codomainType).symm
      codomainEqInverse ▸
        Term.funextRefl (domainType.subst sigma)
                        (codomainType.subst sigma)
                        (applyRaw.subst sigma.forRaw.lift)
  -- HoTT canonical Id-typed identity-equivalence proof at the universe
  -- (Phase 12.A.B8.1).  `Ty.id (Ty.universe innerLevel ...) carrierRaw
  -- carrierRaw` substitutes carrierRaw via `sigma.forRaw`; carrier
  -- substitutes via `sigma`; the universe-code raw is constant.  The
  -- raw-side identity-lambda is constant under any `sigma.forRaw`.
  | _, _, .equivReflIdAtId innerLevel innerLevelLt carrier carrierRaw =>
      Term.equivReflIdAtId innerLevel innerLevelLt
                           (carrier.subst sigma)
                           (carrierRaw.subst sigma.forRaw)
  -- HoTT canonical Id-typed funext witness at arrow types
  -- (Phase 12.A.B8.2).  `Ty.id (Ty.arrow ...) (lam (refl applyRaw))
  -- (lam (refl applyRaw))` substitutes domainType + codomainType via
  -- `sigma`; applyRaw at scope+1 via `sigma.forRaw.lift`.  No
  -- `weaken`-commute cast needed because `Ty.arrow` is a non-binder
  -- carrier whose substitution doesn't introduce a scope shift.
  | _, _, .funextReflAtId domainType codomainType applyRaw =>
      Term.funextReflAtId (domainType.subst sigma)
                          (codomainType.subst sigma)
                          (applyRaw.subst sigma.forRaw.lift)
  -- HoTT heterogeneous-carrier path-from-equivalence (Phase 12.A.B8.5b).
  -- `Ty.id (Ty.universe innerLevel ...) carrierARaw carrierBRaw` substitutes
  -- carrierA + carrierB via `sigma`, and carrierARaw + carrierBRaw via
  -- `sigma.forRaw`.  The single subterm `equivWitness` substitutes
  -- structurally; its raw form `RawTerm.equivIntro forwardRaw backwardRaw`
  -- substitutes pointwise to `RawTerm.equivIntro (forwardRaw.subst
  -- sigma.forRaw) (backwardRaw.subst sigma.forRaw)` — the same shape the
  -- ctor expects.  No `weaken`-commute cast needed since `Ty.equiv` and
  -- `Ty.universe` are non-binder carriers (no scope shift).
  | _, _, .uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw
                      equivWitness =>
      Term.uaIntroHet innerLevel innerLevelLt
                      (carrierARaw.subst sigma.forRaw)
                      (carrierBRaw.subst sigma.forRaw)
                      (Term.subst termSubst equivWitness)
  -- HoTT heterogeneous-carrier funext-introduction at Id-of-arrow
  -- (Phase 12.A.B8.8).  `Ty.id (Ty.arrow domainType codomainType)
  -- (RawTerm.lam applyARaw) (RawTerm.lam applyBRaw)` substitutes via
  -- `sigma`: domainType + codomainType at outer scope, applyARaw +
  -- applyBRaw at scope+1 via `sigma.forRaw.lift` (under the lambda
  -- binder).  No subterm to recurse on — funextIntroHet is a VALUE
  -- (canonical heterogeneous-funext witness) just like funextReflAtId.
  -- No `weaken`-commute cast needed since `Ty.id` and `Ty.arrow` are
  -- non-binder carriers (no scope shift).
  | _, _, .funextIntroHet domainType codomainType applyARaw applyBRaw =>
      Term.funextIntroHet (domainType.subst sigma)
                          (codomainType.subst sigma)
                          (applyARaw.subst sigma.forRaw.lift)
                          (applyBRaw.subst sigma.forRaw.lift)
  -- CUMUL-2.4 typed type-code constructors (VALUE-shaped).  All ten
  -- ctors substitute their schematic raw payloads via `sigma.forRaw`
  -- at the outer scope; binder-shape codes (piTyCode, sigmaTyCode)
  -- thread `sigma.forRaw.lift` through the codomain raw at
  -- `scope + 1`.  The `Ty.universe outerLevel levelLe` result type
  -- substitutes to itself (no scope-dependent payload).
  | _, _, .arrowCode outerLevel levelLe domainCodeRaw codomainCodeRaw =>
      Term.arrowCode outerLevel levelLe
                     (domainCodeRaw.subst sigma.forRaw)
                     (codomainCodeRaw.subst sigma.forRaw)
  | _, _, .piTyCode outerLevel levelLe domainCodeRaw codomainCodeRaw =>
      Term.piTyCode outerLevel levelLe
                    (domainCodeRaw.subst sigma.forRaw)
                    (codomainCodeRaw.subst sigma.forRaw.lift)
  | _, _, .sigmaTyCode outerLevel levelLe domainCodeRaw codomainCodeRaw =>
      Term.sigmaTyCode outerLevel levelLe
                       (domainCodeRaw.subst sigma.forRaw)
                       (codomainCodeRaw.subst sigma.forRaw.lift)
  | _, _, .productCode outerLevel levelLe firstCodeRaw secondCodeRaw =>
      Term.productCode outerLevel levelLe
                       (firstCodeRaw.subst sigma.forRaw)
                       (secondCodeRaw.subst sigma.forRaw)
  | _, _, .sumCode outerLevel levelLe leftCodeRaw rightCodeRaw =>
      Term.sumCode outerLevel levelLe
                   (leftCodeRaw.subst sigma.forRaw)
                   (rightCodeRaw.subst sigma.forRaw)
  | _, _, .listCode outerLevel levelLe elementCodeRaw =>
      Term.listCode outerLevel levelLe (elementCodeRaw.subst sigma.forRaw)
  | _, _, .optionCode outerLevel levelLe elementCodeRaw =>
      Term.optionCode outerLevel levelLe (elementCodeRaw.subst sigma.forRaw)
  | _, _, .eitherCode outerLevel levelLe leftCodeRaw rightCodeRaw =>
      Term.eitherCode outerLevel levelLe
                      (leftCodeRaw.subst sigma.forRaw)
                      (rightCodeRaw.subst sigma.forRaw)
  | _, _, .idCode outerLevel levelLe typeCodeRaw leftRaw rightRaw =>
      Term.idCode outerLevel levelLe
                  (typeCodeRaw.subst sigma.forRaw)
                  (leftRaw.subst sigma.forRaw)
                  (rightRaw.subst sigma.forRaw)
  | _, _, .equivCode outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw =>
      Term.equivCode outerLevel levelLe
                     (leftTypeCodeRaw.subst sigma.forRaw)
                     (rightTypeCodeRaw.subst sigma.forRaw)

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
