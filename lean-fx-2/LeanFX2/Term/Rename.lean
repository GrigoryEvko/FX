import LeanFX2.Term.ToRaw

/-! # Term/Rename — typed termRenaming on Term.

`Term.rename` lifts a raw `RawRenaming` on RawTerm scopes to a typed
termRenaming on the dependently-typed Term inductive.  The raw index of the
result is automatically `rawSrc.rename rho` (no proof obligation —
type-index propagation handles it via per-ctor structural pinning in
the Term inductive).

## TermRenaming

A `TermRenaming sourceCtx targetCtx rho` is the typed companion to a
`RawRenaming sourceScope targetScope`: it asserts that the termRenaming
preserves variable types under the two contexts.  Concretely, looking
up position `rho i` in `targetCtx` gives the rename of position `i`'s
type from `sourceCtx`.

Two operations:
* `TermRenaming.lift termRenaming newSourceType` — extend under one binder
* `TermRenaming.weakenStep context newType` — the canonical weakening
  TermRenaming for adding one binding to the head

## Cast discipline

The non-trivial cases (`var`, `lam`, `lamPi`, `appPi`, `pair`, `snd`)
need type-equality casts to align the recursive call's type with the
expected ctor argument shape.  Each cast uses `▸` on a foundation lemma:

* `var` — cast via `(termRenaming i).symm` to align `varType` lookup
* `lam` / `lamPi` — cast via `Ty.weaken_rename_commute` to align body type
* `appPi` — cast via `Ty.subst0_rename_commute` to align β-redex result
* `pair` — cast via `Ty.subst0_rename_commute` for the second component
* `snd` — cast via `Ty.subst0_rename_commute` for the projection result

All casts on `Term`-typed values are axiom-free (verified via
Smoke/AuditCast — recursor-based `Eq.rec` + reducible motive).
-/

namespace LeanFX2

/-! ## TermRenaming -/

/-- A typed termRenaming relates two contexts via a raw termRenaming, requiring
that variable types align: looking up position `rho i` in target gives
the rename of position `i`'s type from source. -/
def TermRenaming {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    (sourceCtx : Ctx mode level sourceScope)
    (targetCtx : Ctx mode level targetScope)
    (rho : RawRenaming sourceScope targetScope) : Prop :=
  ∀ position, varType targetCtx (rho position) =
              (varType sourceCtx position).rename rho

/-- Lift a TermRenaming under a binder.  Both contexts gain one
binding; the target's binding type is the renamed source binding.
The new positions agree because:
* Position 0: `(newSourceType.rename rho).weaken =
              newSourceType.weaken.rename rho.lift` (Ty.weaken_rename_commute)
* Position k+1: `(varType target (rho ⟨k, _⟩)).weaken` agrees with
                `((varType source ⟨k, _⟩).rename rho).weaken` via the
                termRenaming hypothesis at k, modulo Ty.weaken_rename_commute. -/
theorem TermRenaming.lift
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (newSourceType : Ty level sourceScope) :
    TermRenaming (sourceCtx.cons newSourceType)
                 (targetCtx.cons (newSourceType.rename rho))
                 rho.lift := by
  intro position
  cases position with
  | mk val isLt =>
    cases val with
    | zero =>
      show (newSourceType.rename rho).weaken =
           newSourceType.weaken.rename rho.lift
      exact (Ty.weaken_rename_commute rho newSourceType).symm
    | succ k =>
      show (varType targetCtx (rho ⟨k, Nat.lt_of_succ_lt_succ isLt⟩)).weaken =
           ((varType sourceCtx ⟨k, Nat.lt_of_succ_lt_succ isLt⟩).weaken).rename rho.lift
      rw [termRenaming ⟨k, Nat.lt_of_succ_lt_succ isLt⟩,
          Ty.weaken_rename_commute rho (varType sourceCtx _)]

/-- The canonical weakening TermRenaming: adding one binding to the
head of a context, with `RawRenaming.weaken` shifting all positions
up by one.  Pure rfl per `varType`'s second arm. -/
theorem TermRenaming.weakenStep {mode : Mode} {level scope : Nat}
    (context : Ctx mode level scope) (newType : Ty level scope) :
    TermRenaming context (context.cons newType) RawRenaming.weaken :=
  fun _ => rfl

/-! ## Term.rename -/

/-- Apply a typed termRenaming to a typed term.  The output's raw index is
automatically `raw.rename rho` (the Term inductive's raw index pins the
shape per ctor — recursive calls supply the renamed sub-raws and Lean
elaborates the result raw structurally).

This is a 29-case structural recursion mirroring the Term inductive.
Type-equality casts via `▸` use the Phase 1.D-foundation and 1.E
foundation lemmas to align the recursive call's result with the
expected ctor argument shape. -/
def Term.rename {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho) :
    ∀ {someType : Ty level sourceScope} {raw : RawTerm sourceScope},
      Term sourceCtx someType raw →
      Term targetCtx (someType.rename rho) (raw.rename rho)
  -- Variable: cast via the termRenaming's equation at this position.
  | _, _, .var position =>
      (termRenaming position).symm ▸ Term.var (rho position)
  -- Unit: trivial.
  | _, _, .unit => Term.unit
  -- Non-dep arrow lam: body's type is codomain.weaken; cast to
  -- (codomain.rename rho).weaken via Ty.weaken_rename_commute.
  | _, _, .lam (codomainType := codomainType) body =>
      Term.lam (Ty.weaken_rename_commute rho codomainType ▸
                Term.rename (termRenaming.lift _) body)
  -- Non-dep arrow app: result type Ty.arrow renames automatically.
  | _, _, .app functionTerm argumentTerm =>
      Term.app (Term.rename termRenaming functionTerm)
               (Term.rename termRenaming argumentTerm)
  -- Dep Π lam: body's type is just codomainType (no weaken); direct.
  | _, _, .lamPi body =>
      Term.lamPi (Term.rename (termRenaming.lift _) body)
  -- Dep Π app: result type uses subst0; cast via Ty.subst0_rename_commute.
  | _, _, .appPi (codomainType := codomainType) (domainType := domainType)
                 (argumentRaw := argumentRaw) functionTerm argumentTerm =>
      (Ty.subst0_rename_commute codomainType domainType argumentRaw rho).symm ▸
        Term.appPi (Term.rename termRenaming functionTerm)
                   (Term.rename termRenaming argumentTerm)
  -- Σ pair: second value's type uses subst0; cast.
  | _, _, .pair (secondType := secondType) (firstType := firstType)
                (firstRaw := firstRaw) firstValue secondValue =>
      Term.pair (Term.rename termRenaming firstValue)
                (Ty.subst0_rename_commute secondType firstType firstRaw rho ▸
                  Term.rename termRenaming secondValue)
  -- Σ fst: result is firstType; direct.
  | _, _, .fst pairTerm => Term.fst (Term.rename termRenaming pairTerm)
  -- Σ snd: result type uses subst0 with RawTerm.fst pairRaw; cast.
  | _, _, .snd (secondType := secondType) (firstType := firstType)
               (pairRaw := pairRaw) pairTerm =>
      (Ty.subst0_rename_commute secondType firstType
        (RawTerm.fst pairRaw) rho).symm ▸
        Term.snd (Term.rename termRenaming pairTerm)
  -- Booleans: trivial.
  | _, _, .boolTrue => Term.boolTrue
  | _, _, .boolFalse => Term.boolFalse
  | _, _, .boolElim scrutinee thenBranch elseBranch =>
      Term.boolElim (Term.rename termRenaming scrutinee)
                    (Term.rename termRenaming thenBranch)
                    (Term.rename termRenaming elseBranch)
  -- Naturals: trivial constants + structural cong.
  | _, _, .natZero => Term.natZero
  | _, _, .natSucc predecessor =>
      Term.natSucc (Term.rename termRenaming predecessor)
  | _, _, .natElim scrutinee zeroBranch succBranch =>
      Term.natElim (Term.rename termRenaming scrutinee)
                   (Term.rename termRenaming zeroBranch)
                   (Term.rename termRenaming succBranch)
  | _, _, .natRec scrutinee zeroBranch succBranch =>
      Term.natRec (Term.rename termRenaming scrutinee)
                  (Term.rename termRenaming zeroBranch)
                  (Term.rename termRenaming succBranch)
  -- Lists: structural.
  | _, _, .listNil => Term.listNil
  | _, _, .listCons headTerm tailTerm =>
      Term.listCons (Term.rename termRenaming headTerm)
                    (Term.rename termRenaming tailTerm)
  | _, _, .listElim scrutinee nilBranch consBranch =>
      Term.listElim (Term.rename termRenaming scrutinee)
                    (Term.rename termRenaming nilBranch)
                    (Term.rename termRenaming consBranch)
  -- Options: structural.
  | _, _, .optionNone => Term.optionNone
  | _, _, .optionSome valueTerm =>
      Term.optionSome (Term.rename termRenaming valueTerm)
  | _, _, .optionMatch scrutinee noneBranch someBranch =>
      Term.optionMatch (Term.rename termRenaming scrutinee)
                       (Term.rename termRenaming noneBranch)
                       (Term.rename termRenaming someBranch)
  -- Eithers: structural.
  | _, _, .eitherInl valueTerm =>
      Term.eitherInl (Term.rename termRenaming valueTerm)
  | _, _, .eitherInr valueTerm =>
      Term.eitherInr (Term.rename termRenaming valueTerm)
  | _, _, .eitherMatch scrutinee leftBranch rightBranch =>
      Term.eitherMatch (Term.rename termRenaming scrutinee)
                       (Term.rename termRenaming leftBranch)
                       (Term.rename termRenaming rightBranch)
  -- Identity types.  refl carries explicit raw witness.
  | _, _, .refl carrier rawWitness =>
      Term.refl (carrier.rename rho) (rawWitness.rename rho)
  | _, _, .idJ baseCase witness =>
      Term.idJ (Term.rename termRenaming baseCase)
               (Term.rename termRenaming witness)
  | _, _, .oeqRefl carrier rawWitness =>
      Term.oeqRefl (carrier.rename rho) (rawWitness.rename rho)
  | _, _, .oeqJ baseCase witness =>
      Term.oeqJ (Term.rename termRenaming baseCase)
                (Term.rename termRenaming witness)
  | _, _, .oeqFunext domainType codomainType
      leftFunctionRaw rightFunctionRaw pointwiseProof =>
      Term.oeqFunext (domainType.rename rho) (codomainType.rename rho)
        (leftFunctionRaw.rename rho) (rightFunctionRaw.rename rho)
        (Term.rename termRenaming pointwiseProof)
  | _, _, .idStrictRefl carrier rawWitness =>
      Term.idStrictRefl (carrier.rename rho) (rawWitness.rename rho)
  | _, _, .idStrictRec baseCase witness =>
      Term.idStrictRec (Term.rename termRenaming baseCase)
                       (Term.rename termRenaming witness)
  -- Modal: Layer 1 scaffolding preserves innerType.
  | _, _, .modIntro innerTerm =>
      Term.modIntro (Term.rename termRenaming innerTerm)
  | _, _, .modElim innerTerm =>
      Term.modElim (Term.rename termRenaming innerTerm)
  | _, _, .subsume innerTerm =>
      Term.subsume (Term.rename termRenaming innerTerm)
  -- Cubical path fragment.
  | _, _, .interval0 => Term.interval0
  | _, _, .interval1 => Term.interval1
  | _, _, .intervalOpp innerValue =>
      Term.intervalOpp (Term.rename termRenaming innerValue)
  | _, _, .intervalMeet leftValue rightValue =>
      Term.intervalMeet (Term.rename termRenaming leftValue)
                        (Term.rename termRenaming rightValue)
  | _, _, .intervalJoin leftValue rightValue =>
      Term.intervalJoin (Term.rename termRenaming leftValue)
                        (Term.rename termRenaming rightValue)
  | _, _, .pathLam carrierType leftEndpoint rightEndpoint body =>
      Term.pathLam (carrierType.rename rho)
        (leftEndpoint.rename rho)
        (rightEndpoint.rename rho)
        (Ty.weaken_rename_commute rho carrierType ▸
          Term.rename (termRenaming.lift Ty.interval) body)
  | _, _, .pathApp pathTerm intervalTerm =>
      Term.pathApp (Term.rename termRenaming pathTerm)
                   (Term.rename termRenaming intervalTerm)
  | _, _, .glueIntro baseType boundaryWitness baseValue partialValue =>
      Term.glueIntro (baseType.rename rho)
        (boundaryWitness.rename rho)
        (Term.rename termRenaming baseValue)
        (Term.rename termRenaming partialValue)
  | _, _, .glueElim gluedValue =>
      Term.glueElim (Term.rename termRenaming gluedValue)
  | _, _, .transp universeLevel universeLevelLt sourceType targetType
      sourceTypeRaw targetTypeRaw typePath sourceValue =>
      Term.transp universeLevel universeLevelLt
        (sourceType.rename rho)
        (targetType.rename rho)
        (sourceTypeRaw.rename rho)
        (targetTypeRaw.rename rho)
        (Term.rename termRenaming typePath)
        (Term.rename termRenaming sourceValue)
  | _, _, .hcomp sidesValue capValue =>
      Term.hcomp (Term.rename termRenaming sidesValue)
                 (Term.rename termRenaming capValue)
  | _, _, .recordIntro firstField =>
      Term.recordIntro (Term.rename termRenaming firstField)
  | _, _, .recordProj recordValue =>
      Term.recordProj (Term.rename termRenaming recordValue)
  | _, _, .refineIntro predicate baseValue predicateProof =>
      Term.refineIntro (predicate.rename rho.lift)
        (Term.rename termRenaming baseValue)
        (Term.rename termRenaming predicateProof)
  | _, _, .refineElim refinedValue =>
      Term.refineElim (Term.rename termRenaming refinedValue)
  | _, _, .codataUnfold initialState transition =>
      Term.codataUnfold (Term.rename termRenaming initialState)
                        (Term.rename termRenaming transition)
  | _, _, .codataDest codataValue =>
      Term.codataDest (Term.rename termRenaming codataValue)
  | _, _, .sessionSend protocolStep channel payload =>
      Term.sessionSend (protocolStep.rename rho)
        (Term.rename termRenaming channel)
        (Term.rename termRenaming payload)
  | _, _, .sessionRecv channel =>
      Term.sessionRecv (Term.rename termRenaming channel)
  | _, _, .effectPerform effectTag operationTag arguments =>
      Term.effectPerform (effectTag.rename rho)
        (Term.rename termRenaming operationTag)
        (Term.rename termRenaming arguments)
  -- Universe-code: scope-polymorphic.  Both `Ty.universe outerLevel
  -- levelLe` and `RawTerm.universeCode innerLevel.toNat` rename to
  -- themselves (no scope-dependent payload), so the `someType.rename
  -- rho` and `raw.rename rho` results match the ctor's expected types
  -- definitionally.
  | _, _, .universeCode innerLevel outerLevel cumulOk levelLe =>
      Term.universeCode innerLevel outerLevel cumulOk levelLe
  -- Cumul-up (REAL cumul ctor) — Phase CUMUL-2.6 Design D.  Single
  -- context throughout, schematic codeRaw, output wrapped in
  -- cumulUpMarker.  Since the inner typed source term lives at the
  -- SAME scope/context as the outer (Design D unification), we
  -- recursively rename the inner typeCode and reconstruct the
  -- cumulUp ctor at the target scope.  The output raw becomes
  -- `RawTerm.cumulUpMarker (codeRaw.rename rho)`, which is
  -- definitionally `(RawTerm.cumulUpMarker codeRaw).rename rho` —
  -- the cumulUpMarker arm of `RawTerm.rename` recurses on inner.
  | _, _, .cumulUp lowerLevel higherLevel
                   cumulMonotone levelLeLow levelLeHigh typeCode =>
      Term.cumulUp (context := targetCtx)
                   lowerLevel higherLevel cumulMonotone
                   levelLeLow levelLeHigh
                   (Term.rename termRenaming typeCode)
  -- HoTT canonical identity equivalence (Phase 12.A.B8.1): renames
  -- structurally; carrier is renamed; the raw-side identity-lambda
  -- shape is constant (no scope-dependent payload beyond Fin 0
  -- positions which are vacuous).
  | _, _, .equivReflId carrier =>
      Term.equivReflId (carrier.rename rho)
  -- HoTT heterogeneous-carrier equivalence introduction (Phase 12.A.B8.5):
  -- carrierA + carrierB rename via `rho`; the two subterms `forward`
  -- and `backward` rename structurally; raw projection is
  -- `RawTerm.equivIntro (forwardRaw.rename rho) (backwardRaw.rename
  -- rho)` which aligns with the ctor's expected raw form.  No type-
  -- equality cast needed because `Ty.equiv` and `Ty.arrow` rename
  -- structurally (no binder shift, no weaken interaction).
  | _, _, .equivIntroHet forward backward =>
      Term.equivIntroHet (Term.rename termRenaming forward)
                         (Term.rename termRenaming backward)
  | _, _, .equivApp equivTerm argumentTerm =>
      Term.equivApp (Term.rename termRenaming equivTerm)
                    (Term.rename termRenaming argumentTerm)
  -- HoTT canonical funext refl-fragment witness (Phase 12.A.B8.2):
  -- carrier types rename via `rho`; the schematic `applyRaw` payload
  -- (at scope+1) renames via `rho.lift`.  The result type involves
  -- `codomainType.weaken.id ...`, which after rename matches the
  -- `funextRefl` ctor's expected type via `Ty.weaken_rename_commute`.
  -- We build the term at `(codomainType.rename rho).weaken.id ...`
  -- via the ctor, then transport the type through the eqn
  -- `(codomainType.rename rho).weaken = codomainType.weaken.rename rho.lift`
  -- using `show` to expose the post-rename shape that needs the cast.
  | _, _, .funextRefl domainType codomainType applyRaw =>
      show Term targetCtx
        (Ty.piTy (domainType.rename rho)
          (Ty.id (codomainType.weaken.rename rho.lift)
            (applyRaw.rename rho.lift) (applyRaw.rename rho.lift)))
        (RawTerm.lam (RawTerm.refl (applyRaw.rename rho.lift))) from
      let codomainEqInverse :
          (codomainType.rename rho).weaken =
            codomainType.weaken.rename rho.lift :=
        (Ty.weaken_rename_commute rho codomainType).symm
      codomainEqInverse ▸
        Term.funextRefl (domainType.rename rho)
                        (codomainType.rename rho)
                        (applyRaw.rename rho.lift)
  -- HoTT canonical Id-typed identity-equivalence proof at the universe
  -- (Phase 12.A.B8.1).  The Ty `Ty.id (Ty.universe innerLevel ...)
  -- carrierRaw carrierRaw` renames carrierRaw via `rho`; the universe
  -- code is constant (no scope dependency).  The raw form is the same
  -- under any rename (only Fin 0 positions appear in the id-lambdas).
  | _, _, .equivReflIdAtId innerLevel innerLevelLt carrier carrierRaw =>
      Term.equivReflIdAtId innerLevel innerLevelLt
                           (carrier.rename rho)
                           (carrierRaw.rename rho)
  -- HoTT canonical Id-typed funext witness at arrow types
  -- (Phase 12.A.B8.2).  The Ty `Ty.id (Ty.arrow domainType codomainType)
  -- (RawTerm.lam (RawTerm.refl applyRaw)) ...` renames structurally:
  -- domainType + codomainType via `rho`; applyRaw at scope+1 via
  -- `rho.lift`; the lambda-refl raw form lifts uniformly.  No type-
  -- equality cast needed since both endpoints inside `Ty.id` use the
  -- same lambda-refl shape and the carrier `Ty.arrow ...` doesn't
  -- involve scope-shifting `weaken`.
  | _, _, .funextReflAtId domainType codomainType applyRaw =>
      Term.funextReflAtId (domainType.rename rho)
                          (codomainType.rename rho)
                          (applyRaw.rename rho.lift)
  -- HoTT heterogeneous-carrier path-from-equivalence (Phase 12.A.B8.5b).
  -- The Ty `Ty.id (Ty.universe innerLevel ...) carrierARaw carrierBRaw`
  -- renames carrierA + carrierB via `rho`, and carrierARaw + carrierBRaw
  -- via `rho`.  The single subterm `equivWitness` recurses structurally;
  -- its raw form `RawTerm.equivIntro forwardRaw backwardRaw` renames
  -- pointwise to `RawTerm.equivIntro (forwardRaw.rename rho)
  -- (backwardRaw.rename rho)` — same shape as the ctor expects after
  -- the recursive call.  No type-equality cast needed since `Ty.equiv`
  -- and `Ty.universe` rename structurally (no binder shift).
  | _, _, .uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw
                      equivWitness =>
      Term.uaIntroHet innerLevel innerLevelLt
                      (carrierARaw.rename rho) (carrierBRaw.rename rho)
                      (Term.rename termRenaming equivWitness)
  -- HoTT heterogeneous-carrier funext-introduction at Id-of-arrow
  -- (Phase 12.A.B8.8).  `Ty.id (Ty.arrow domainType codomainType)
  -- (RawTerm.lam applyARaw) (RawTerm.lam applyBRaw)` renames via `rho`:
  -- domainType + codomainType rename at outer scope; applyARaw + applyBRaw
  -- at scope+1 rename via `rho.lift` (under the lambda binder).  No
  -- subterm to recurse on — funextIntroHet is a VALUE (canonical
  -- heterogeneous-funext witness) just like funextReflAtId.  No
  -- type-equality cast needed since `Ty.id` and `Ty.arrow` are
  -- non-binder carriers (no scope shift).
  | _, _, .funextIntroHet domainType codomainType applyARaw applyBRaw =>
      Term.funextIntroHet (domainType.rename rho)
                          (codomainType.rename rho)
                          (applyARaw.rename rho.lift)
                          (applyBRaw.rename rho.lift)
  -- CUMUL-2.4 typed type-code constructors.  All ten ctors are
  -- VALUE-shaped (schematic raw payloads, no recursive Term
  -- children).  Atom-shape codes rename their raw payloads via
  -- `rho` at the outer scope; binder-shape codes (piTyCode,
  -- sigmaTyCode) thread `rho.lift` through the codomain raw at
  -- `scope + 1`.  Both sides project to the matching
  -- `RawTerm.{X}Code (raw.rename rho) ...` (and `rho.lift` for
  -- binder slot), aligning definitionally with the ctor's expected
  -- raw form.  The `Ty.universe outerLevel levelLe` result type
  -- renames to itself (no scope-dependent payload).
  | _, _, .arrowCode outerLevel levelLe domainCodeRaw codomainCodeRaw =>
      Term.arrowCode outerLevel levelLe
                     (domainCodeRaw.rename rho)
                     (codomainCodeRaw.rename rho)
  | _, _, .piTyCode outerLevel levelLe domainCodeRaw codomainCodeRaw =>
      Term.piTyCode outerLevel levelLe
                    (domainCodeRaw.rename rho)
                    (codomainCodeRaw.rename rho.lift)
  | _, _, .sigmaTyCode outerLevel levelLe domainCodeRaw codomainCodeRaw =>
      Term.sigmaTyCode outerLevel levelLe
                       (domainCodeRaw.rename rho)
                       (codomainCodeRaw.rename rho.lift)
  | _, _, .productCode outerLevel levelLe firstCodeRaw secondCodeRaw =>
      Term.productCode outerLevel levelLe
                       (firstCodeRaw.rename rho)
                       (secondCodeRaw.rename rho)
  | _, _, .sumCode outerLevel levelLe leftCodeRaw rightCodeRaw =>
      Term.sumCode outerLevel levelLe
                   (leftCodeRaw.rename rho)
                   (rightCodeRaw.rename rho)
  | _, _, .listCode outerLevel levelLe elementCodeRaw =>
      Term.listCode outerLevel levelLe (elementCodeRaw.rename rho)
  | _, _, .optionCode outerLevel levelLe elementCodeRaw =>
      Term.optionCode outerLevel levelLe (elementCodeRaw.rename rho)
  | _, _, .eitherCode outerLevel levelLe leftCodeRaw rightCodeRaw =>
      Term.eitherCode outerLevel levelLe
                      (leftCodeRaw.rename rho)
                      (rightCodeRaw.rename rho)
  | _, _, .idCode outerLevel levelLe typeCodeRaw leftRaw rightRaw =>
      Term.idCode outerLevel levelLe
                  (typeCodeRaw.rename rho)
                  (leftRaw.rename rho)
                  (rightRaw.rename rho)
  | _, _, .equivCode outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw =>
      Term.equivCode outerLevel levelLe
                     (leftTypeCodeRaw.rename rho)
                     (rightTypeCodeRaw.rename rho)

/-! ## Term.weaken — convenience wrapper -/

/-- Single-binder weakening on a typed term: lift through one new
binder via the canonical weakening TermRenaming. -/
@[reducible] def Term.weaken {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {someType : Ty level scope}
    {raw : RawTerm scope} (newType : Ty level scope)
    (term : Term context someType raw) :
    Term (context.cons newType) someType.weaken raw.weaken :=
  Term.rename (TermRenaming.weakenStep context newType) term

end LeanFX2
