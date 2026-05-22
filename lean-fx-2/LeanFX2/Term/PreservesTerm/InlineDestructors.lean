import LeanFX2.Term.Inversion

/-! # LeanFX2.Term.PreservesTerm.InlineDestructors

Inline destructors for canonical-head Term values used by the
Tier 3 shallow-β eliminator lifts.  Each destructor mirrors the
shape in `Term/Inversion.lean`, freeing the type index via
`suffices`, then realigning with the matching canonical ctor.

Covers 6 destructors: modIntroDestruct, recordIntroDestruct,
refineIntroDestruct, glueIntroDestruct, lamDestruct,
codataUnfoldDestruct.

## Root status

Zero-axiom; carved from `Term/PreservesTerm.lean`. -/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}


/-! ## Inline destructors for canonical-head Term values

These destructors mirror the ones in `Term/Inversion.lean`
(natSuccDestruct, listConsDestruct, optionSomeDestruct,
eitherInlDestruct, eitherInrDestruct, pairDestruct) for ctors not
yet covered upstream — each follows the suffices/free-the-index
pattern documented in `feedback_lean_free_type_via_suffices.md` to
sidestep the `Ty.X = varType ctx pos` dep-elim wall.

Inline in this file because they're consumed only by the lift
theorems below; promoting to Inversion.lean is a future cleanup. -/

/-- Destructor for `Term.modIntro`: from a typed Term whose raw form
is `RawTerm.modIntro innerRaw`, extract the typed inner. -/
def Term.modIntroDestruct
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (someTerm : Term context innerType (RawTerm.modIntro innerRaw)) :
    Σ' (innerTerm : Term context innerType innerRaw),
       HEq someTerm (Term.modIntro innerTerm) := by
  cases someTerm
  rename_i innerTerm
  exact ⟨innerTerm, HEq.rfl⟩

/-- Destructor for `Term.recordIntro`. -/
def Term.recordIntroDestruct
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    (someTerm :
      Term context (Ty.record singleFieldType) (RawTerm.recordIntro firstRaw)) :
    Σ' (firstField : Term context singleFieldType firstRaw),
       HEq someTerm (Term.recordIntro firstField) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.recordIntro firstRaw)),
        someType = Ty.record singleFieldType →
        Σ' (firstField : Term context singleFieldType firstRaw),
           HEq genericTerm (Term.recordIntro firstField) by
    exact key someTerm rfl
  intro someType genericTerm someTypeIsRecord
  cases genericTerm
  rename_i innerSingleField firstField
  have singleFieldEq : innerSingleField = singleFieldType :=
    Ty.record.inj someTypeIsRecord
  cases singleFieldEq
  exact ⟨firstField, HEq.rfl⟩

/-- Destructor for `Term.refineIntro`. -/
def Term.refineIntroDestruct
    {baseType : Ty level scope}
    (predicate : RawTerm (scope + 1))
    {valueRaw proofRaw : RawTerm scope}
    (someTerm :
      Term context (Ty.refine baseType predicate)
        (RawTerm.refineIntro valueRaw proofRaw)) :
    Σ' (baseValue : Term context baseType valueRaw)
       (predicateProof : Term context Ty.unit proofRaw),
       HEq someTerm (Term.refineIntro predicate baseValue predicateProof) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType (RawTerm.refineIntro valueRaw proofRaw)),
        someType = Ty.refine baseType predicate →
        Σ' (baseValue : Term context baseType valueRaw)
           (predicateProof : Term context Ty.unit proofRaw),
           HEq genericTerm (Term.refineIntro predicate baseValue predicateProof) by
    exact key someTerm rfl
  intro someType genericTerm someTypeIsRefine
  cases genericTerm
  rename_i innerBase innerPredicate baseValue predicateProof
  have refineEq := Ty.refine.inj someTypeIsRefine
  cases refineEq.1
  cases refineEq.2
  exact ⟨baseValue, predicateProof, HEq.rfl⟩

/-- Destructor for `Term.glueIntro`. -/
def Term.glueIntroDestruct
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level scope)
    (boundaryWitness : RawTerm scope)
    {baseRaw partialRaw : RawTerm scope}
    (someTerm :
      Term context (Ty.glue baseType boundaryWitness)
        (RawTerm.glueIntro baseRaw partialRaw)) :
    Σ' (baseValue : Term context baseType baseRaw)
       (partialValue : Term context baseType partialRaw),
       HEq someTerm
            (Term.glueIntro modeIsUnivalent baseType boundaryWitness baseValue
                            partialValue) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType (RawTerm.glueIntro baseRaw partialRaw)),
        someType = Ty.glue baseType boundaryWitness →
        Σ' (baseValue : Term context baseType baseRaw)
           (partialValue : Term context baseType partialRaw),
           HEq genericTerm
                (Term.glueIntro modeIsUnivalent baseType boundaryWitness baseValue
                                partialValue) by
    exact key someTerm rfl
  intro someType genericTerm someTypeIsGlue
  cases genericTerm
  rename_i innerMode innerBase innerBoundary baseValue partialValue
  have glueEq := Ty.glue.inj someTypeIsGlue
  cases glueEq.1
  cases glueEq.2
  exact ⟨baseValue, partialValue, HEq.rfl⟩

/-- Destructor for `Term.lam` (non-dep arrow).  Disambiguated from
`Term.lamPi`, `Term.funextRefl`, `Term.funextReflAtId`, and
`Term.funextIntroHet` (all with raw `RawTerm.lam ...`) by the fixed
`Ty.arrow` source-type index — the latter three have `Ty.id` or
`Ty.piTy` shaped types. -/
def Term.lamDestruct
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    (someTerm :
      Term context (Ty.arrow domainType codomainType) (RawTerm.lam bodyRaw)) :
    Σ' (body : Term (context.cons domainType) codomainType.weaken bodyRaw),
       HEq someTerm (Term.lam (codomainType := codomainType) body) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.lam bodyRaw)),
        someType = Ty.arrow domainType codomainType →
        Σ' (body : Term (context.cons domainType) codomainType.weaken bodyRaw),
           HEq genericTerm (Term.lam (codomainType := codomainType) body) by
    exact key someTerm rfl
  intro someType genericTerm someTypeIsArrow
  cases genericTerm
  case lam innerDomain innerCodomain body =>
    have arrowEq := Ty.arrow.inj someTypeIsArrow
    cases arrowEq.1
    cases arrowEq.2
    exact ⟨body, HEq.rfl⟩
  case lamPi innerDomain innerCodomain body =>
    -- Ty.piTy ≠ Ty.arrow shape mismatch
    nomatch someTypeIsArrow
  case funextRefl _ _ _ => nomatch someTypeIsArrow
  case funextReflAtId _ _ _ => nomatch someTypeIsArrow
  case funextIntroHet _ _ _ _ => nomatch someTypeIsArrow

/-- Disjunctive destructor for `Term ctx (Ty.piTy A B) (RawTerm.lam _)`:
exactly two inhabitants under this index pair — generic `Term.lamPi body`
or the special funextRefl shape `Term.funextRefl A B' applyRaw` where
`B = Ty.id B'.weaken applyRaw applyRaw` and body = `RawTerm.refl applyRaw`.

The other Term ctors producing `RawTerm.lam _` raw projections are
either typed at `Ty.arrow` (`Term.lam`) or at `Ty.id (Ty.arrow ...)`
(`Term.funextReflAtId`, `Term.funextIntroHet`) — all refuted by the
type index via `Ty` constructor injectivity / mismatch.

Consumed by `RawStep.par.lift_full_appPi` to discharge the typed
β-deep arm: when `Term.appPi functionTerm argumentTerm` reduces via
`RawStep.par.betaApp`, the lifted `functionCanonical` shape is
exactly the `Ty.piTy + RawTerm.lam` collision point this destructor
resolves. -/
def Term.lamPi_or_funextRefl_destruct
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    (someTerm :
      Term context (Ty.piTy domainType codomainType) (RawTerm.lam bodyRaw)) :
    PSum
      (Σ' (body : Term (context.cons domainType) codomainType bodyRaw),
          HEq someTerm
              (Term.lamPi (context := context)
                          (codomainType := codomainType) body))
      (Σ' (codomainBase : Ty level scope)
          (applyRaw : RawTerm (scope + 1))
          (_codomainEq :
            codomainType = Ty.id codomainBase.weaken applyRaw applyRaw)
          (_bodyEq : bodyRaw = RawTerm.refl applyRaw),
          HEq someTerm
              (Term.funextRefl (context := context)
                                domainType codomainBase applyRaw)) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.lam bodyRaw)),
        someType = Ty.piTy domainType codomainType →
        PSum
          (Σ' (body : Term (context.cons domainType) codomainType bodyRaw),
              HEq genericTerm
                  (Term.lamPi (context := context)
                              (codomainType := codomainType) body))
          (Σ' (codomainBase : Ty level scope)
              (applyRaw : RawTerm (scope + 1))
              (_codomainEq :
                codomainType = Ty.id codomainBase.weaken applyRaw applyRaw)
              (_bodyEq : bodyRaw = RawTerm.refl applyRaw),
              HEq genericTerm
                  (Term.funextRefl (context := context)
                                    domainType codomainBase applyRaw)) by
    exact key someTerm rfl
  intro someType genericTerm someTypeIsPiTy
  cases genericTerm
  case lam _innerDomain _innerCodomain _body =>
    nomatch someTypeIsPiTy
  case lamPi innerDomain innerCodomain body =>
    have piEq := Ty.piTy.inj someTypeIsPiTy
    cases piEq.1
    cases piEq.2
    exact PSum.inl ⟨body, HEq.rfl⟩
  case funextRefl innerDomain innerCodomain applyRaw =>
    -- ctor type: Ty.piTy innerDomain (Ty.id innerCodomain.weaken applyRaw applyRaw)
    have piEq := Ty.piTy.inj someTypeIsPiTy
    cases piEq.1
    exact PSum.inr ⟨innerCodomain, applyRaw, piEq.2.symm, rfl, HEq.rfl⟩
  case funextReflAtId _ _ _ => nomatch someTypeIsPiTy
  case funextIntroHet _ _ _ _ => nomatch someTypeIsPiTy

/-- Destructor for `Term.codataUnfold`. -/
def Term.codataUnfoldDestruct
    {stateType outputType : Ty level scope}
    {stateRaw transitionRaw : RawTerm scope}
    (someTerm :
      Term context (Ty.codata stateType outputType)
        (RawTerm.codataUnfold stateRaw transitionRaw)) :
    Σ' (initialState : Term context stateType stateRaw)
       (transition : Term context (Ty.arrow stateType outputType) transitionRaw),
       HEq someTerm (Term.codataUnfold initialState transition) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType (RawTerm.codataUnfold stateRaw transitionRaw)),
        someType = Ty.codata stateType outputType →
        Σ' (initialState : Term context stateType stateRaw)
           (transition : Term context (Ty.arrow stateType outputType) transitionRaw),
           HEq genericTerm (Term.codataUnfold initialState transition) by
    exact key someTerm rfl
  intro someType genericTerm someTypeIsCodata
  cases genericTerm
  rename_i innerState innerOutput initialState transition
  have codataEq := Ty.codata.inj someTypeIsCodata
  cases codataEq.1
  cases codataEq.2
  exact ⟨initialState, transition, HEq.rfl⟩

end LeanFX2
