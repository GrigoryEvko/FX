import LeanFX2.Algo.Progress.Headline.Prelude

namespace LeanFX2

variable {mode : Mode} {level scope : Nat}

/-- Algo-layer destructor for `Term.refl` at an identity type
`Ty.id carrier leftEndpoint rightEndpoint` with raw form
`RawTerm.refl witnessRaw`.  `Term.refl` produces type
`Ty.id carrier rawWitness rawWitness` — both endpoints equal the
raw witness — so destructuring forces `leftEndpoint = witnessRaw`
and `rightEndpoint = witnessRaw` plus an HEq witness aligning
`someTerm` with the canonical `Term.refl carrier witnessRaw`.

Inlined here to avoid importing `Term.PreservesTerm.BetaCastWallDemolition`
(which lives at a later layer pulling in `Reduction.ParRed`).
Pattern follows `Term.idReflDestruct`; both definitions are
byte-equivalent except for the name. -/
def Term.idReflDestructAlgo {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {witnessRaw : RawTerm scope}
    (someTerm :
      Term context (Ty.id carrier leftEndpoint rightEndpoint)
                   (RawTerm.refl witnessRaw)) :
    Σ' (_leftEqWitness : leftEndpoint = witnessRaw)
       (_rightEqWitness : rightEndpoint = witnessRaw),
       HEq someTerm (Term.refl (context := context) carrier witnessRaw) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.refl witnessRaw)),
        someType = Ty.id carrier leftEndpoint rightEndpoint →
        Σ' (leftEqWitness : leftEndpoint = witnessRaw)
           (rightEqWitness : rightEndpoint = witnessRaw),
           HEq genericTerm
                (Term.refl (context := context) carrier witnessRaw) by
    exact key someTerm rfl
  intro someType genericTerm someTypeIsId
  cases genericTerm
  rename_i innerCarrier
  have idEq := Ty.id.inj someTypeIsId
  cases idEq.1
  exact ⟨idEq.2.1.symm, idEq.2.2.symm, HEq.rfl⟩

/-- Focused progress theorem for the `Term.idJ` head (HoTT
identity-type J).  Every well-typed `idJ`-headed term is either
in WHNF (when the witness position is not a `refl`) or takes a
ι-step (when the witness IS a `refl`).

M05.D.2 conditional eliminator #12 of 17.  Endpoint-equality
complication: `Term.refl carrier rawWitness` has type
`Ty.id carrier rawWitness rawWitness`, so the outer
`leftEndpoint, rightEndpoint` get forced equal to the refl's
raw witness via `Ty.id.inj` inside `Term.idReflDestructAlgo`.
After substituting both endpoints via the returned `Eq` witnesses
and rewriting `witness` through the HEq, `Step.iotaIdJRefl` fires
producing `baseCase` as the contractum. -/
theorem Term.idJ_progress_or_step
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    (witness :
      Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw) :
    Term.isWHNF (Term.idJ baseCase witness) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.idJ baseCase witness) target := by
  cases h : witness.headCtor with
  | refl =>
      obtain ⟨reflRaw, rawEq⟩ := Term.headCtor_refl_raw witness h
      cases rawEq
      obtain ⟨leftEqRefl, rightEqRefl, witnessHeq⟩ :=
        Term.idReflDestructAlgo witness
      -- leftEqRefl : leftEndpoint = reflRaw, rightEqRefl : rightEndpoint = reflRaw.
      -- `cases` substitutes the later-introduced binder (reflRaw) into the
      -- earlier ones, so reflRaw is consumed and both endpoints survive.
      -- Pass `leftEndpoint` to iotaIdJRefl; rightEndpoint then matches via
      -- the second cases substitution.
      cases leftEqRefl
      cases rightEqRefl
      have witnessEq := eq_of_heq witnessHeq
      rw [witnessEq]
      exact Or.inr
        ⟨_, _, _, Step.iotaIdJRefl carrier leftEndpoint baseCase⟩
  | var =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | unit =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | lam =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | app =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | lamPi =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | appPi =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | pair =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | fst =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | snd =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | boolTrue =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | boolFalse =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | boolElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | natZero =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | natSucc =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | natElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | natRec =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listNil =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listCons =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionNone =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionSome =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionMatch =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherInl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherInr =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherMatch =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idJ =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | oeqRefl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | oeqJ =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | oeqFunext =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idStrictRefl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idStrictRec =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | modIntro =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | modElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | subsume =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | interval0 =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | interval1 =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | intervalOpp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | intervalMeet =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | intervalJoin =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | pathLam =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | pathApp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | glueIntro =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | glueElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | transp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | hcomp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | recordIntro =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | recordProj =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | refineIntro =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | refineElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | codataUnfold =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | codataDest =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sessionSend =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sessionRecv =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | effectPerform =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | universeCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | cumulUp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivReflId =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | funextRefl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivReflIdAtId =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | funextReflAtId =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivIntroHet =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivApp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | uaIntroHet =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | funextIntroHet =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | uaToEquiv =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivApply =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | arrowCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | piTyCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sigmaTyCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | productCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sumCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide


end LeanFX2
