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
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | unit =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lam =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | app =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lamPi =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | appPi =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | pair =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | fst =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | snd =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | boolTrue =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | boolFalse =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | boolElim =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natZero =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natSucc =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natElim =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natRec =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listNil =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listCons =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listElim =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionNone =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionSome =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionMatch =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherInl =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherInr =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherMatch =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idJ =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | oeqRefl =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | oeqJ =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | oeqFunext =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idStrictRefl =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idStrictRec =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | modIntro =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | modElim =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | subsume =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | interval0 =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | interval1 =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | intervalOpp =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | intervalMeet =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | intervalJoin =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | pathLam =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | pathApp =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | glueIntro =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | glueElim =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | transp =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | hcomp =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | recordIntro =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | recordProj =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | refineIntro =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | refineElim =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | codataUnfold =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | codataDest =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sessionSend =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sessionRecv =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | effectPerform =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | universeCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | cumulUp =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivReflId =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | funextRefl =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivReflIdAtId =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | funextReflAtId =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivIntroHet =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApp =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | uaIntroHet =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | funextIntroHet =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | uaToEquiv =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApply =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | arrowCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | piTyCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sigmaTyCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | productCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sumCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl


end LeanFX2
