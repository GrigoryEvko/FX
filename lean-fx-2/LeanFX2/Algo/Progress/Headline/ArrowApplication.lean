import LeanFX2.Algo.Progress.Headline.Prelude


namespace LeanFX2

variable {mode : Mode} {level scope : Nat}

/-! ## Local destructor for non-dep λ

`Term.lamDestructAlgo` is the Algo-layer copy of
`Term.lamDestruct` (which lives in `Term/PreservesTerm.lean`).
Inlined here to avoid importing PreservesTerm — that module
imports `Reduction.ParRed` (a later layer), so pulling it into
Algo would violate the production import-surface gate.

The two definitions are byte-equivalent except for the name.
Both are zero-axiom under strict policy via the suffices/free-
index pattern from `feedback_lean_free_type_via_suffices.md`. -/

/-- Algo-layer destructor for `Term.lam` (non-dep arrow).
Disambiguated from `Term.lamPi`, `Term.funextRefl`,
`Term.funextReflAtId`, and `Term.funextIntroHet` (all with raw
`RawTerm.lam ...`) by the fixed `Ty.arrow` source-type index —
the latter four have `Ty.id` or `Ty.piTy` shaped types.

Used by `Term.app_progress_or_step` to extract the typed body
of the `Term.lam` form when the function position of an `app`
node is itself a lambda.  Zero-axiom via the suffices/free-
index pattern (mirrors `Term.lamDestruct` in
`Term/PreservesTerm.lean`). -/
def Term.lamDestructAlgo {context : Ctx mode level scope}
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
    nomatch someTypeIsArrow
  case funextRefl _ _ _ => nomatch someTypeIsArrow
  case funextReflAtId _ _ _ => nomatch someTypeIsArrow
  case funextIntroHet _ _ _ _ => nomatch someTypeIsArrow

/-- Focused progress theorem for the `Term.app` head.  Every
non-dep `app`-headed term is either in WHNF (when the function
position is not a `lam`) or takes a β-step (when the function
position IS a `lam`).

Reference pattern for the remaining 16 conditional eliminators
of the full `Term.progress_or_step` headline.  Uses
`Term.headCtor_lam_raw` (M05.A.1) for the canonical-form raw
inversion and `Term.lamDestruct` (Term/PreservesTerm.lean) for
the typed body extraction; the canonical case fires
`Step.betaApp` from M05.B.1.1.

Zero-axiom under strict policy: full 75-case enumeration on
`functionTerm.headCtor` with each non-`.lam` case discharged
by `simp only [Term.isWHNF, h]; rfl` (definitional reduction
of the WHNF predicate). -/
theorem Term.app_progress_or_step
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionRaw argumentRaw : RawTerm scope}
    (functionTerm :
      Term context (Ty.arrow domainType codomainType) functionRaw)
    (argumentTerm : Term context domainType argumentRaw) :
    Term.isWHNF (Term.app functionTerm argumentTerm) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.app functionTerm argumentTerm) target := by
  cases h : functionTerm.headCtor with
  | lam =>
      obtain ⟨bodyRaw, rawEq⟩ := Term.headCtor_lam_raw functionTerm h
      cases rawEq
      obtain ⟨body, bodyHeq⟩ := Term.lamDestructAlgo functionTerm
      have bodyEq := eq_of_heq bodyHeq
      rw [bodyEq]
      exact Or.inr ⟨_, _, _, Step.betaApp body argumentTerm⟩
  | var =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | unit =>
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
  | refl =>
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
