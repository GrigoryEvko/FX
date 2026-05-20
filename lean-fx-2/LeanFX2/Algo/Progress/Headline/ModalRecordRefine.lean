import LeanFX2.Algo.Progress.Headline.Prelude

namespace LeanFX2

variable {mode : Mode} {level scope : Nat}

/-- Algo-layer destructor for `Term.modIntro` (modal intro).
Given a term whose `headCtor` is `.modIntro` and whose raw form
is `RawTerm.modIntro innerRaw`, extracts the inner typed term
plus an HEq witness.  Used by `Term.modElim_progress_or_step`
to rewrite the inner position of a `modElim` to a literal
`Term.modIntro` form so `Step.betaModElimIntro` can fire. -/
def Term.modIntroDestructAlgo {context : Ctx mode level scope}
    {innerType : Ty level scope} {innerRaw : RawTerm scope}
    (someTerm : Term context innerType (RawTerm.modIntro innerRaw))
    (headEq : someTerm.headCtor = Term.HeadCtor.modIntro) :
    Σ' (innerTerm : Term context innerType innerRaw),
       HEq someTerm (Term.modIntro innerTerm) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.modIntro innerRaw))
        (sTyEq : someType = innerType)
        (hcEq : genericTerm.headCtor = Term.HeadCtor.modIntro),
        Σ' (innerTerm : Term context innerType innerRaw),
           HEq genericTerm (Term.modIntro innerTerm) by
    exact key someTerm rfl headEq
  intro someType genericTerm sTyEq hcEq
  cases genericTerm
  case modIntro innerTermVal =>
    cases sTyEq
    exact ⟨innerTermVal, HEq.rfl⟩

/-- Focused progress theorem for the `Term.modElim` head (modal
elimination).  Every well-typed `modElim`-headed term is either
in WHNF (when the inner position is not a `modIntro`) or takes
a β-step (when the inner IS a `modIntro`).

M05.D.2 conditional eliminator #5 of 17.  Same template as
`Term.app_progress_or_step` but with `modElim`-shaped firing
via `Step.betaModElimIntro` and `Term.modIntroDestructAlgo`
for the typed inner-term extraction. -/
theorem Term.modElim_progress_or_step
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw) :
    Term.isWHNF (Term.modElim innerTerm) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.modElim innerTerm) target := by
  cases h : innerTerm.headCtor with
  | modIntro =>
      obtain ⟨innerInnerRaw, rawEq⟩ := Term.headCtor_modIntro_raw innerTerm h
      cases rawEq
      obtain ⟨innerInner, innerHeq⟩ := Term.modIntroDestructAlgo innerTerm h
      have innerEq := eq_of_heq innerHeq
      rw [innerEq]
      exact Or.inr ⟨_, _, _, Step.betaModElimIntro innerInner⟩
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

/-- Algo-layer destructor for `Term.recordIntro`.  Extracts the
single field of a record introduction term when its `headCtor`
is `.recordIntro`.  Used by `Term.recordProj_progress_or_step`
to enable `Step.betaRecordProjIntro` firing. -/
def Term.recordIntroDestructAlgo {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    (someTerm : Term context (Ty.record singleFieldType)
                  (RawTerm.recordIntro firstRaw))
    (headEq : someTerm.headCtor = Term.HeadCtor.recordIntro) :
    Σ' (firstField : Term context singleFieldType firstRaw),
       HEq someTerm (Term.recordIntro firstField) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.recordIntro firstRaw))
        (sTyEq : someType = Ty.record singleFieldType)
        (hcEq : genericTerm.headCtor = Term.HeadCtor.recordIntro),
        Σ' (firstField : Term context singleFieldType firstRaw),
           HEq genericTerm (Term.recordIntro firstField) by
    exact key someTerm rfl headEq
  intro someType genericTerm sTyEq hcEq
  cases genericTerm
  case recordIntro firstFieldVal =>
    cases Ty.record.inj sTyEq
    exact ⟨firstFieldVal, HEq.rfl⟩

/-- Focused progress theorem for the `Term.recordProj` head.
M05.D.2 conditional eliminator #6 of 17.  Fires
`Step.betaRecordProjIntro` when the record head is
`.recordIntro`, otherwise WHNF. -/
theorem Term.recordProj_progress_or_step
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {recordRaw : RawTerm scope}
    (recordValue :
      Term context (Ty.record singleFieldType) recordRaw) :
    Term.isWHNF (Term.recordProj recordValue) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.recordProj recordValue) target := by
  cases h : recordValue.headCtor with
  | recordIntro =>
      obtain ⟨innerFirstRaw, rawEq⟩ := Term.headCtor_recordIntro_raw recordValue h
      cases rawEq
      obtain ⟨firstField, fieldHeq⟩ := Term.recordIntroDestructAlgo recordValue h
      have fieldEq := eq_of_heq fieldHeq
      rw [fieldEq]
      exact Or.inr ⟨_, _, _, Step.betaRecordProjIntro firstField⟩
  | var => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | unit => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | lam => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | app => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | lamPi => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | appPi => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | pair => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | fst => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | snd => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | boolTrue => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | boolFalse => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | boolElim => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | natZero => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | natSucc => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | natElim => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | natRec => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listNil => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listCons => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listElim => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionNone => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionSome => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionMatch => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherInl => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherInr => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherMatch => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | refl => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idJ => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | oeqRefl => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | oeqJ => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | oeqFunext => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idStrictRefl => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idStrictRec => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | modIntro => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | modElim => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | subsume => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | interval0 => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | interval1 => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | intervalOpp => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | intervalMeet => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | intervalJoin => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | pathLam => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | pathApp => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | glueIntro => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | glueElim => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | transp => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | hcomp => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | recordProj => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | refineIntro => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | refineElim => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | codataUnfold => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | codataDest => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sessionSend => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sessionRecv => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | effectPerform => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | universeCode => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | cumulUp => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivReflId => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | funextRefl => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivReflIdAtId => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | funextReflAtId => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivIntroHet => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivApp => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | uaIntroHet => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | funextIntroHet => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | uaToEquiv => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivApply => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | arrowCode => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | piTyCode => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sigmaTyCode => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | productCode => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sumCode => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listCode => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionCode => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherCode => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idCode => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivCode => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide

/-- Algo-layer destructor for `Term.refineIntro`.  Extracts the
base value, predicate proof, and HEq witness when `headCtor`
is `.refineIntro`.  Used by `Term.refineElim_progress_or_step`
to enable `Step.betaRefineElimIntro` firing. -/
def Term.refineIntroDestructAlgo {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {valueRaw proofRaw : RawTerm scope}
    (someTerm : Term context (Ty.refine baseType predicate)
                  (RawTerm.refineIntro valueRaw proofRaw))
    (headEq : someTerm.headCtor = Term.HeadCtor.refineIntro) :
    Σ' (baseValue : Term context baseType valueRaw)
       (predicateProof : Term context Ty.unit proofRaw),
       HEq someTerm
         (Term.refineIntro predicate baseValue predicateProof) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType (RawTerm.refineIntro valueRaw proofRaw))
        (sTyEq : someType = Ty.refine baseType predicate)
        (hcEq : genericTerm.headCtor = Term.HeadCtor.refineIntro),
        Σ' (baseValue : Term context baseType valueRaw)
           (predicateProof : Term context Ty.unit proofRaw),
           HEq genericTerm
             (Term.refineIntro predicate baseValue predicateProof) by
    exact key someTerm rfl headEq
  intro someType genericTerm sTyEq hcEq
  cases genericTerm
  case refineIntro predicateBound baseValueBound predicateProofBound =>
    have refineEq := Ty.refine.inj sTyEq
    cases refineEq.1
    cases refineEq.2
    exact ⟨baseValueBound, predicateProofBound, HEq.rfl⟩

/-- Focused progress theorem for the `Term.refineElim` head.
M05.D.2 conditional eliminator #7 of 17.  Fires
`Step.betaRefineElimIntro` when the refined head is
`.refineIntro`, otherwise WHNF. -/
theorem Term.refineElim_progress_or_step
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {refinedRaw : RawTerm scope}
    (refinedValue :
      Term context (Ty.refine baseType predicate) refinedRaw) :
    Term.isWHNF (Term.refineElim refinedValue) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.refineElim refinedValue) target := by
  cases h : refinedValue.headCtor with
  | refineIntro =>
      obtain ⟨innerValueRaw, innerProofRaw, rawEq⟩ :=
        Term.headCtor_refineIntro_raw refinedValue h
      cases rawEq
      obtain ⟨baseValue, predicateProof, refinedHeq⟩ :=
        Term.refineIntroDestructAlgo refinedValue h
      have refinedEq := eq_of_heq refinedHeq
      rw [refinedEq]
      exact Or.inr ⟨_, _, _,
        Step.betaRefineElimIntro predicate baseValue predicateProof⟩
  | var => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | unit => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | lam => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | app => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | lamPi => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | appPi => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | pair => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | fst => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | snd => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | boolTrue => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | boolFalse => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | boolElim => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | natZero => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | natSucc => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | natElim => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | natRec => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listNil => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listCons => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listElim => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionNone => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionSome => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionMatch => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherInl => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherInr => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherMatch => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | refl => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idJ => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | oeqRefl => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | oeqJ => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | oeqFunext => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idStrictRefl => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idStrictRec => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | modIntro => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | modElim => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | subsume => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | interval0 => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | interval1 => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | intervalOpp => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | intervalMeet => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | intervalJoin => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | pathLam => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | pathApp => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | glueIntro => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | glueElim => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | transp => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | hcomp => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | recordIntro => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | recordProj => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | refineElim => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | codataUnfold => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | codataDest => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sessionSend => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sessionRecv => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | effectPerform => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | universeCode => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | cumulUp => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivReflId => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | funextRefl => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivReflIdAtId => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | funextReflAtId => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivIntroHet => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivApp => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | uaIntroHet => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | funextIntroHet => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | uaToEquiv => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivApply => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | arrowCode => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | piTyCode => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sigmaTyCode => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | productCode => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sumCode => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listCode => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionCode => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherCode => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idCode => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivCode => apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide


end LeanFX2
