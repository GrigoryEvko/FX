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
  | refl =>
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
  | var => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | unit => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lam => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | app => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lamPi => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | appPi => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | pair => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | fst => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | snd => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | boolTrue => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | boolFalse => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | boolElim => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natZero => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natSucc => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natElim => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natRec => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listNil => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listCons => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listElim => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionNone => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionSome => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionMatch => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherInl => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherInr => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherMatch => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | refl => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idJ => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | oeqRefl => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | oeqJ => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | oeqFunext => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idStrictRefl => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idStrictRec => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | modIntro => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | modElim => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | subsume => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | interval0 => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | interval1 => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | intervalOpp => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | intervalMeet => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | intervalJoin => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | pathLam => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | pathApp => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | glueIntro => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | glueElim => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | transp => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | hcomp => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | recordProj => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | refineIntro => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | refineElim => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | codataUnfold => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | codataDest => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sessionSend => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sessionRecv => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | effectPerform => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | universeCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | cumulUp => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivReflId => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | funextRefl => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivReflIdAtId => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | funextReflAtId => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivIntroHet => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApp => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | uaIntroHet => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | funextIntroHet => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | uaToEquiv => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApply => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | arrowCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | piTyCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sigmaTyCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | productCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sumCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl

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
  | var => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | unit => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lam => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | app => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lamPi => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | appPi => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | pair => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | fst => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | snd => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | boolTrue => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | boolFalse => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | boolElim => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natZero => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natSucc => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natElim => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natRec => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listNil => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listCons => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listElim => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionNone => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionSome => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionMatch => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherInl => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherInr => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherMatch => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | refl => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idJ => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | oeqRefl => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | oeqJ => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | oeqFunext => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idStrictRefl => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idStrictRec => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | modIntro => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | modElim => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | subsume => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | interval0 => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | interval1 => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | intervalOpp => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | intervalMeet => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | intervalJoin => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | pathLam => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | pathApp => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | glueIntro => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | glueElim => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | transp => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | hcomp => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | recordIntro => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | recordProj => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | refineElim => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | codataUnfold => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | codataDest => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sessionSend => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sessionRecv => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | effectPerform => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | universeCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | cumulUp => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivReflId => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | funextRefl => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivReflIdAtId => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | funextReflAtId => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivIntroHet => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApp => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | uaIntroHet => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | funextIntroHet => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | uaToEquiv => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApply => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | arrowCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | piTyCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sigmaTyCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | productCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sumCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl


end LeanFX2
