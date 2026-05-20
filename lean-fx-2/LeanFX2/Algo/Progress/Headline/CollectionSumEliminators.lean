import LeanFX2.Algo.Progress.Headline.Prelude

namespace LeanFX2

variable {mode : Mode} {level scope : Nat}

/-! ## Parametric-canonical uniqueness helpers

The four parametric nullary canonical introducers — `listNil`,
`optionNone`, `eitherInl`-style and `eitherInr`-style — are not
uniquely determined by their raw projection alone: each carries
implicit type parameters (elementType for list/option;
leftType/rightType for either) that the destructor needs to align.
The helpers below specialize `Term.<X>_unique` from
`Term/Inversion.lean` to the case where both terms live at the
SAME parametric type, freeing the index via `suffices` and
realigning with the relevant `Ty.<X>.inj` injectivity lemma.

Identical in shape to the `_sameType` companions in
`Algo/Soundness.lean:142-188`; reinlined here because
`Algo.Soundness` depends transitively on `Algo.Progress.Headline`
(via `Algo.Eval`), so we cannot import it without creating a
cycle.  Each ships zero-axiom under the matcher rules cited
in `feedback_lean_free_type_via_suffices.md`. -/

/-- Strong listNil uniqueness when both terms are at the SAME
element type. -/
theorem Term.listNil_unique_sameType
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    (firstNil secondNil :
      Term context (Ty.listType elementType) RawTerm.listNil) :
    HEq firstNil secondNil := by
  suffices key : ∀ {firstType secondType : Ty level scope}
                  (firstGeneric : Term context firstType RawTerm.listNil)
                  (secondGeneric : Term context secondType RawTerm.listNil),
                  firstType = Ty.listType elementType →
                  secondType = Ty.listType elementType →
                  HEq firstGeneric secondGeneric by
    exact key firstNil secondNil rfl rfl
  intro firstType secondType firstGeneric secondGeneric firstTypeEq secondTypeEq
  cases firstGeneric
  cases secondGeneric
  rename_i firstElement secondElement
  have firstElementEq : firstElement = elementType := Ty.listType.inj firstTypeEq
  have secondElementEq : secondElement = elementType := Ty.listType.inj secondTypeEq
  cases firstElementEq
  cases secondElementEq
  rfl

/-- Strong optionNone uniqueness when both terms are at the SAME
element type. -/
theorem Term.optionNone_unique_sameType
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    (firstNone secondNone :
      Term context (Ty.optionType elementType) RawTerm.optionNone) :
    HEq firstNone secondNone := by
  suffices key : ∀ {firstType secondType : Ty level scope}
                  (firstGeneric : Term context firstType RawTerm.optionNone)
                  (secondGeneric : Term context secondType RawTerm.optionNone),
                  firstType = Ty.optionType elementType →
                  secondType = Ty.optionType elementType →
                  HEq firstGeneric secondGeneric by
    exact key firstNone secondNone rfl rfl
  intro firstType secondType firstGeneric secondGeneric firstTypeEq secondTypeEq
  cases firstGeneric
  cases secondGeneric
  rename_i firstElement secondElement
  have firstElementEq : firstElement = elementType := Ty.optionType.inj firstTypeEq
  have secondElementEq : secondElement = elementType := Ty.optionType.inj secondTypeEq
  cases firstElementEq
  cases secondElementEq
  rfl

/-- Progress or step for `Term.listElim`: when scrutinee head is `listNil`,
fires `Step.iotaListElimNil` producing `nilBranch`; when `listCons`, fires
`Step.iotaListElimCons` producing
`Term.app (Term.app consBranch head) tail`; otherwise listElim is WHNF.

M05.D.2 conditional eliminator #16 of 17.  Parametric two-firing case
over `listType elementType`: the `listNil` arm needs `listNil_unique_sameType`
(parametric, requires same `elementType`) rather than the simpler `_unique`;
the `listCons` arm uses `Term.listConsDestruct` (yields head + tail + HEq).
Mirrors `Algo/Soundness.lean:190-206` (nil) and `Algo/Soundness.lean:291-311`
(cons). -/
theorem Term.listElim_progress_or_step
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    (scrutinee : Term context (Ty.listType elementType) scrutineeRaw)
    (nilBranch : Term context motiveType nilRaw)
    (consBranch :
      Term context (Ty.arrow elementType
                      (Ty.arrow (Ty.listType elementType) motiveType)) consRaw) :
    Term.isWHNF (Term.listElim scrutinee nilBranch consBranch) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.listElim scrutinee nilBranch consBranch) target := by
  cases h : scrutinee.headCtor with
  | listNil =>
      have rawEq : scrutineeRaw = RawTerm.listNil :=
        Term.headCtor_listNil_raw scrutinee h
      cases rawEq
      have scrutEq : scrutinee = Term.listNil :=
        eq_of_heq (Term.listNil_unique_sameType scrutinee Term.listNil)
      rw [scrutEq]
      exact Or.inr
        ⟨_, _, _, Step.iotaListElimNil nilBranch consBranch⟩
  | listCons =>
      obtain ⟨headRaw, tailRaw, rawEq⟩ := Term.headCtor_listCons_raw scrutinee h
      cases rawEq
      obtain ⟨headTerm, tailTerm, scrutHEq⟩ := Term.listConsDestruct scrutinee
      have scrutEq : scrutinee = Term.listCons headTerm tailTerm :=
        eq_of_heq scrutHEq
      rw [scrutEq]
      exact Or.inr
        ⟨_, _, _, Step.iotaListElimCons headTerm tailTerm nilBranch consBranch⟩
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

/-- Progress or step for `Term.optionMatch`: when scrutinee head is
`optionNone`, fires `Step.iotaOptionMatchNone` producing `noneBranch`;
when `optionSome`, fires `Step.iotaOptionMatchSome` producing
`Term.app someBranch valueTerm`; otherwise optionMatch is WHNF.

M05.D.2 conditional eliminator #17 of 17.  Final ι-elimination of
M05.D.2.  Parametric over `optionType elementType`.  Uses pre-staged
`Term.optionNone_unique_sameType` (inlined just before listElim) for
the noneBranch arm; uses `Term.optionSomeDestruct` (Term/Inversion.lean)
for the someBranch arm.  Mirrors `Algo/Soundness.lean:208-223` (none)
and `Algo/Soundness.lean:313-330` (some). -/
theorem Term.optionMatch_progress_or_step
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    (scrutinee : Term context (Ty.optionType elementType) scrutineeRaw)
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw) :
    Term.isWHNF (Term.optionMatch scrutinee noneBranch someBranch) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.optionMatch scrutinee noneBranch someBranch) target := by
  cases h : scrutinee.headCtor with
  | optionNone =>
      have rawEq : scrutineeRaw = RawTerm.optionNone :=
        Term.headCtor_optionNone_raw scrutinee h
      cases rawEq
      have scrutEq : scrutinee = Term.optionNone :=
        eq_of_heq (Term.optionNone_unique_sameType scrutinee Term.optionNone)
      rw [scrutEq]
      exact Or.inr
        ⟨_, _, _, Step.iotaOptionMatchNone noneBranch someBranch⟩
  | optionSome =>
      obtain ⟨valueRaw, rawEq⟩ := Term.headCtor_optionSome_raw scrutinee h
      cases rawEq
      obtain ⟨valueTerm, scrutHEq⟩ := Term.optionSomeDestruct scrutinee
      have scrutEq : scrutinee = Term.optionSome valueTerm :=
        eq_of_heq scrutHEq
      rw [scrutEq]
      exact Or.inr
        ⟨_, _, _, Step.iotaOptionMatchSome valueTerm noneBranch someBranch⟩
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

/-- Progress or step for `Term.eitherMatch`: when scrutinee head is
`eitherInl`, fires `Step.iotaEitherMatchInl` producing
`Term.app leftBranch valueTerm`; when `eitherInr`, fires
`Step.iotaEitherMatchInr` producing `Term.app rightBranch valueTerm`;
otherwise eitherMatch is WHNF.

M05.D.2 conditional eliminator #18 (final two-firing case for the
M05.D.2 sweep).  Both eitherInl and eitherInr carry a single value
payload, so both firings use destructors — no nullary-uniqueness
lemma needed.  Mirrors `Algo/Soundness.lean:332-350` (inl) and
`Algo/Soundness.lean:352-370` (inr). -/
theorem Term.eitherMatch_progress_or_step
    {context : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    (scrutinee : Term context (Ty.eitherType leftType rightType) scrutineeRaw)
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw) :
    Term.isWHNF (Term.eitherMatch scrutinee leftBranch rightBranch) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.eitherMatch scrutinee leftBranch rightBranch) target := by
  cases h : scrutinee.headCtor with
  | eitherInl =>
      obtain ⟨valueRaw, rawEq⟩ := Term.headCtor_eitherInl_raw scrutinee h
      cases rawEq
      obtain ⟨valueTerm, scrutHEq⟩ := Term.eitherInlDestruct scrutinee
      have scrutEq : scrutinee = Term.eitherInl (rightType := rightType) valueTerm :=
        eq_of_heq scrutHEq
      rw [scrutEq]
      exact Or.inr
        ⟨_, _, _, Step.iotaEitherMatchInl valueTerm leftBranch rightBranch⟩
  | eitherInr =>
      obtain ⟨valueRaw, rawEq⟩ := Term.headCtor_eitherInr_raw scrutinee h
      cases rawEq
      obtain ⟨valueTerm, scrutHEq⟩ := Term.eitherInrDestruct scrutinee
      have scrutEq : scrutinee = Term.eitherInr (leftType := leftType) valueTerm :=
        eq_of_heq scrutHEq
      rw [scrutEq]
      exact Or.inr
        ⟨_, _, _, Step.iotaEitherMatchInr valueTerm leftBranch rightBranch⟩
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
