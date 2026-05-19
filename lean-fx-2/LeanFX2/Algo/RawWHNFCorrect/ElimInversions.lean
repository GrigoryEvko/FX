import LeanFX2.Algo.RawWHNF.Projections
import LeanFX2.Confluence.RawParStarCong

/-! # LeanFX2.Algo.RawWHNFCorrect.ElimInversions — list/option/either inversions

Inversion lemmas for `listConsParts?`, `optionSomeValue?`,
`eitherInlValue?`, and `eitherInrValue?`.  Each lemma takes a
`some`-witness and recovers the underlying constructor — the
basis on which the headline `whnf_reaches` discharges its ι-arms
for list, option, and sum eliminators.

## Root status

Layer 3 algorithm correctness helper. -/

namespace LeanFX2

variable {scope : Nat}

/-- Inversion for `listConsParts?`. -/
theorem RawTerm.eq_listCons_of_listConsParts?_eq_some
    {headTerm tailTerm : RawTerm scope}
    (term : RawTerm scope)
    (witness : RawTerm.listConsParts? term = some (headTerm, tailTerm)) :
    term = .listCons headTerm tailTerm := by
  cases term with
  | listCons headMatched tailMatched =>
      have pairEq : (headMatched, tailMatched) = (headTerm, tailTerm) :=
        Option.some.inj witness
      have headEq : headMatched = headTerm := (Prod.mk.inj pairEq).1
      have tailEq : tailMatched = tailTerm := (Prod.mk.inj pairEq).2
      exact headEq ▸ tailEq ▸ rfl
  | var _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | unit => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | lam _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | app _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | pair _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | fst _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | snd _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | boolTrue => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | boolFalse => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | boolElim _ _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | natZero => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | natSucc _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | natElim _ _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | natRec _ _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | listNil => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | listElim _ _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | optionNone => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | optionSome _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | optionMatch _ _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | eitherInl _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | eitherInr _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | eitherMatch _ _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | refl _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | idJ _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | modIntro _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | modElim _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | subsume _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | interval0 => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | interval1 => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | intervalOpp _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | intervalMeet _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | intervalJoin _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | pathLam _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | pathApp _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | glueIntro _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | glueElim _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | transp _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | transpFill _ _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | hcomp _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | oeqRefl _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | oeqJ _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | oeqFunext _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | idStrictRefl _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | idStrictRec _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | equivIntro _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | equivApp _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | refineIntro _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | refineElim _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | recordIntro _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | recordProj _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | codataUnfold _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | codataDest _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | sessionSend _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | sessionRecv _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | effectPerform _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | universeCode _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | arrowCode _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | piTyCode _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | sigmaTyCode _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | productCode _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | sumCode _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | listCode _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | optionCode _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | eitherCode _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | idCode _ _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | equivCode _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | cumulUpMarker _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | uaToEquiv _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | equivApply _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | pathCompose _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | idToEquiv _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | oeqTrans _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness
  | equivCompose _ _ => dsimp only [RawTerm.listConsParts?] at witness; nomatch witness

/-- Inversion for `optionSomeValue?`. -/
theorem RawTerm.eq_optionSome_of_optionSomeValue?_eq_some
    {valueTerm : RawTerm scope}
    (term : RawTerm scope)
    (witness : RawTerm.optionSomeValue? term = some valueTerm) :
    term = .optionSome valueTerm := by
  cases term with
  | optionSome valueMatched =>
      have valueEq : valueMatched = valueTerm := Option.some.inj witness
      exact valueEq ▸ rfl
  | var _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | unit => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | lam _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | app _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | pair _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | fst _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | snd _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | boolTrue => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | boolFalse => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | boolElim _ _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | natZero => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | natSucc _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | natElim _ _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | natRec _ _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | listNil => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | listCons _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | listElim _ _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | optionNone => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | optionMatch _ _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | eitherInl _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | eitherInr _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | eitherMatch _ _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | refl _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | idJ _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | modIntro _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | modElim _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | subsume _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | interval0 => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | interval1 => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | intervalOpp _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | intervalMeet _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | intervalJoin _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | pathLam _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | pathApp _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | glueIntro _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | glueElim _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | transp _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | transpFill _ _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | hcomp _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | oeqRefl _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | oeqJ _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | oeqFunext _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | idStrictRefl _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | idStrictRec _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | equivIntro _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | equivApp _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | refineIntro _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | refineElim _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | recordIntro _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | recordProj _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | codataUnfold _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | codataDest _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | sessionSend _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | sessionRecv _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | effectPerform _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | universeCode _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | arrowCode _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | piTyCode _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | sigmaTyCode _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | productCode _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | sumCode _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | listCode _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | optionCode _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | eitherCode _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | idCode _ _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | equivCode _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | cumulUpMarker _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | uaToEquiv _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | equivApply _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | pathCompose _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | idToEquiv _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | oeqTrans _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness
  | equivCompose _ _ => dsimp only [RawTerm.optionSomeValue?] at witness; nomatch witness

/-- Inversion for `eitherInlValue?`. -/
theorem RawTerm.eq_eitherInl_of_eitherInlValue?_eq_some
    {valueTerm : RawTerm scope}
    (term : RawTerm scope)
    (witness : RawTerm.eitherInlValue? term = some valueTerm) :
    term = .eitherInl valueTerm := by
  cases term with
  | eitherInl valueMatched =>
      have valueEq : valueMatched = valueTerm := Option.some.inj witness
      exact valueEq ▸ rfl
  | var _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | unit => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | lam _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | app _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | pair _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | fst _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | snd _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | boolTrue => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | boolFalse => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | boolElim _ _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | natZero => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | natSucc _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | natElim _ _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | natRec _ _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | listNil => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | listCons _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | listElim _ _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | optionNone => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | optionSome _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | optionMatch _ _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | eitherInr _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | eitherMatch _ _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | refl _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | idJ _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | modIntro _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | modElim _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | subsume _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | interval0 => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | interval1 => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | intervalOpp _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | intervalMeet _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | intervalJoin _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | pathLam _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | pathApp _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | glueIntro _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | glueElim _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | transp _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | transpFill _ _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | hcomp _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | oeqRefl _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | oeqJ _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | oeqFunext _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | idStrictRefl _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | idStrictRec _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | equivIntro _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | equivApp _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | refineIntro _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | refineElim _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | recordIntro _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | recordProj _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | codataUnfold _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | codataDest _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | sessionSend _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | sessionRecv _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | effectPerform _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | universeCode _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | arrowCode _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | piTyCode _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | sigmaTyCode _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | productCode _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | sumCode _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | listCode _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | optionCode _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | eitherCode _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | idCode _ _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | equivCode _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | cumulUpMarker _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | uaToEquiv _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | equivApply _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | pathCompose _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | idToEquiv _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | oeqTrans _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness
  | equivCompose _ _ => dsimp only [RawTerm.eitherInlValue?] at witness; nomatch witness

/-- Inversion for `eitherInrValue?`. -/
theorem RawTerm.eq_eitherInr_of_eitherInrValue?_eq_some
    {valueTerm : RawTerm scope}
    (term : RawTerm scope)
    (witness : RawTerm.eitherInrValue? term = some valueTerm) :
    term = .eitherInr valueTerm := by
  cases term with
  | eitherInr valueMatched =>
      have valueEq : valueMatched = valueTerm := Option.some.inj witness
      exact valueEq ▸ rfl
  | var _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | unit => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | lam _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | app _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | pair _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | fst _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | snd _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | boolTrue => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | boolFalse => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | boolElim _ _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | natZero => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | natSucc _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | natElim _ _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | natRec _ _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | listNil => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | listCons _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | listElim _ _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | optionNone => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | optionSome _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | optionMatch _ _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | eitherInl _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | eitherMatch _ _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | refl _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | idJ _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | modIntro _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | modElim _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | subsume _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | interval0 => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | interval1 => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | intervalOpp _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | intervalMeet _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | intervalJoin _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | pathLam _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | pathApp _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | glueIntro _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | glueElim _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | transp _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | transpFill _ _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | hcomp _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | oeqRefl _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | oeqJ _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | oeqFunext _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | idStrictRefl _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | idStrictRec _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | equivIntro _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | equivApp _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | refineIntro _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | refineElim _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | recordIntro _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | recordProj _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | codataUnfold _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | codataDest _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | sessionSend _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | sessionRecv _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | effectPerform _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | universeCode _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | arrowCode _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | piTyCode _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | sigmaTyCode _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | productCode _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | sumCode _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | listCode _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | optionCode _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | eitherCode _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | idCode _ _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | equivCode _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | cumulUpMarker _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | uaToEquiv _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | equivApply _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | pathCompose _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | idToEquiv _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | oeqTrans _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness
  | equivCompose _ _ => dsimp only [RawTerm.eitherInrValue?] at witness; nomatch witness


end LeanFX2
