import LeanFX2.Algo.RawWHNF
import LeanFX2.Confluence.RawParStarCong

/-! # LeanFX2.Algo.RawWHNFCorrect.Base — small-head inversions

Inversion lemmas for `lamBody?`, `pairComponents?`, and
`natSuccPred?`.  Each lemma takes a `some`-witness and recovers
the underlying constructor — the basis on which the headline
`whnf_reaches` discharges its β / ι-arms for arrow, sigma, and
natural-number eliminators.

## Root status

Layer 3 algorithm correctness helper. -/

namespace LeanFX2

variable {scope : Nat}

/-- Inversion: if `lamBody? term = some body`, then `term = .lam body`.

Proven by full case enumeration over all 28 RawTerm ctors — only
the `.lam` case returns `some`; every other case returns `none`,
which contradicts the hypothesis.  Uses `dsimp only` to force the
`?`-projection to reduce on each constructor. -/
theorem RawTerm.eq_lam_of_lamBody?_eq_some
    {body : RawTerm (scope + 1)}
    (term : RawTerm scope)
    (witness : RawTerm.lamBody? term = some body) :
    term = .lam body := by
  cases term with
  | lam bodyMatched =>
      have bodyEq : bodyMatched = body :=
        Option.some.inj witness
      exact bodyEq ▸ rfl
  | var _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | unit => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | app _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | pair _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | fst _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | snd _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | boolTrue => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | boolFalse => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | boolElim _ _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | natZero => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | natSucc _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | natElim _ _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | natRec _ _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | listNil => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | listCons _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | listElim _ _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | optionNone => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | optionSome _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | optionMatch _ _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | eitherInl _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | eitherInr _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | eitherMatch _ _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | refl _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | idJ _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | modIntro _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | modElim _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | subsume _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | interval0 => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | interval1 => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | intervalOpp _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | intervalMeet _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | intervalJoin _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | pathLam _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | pathApp _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | glueIntro _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | glueElim _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | transp _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | transpFill _ _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | hcomp _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | oeqRefl _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | oeqJ _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | oeqFunext _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | idStrictRefl _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | idStrictRec _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | equivIntro _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | equivApp _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | refineIntro _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | refineElim _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | recordIntro _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | recordProj _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | codataUnfold _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | codataDest _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | sessionSend _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | sessionRecv _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | effectPerform _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | universeCode _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | arrowCode _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | piTyCode _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | sigmaTyCode _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | productCode _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | sumCode _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | listCode _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | optionCode _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | eitherCode _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | idCode _ _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | equivCode _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | cumulUpMarker _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | uaToEquiv _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | equivApply _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | pathCompose _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | idToEquiv _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | oeqTrans _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness
  | equivCompose _ _ => dsimp only [RawTerm.lamBody?] at witness; nomatch witness

/-- Inversion for `pairComponents?`. -/
theorem RawTerm.eq_pair_of_pairComponents?_eq_some
    {firstValue secondValue : RawTerm scope}
    (term : RawTerm scope)
    (witness : RawTerm.pairComponents? term = some (firstValue, secondValue)) :
    term = .pair firstValue secondValue := by
  cases term with
  | pair firstMatched secondMatched =>
      have pairEq : (firstMatched, secondMatched) = (firstValue, secondValue) :=
        Option.some.inj witness
      have firstEq : firstMatched = firstValue := (Prod.mk.inj pairEq).1
      have secondEq : secondMatched = secondValue := (Prod.mk.inj pairEq).2
      exact firstEq ▸ secondEq ▸ rfl
  | var _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | unit => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | lam _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | app _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | fst _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | snd _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | boolTrue => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | boolFalse => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | boolElim _ _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | natZero => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | natSucc _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | natElim _ _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | natRec _ _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | listNil => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | listCons _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | listElim _ _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | optionNone => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | optionSome _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | optionMatch _ _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | eitherInl _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | eitherInr _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | eitherMatch _ _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | refl _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | idJ _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | modIntro _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | modElim _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | subsume _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | interval0 => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | interval1 => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | intervalOpp _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | intervalMeet _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | intervalJoin _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | pathLam _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | pathApp _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | glueIntro _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | glueElim _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | transp _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | transpFill _ _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | hcomp _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | oeqRefl _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | oeqJ _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | oeqFunext _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | idStrictRefl _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | idStrictRec _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | equivIntro _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | equivApp _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | refineIntro _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | refineElim _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | recordIntro _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | recordProj _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | codataUnfold _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | codataDest _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | sessionSend _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | sessionRecv _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | effectPerform _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | universeCode _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | arrowCode _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | piTyCode _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | sigmaTyCode _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | productCode _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | sumCode _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | listCode _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | optionCode _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | eitherCode _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | idCode _ _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | equivCode _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | cumulUpMarker _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | uaToEquiv _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | equivApply _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | pathCompose _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | idToEquiv _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | oeqTrans _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness
  | equivCompose _ _ => dsimp only [RawTerm.pairComponents?] at witness; nomatch witness

/-- Inversion for `natSuccPred?`. -/
theorem RawTerm.eq_natSucc_of_natSuccPred?_eq_some
    {predecessor : RawTerm scope}
    (term : RawTerm scope)
    (witness : RawTerm.natSuccPred? term = some predecessor) :
    term = .natSucc predecessor := by
  cases term with
  | natSucc predMatched =>
      have predEq : predMatched = predecessor := Option.some.inj witness
      exact predEq ▸ rfl
  | var _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | unit => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | lam _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | app _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | pair _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | fst _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | snd _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | boolTrue => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | boolFalse => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | boolElim _ _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | natZero => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | natElim _ _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | natRec _ _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | listNil => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | listCons _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | listElim _ _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | optionNone => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | optionSome _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | optionMatch _ _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | eitherInl _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | eitherInr _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | eitherMatch _ _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | refl _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | idJ _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | modIntro _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | modElim _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | subsume _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | interval0 => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | interval1 => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | intervalOpp _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | intervalMeet _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | intervalJoin _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | pathLam _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | pathApp _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | glueIntro _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | glueElim _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | transp _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | transpFill _ _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | hcomp _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | oeqRefl _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | oeqJ _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | oeqFunext _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | idStrictRefl _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | idStrictRec _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | equivIntro _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | equivApp _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | refineIntro _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | refineElim _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | recordIntro _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | recordProj _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | codataUnfold _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | codataDest _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | sessionSend _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | sessionRecv _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | effectPerform _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | universeCode _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | arrowCode _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | piTyCode _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | sigmaTyCode _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | productCode _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | sumCode _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | listCode _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | optionCode _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | eitherCode _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | idCode _ _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | equivCode _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | cumulUpMarker _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | uaToEquiv _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | equivApply _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | pathCompose _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | idToEquiv _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | oeqTrans _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness
  | equivCompose _ _ => dsimp only [RawTerm.natSuccPred?] at witness; nomatch witness

end LeanFX2
