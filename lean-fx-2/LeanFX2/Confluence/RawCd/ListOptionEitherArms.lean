import LeanFX2.Foundation.RawSubst
import LeanFX2.Foundation.RawPartialRename

/-! # LeanFX2.Confluence.RawCd.ListOptionEitherArms

Per-redex helpers for list, option, and either iota rules:
`cdListElimCase` (`listElim nil n c → n`, `listElim (cons h t) n c → c h t`),
`cdOptionMatchCase` (`optionMatch none n s → n`, `optionMatch (some v) n s → s v`),
`cdEitherMatchCase` (`eitherMatch (inl v) l r → l v`, `eitherMatch (inr v) l r → r v`).

Every inner `match` enumerates all 55 `RawTerm` constructors
explicitly to satisfy AXIOMS.md Layer M strict-zero-axiom policy.

## Root status

Layer 2 confluence helper.  Consumed by `Confluence.RawCd` shim and
downstream `Confluence.RawCdLemma`. -/

namespace LeanFX2

/-- ListElim redex: `listElim nil n c → n`,
`listElim (cons h t) n c → c h t`; otherwise rebuild. -/
def RawTerm.cdListElimCase {scope : Nat}
    (developedScrutinee developedNil developedCons : RawTerm scope) :
    RawTerm scope :=
  match developedScrutinee with
  | RawTerm.listNil => developedNil
  | RawTerm.listCons headTerm tailTerm =>
      RawTerm.app (RawTerm.app developedCons headTerm) tailTerm
  | RawTerm.var _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.unit =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.lam _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.app _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.pair _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.fst _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.snd _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.boolTrue =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.boolFalse =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.boolElim _ _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.natZero =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.natSucc _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.natElim _ _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.natRec _ _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.listElim _ _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.optionNone =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.optionSome _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.optionMatch _ _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.eitherInl _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.eitherInr _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.eitherMatch _ _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.refl _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.idJ _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.modIntro _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.modElim _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.subsume _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.interval0 =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.interval1 =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.intervalOpp _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.intervalMeet _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.intervalJoin _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.pathLam _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.pathApp _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.glueIntro _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.glueElim _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.transp _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.hcomp _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.oeqRefl _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.oeqJ _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.oeqFunext _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.idStrictRefl _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.idStrictRec _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.equivIntro _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.equivApp _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.refineIntro _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.refineElim _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.recordIntro _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.recordProj _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.codataUnfold _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.codataDest _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.sessionSend _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.sessionRecv _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.effectPerform _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.universeCode _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.arrowCode _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.piTyCode _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.sigmaTyCode _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.productCode _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.sumCode _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.listCode _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.optionCode _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.eitherCode _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.idCode _ _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.equivCode _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.cumulUpMarker _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.uaToEquiv _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.equivApply _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.pathCompose _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.idToEquiv _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.oeqTrans _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons
  | RawTerm.equivCompose _ _ =>
      RawTerm.listElim developedScrutinee developedNil developedCons

/-- OptionMatch redex: `optionMatch none n s → n`,
`optionMatch (some v) n s → s v`; otherwise rebuild. -/
def RawTerm.cdOptionMatchCase {scope : Nat}
    (developedScrutinee developedNone developedSome : RawTerm scope) :
    RawTerm scope :=
  match developedScrutinee with
  | RawTerm.optionNone => developedNone
  | RawTerm.optionSome valueTerm =>
      RawTerm.app developedSome valueTerm
  | RawTerm.var _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.unit =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.lam _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.app _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.pair _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.fst _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.snd _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.boolTrue =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.boolFalse =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.boolElim _ _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.natZero =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.natSucc _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.natElim _ _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.natRec _ _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.listNil =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.listCons _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.listElim _ _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.optionMatch _ _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.eitherInl _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.eitherInr _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.eitherMatch _ _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.refl _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.idJ _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.modIntro _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.modElim _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.subsume _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.interval0 =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.interval1 =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.intervalOpp _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.intervalMeet _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.intervalJoin _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.pathLam _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.pathApp _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.glueIntro _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.glueElim _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.transp _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.hcomp _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.oeqRefl _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.oeqJ _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.oeqFunext _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.idStrictRefl _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.idStrictRec _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.equivIntro _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.equivApp _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.refineIntro _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.refineElim _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.recordIntro _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.recordProj _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.codataUnfold _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.codataDest _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.sessionSend _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.sessionRecv _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.effectPerform _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.universeCode _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.arrowCode _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.piTyCode _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.sigmaTyCode _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.productCode _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.sumCode _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.listCode _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.optionCode _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.eitherCode _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.idCode _ _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.equivCode _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.cumulUpMarker _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.uaToEquiv _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.equivApply _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.pathCompose _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.idToEquiv _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.oeqTrans _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.equivCompose _ _ =>
      RawTerm.optionMatch developedScrutinee developedNone developedSome

/-- EitherMatch redex: `eitherMatch (inl v) l r → l v`,
`eitherMatch (inr v) l r → r v`; otherwise rebuild. -/
def RawTerm.cdEitherMatchCase {scope : Nat}
    (developedScrutinee developedLeft developedRight : RawTerm scope) :
    RawTerm scope :=
  match developedScrutinee with
  | RawTerm.eitherInl valueTerm => RawTerm.app developedLeft valueTerm
  | RawTerm.eitherInr valueTerm => RawTerm.app developedRight valueTerm
  | RawTerm.var _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.unit =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.lam _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.app _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.pair _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.fst _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.snd _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.boolTrue =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.boolFalse =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.boolElim _ _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.natZero =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.natSucc _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.natElim _ _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.natRec _ _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.listNil =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.listCons _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.listElim _ _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.optionNone =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.optionSome _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.optionMatch _ _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.eitherMatch _ _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.refl _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.idJ _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.modIntro _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.modElim _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.subsume _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.interval0 =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.interval1 =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.intervalOpp _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.intervalMeet _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.intervalJoin _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.pathLam _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.pathApp _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.glueIntro _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.glueElim _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.transp _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.hcomp _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.oeqRefl _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.oeqJ _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.oeqFunext _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.idStrictRefl _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.idStrictRec _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.equivIntro _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.equivApp _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.refineIntro _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.refineElim _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.recordIntro _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.recordProj _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.codataUnfold _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.codataDest _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.sessionSend _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.sessionRecv _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.effectPerform _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.universeCode _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.arrowCode _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.piTyCode _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.sigmaTyCode _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.productCode _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.sumCode _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.listCode _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.optionCode _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.eitherCode _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.idCode _ _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.equivCode _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.cumulUpMarker _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.uaToEquiv _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.equivApply _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.pathCompose _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.idToEquiv _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.oeqTrans _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.equivCompose _ _ =>
      RawTerm.eitherMatch developedScrutinee developedLeft developedRight

end LeanFX2
