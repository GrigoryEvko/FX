import LeanFX2.Foundation.RawSubst
import LeanFX2.Foundation.RawPartialRename

/-! # LeanFX2.Confluence.RawCd.BoolNatArms

Per-redex helpers for boolean and natural-number iota rules:
`cdBoolElimCase` (`boolElim true t e → t`, `boolElim false t e → e`),
`cdNatElimCase` (`natElim 0 z s → z`, `natElim (succ p) z s → s p`),
`cdNatRecCase` (`natRec` analogous with motive-tracking signature).

Every inner `match` enumerates all 55 `RawTerm` constructors
explicitly to satisfy AXIOMS.md Layer M strict-zero-axiom policy.

## Root status

Layer 2 confluence helper.  Consumed by `Confluence.RawCd` shim and
downstream `Confluence.RawCdLemma`. -/

namespace LeanFX2

/-- BoolElim redex: `boolElim true t e → t`, `boolElim false t e → e`;
otherwise rebuild. -/
def RawTerm.cdBoolElimCase {scope : Nat}
    (developedScrutinee developedThen developedElse : RawTerm scope) :
    RawTerm scope :=
  match developedScrutinee with
  | RawTerm.boolTrue => developedThen
  | RawTerm.boolFalse => developedElse
  | RawTerm.var _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.unit =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.lam _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.app _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.pair _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.fst _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.snd _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.boolElim _ _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.natZero =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.natSucc _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.natElim _ _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.natRec _ _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.listNil =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.listCons _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.listElim _ _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.optionNone =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.optionSome _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.optionMatch _ _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.eitherInl _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.eitherInr _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.eitherMatch _ _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.refl _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.idJ _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.modIntro _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.modElim _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.subsume _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.interval0 =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.interval1 =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.intervalOpp _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.intervalMeet _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.intervalJoin _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.pathLam _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.pathApp _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.glueIntro _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.glueElim _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.transp _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.hcomp _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.oeqRefl _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.oeqJ _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.oeqFunext _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.idStrictRefl _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.idStrictRec _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.equivIntro _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.equivApp _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.refineIntro _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.refineElim _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.recordIntro _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.recordProj _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.codataUnfold _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.codataDest _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.sessionSend _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.sessionRecv _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.effectPerform _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.universeCode _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.arrowCode _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.piTyCode _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.sigmaTyCode _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.productCode _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.sumCode _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.listCode _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.optionCode _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.eitherCode _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.idCode _ _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.equivCode _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.cumulUpMarker _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.uaToEquiv _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.equivApply _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.pathCompose _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.idToEquiv _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.oeqTrans _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse
  | RawTerm.equivCompose _ _ =>
      RawTerm.boolElim developedScrutinee developedThen developedElse

/-- NatElim redex: `natElim 0 z s → z`, `natElim (succ p) z s → s p`;
otherwise rebuild. -/
def RawTerm.cdNatElimCase {scope : Nat}
    (developedScrutinee developedZero developedSucc : RawTerm scope) :
    RawTerm scope :=
  match developedScrutinee with
  | RawTerm.natZero => developedZero
  | RawTerm.natSucc predecessor =>
      RawTerm.app developedSucc predecessor
  | RawTerm.var _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.unit =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.lam _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.app _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.pair _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.fst _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.snd _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.boolTrue =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.boolFalse =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.boolElim _ _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.natElim _ _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.natRec _ _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.listNil =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.listCons _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.listElim _ _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.optionNone =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.optionSome _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.optionMatch _ _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.eitherInl _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.eitherInr _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.eitherMatch _ _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.refl _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.idJ _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.modIntro _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.modElim _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.subsume _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.interval0 =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.interval1 =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.intervalOpp _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.intervalMeet _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.intervalJoin _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.pathLam _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.pathApp _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.glueIntro _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.glueElim _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.transp _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.hcomp _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.oeqRefl _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.oeqJ _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.oeqFunext _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.idStrictRefl _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.idStrictRec _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.equivIntro _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.equivApp _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.refineIntro _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.refineElim _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.recordIntro _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.recordProj _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.codataUnfold _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.codataDest _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.sessionSend _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.sessionRecv _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.effectPerform _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.universeCode _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.arrowCode _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.piTyCode _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.sigmaTyCode _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.productCode _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.sumCode _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.listCode _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.optionCode _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.eitherCode _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.idCode _ _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.equivCode _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.cumulUpMarker _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.uaToEquiv _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.equivApply _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.pathCompose _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.idToEquiv _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.oeqTrans _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc
  | RawTerm.equivCompose _ _ =>
      RawTerm.natElim developedScrutinee developedZero developedSucc

/-- NatRec redex: `natRec 0 z s → z`,
`natRec (succ p) z s → s p (natRec p z s)`; otherwise rebuild. -/
def RawTerm.cdNatRecCase {scope : Nat}
    (developedScrutinee developedZero developedSucc : RawTerm scope) :
    RawTerm scope :=
  match developedScrutinee with
  | RawTerm.natZero => developedZero
  | RawTerm.natSucc predecessor =>
      RawTerm.app (RawTerm.app developedSucc predecessor)
        (RawTerm.natRec predecessor developedZero developedSucc)
  | RawTerm.var _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.unit =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.lam _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.app _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.pair _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.fst _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.snd _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.boolTrue =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.boolFalse =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.boolElim _ _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.natElim _ _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.natRec _ _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.listNil =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.listCons _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.listElim _ _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.optionNone =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.optionSome _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.optionMatch _ _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.eitherInl _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.eitherInr _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.eitherMatch _ _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.refl _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.idJ _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.modIntro _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.modElim _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.subsume _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.interval0 =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.interval1 =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.intervalOpp _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.intervalMeet _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.intervalJoin _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.pathLam _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.pathApp _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.glueIntro _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.glueElim _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.transp _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.hcomp _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.oeqRefl _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.oeqJ _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.oeqFunext _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.idStrictRefl _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.idStrictRec _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.equivIntro _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.equivApp _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.refineIntro _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.refineElim _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.recordIntro _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.recordProj _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.codataUnfold _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.codataDest _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.sessionSend _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.sessionRecv _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.effectPerform _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.universeCode _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.arrowCode _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.piTyCode _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.sigmaTyCode _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.productCode _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.sumCode _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.listCode _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.optionCode _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.eitherCode _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.idCode _ _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.equivCode _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.cumulUpMarker _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.uaToEquiv _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.equivApply _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.pathCompose _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.idToEquiv _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.oeqTrans _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc
  | RawTerm.equivCompose _ _ =>
      RawTerm.natRec developedScrutinee developedZero developedSucc

end LeanFX2
