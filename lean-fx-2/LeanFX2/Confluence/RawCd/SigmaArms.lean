import LeanFX2.Foundation.RawTerm

/-! # LeanFX2.Confluence.RawCd.SigmaArms

Per-redex helpers for Sigma-type projections:
`cdFstCase` (`fst (a, b) → a`) and `cdSndCase` (`snd (a, b) → b`).

Every inner `match` enumerates all 55 `RawTerm` constructors
explicitly to satisfy AXIOMS.md Layer M strict-zero-axiom policy.

## Root status

Layer 2 confluence helper.  Consumed by `Confluence.RawCd` shim and
downstream `Confluence.RawCdLemma`. -/

namespace LeanFX2

/-- Fst redex: `fst (a, b) → a`; otherwise rebuild `fst dp`. -/
def RawTerm.cdFstCase {scope : Nat}
    (developedPair : RawTerm scope) : RawTerm scope :=
  match developedPair with
  | RawTerm.pair firstValue _ => firstValue
  | RawTerm.var _ => RawTerm.fst developedPair
  | RawTerm.unit => RawTerm.fst developedPair
  | RawTerm.lam _ => RawTerm.fst developedPair
  | RawTerm.app _ _ => RawTerm.fst developedPair
  | RawTerm.fst _ => RawTerm.fst developedPair
  | RawTerm.snd _ => RawTerm.fst developedPair
  | RawTerm.boolTrue => RawTerm.fst developedPair
  | RawTerm.boolFalse => RawTerm.fst developedPair
  | RawTerm.boolElim _ _ _ => RawTerm.fst developedPair
  | RawTerm.natZero => RawTerm.fst developedPair
  | RawTerm.natSucc _ => RawTerm.fst developedPair
  | RawTerm.natElim _ _ _ => RawTerm.fst developedPair
  | RawTerm.natRec _ _ _ => RawTerm.fst developedPair
  | RawTerm.listNil => RawTerm.fst developedPair
  | RawTerm.listCons _ _ => RawTerm.fst developedPair
  | RawTerm.listElim _ _ _ => RawTerm.fst developedPair
  | RawTerm.optionNone => RawTerm.fst developedPair
  | RawTerm.optionSome _ => RawTerm.fst developedPair
  | RawTerm.optionMatch _ _ _ => RawTerm.fst developedPair
  | RawTerm.eitherInl _ => RawTerm.fst developedPair
  | RawTerm.eitherInr _ => RawTerm.fst developedPair
  | RawTerm.eitherMatch _ _ _ => RawTerm.fst developedPair
  | RawTerm.refl _ => RawTerm.fst developedPair
  | RawTerm.idJ _ _ => RawTerm.fst developedPair
  | RawTerm.modIntro _ => RawTerm.fst developedPair
  | RawTerm.modElim _ => RawTerm.fst developedPair
  | RawTerm.subsume _ => RawTerm.fst developedPair
  | RawTerm.interval0 => RawTerm.fst developedPair
  | RawTerm.interval1 => RawTerm.fst developedPair
  | RawTerm.intervalOpp _ => RawTerm.fst developedPair
  | RawTerm.intervalMeet _ _ => RawTerm.fst developedPair
  | RawTerm.intervalJoin _ _ => RawTerm.fst developedPair
  | RawTerm.pathLam _ => RawTerm.fst developedPair
  | RawTerm.pathApp _ _ => RawTerm.fst developedPair
  | RawTerm.glueIntro _ _ => RawTerm.fst developedPair
  | RawTerm.glueElim _ => RawTerm.fst developedPair
  | RawTerm.transp _ _ => RawTerm.fst developedPair
  | RawTerm.transpFill _ _ _ => RawTerm.fst developedPair
  | RawTerm.hcomp _ _ => RawTerm.fst developedPair
  | RawTerm.oeqRefl _ => RawTerm.fst developedPair
  | RawTerm.oeqJ _ _ => RawTerm.fst developedPair
  | RawTerm.oeqFunext _ => RawTerm.fst developedPair
  | RawTerm.idStrictRefl _ => RawTerm.fst developedPair
  | RawTerm.idStrictRec _ _ => RawTerm.fst developedPair
  | RawTerm.equivIntro _ _ => RawTerm.fst developedPair
  | RawTerm.equivApp _ _ => RawTerm.fst developedPair
  | RawTerm.refineIntro _ _ => RawTerm.fst developedPair
  | RawTerm.refineElim _ => RawTerm.fst developedPair
  | RawTerm.recordIntro _ => RawTerm.fst developedPair
  | RawTerm.recordProj _ => RawTerm.fst developedPair
  | RawTerm.codataUnfold _ _ => RawTerm.fst developedPair
  | RawTerm.codataDest _ => RawTerm.fst developedPair
  | RawTerm.sessionSend _ _ => RawTerm.fst developedPair
  | RawTerm.sessionRecv _ => RawTerm.fst developedPair
  | RawTerm.effectPerform _ _ => RawTerm.fst developedPair
  | RawTerm.universeCode _ => RawTerm.fst developedPair
  | RawTerm.arrowCode _ _ => RawTerm.fst developedPair
  | RawTerm.piTyCode _ _ => RawTerm.fst developedPair
  | RawTerm.sigmaTyCode _ _ => RawTerm.fst developedPair
  | RawTerm.productCode _ _ => RawTerm.fst developedPair
  | RawTerm.sumCode _ _ => RawTerm.fst developedPair
  | RawTerm.listCode _ => RawTerm.fst developedPair
  | RawTerm.optionCode _ => RawTerm.fst developedPair
  | RawTerm.eitherCode _ _ => RawTerm.fst developedPair
  | RawTerm.idCode _ _ _ => RawTerm.fst developedPair
  | RawTerm.equivCode _ _ => RawTerm.fst developedPair
  | RawTerm.cumulUpMarker _ => RawTerm.fst developedPair
  | RawTerm.uaToEquiv _ => RawTerm.fst developedPair
  | RawTerm.equivApply _ _ => RawTerm.fst developedPair
  | RawTerm.pathCompose _ _ => RawTerm.fst developedPair
  | RawTerm.idToEquiv _ => RawTerm.fst developedPair
  | RawTerm.oeqTrans _ _ => RawTerm.fst developedPair
  | RawTerm.equivCompose _ _ => RawTerm.fst developedPair

/-- Snd redex: `snd (a, b) → b`; otherwise rebuild `snd dp`. -/
def RawTerm.cdSndCase {scope : Nat}
    (developedPair : RawTerm scope) : RawTerm scope :=
  match developedPair with
  | RawTerm.pair _ secondValue => secondValue
  | RawTerm.var _ => RawTerm.snd developedPair
  | RawTerm.unit => RawTerm.snd developedPair
  | RawTerm.lam _ => RawTerm.snd developedPair
  | RawTerm.app _ _ => RawTerm.snd developedPair
  | RawTerm.fst _ => RawTerm.snd developedPair
  | RawTerm.snd _ => RawTerm.snd developedPair
  | RawTerm.boolTrue => RawTerm.snd developedPair
  | RawTerm.boolFalse => RawTerm.snd developedPair
  | RawTerm.boolElim _ _ _ => RawTerm.snd developedPair
  | RawTerm.natZero => RawTerm.snd developedPair
  | RawTerm.natSucc _ => RawTerm.snd developedPair
  | RawTerm.natElim _ _ _ => RawTerm.snd developedPair
  | RawTerm.natRec _ _ _ => RawTerm.snd developedPair
  | RawTerm.listNil => RawTerm.snd developedPair
  | RawTerm.listCons _ _ => RawTerm.snd developedPair
  | RawTerm.listElim _ _ _ => RawTerm.snd developedPair
  | RawTerm.optionNone => RawTerm.snd developedPair
  | RawTerm.optionSome _ => RawTerm.snd developedPair
  | RawTerm.optionMatch _ _ _ => RawTerm.snd developedPair
  | RawTerm.eitherInl _ => RawTerm.snd developedPair
  | RawTerm.eitherInr _ => RawTerm.snd developedPair
  | RawTerm.eitherMatch _ _ _ => RawTerm.snd developedPair
  | RawTerm.refl _ => RawTerm.snd developedPair
  | RawTerm.idJ _ _ => RawTerm.snd developedPair
  | RawTerm.modIntro _ => RawTerm.snd developedPair
  | RawTerm.modElim _ => RawTerm.snd developedPair
  | RawTerm.subsume _ => RawTerm.snd developedPair
  | RawTerm.interval0 => RawTerm.snd developedPair
  | RawTerm.interval1 => RawTerm.snd developedPair
  | RawTerm.intervalOpp _ => RawTerm.snd developedPair
  | RawTerm.intervalMeet _ _ => RawTerm.snd developedPair
  | RawTerm.intervalJoin _ _ => RawTerm.snd developedPair
  | RawTerm.pathLam _ => RawTerm.snd developedPair
  | RawTerm.pathApp _ _ => RawTerm.snd developedPair
  | RawTerm.glueIntro _ _ => RawTerm.snd developedPair
  | RawTerm.glueElim _ => RawTerm.snd developedPair
  | RawTerm.transp _ _ => RawTerm.snd developedPair
  | RawTerm.transpFill _ _ _ => RawTerm.snd developedPair
  | RawTerm.hcomp _ _ => RawTerm.snd developedPair
  | RawTerm.oeqRefl _ => RawTerm.snd developedPair
  | RawTerm.oeqJ _ _ => RawTerm.snd developedPair
  | RawTerm.oeqFunext _ => RawTerm.snd developedPair
  | RawTerm.idStrictRefl _ => RawTerm.snd developedPair
  | RawTerm.idStrictRec _ _ => RawTerm.snd developedPair
  | RawTerm.equivIntro _ _ => RawTerm.snd developedPair
  | RawTerm.equivApp _ _ => RawTerm.snd developedPair
  | RawTerm.refineIntro _ _ => RawTerm.snd developedPair
  | RawTerm.refineElim _ => RawTerm.snd developedPair
  | RawTerm.recordIntro _ => RawTerm.snd developedPair
  | RawTerm.recordProj _ => RawTerm.snd developedPair
  | RawTerm.codataUnfold _ _ => RawTerm.snd developedPair
  | RawTerm.codataDest _ => RawTerm.snd developedPair
  | RawTerm.sessionSend _ _ => RawTerm.snd developedPair
  | RawTerm.sessionRecv _ => RawTerm.snd developedPair
  | RawTerm.effectPerform _ _ => RawTerm.snd developedPair
  | RawTerm.universeCode _ => RawTerm.snd developedPair
  | RawTerm.arrowCode _ _ => RawTerm.snd developedPair
  | RawTerm.piTyCode _ _ => RawTerm.snd developedPair
  | RawTerm.sigmaTyCode _ _ => RawTerm.snd developedPair
  | RawTerm.productCode _ _ => RawTerm.snd developedPair
  | RawTerm.sumCode _ _ => RawTerm.snd developedPair
  | RawTerm.listCode _ => RawTerm.snd developedPair
  | RawTerm.optionCode _ => RawTerm.snd developedPair
  | RawTerm.eitherCode _ _ => RawTerm.snd developedPair
  | RawTerm.idCode _ _ _ => RawTerm.snd developedPair
  | RawTerm.equivCode _ _ => RawTerm.snd developedPair
  | RawTerm.cumulUpMarker _ => RawTerm.snd developedPair
  | RawTerm.uaToEquiv _ => RawTerm.snd developedPair
  | RawTerm.equivApply _ _ => RawTerm.snd developedPair
  | RawTerm.pathCompose _ _ => RawTerm.snd developedPair
  | RawTerm.idToEquiv _ => RawTerm.snd developedPair
  | RawTerm.oeqTrans _ _ => RawTerm.snd developedPair
  | RawTerm.equivCompose _ _ => RawTerm.snd developedPair

end LeanFX2
