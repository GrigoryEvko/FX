import LeanFX2.Foundation.RawSubst

/-! # LeanFX2.Confluence.RawCd.RecordAndCodata

Per-redex helpers for record and codata projection / destruction:
`cdRecordProjCase` (`recordProj (recordIntro field) → field`) and
`cdCodataDestCase` (codata observation).

Every inner `match` enumerates all 55 `RawTerm` constructors
explicitly to satisfy AXIOMS.md Layer M strict-zero-axiom policy.

## Root status

Layer 2 confluence helper.  Consumed by `Confluence.RawCd` shim and
downstream `Confluence.RawCdLemma`. -/

namespace LeanFX2

/-- Record projection redex: `recordProj (recordIntro field) → field`;
otherwise rebuild `recordProj dr`. -/
def RawTerm.cdRecordProjCase {scope : Nat}
    (developedRecord : RawTerm scope) : RawTerm scope :=
  match developedRecord with
  | RawTerm.recordIntro firstField => firstField
  | RawTerm.var _ => RawTerm.recordProj developedRecord
  | RawTerm.unit => RawTerm.recordProj developedRecord
  | RawTerm.lam _ => RawTerm.recordProj developedRecord
  | RawTerm.app _ _ => RawTerm.recordProj developedRecord
  | RawTerm.pair _ _ => RawTerm.recordProj developedRecord
  | RawTerm.fst _ => RawTerm.recordProj developedRecord
  | RawTerm.snd _ => RawTerm.recordProj developedRecord
  | RawTerm.boolTrue => RawTerm.recordProj developedRecord
  | RawTerm.boolFalse => RawTerm.recordProj developedRecord
  | RawTerm.boolElim _ _ _ => RawTerm.recordProj developedRecord
  | RawTerm.natZero => RawTerm.recordProj developedRecord
  | RawTerm.natSucc _ => RawTerm.recordProj developedRecord
  | RawTerm.natElim _ _ _ => RawTerm.recordProj developedRecord
  | RawTerm.natRec _ _ _ => RawTerm.recordProj developedRecord
  | RawTerm.listNil => RawTerm.recordProj developedRecord
  | RawTerm.listCons _ _ => RawTerm.recordProj developedRecord
  | RawTerm.listElim _ _ _ => RawTerm.recordProj developedRecord
  | RawTerm.optionNone => RawTerm.recordProj developedRecord
  | RawTerm.optionSome _ => RawTerm.recordProj developedRecord
  | RawTerm.optionMatch _ _ _ => RawTerm.recordProj developedRecord
  | RawTerm.eitherInl _ => RawTerm.recordProj developedRecord
  | RawTerm.eitherInr _ => RawTerm.recordProj developedRecord
  | RawTerm.eitherMatch _ _ _ => RawTerm.recordProj developedRecord
  | RawTerm.refl _ => RawTerm.recordProj developedRecord
  | RawTerm.idJ _ _ => RawTerm.recordProj developedRecord
  | RawTerm.modIntro _ => RawTerm.recordProj developedRecord
  | RawTerm.modElim _ => RawTerm.recordProj developedRecord
  | RawTerm.subsume _ => RawTerm.recordProj developedRecord
  | RawTerm.interval0 => RawTerm.recordProj developedRecord
  | RawTerm.interval1 => RawTerm.recordProj developedRecord
  | RawTerm.intervalOpp _ => RawTerm.recordProj developedRecord
  | RawTerm.intervalMeet _ _ => RawTerm.recordProj developedRecord
  | RawTerm.intervalJoin _ _ => RawTerm.recordProj developedRecord
  | RawTerm.pathLam _ => RawTerm.recordProj developedRecord
  | RawTerm.pathApp _ _ => RawTerm.recordProj developedRecord
  | RawTerm.glueIntro _ _ => RawTerm.recordProj developedRecord
  | RawTerm.glueElim _ => RawTerm.recordProj developedRecord
  | RawTerm.transp _ _ => RawTerm.recordProj developedRecord
  | RawTerm.transpFill _ _ _ => RawTerm.recordProj developedRecord
  | RawTerm.hcomp _ _ => RawTerm.recordProj developedRecord
  | RawTerm.oeqRefl _ => RawTerm.recordProj developedRecord
  | RawTerm.oeqJ _ _ => RawTerm.recordProj developedRecord
  | RawTerm.oeqFunext _ => RawTerm.recordProj developedRecord
  | RawTerm.idStrictRefl _ => RawTerm.recordProj developedRecord
  | RawTerm.idStrictRec _ _ => RawTerm.recordProj developedRecord
  | RawTerm.equivIntro _ _ => RawTerm.recordProj developedRecord
  | RawTerm.equivApp _ _ => RawTerm.recordProj developedRecord
  | RawTerm.refineIntro _ _ => RawTerm.recordProj developedRecord
  | RawTerm.refineElim _ => RawTerm.recordProj developedRecord
  | RawTerm.recordProj _ => RawTerm.recordProj developedRecord
  | RawTerm.codataUnfold _ _ => RawTerm.recordProj developedRecord
  | RawTerm.codataDest _ => RawTerm.recordProj developedRecord
  | RawTerm.sessionSend _ _ => RawTerm.recordProj developedRecord
  | RawTerm.sessionRecv _ => RawTerm.recordProj developedRecord
  | RawTerm.effectPerform _ _ => RawTerm.recordProj developedRecord
  | RawTerm.universeCode _ => RawTerm.recordProj developedRecord
  | RawTerm.arrowCode _ _ => RawTerm.recordProj developedRecord
  | RawTerm.piTyCode _ _ => RawTerm.recordProj developedRecord
  | RawTerm.sigmaTyCode _ _ => RawTerm.recordProj developedRecord
  | RawTerm.productCode _ _ => RawTerm.recordProj developedRecord
  | RawTerm.sumCode _ _ => RawTerm.recordProj developedRecord
  | RawTerm.listCode _ => RawTerm.recordProj developedRecord
  | RawTerm.optionCode _ => RawTerm.recordProj developedRecord
  | RawTerm.eitherCode _ _ => RawTerm.recordProj developedRecord
  | RawTerm.idCode _ _ _ => RawTerm.recordProj developedRecord
  | RawTerm.equivCode _ _ => RawTerm.recordProj developedRecord
  | RawTerm.cumulUpMarker _ => RawTerm.recordProj developedRecord
  | RawTerm.uaToEquiv _ => RawTerm.recordProj developedRecord
  | RawTerm.equivApply _ _ => RawTerm.recordProj developedRecord
  | RawTerm.pathCompose _ _ => RawTerm.recordProj developedRecord
  | RawTerm.idToEquiv _ => RawTerm.recordProj developedRecord
  | RawTerm.oeqTrans _ _ => RawTerm.recordProj developedRecord
  | RawTerm.equivCompose _ _ => RawTerm.recordProj developedRecord

/-- Codata observation redex:
`codataDest (codataUnfold state transition) → transition state`;
otherwise rebuild `codataDest developedCodata`. -/
def RawTerm.cdCodataDestCase {scope : Nat}
    (developedCodata : RawTerm scope) : RawTerm scope :=
  match developedCodata with
  | RawTerm.codataUnfold stateValue transition =>
      RawTerm.app transition stateValue
  | RawTerm.var _ => RawTerm.codataDest developedCodata
  | RawTerm.unit => RawTerm.codataDest developedCodata
  | RawTerm.lam _ => RawTerm.codataDest developedCodata
  | RawTerm.app _ _ => RawTerm.codataDest developedCodata
  | RawTerm.pair _ _ => RawTerm.codataDest developedCodata
  | RawTerm.fst _ => RawTerm.codataDest developedCodata
  | RawTerm.snd _ => RawTerm.codataDest developedCodata
  | RawTerm.boolTrue => RawTerm.codataDest developedCodata
  | RawTerm.boolFalse => RawTerm.codataDest developedCodata
  | RawTerm.boolElim _ _ _ => RawTerm.codataDest developedCodata
  | RawTerm.natZero => RawTerm.codataDest developedCodata
  | RawTerm.natSucc _ => RawTerm.codataDest developedCodata
  | RawTerm.natElim _ _ _ => RawTerm.codataDest developedCodata
  | RawTerm.natRec _ _ _ => RawTerm.codataDest developedCodata
  | RawTerm.listNil => RawTerm.codataDest developedCodata
  | RawTerm.listCons _ _ => RawTerm.codataDest developedCodata
  | RawTerm.listElim _ _ _ => RawTerm.codataDest developedCodata
  | RawTerm.optionNone => RawTerm.codataDest developedCodata
  | RawTerm.optionSome _ => RawTerm.codataDest developedCodata
  | RawTerm.optionMatch _ _ _ => RawTerm.codataDest developedCodata
  | RawTerm.eitherInl _ => RawTerm.codataDest developedCodata
  | RawTerm.eitherInr _ => RawTerm.codataDest developedCodata
  | RawTerm.eitherMatch _ _ _ => RawTerm.codataDest developedCodata
  | RawTerm.refl _ => RawTerm.codataDest developedCodata
  | RawTerm.idJ _ _ => RawTerm.codataDest developedCodata
  | RawTerm.modIntro _ => RawTerm.codataDest developedCodata
  | RawTerm.modElim _ => RawTerm.codataDest developedCodata
  | RawTerm.subsume _ => RawTerm.codataDest developedCodata
  | RawTerm.interval0 => RawTerm.codataDest developedCodata
  | RawTerm.interval1 => RawTerm.codataDest developedCodata
  | RawTerm.intervalOpp _ => RawTerm.codataDest developedCodata
  | RawTerm.intervalMeet _ _ => RawTerm.codataDest developedCodata
  | RawTerm.intervalJoin _ _ => RawTerm.codataDest developedCodata
  | RawTerm.pathLam _ => RawTerm.codataDest developedCodata
  | RawTerm.pathApp _ _ => RawTerm.codataDest developedCodata
  | RawTerm.glueIntro _ _ => RawTerm.codataDest developedCodata
  | RawTerm.glueElim _ => RawTerm.codataDest developedCodata
  | RawTerm.transp _ _ => RawTerm.codataDest developedCodata
  | RawTerm.transpFill _ _ _ => RawTerm.codataDest developedCodata
  | RawTerm.hcomp _ _ => RawTerm.codataDest developedCodata
  | RawTerm.oeqRefl _ => RawTerm.codataDest developedCodata
  | RawTerm.oeqJ _ _ => RawTerm.codataDest developedCodata
  | RawTerm.oeqFunext _ => RawTerm.codataDest developedCodata
  | RawTerm.idStrictRefl _ => RawTerm.codataDest developedCodata
  | RawTerm.idStrictRec _ _ => RawTerm.codataDest developedCodata
  | RawTerm.equivIntro _ _ => RawTerm.codataDest developedCodata
  | RawTerm.equivApp _ _ => RawTerm.codataDest developedCodata
  | RawTerm.refineIntro _ _ => RawTerm.codataDest developedCodata
  | RawTerm.refineElim _ => RawTerm.codataDest developedCodata
  | RawTerm.recordIntro _ => RawTerm.codataDest developedCodata
  | RawTerm.recordProj _ => RawTerm.codataDest developedCodata
  | RawTerm.codataDest _ => RawTerm.codataDest developedCodata
  | RawTerm.sessionSend _ _ => RawTerm.codataDest developedCodata
  | RawTerm.sessionRecv _ => RawTerm.codataDest developedCodata
  | RawTerm.effectPerform _ _ => RawTerm.codataDest developedCodata
  | RawTerm.universeCode _ => RawTerm.codataDest developedCodata
  | RawTerm.arrowCode _ _ => RawTerm.codataDest developedCodata
  | RawTerm.piTyCode _ _ => RawTerm.codataDest developedCodata
  | RawTerm.sigmaTyCode _ _ => RawTerm.codataDest developedCodata
  | RawTerm.productCode _ _ => RawTerm.codataDest developedCodata
  | RawTerm.sumCode _ _ => RawTerm.codataDest developedCodata
  | RawTerm.listCode _ => RawTerm.codataDest developedCodata
  | RawTerm.optionCode _ => RawTerm.codataDest developedCodata
  | RawTerm.eitherCode _ _ => RawTerm.codataDest developedCodata
  | RawTerm.idCode _ _ _ => RawTerm.codataDest developedCodata
  | RawTerm.equivCode _ _ => RawTerm.codataDest developedCodata
  | RawTerm.cumulUpMarker _ => RawTerm.codataDest developedCodata
  | RawTerm.uaToEquiv _ => RawTerm.codataDest developedCodata
  | RawTerm.equivApply _ _ => RawTerm.codataDest developedCodata
  | RawTerm.pathCompose _ _ => RawTerm.codataDest developedCodata
  | RawTerm.idToEquiv _ => RawTerm.codataDest developedCodata
  | RawTerm.oeqTrans _ _ => RawTerm.codataDest developedCodata
  | RawTerm.equivCompose _ _ => RawTerm.codataDest developedCodata

end LeanFX2
