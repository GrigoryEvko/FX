import LeanFX2.Foundation.RawTerm

/-! # LeanFX2.Confluence.RawCd.IdentityArms

Per-redex helpers for the identity-type J-eliminators:
`cdIdJCase` (`idJ b (refl _) → b`) and
`cdIdStrictRecCase` (`idStrictRec b (idStrictRefl _) → b`).

Every inner `match` enumerates all 55 `RawTerm` constructors
explicitly to satisfy AXIOMS.md Layer M strict-zero-axiom policy.

## Root status

Layer 2 confluence helper.  Consumed by `Confluence.RawCd` shim and
downstream `Confluence.RawCdLemma`. -/

namespace LeanFX2

/-- IdJ redex: `idJ b (refl _) → b`; otherwise rebuild. -/
def RawTerm.cdIdJCase {scope : Nat}
    (developedBase developedWitness : RawTerm scope) : RawTerm scope :=
  match developedWitness with
  | RawTerm.refl _ => developedBase
  | RawTerm.var _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.unit => RawTerm.idJ developedBase developedWitness
  | RawTerm.lam _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.app _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.pair _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.fst _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.snd _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.boolTrue => RawTerm.idJ developedBase developedWitness
  | RawTerm.boolFalse => RawTerm.idJ developedBase developedWitness
  | RawTerm.boolElim _ _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.natZero => RawTerm.idJ developedBase developedWitness
  | RawTerm.natSucc _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.natElim _ _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.natRec _ _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.listNil => RawTerm.idJ developedBase developedWitness
  | RawTerm.listCons _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.listElim _ _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.optionNone => RawTerm.idJ developedBase developedWitness
  | RawTerm.optionSome _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.optionMatch _ _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.eitherInl _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.eitherInr _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.eitherMatch _ _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.idJ _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.modIntro _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.modElim _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.subsume _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.interval0 => RawTerm.idJ developedBase developedWitness
  | RawTerm.interval1 => RawTerm.idJ developedBase developedWitness
  | RawTerm.intervalOpp _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.intervalMeet _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.intervalJoin _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.pathLam _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.pathApp _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.glueIntro _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.glueElim _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.transp _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.transpFill _ _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.hcomp _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.oeqRefl _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.oeqJ _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.oeqFunext _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.idStrictRefl _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.idStrictRec _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.equivIntro _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.equivApp _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.refineIntro _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.refineElim _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.recordIntro _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.recordProj _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.codataUnfold _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.codataDest _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.sessionSend _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.sessionRecv _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.effectPerform _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.universeCode _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.arrowCode _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.piTyCode _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.sigmaTyCode _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.productCode _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.sumCode _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.listCode _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.optionCode _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.eitherCode _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.idCode _ _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.equivCode _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.cumulUpMarker _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.uaToEquiv _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.equivApply _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.pathCompose _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.idToEquiv _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.oeqTrans _ _ => RawTerm.idJ developedBase developedWitness
  | RawTerm.equivCompose _ _ => RawTerm.idJ developedBase developedWitness

/-- Strict identity recursor redex: `idStrictRec b (idStrictRefl _) → b`;
otherwise rebuild. -/
def RawTerm.cdIdStrictRecCase {scope : Nat}
    (developedBase developedWitness : RawTerm scope) : RawTerm scope :=
  match developedWitness with
  | RawTerm.idStrictRefl _ => developedBase
  | RawTerm.var _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.unit => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.lam _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.app _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.pair _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.fst _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.snd _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.boolTrue => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.boolFalse => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.boolElim _ _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.natZero => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.natSucc _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.natElim _ _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.natRec _ _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.listNil => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.listCons _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.listElim _ _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.optionNone => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.optionSome _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.optionMatch _ _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.eitherInl _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.eitherInr _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.eitherMatch _ _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.refl _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.idJ _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.modIntro _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.modElim _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.subsume _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.interval0 => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.interval1 => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.intervalOpp _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.intervalMeet _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.intervalJoin _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.pathLam _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.pathApp _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.glueIntro _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.glueElim _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.transp _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.transpFill _ _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.hcomp _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.oeqRefl _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.oeqJ _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.oeqFunext _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.idStrictRec _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.equivIntro _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.equivApp _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.refineIntro _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.refineElim _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.recordIntro _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.recordProj _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.codataUnfold _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.codataDest _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.sessionSend _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.sessionRecv _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.effectPerform _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.universeCode _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.arrowCode _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.piTyCode _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.sigmaTyCode _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.productCode _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.sumCode _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.listCode _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.optionCode _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.eitherCode _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.idCode _ _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.equivCode _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.cumulUpMarker _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.uaToEquiv _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.equivApply _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.pathCompose _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.idToEquiv _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.oeqTrans _ _ => RawTerm.idStrictRec developedBase developedWitness
  | RawTerm.equivCompose _ _ => RawTerm.idStrictRec developedBase developedWitness

end LeanFX2
