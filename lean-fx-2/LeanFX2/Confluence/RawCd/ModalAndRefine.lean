import LeanFX2.Foundation.RawTerm

/-! # LeanFX2.Confluence.RawCd.ModalAndRefine

Per-redex helpers for modal and refinement-type families:
`cdGlueElimCase` (`unglue (glue base partial) → base`),
`cdModElimCase` (`modElim (modIntro payload) → payload`),
`cdRefineElimCase` (`refineElim (refineIntro value proof) → value`).

Every inner `match` enumerates all 55 `RawTerm` constructors
explicitly to satisfy AXIOMS.md Layer M strict-zero-axiom policy.

## Root status

Layer 2 confluence helper.  Consumed by `Confluence.RawCd` shim and
downstream `Confluence.RawCdLemma`. -/

namespace LeanFX2

/-- Glue elimination redex: `unglue (glue base partial) → base`;
otherwise rebuild `glueElim dg`. -/
def RawTerm.cdGlueElimCase {scope : Nat}
    (developedGlued : RawTerm scope) : RawTerm scope :=
  match developedGlued with
  | RawTerm.glueIntro baseValue _ => baseValue
  | RawTerm.var _ => RawTerm.glueElim developedGlued
  | RawTerm.unit => RawTerm.glueElim developedGlued
  | RawTerm.lam _ => RawTerm.glueElim developedGlued
  | RawTerm.app _ _ => RawTerm.glueElim developedGlued
  | RawTerm.pair _ _ => RawTerm.glueElim developedGlued
  | RawTerm.fst _ => RawTerm.glueElim developedGlued
  | RawTerm.snd _ => RawTerm.glueElim developedGlued
  | RawTerm.boolTrue => RawTerm.glueElim developedGlued
  | RawTerm.boolFalse => RawTerm.glueElim developedGlued
  | RawTerm.boolElim _ _ _ => RawTerm.glueElim developedGlued
  | RawTerm.natZero => RawTerm.glueElim developedGlued
  | RawTerm.natSucc _ => RawTerm.glueElim developedGlued
  | RawTerm.natElim _ _ _ => RawTerm.glueElim developedGlued
  | RawTerm.natRec _ _ _ => RawTerm.glueElim developedGlued
  | RawTerm.listNil => RawTerm.glueElim developedGlued
  | RawTerm.listCons _ _ => RawTerm.glueElim developedGlued
  | RawTerm.listElim _ _ _ => RawTerm.glueElim developedGlued
  | RawTerm.optionNone => RawTerm.glueElim developedGlued
  | RawTerm.optionSome _ => RawTerm.glueElim developedGlued
  | RawTerm.optionMatch _ _ _ => RawTerm.glueElim developedGlued
  | RawTerm.eitherInl _ => RawTerm.glueElim developedGlued
  | RawTerm.eitherInr _ => RawTerm.glueElim developedGlued
  | RawTerm.eitherMatch _ _ _ => RawTerm.glueElim developedGlued
  | RawTerm.refl _ => RawTerm.glueElim developedGlued
  | RawTerm.idJ _ _ => RawTerm.glueElim developedGlued
  | RawTerm.modIntro _ => RawTerm.glueElim developedGlued
  | RawTerm.modElim _ => RawTerm.glueElim developedGlued
  | RawTerm.subsume _ => RawTerm.glueElim developedGlued
  | RawTerm.interval0 => RawTerm.glueElim developedGlued
  | RawTerm.interval1 => RawTerm.glueElim developedGlued
  | RawTerm.intervalOpp _ => RawTerm.glueElim developedGlued
  | RawTerm.intervalMeet _ _ => RawTerm.glueElim developedGlued
  | RawTerm.intervalJoin _ _ => RawTerm.glueElim developedGlued
  | RawTerm.pathLam _ => RawTerm.glueElim developedGlued
  | RawTerm.pathApp _ _ => RawTerm.glueElim developedGlued
  | RawTerm.glueElim _ => RawTerm.glueElim developedGlued
  | RawTerm.transp _ _ => RawTerm.glueElim developedGlued
  | RawTerm.transpFill _ _ _ => RawTerm.glueElim developedGlued
  | RawTerm.hcomp _ _ => RawTerm.glueElim developedGlued
  | RawTerm.oeqRefl _ => RawTerm.glueElim developedGlued
  | RawTerm.oeqJ _ _ => RawTerm.glueElim developedGlued
  | RawTerm.oeqFunext _ => RawTerm.glueElim developedGlued
  | RawTerm.idStrictRefl _ => RawTerm.glueElim developedGlued
  | RawTerm.idStrictRec _ _ => RawTerm.glueElim developedGlued
  | RawTerm.equivIntro _ _ => RawTerm.glueElim developedGlued
  | RawTerm.equivApp _ _ => RawTerm.glueElim developedGlued
  | RawTerm.refineIntro _ _ => RawTerm.glueElim developedGlued
  | RawTerm.refineElim _ => RawTerm.glueElim developedGlued
  | RawTerm.recordIntro _ => RawTerm.glueElim developedGlued
  | RawTerm.recordProj _ => RawTerm.glueElim developedGlued
  | RawTerm.codataUnfold _ _ => RawTerm.glueElim developedGlued
  | RawTerm.codataDest _ => RawTerm.glueElim developedGlued
  | RawTerm.sessionSend _ _ => RawTerm.glueElim developedGlued
  | RawTerm.sessionRecv _ => RawTerm.glueElim developedGlued
  | RawTerm.effectPerform _ _ => RawTerm.glueElim developedGlued
  | RawTerm.universeCode _ => RawTerm.glueElim developedGlued
  | RawTerm.arrowCode _ _ => RawTerm.glueElim developedGlued
  | RawTerm.piTyCode _ _ => RawTerm.glueElim developedGlued
  | RawTerm.sigmaTyCode _ _ => RawTerm.glueElim developedGlued
  | RawTerm.productCode _ _ => RawTerm.glueElim developedGlued
  | RawTerm.sumCode _ _ => RawTerm.glueElim developedGlued
  | RawTerm.listCode _ => RawTerm.glueElim developedGlued
  | RawTerm.optionCode _ => RawTerm.glueElim developedGlued
  | RawTerm.eitherCode _ _ => RawTerm.glueElim developedGlued
  | RawTerm.idCode _ _ _ => RawTerm.glueElim developedGlued
  | RawTerm.equivCode _ _ => RawTerm.glueElim developedGlued
  | RawTerm.cumulUpMarker _ => RawTerm.glueElim developedGlued
  | RawTerm.uaToEquiv _ => RawTerm.glueElim developedGlued
  | RawTerm.equivApply _ _ => RawTerm.glueElim developedGlued
  | RawTerm.pathCompose _ _ => RawTerm.glueElim developedGlued
  | RawTerm.idToEquiv _ => RawTerm.glueElim developedGlued
  | RawTerm.oeqTrans _ _ => RawTerm.glueElim developedGlued
  | RawTerm.equivCompose _ _ => RawTerm.glueElim developedGlued

/-- Modal elimination redex: `modElim (modIntro payload) → payload`;
otherwise rebuild `modElim developedInner`. -/
def RawTerm.cdModElimCase {scope : Nat}
    (developedInner : RawTerm scope) : RawTerm scope :=
  match developedInner with
  | RawTerm.modIntro payload => payload
  | RawTerm.var _ => RawTerm.modElim developedInner
  | RawTerm.unit => RawTerm.modElim developedInner
  | RawTerm.lam _ => RawTerm.modElim developedInner
  | RawTerm.app _ _ => RawTerm.modElim developedInner
  | RawTerm.pair _ _ => RawTerm.modElim developedInner
  | RawTerm.fst _ => RawTerm.modElim developedInner
  | RawTerm.snd _ => RawTerm.modElim developedInner
  | RawTerm.boolTrue => RawTerm.modElim developedInner
  | RawTerm.boolFalse => RawTerm.modElim developedInner
  | RawTerm.boolElim _ _ _ => RawTerm.modElim developedInner
  | RawTerm.natZero => RawTerm.modElim developedInner
  | RawTerm.natSucc _ => RawTerm.modElim developedInner
  | RawTerm.natElim _ _ _ => RawTerm.modElim developedInner
  | RawTerm.natRec _ _ _ => RawTerm.modElim developedInner
  | RawTerm.listNil => RawTerm.modElim developedInner
  | RawTerm.listCons _ _ => RawTerm.modElim developedInner
  | RawTerm.listElim _ _ _ => RawTerm.modElim developedInner
  | RawTerm.optionNone => RawTerm.modElim developedInner
  | RawTerm.optionSome _ => RawTerm.modElim developedInner
  | RawTerm.optionMatch _ _ _ => RawTerm.modElim developedInner
  | RawTerm.eitherInl _ => RawTerm.modElim developedInner
  | RawTerm.eitherInr _ => RawTerm.modElim developedInner
  | RawTerm.eitherMatch _ _ _ => RawTerm.modElim developedInner
  | RawTerm.refl _ => RawTerm.modElim developedInner
  | RawTerm.idJ _ _ => RawTerm.modElim developedInner
  | RawTerm.modElim _ => RawTerm.modElim developedInner
  | RawTerm.subsume _ => RawTerm.modElim developedInner
  | RawTerm.interval0 => RawTerm.modElim developedInner
  | RawTerm.interval1 => RawTerm.modElim developedInner
  | RawTerm.intervalOpp _ => RawTerm.modElim developedInner
  | RawTerm.intervalMeet _ _ => RawTerm.modElim developedInner
  | RawTerm.intervalJoin _ _ => RawTerm.modElim developedInner
  | RawTerm.pathLam _ => RawTerm.modElim developedInner
  | RawTerm.pathApp _ _ => RawTerm.modElim developedInner
  | RawTerm.glueIntro _ _ => RawTerm.modElim developedInner
  | RawTerm.glueElim _ => RawTerm.modElim developedInner
  | RawTerm.transp _ _ => RawTerm.modElim developedInner
  | RawTerm.transpFill _ _ _ => RawTerm.modElim developedInner
  | RawTerm.hcomp _ _ => RawTerm.modElim developedInner
  | RawTerm.oeqRefl _ => RawTerm.modElim developedInner
  | RawTerm.oeqJ _ _ => RawTerm.modElim developedInner
  | RawTerm.oeqFunext _ => RawTerm.modElim developedInner
  | RawTerm.idStrictRefl _ => RawTerm.modElim developedInner
  | RawTerm.idStrictRec _ _ => RawTerm.modElim developedInner
  | RawTerm.equivIntro _ _ => RawTerm.modElim developedInner
  | RawTerm.equivApp _ _ => RawTerm.modElim developedInner
  | RawTerm.refineIntro _ _ => RawTerm.modElim developedInner
  | RawTerm.refineElim _ => RawTerm.modElim developedInner
  | RawTerm.recordIntro _ => RawTerm.modElim developedInner
  | RawTerm.recordProj _ => RawTerm.modElim developedInner
  | RawTerm.codataUnfold _ _ => RawTerm.modElim developedInner
  | RawTerm.codataDest _ => RawTerm.modElim developedInner
  | RawTerm.sessionSend _ _ => RawTerm.modElim developedInner
  | RawTerm.sessionRecv _ => RawTerm.modElim developedInner
  | RawTerm.effectPerform _ _ => RawTerm.modElim developedInner
  | RawTerm.universeCode _ => RawTerm.modElim developedInner
  | RawTerm.arrowCode _ _ => RawTerm.modElim developedInner
  | RawTerm.piTyCode _ _ => RawTerm.modElim developedInner
  | RawTerm.sigmaTyCode _ _ => RawTerm.modElim developedInner
  | RawTerm.productCode _ _ => RawTerm.modElim developedInner
  | RawTerm.sumCode _ _ => RawTerm.modElim developedInner
  | RawTerm.listCode _ => RawTerm.modElim developedInner
  | RawTerm.optionCode _ => RawTerm.modElim developedInner
  | RawTerm.eitherCode _ _ => RawTerm.modElim developedInner
  | RawTerm.idCode _ _ _ => RawTerm.modElim developedInner
  | RawTerm.equivCode _ _ => RawTerm.modElim developedInner
  | RawTerm.cumulUpMarker _ => RawTerm.modElim developedInner
  | RawTerm.uaToEquiv _ => RawTerm.modElim developedInner
  | RawTerm.equivApply _ _ => RawTerm.modElim developedInner
  | RawTerm.pathCompose _ _ => RawTerm.modElim developedInner
  | RawTerm.idToEquiv _ => RawTerm.modElim developedInner
  | RawTerm.oeqTrans _ _ => RawTerm.modElim developedInner
  | RawTerm.equivCompose _ _ => RawTerm.modElim developedInner

/-- Refinement elimination redex: `refineElim (refineIntro value proof)
→ value`; otherwise rebuild `refineElim dr`. -/
def RawTerm.cdRefineElimCase {scope : Nat}
    (developedRefined : RawTerm scope) : RawTerm scope :=
  match developedRefined with
  | RawTerm.refineIntro rawValue _ => rawValue
  | RawTerm.var _ => RawTerm.refineElim developedRefined
  | RawTerm.unit => RawTerm.refineElim developedRefined
  | RawTerm.lam _ => RawTerm.refineElim developedRefined
  | RawTerm.app _ _ => RawTerm.refineElim developedRefined
  | RawTerm.pair _ _ => RawTerm.refineElim developedRefined
  | RawTerm.fst _ => RawTerm.refineElim developedRefined
  | RawTerm.snd _ => RawTerm.refineElim developedRefined
  | RawTerm.boolTrue => RawTerm.refineElim developedRefined
  | RawTerm.boolFalse => RawTerm.refineElim developedRefined
  | RawTerm.boolElim _ _ _ => RawTerm.refineElim developedRefined
  | RawTerm.natZero => RawTerm.refineElim developedRefined
  | RawTerm.natSucc _ => RawTerm.refineElim developedRefined
  | RawTerm.natElim _ _ _ => RawTerm.refineElim developedRefined
  | RawTerm.natRec _ _ _ => RawTerm.refineElim developedRefined
  | RawTerm.listNil => RawTerm.refineElim developedRefined
  | RawTerm.listCons _ _ => RawTerm.refineElim developedRefined
  | RawTerm.listElim _ _ _ => RawTerm.refineElim developedRefined
  | RawTerm.optionNone => RawTerm.refineElim developedRefined
  | RawTerm.optionSome _ => RawTerm.refineElim developedRefined
  | RawTerm.optionMatch _ _ _ => RawTerm.refineElim developedRefined
  | RawTerm.eitherInl _ => RawTerm.refineElim developedRefined
  | RawTerm.eitherInr _ => RawTerm.refineElim developedRefined
  | RawTerm.eitherMatch _ _ _ => RawTerm.refineElim developedRefined
  | RawTerm.refl _ => RawTerm.refineElim developedRefined
  | RawTerm.idJ _ _ => RawTerm.refineElim developedRefined
  | RawTerm.modIntro _ => RawTerm.refineElim developedRefined
  | RawTerm.modElim _ => RawTerm.refineElim developedRefined
  | RawTerm.subsume _ => RawTerm.refineElim developedRefined
  | RawTerm.interval0 => RawTerm.refineElim developedRefined
  | RawTerm.interval1 => RawTerm.refineElim developedRefined
  | RawTerm.intervalOpp _ => RawTerm.refineElim developedRefined
  | RawTerm.intervalMeet _ _ => RawTerm.refineElim developedRefined
  | RawTerm.intervalJoin _ _ => RawTerm.refineElim developedRefined
  | RawTerm.pathLam _ => RawTerm.refineElim developedRefined
  | RawTerm.pathApp _ _ => RawTerm.refineElim developedRefined
  | RawTerm.glueIntro _ _ => RawTerm.refineElim developedRefined
  | RawTerm.glueElim _ => RawTerm.refineElim developedRefined
  | RawTerm.transp _ _ => RawTerm.refineElim developedRefined
  | RawTerm.transpFill _ _ _ => RawTerm.refineElim developedRefined
  | RawTerm.hcomp _ _ => RawTerm.refineElim developedRefined
  | RawTerm.oeqRefl _ => RawTerm.refineElim developedRefined
  | RawTerm.oeqJ _ _ => RawTerm.refineElim developedRefined
  | RawTerm.oeqFunext _ => RawTerm.refineElim developedRefined
  | RawTerm.idStrictRefl _ => RawTerm.refineElim developedRefined
  | RawTerm.idStrictRec _ _ => RawTerm.refineElim developedRefined
  | RawTerm.equivIntro _ _ => RawTerm.refineElim developedRefined
  | RawTerm.equivApp _ _ => RawTerm.refineElim developedRefined
  | RawTerm.refineElim _ => RawTerm.refineElim developedRefined
  | RawTerm.recordIntro _ => RawTerm.refineElim developedRefined
  | RawTerm.recordProj _ => RawTerm.refineElim developedRefined
  | RawTerm.codataUnfold _ _ => RawTerm.refineElim developedRefined
  | RawTerm.codataDest _ => RawTerm.refineElim developedRefined
  | RawTerm.sessionSend _ _ => RawTerm.refineElim developedRefined
  | RawTerm.sessionRecv _ => RawTerm.refineElim developedRefined
  | RawTerm.effectPerform _ _ => RawTerm.refineElim developedRefined
  | RawTerm.universeCode _ => RawTerm.refineElim developedRefined
  | RawTerm.arrowCode _ _ => RawTerm.refineElim developedRefined
  | RawTerm.piTyCode _ _ => RawTerm.refineElim developedRefined
  | RawTerm.sigmaTyCode _ _ => RawTerm.refineElim developedRefined
  | RawTerm.productCode _ _ => RawTerm.refineElim developedRefined
  | RawTerm.sumCode _ _ => RawTerm.refineElim developedRefined
  | RawTerm.listCode _ => RawTerm.refineElim developedRefined
  | RawTerm.optionCode _ => RawTerm.refineElim developedRefined
  | RawTerm.eitherCode _ _ => RawTerm.refineElim developedRefined
  | RawTerm.idCode _ _ _ => RawTerm.refineElim developedRefined
  | RawTerm.equivCode _ _ => RawTerm.refineElim developedRefined
  | RawTerm.cumulUpMarker _ => RawTerm.refineElim developedRefined
  | RawTerm.uaToEquiv _ => RawTerm.refineElim developedRefined
  | RawTerm.equivApply _ _ => RawTerm.refineElim developedRefined
  | RawTerm.pathCompose _ _ => RawTerm.refineElim developedRefined
  | RawTerm.idToEquiv _ => RawTerm.refineElim developedRefined
  | RawTerm.oeqTrans _ _ => RawTerm.refineElim developedRefined
  | RawTerm.equivCompose _ _ => RawTerm.refineElim developedRefined

end LeanFX2
