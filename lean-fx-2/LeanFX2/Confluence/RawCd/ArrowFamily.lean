import LeanFX2.Foundation.RawSubst
import LeanFX2.Foundation.RawPartialRename

/-! # LeanFX2.Confluence.RawCd.ArrowFamily

Per-redex helpers for the arrow / path-application families:
`cdAppCase` (β: `(λ b) a → b[a]`) and `cdPathAppCase`
(cubical pathLam β: `(pathLam body) @ point → body[point/i]`).

Every inner `match` enumerates all 55 `RawTerm` constructors
explicitly to satisfy AXIOMS.md Layer M strict-zero-axiom policy.

## Root status

Layer 2 confluence helper.  Consumed by `Confluence.RawCd` shim and
downstream `Confluence.RawCdLemma`. -/

namespace LeanFX2

/-- App redex: `(λ b) a → b[a]`; otherwise rebuild `app df da`.
55-arm full enumeration keeps match propext-clean. -/
def RawTerm.cdAppCase {scope : Nat}
    (developedFunction developedArgument : RawTerm scope) : RawTerm scope :=
  match developedFunction with
  | RawTerm.lam body => body.subst0 developedArgument
  | RawTerm.var _ => RawTerm.app developedFunction developedArgument
  | RawTerm.unit => RawTerm.app developedFunction developedArgument
  | RawTerm.app _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.pair _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.fst _ => RawTerm.app developedFunction developedArgument
  | RawTerm.snd _ => RawTerm.app developedFunction developedArgument
  | RawTerm.boolTrue => RawTerm.app developedFunction developedArgument
  | RawTerm.boolFalse => RawTerm.app developedFunction developedArgument
  | RawTerm.boolElim _ _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.natZero => RawTerm.app developedFunction developedArgument
  | RawTerm.natSucc _ => RawTerm.app developedFunction developedArgument
  | RawTerm.natElim _ _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.natRec _ _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.listNil => RawTerm.app developedFunction developedArgument
  | RawTerm.listCons _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.listElim _ _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.optionNone => RawTerm.app developedFunction developedArgument
  | RawTerm.optionSome _ => RawTerm.app developedFunction developedArgument
  | RawTerm.optionMatch _ _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.eitherInl _ => RawTerm.app developedFunction developedArgument
  | RawTerm.eitherInr _ => RawTerm.app developedFunction developedArgument
  | RawTerm.eitherMatch _ _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.refl _ => RawTerm.app developedFunction developedArgument
  | RawTerm.idJ _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.modIntro _ => RawTerm.app developedFunction developedArgument
  | RawTerm.modElim _ => RawTerm.app developedFunction developedArgument
  | RawTerm.subsume _ => RawTerm.app developedFunction developedArgument
  | RawTerm.interval0 => RawTerm.app developedFunction developedArgument
  | RawTerm.interval1 => RawTerm.app developedFunction developedArgument
  | RawTerm.intervalOpp _ => RawTerm.app developedFunction developedArgument
  | RawTerm.intervalMeet _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.intervalJoin _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.pathLam _ => RawTerm.app developedFunction developedArgument
  | RawTerm.pathApp _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.glueIntro _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.glueElim _ => RawTerm.app developedFunction developedArgument
  | RawTerm.transp _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.transpFill _ _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.hcomp _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.oeqRefl _ => RawTerm.app developedFunction developedArgument
  | RawTerm.oeqJ _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.oeqFunext _ => RawTerm.app developedFunction developedArgument
  | RawTerm.idStrictRefl _ => RawTerm.app developedFunction developedArgument
  | RawTerm.idStrictRec _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.equivIntro _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.equivApp _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.refineIntro _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.refineElim _ => RawTerm.app developedFunction developedArgument
  | RawTerm.recordIntro _ => RawTerm.app developedFunction developedArgument
  | RawTerm.recordProj _ => RawTerm.app developedFunction developedArgument
  | RawTerm.codataUnfold _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.codataDest _ => RawTerm.app developedFunction developedArgument
  | RawTerm.sessionSend _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.sessionRecv _ => RawTerm.app developedFunction developedArgument
  | RawTerm.effectPerform _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.universeCode _ => RawTerm.app developedFunction developedArgument
  | RawTerm.arrowCode _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.piTyCode _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.sigmaTyCode _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.productCode _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.sumCode _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.listCode _ => RawTerm.app developedFunction developedArgument
  | RawTerm.optionCode _ => RawTerm.app developedFunction developedArgument
  | RawTerm.eitherCode _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.idCode _ _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.equivCode _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.cumulUpMarker _ => RawTerm.app developedFunction developedArgument
  | RawTerm.uaToEquiv _ => RawTerm.app developedFunction developedArgument
  | RawTerm.equivApply _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.pathCompose _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.idToEquiv _ => RawTerm.app developedFunction developedArgument
  | RawTerm.oeqTrans _ _ => RawTerm.app developedFunction developedArgument
  | RawTerm.equivCompose _ _ => RawTerm.app developedFunction developedArgument

/-- Path application redex: `(pathLam body) @ point → body[point/i]`;
otherwise rebuild `pathApp dp di`. -/
def RawTerm.cdPathAppCase {scope : Nat}
    (developedPath developedInterval : RawTerm scope) : RawTerm scope :=
  match developedPath with
  | RawTerm.pathLam body => body.subst0 developedInterval
  | RawTerm.var _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.unit => RawTerm.pathApp developedPath developedInterval
  | RawTerm.lam _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.app _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.pair _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.fst _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.snd _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.boolTrue => RawTerm.pathApp developedPath developedInterval
  | RawTerm.boolFalse => RawTerm.pathApp developedPath developedInterval
  | RawTerm.boolElim _ _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.natZero => RawTerm.pathApp developedPath developedInterval
  | RawTerm.natSucc _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.natElim _ _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.natRec _ _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.listNil => RawTerm.pathApp developedPath developedInterval
  | RawTerm.listCons _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.listElim _ _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.optionNone => RawTerm.pathApp developedPath developedInterval
  | RawTerm.optionSome _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.optionMatch _ _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.eitherInl _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.eitherInr _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.eitherMatch _ _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.refl _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.idJ _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.modIntro _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.modElim _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.subsume _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.interval0 => RawTerm.pathApp developedPath developedInterval
  | RawTerm.interval1 => RawTerm.pathApp developedPath developedInterval
  | RawTerm.intervalOpp _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.intervalMeet _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.intervalJoin _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.pathApp _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.glueIntro _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.glueElim _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.transp _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.transpFill _ _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.hcomp _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.oeqRefl _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.oeqJ _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.oeqFunext _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.idStrictRefl _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.idStrictRec _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.equivIntro _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.equivApp _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.refineIntro _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.refineElim _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.recordIntro _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.recordProj _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.codataUnfold _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.codataDest _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.sessionSend _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.sessionRecv _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.effectPerform _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.universeCode _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.arrowCode _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.piTyCode _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.sigmaTyCode _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.productCode _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.sumCode _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.listCode _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.optionCode _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.eitherCode _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.idCode _ _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.equivCode _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.cumulUpMarker _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.uaToEquiv _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.equivApply _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.pathCompose _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.idToEquiv _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.oeqTrans _ _ => RawTerm.pathApp developedPath developedInterval
  | RawTerm.equivCompose _ _ => RawTerm.pathApp developedPath developedInterval

end LeanFX2
