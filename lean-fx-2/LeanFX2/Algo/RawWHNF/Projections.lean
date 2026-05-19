import LeanFX2.Algo.RawWHNF.HeadCtor

namespace LeanFX2

/-! ## ?-projection helpers — full 28-arm enumeration

Each helper extracts data from a specific RawTerm constructor.
Full enumeration of all 28 ctors keeps every match propext-free
(per `feedback_lean_zero_axiom_match.md`: wildcards on dependent
inductives always leak propext, full enumeration is clean for
universal-index projection targets).

Verbose but mechanical — each non-matching ctor returns `none`
(or `false` for `isRefl`).  The compiler reduces these helpers
on closed terms, so smoke tests via `rfl` work. -/

/-- Project the body of a `lam` term.  See file-level comment
for the "full enumeration not wildcard" rule. -/
def RawTerm.lamBody? {scope : Nat} (term : RawTerm scope) :
    Option (RawTerm (scope + 1)) :=
  match term with
  | .lam body => some body
  | .var _ => none | .unit => none | .app _ _ => none
  | .pair _ _ => none | .fst _ => none | .snd _ => none
  | .boolTrue => none | .boolFalse => none | .boolElim _ _ _ => none
  | .natZero => none | .natSucc _ => none
  | .natElim _ _ _ => none | .natRec _ _ _ => none
  | .listNil => none | .listCons _ _ => none | .listElim _ _ _ => none
  | .optionNone => none | .optionSome _ => none | .optionMatch _ _ _ => none
  | .eitherInl _ => none | .eitherInr _ => none | .eitherMatch _ _ _ => none
  | .refl _ => none | .idJ _ _ => none
  | .modIntro _ => none | .modElim _ => none | .subsume _ => none
  | .interval0 => none | .interval1 => none
  | .intervalOpp _ => none | .intervalMeet _ _ => none | .intervalJoin _ _ => none
  | .pathLam _ => none | .pathApp _ _ => none
  | .glueIntro _ _ => none | .glueElim _ => none
  | .transp _ _ => none | .hcomp _ _ => none
  | .oeqRefl _ => none | .oeqJ _ _ => none | .oeqFunext _ => none
  | .idStrictRefl _ => none | .idStrictRec _ _ => none
  | .equivIntro _ _ => none | .equivApp _ _ => none
  | .refineIntro _ _ => none | .refineElim _ => none
  | .recordIntro _ => none | .recordProj _ => none
  | .codataUnfold _ _ => none | .codataDest _ => none
  | .sessionSend _ _ => none | .sessionRecv _ => none
  | .effectPerform _ _ => none
  | .universeCode _ => none
  | .arrowCode _ _ => none | .piTyCode _ _ => none | .sigmaTyCode _ _ => none
  | .productCode _ _ => none | .sumCode _ _ => none
  | .listCode _ => none | .optionCode _ => none | .eitherCode _ _ => none
  | .idCode _ _ _ => none | .equivCode _ _ => none
  | .cumulUpMarker _ => none | .uaToEquiv _ => none | .equivApply _ _ => none
  | .pathCompose _ _ => none | .idToEquiv _ => none
  | .oeqTrans _ _ => none | .equivCompose _ _ => none
  | .transpFill _ _ _ => none

/-- Project the components of a `pair` term. -/
def RawTerm.pairComponents? {scope : Nat} (term : RawTerm scope) :
    Option (RawTerm scope × RawTerm scope) :=
  match term with
  | .pair firstValue secondValue => some (firstValue, secondValue)
  | .var _ => none | .unit => none | .lam _ => none | .app _ _ => none
  | .fst _ => none | .snd _ => none
  | .boolTrue => none | .boolFalse => none | .boolElim _ _ _ => none
  | .natZero => none | .natSucc _ => none
  | .natElim _ _ _ => none | .natRec _ _ _ => none
  | .listNil => none | .listCons _ _ => none | .listElim _ _ _ => none
  | .optionNone => none | .optionSome _ => none | .optionMatch _ _ _ => none
  | .eitherInl _ => none | .eitherInr _ => none | .eitherMatch _ _ _ => none
  | .refl _ => none | .idJ _ _ => none
  | .modIntro _ => none | .modElim _ => none | .subsume _ => none
  | .interval0 => none | .interval1 => none
  | .intervalOpp _ => none | .intervalMeet _ _ => none | .intervalJoin _ _ => none
  | .pathLam _ => none | .pathApp _ _ => none
  | .glueIntro _ _ => none | .glueElim _ => none
  | .transp _ _ => none | .hcomp _ _ => none
  | .oeqRefl _ => none | .oeqJ _ _ => none | .oeqFunext _ => none
  | .idStrictRefl _ => none | .idStrictRec _ _ => none
  | .equivIntro _ _ => none | .equivApp _ _ => none
  | .refineIntro _ _ => none | .refineElim _ => none
  | .recordIntro _ => none | .recordProj _ => none
  | .codataUnfold _ _ => none | .codataDest _ => none
  | .sessionSend _ _ => none | .sessionRecv _ => none
  | .effectPerform _ _ => none
  | .universeCode _ => none
  | .arrowCode _ _ => none | .piTyCode _ _ => none | .sigmaTyCode _ _ => none
  | .productCode _ _ => none | .sumCode _ _ => none
  | .listCode _ => none | .optionCode _ => none | .eitherCode _ _ => none
  | .idCode _ _ _ => none | .equivCode _ _ => none
  | .cumulUpMarker _ => none | .uaToEquiv _ => none | .equivApply _ _ => none
  | .pathCompose _ _ => none | .idToEquiv _ => none
  | .oeqTrans _ _ => none | .equivCompose _ _ => none
  | .transpFill _ _ _ => none

/-- Project the predecessor from a `natSucc` term. -/
def RawTerm.natSuccPred? {scope : Nat} (term : RawTerm scope) :
    Option (RawTerm scope) :=
  match term with
  | .natSucc predecessor => some predecessor
  | .var _ => none | .unit => none | .lam _ => none | .app _ _ => none
  | .pair _ _ => none | .fst _ => none | .snd _ => none
  | .boolTrue => none | .boolFalse => none | .boolElim _ _ _ => none
  | .natZero => none
  | .natElim _ _ _ => none | .natRec _ _ _ => none
  | .listNil => none | .listCons _ _ => none | .listElim _ _ _ => none
  | .optionNone => none | .optionSome _ => none | .optionMatch _ _ _ => none
  | .eitherInl _ => none | .eitherInr _ => none | .eitherMatch _ _ _ => none
  | .refl _ => none | .idJ _ _ => none
  | .modIntro _ => none | .modElim _ => none | .subsume _ => none
  | .interval0 => none | .interval1 => none
  | .intervalOpp _ => none | .intervalMeet _ _ => none | .intervalJoin _ _ => none
  | .pathLam _ => none | .pathApp _ _ => none
  | .glueIntro _ _ => none | .glueElim _ => none
  | .transp _ _ => none | .hcomp _ _ => none
  | .oeqRefl _ => none | .oeqJ _ _ => none | .oeqFunext _ => none
  | .idStrictRefl _ => none | .idStrictRec _ _ => none
  | .equivIntro _ _ => none | .equivApp _ _ => none
  | .refineIntro _ _ => none | .refineElim _ => none
  | .recordIntro _ => none | .recordProj _ => none
  | .codataUnfold _ _ => none | .codataDest _ => none
  | .sessionSend _ _ => none | .sessionRecv _ => none
  | .effectPerform _ _ => none
  | .universeCode _ => none
  | .arrowCode _ _ => none | .piTyCode _ _ => none | .sigmaTyCode _ _ => none
  | .productCode _ _ => none | .sumCode _ _ => none
  | .listCode _ => none | .optionCode _ => none | .eitherCode _ _ => none
  | .idCode _ _ _ => none | .equivCode _ _ => none
  | .cumulUpMarker _ => none | .uaToEquiv _ => none | .equivApply _ _ => none
  | .pathCompose _ _ => none | .idToEquiv _ => none
  | .oeqTrans _ _ => none | .equivCompose _ _ => none
  | .transpFill _ _ _ => none

/-- Project head/tail from a `listCons`. -/
def RawTerm.listConsParts? {scope : Nat} (term : RawTerm scope) :
    Option (RawTerm scope × RawTerm scope) :=
  match term with
  | .listCons headTerm tailTerm => some (headTerm, tailTerm)
  | .var _ => none | .unit => none | .lam _ => none | .app _ _ => none
  | .pair _ _ => none | .fst _ => none | .snd _ => none
  | .boolTrue => none | .boolFalse => none | .boolElim _ _ _ => none
  | .natZero => none | .natSucc _ => none
  | .natElim _ _ _ => none | .natRec _ _ _ => none
  | .listNil => none | .listElim _ _ _ => none
  | .optionNone => none | .optionSome _ => none | .optionMatch _ _ _ => none
  | .eitherInl _ => none | .eitherInr _ => none | .eitherMatch _ _ _ => none
  | .refl _ => none | .idJ _ _ => none
  | .modIntro _ => none | .modElim _ => none | .subsume _ => none
  | .interval0 => none | .interval1 => none
  | .intervalOpp _ => none | .intervalMeet _ _ => none | .intervalJoin _ _ => none
  | .pathLam _ => none | .pathApp _ _ => none
  | .glueIntro _ _ => none | .glueElim _ => none
  | .transp _ _ => none | .hcomp _ _ => none
  | .oeqRefl _ => none | .oeqJ _ _ => none | .oeqFunext _ => none
  | .idStrictRefl _ => none | .idStrictRec _ _ => none
  | .equivIntro _ _ => none | .equivApp _ _ => none
  | .refineIntro _ _ => none | .refineElim _ => none
  | .recordIntro _ => none | .recordProj _ => none
  | .codataUnfold _ _ => none | .codataDest _ => none
  | .sessionSend _ _ => none | .sessionRecv _ => none
  | .effectPerform _ _ => none
  | .universeCode _ => none
  | .arrowCode _ _ => none | .piTyCode _ _ => none | .sigmaTyCode _ _ => none
  | .productCode _ _ => none | .sumCode _ _ => none
  | .listCode _ => none | .optionCode _ => none | .eitherCode _ _ => none
  | .idCode _ _ _ => none | .equivCode _ _ => none
  | .cumulUpMarker _ => none | .uaToEquiv _ => none | .equivApply _ _ => none
  | .pathCompose _ _ => none | .idToEquiv _ => none
  | .oeqTrans _ _ => none | .equivCompose _ _ => none
  | .transpFill _ _ _ => none

/-- Project the value from `optionSome`. -/
def RawTerm.optionSomeValue? {scope : Nat} (term : RawTerm scope) :
    Option (RawTerm scope) :=
  match term with
  | .optionSome valueTerm => some valueTerm
  | .var _ => none | .unit => none | .lam _ => none | .app _ _ => none
  | .pair _ _ => none | .fst _ => none | .snd _ => none
  | .boolTrue => none | .boolFalse => none | .boolElim _ _ _ => none
  | .natZero => none | .natSucc _ => none
  | .natElim _ _ _ => none | .natRec _ _ _ => none
  | .listNil => none | .listCons _ _ => none | .listElim _ _ _ => none
  | .optionNone => none | .optionMatch _ _ _ => none
  | .eitherInl _ => none | .eitherInr _ => none | .eitherMatch _ _ _ => none
  | .refl _ => none | .idJ _ _ => none
  | .modIntro _ => none | .modElim _ => none | .subsume _ => none
  | .interval0 => none | .interval1 => none
  | .intervalOpp _ => none | .intervalMeet _ _ => none | .intervalJoin _ _ => none
  | .pathLam _ => none | .pathApp _ _ => none
  | .glueIntro _ _ => none | .glueElim _ => none
  | .transp _ _ => none | .hcomp _ _ => none
  | .oeqRefl _ => none | .oeqJ _ _ => none | .oeqFunext _ => none
  | .idStrictRefl _ => none | .idStrictRec _ _ => none
  | .equivIntro _ _ => none | .equivApp _ _ => none
  | .refineIntro _ _ => none | .refineElim _ => none
  | .recordIntro _ => none | .recordProj _ => none
  | .codataUnfold _ _ => none | .codataDest _ => none
  | .sessionSend _ _ => none | .sessionRecv _ => none
  | .effectPerform _ _ => none
  | .universeCode _ => none
  | .arrowCode _ _ => none | .piTyCode _ _ => none | .sigmaTyCode _ _ => none
  | .productCode _ _ => none | .sumCode _ _ => none
  | .listCode _ => none | .optionCode _ => none | .eitherCode _ _ => none
  | .idCode _ _ _ => none | .equivCode _ _ => none
  | .cumulUpMarker _ => none | .uaToEquiv _ => none | .equivApply _ _ => none
  | .pathCompose _ _ => none | .idToEquiv _ => none
  | .oeqTrans _ _ => none | .equivCompose _ _ => none
  | .transpFill _ _ _ => none

/-- Project the value from `eitherInl`. -/
def RawTerm.eitherInlValue? {scope : Nat} (term : RawTerm scope) :
    Option (RawTerm scope) :=
  match term with
  | .eitherInl valueTerm => some valueTerm
  | .var _ => none | .unit => none | .lam _ => none | .app _ _ => none
  | .pair _ _ => none | .fst _ => none | .snd _ => none
  | .boolTrue => none | .boolFalse => none | .boolElim _ _ _ => none
  | .natZero => none | .natSucc _ => none
  | .natElim _ _ _ => none | .natRec _ _ _ => none
  | .listNil => none | .listCons _ _ => none | .listElim _ _ _ => none
  | .optionNone => none | .optionSome _ => none | .optionMatch _ _ _ => none
  | .eitherInr _ => none | .eitherMatch _ _ _ => none
  | .refl _ => none | .idJ _ _ => none
  | .modIntro _ => none | .modElim _ => none | .subsume _ => none
  | .interval0 => none | .interval1 => none
  | .intervalOpp _ => none | .intervalMeet _ _ => none | .intervalJoin _ _ => none
  | .pathLam _ => none | .pathApp _ _ => none
  | .glueIntro _ _ => none | .glueElim _ => none
  | .transp _ _ => none | .hcomp _ _ => none
  | .oeqRefl _ => none | .oeqJ _ _ => none | .oeqFunext _ => none
  | .idStrictRefl _ => none | .idStrictRec _ _ => none
  | .equivIntro _ _ => none | .equivApp _ _ => none
  | .refineIntro _ _ => none | .refineElim _ => none
  | .recordIntro _ => none | .recordProj _ => none
  | .codataUnfold _ _ => none | .codataDest _ => none
  | .sessionSend _ _ => none | .sessionRecv _ => none
  | .effectPerform _ _ => none
  | .universeCode _ => none
  | .arrowCode _ _ => none | .piTyCode _ _ => none | .sigmaTyCode _ _ => none
  | .productCode _ _ => none | .sumCode _ _ => none
  | .listCode _ => none | .optionCode _ => none | .eitherCode _ _ => none
  | .idCode _ _ _ => none | .equivCode _ _ => none
  | .cumulUpMarker _ => none | .uaToEquiv _ => none | .equivApply _ _ => none
  | .pathCompose _ _ => none | .idToEquiv _ => none
  | .oeqTrans _ _ => none | .equivCompose _ _ => none
  | .transpFill _ _ _ => none

/-- Project the value from `eitherInr`. -/
def RawTerm.eitherInrValue? {scope : Nat} (term : RawTerm scope) :
    Option (RawTerm scope) :=
  match term with
  | .eitherInr valueTerm => some valueTerm
  | .var _ => none | .unit => none | .lam _ => none | .app _ _ => none
  | .pair _ _ => none | .fst _ => none | .snd _ => none
  | .boolTrue => none | .boolFalse => none | .boolElim _ _ _ => none
  | .natZero => none | .natSucc _ => none
  | .natElim _ _ _ => none | .natRec _ _ _ => none
  | .listNil => none | .listCons _ _ => none | .listElim _ _ _ => none
  | .optionNone => none | .optionSome _ => none | .optionMatch _ _ _ => none
  | .eitherInl _ => none | .eitherMatch _ _ _ => none
  | .refl _ => none | .idJ _ _ => none
  | .modIntro _ => none | .modElim _ => none | .subsume _ => none
  | .interval0 => none | .interval1 => none
  | .intervalOpp _ => none | .intervalMeet _ _ => none | .intervalJoin _ _ => none
  | .pathLam _ => none | .pathApp _ _ => none
  | .glueIntro _ _ => none | .glueElim _ => none
  | .transp _ _ => none | .hcomp _ _ => none
  | .oeqRefl _ => none | .oeqJ _ _ => none | .oeqFunext _ => none
  | .idStrictRefl _ => none | .idStrictRec _ _ => none
  | .equivIntro _ _ => none | .equivApp _ _ => none
  | .refineIntro _ _ => none | .refineElim _ => none
  | .recordIntro _ => none | .recordProj _ => none
  | .codataUnfold _ _ => none | .codataDest _ => none
  | .sessionSend _ _ => none | .sessionRecv _ => none
  | .effectPerform _ _ => none
  | .universeCode _ => none
  | .arrowCode _ _ => none | .piTyCode _ _ => none | .sigmaTyCode _ _ => none
  | .productCode _ _ => none | .sumCode _ _ => none
  | .listCode _ => none | .optionCode _ => none | .eitherCode _ _ => none
  | .idCode _ _ _ => none | .equivCode _ _ => none
  | .cumulUpMarker _ => none | .uaToEquiv _ => none | .equivApply _ _ => none
  | .pathCompose _ _ => none | .idToEquiv _ => none
  | .oeqTrans _ _ => none | .equivCompose _ _ => none
  | .transpFill _ _ _ => none

/-- Test whether a term is a `refl` (independent of the witness). -/
def RawTerm.isRefl {scope : Nat} (term : RawTerm scope) : Bool :=
  match term with
  | .refl _ => true
  | .var _ => false | .unit => false | .lam _ => false | .app _ _ => false
  | .pair _ _ => false | .fst _ => false | .snd _ => false
  | .boolTrue => false | .boolFalse => false | .boolElim _ _ _ => false
  | .natZero => false | .natSucc _ => false
  | .natElim _ _ _ => false | .natRec _ _ _ => false
  | .listNil => false | .listCons _ _ => false | .listElim _ _ _ => false
  | .optionNone => false | .optionSome _ => false | .optionMatch _ _ _ => false
  | .eitherInl _ => false | .eitherInr _ => false | .eitherMatch _ _ _ => false
  | .idJ _ _ => false
  | .modIntro _ => false | .modElim _ => false | .subsume _ => false
  | .interval0 => false | .interval1 => false
  | .intervalOpp _ => false | .intervalMeet _ _ => false | .intervalJoin _ _ => false
  | .pathLam _ => false | .pathApp _ _ => false
  | .glueIntro _ _ => false | .glueElim _ => false
  | .transp _ _ => false | .hcomp _ _ => false
  | .oeqRefl _ => false | .oeqJ _ _ => false | .oeqFunext _ => false
  | .idStrictRefl _ => false | .idStrictRec _ _ => false
  | .equivIntro _ _ => false | .equivApp _ _ => false
  | .refineIntro _ _ => false | .refineElim _ => false
  | .recordIntro _ => false | .recordProj _ => false
  | .codataUnfold _ _ => false | .codataDest _ => false
  | .sessionSend _ _ => false | .sessionRecv _ => false
  | .effectPerform _ _ => false
  | .universeCode _ => false
  | .arrowCode _ _ => false | .piTyCode _ _ => false | .sigmaTyCode _ _ => false
  | .productCode _ _ => false | .sumCode _ _ => false
  | .listCode _ => false | .optionCode _ => false | .eitherCode _ _ => false
  | .idCode _ _ _ => false | .equivCode _ _ => false
  | .cumulUpMarker _ => false | .uaToEquiv _ => false | .equivApply _ _ => false
  | .pathCompose _ _ => false | .idToEquiv _ => false
  | .oeqTrans _ _ => false | .equivCompose _ _ => false
  | .transpFill _ _ _ => false

end LeanFX2
