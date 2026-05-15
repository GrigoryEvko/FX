import LeanFX2.Algo.WHNF.Evaluator

/-! # LeanFX2.Algo.WHNF.NullaryInversions — raw recovery for nullary heads

If `term.headCtor = X`, then term's raw form is uniquely determined
by `X` for nullary canonical heads (boolTrue/False, natZero, listNil,
optionNone).  These bridge lemmas convert the Bool-level dispatch
in `Term.headStep?` back into typed-level facts about the term's
raw projection — useful for deriving Step witnesses from headStep?
behavior (Algo/Soundness, Phase 9.G).

## Root status

Layer 3 typed-algorithm WHNF helper.  Zero-axiom under
`LeanFX2Audit`. -/

namespace LeanFX2

/-- If a term's `headCtor` is `boolTrue`, its raw projection
is `RawTerm.boolTrue`.  Zero-axiom via full Term enumeration with
`nomatch` for the contradictory cases. -/
theorem Term.headCtor_boolTrue_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.boolTrue) :
    raw = RawTerm.boolTrue := by
  cases someTerm with
  | var _ => nomatch headEq
  | unit => nomatch headEq
  | lam _ => nomatch headEq
  | app _ _ => nomatch headEq
  | lamPi _ => nomatch headEq
  | appPi _ _ => nomatch headEq
  | pair _ _ => nomatch headEq
  | fst _ => nomatch headEq
  | snd _ => nomatch headEq
  | boolTrue => rfl
  | boolFalse => nomatch headEq
  | boolElim _ _ _ => nomatch headEq
  | natZero => nomatch headEq
  | natSucc _ => nomatch headEq
  | natElim _ _ _ => nomatch headEq
  | natRec _ _ _ => nomatch headEq
  | listNil => nomatch headEq
  | listCons _ _ => nomatch headEq
  | listElim _ _ _ => nomatch headEq
  | optionNone => nomatch headEq
  | optionSome _ => nomatch headEq
  | optionMatch _ _ _ => nomatch headEq
  | eitherInl _ => nomatch headEq
  | eitherInr _ => nomatch headEq
  | eitherMatch _ _ _ => nomatch headEq
  | refl _ _ => nomatch headEq
  | idJ _ _ => nomatch headEq
  | oeqRefl _ _ => nomatch headEq
  | oeqJ _ _ => nomatch headEq
  | oeqFunext _ _ _ _ _ => nomatch headEq
  | idStrictRefl _ _ _ => nomatch headEq
  | idStrictRec _ _ _ => nomatch headEq
  | modIntro _ => nomatch headEq
  | modElim _ => nomatch headEq
  | subsume _ => nomatch headEq
  | interval0 => nomatch headEq
  | interval1 => nomatch headEq
  | intervalOpp _ => nomatch headEq
  | intervalMeet _ _ => nomatch headEq
  | intervalJoin _ _ => nomatch headEq
  | pathLam _ _ _ _ _ => nomatch headEq
  | pathApp _ _ _ => nomatch headEq
  | glueIntro _ _ _ _ _ => nomatch headEq
  | glueElim _ _ => nomatch headEq
  | transp _ _ _ _ _ _ _ _ _ => nomatch headEq
  | hcomp _ _ _ => nomatch headEq
  | hcompPath _ _ _ _ _ => nomatch headEq
  | recordIntro _ => nomatch headEq
  | recordProj _ => nomatch headEq
  | refineIntro _ _ _ => nomatch headEq
  | refineElim _ => nomatch headEq
  | codataUnfold _ _ => nomatch headEq
  | codataDest _ => nomatch headEq
  | sessionSend _ _ _ => nomatch headEq
  | sessionRecv _ => nomatch headEq
  | effectPerform _ _ _ _ _ _ => nomatch headEq
  | universeCode _ _ _ _ => nomatch headEq
  | cumulUp _ _ _ _ _ _ => nomatch headEq
  | equivReflId _ => nomatch headEq
  | funextRefl _ _ _ => nomatch headEq
  | equivReflIdAtId _ _ _ _ => nomatch headEq
  | funextReflAtId _ _ _ => nomatch headEq
  | equivIntroHet _ _ _ _ => nomatch headEq
  | equivApp _ _ => nomatch headEq
  | uaIntroHet _ _ _ _ _ => nomatch headEq
  | funextIntroHet _ _ _ _ => nomatch headEq
  | uaToEquiv _ _ _ _ _ _ _ => nomatch headEq
  | equivApply _ _ => nomatch headEq
  | arrowCode _ _ _ _ => nomatch headEq
  | piTyCode _ _ _ _ => nomatch headEq
  | sigmaTyCode _ _ _ _ => nomatch headEq
  | productCode _ _ _ _ => nomatch headEq
  | sumCode _ _ _ _ => nomatch headEq
  | listCode _ _ _ => nomatch headEq
  | optionCode _ _ _ => nomatch headEq
  | eitherCode _ _ _ _ => nomatch headEq
  | idCode _ _ _ _ _ => nomatch headEq
  | equivCode _ _ _ _ => nomatch headEq

/-- If a term's `headCtor` is `boolFalse`, its raw is `RawTerm.boolFalse`. -/
theorem Term.headCtor_boolFalse_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.boolFalse) :
    raw = RawTerm.boolFalse := by
  cases someTerm with
  | var _ => nomatch headEq
  | unit => nomatch headEq
  | lam _ => nomatch headEq
  | app _ _ => nomatch headEq
  | lamPi _ => nomatch headEq
  | appPi _ _ => nomatch headEq
  | pair _ _ => nomatch headEq
  | fst _ => nomatch headEq
  | snd _ => nomatch headEq
  | boolTrue => nomatch headEq
  | boolFalse => rfl
  | boolElim _ _ _ => nomatch headEq
  | natZero => nomatch headEq
  | natSucc _ => nomatch headEq
  | natElim _ _ _ => nomatch headEq
  | natRec _ _ _ => nomatch headEq
  | listNil => nomatch headEq
  | listCons _ _ => nomatch headEq
  | listElim _ _ _ => nomatch headEq
  | optionNone => nomatch headEq
  | optionSome _ => nomatch headEq
  | optionMatch _ _ _ => nomatch headEq
  | eitherInl _ => nomatch headEq
  | eitherInr _ => nomatch headEq
  | eitherMatch _ _ _ => nomatch headEq
  | refl _ _ => nomatch headEq
  | idJ _ _ => nomatch headEq
  | oeqRefl _ _ => nomatch headEq
  | oeqJ _ _ => nomatch headEq
  | oeqFunext _ _ _ _ _ => nomatch headEq
  | idStrictRefl _ _ _ => nomatch headEq
  | idStrictRec _ _ _ => nomatch headEq
  | modIntro _ => nomatch headEq
  | modElim _ => nomatch headEq
  | subsume _ => nomatch headEq
  | interval0 => nomatch headEq
  | interval1 => nomatch headEq
  | intervalOpp _ => nomatch headEq
  | intervalMeet _ _ => nomatch headEq
  | intervalJoin _ _ => nomatch headEq
  | pathLam _ _ _ _ _ => nomatch headEq
  | pathApp _ _ _ => nomatch headEq
  | glueIntro _ _ _ _ _ => nomatch headEq
  | glueElim _ _ => nomatch headEq
  | transp _ _ _ _ _ _ _ _ _ => nomatch headEq
  | hcomp _ _ _ => nomatch headEq
  | hcompPath _ _ _ _ _ => nomatch headEq
  | recordIntro _ => nomatch headEq
  | recordProj _ => nomatch headEq
  | refineIntro _ _ _ => nomatch headEq
  | refineElim _ => nomatch headEq
  | codataUnfold _ _ => nomatch headEq
  | codataDest _ => nomatch headEq
  | sessionSend _ _ _ => nomatch headEq
  | sessionRecv _ => nomatch headEq
  | effectPerform _ _ _ _ _ _ => nomatch headEq
  | universeCode _ _ _ _ => nomatch headEq
  | cumulUp _ _ _ _ _ _ => nomatch headEq
  | equivReflId _ => nomatch headEq
  | funextRefl _ _ _ => nomatch headEq
  | equivReflIdAtId _ _ _ _ => nomatch headEq
  | funextReflAtId _ _ _ => nomatch headEq
  | equivIntroHet _ _ _ _ => nomatch headEq
  | equivApp _ _ => nomatch headEq
  | uaIntroHet _ _ _ _ _ => nomatch headEq
  | funextIntroHet _ _ _ _ => nomatch headEq
  | uaToEquiv _ _ _ _ _ _ _ => nomatch headEq
  | equivApply _ _ => nomatch headEq
  | arrowCode _ _ _ _ => nomatch headEq
  | piTyCode _ _ _ _ => nomatch headEq
  | sigmaTyCode _ _ _ _ => nomatch headEq
  | productCode _ _ _ _ => nomatch headEq
  | sumCode _ _ _ _ => nomatch headEq
  | listCode _ _ _ => nomatch headEq
  | optionCode _ _ _ => nomatch headEq
  | eitherCode _ _ _ _ => nomatch headEq
  | idCode _ _ _ _ _ => nomatch headEq
  | equivCode _ _ _ _ => nomatch headEq

/-- If a term's `headCtor` is `natZero`, its raw is `RawTerm.natZero`. -/
theorem Term.headCtor_natZero_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.natZero) :
    raw = RawTerm.natZero := by
  cases someTerm with
  | var _ => nomatch headEq
  | unit => nomatch headEq
  | lam _ => nomatch headEq
  | app _ _ => nomatch headEq
  | lamPi _ => nomatch headEq
  | appPi _ _ => nomatch headEq
  | pair _ _ => nomatch headEq
  | fst _ => nomatch headEq
  | snd _ => nomatch headEq
  | boolTrue => nomatch headEq
  | boolFalse => nomatch headEq
  | boolElim _ _ _ => nomatch headEq
  | natZero => rfl
  | natSucc _ => nomatch headEq
  | natElim _ _ _ => nomatch headEq
  | natRec _ _ _ => nomatch headEq
  | listNil => nomatch headEq
  | listCons _ _ => nomatch headEq
  | listElim _ _ _ => nomatch headEq
  | optionNone => nomatch headEq
  | optionSome _ => nomatch headEq
  | optionMatch _ _ _ => nomatch headEq
  | eitherInl _ => nomatch headEq
  | eitherInr _ => nomatch headEq
  | eitherMatch _ _ _ => nomatch headEq
  | refl _ _ => nomatch headEq
  | idJ _ _ => nomatch headEq
  | oeqRefl _ _ => nomatch headEq
  | oeqJ _ _ => nomatch headEq
  | oeqFunext _ _ _ _ _ => nomatch headEq
  | idStrictRefl _ _ _ => nomatch headEq
  | idStrictRec _ _ _ => nomatch headEq
  | modIntro _ => nomatch headEq
  | modElim _ => nomatch headEq
  | subsume _ => nomatch headEq
  | interval0 => nomatch headEq
  | interval1 => nomatch headEq
  | intervalOpp _ => nomatch headEq
  | intervalMeet _ _ => nomatch headEq
  | intervalJoin _ _ => nomatch headEq
  | pathLam _ _ _ _ _ => nomatch headEq
  | pathApp _ _ _ => nomatch headEq
  | glueIntro _ _ _ _ _ => nomatch headEq
  | glueElim _ _ => nomatch headEq
  | transp _ _ _ _ _ _ _ _ _ => nomatch headEq
  | hcomp _ _ _ => nomatch headEq
  | hcompPath _ _ _ _ _ => nomatch headEq
  | recordIntro _ => nomatch headEq
  | recordProj _ => nomatch headEq
  | refineIntro _ _ _ => nomatch headEq
  | refineElim _ => nomatch headEq
  | codataUnfold _ _ => nomatch headEq
  | codataDest _ => nomatch headEq
  | sessionSend _ _ _ => nomatch headEq
  | sessionRecv _ => nomatch headEq
  | effectPerform _ _ _ _ _ _ => nomatch headEq
  | universeCode _ _ _ _ => nomatch headEq
  | cumulUp _ _ _ _ _ _ => nomatch headEq
  | equivReflId _ => nomatch headEq
  | funextRefl _ _ _ => nomatch headEq
  | equivReflIdAtId _ _ _ _ => nomatch headEq
  | funextReflAtId _ _ _ => nomatch headEq
  | equivIntroHet _ _ _ _ => nomatch headEq
  | equivApp _ _ => nomatch headEq
  | uaIntroHet _ _ _ _ _ => nomatch headEq
  | funextIntroHet _ _ _ _ => nomatch headEq
  | uaToEquiv _ _ _ _ _ _ _ => nomatch headEq
  | equivApply _ _ => nomatch headEq
  | arrowCode _ _ _ _ => nomatch headEq
  | piTyCode _ _ _ _ => nomatch headEq
  | sigmaTyCode _ _ _ _ => nomatch headEq
  | productCode _ _ _ _ => nomatch headEq
  | sumCode _ _ _ _ => nomatch headEq
  | listCode _ _ _ => nomatch headEq
  | optionCode _ _ _ => nomatch headEq
  | eitherCode _ _ _ _ => nomatch headEq
  | idCode _ _ _ _ _ => nomatch headEq
  | equivCode _ _ _ _ => nomatch headEq

/-- If a term's `headCtor` is `listNil`, its raw is `RawTerm.listNil`. -/
theorem Term.headCtor_listNil_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.listNil) :
    raw = RawTerm.listNil := by
  cases someTerm with
  | var _ => nomatch headEq
  | unit => nomatch headEq
  | lam _ => nomatch headEq
  | app _ _ => nomatch headEq
  | lamPi _ => nomatch headEq
  | appPi _ _ => nomatch headEq
  | pair _ _ => nomatch headEq
  | fst _ => nomatch headEq
  | snd _ => nomatch headEq
  | boolTrue => nomatch headEq
  | boolFalse => nomatch headEq
  | boolElim _ _ _ => nomatch headEq
  | natZero => nomatch headEq
  | natSucc _ => nomatch headEq
  | natElim _ _ _ => nomatch headEq
  | natRec _ _ _ => nomatch headEq
  | listNil => rfl
  | listCons _ _ => nomatch headEq
  | listElim _ _ _ => nomatch headEq
  | optionNone => nomatch headEq
  | optionSome _ => nomatch headEq
  | optionMatch _ _ _ => nomatch headEq
  | eitherInl _ => nomatch headEq
  | eitherInr _ => nomatch headEq
  | eitherMatch _ _ _ => nomatch headEq
  | refl _ _ => nomatch headEq
  | idJ _ _ => nomatch headEq
  | oeqRefl _ _ => nomatch headEq
  | oeqJ _ _ => nomatch headEq
  | oeqFunext _ _ _ _ _ => nomatch headEq
  | idStrictRefl _ _ _ => nomatch headEq
  | idStrictRec _ _ _ => nomatch headEq
  | modIntro _ => nomatch headEq
  | modElim _ => nomatch headEq
  | subsume _ => nomatch headEq
  | interval0 => nomatch headEq
  | interval1 => nomatch headEq
  | intervalOpp _ => nomatch headEq
  | intervalMeet _ _ => nomatch headEq
  | intervalJoin _ _ => nomatch headEq
  | pathLam _ _ _ _ _ => nomatch headEq
  | pathApp _ _ _ => nomatch headEq
  | glueIntro _ _ _ _ _ => nomatch headEq
  | glueElim _ _ => nomatch headEq
  | transp _ _ _ _ _ _ _ _ _ => nomatch headEq
  | hcomp _ _ _ => nomatch headEq
  | hcompPath _ _ _ _ _ => nomatch headEq
  | recordIntro _ => nomatch headEq
  | recordProj _ => nomatch headEq
  | refineIntro _ _ _ => nomatch headEq
  | refineElim _ => nomatch headEq
  | codataUnfold _ _ => nomatch headEq
  | codataDest _ => nomatch headEq
  | sessionSend _ _ _ => nomatch headEq
  | sessionRecv _ => nomatch headEq
  | effectPerform _ _ _ _ _ _ => nomatch headEq
  | universeCode _ _ _ _ => nomatch headEq
  | cumulUp _ _ _ _ _ _ => nomatch headEq
  | equivReflId _ => nomatch headEq
  | funextRefl _ _ _ => nomatch headEq
  | equivReflIdAtId _ _ _ _ => nomatch headEq
  | funextReflAtId _ _ _ => nomatch headEq
  | equivIntroHet _ _ _ _ => nomatch headEq
  | equivApp _ _ => nomatch headEq
  | uaIntroHet _ _ _ _ _ => nomatch headEq
  | funextIntroHet _ _ _ _ => nomatch headEq
  | uaToEquiv _ _ _ _ _ _ _ => nomatch headEq
  | equivApply _ _ => nomatch headEq
  | arrowCode _ _ _ _ => nomatch headEq
  | piTyCode _ _ _ _ => nomatch headEq
  | sigmaTyCode _ _ _ _ => nomatch headEq
  | productCode _ _ _ _ => nomatch headEq
  | sumCode _ _ _ _ => nomatch headEq
  | listCode _ _ _ => nomatch headEq
  | optionCode _ _ _ => nomatch headEq
  | eitherCode _ _ _ _ => nomatch headEq
  | idCode _ _ _ _ _ => nomatch headEq
  | equivCode _ _ _ _ => nomatch headEq

/-- If a term's `headCtor` is `optionNone`, its raw is `RawTerm.optionNone`. -/
theorem Term.headCtor_optionNone_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.optionNone) :
    raw = RawTerm.optionNone := by
  cases someTerm with
  | var _ => nomatch headEq
  | unit => nomatch headEq
  | lam _ => nomatch headEq
  | app _ _ => nomatch headEq
  | lamPi _ => nomatch headEq
  | appPi _ _ => nomatch headEq
  | pair _ _ => nomatch headEq
  | fst _ => nomatch headEq
  | snd _ => nomatch headEq
  | boolTrue => nomatch headEq
  | boolFalse => nomatch headEq
  | boolElim _ _ _ => nomatch headEq
  | natZero => nomatch headEq
  | natSucc _ => nomatch headEq
  | natElim _ _ _ => nomatch headEq
  | natRec _ _ _ => nomatch headEq
  | listNil => nomatch headEq
  | listCons _ _ => nomatch headEq
  | listElim _ _ _ => nomatch headEq
  | optionNone => rfl
  | optionSome _ => nomatch headEq
  | optionMatch _ _ _ => nomatch headEq
  | eitherInl _ => nomatch headEq
  | eitherInr _ => nomatch headEq
  | eitherMatch _ _ _ => nomatch headEq
  | refl _ _ => nomatch headEq
  | idJ _ _ => nomatch headEq
  | oeqRefl _ _ => nomatch headEq
  | oeqJ _ _ => nomatch headEq
  | oeqFunext _ _ _ _ _ => nomatch headEq
  | idStrictRefl _ _ _ => nomatch headEq
  | idStrictRec _ _ _ => nomatch headEq
  | modIntro _ => nomatch headEq
  | modElim _ => nomatch headEq
  | subsume _ => nomatch headEq
  | interval0 => nomatch headEq
  | interval1 => nomatch headEq
  | intervalOpp _ => nomatch headEq
  | intervalMeet _ _ => nomatch headEq
  | intervalJoin _ _ => nomatch headEq
  | pathLam _ _ _ _ _ => nomatch headEq
  | pathApp _ _ _ => nomatch headEq
  | glueIntro _ _ _ _ _ => nomatch headEq
  | glueElim _ _ => nomatch headEq
  | transp _ _ _ _ _ _ _ _ _ => nomatch headEq
  | hcomp _ _ _ => nomatch headEq
  | hcompPath _ _ _ _ _ => nomatch headEq
  | recordIntro _ => nomatch headEq
  | recordProj _ => nomatch headEq
  | refineIntro _ _ _ => nomatch headEq
  | refineElim _ => nomatch headEq
  | codataUnfold _ _ => nomatch headEq
  | codataDest _ => nomatch headEq
  | sessionSend _ _ _ => nomatch headEq
  | sessionRecv _ => nomatch headEq
  | effectPerform _ _ _ _ _ _ => nomatch headEq
  | universeCode _ _ _ _ => nomatch headEq
  | cumulUp _ _ _ _ _ _ => nomatch headEq
  | equivReflId _ => nomatch headEq
  | funextRefl _ _ _ => nomatch headEq
  | equivReflIdAtId _ _ _ _ => nomatch headEq
  | funextReflAtId _ _ _ => nomatch headEq
  | equivIntroHet _ _ _ _ => nomatch headEq
  | equivApp _ _ => nomatch headEq
  | uaIntroHet _ _ _ _ _ => nomatch headEq
  | funextIntroHet _ _ _ _ => nomatch headEq
  | uaToEquiv _ _ _ _ _ _ _ => nomatch headEq
  | equivApply _ _ => nomatch headEq
  | arrowCode _ _ _ _ => nomatch headEq
  | piTyCode _ _ _ _ => nomatch headEq
  | sigmaTyCode _ _ _ _ => nomatch headEq
  | productCode _ _ _ _ => nomatch headEq
  | sumCode _ _ _ _ => nomatch headEq
  | listCode _ _ _ => nomatch headEq
  | optionCode _ _ _ => nomatch headEq
  | eitherCode _ _ _ _ => nomatch headEq
  | idCode _ _ _ _ _ => nomatch headEq
  | equivCode _ _ _ _ => nomatch headEq

end LeanFX2
