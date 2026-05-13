import LeanFX2.Algo.WHNF.NullaryInversions

/-! # LeanFX2.Algo.WHNF.PayloadInversions — raw recovery for payload heads

For `natSucc / listCons / optionSome / eitherInl / eitherInr`,
the raw form has a payload (predecessor / head-tail / value).
Each headCtor witness gives an EXISTENTIAL: the raw is some
ctor-application with a specific payload.

These extend the no-payload lemmas in `NullaryInversions` to support
payload-bearing β/ι firings in `Term.headStep?` (M08).  The trailing
`unit` recovery rounds out the canonical-leaf set.

## Root status

Layer 3 typed-algorithm WHNF helper.  Zero-axiom under
`LeanFX2Audit`. -/

namespace LeanFX2

/-- If `someTerm.headCtor = .natSucc`, the raw is `natSucc`-shaped
for some predecessor raw. -/
theorem Term.headCtor_natSucc_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.natSucc) :
    ∃ (predRaw : RawTerm scope), raw = RawTerm.natSucc predRaw := by
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
  | natSucc _ => exact ⟨_, rfl⟩
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

/-- If `someTerm.headCtor = .listCons`, the raw is `listCons`-shaped. -/
theorem Term.headCtor_listCons_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.listCons) :
    ∃ (headRaw tailRaw : RawTerm scope), raw = RawTerm.listCons headRaw tailRaw := by
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
  | listCons _ _ => exact ⟨_, _, rfl⟩
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

/-- If `someTerm.headCtor = .optionSome`, the raw is `optionSome`-shaped. -/
theorem Term.headCtor_optionSome_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.optionSome) :
    ∃ (valueRaw : RawTerm scope), raw = RawTerm.optionSome valueRaw := by
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
  | optionNone => nomatch headEq
  | optionSome _ => exact ⟨_, rfl⟩
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

/-- If `someTerm.headCtor = .eitherInl`, the raw is `eitherInl`-shaped. -/
theorem Term.headCtor_eitherInl_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.eitherInl) :
    ∃ (valueRaw : RawTerm scope), raw = RawTerm.eitherInl valueRaw := by
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
  | optionNone => nomatch headEq
  | optionSome _ => nomatch headEq
  | optionMatch _ _ _ => nomatch headEq
  | eitherInl _ => exact ⟨_, rfl⟩
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

/-- If `someTerm.headCtor = .eitherInr`, the raw is `eitherInr`-shaped. -/
theorem Term.headCtor_eitherInr_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.eitherInr) :
    ∃ (valueRaw : RawTerm scope), raw = RawTerm.eitherInr valueRaw := by
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
  | optionNone => nomatch headEq
  | optionSome _ => nomatch headEq
  | optionMatch _ _ _ => nomatch headEq
  | eitherInl _ => nomatch headEq
  | eitherInr _ => exact ⟨_, rfl⟩
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

/-- If a term's `headCtor` is `unit`, its raw is `RawTerm.unit`. -/
theorem Term.headCtor_unit_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.unit) :
    raw = RawTerm.unit := by
  cases someTerm with
  | var _ => nomatch headEq
  | unit => rfl
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
