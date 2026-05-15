import LeanFX2.Algo.WHNF
import LeanFX2.Term.Inversion
import LeanFX2.Reduction.Step

/-! # LeanFX2.Algo.Progress.CanonicalInterval

Canonical-form raw inversions for cubical-interval head ctors.
Given a typed Term whose `headCtor` is an interval value
(`interval0`, `interval1`, `intervalOpp`, `intervalMeet`,
`intervalJoin`), extract the raw shape `RawTerm.<intervalCtor>`.

## Root status

Interval-value canonical-form inversions; feed the headline
Progress proof for cubical β-rules. Zero-axiom under strict
policy. -/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat}

/-- If a term's `headCtor` is `interval0`, its raw is the niladic
constructor `RawTerm.interval0`.  Cubical-interval endpoint canonical
form (zero endpoint) needed by the Progress proof for cubical
path-elim / interval-meet / interval-join / interval-opp beta-rules
(scrutinee inversion when the scrutinee head is `interval0`).
Niladic-payload pattern (no schematic raws); first of the M05.A.2
interval-value cohort. -/
theorem Term.headCtor_interval0_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.interval0) :
    raw = RawTerm.interval0 := by
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
  | interval0 => rfl
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

/-- If a term's `headCtor` is `interval1`, its raw is the niladic
constructor `RawTerm.interval1`.  Cubical-interval endpoint canonical
form (one endpoint) needed by the Progress proof for cubical
path-elim / interval-meet / interval-join / interval-opp beta-rules
(scrutinee inversion when the scrutinee head is `interval1`).
Niladic-payload pattern; mirror of `interval0`.  Second of the
M05.A.2 interval-value cohort. -/
theorem Term.headCtor_interval1_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.interval1) :
    raw = RawTerm.interval1 := by
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
  | interval1 => rfl
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

/-- If a term's `headCtor` is `intervalOpp`, its raw is
`RawTerm.intervalOpp` of an inner interval raw at the outer scope.
Cubical-interval involution canonical form needed by the Progress
proof for cubical interval-opp-of-zero / interval-opp-of-one /
double-involution beta-rules (scrutinee inversion when the scrutinee
head is `intervalOpp`).  Unary-payload pattern with the inner
interval raw at outer scope (no scope shift); mirror of `natSucc`
unary intro shape from the M05.A.0 cohort.  Third of the M05.A.2
interval-value cohort. -/
theorem Term.headCtor_intervalOpp_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.intervalOpp) :
    ∃ innerRaw : RawTerm scope, raw = RawTerm.intervalOpp innerRaw := by
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
  | intervalOpp _ => exact ⟨_, rfl⟩
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

/-- If a term's `headCtor` is `intervalMeet`, its raw is
`RawTerm.intervalMeet` of a left interval raw and a right interval
raw (both at the outer scope).  Cubical-interval lattice-meet
canonical form needed by the Progress proof for cubical
intervalMeet-of-zero / intervalMeet-of-one / commutativity /
associativity beta-rules (scrutinee inversion when the scrutinee
head is `intervalMeet`).  Binary-payload pattern with both raws at
outer scope (no scope shift); SCHEMATIC raw fields discharged via
`exact ⟨_, _, rfl⟩`.  Fourth of the M05.A.2 interval-value cohort. -/
theorem Term.headCtor_intervalMeet_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.intervalMeet) :
    ∃ leftRaw rightRaw : RawTerm scope,
      raw = RawTerm.intervalMeet leftRaw rightRaw := by
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
  | intervalMeet _ _ => exact ⟨_, _, rfl⟩
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

/-- If a term's `headCtor` is `intervalJoin`, its raw is
`RawTerm.intervalJoin` of a left interval raw and a right interval
raw (both at the outer scope).  Cubical-interval lattice-join
canonical form needed by the Progress proof for cubical
intervalJoin-of-zero / intervalJoin-of-one / commutativity /
associativity beta-rules (scrutinee inversion when the scrutinee
head is `intervalJoin`).  Binary-payload pattern with both raws at
outer scope (no scope shift); SCHEMATIC raw fields discharged via
`exact ⟨_, _, rfl⟩`.  Mirror of `intervalMeet`.  Fifth and final of
the M05.A.2 interval-value cohort, closing the cohort. -/
theorem Term.headCtor_intervalJoin_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.intervalJoin) :
    ∃ leftRaw rightRaw : RawTerm scope,
      raw = RawTerm.intervalJoin leftRaw rightRaw := by
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
  | intervalJoin _ _ => exact ⟨_, _, rfl⟩
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
