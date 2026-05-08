import LeanFX2.Algo.WHNF
import LeanFX2.Term.Inversion
import LeanFX2.Reduction.Step

/-! # Algo/Progress — Wright-Felleisen Progress lemma (M05).

This file ships the first installment of the canonical Wright-Felleisen
**Progress** half of type soundness for the typed kernel.  Preservation
(the dual half) already lives in `Term/SubjectReduction.lean` and
`Term/SubjectReductionGeneral.lean` (M06/M07).

## Layer placement

This module sits at Layer 10 (Algo) rather than Layer 1 (Term) because
its statement and proof reference both the typed kernel (Term, Step) and
the Algo WHNF classifier (`Term.isWHNF`, `Term.headCtor`).  Layer 10 is
the natural home for "value-or-step" results that combine kernel
reduction with the operational classifier.

## Headline shape

For a typed term `term : Term context ty raw`:

```
either  Term.isWHNF term = true
   or   ∃ targetRaw (target : Term context ty' targetRaw),
        Step term target
```

where `ty'` may differ syntactically from `ty` (Step has a two-Ty
signature — see `Reduction/Step.lean`).  The boolean WHNF predicate
`Term.isWHNF` (in `Algo/WHNF.lean`) is the value classifier; the
disjunction says "value-or-step" in the standard sense.

## Coverage in this revision

Phase 1 deliverable.  Builds the **β-app step constructor** that is
needed by every Progress proof for the `app` case.  Specifically:

* `Term.headCtor_lam_raw` — canonical-form raw inversion: if a typed
  Term has headCtor `.lam`, its raw form is `RawTerm.lam ...`.
* `Term.headCtor_pair_raw` (M05.3) — Σ-pair canonical form: if
  headCtor is `.pair`, raw is `RawTerm.pair firstRaw secondRaw`.
* `Term.headCtor_refl_raw` (M05.4) — identity-type canonical
  form: if headCtor is `.refl`, raw is `RawTerm.refl witnessRaw`.
* `Term.headCtor_lamPi_raw` (M05.3b) — Π-lambda canonical form:
  if headCtor is `.lamPi`, raw is `RawTerm.lam bodyRaw` (same raw
  shape as `lam`; the typed distinction lives only in the type
  index).
* `Term.headCtor_modIntro_raw` (M05.3b) — modal-intro canonical
  form: if headCtor is `.modIntro`, raw is `RawTerm.modIntro innerRaw`.
* (future commits) Headline Progress theorem assembled from
  per-ctor cases.

Note: closed-type canonical forms (`headCtor_unit_raw`,
`headCtor_boolTrue_raw`, `headCtor_boolFalse_raw`, `headCtor_natZero_raw`,
`headCtor_natSucc_raw`, `headCtor_listNil_raw`, `headCtor_listCons_raw`,
`headCtor_optionNone_raw`, `headCtor_optionSome_raw`,
`headCtor_eitherInl_raw`, `headCtor_eitherInr_raw`) already live in
`Algo/WHNF.lean` and are reused by Progress directly.

## Zero-axiom discipline

Every theorem here uses full `cases` enumeration with `nomatch` for
ctors that the type-index excludes — this avoids the propext leak
from wildcard-on-dep-indexed-match that the project repeatedly
documents (`feedback_lean_zero_axiom_match.md`,
`feedback_lean_indexed_partial_match.md`).
-/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat}

/-! ## Canonical-form raw inversions (Term.headCtor → raw shape)

If a Term's `headCtor` projection is `.lam`, then its raw is
`RawTerm.lam bodyRaw` for some `bodyRaw`.  This mirrors the
existing inversions in `Algo/WHNF.lean` for nullary canonical
heads (`boolTrue`, `boolFalse`, `natZero`, `listNil`, `optionNone`,
`unit`) plus unary canonical heads (`natSucc`, `listCons`,
`optionSome`, `eitherInl`, `eitherInr`).
-/

/-- If a term's `headCtor` is `lam`, its raw is `RawTerm.lam` of
some body raw form.  The witness body raw is existentially
extracted; full ctor enumeration with `nomatch` for the
contradictory cases keeps this zero-axiom. -/
theorem Term.headCtor_lam_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.lam) :
    ∃ bodyRaw : RawTerm (scope + 1), raw = RawTerm.lam bodyRaw := by
  cases someTerm with
  | var _ => nomatch headEq
  | unit => nomatch headEq
  | lam body =>
      rename_i innerDomainType innerCodomainType innerBodyRaw
      exact ⟨innerBodyRaw, rfl⟩
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

/-- If a term's `headCtor` is `pair`, its raw is `RawTerm.pair`
of two body raw forms.  The witness body raws are existentially
extracted; full ctor enumeration with `nomatch` for the
contradictory cases keeps this zero-axiom.  Mirrors the binary-
payload pattern used by `Term.headCtor_listCons_raw` in
`Algo/WHNF.lean`. -/
theorem Term.headCtor_pair_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.pair) :
    ∃ (firstRaw secondRaw : RawTerm scope),
      raw = RawTerm.pair firstRaw secondRaw := by
  cases someTerm with
  | var _ => nomatch headEq
  | unit => nomatch headEq
  | lam _ => nomatch headEq
  | app _ _ => nomatch headEq
  | lamPi _ => nomatch headEq
  | appPi _ _ => nomatch headEq
  | pair _ _ => exact ⟨_, _, rfl⟩
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

/-- If a term's `headCtor` is `refl`, its raw is `RawTerm.refl`
of a witness raw form.  Mirrors the unary-payload pattern used
by `Term.headCtor_natSucc_raw` / `headCtor_optionSome_raw` in
`Algo/WHNF.lean`. -/
theorem Term.headCtor_refl_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.refl) :
    ∃ witnessRaw : RawTerm scope, raw = RawTerm.refl witnessRaw := by
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
  | refl _ _ => exact ⟨_, rfl⟩
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

/-- If a term's `headCtor` is `lamPi`, its raw is `RawTerm.lam`
of a body raw form.  Note: the dependent-Π lambda `Term.lamPi`
shares the surface raw shape `RawTerm.lam` with the non-dependent
`Term.lam`; the distinction lives only in the type index
(`Ty.piTy` vs `Ty.arrow`).  The headCtor projection separates
them at the flat-enum level. -/
theorem Term.headCtor_lamPi_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.lamPi) :
    ∃ bodyRaw : RawTerm (scope + 1), raw = RawTerm.lam bodyRaw := by
  cases someTerm with
  | var _ => nomatch headEq
  | unit => nomatch headEq
  | lam _ => nomatch headEq
  | app _ _ => nomatch headEq
  | lamPi _ => exact ⟨_, rfl⟩
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

/-- If a term's `headCtor` is `recordIntro`, its raw is
`RawTerm.recordIntro` of a first-field raw form.  Mirrors the unary-
payload pattern; needed by the Progress proof for the `recordProj`
case (scrutinee inversion).  Records are encoded directly via
`Term.recordIntro` (single-field placeholder); not Sigma-encoded. -/
theorem Term.headCtor_recordIntro_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.recordIntro) :
    ∃ firstRaw : RawTerm scope,
      raw = RawTerm.recordIntro firstRaw := by
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
  | intervalJoin _ _ => nomatch headEq
  | pathLam _ _ _ _ _ => nomatch headEq
  | pathApp _ _ _ => nomatch headEq
  | glueIntro _ _ _ _ _ => nomatch headEq
  | glueElim _ _ => nomatch headEq
  | transp _ _ _ _ _ _ _ _ _ => nomatch headEq
  | hcomp _ _ _ => nomatch headEq
  | recordIntro _ => exact ⟨_, rfl⟩
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

/-- If a term's `headCtor` is `modIntro`, its raw is
`RawTerm.modIntro` of an inner raw form.  Modal-value canonical
form needed by the Progress proof for the `modElim` case. -/
theorem Term.headCtor_modIntro_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.modIntro) :
    ∃ innerRaw : RawTerm scope, raw = RawTerm.modIntro innerRaw := by
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
  | modIntro _ => exact ⟨_, rfl⟩
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

/-- If a term's `headCtor` is `pathLam`, its raw is `RawTerm.pathLam`
of a body raw form under one binder.  Cubical-path canonical form
needed by the Progress proof for the `pathApp` case (scrutinee
inversion). -/
theorem Term.headCtor_pathLam_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.pathLam) :
    ∃ bodyRaw : RawTerm (scope + 1),
      raw = RawTerm.pathLam bodyRaw := by
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
  | intervalJoin _ _ => nomatch headEq
  | pathLam _ _ _ _ _ => exact ⟨_, rfl⟩
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

/-- If a term's `headCtor` is `glueIntro`, its raw is
`RawTerm.glueIntro` of a base raw form and a partial raw form.
Cubical-Glue canonical form needed by the Progress proof for the
`glueElim` case (scrutinee inversion). -/
theorem Term.headCtor_glueIntro_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.glueIntro) :
    ∃ baseRaw partialRaw : RawTerm scope,
      raw = RawTerm.glueIntro baseRaw partialRaw := by
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
  | intervalJoin _ _ => nomatch headEq
  | pathLam _ _ _ _ _ => nomatch headEq
  | pathApp _ _ _ => nomatch headEq
  | glueIntro _ _ _ _ _ => exact ⟨_, _, rfl⟩
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

/-- If a term's `headCtor` is `refineIntro`, its raw is
`RawTerm.refineIntro` of a value raw form and a proof raw form.
Refinement-introduction canonical form needed by the Progress proof
for the `refineElim` case (scrutinee inversion). -/
theorem Term.headCtor_refineIntro_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.refineIntro) :
    ∃ valueRaw proofRaw : RawTerm scope,
      raw = RawTerm.refineIntro valueRaw proofRaw := by
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
  | intervalJoin _ _ => nomatch headEq
  | pathLam _ _ _ _ _ => nomatch headEq
  | pathApp _ _ _ => nomatch headEq
  | glueIntro _ _ _ _ _ => nomatch headEq
  | glueElim _ _ => nomatch headEq
  | transp _ _ _ _ _ _ _ _ _ => nomatch headEq
  | hcomp _ _ _ => nomatch headEq
  | recordIntro _ => nomatch headEq
  | recordProj _ => nomatch headEq
  | refineIntro _ _ _ => exact ⟨_, _, rfl⟩
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

/-- If a term's `headCtor` is `codataUnfold`, its raw is
`RawTerm.codataUnfold` of a state raw form and a transition raw form.
Codata-unfold canonical form needed by the Progress proof for the
`codataDest` case (scrutinee inversion).  The current raw kernel has
no codata observation β-rule, so this lemma is currently stocked for
future use when `codataDest (codataUnfold _ _)` becomes a redex; it
also rounds out the canonical-form cohort by parity with
`recordIntro` / `glueIntro` / `refineIntro`. -/
theorem Term.headCtor_codataUnfold_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.codataUnfold) :
    ∃ stateRaw transitionRaw : RawTerm scope,
      raw = RawTerm.codataUnfold stateRaw transitionRaw := by
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
  | codataUnfold _ _ => exact ⟨_, _, rfl⟩
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

/-- If a term's `headCtor` is `universeCode`, its raw is
`RawTerm.universeCode` of a single inner-universe level (a `Nat`).
Universe-code canonical form needed by the Progress proof for the
`cumulUp` and code-elimination cases (scrutinee inversion).  Mirrors
the single-payload pattern of `modIntro` / `optionSome` inversions but
the payload is a `Nat` (the inner universe level) rather than a
`RawTerm`.  Stocked for the future `Step.cumulUpInner` β-rule and
universe-level decoding lemmas. -/
theorem Term.headCtor_universeCode_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.universeCode) :
    ∃ universeLevelRaw : Nat,
      raw = RawTerm.universeCode universeLevelRaw := by
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
  | universeCode _ _ _ _ => exact ⟨_, rfl⟩
  | cumulUp _ _ _ _ _ _ => nomatch headEq
  | equivReflId _ => nomatch headEq
  | funextRefl _ _ _ => nomatch headEq
  | equivReflIdAtId _ _ _ _ => nomatch headEq
  | funextReflAtId _ _ _ => nomatch headEq
  | equivIntroHet _ _ _ _ => nomatch headEq
  | equivApp _ _ => nomatch headEq
  | uaIntroHet _ _ _ _ _ => nomatch headEq
  | funextIntroHet _ _ _ _ => nomatch headEq
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

/-- If a term's `headCtor` is `arrowCode`, its raw is
`RawTerm.arrowCode` of a domain code raw form and a codomain code raw
form (both at the outer scope).  Arrow-code canonical form needed by
the Progress proof for the future arrow-code-elimination β-rules
(scrutinee inversion).  Mirrors the binary-payload pattern of
`pair` / `recordIntro` / `codataUnfold` inversions but the payloads
are SCHEMATIC raw fields (per CUMUL-2.4 VALUE-shape discipline)
rather than recursive Term children. -/
theorem Term.headCtor_arrowCode_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.arrowCode) :
    ∃ domainCodeRaw codomainCodeRaw : RawTerm scope,
      raw = RawTerm.arrowCode domainCodeRaw codomainCodeRaw := by
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
  | arrowCode _ _ _ _ => exact ⟨_, _, rfl⟩
  | piTyCode _ _ _ _ => nomatch headEq
  | sigmaTyCode _ _ _ _ => nomatch headEq
  | productCode _ _ _ _ => nomatch headEq
  | sumCode _ _ _ _ => nomatch headEq
  | listCode _ _ _ => nomatch headEq
  | optionCode _ _ _ => nomatch headEq
  | eitherCode _ _ _ _ => nomatch headEq
  | idCode _ _ _ _ _ => nomatch headEq
  | equivCode _ _ _ _ => nomatch headEq

/-- If a term's `headCtor` is `piTyCode`, its raw is `RawTerm.piTyCode`
of a domain code raw form (at scope) and a codomain code raw form (at
`scope + 1`, under the Π binder).  Mirror of `arrowCode` inversion;
the codomain raw lives at scope+1 because piTyCode encodes a
DEPENDENT function type at the raw level.  Schematic-payload pattern
per CUMUL-2.4 VALUE-shape discipline. -/
theorem Term.headCtor_piTyCode_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.piTyCode) :
    ∃ (domainCodeRaw : RawTerm scope) (codomainCodeRaw : RawTerm (scope + 1)),
      raw = RawTerm.piTyCode domainCodeRaw codomainCodeRaw := by
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
  | arrowCode _ _ _ _ => nomatch headEq
  | piTyCode _ _ _ _ => exact ⟨_, _, rfl⟩
  | sigmaTyCode _ _ _ _ => nomatch headEq
  | productCode _ _ _ _ => nomatch headEq
  | sumCode _ _ _ _ => nomatch headEq
  | listCode _ _ _ => nomatch headEq
  | optionCode _ _ _ => nomatch headEq
  | eitherCode _ _ _ _ => nomatch headEq
  | idCode _ _ _ _ _ => nomatch headEq
  | equivCode _ _ _ _ => nomatch headEq

/-- If a term's `headCtor` is `sigmaTyCode`, its raw is
`RawTerm.sigmaTyCode` of a domain code raw form (at scope) and a
codomain code raw form (at `scope + 1`, under the Σ binder).  Mirror
of `piTyCode` inversion; the codomain raw lives at scope+1 because
sigmaTyCode encodes a DEPENDENT pair type at the raw level (the
second component's type may depend on the first).  Schematic-payload
pattern per CUMUL-2.4 VALUE-shape discipline. -/
theorem Term.headCtor_sigmaTyCode_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.sigmaTyCode) :
    ∃ (domainCodeRaw : RawTerm scope) (codomainCodeRaw : RawTerm (scope + 1)),
      raw = RawTerm.sigmaTyCode domainCodeRaw codomainCodeRaw := by
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
  | arrowCode _ _ _ _ => nomatch headEq
  | piTyCode _ _ _ _ => nomatch headEq
  | sigmaTyCode _ _ _ _ => exact ⟨_, _, rfl⟩
  | productCode _ _ _ _ => nomatch headEq
  | sumCode _ _ _ _ => nomatch headEq
  | listCode _ _ _ => nomatch headEq
  | optionCode _ _ _ => nomatch headEq
  | eitherCode _ _ _ _ => nomatch headEq
  | idCode _ _ _ _ _ => nomatch headEq
  | equivCode _ _ _ _ => nomatch headEq

/-- If a term's `headCtor` is `productCode`, its raw is
`RawTerm.productCode` of a first-component code raw form and a
second-component code raw form (both at the outer scope).
Product-type-code canonical form needed by the Progress proof for
the future product-type-code-elimination beta-rules (scrutinee
inversion).  Binary-payload pattern with both raws at outer scope
(non-dependent product); SCHEMATIC raw fields per CUMUL-2.4
VALUE-shape discipline.  Mirror of `arrowCode` inversion. -/
theorem Term.headCtor_productCode_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.productCode) :
    ∃ firstCodeRaw secondCodeRaw : RawTerm scope,
      raw = RawTerm.productCode firstCodeRaw secondCodeRaw := by
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
  | arrowCode _ _ _ _ => nomatch headEq
  | piTyCode _ _ _ _ => nomatch headEq
  | sigmaTyCode _ _ _ _ => nomatch headEq
  | productCode _ _ _ _ => exact ⟨_, _, rfl⟩
  | sumCode _ _ _ _ => nomatch headEq
  | listCode _ _ _ => nomatch headEq
  | optionCode _ _ _ => nomatch headEq
  | eitherCode _ _ _ _ => nomatch headEq
  | idCode _ _ _ _ _ => nomatch headEq
  | equivCode _ _ _ _ => nomatch headEq

/-- If a term's `headCtor` is `sumCode`, its raw is `RawTerm.sumCode`
of a left-component code raw form and a right-component code raw form
(both at the outer scope; binary sum type code).  Sum-type-code
canonical form needed by the Progress proof for the future
sum-type-code-elimination beta-rules (scrutinee inversion).  Mirror
of `productCode` inversion (binary outer-scope payloads); SCHEMATIC
raw fields per CUMUL-2.4 VALUE-shape discipline. -/
theorem Term.headCtor_sumCode_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.sumCode) :
    ∃ leftCodeRaw rightCodeRaw : RawTerm scope,
      raw = RawTerm.sumCode leftCodeRaw rightCodeRaw := by
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
  | arrowCode _ _ _ _ => nomatch headEq
  | piTyCode _ _ _ _ => nomatch headEq
  | sigmaTyCode _ _ _ _ => nomatch headEq
  | productCode _ _ _ _ => nomatch headEq
  | sumCode _ _ _ _ => exact ⟨_, _, rfl⟩
  | listCode _ _ _ => nomatch headEq
  | optionCode _ _ _ => nomatch headEq
  | eitherCode _ _ _ _ => nomatch headEq
  | idCode _ _ _ _ _ => nomatch headEq
  | equivCode _ _ _ _ => nomatch headEq

/-- If a term's `headCtor` is `listCode`, its raw is `RawTerm.listCode`
of a single element-type code raw form (at outer scope).  List-type-
code canonical form needed by the Progress proof for the future
list-type-code-elimination beta-rules (scrutinee inversion).  Single-
payload pattern with the raw at outer scope; SCHEMATIC raw field per
CUMUL-2.4 VALUE-shape discipline.  Mirror of single-payload
inversions like `optionSome` but the payload is a SCHEMATIC raw
(rather than a recursive Term child). -/
theorem Term.headCtor_listCode_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.listCode) :
    ∃ elementCodeRaw : RawTerm scope,
      raw = RawTerm.listCode elementCodeRaw := by
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
  | arrowCode _ _ _ _ => nomatch headEq
  | piTyCode _ _ _ _ => nomatch headEq
  | sigmaTyCode _ _ _ _ => nomatch headEq
  | productCode _ _ _ _ => nomatch headEq
  | sumCode _ _ _ _ => nomatch headEq
  | listCode _ _ _ => exact ⟨_, rfl⟩
  | optionCode _ _ _ => nomatch headEq
  | eitherCode _ _ _ _ => nomatch headEq
  | idCode _ _ _ _ _ => nomatch headEq
  | equivCode _ _ _ _ => nomatch headEq

/-- If a term's `headCtor` is `optionCode`, its raw is
`RawTerm.optionCode` of a single element-type code raw form (at outer
scope).  Option-type-code canonical form needed by the Progress proof
for the future option-type-code-elimination beta-rules (scrutinee
inversion).  Mirror of `listCode` inversion (single outer-scope
payload); SCHEMATIC raw field per CUMUL-2.4 VALUE-shape discipline. -/
theorem Term.headCtor_optionCode_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.optionCode) :
    ∃ elementCodeRaw : RawTerm scope,
      raw = RawTerm.optionCode elementCodeRaw := by
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
  | arrowCode _ _ _ _ => nomatch headEq
  | piTyCode _ _ _ _ => nomatch headEq
  | sigmaTyCode _ _ _ _ => nomatch headEq
  | productCode _ _ _ _ => nomatch headEq
  | sumCode _ _ _ _ => nomatch headEq
  | listCode _ _ _ => nomatch headEq
  | optionCode _ _ _ => exact ⟨_, rfl⟩
  | eitherCode _ _ _ _ => nomatch headEq
  | idCode _ _ _ _ _ => nomatch headEq
  | equivCode _ _ _ _ => nomatch headEq

/-- If a term's `headCtor` is `eitherCode`, its raw is
`RawTerm.eitherCode` of a left-component code raw and a
right-component code raw (both at the outer scope).  Either-type-code
canonical form needed by the Progress proof for the future
either-type-code-elimination beta-rules (scrutinee inversion).
Mirror of `sumCode` / `productCode` inversions (binary outer-scope
payloads); SCHEMATIC raw fields per CUMUL-2.4 VALUE-shape
discipline. -/
theorem Term.headCtor_eitherCode_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.eitherCode) :
    ∃ leftCodeRaw rightCodeRaw : RawTerm scope,
      raw = RawTerm.eitherCode leftCodeRaw rightCodeRaw := by
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
  | arrowCode _ _ _ _ => nomatch headEq
  | piTyCode _ _ _ _ => nomatch headEq
  | sigmaTyCode _ _ _ _ => nomatch headEq
  | productCode _ _ _ _ => nomatch headEq
  | sumCode _ _ _ _ => nomatch headEq
  | listCode _ _ _ => nomatch headEq
  | optionCode _ _ _ => nomatch headEq
  | eitherCode _ _ _ _ => exact ⟨_, _, rfl⟩
  | idCode _ _ _ _ _ => nomatch headEq
  | equivCode _ _ _ _ => nomatch headEq

/-- If a term's `headCtor` is `idCode`, its raw is `RawTerm.idCode` of
a type code raw and two endpoint raws (left and right) at outer scope
(identity type code with three payloads: typeCodeRaw, leftRaw,
rightRaw).  Identity-type-code canonical form needed by the Progress
proof for the future identity-type-code-elimination beta-rules
(scrutinee inversion).  Ternary-payload pattern with all three raws
at outer scope; SCHEMATIC raw fields per CUMUL-2.4 VALUE-shape
discipline. -/
theorem Term.headCtor_idCode_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.idCode) :
    ∃ typeCodeRaw leftRaw rightRaw : RawTerm scope,
      raw = RawTerm.idCode typeCodeRaw leftRaw rightRaw := by
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
  | arrowCode _ _ _ _ => nomatch headEq
  | piTyCode _ _ _ _ => nomatch headEq
  | sigmaTyCode _ _ _ _ => nomatch headEq
  | productCode _ _ _ _ => nomatch headEq
  | sumCode _ _ _ _ => nomatch headEq
  | listCode _ _ _ => nomatch headEq
  | optionCode _ _ _ => nomatch headEq
  | eitherCode _ _ _ _ => nomatch headEq
  | idCode _ _ _ _ _ => exact ⟨_, _, _, rfl⟩
  | equivCode _ _ _ _ => nomatch headEq

/-- If a term's `headCtor` is `equivCode`, its raw is
`RawTerm.equivCode` of a left-type code raw and a right-type code raw
(both at the outer scope).  Equivalence-type-code canonical form
needed by the Progress proof for the future
equivalence-type-code-elimination beta-rules (scrutinee inversion).
Mirror of `eitherCode` / `sumCode` / `productCode` / `arrowCode`
inversions (binary outer-scope payloads); SCHEMATIC raw fields per
CUMUL-2.4 VALUE-shape discipline.  Closes the type-code subset of
M05's canonical-form cohort. -/
theorem Term.headCtor_equivCode_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.equivCode) :
    ∃ leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope,
      raw = RawTerm.equivCode leftTypeCodeRaw rightTypeCodeRaw := by
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
  | arrowCode _ _ _ _ => nomatch headEq
  | piTyCode _ _ _ _ => nomatch headEq
  | sigmaTyCode _ _ _ _ => nomatch headEq
  | productCode _ _ _ _ => nomatch headEq
  | sumCode _ _ _ _ => nomatch headEq
  | listCode _ _ _ => nomatch headEq
  | optionCode _ _ _ => nomatch headEq
  | eitherCode _ _ _ _ => nomatch headEq
  | idCode _ _ _ _ _ => nomatch headEq
  | equivCode _ _ _ _ => exact ⟨_, _, rfl⟩

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

/-- If a term's `headCtor` is `equivReflId`, its raw is the canonical
identity-equivalence raw form `RawTerm.equivIntro (RawTerm.lam
(RawTerm.var ⟨0, _⟩)) (RawTerm.lam (RawTerm.var ⟨0, _⟩))` — i.e. a
packaged equivalence whose forward and backward functions are both
the syntactic identity lambda.  Identity-equivalence canonical form
needed by the Progress proof for the rfl-fragment of Univalence
(`Step.eqType` reduces a universe-level identity proof to this
canonical equivalence; future scrutinee inversion when the scrutinee
head is `equivReflId`).  Constant-raw payload pattern (no existential
binders); mirror of `interval0` / `interval1`.  First of the M05.A.3
Univalence-rfl-fragment cohort. -/
theorem Term.headCtor_equivReflId_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.equivReflId) :
    raw = RawTerm.equivIntro
            (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
            (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)) := by
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
  | equivReflId _ => rfl
  | funextRefl _ _ _ => nomatch headEq
  | equivReflIdAtId _ _ _ _ => nomatch headEq
  | funextReflAtId _ _ _ => nomatch headEq
  | equivIntroHet _ _ _ _ => nomatch headEq
  | equivApp _ _ => nomatch headEq
  | uaIntroHet _ _ _ _ _ => nomatch headEq
  | funextIntroHet _ _ _ _ => nomatch headEq
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

/-- If a term's `headCtor` is `funextRefl`, its raw is `RawTerm.lam
(RawTerm.refl applyRaw)` for some `applyRaw : RawTerm (scope+1)` (the
schematic apply payload under the binder, semantically "f x").
Pointwise-refl funext canonical form needed by the Progress proof
for the rfl-fragment of funext (`Step.eqArrow` reduces an arrow-
typed identity proof to this canonical pointwise-refl witness;
future scrutinee inversion when the scrutinee head is `funextRefl`).
Single-payload pattern with raw at scope+1 (one binder shift);
SCHEMATIC raw field discharged via `exact ⟨_, rfl⟩`.  Mirror of
`lam` / `pathLam`.  Second of the M05.A.3 Univalence-rfl-fragment
cohort. -/
theorem Term.headCtor_funextRefl_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.funextRefl) :
    ∃ applyRaw : RawTerm (scope + 1),
      raw = RawTerm.lam (RawTerm.refl applyRaw) := by
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
  | funextRefl _ _ _ => exact ⟨_, rfl⟩
  | equivReflIdAtId _ _ _ _ => nomatch headEq
  | funextReflAtId _ _ _ => nomatch headEq
  | equivIntroHet _ _ _ _ => nomatch headEq
  | equivApp _ _ => nomatch headEq
  | uaIntroHet _ _ _ _ _ => nomatch headEq
  | funextIntroHet _ _ _ _ => nomatch headEq
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

/-- If a term's `headCtor` is `equivReflIdAtId`, its raw is the same
canonical identity-equivalence raw form `RawTerm.equivIntro
(RawTerm.lam (RawTerm.var ⟨0, _⟩)) (RawTerm.lam (RawTerm.var ⟨0, _⟩))`
as `equivReflId` — i.e. a packaged identity equivalence whose forward
and backward functions are both the syntactic identity lambda.  This
ctor inhabits `Ty.id (Ty.universe lvl) carrierRaw carrierRaw` (the
universe-level identity type, NOT `Ty.equiv`); its raw is pre-aligned
with `equivReflId`'s raw form so that `Step.eqType` is a type-only
reduction at the raw level.  Universe-level identity-equivalence
canonical form needed by the Progress proof for the Id-fragment of
Univalence (`Step.eqType` reduces a universe-level identity proof to
this canonical witness; future scrutinee inversion when the scrutinee
head is `equivReflIdAtId`).  Constant-raw payload pattern (no
existential binders); mirror of `equivReflId` / `interval0`.  Third
of the M05.A.3 Univalence-rfl-fragment cohort. -/
theorem Term.headCtor_equivReflIdAtId_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.equivReflIdAtId) :
    raw = RawTerm.equivIntro
            (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
            (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)) := by
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
  | equivReflIdAtId _ _ _ _ => rfl
  | funextReflAtId _ _ _ => nomatch headEq
  | equivIntroHet _ _ _ _ => nomatch headEq
  | equivApp _ _ => nomatch headEq
  | uaIntroHet _ _ _ _ _ => nomatch headEq
  | funextIntroHet _ _ _ _ => nomatch headEq
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

/-- If a term's `headCtor` is `funextReflAtId`, its raw is the
canonical funext-reflexivity-at-the-Id-of-arrow lambda raw form
`RawTerm.lam (RawTerm.refl applyRaw)` for some `applyRaw :
RawTerm (scope + 1)`.  This ctor inhabits `Ty.id (Ty.arrow
domainType codomainType) (RawTerm.lam (RawTerm.refl applyRaw))
(RawTerm.lam (RawTerm.refl applyRaw))` (an Id-of-arrow path
witnessing `f = f` at the homogeneous-apply rfl-fragment); its
raw is pre-aligned with `funextRefl`'s raw form so that
`Step.eqArrow` is type-only at the raw level.  Arrow-Id
funext-rfl canonical form needed by the Progress proof for
the Id-of-arrow fragment of funext (`Step.eqArrow` reduces
an Id-of-arrow proof to this canonical witness; future
scrutinee inversion when the head is `funextReflAtId`).
Existential-payload pattern (one binder, the `applyRaw : RawTerm
(scope + 1)`); mirror of `funextRefl`.  Fourth of the M05.A.3
Univalence-rfl-fragment cohort. -/
theorem Term.headCtor_funextReflAtId_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.funextReflAtId) :
    ∃ applyRaw : RawTerm (scope + 1),
      raw = RawTerm.lam (RawTerm.refl applyRaw) := by
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
  | funextReflAtId _ _ _ => exact ⟨_, rfl⟩
  | equivIntroHet _ _ _ _ => nomatch headEq
  | equivApp _ _ => nomatch headEq
  | uaIntroHet _ _ _ _ _ => nomatch headEq
  | funextIntroHet _ _ _ _ => nomatch headEq
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

/-- If a term's `headCtor` is `equivIntroHet`, its raw is the
heterogeneous-carrier equivalence-introduction raw form
`RawTerm.equivIntro forwardRaw backwardRaw` for some
`forwardRaw, backwardRaw : RawTerm scope`.  This ctor inhabits
`Ty.equiv carrierA carrierB` for arbitrary carriers A, B at the
same universe level — packaging a forward function `A → B`,
a backward function `B → A`, and proof functions for the two
inverse laws.  The raw form drops the proof-function payloads
(they live only in the type signature) and keeps only the
computational `forwardRaw, backwardRaw` projections.
Heterogeneous-carrier equivalence canonical form needed by
the Progress proof for the heterogeneous fragment of
Univalence (`Step.eqTypeHet` will eventually reduce a
universe-level identity proof to this canonical witness;
future scrutinee inversion when the head is `equivIntroHet`).
Existential-payload pattern (two binders); mirror of
`equivReflId` generalized.  Fifth of the M05.A.3 Univalence-
rfl-fragment cohort. -/
theorem Term.headCtor_equivIntroHet_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.equivIntroHet) :
    ∃ forwardRaw backwardRaw : RawTerm scope,
      raw = RawTerm.equivIntro forwardRaw backwardRaw := by
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
  | equivIntroHet _ _ _ _ => exact ⟨_, _, rfl⟩
  | equivApp _ _ => nomatch headEq
  | uaIntroHet _ _ _ _ _ => nomatch headEq
  | funextIntroHet _ _ _ _ => nomatch headEq
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

/-- If a term's `headCtor` is `uaIntroHet`, its raw is the
heterogeneous-carrier path-from-equivalence raw form
`RawTerm.equivIntro forwardRaw backwardRaw` for some
`forwardRaw, backwardRaw : RawTerm scope`.  This ctor inhabits
`Ty.id (Ty.universe innerLevel innerLevelLt) carrierARaw
carrierBRaw` — a universe-level path proof between two arbitrary
type-codes — built from a packaged equivalence between A and B.
The raw form is THE SAME as the underlying `equivWitness`'s raw
(`RawTerm.equivIntro forwardRaw backwardRaw`), pre-aligning the
projected raw form for the eventual `Step.eqTypeHet` reduction
(heterogeneous Univalence): the source `Term.uaIntroHet ...` and
the target `Term.equivIntroHet ...` share the same raw projection,
so the `Step.par.toRawBridge` arm collapses to `RawStep.par.refl _`
(same architectural trick as `Step.eqType` / `Step.eqArrow` /
`Step.cumulUpInner`).  Heterogeneous-Univalence path-introduction
canonical form needed by Progress for full HoTT path-via-
equivalence; future scrutinee inversion when the head is
`uaIntroHet`.  Existential-payload pattern (two binders); mirror
of `equivIntroHet` at the universe-Id type rather than at
`Ty.equiv`.  Sixth of the M05.A.3 Univalence-rfl-fragment
cohort. -/
theorem Term.headCtor_uaIntroHet_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.uaIntroHet) :
    ∃ forwardRaw backwardRaw : RawTerm scope,
      raw = RawTerm.equivIntro forwardRaw backwardRaw := by
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
  | uaIntroHet _ _ _ _ _ => exact ⟨_, _, rfl⟩
  | funextIntroHet _ _ _ _ => nomatch headEq
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

/-- If a term's `headCtor` is `funextIntroHet`, its raw is the
heterogeneous-carrier funext-introduction lambda raw form
`RawTerm.lam (RawTerm.refl applyARaw)` for some
`applyARaw : RawTerm (scope + 1)`.  This ctor inhabits
`Ty.id (Ty.arrow domainType codomainType) (RawTerm.lam applyARaw)
(RawTerm.lam applyBRaw)` — a path between two DISTINCT lambda-shaped
raw functions at the arrow type — but its raw payload is the
`applyARaw`-only side of the path (pre-aligned with `funextRefl` /
`funextReflAtId`'s raw shape, with `applyBRaw` living only in the
type signature).  This sets up `Step.eqArrowHet` to fire as a
type-only reduction at the raw level, collapsing the
`Step.par.toRawBridge` arm to `RawStep.par.refl _`.
Heterogeneous-funext path-introduction canonical form needed by
Progress for full HoTT path-via-pointwise; future scrutinee
inversion when the head is `funextIntroHet`.  Existential-payload
pattern (one binder, the `applyARaw : RawTerm (scope + 1)`);
mirror of `funextReflAtId` generalized.  Seventh of the M05.A
Univalence-rfl-fragment cohort. -/
theorem Term.headCtor_funextIntroHet_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.funextIntroHet) :
    ∃ applyARaw : RawTerm (scope + 1),
      raw = RawTerm.lam (RawTerm.refl applyARaw) := by
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
  | funextIntroHet _ _ _ _ => exact ⟨_, rfl⟩
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

/-- If a term's `headCtor` is `oeqRefl`, its raw is the
observational-equality reflexivity raw form `RawTerm.oeqRefl
rawWitness` for some `rawWitness : RawTerm scope`.  This ctor
inhabits `Ty.oeq carrier rawWitness rawWitness` — the
observational-equality reflexivity proof at the typed layer
(observational equality mirrors HoTT set-level equality in
`Ty.oeq`, kept distinct from the HoTT path type `Ty.id` and from
strict identity `Ty.idStrict`).  Observational-equality canonical
form needed by Progress for the rfl-fragment of `Ty.oeq`; future
scrutinee inversion when an oeqJ scrutinee head is `oeqRefl`
(reduces oeqJ on a refl proof to the base case).  Existential-
payload pattern (one binder, `rawWitness : RawTerm scope`);
mirror of `refl` at the observational layer.  First of the
M05.A.4 observational-and-strict-equality cohort. -/
theorem Term.headCtor_oeqRefl_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.oeqRefl) :
    ∃ rawWitness : RawTerm scope,
      raw = RawTerm.oeqRefl rawWitness := by
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
  | oeqRefl _ _ => exact ⟨_, rfl⟩
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

/-- If a term's `headCtor` is `idStrictRefl`, its raw is the
strict-identity reflexivity raw form `RawTerm.idStrictRefl
rawWitness` for some `rawWitness : RawTerm scope`.  This ctor
inhabits `Ty.idStrict carrier rawWitness rawWitness` — the
strict-identity reflexivity proof at the typed layer (strict
identity mirrors identity at the typed layer but lives in
`Ty.idStrict`, keeping definitional identity separate from HoTT
`Ty.id` and from observational equality `Ty.oeq`).  Strict-
identity canonical form needed by Progress for the rfl-fragment
of `Ty.idStrict`; future scrutinee inversion when an idStrictRec
scrutinee head is `idStrictRefl` (reduces idStrictRec on a refl
proof to the base case).  Note: this ctor carries a
`modeIsStrict : mode = Mode.strict` discharge so it only appears
in the strict mode (graded `Ty.idStrict` is restricted to
strict-mode contexts).  Existential-payload pattern (one binder,
`rawWitness : RawTerm scope`); mirror of `refl` / `oeqRefl` at
the strict-identity layer.  Second of the M05.A.4 observational-
and-strict-equality cohort. -/
theorem Term.headCtor_idStrictRefl_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.idStrictRefl) :
    ∃ rawWitness : RawTerm scope,
      raw = RawTerm.idStrictRefl rawWitness := by
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
  | idStrictRefl _ _ _ => exact ⟨_, rfl⟩
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

/-! ## Step-provability for non-canonical β/ι forms (M05.B)

These atoms package the existing Step β/ι constructors as
existential-result theorems: "if a typed term has the shape
of a non-canonical β-redex, then it can take a Step."  Each
atom is mechanical Step-witness packaging — the load-bearing
work lives in `Reduction/Step.lean` (the β/ι ctor).  These
existentials feed the headline Progress theorem's β/ι cases.
-/

/-- β-app step provability: a non-dep β-redex `(λ. body) arg`
can take a Step.  Packages `Step.betaApp` as an existential.
First atom of the M05.B.1 Π/Σ β cohort. -/
theorem Term.app_lam_steps {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)} {argumentRaw : RawTerm scope}
    (bodyTerm :
      Term (context.cons domainType) codomainType.weaken bodyRaw)
    (argumentTerm : Term context domainType argumentRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.app (Term.lam (codomainType := codomainType) bodyTerm)
                     argumentTerm) target :=
  ⟨_, _, _, Step.betaApp bodyTerm argumentTerm⟩

/-- β-appPi step provability: a dependent Π β-redex
`(λ. body) arg` at the dependent Π type can take a Step.
Packages `Step.betaAppPi` as an existential.  The dependent
codomain `codomainType : Ty level (scope + 1)` distinguishes
this from the non-dep `app_lam_steps`; same witness shape via
`Step.betaAppPi`.  Second atom of the M05.B.1 Π/Σ β cohort. -/
theorem Term.appPi_lamPi_steps {context : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)} {argumentRaw : RawTerm scope}
    (bodyTerm : Term (context.cons domainType) codomainType bodyRaw)
    (argumentTerm : Term context domainType argumentRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.appPi (Term.lamPi (domainType := domainType) bodyTerm)
                       argumentTerm) target :=
  ⟨_, _, _, Step.betaAppPi bodyTerm argumentTerm⟩

/-- β-fst step provability: a Σ first-projection of a pair
`fst (pair fv sv)` can take a Step.  Packages `Step.betaFstPair`
as an existential.  First atom of the M05.B.2 Σ projection cohort. -/
theorem Term.fst_pair_steps {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    (firstValue : Term context firstType firstRaw)
    (secondValue :
      Term context (secondType.subst0 firstType firstRaw) secondRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.fst (Term.pair (secondType := secondType)
                                firstValue secondValue)) target :=
  ⟨_, _, _, Step.betaFstPair firstValue secondValue⟩

/-- β-snd step provability: a Σ second-projection of a pair
`snd (pair fv sv)` can take a Step.  Packages `Step.betaSndPair`
as an existential.  Second atom of the M05.B.2 Σ projection cohort. -/
theorem Term.snd_pair_steps {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    (firstValue : Term context firstType firstRaw)
    (secondValue :
      Term context (secondType.subst0 firstType firstRaw) secondRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.snd (Term.pair (secondType := secondType)
                                firstValue secondValue)) target :=
  ⟨_, _, _, Step.betaSndPair firstValue secondValue⟩

/-! ## Closed-type ι-rule step provability (M05.B.3 cohort) -/

/-- ι-boolElim-true step provability: `boolElim true t e` reduces.
Packages `Step.iotaBoolElimTrue`. -/
theorem Term.boolElim_boolTrue_steps {context : Ctx mode level scope}
    {motiveType : Ty level (scope + 1)}
    {thenRaw elseRaw : RawTerm scope}
    (thenBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.boolElim (motiveType := motiveType)
              Term.boolTrue thenBranch elseBranch) target :=
  ⟨_, _, _, Step.iotaBoolElimTrue thenBranch elseBranch⟩

/-- ι-boolElim-false step provability: `boolElim false t e` reduces.
Packages `Step.iotaBoolElimFalse`. -/
theorem Term.boolElim_boolFalse_steps {context : Ctx mode level scope}
    {motiveType : Ty level (scope + 1)}
    {thenRaw elseRaw : RawTerm scope}
    (thenBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.boolElim (motiveType := motiveType)
              Term.boolFalse thenBranch elseBranch) target :=
  ⟨_, _, _, Step.iotaBoolElimFalse thenBranch elseBranch⟩

/-- ι-natElim-zero step provability: `natElim zero z s` reduces.
Packages `Step.iotaNatElimZero`. -/
theorem Term.natElim_natZero_steps {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {zeroRaw succRaw : RawTerm scope}
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.natElim Term.natZero zeroBranch succBranch) target :=
  ⟨_, _, _, Step.iotaNatElimZero zeroBranch succBranch⟩

/-- ι-natElim-succ step provability: `natElim (succ n) z s` reduces.
Packages `Step.iotaNatElimSucc`. -/
theorem Term.natElim_natSucc_steps {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {predecessorRaw zeroRaw succRaw : RawTerm scope}
    (predecessor : Term context Ty.nat predecessorRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.natElim (Term.natSucc predecessor) zeroBranch succBranch)
           target :=
  ⟨_, _, _, Step.iotaNatElimSucc predecessor zeroBranch succBranch⟩

/-- ι-natRec-zero step provability: `natRec zero z s` reduces.
Packages `Step.iotaNatRecZero`. -/
theorem Term.natRec_natZero_steps {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {zeroRaw succRaw : RawTerm scope}
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.natRec Term.natZero zeroBranch succBranch) target :=
  ⟨_, _, _, Step.iotaNatRecZero zeroBranch succBranch⟩

/-- ι-natRec-succ step provability: `natRec (succ n) z s` reduces.
Packages `Step.iotaNatRecSucc`. -/
theorem Term.natRec_natSucc_steps {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {predecessorRaw zeroRaw succRaw : RawTerm scope}
    (predecessor : Term context Ty.nat predecessorRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.natRec (Term.natSucc predecessor) zeroBranch succBranch)
           target :=
  ⟨_, _, _, Step.iotaNatRecSucc predecessor zeroBranch succBranch⟩

/-- ι-listElim-nil step provability: `listElim nil n c` reduces.
Packages `Step.iotaListElimNil`. -/
theorem Term.listElim_listNil_steps {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {nilRaw consRaw : RawTerm scope}
    (nilBranch : Term context motiveType nilRaw)
    (consBranch :
      Term context (Ty.arrow elementType
                      (Ty.arrow (Ty.listType elementType) motiveType)) consRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.listElim (elementType := elementType) Term.listNil
              nilBranch consBranch) target :=
  ⟨_, _, _, Step.iotaListElimNil nilBranch consBranch⟩

/-- ι-listElim-cons step provability: `listElim (cons h t) n c` reduces.
Packages `Step.iotaListElimCons`. -/
theorem Term.listElim_listCons_steps {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {headRaw tailRaw nilRaw consRaw : RawTerm scope}
    (headTerm : Term context elementType headRaw)
    (tailTerm : Term context (Ty.listType elementType) tailRaw)
    (nilBranch : Term context motiveType nilRaw)
    (consBranch :
      Term context (Ty.arrow elementType
                      (Ty.arrow (Ty.listType elementType) motiveType)) consRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.listElim (Term.listCons headTerm tailTerm)
              nilBranch consBranch) target :=
  ⟨_, _, _, Step.iotaListElimCons headTerm tailTerm nilBranch consBranch⟩

/-- ι-optionMatch-none step provability: `optionMatch none n s` reduces.
Packages `Step.iotaOptionMatchNone`. -/
theorem Term.optionMatch_optionNone_steps {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {noneRaw someRaw : RawTerm scope}
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.optionMatch (elementType := elementType) Term.optionNone
              noneBranch someBranch) target :=
  ⟨_, _, _, Step.iotaOptionMatchNone noneBranch someBranch⟩

/-- ι-optionMatch-some step provability: `optionMatch (some v) n s` reduces.
Packages `Step.iotaOptionMatchSome`. -/
theorem Term.optionMatch_optionSome_steps {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {valueRaw noneRaw someRaw : RawTerm scope}
    (valueTerm : Term context elementType valueRaw)
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.optionMatch (Term.optionSome valueTerm)
              noneBranch someBranch) target :=
  ⟨_, _, _, Step.iotaOptionMatchSome valueTerm noneBranch someBranch⟩

/-- ι-eitherMatch-inl step provability: `eitherMatch (inl v) lb rb` reduces.
Packages `Step.iotaEitherMatchInl`. -/
theorem Term.eitherMatch_eitherInl_steps {context : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {valueRaw leftRaw rightRaw : RawTerm scope}
    (valueTerm : Term context leftType valueRaw)
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.eitherMatch (Term.eitherInl (rightType := rightType) valueTerm)
              leftBranch rightBranch) target :=
  ⟨_, _, _, Step.iotaEitherMatchInl valueTerm leftBranch rightBranch⟩

/-- ι-eitherMatch-inr step provability: `eitherMatch (inr v) lb rb` reduces.
Packages `Step.iotaEitherMatchInr`. -/
theorem Term.eitherMatch_eitherInr_steps {context : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {valueRaw leftRaw rightRaw : RawTerm scope}
    (valueTerm : Term context rightType valueRaw)
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.eitherMatch (Term.eitherInr (leftType := leftType) valueTerm)
              leftBranch rightBranch) target :=
  ⟨_, _, _, Step.iotaEitherMatchInr valueTerm leftBranch rightBranch⟩

/-! ## J-on-refl step provability (M05.B.4 cohort) -/

/-- ι-idJ-refl step provability: `idJ base (refl rt)` reduces to `base`.
Packages `Step.iotaIdJRefl`. -/
theorem Term.idJ_refl_steps {context : Ctx mode level scope}
    {carrier : Ty level scope} {endpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.idJ (carrier := carrier)
                     (leftEndpoint := endpoint)
                     (rightEndpoint := endpoint)
              baseCase
              (Term.refl carrier endpoint)) target :=
  ⟨_, _, _, Step.iotaIdJRefl carrier endpoint baseCase⟩

-- BLOCKED: M05.B.4.2 `Term.oeqJ_oeqRefl_steps` requires Step ctor
-- `Step.iotaOeqJRefl` for `oeqJ base (oeqRefl rt) ⟶ base` which does
-- not exist in the typed kernel today; only the cong rules
-- `Step.oeqJBase` and `Step.oeqJWitness` are shipped at the typed
-- layer.  Adding `Step.iotaOeqJRefl` is out of scope for M05.B
-- (spec rule).  Atom skipped pending typed observational-equality ι
-- ratchet.

/-- ι-idStrictRec-refl step provability: `idStrictRec base
(idStrictRefl rt)` reduces to `base`.  Packages
`Step.iotaIdStrictRecRefl`. -/
theorem Term.idStrictRec_idStrictRefl_steps {context : Ctx mode level scope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope} {endpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.idStrictRec (carrier := carrier)
                             (leftEndpoint := endpoint)
                             (rightEndpoint := endpoint)
              modeIsStrict
              baseCase
              (Term.idStrictRefl modeIsStrict carrier endpoint)) target :=
  ⟨_, _, _, Step.iotaIdStrictRecRefl modeIsStrict carrier endpoint baseCase⟩

/-! ## Modal β step provability (M05.B.5 cohort) -/

/-- β-modElim-modIntro step provability: `modElim (modIntro v)` reduces.
Packages `Step.betaModElimIntro`. -/
theorem Term.modElim_modIntro_steps {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.modElim (Term.modIntro innerTerm)) target :=
  ⟨_, _, _, Step.betaModElimIntro innerTerm⟩

-- BLOCKED: M05.B.5.2 `Term.subsume_modIntro_steps` requires Step ctor
-- `Step.betaSubsumeIntro` for `subsume (modIntro v) ⟶ ...` which does
-- not exist in the typed kernel today; only the cong rule
-- `Step.subsumeInner` is shipped at the typed layer.  Adding
-- `Step.betaSubsumeIntro` is out of scope for M05.B (spec rule).
-- Atom skipped pending typed subsumption-β ratchet.

/-! ## Cubical β step provability (M05.B.6 cohort) -/

/-- β-pathApp-pathLam step provability: `(pathLam body) @ i` reduces.
Packages `Step.betaPathApp`. -/
theorem Term.pathApp_pathLam_steps {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {bodyRaw : RawTerm (scope + 1)}
    {intervalRaw : RawTerm scope}
    (bodyTerm :
      Term (context.cons Ty.interval) carrierType.weaken bodyRaw)
    (intervalTerm : Term context Ty.interval intervalRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step
        (Term.pathApp modeIsUnivalent
          (Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint
            bodyTerm)
          intervalTerm) target :=
  ⟨_, _, _, Step.betaPathApp modeIsUnivalent bodyTerm intervalTerm⟩

/-- β-glueElim-glueIntro step provability: `glueElim (glueIntro ...)`
reduces.  Packages `Step.betaGlueElimIntro`. -/
theorem Term.glueElim_glueIntro_steps {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level scope}
    {boundaryWitness : RawTerm scope}
    {baseRaw partialRaw : RawTerm scope}
    (baseValue : Term context baseType baseRaw)
    (partialValue : Term context baseType partialRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step
        (Term.glueElim modeIsUnivalent
          (Term.glueIntro modeIsUnivalent baseType boundaryWitness
            baseValue partialValue)) target :=
  ⟨_, _, _, Step.betaGlueElimIntro modeIsUnivalent baseValue partialValue⟩

/-- β-transp-pathRefl step provability: `transp (pathLam typeRaw.weaken)
v` reduces (transport along constant type path is identity).
Packages `Step.transpReflBeta`. -/
theorem Term.transp_pathRefl_steps {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType : Ty level scope)
    {typeRaw sourceRaw : RawTerm scope}
    (typePath :
      Term context
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          typeRaw typeRaw)
        (RawTerm.pathLam typeRaw.weaken))
    (sourceValue : Term context sourceType sourceRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step
        (Term.transp modeIsUnivalent universeLevel universeLevelLt
          sourceType sourceType
          typeRaw typeRaw typePath sourceValue) target :=
  ⟨_, _, _,
    Step.transpReflBeta modeIsUnivalent universeLevel universeLevelLt
      sourceType typePath sourceValue⟩

/-! ## Record/Refine/Codata/Equiv/Cumul β step provability
(M05.B.7 cohort) -/

/-- β-recordProj-recordIntro step provability: `recordProj
(recordIntro f)` reduces.  Packages `Step.betaRecordProjIntro`. -/
theorem Term.recordProj_recordIntro_steps {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    (firstField : Term context singleFieldType firstRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.recordProj (Term.recordIntro firstField)) target :=
  ⟨_, _, _, Step.betaRecordProjIntro firstField⟩

/-- β-refineElim-refineIntro step provability: `refineElim
(refineIntro p v proof)` reduces.  Packages `Step.betaRefineElimIntro`. -/
theorem Term.refineElim_refineIntro_steps {context : Ctx mode level scope}
    {baseType : Ty level scope}
    (predicate : RawTerm (scope + 1))
    {valueRaw proofRaw : RawTerm scope}
    (baseValue : Term context baseType valueRaw)
    (predicateProof : Term context Ty.unit proofRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.refineElim
              (Term.refineIntro predicate baseValue predicateProof))
           target :=
  ⟨_, _, _, Step.betaRefineElimIntro predicate baseValue predicateProof⟩

/-- β-codataDest-codataUnfold step provability: `codataDest
(codataUnfold s t)` reduces to `t s`.  Packages
`Step.betaCodataDestUnfold`. -/
theorem Term.codataDest_codataUnfold_steps {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {stateRaw transitionRaw : RawTerm scope}
    (initialState : Term context stateType stateRaw)
    (transition :
      Term context (Ty.arrow stateType outputType) transitionRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.codataDest (Term.codataUnfold initialState transition))
           target :=
  ⟨_, _, _, Step.betaCodataDestUnfold initialState transition⟩

-- BLOCKED: M05.B.7.4 `Term.equivApp_equivIntroHet_steps` requires
-- Step ctor `Step.betaEquivAppIntro` for `equivApp (equivIntroHet
-- f b lInv rInv) arg ⟶ f arg` which does not exist in the typed
-- kernel today; only the cong rules `Step.equivAppEquiv` and
-- `Step.equivAppArgument` are shipped at the typed layer.  Adding
-- `Step.betaEquivAppIntro` is out of scope for M05.B (spec rule).
-- Atom skipped pending typed equivalence-β ratchet.

/-- cumulUp-inner step provability (cong-rule packaging): given
an inner Step `Step typeCodeSource typeCodeTarget` between two
type codes at the lower universe, the wrapping `cumulUp` lifts.
Packages `Step.cumulUpInner`.  Unlike the β/ι atoms above, this
atom takes the inner Step as an explicit hypothesis — `cumulUp`
has no β rule (it's the cumulativity injection, not an
elim/intro pair) so this atom captures the cong rule's existential
shape rather than a redex-firing shape.  Last atom of the M05.B
batch. -/
theorem Term.cumulUp_inner_steps {context : Ctx mode level scope}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeSourceRaw codeTargetRaw : RawTerm scope}
    {typeCodeSource :
      Term context (Ty.universe lowerLevel levelLeLow) codeSourceRaw}
    {typeCodeTarget :
      Term context (Ty.universe lowerLevel levelLeLow) codeTargetRaw}
    (innerStep : Step typeCodeSource typeCodeTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.cumulUp (context := context)
                         lowerLevel higherLevel cumulMonotone
                         levelLeLow levelLeHigh typeCodeSource) target :=
  ⟨_, _, _,
    Step.cumulUpInner lowerLevel higherLevel cumulMonotone
      levelLeLow levelLeHigh innerStep⟩

/-! ## M05.C — eliminator-eliminand cong-rule lifters (#1644)

Cong-rule completeness audit: for every typed eliminator whose
eliminand position is reducible, package the corresponding
`Step.<elim>{Scrutinee/Cong/Path/Value/...}` cong constructor as
an existential-result theorem.  Each atom takes an inner Step on
the eliminand and returns an existential Step on the outer
eliminator term.

These atoms are the "scrutinee-step lifters" that complete the
M05.B step-provability cohort: M05.B handles the
ELIMINATOR-ON-CANONICAL case (β/ι firing); M05.C handles the
ELIMINATOR-ON-REDUCING-ELIMINAND case (cong rule lifting an
inner Step to the outer eliminator).

Each lifter is a one-line cong-rule packaging — the load-bearing
work lives in `Reduction/Step.lean` (the cong ctor).  The atom
captures the cong rule's existential shape for use by callers
that need to step an eliminator whose eliminand is itself
reducing.

Note on the "audit completeness" interpretation: the headline
M05.D `Term.progress_or_step` does NOT directly invoke these
lifters because `Term.isWHNF` is shallow — an eliminator with a
non-canonical (e.g. variable, neutral, or itself-an-eliminator)
eliminand reports `isWHNF = true` regardless of whether the
eliminand could itself take a Step.  M05.C exists as
infrastructure for downstream consumers (e.g. an eventual
`headStep?` totality lemma or a "reduce-to-WHNF" function) that
need to recurse INTO the eliminand to fire its inner Step.
-/

/-- Cong-rule lifter: a Step inside the function position of a
non-dep application lifts to a Step on the outer `Term.app`.
Packages `Step.appLeft`. -/
theorem Term.app_function_steps_lift {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionRawSource functionRawTarget argumentRaw : RawTerm scope}
    {functionTermSource :
      Term context (Ty.arrow domainType codomainType) functionRawSource}
    {functionTermTarget :
      Term context (Ty.arrow domainType codomainType) functionRawTarget}
    (argumentTerm : Term context domainType argumentRaw)
    (innerStep : Step functionTermSource functionTermTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.app functionTermSource argumentTerm) target :=
  ⟨_, _, _, Step.appLeft (argumentTerm := argumentTerm) innerStep⟩

/-- Cong-rule lifter: a Step inside the function position of a
dependent Π application lifts to a Step on the outer `Term.appPi`.
Packages `Step.appPiLeft`. -/
theorem Term.appPi_function_steps_lift {context : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {functionRawSource functionRawTarget argumentRaw : RawTerm scope}
    {functionTermSource :
      Term context (Ty.piTy domainType codomainType) functionRawSource}
    {functionTermTarget :
      Term context (Ty.piTy domainType codomainType) functionRawTarget}
    (argumentTerm : Term context domainType argumentRaw)
    (innerStep : Step functionTermSource functionTermTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.appPi functionTermSource argumentTerm) target :=
  ⟨_, _, _, Step.appPiLeft (argumentTerm := argumentTerm) innerStep⟩

/-- Cong-rule lifter: a Step inside a Σ first-projection's pair
position lifts to a Step on the outer `Term.fst`.  Packages
`Step.fstCong`. -/
theorem Term.fst_pair_steps_lift {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRawSource pairRawTarget : RawTerm scope}
    {pairTermSource :
      Term context (Ty.sigmaTy firstType secondType) pairRawSource}
    {pairTermTarget :
      Term context (Ty.sigmaTy firstType secondType) pairRawTarget}
    (innerStep : Step pairTermSource pairTermTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.fst (secondType := secondType) pairTermSource) target :=
  ⟨_, _, _, Step.fstCong innerStep⟩

/-- Cong-rule lifter: a Step inside a Σ second-projection's pair
position lifts to a Step on the outer `Term.snd`.  Packages
`Step.sndCong`. -/
theorem Term.snd_pair_steps_lift {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRawSource pairRawTarget : RawTerm scope}
    {pairTermSource :
      Term context (Ty.sigmaTy firstType secondType) pairRawSource}
    {pairTermTarget :
      Term context (Ty.sigmaTy firstType secondType) pairRawTarget}
    (innerStep : Step pairTermSource pairTermTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.snd (secondType := secondType) pairTermSource) target :=
  ⟨_, _, _, Step.sndCong innerStep⟩

/-- Cong-rule lifter: a Step inside a `boolElim` scrutinee lifts
to a Step on the outer `Term.boolElim`.  Packages
`Step.boolElimScrutinee`. -/
theorem Term.boolElim_scrutinee_steps_lift {context : Ctx mode level scope}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRawSource scrutineeRawTarget thenRaw elseRaw : RawTerm scope}
    {scrutineeSource : Term context Ty.bool scrutineeRawSource}
    {scrutineeTarget : Term context Ty.bool scrutineeRawTarget}
    (thenBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw)
    (innerStep : Step scrutineeSource scrutineeTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.boolElim (motiveType := motiveType)
              scrutineeSource thenBranch elseBranch) target :=
  ⟨_, _, _,
    Step.boolElimScrutinee (thenBranch := thenBranch)
      (elseBranch := elseBranch) innerStep⟩

/-- Cong-rule lifter: a Step inside a `natElim` scrutinee lifts
to a Step on the outer `Term.natElim`.  Packages
`Step.natElimScrutinee`. -/
theorem Term.natElim_scrutinee_steps_lift {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRawSource scrutineeRawTarget zeroRaw succRaw : RawTerm scope}
    {scrutineeSource : Term context Ty.nat scrutineeRawSource}
    {scrutineeTarget : Term context Ty.nat scrutineeRawTarget}
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw)
    (innerStep : Step scrutineeSource scrutineeTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.natElim scrutineeSource zeroBranch succBranch) target :=
  ⟨_, _, _,
    Step.natElimScrutinee (zeroBranch := zeroBranch)
      (succBranch := succBranch) innerStep⟩

/-- Cong-rule lifter: a Step inside a `natRec` scrutinee lifts
to a Step on the outer `Term.natRec`.  Packages
`Step.natRecScrutinee`. -/
theorem Term.natRec_scrutinee_steps_lift {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRawSource scrutineeRawTarget zeroRaw succRaw : RawTerm scope}
    {scrutineeSource : Term context Ty.nat scrutineeRawSource}
    {scrutineeTarget : Term context Ty.nat scrutineeRawTarget}
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw)
    (innerStep : Step scrutineeSource scrutineeTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.natRec scrutineeSource zeroBranch succBranch) target :=
  ⟨_, _, _,
    Step.natRecScrutinee (zeroBranch := zeroBranch)
      (succBranch := succBranch) innerStep⟩

/-- Cong-rule lifter: a Step inside a `listElim` scrutinee lifts
to a Step on the outer `Term.listElim`.  Packages
`Step.listElimScrutinee`. -/
theorem Term.listElim_scrutinee_steps_lift {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRawSource scrutineeRawTarget nilRaw consRaw : RawTerm scope}
    {scrutineeSource :
      Term context (Ty.listType elementType) scrutineeRawSource}
    {scrutineeTarget :
      Term context (Ty.listType elementType) scrutineeRawTarget}
    (nilBranch : Term context motiveType nilRaw)
    (consBranch :
      Term context (Ty.arrow elementType
                      (Ty.arrow (Ty.listType elementType) motiveType)) consRaw)
    (innerStep : Step scrutineeSource scrutineeTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.listElim scrutineeSource nilBranch consBranch) target :=
  ⟨_, _, _,
    Step.listElimScrutinee (nilBranch := nilBranch)
      (consBranch := consBranch) innerStep⟩

/-- Cong-rule lifter: a Step inside an `optionMatch` scrutinee
lifts to a Step on the outer `Term.optionMatch`.  Packages
`Step.optionMatchScrutinee`. -/
theorem Term.optionMatch_scrutinee_steps_lift
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRawSource scrutineeRawTarget noneRaw someRaw : RawTerm scope}
    {scrutineeSource :
      Term context (Ty.optionType elementType) scrutineeRawSource}
    {scrutineeTarget :
      Term context (Ty.optionType elementType) scrutineeRawTarget}
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw)
    (innerStep : Step scrutineeSource scrutineeTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.optionMatch scrutineeSource noneBranch someBranch) target :=
  ⟨_, _, _,
    Step.optionMatchScrutinee (noneBranch := noneBranch)
      (someBranch := someBranch) innerStep⟩

/-- Cong-rule lifter: a Step inside an `eitherMatch` scrutinee
lifts to a Step on the outer `Term.eitherMatch`.  Packages
`Step.eitherMatchScrutinee`. -/
theorem Term.eitherMatch_scrutinee_steps_lift
    {context : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRawSource scrutineeRawTarget leftRaw rightRaw : RawTerm scope}
    {scrutineeSource :
      Term context (Ty.eitherType leftType rightType) scrutineeRawSource}
    {scrutineeTarget :
      Term context (Ty.eitherType leftType rightType) scrutineeRawTarget}
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw)
    (innerStep : Step scrutineeSource scrutineeTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.eitherMatch scrutineeSource leftBranch rightBranch) target :=
  ⟨_, _, _,
    Step.eitherMatchScrutinee (leftBranch := leftBranch)
      (rightBranch := rightBranch) innerStep⟩

/-- Cong-rule lifter: a Step inside an `idJ` witness lifts to a
Step on the outer `Term.idJ`.  Packages `Step.idJWitness`. -/
theorem Term.idJ_witness_steps_lift {context : Ctx mode level scope}
    {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRawSource witnessRawTarget : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    {witnessSource :
      Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRawSource}
    {witnessTarget :
      Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRawTarget}
    (innerStep : Step witnessSource witnessTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.idJ baseCase witnessSource) target :=
  ⟨_, _, _, Step.idJWitness baseCase innerStep⟩

/-- Cong-rule lifter: a Step inside a `modElim` payload lifts to
a Step on the outer `Term.modElim`.  Packages
`Step.modElimInner`. -/
theorem Term.modElim_inner_steps_lift {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRawSource innerRawTarget : RawTerm scope}
    {innerSource : Term context innerType innerRawSource}
    {innerTarget : Term context innerType innerRawTarget}
    (innerStep : Step innerSource innerTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.modElim innerSource) target :=
  ⟨_, _, _, Step.modElimInner innerStep⟩

/-- Cong-rule lifter: a Step inside a `pathApp` path-position
lifts to a Step on the outer `Term.pathApp`.  Packages
`Step.pathAppPath`. -/
theorem Term.pathApp_path_steps_lift {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {pathRawSource pathRawTarget intervalRaw : RawTerm scope}
    {pathSource :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint)
        pathRawSource}
    {pathTarget :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint)
        pathRawTarget}
    (intervalTerm : Term context Ty.interval intervalRaw)
    (innerStep : Step pathSource pathTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.pathApp modeIsUnivalent pathSource intervalTerm) target :=
  ⟨_, _, _,
    Step.pathAppPath modeIsUnivalent (intervalTerm := intervalTerm) innerStep⟩

/-- Cong-rule lifter: a Step inside a `glueElim` glued value lifts
to a Step on the outer `Term.glueElim`.  Packages
`Step.glueElimValue`. -/
theorem Term.glueElim_value_steps_lift {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level scope}
    {boundaryWitness : RawTerm scope}
    {gluedRawSource gluedRawTarget : RawTerm scope}
    {gluedSource :
      Term context (Ty.glue baseType boundaryWitness) gluedRawSource}
    {gluedTarget :
      Term context (Ty.glue baseType boundaryWitness) gluedRawTarget}
    (innerStep : Step gluedSource gluedTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.glueElim modeIsUnivalent gluedSource) target :=
  ⟨_, _, _, Step.glueElimValue modeIsUnivalent innerStep⟩

/-- Cong-rule lifter: a Step inside a `recordProj` record value
lifts to a Step on the outer `Term.recordProj`.  Packages
`Step.recordProjRecord`. -/
theorem Term.recordProj_record_steps_lift
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {recordRawSource recordRawTarget : RawTerm scope}
    {recordSource :
      Term context (Ty.record singleFieldType) recordRawSource}
    {recordTarget :
      Term context (Ty.record singleFieldType) recordRawTarget}
    (innerStep : Step recordSource recordTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.recordProj recordSource) target :=
  ⟨_, _, _, Step.recordProjRecord innerStep⟩

/-- Cong-rule lifter: a Step inside a `refineElim` refined value
lifts to a Step on the outer `Term.refineElim`.  Packages
`Step.refineElimValue`. -/
theorem Term.refineElim_value_steps_lift {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {refinedRawSource refinedRawTarget : RawTerm scope}
    {refinedSource :
      Term context (Ty.refine baseType predicate) refinedRawSource}
    {refinedTarget :
      Term context (Ty.refine baseType predicate) refinedRawTarget}
    (innerStep : Step refinedSource refinedTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.refineElim refinedSource) target :=
  ⟨_, _, _, Step.refineElimValue innerStep⟩

/-- Cong-rule lifter: a Step inside a `codataDest` codata value
lifts to a Step on the outer `Term.codataDest`.  Packages
`Step.codataDestValue`. -/
theorem Term.codataDest_value_steps_lift {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {codataRawSource codataRawTarget : RawTerm scope}
    {codataSource :
      Term context (Ty.codata stateType outputType) codataRawSource}
    {codataTarget :
      Term context (Ty.codata stateType outputType) codataRawTarget}
    (innerStep : Step codataSource codataTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.codataDest codataSource) target :=
  ⟨_, _, _, Step.codataDestValue innerStep⟩

/-! ## M05.D — headline progress theorem (#1645) — partial coverage

Wright-Felleisen progress: every typed term is either in weak
head normal form (`Term.isWHNF = true`) or takes a Step to some
target.

This file ships the **partial** headline progress theorem for
the M05.D milestone.  Full coverage of all 75 Term ctors is
factored into focused per-construct theorems that compose
into a future final headline.

## Coverage in this revision

Three deliverables:

1. **`Term.value_cases_progress`** — the always-WHNF half: any
   term whose head ctor is a value-introduction (`var`, `unit`,
   `lam`, `lamPi`, `pair`, `refl`, ..., or any of the 57
   always-WHNF heads) is in WHNF directly.  Mechanical
   enumeration; zero-axiom under strict policy via `cases` +
   `rfl`.

2. **`Term.cong_only_eliminator_progress`** — the three
   eliminators that are kernel-WHNF in the current layer:
   `oeqJ`, `idStrictRec`, `codataDest`.  Each is classified
   as WHNF because no β/ι rule fires from them in the typed
   layer today (raw layer rules are gated behind missing
   bridge work).  These are documented gaps M05.B #1632 + the
   subsume / equivApp fall-through.

3. **`Term.app_progress_or_step`** — full progress for the
   `Term.app` head, with the canonical β-firing case proven
   via `Term.headCtor_lam_raw` + `Term.lamDestruct` +
   `Step.betaApp`.  This is the LOAD-BEARING demonstration
   that the Progress proof template works end-to-end at zero
   axioms; it serves as the reference pattern for the
   remaining 16 conditional eliminators (which are deferred
   per the gap analysis below).

## Documented gap — full headline `Term.progress_or_step`

The full headline `Term.progress_or_step (someTerm : Term ...) :
Term.isWHNF someTerm = true ∨ ∃ result, Step someTerm result`
covering ALL 75 Term ctors requires per-conditional-eliminator
canonical-case extraction theorems.  The pattern is shown in
`Term.app_progress_or_step`:

```
| .lam =>
  obtain ⟨bodyRaw, rawEq⟩ := Term.headCtor_lam_raw functionTerm h
  cases rawEq
  obtain ⟨body, bodyHeq⟩ := Term.lamDestruct functionTerm
  ...
  exact Or.inr ⟨_, _, _, Step.betaApp body argumentTerm⟩
```

For the remaining 16 conditional eliminators (`appPi`, `fst`,
`snd`, `boolElim`, `natElim`, `natRec`, `listElim`,
`optionMatch`, `eitherMatch`, `idJ`, `modElim`, `pathApp`,
`glueElim`, `recordProj`, `refineElim`, `subsume`), the same
pattern applies but requires:

  * Per-eliminator canonical-form destructors for the typed
    payload extraction (some exist in
    `Term/PreservesTerm.lean` — `lamDestruct`, `pairDestruct`,
    `modIntroDestruct`, etc. — others need to be written:
    `lamPiDestruct` for `appPi`).
  * Mechanical 75-case `cases h : eliminand.headCtor with`
    enumeration per eliminator (1275 cases total across 17
    eliminators).

Estimated work: ~3000 lines of mechanical case enumeration +
~5 missing destructors.  Deferred to a follow-up M05.D.2
session — out of scope for the current M05.D.1 milestone
which establishes the proof template and the always-WHNF +
`app` coverage.

## Zero-axiom discipline

Every theorem here uses full `cases` enumeration + `rfl`-style
discharge.  Per-decl `#assert_no_axioms` gates installed in
M05.E.
-/

/-- Always-WHNF half of progress: every value-introduction Term
ctor is in WHNF.  This covers the 57 always-WHNF heads
(canonical leaf values, value introductions, type codes, HoTT
canonical refl-fragment witnesses) plus the 3 cong-only
eliminators (`oeqJ`, `idStrictRec`, `codataDest`).

The theorem statement uses an `Or` disjunction matching the
shape of the future full `Term.progress_or_step` headline; the
`Or.inr` case is impossible for these heads (no β/ι rule fires
from a value form), so the proof always picks `Or.inl rfl`.

For conditional eliminator heads (`app`, `appPi`, `fst`, `snd`,
`boolElim`, `natElim`, `natRec`, `listElim`, `optionMatch`,
`eitherMatch`, `idJ`, `modElim`, `pathApp`, `glueElim`,
`recordProj`, `refineElim`, `subsume`), see the per-construct
helpers (`Term.app_progress_or_step` is shipped here; others
are deferred — see the docstring of the M05.D section above). -/
theorem Term.value_or_cong_only_progress
    {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (notConditionalElim :
      someTerm.headCtor ≠ Term.HeadCtor.app ∧
      someTerm.headCtor ≠ Term.HeadCtor.appPi ∧
      someTerm.headCtor ≠ Term.HeadCtor.fst ∧
      someTerm.headCtor ≠ Term.HeadCtor.snd ∧
      someTerm.headCtor ≠ Term.HeadCtor.boolElim ∧
      someTerm.headCtor ≠ Term.HeadCtor.natElim ∧
      someTerm.headCtor ≠ Term.HeadCtor.natRec ∧
      someTerm.headCtor ≠ Term.HeadCtor.listElim ∧
      someTerm.headCtor ≠ Term.HeadCtor.optionMatch ∧
      someTerm.headCtor ≠ Term.HeadCtor.eitherMatch ∧
      someTerm.headCtor ≠ Term.HeadCtor.idJ ∧
      someTerm.headCtor ≠ Term.HeadCtor.modElim ∧
      someTerm.headCtor ≠ Term.HeadCtor.pathApp ∧
      someTerm.headCtor ≠ Term.HeadCtor.glueElim ∧
      someTerm.headCtor ≠ Term.HeadCtor.recordProj ∧
      someTerm.headCtor ≠ Term.HeadCtor.refineElim) :
    Term.isWHNF someTerm = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step someTerm target := by
  cases someTerm with
  | var _ => exact Or.inl rfl
  | unit => exact Or.inl rfl
  | boolTrue => exact Or.inl rfl
  | boolFalse => exact Or.inl rfl
  | natZero => exact Or.inl rfl
  | listNil => exact Or.inl rfl
  | optionNone => exact Or.inl rfl
  | interval0 => exact Or.inl rfl
  | interval1 => exact Or.inl rfl
  | lam _ => exact Or.inl rfl
  | lamPi _ => exact Or.inl rfl
  | pair _ _ => exact Or.inl rfl
  | refl _ _ => exact Or.inl rfl
  | oeqRefl _ _ => exact Or.inl rfl
  | oeqFunext _ _ _ _ _ => exact Or.inl rfl
  | idStrictRefl _ _ _ => exact Or.inl rfl
  | natSucc _ => exact Or.inl rfl
  | listCons _ _ => exact Or.inl rfl
  | optionSome _ => exact Or.inl rfl
  | eitherInl _ => exact Or.inl rfl
  | eitherInr _ => exact Or.inl rfl
  | modIntro _ => exact Or.inl rfl
  | subsume _ => exact Or.inl rfl
  | intervalOpp _ => exact Or.inl rfl
  | intervalMeet _ _ => exact Or.inl rfl
  | intervalJoin _ _ => exact Or.inl rfl
  | pathLam _ _ _ _ _ => exact Or.inl rfl
  | glueIntro _ _ _ _ _ => exact Or.inl rfl
  | transp _ _ _ _ _ _ _ _ _ => exact Or.inl rfl
  | hcomp _ _ _ => exact Or.inl rfl
  | recordIntro _ => exact Or.inl rfl
  | refineIntro _ _ _ => exact Or.inl rfl
  | codataUnfold _ _ => exact Or.inl rfl
  | sessionSend _ _ _ => exact Or.inl rfl
  | sessionRecv _ => exact Or.inl rfl
  | effectPerform _ _ _ _ _ _ => exact Or.inl rfl
  | universeCode _ _ _ _ => exact Or.inl rfl
  | cumulUp _ _ _ _ _ _ => exact Or.inl rfl
  | equivReflId _ => exact Or.inl rfl
  | funextRefl _ _ _ => exact Or.inl rfl
  | equivReflIdAtId _ _ _ _ => exact Or.inl rfl
  | funextReflAtId _ _ _ => exact Or.inl rfl
  | equivIntroHet _ _ _ _ => exact Or.inl rfl
  | uaIntroHet _ _ _ _ _ => exact Or.inl rfl
  | funextIntroHet _ _ _ _ => exact Or.inl rfl
  | equivApp _ _ => exact Or.inl rfl
  | arrowCode _ _ _ _ => exact Or.inl rfl
  | piTyCode _ _ _ _ => exact Or.inl rfl
  | sigmaTyCode _ _ _ _ => exact Or.inl rfl
  | productCode _ _ _ _ => exact Or.inl rfl
  | sumCode _ _ _ _ => exact Or.inl rfl
  | listCode _ _ _ => exact Or.inl rfl
  | optionCode _ _ _ => exact Or.inl rfl
  | eitherCode _ _ _ _ => exact Or.inl rfl
  | idCode _ _ _ _ _ => exact Or.inl rfl
  | equivCode _ _ _ _ => exact Or.inl rfl
  | oeqJ _ _ => exact Or.inl rfl
  | idStrictRec _ _ _ => exact Or.inl rfl
  | codataDest _ => exact Or.inl rfl
  -- Conditional eliminators are excluded by `notConditionalElim`.
  | app _ _ => exact absurd rfl notConditionalElim.1
  | appPi _ _ => exact absurd rfl notConditionalElim.2.1
  | fst _ => exact absurd rfl notConditionalElim.2.2.1
  | snd _ => exact absurd rfl notConditionalElim.2.2.2.1
  | boolElim _ _ _ => exact absurd rfl notConditionalElim.2.2.2.2.1
  | natElim _ _ _ => exact absurd rfl notConditionalElim.2.2.2.2.2.1
  | natRec _ _ _ => exact absurd rfl notConditionalElim.2.2.2.2.2.2.1
  | listElim _ _ _ => exact absurd rfl notConditionalElim.2.2.2.2.2.2.2.1
  | optionMatch _ _ _ => exact absurd rfl notConditionalElim.2.2.2.2.2.2.2.2.1
  | eitherMatch _ _ _ => exact absurd rfl notConditionalElim.2.2.2.2.2.2.2.2.2.1
  | idJ _ _ => exact absurd rfl notConditionalElim.2.2.2.2.2.2.2.2.2.2.1
  | modElim _ => exact absurd rfl notConditionalElim.2.2.2.2.2.2.2.2.2.2.2.1
  | pathApp _ _ _ => exact absurd rfl notConditionalElim.2.2.2.2.2.2.2.2.2.2.2.2.1
  | glueElim _ _ => exact absurd rfl notConditionalElim.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | recordProj _ => exact absurd rfl notConditionalElim.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | refineElim _ => exact absurd rfl notConditionalElim.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-! ## Local destructor for non-dep λ

`Term.lamDestructAlgo` is the Algo-layer copy of
`Term.lamDestruct` (which lives in `Term/PreservesTerm.lean`).
Inlined here to avoid importing PreservesTerm — that module
imports `Reduction.ParRed` (a later layer), so pulling it into
Algo would violate the production import-surface gate.

The two definitions are byte-equivalent except for the name.
Both are zero-axiom under strict policy via the suffices/free-
index pattern from `feedback_lean_free_type_via_suffices.md`. -/

/-- Algo-layer destructor for `Term.lam` (non-dep arrow).
Disambiguated from `Term.lamPi`, `Term.funextRefl`,
`Term.funextReflAtId`, and `Term.funextIntroHet` (all with raw
`RawTerm.lam ...`) by the fixed `Ty.arrow` source-type index —
the latter four have `Ty.id` or `Ty.piTy` shaped types.

Used by `Term.app_progress_or_step` to extract the typed body
of the `Term.lam` form when the function position of an `app`
node is itself a lambda.  Zero-axiom via the suffices/free-
index pattern (mirrors `Term.lamDestruct` in
`Term/PreservesTerm.lean`). -/
def Term.lamDestructAlgo {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    (someTerm :
      Term context (Ty.arrow domainType codomainType) (RawTerm.lam bodyRaw)) :
    Σ' (body : Term (context.cons domainType) codomainType.weaken bodyRaw),
       HEq someTerm (Term.lam (codomainType := codomainType) body) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.lam bodyRaw)),
        someType = Ty.arrow domainType codomainType →
        Σ' (body : Term (context.cons domainType) codomainType.weaken bodyRaw),
           HEq genericTerm (Term.lam (codomainType := codomainType) body) by
    exact key someTerm rfl
  intro someType genericTerm someTypeIsArrow
  cases genericTerm
  case lam innerDomain innerCodomain body =>
    have arrowEq := Ty.arrow.inj someTypeIsArrow
    cases arrowEq.1
    cases arrowEq.2
    exact ⟨body, HEq.rfl⟩
  case lamPi innerDomain innerCodomain body =>
    nomatch someTypeIsArrow
  case funextRefl _ _ _ => nomatch someTypeIsArrow
  case funextReflAtId _ _ _ => nomatch someTypeIsArrow
  case funextIntroHet _ _ _ _ => nomatch someTypeIsArrow

/-- Focused progress theorem for the `Term.app` head.  Every
non-dep `app`-headed term is either in WHNF (when the function
position is not a `lam`) or takes a β-step (when the function
position IS a `lam`).

Reference pattern for the remaining 16 conditional eliminators
of the full `Term.progress_or_step` headline.  Uses
`Term.headCtor_lam_raw` (M05.A.1) for the canonical-form raw
inversion and `Term.lamDestruct` (Term/PreservesTerm.lean) for
the typed body extraction; the canonical case fires
`Step.betaApp` from M05.B.1.1.

Zero-axiom under strict policy: full 75-case enumeration on
`functionTerm.headCtor` with each non-`.lam` case discharged
by `simp only [Term.isWHNF, h]; rfl` (definitional reduction
of the WHNF predicate). -/
theorem Term.app_progress_or_step
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionRaw argumentRaw : RawTerm scope}
    (functionTerm :
      Term context (Ty.arrow domainType codomainType) functionRaw)
    (argumentTerm : Term context domainType argumentRaw) :
    Term.isWHNF (Term.app functionTerm argumentTerm) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.app functionTerm argumentTerm) target := by
  cases h : functionTerm.headCtor with
  | lam =>
      obtain ⟨bodyRaw, rawEq⟩ := Term.headCtor_lam_raw functionTerm h
      cases rawEq
      obtain ⟨body, bodyHeq⟩ := Term.lamDestructAlgo functionTerm
      have bodyEq := eq_of_heq bodyHeq
      rw [bodyEq]
      exact Or.inr ⟨_, _, _, Step.betaApp body argumentTerm⟩
  | var =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | unit =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | app =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lamPi =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | appPi =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | pair =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | fst =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | snd =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | boolTrue =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | boolFalse =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | boolElim =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natZero =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natSucc =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natElim =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natRec =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listNil =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listCons =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listElim =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionNone =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionSome =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionMatch =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherInl =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherInr =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherMatch =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | refl =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idJ =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | oeqRefl =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | oeqJ =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | oeqFunext =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idStrictRefl =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idStrictRec =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | modIntro =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | modElim =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | subsume =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | interval0 =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | interval1 =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | intervalOpp =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | intervalMeet =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | intervalJoin =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | pathLam =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | pathApp =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | glueIntro =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | glueElim =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | transp =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | hcomp =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | recordIntro =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | recordProj =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | refineIntro =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | refineElim =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | codataUnfold =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | codataDest =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sessionSend =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sessionRecv =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | effectPerform =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | universeCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | cumulUp =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivReflId =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | funextRefl =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivReflIdAtId =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | funextReflAtId =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivIntroHet =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApp =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | uaIntroHet =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | funextIntroHet =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | arrowCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | piTyCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sigmaTyCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | productCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sumCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivCode =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl

end LeanFX2
