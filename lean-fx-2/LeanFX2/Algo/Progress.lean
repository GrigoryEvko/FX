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
* (future commits) Canonical-form lemmas for the remaining value
  introduction heads (`refl`, `lamPi`, `modIntro`) and the headline
  Progress theorem assembled from per-ctor cases.

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

end LeanFX2
