import LeanFX2.Algo.WHNF
import LeanFX2.Term.Inversion
import LeanFX2.Reduction.Step
import LeanFX2.Algo.Progress.CanonicalIntroductions
import LeanFX2.Algo.Progress.CanonicalTypeCodes
import LeanFX2.Algo.Progress.CanonicalInterval
import LeanFX2.Algo.Progress.CanonicalHoTTRefl
import LeanFX2.Algo.Progress.BetaIotaStepProvability
import LeanFX2.Algo.Progress.CongRuleLifters

/-! # LeanFX2.Algo.Progress.Headline

The headline Wright-Felleisen Progress theorem (M05.D, #1645) —
partial coverage. Ships `Term.value_or_cong_only_progress` (the
always-WHNF half covering 57 value-introduction heads + 3 cong-only
eliminators), the local `Term.lamDestructAlgo` destructor, and
`Term.app_progress_or_step` (focused progress for the `Term.app`
head — the LOAD-BEARING demonstration that the Progress proof
template works end-to-end at zero axioms).

## Root status

Headline Progress theorem assembly; consumes canonical-form
inversions, β/ι step-provability atoms, and cong-rule lifters
from the sibling sub-modules. Zero-axiom under strict policy. -/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat}

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
  | hcompPath _ _ _ _ _ => exact Or.inl rfl
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
  | uaToEquiv _ _ _ _ _ _ _ => exact Or.inl rfl
  | equivApp _ _ => exact Or.inl rfl
  | equivApply _ _ => exact Or.inl rfl
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
  | uaToEquiv =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApply =>
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

/-- Focused progress theorem for the `Term.fst` head.  Every
Σ first-projection term is either in WHNF (when the pair position
is not a `pair`) or takes a β-step (when the pair position IS a
`pair`).

Second instance of the M05.D.2 conditional-eliminator progress
template, applying the same recipe as `Term.app_progress_or_step`
to Σ-fst: `Term.headCtor_pair_raw` (canonical-form raw inversion
from `CanonicalIntroductions.lean`) + `Term.pairDestruct` (typed
component extraction from `Term/Inversion.lean`) + `Step.betaFstPair`
(β-firing from M05.B.2).

Zero-axiom under strict policy: 75-case enumeration on
`pairTerm.headCtor` with non-`.pair` cases discharged by
`simp only [Term.isWHNF, h]; rfl`. -/
theorem Term.fst_progress_or_step
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (pairTerm :
      Term context (Ty.sigmaTy firstType secondType) pairRaw) :
    Term.isWHNF (Term.fst pairTerm) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.fst pairTerm) target := by
  cases h : pairTerm.headCtor with
  | pair =>
      obtain ⟨firstRaw, secondRaw, rawEq⟩ := Term.headCtor_pair_raw pairTerm h
      cases rawEq
      obtain ⟨firstValue, secondValue, pairHeq⟩ := Term.pairDestruct pairTerm
      have pairEq := eq_of_heq pairHeq
      rw [pairEq]
      exact Or.inr ⟨_, _, _, Step.betaFstPair firstValue secondValue⟩
  | var =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | unit =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lam =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | app =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lamPi =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | appPi =>
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
  | uaToEquiv =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApply =>
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

/-- Focused progress theorem for the `Term.snd` head.  Symmetric
sibling of `Term.fst_progress_or_step`: every Σ second-projection
term is either in WHNF (when the pair position is not a `pair`)
or takes a β-step via `Step.betaSndPair`.

Third instance of the M05.D.2 conditional-eliminator progress
template.  Same destructors as `fst_progress_or_step`
(`Term.headCtor_pair_raw` + `Term.pairDestruct`); β-firing uses
`Step.betaSndPair`. -/
theorem Term.snd_progress_or_step
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (pairTerm :
      Term context (Ty.sigmaTy firstType secondType) pairRaw) :
    Term.isWHNF (Term.snd pairTerm) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.snd pairTerm) target := by
  cases h : pairTerm.headCtor with
  | pair =>
      obtain ⟨firstRaw, secondRaw, rawEq⟩ := Term.headCtor_pair_raw pairTerm h
      cases rawEq
      obtain ⟨firstValue, secondValue, pairHeq⟩ := Term.pairDestruct pairTerm
      have pairEq := eq_of_heq pairHeq
      rw [pairEq]
      exact Or.inr ⟨_, _, _, Step.betaSndPair firstValue secondValue⟩
  | var =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | unit =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lam =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | app =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lamPi =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | appPi =>
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
  | uaToEquiv =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApply =>
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

/-- Algo-layer destructor for `Term.lamPi` (dependent Π intro).
Disambiguated from sibling `RawTerm.lam`-shaped ctors
(`Term.lam`, `Term.funextRefl`, `Term.funextReflAtId`,
`Term.funextIntroHet`) by the runtime head-ctor witness, since
`funextReflType` reduces to `Ty.piTy` and the source-type alone
cannot rule out the funext arms.  Pattern follows
`Term.lamDestructAlgo` plus an explicit `headEq` hypothesis.

Used by `Term.appPi_progress_or_step` to extract the typed body
of the `Term.lamPi` form when the function position of an
`appPi` node has `headCtor = .lamPi`. -/
def Term.lamPiDestructAlgo {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    (someTerm :
      Term context (Ty.piTy domainType codomainType) (RawTerm.lam bodyRaw))
    (headEq : someTerm.headCtor = Term.HeadCtor.lamPi) :
    Σ' (body : Term (context.cons domainType) codomainType bodyRaw),
       HEq someTerm (Term.lamPi (codomainType := codomainType) body) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.lam bodyRaw))
        (sTyEq : someType = Ty.piTy domainType codomainType)
        (hcEq : genericTerm.headCtor = Term.HeadCtor.lamPi),
        Σ' (body : Term (context.cons domainType) codomainType bodyRaw),
           HEq genericTerm (Term.lamPi (codomainType := codomainType) body) by
    exact key someTerm rfl headEq
  intro someType genericTerm sTyEq hcEq
  cases genericTerm
  case lam _ _ _ => nomatch hcEq
  case lamPi innerDomain innerCodomain body =>
    have piEq := Ty.piTy.inj sTyEq
    cases piEq.1
    cases piEq.2
    exact ⟨body, HEq.rfl⟩
  case funextRefl _ _ _ => nomatch hcEq
  case funextReflAtId _ _ _ => nomatch hcEq
  case funextIntroHet _ _ _ _ => nomatch hcEq

/-- Focused progress theorem for the `Term.appPi` head (dependent
Π application).  Every well-typed `appPi`-headed term is either
in WHNF (when the function position is not a `lamPi`) or takes a
β-step (when the function position IS a `lamPi`).

M05.D.2 conditional eliminator #4 of 17.  Same template as
`Term.app_progress_or_step` but with `Ty.piTy` source type,
`Term.lamPiDestructAlgo` (taking explicit headCtor witness) for
the typed body extraction, and `Step.betaAppPi` as the firing
contraction. -/
theorem Term.appPi_progress_or_step
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {functionRaw argumentRaw : RawTerm scope}
    (functionTerm :
      Term context (Ty.piTy domainType codomainType) functionRaw)
    (argumentTerm : Term context domainType argumentRaw) :
    Term.isWHNF (Term.appPi functionTerm argumentTerm) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.appPi functionTerm argumentTerm) target := by
  cases h : functionTerm.headCtor with
  | lamPi =>
      obtain ⟨bodyRaw, rawEq⟩ := Term.headCtor_lamPi_raw functionTerm h
      cases rawEq
      obtain ⟨body, bodyHeq⟩ := Term.lamPiDestructAlgo functionTerm h
      have bodyEq := eq_of_heq bodyHeq
      rw [bodyEq]
      exact Or.inr ⟨_, _, _, Step.betaAppPi body argumentTerm⟩
  | var =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | unit =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lam =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | app =>
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
  | uaToEquiv =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApply =>
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

/-- Algo-layer destructor for `Term.modIntro` (modal intro).
Given a term whose `headCtor` is `.modIntro` and whose raw form
is `RawTerm.modIntro innerRaw`, extracts the inner typed term
plus an HEq witness.  Used by `Term.modElim_progress_or_step`
to rewrite the inner position of a `modElim` to a literal
`Term.modIntro` form so `Step.betaModElimIntro` can fire. -/
def Term.modIntroDestructAlgo {context : Ctx mode level scope}
    {innerType : Ty level scope} {innerRaw : RawTerm scope}
    (someTerm : Term context innerType (RawTerm.modIntro innerRaw))
    (headEq : someTerm.headCtor = Term.HeadCtor.modIntro) :
    Σ' (innerTerm : Term context innerType innerRaw),
       HEq someTerm (Term.modIntro innerTerm) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.modIntro innerRaw))
        (sTyEq : someType = innerType)
        (hcEq : genericTerm.headCtor = Term.HeadCtor.modIntro),
        Σ' (innerTerm : Term context innerType innerRaw),
           HEq genericTerm (Term.modIntro innerTerm) by
    exact key someTerm rfl headEq
  intro someType genericTerm sTyEq hcEq
  cases genericTerm
  case modIntro innerTermVal =>
    cases sTyEq
    exact ⟨innerTermVal, HEq.rfl⟩

/-- Focused progress theorem for the `Term.modElim` head (modal
elimination).  Every well-typed `modElim`-headed term is either
in WHNF (when the inner position is not a `modIntro`) or takes
a β-step (when the inner IS a `modIntro`).

M05.D.2 conditional eliminator #5 of 17.  Same template as
`Term.app_progress_or_step` but with `modElim`-shaped firing
via `Step.betaModElimIntro` and `Term.modIntroDestructAlgo`
for the typed inner-term extraction. -/
theorem Term.modElim_progress_or_step
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw) :
    Term.isWHNF (Term.modElim innerTerm) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.modElim innerTerm) target := by
  cases h : innerTerm.headCtor with
  | modIntro =>
      obtain ⟨innerInnerRaw, rawEq⟩ := Term.headCtor_modIntro_raw innerTerm h
      cases rawEq
      obtain ⟨innerInner, innerHeq⟩ := Term.modIntroDestructAlgo innerTerm h
      have innerEq := eq_of_heq innerHeq
      rw [innerEq]
      exact Or.inr ⟨_, _, _, Step.betaModElimIntro innerInner⟩
  | var =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | unit =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lam =>
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
  | uaToEquiv =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApply =>
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

/-- Algo-layer destructor for `Term.recordIntro`.  Extracts the
single field of a record introduction term when its `headCtor`
is `.recordIntro`.  Used by `Term.recordProj_progress_or_step`
to enable `Step.betaRecordProjIntro` firing. -/
def Term.recordIntroDestructAlgo {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    (someTerm : Term context (Ty.record singleFieldType)
                  (RawTerm.recordIntro firstRaw))
    (headEq : someTerm.headCtor = Term.HeadCtor.recordIntro) :
    Σ' (firstField : Term context singleFieldType firstRaw),
       HEq someTerm (Term.recordIntro firstField) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.recordIntro firstRaw))
        (sTyEq : someType = Ty.record singleFieldType)
        (hcEq : genericTerm.headCtor = Term.HeadCtor.recordIntro),
        Σ' (firstField : Term context singleFieldType firstRaw),
           HEq genericTerm (Term.recordIntro firstField) by
    exact key someTerm rfl headEq
  intro someType genericTerm sTyEq hcEq
  cases genericTerm
  case recordIntro firstFieldVal =>
    cases Ty.record.inj sTyEq
    exact ⟨firstFieldVal, HEq.rfl⟩

/-- Focused progress theorem for the `Term.recordProj` head.
M05.D.2 conditional eliminator #6 of 17.  Fires
`Step.betaRecordProjIntro` when the record head is
`.recordIntro`, otherwise WHNF. -/
theorem Term.recordProj_progress_or_step
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {recordRaw : RawTerm scope}
    (recordValue :
      Term context (Ty.record singleFieldType) recordRaw) :
    Term.isWHNF (Term.recordProj recordValue) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.recordProj recordValue) target := by
  cases h : recordValue.headCtor with
  | recordIntro =>
      obtain ⟨innerFirstRaw, rawEq⟩ := Term.headCtor_recordIntro_raw recordValue h
      cases rawEq
      obtain ⟨firstField, fieldHeq⟩ := Term.recordIntroDestructAlgo recordValue h
      have fieldEq := eq_of_heq fieldHeq
      rw [fieldEq]
      exact Or.inr ⟨_, _, _, Step.betaRecordProjIntro firstField⟩
  | var => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | unit => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lam => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | app => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lamPi => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | appPi => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | pair => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | fst => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | snd => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | boolTrue => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | boolFalse => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | boolElim => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natZero => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natSucc => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natElim => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natRec => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listNil => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listCons => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listElim => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionNone => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionSome => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionMatch => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherInl => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherInr => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherMatch => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | refl => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idJ => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | oeqRefl => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | oeqJ => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | oeqFunext => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idStrictRefl => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idStrictRec => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | modIntro => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | modElim => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | subsume => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | interval0 => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | interval1 => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | intervalOpp => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | intervalMeet => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | intervalJoin => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | pathLam => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | pathApp => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | glueIntro => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | glueElim => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | transp => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | hcomp => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | recordProj => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | refineIntro => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | refineElim => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | codataUnfold => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | codataDest => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sessionSend => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sessionRecv => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | effectPerform => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | universeCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | cumulUp => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivReflId => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | funextRefl => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivReflIdAtId => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | funextReflAtId => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivIntroHet => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApp => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | uaIntroHet => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | funextIntroHet => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | uaToEquiv => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApply => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | arrowCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | piTyCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sigmaTyCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | productCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sumCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl

/-- Algo-layer destructor for `Term.refineIntro`.  Extracts the
base value, predicate proof, and HEq witness when `headCtor`
is `.refineIntro`.  Used by `Term.refineElim_progress_or_step`
to enable `Step.betaRefineElimIntro` firing. -/
def Term.refineIntroDestructAlgo {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {valueRaw proofRaw : RawTerm scope}
    (someTerm : Term context (Ty.refine baseType predicate)
                  (RawTerm.refineIntro valueRaw proofRaw))
    (headEq : someTerm.headCtor = Term.HeadCtor.refineIntro) :
    Σ' (baseValue : Term context baseType valueRaw)
       (predicateProof : Term context Ty.unit proofRaw),
       HEq someTerm
         (Term.refineIntro predicate baseValue predicateProof) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType (RawTerm.refineIntro valueRaw proofRaw))
        (sTyEq : someType = Ty.refine baseType predicate)
        (hcEq : genericTerm.headCtor = Term.HeadCtor.refineIntro),
        Σ' (baseValue : Term context baseType valueRaw)
           (predicateProof : Term context Ty.unit proofRaw),
           HEq genericTerm
             (Term.refineIntro predicate baseValue predicateProof) by
    exact key someTerm rfl headEq
  intro someType genericTerm sTyEq hcEq
  cases genericTerm
  case refineIntro predicateBound baseValueBound predicateProofBound =>
    have refineEq := Ty.refine.inj sTyEq
    cases refineEq.1
    cases refineEq.2
    exact ⟨baseValueBound, predicateProofBound, HEq.rfl⟩

/-- Focused progress theorem for the `Term.refineElim` head.
M05.D.2 conditional eliminator #7 of 17.  Fires
`Step.betaRefineElimIntro` when the refined head is
`.refineIntro`, otherwise WHNF. -/
theorem Term.refineElim_progress_or_step
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {refinedRaw : RawTerm scope}
    (refinedValue :
      Term context (Ty.refine baseType predicate) refinedRaw) :
    Term.isWHNF (Term.refineElim refinedValue) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.refineElim refinedValue) target := by
  cases h : refinedValue.headCtor with
  | refineIntro =>
      obtain ⟨innerValueRaw, innerProofRaw, rawEq⟩ :=
        Term.headCtor_refineIntro_raw refinedValue h
      cases rawEq
      obtain ⟨baseValue, predicateProof, refinedHeq⟩ :=
        Term.refineIntroDestructAlgo refinedValue h
      have refinedEq := eq_of_heq refinedHeq
      rw [refinedEq]
      exact Or.inr ⟨_, _, _,
        Step.betaRefineElimIntro predicate baseValue predicateProof⟩
  | var => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | unit => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lam => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | app => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lamPi => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | appPi => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | pair => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | fst => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | snd => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | boolTrue => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | boolFalse => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | boolElim => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natZero => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natSucc => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natElim => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | natRec => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listNil => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listCons => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listElim => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionNone => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionSome => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionMatch => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherInl => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherInr => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherMatch => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | refl => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idJ => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | oeqRefl => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | oeqJ => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | oeqFunext => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idStrictRefl => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idStrictRec => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | modIntro => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | modElim => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | subsume => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | interval0 => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | interval1 => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | intervalOpp => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | intervalMeet => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | intervalJoin => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | pathLam => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | pathApp => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | glueIntro => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | glueElim => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | transp => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | hcomp => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | recordIntro => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | recordProj => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | refineElim => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | codataUnfold => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | codataDest => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sessionSend => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sessionRecv => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | effectPerform => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | universeCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | cumulUp => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivReflId => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | funextRefl => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivReflIdAtId => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | funextReflAtId => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivIntroHet => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApp => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | uaIntroHet => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | funextIntroHet => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | uaToEquiv => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApply => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | arrowCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | piTyCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sigmaTyCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | productCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | sumCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | listCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | optionCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | eitherCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | idCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivCode => apply Or.inl; simp only [Term.isWHNF, h]; rfl

/-- Focused progress theorem for the `Term.codataDest` head.
M05.D.2 conditional eliminator #8 of 17.  Currently a trivial
unconditional WHNF case: the raw layer ships no codata
observation β rule yet (`Term.isWHNF (Term.codataDest _) = true`
unconditionally per `Algo/WHNF/Evaluator.lean:382`).  When the
β rule lands this theorem will expand to the standard
firing/non-firing pattern. -/
theorem Term.codataDest_progress_or_step
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {codataRaw : RawTerm scope}
    (codataValue :
      Term context (Ty.codata stateType outputType) codataRaw) :
    Term.isWHNF (Term.codataDest codataValue) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.codataDest codataValue) target := Or.inl rfl

/-- Focused progress theorem for the `Term.subsume` head.
M05.D.2 conditional eliminator #9 of 17.  Trivial unconditional
WHNF case: `Term.isWHNF (Term.subsume _) = true` holds by
definition (no typed β rule `Step.betaSubsumeIntro` exists yet;
spec-blocker for M05.B.5.2 `Term.subsume_modIntro_steps` per the
docstring in `BetaIotaStepProvability.lean:326`).  Placeholder
for future kernel extension. -/
theorem Term.subsume_progress_or_step
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw) :
    Term.isWHNF (Term.subsume innerTerm) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.subsume innerTerm) target := Or.inl rfl

/-- Algo-layer destructor for `Term.pathLam` (cubical path
abstraction).  Given a term whose `headCtor` is `.pathLam` and
whose raw form is `RawTerm.pathLam bodyRaw` at a path type
`Ty.path carrierType leftEndpoint rightEndpoint`, extracts the
mode-univalent witness, the typed body under one interval
binder, and an HEq witness that the original term equals the
reconstructed `Term.pathLam` application.

`Term.pathLam` is the unique Term ctor producing `RawTerm.pathLam`,
so the destructor's `cases` only sees the pathLam case.  The
extra wrinkle vs `Term.modIntroDestructAlgo` is the
`modeIsUnivalent : mode = Mode.univalent` proof carried by
`Term.pathLam`'s signature — we recover that proof from the
cases pattern and thread it back into the HEq witness. -/
def Term.pathLamDestructAlgo {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {bodyRaw : RawTerm (scope + 1)}
    (someTerm :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint)
        (RawTerm.pathLam bodyRaw))
    (headEq : someTerm.headCtor = Term.HeadCtor.pathLam) :
    Σ' (modeIsUnivalent : mode = Mode.univalent)
       (body : Term (context.cons Ty.interval) carrierType.weaken bodyRaw),
       HEq someTerm
         (Term.pathLam modeIsUnivalent carrierType
            leftEndpoint rightEndpoint body) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.pathLam bodyRaw))
        (sTyEq : someType = Ty.path carrierType leftEndpoint rightEndpoint)
        (hcEq : genericTerm.headCtor = Term.HeadCtor.pathLam),
        Σ' (modeIsUnivalent : mode = Mode.univalent)
           (body : Term (context.cons Ty.interval) carrierType.weaken bodyRaw),
           HEq genericTerm
             (Term.pathLam modeIsUnivalent carrierType
                leftEndpoint rightEndpoint body) by
    exact key someTerm rfl headEq
  intro someType genericTerm sTyEq _hcEq
  cases genericTerm
  case pathLam modeIsUnivalent innerCarrier innerLeft innerRight body =>
    have pathEq := Ty.path.inj sTyEq
    cases pathEq.1
    cases pathEq.2.1
    cases pathEq.2.2
    exact ⟨modeIsUnivalent, body, HEq.rfl⟩

/-- Focused progress theorem for the `Term.pathApp` head (cubical
path application).  Every well-typed `pathApp`-headed term is
either in WHNF (when the path position is not a `pathLam`) or
takes a cubical β-step (when the path position IS a `pathLam`).

M05.D.2 conditional eliminator #10 of 17.  Same template as
`Term.app_progress_or_step` but with `Ty.path` source type for
the path position, `Term.pathLamDestructAlgo` for the typed
body + modeIsUnivalent witness extraction, and `Step.betaPathApp`
as the firing contraction.  Threads the `modeIsUnivalent` proof
recovered from the destructor through both the rewrite and the
firing step. -/
theorem Term.pathApp_progress_or_step
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {pathRaw intervalRaw : RawTerm scope}
    (pathTerm :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw)
    (intervalTerm : Term context Ty.interval intervalRaw) :
    Term.isWHNF (Term.pathApp modeIsUnivalent pathTerm intervalTerm) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.pathApp modeIsUnivalent pathTerm intervalTerm) target := by
  cases h : pathTerm.headCtor with
  | pathLam =>
      obtain ⟨bodyRaw, rawEq⟩ := Term.headCtor_pathLam_raw pathTerm h
      cases rawEq
      obtain ⟨univWitness, body, bodyHeq⟩ :=
        Term.pathLamDestructAlgo pathTerm h
      have bodyEq := eq_of_heq bodyHeq
      rw [bodyEq]
      exact Or.inr ⟨_, _, _, Step.betaPathApp univWitness body intervalTerm⟩
  | var =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | unit =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lam =>
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
  | uaToEquiv =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApply =>
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

/-- Algo-layer destructor for `Term.glueIntro` (cubical Glue
introduction).  Given a term whose `headCtor` is `.glueIntro`
and whose raw form is `RawTerm.glueIntro baseRaw partialRaw` at
a glue type `Ty.glue baseType boundaryWitness`, extracts the
mode-univalent witness, base and partial typed terms, and an
HEq witness.

`Term.glueIntro` is the unique Term ctor producing
`RawTerm.glueIntro`, so the destructor's `cases` only sees the
glueIntro case.  The signature carries `modeIsUnivalent` and
two payload terms; we recover all three via the cases pattern
and thread them back into the HEq witness. -/
def Term.glueIntroDestructAlgo {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {boundaryWitness : RawTerm scope}
    {baseRaw partialRaw : RawTerm scope}
    (someTerm :
      Term context (Ty.glue baseType boundaryWitness)
        (RawTerm.glueIntro baseRaw partialRaw))
    (headEq : someTerm.headCtor = Term.HeadCtor.glueIntro) :
    Σ' (modeIsUnivalent : mode = Mode.univalent)
       (baseValue : Term context baseType baseRaw)
       (partialValue : Term context baseType partialRaw),
       HEq someTerm
         (Term.glueIntro modeIsUnivalent baseType boundaryWitness
            baseValue partialValue) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType (RawTerm.glueIntro baseRaw partialRaw))
        (sTyEq : someType = Ty.glue baseType boundaryWitness)
        (hcEq : genericTerm.headCtor = Term.HeadCtor.glueIntro),
        Σ' (modeIsUnivalent : mode = Mode.univalent)
           (baseValue : Term context baseType baseRaw)
           (partialValue : Term context baseType partialRaw),
           HEq genericTerm
             (Term.glueIntro modeIsUnivalent baseType boundaryWitness
                baseValue partialValue) by
    exact key someTerm rfl headEq
  intro someType genericTerm sTyEq _hcEq
  cases genericTerm
  case glueIntro modeIsUnivalent innerBase innerBoundary
                 baseValueVal partialValueVal =>
    have glueEq := Ty.glue.inj sTyEq
    cases glueEq.1
    cases glueEq.2
    exact ⟨modeIsUnivalent, baseValueVal, partialValueVal, HEq.rfl⟩

/-- Focused progress theorem for the `Term.glueElim` head
(cubical Glue elimination).  Every well-typed `glueElim`-headed
term is either in WHNF (when the glued position is not a
`glueIntro`) or takes a cubical β-step (when the glued IS a
`glueIntro`).

M05.D.2 conditional eliminator #11 of 17.  Same template as
`Term.modElim_progress_or_step` (single-case destructor by raw
uniqueness) plus the `modeIsUnivalent` proof threaded through
both the outer `glueElim` and the firing
`Step.betaGlueElimIntro`. -/
theorem Term.glueElim_progress_or_step
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level scope}
    {boundaryWitness gluedRaw : RawTerm scope}
    (gluedValue :
      Term context (Ty.glue baseType boundaryWitness) gluedRaw) :
    Term.isWHNF (Term.glueElim modeIsUnivalent gluedValue) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.glueElim modeIsUnivalent gluedValue) target := by
  cases h : gluedValue.headCtor with
  | glueIntro =>
      obtain ⟨baseRaw, partialRaw, rawEq⟩ :=
        Term.headCtor_glueIntro_raw gluedValue h
      cases rawEq
      obtain ⟨univWitness, baseValue, partialValue, gluedHeq⟩ :=
        Term.glueIntroDestructAlgo gluedValue h
      have gluedEq := eq_of_heq gluedHeq
      rw [gluedEq]
      exact Or.inr
        ⟨_, _, _,
          Step.betaGlueElimIntro univWitness baseValue partialValue⟩
  | var =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | unit =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lam =>
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
  | uaToEquiv =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApply =>
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

/-- Algo-layer destructor for `Term.refl` at an identity type
`Ty.id carrier leftEndpoint rightEndpoint` with raw form
`RawTerm.refl witnessRaw`.  `Term.refl` produces type
`Ty.id carrier rawWitness rawWitness` — both endpoints equal the
raw witness — so destructuring forces `leftEndpoint = witnessRaw`
and `rightEndpoint = witnessRaw` plus an HEq witness aligning
`someTerm` with the canonical `Term.refl carrier witnessRaw`.

Inlined here to avoid importing `Term.PreservesTerm.BetaCastWallDemolition`
(which lives at a later layer pulling in `Reduction.ParRed`).
Pattern follows `Term.idReflDestruct`; both definitions are
byte-equivalent except for the name. -/
def Term.idReflDestructAlgo {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {witnessRaw : RawTerm scope}
    (someTerm :
      Term context (Ty.id carrier leftEndpoint rightEndpoint)
                   (RawTerm.refl witnessRaw)) :
    Σ' (leftEqWitness : leftEndpoint = witnessRaw)
       (rightEqWitness : rightEndpoint = witnessRaw),
       HEq someTerm (Term.refl (context := context) carrier witnessRaw) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.refl witnessRaw)),
        someType = Ty.id carrier leftEndpoint rightEndpoint →
        Σ' (leftEqWitness : leftEndpoint = witnessRaw)
           (rightEqWitness : rightEndpoint = witnessRaw),
           HEq genericTerm
                (Term.refl (context := context) carrier witnessRaw) by
    exact key someTerm rfl
  intro someType genericTerm someTypeIsId
  cases genericTerm
  rename_i innerCarrier
  have idEq := Ty.id.inj someTypeIsId
  cases idEq.1
  exact ⟨idEq.2.1.symm, idEq.2.2.symm, HEq.rfl⟩

/-- Focused progress theorem for the `Term.idJ` head (HoTT
identity-type J).  Every well-typed `idJ`-headed term is either
in WHNF (when the witness position is not a `refl`) or takes a
ι-step (when the witness IS a `refl`).

M05.D.2 conditional eliminator #12 of 17.  Endpoint-equality
complication: `Term.refl carrier rawWitness` has type
`Ty.id carrier rawWitness rawWitness`, so the outer
`leftEndpoint, rightEndpoint` get forced equal to the refl's
raw witness via `Ty.id.inj` inside `Term.idReflDestructAlgo`.
After substituting both endpoints via the returned `Eq` witnesses
and rewriting `witness` through the HEq, `Step.iotaIdJRefl` fires
producing `baseCase` as the contractum. -/
theorem Term.idJ_progress_or_step
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    (witness :
      Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw) :
    Term.isWHNF (Term.idJ baseCase witness) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.idJ baseCase witness) target := by
  cases h : witness.headCtor with
  | refl =>
      obtain ⟨reflRaw, rawEq⟩ := Term.headCtor_refl_raw witness h
      cases rawEq
      obtain ⟨leftEqRefl, rightEqRefl, witnessHeq⟩ :=
        Term.idReflDestructAlgo witness
      -- leftEqRefl : leftEndpoint = reflRaw, rightEqRefl : rightEndpoint = reflRaw.
      -- `cases` substitutes the later-introduced binder (reflRaw) into the
      -- earlier ones, so reflRaw is consumed and both endpoints survive.
      -- Pass `leftEndpoint` to iotaIdJRefl; rightEndpoint then matches via
      -- the second cases substitution.
      cases leftEqRefl
      cases rightEqRefl
      have witnessEq := eq_of_heq witnessHeq
      rw [witnessEq]
      exact Or.inr
        ⟨_, _, _, Step.iotaIdJRefl carrier leftEndpoint baseCase⟩
  | var =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | unit =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lam =>
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
  | uaToEquiv =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApply =>
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

/-- Progress or step for `Term.boolElim`: when the scrutinee's head
is `boolTrue`, the term fires via `Step.iotaBoolElimTrue` producing
`thenBranch`; when `boolFalse`, via `Step.iotaBoolElimFalse` producing
`elseBranch`; for any other 74 heads, the boolElim is itself in WHNF
(template arm).

M05.D.2 conditional eliminator #13 of 17.  First TWO-firing case:
both literal Boolean introducers produce contracta.  Unlike the
previous three (pathApp/glueElim/idJ) — which required inlined
destructors to deconstruct unique-raw-shape Term ctors — boolElim
needs NO new destructor since `boolTrue` and `boolFalse` are
nullary canonical heads.  We reuse `Term.headCtor_boolTrue_raw` /
`_boolFalse_raw` (Algo/WHNF/NullaryInversions.lean) to recover the
raw projection from the head-ctor dispatch, then `Term.boolTrue_unique`
/ `_boolFalse_unique` (Term/Inversion.lean) to identify the scrutinee
with the literal at the typed level.  Same pattern as `headStep?_sound_boolElimTrue` in `Algo/Soundness.lean:70-86`. -/
theorem Term.boolElim_progress_or_step
    {context : Ctx mode level scope}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    (scrutinee : Term context Ty.bool scrutineeRaw)
    (thenBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw) :
    Term.isWHNF (Term.boolElim scrutinee thenBranch elseBranch) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.boolElim scrutinee thenBranch elseBranch) target := by
  cases h : scrutinee.headCtor with
  | boolTrue =>
      have rawEq : scrutineeRaw = RawTerm.boolTrue :=
        Term.headCtor_boolTrue_raw scrutinee h
      cases rawEq
      have scrutEq : scrutinee = Term.boolTrue :=
        eq_of_heq (Term.boolTrue_unique scrutinee Term.boolTrue)
      rw [scrutEq]
      exact Or.inr
        ⟨_, _, _, Step.iotaBoolElimTrue thenBranch elseBranch⟩
  | boolFalse =>
      have rawEq : scrutineeRaw = RawTerm.boolFalse :=
        Term.headCtor_boolFalse_raw scrutinee h
      cases rawEq
      have scrutEq : scrutinee = Term.boolFalse :=
        eq_of_heq (Term.boolFalse_unique scrutinee Term.boolFalse)
      rw [scrutEq]
      exact Or.inr
        ⟨_, _, _, Step.iotaBoolElimFalse thenBranch elseBranch⟩
  | var =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | unit =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lam =>
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
  | uaToEquiv =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApply =>
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

/-- Progress or step for `Term.natElim`: when the scrutinee's head is
`natZero`, the term fires via `Step.iotaNatElimZero` producing
`zeroBranch`; when `natSucc`, via `Step.iotaNatElimSucc` producing
`Term.app succBranch predecessor`; for any other 74 heads, the natElim
is itself in WHNF (template arm).

M05.D.2 conditional eliminator #14 of 17.  Second two-firing case.
Unlike `boolElim_progress_or_step` (#13), the `natSucc` firing branch
needs the destructor `Term.natSuccDestruct` (Term/Inversion.lean:123)
to extract the predecessor for the `Step.iotaNatElimSucc` reduct
`Term.app succBranch predTerm`.  The `natZero` arm is identical in
shape to a nullary-canonical firing (parallel to boolTrue/boolFalse).
Same pattern as `headStep?_sound_natElimSucc` in
`Algo/Soundness.lean:251-267`. -/
theorem Term.natElim_progress_or_step
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw) :
    Term.isWHNF (Term.natElim scrutinee zeroBranch succBranch) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.natElim scrutinee zeroBranch succBranch) target := by
  cases h : scrutinee.headCtor with
  | natZero =>
      have rawEq : scrutineeRaw = RawTerm.natZero :=
        Term.headCtor_natZero_raw scrutinee h
      cases rawEq
      have scrutEq : scrutinee = Term.natZero :=
        eq_of_heq (Term.natZero_unique scrutinee Term.natZero)
      rw [scrutEq]
      exact Or.inr
        ⟨_, _, _, Step.iotaNatElimZero zeroBranch succBranch⟩
  | natSucc =>
      obtain ⟨predRaw, rawEq⟩ := Term.headCtor_natSucc_raw scrutinee h
      cases rawEq
      obtain ⟨predTerm, scrutHEq⟩ := Term.natSuccDestruct scrutinee
      have scrutEq : scrutinee = Term.natSucc predTerm :=
        eq_of_heq scrutHEq
      rw [scrutEq]
      exact Or.inr
        ⟨_, _, _, Step.iotaNatElimSucc predTerm zeroBranch succBranch⟩
  | var =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | unit =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lam =>
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
  | uaToEquiv =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApply =>
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

/-- Progress or step for `Term.natRec`: when scrutinee head is `natZero`,
fires `Step.iotaNatRecZero` producing `zeroBranch`; when `natSucc`,
fires `Step.iotaNatRecSucc` producing `Term.app (Term.app succBranch
predecessor) (Term.natRec predecessor zeroBranch succBranch)`; otherwise
natRec is WHNF.

M05.D.2 conditional eliminator #15 of 17.  Mirrors
`natElim_progress_or_step` structure; only difference is `succBranch`
has binary arrow type (predecessor + prior result) and the reduct is
a nested `Term.app` chain.  Reuses the same `Term.natSuccDestruct`.
Pattern at `Algo/Soundness.lean:269-288`. -/
theorem Term.natRec_progress_or_step
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw) :
    Term.isWHNF (Term.natRec scrutinee zeroBranch succBranch) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.natRec scrutinee zeroBranch succBranch) target := by
  cases h : scrutinee.headCtor with
  | natZero =>
      have rawEq : scrutineeRaw = RawTerm.natZero :=
        Term.headCtor_natZero_raw scrutinee h
      cases rawEq
      have scrutEq : scrutinee = Term.natZero :=
        eq_of_heq (Term.natZero_unique scrutinee Term.natZero)
      rw [scrutEq]
      exact Or.inr
        ⟨_, _, _, Step.iotaNatRecZero zeroBranch succBranch⟩
  | natSucc =>
      obtain ⟨predRaw, rawEq⟩ := Term.headCtor_natSucc_raw scrutinee h
      cases rawEq
      obtain ⟨predTerm, scrutHEq⟩ := Term.natSuccDestruct scrutinee
      have scrutEq : scrutinee = Term.natSucc predTerm :=
        eq_of_heq scrutHEq
      rw [scrutEq]
      exact Or.inr
        ⟨_, _, _, Step.iotaNatRecSucc predTerm zeroBranch succBranch⟩
  | var =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | unit =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lam =>
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
  | uaToEquiv =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApply =>
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

/-! ## Parametric-canonical uniqueness helpers

The four parametric nullary canonical introducers — `listNil`,
`optionNone`, `eitherInl`-style and `eitherInr`-style — are not
uniquely determined by their raw projection alone: each carries
implicit type parameters (elementType for list/option;
leftType/rightType for either) that the destructor needs to align.
The helpers below specialize `Term.<X>_unique` from
`Term/Inversion.lean` to the case where both terms live at the
SAME parametric type, freeing the index via `suffices` and
realigning with the relevant `Ty.<X>.inj` injectivity lemma.

Identical in shape to the `_sameType` companions in
`Algo/Soundness.lean:142-188`; reinlined here because
`Algo.Soundness` depends transitively on `Algo.Progress.Headline`
(via `Algo.Eval`), so we cannot import it without creating a
cycle.  Each ships zero-axiom under the matcher rules cited
in `feedback_lean_free_type_via_suffices.md`. -/

/-- Strong listNil uniqueness when both terms are at the SAME
element type. -/
theorem Term.listNil_unique_sameType
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    (firstNil secondNil :
      Term context (Ty.listType elementType) RawTerm.listNil) :
    HEq firstNil secondNil := by
  suffices key : ∀ {firstType secondType : Ty level scope}
                  (firstGeneric : Term context firstType RawTerm.listNil)
                  (secondGeneric : Term context secondType RawTerm.listNil),
                  firstType = Ty.listType elementType →
                  secondType = Ty.listType elementType →
                  HEq firstGeneric secondGeneric by
    exact key firstNil secondNil rfl rfl
  intro firstType secondType firstGeneric secondGeneric firstTypeEq secondTypeEq
  cases firstGeneric
  cases secondGeneric
  rename_i firstElement secondElement
  have firstElementEq : firstElement = elementType := Ty.listType.inj firstTypeEq
  have secondElementEq : secondElement = elementType := Ty.listType.inj secondTypeEq
  cases firstElementEq
  cases secondElementEq
  rfl

/-- Strong optionNone uniqueness when both terms are at the SAME
element type. -/
theorem Term.optionNone_unique_sameType
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    (firstNone secondNone :
      Term context (Ty.optionType elementType) RawTerm.optionNone) :
    HEq firstNone secondNone := by
  suffices key : ∀ {firstType secondType : Ty level scope}
                  (firstGeneric : Term context firstType RawTerm.optionNone)
                  (secondGeneric : Term context secondType RawTerm.optionNone),
                  firstType = Ty.optionType elementType →
                  secondType = Ty.optionType elementType →
                  HEq firstGeneric secondGeneric by
    exact key firstNone secondNone rfl rfl
  intro firstType secondType firstGeneric secondGeneric firstTypeEq secondTypeEq
  cases firstGeneric
  cases secondGeneric
  rename_i firstElement secondElement
  have firstElementEq : firstElement = elementType := Ty.optionType.inj firstTypeEq
  have secondElementEq : secondElement = elementType := Ty.optionType.inj secondTypeEq
  cases firstElementEq
  cases secondElementEq
  rfl

/-- Progress or step for `Term.listElim`: when scrutinee head is `listNil`,
fires `Step.iotaListElimNil` producing `nilBranch`; when `listCons`, fires
`Step.iotaListElimCons` producing
`Term.app (Term.app consBranch head) tail`; otherwise listElim is WHNF.

M05.D.2 conditional eliminator #16 of 17.  Parametric two-firing case
over `listType elementType`: the `listNil` arm needs `listNil_unique_sameType`
(parametric, requires same `elementType`) rather than the simpler `_unique`;
the `listCons` arm uses `Term.listConsDestruct` (yields head + tail + HEq).
Mirrors `Algo/Soundness.lean:190-206` (nil) and `Algo/Soundness.lean:291-311`
(cons). -/
theorem Term.listElim_progress_or_step
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    (scrutinee : Term context (Ty.listType elementType) scrutineeRaw)
    (nilBranch : Term context motiveType nilRaw)
    (consBranch :
      Term context (Ty.arrow elementType
                      (Ty.arrow (Ty.listType elementType) motiveType)) consRaw) :
    Term.isWHNF (Term.listElim scrutinee nilBranch consBranch) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.listElim scrutinee nilBranch consBranch) target := by
  cases h : scrutinee.headCtor with
  | listNil =>
      have rawEq : scrutineeRaw = RawTerm.listNil :=
        Term.headCtor_listNil_raw scrutinee h
      cases rawEq
      have scrutEq : scrutinee = Term.listNil :=
        eq_of_heq (Term.listNil_unique_sameType scrutinee Term.listNil)
      rw [scrutEq]
      exact Or.inr
        ⟨_, _, _, Step.iotaListElimNil nilBranch consBranch⟩
  | listCons =>
      obtain ⟨headRaw, tailRaw, rawEq⟩ := Term.headCtor_listCons_raw scrutinee h
      cases rawEq
      obtain ⟨headTerm, tailTerm, scrutHEq⟩ := Term.listConsDestruct scrutinee
      have scrutEq : scrutinee = Term.listCons headTerm tailTerm :=
        eq_of_heq scrutHEq
      rw [scrutEq]
      exact Or.inr
        ⟨_, _, _, Step.iotaListElimCons headTerm tailTerm nilBranch consBranch⟩
  | var =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | unit =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lam =>
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
  | uaToEquiv =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApply =>
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

/-- Progress or step for `Term.optionMatch`: when scrutinee head is
`optionNone`, fires `Step.iotaOptionMatchNone` producing `noneBranch`;
when `optionSome`, fires `Step.iotaOptionMatchSome` producing
`Term.app someBranch valueTerm`; otherwise optionMatch is WHNF.

M05.D.2 conditional eliminator #17 of 17.  Final ι-elimination of
M05.D.2.  Parametric over `optionType elementType`.  Uses pre-staged
`Term.optionNone_unique_sameType` (inlined just before listElim) for
the noneBranch arm; uses `Term.optionSomeDestruct` (Term/Inversion.lean)
for the someBranch arm.  Mirrors `Algo/Soundness.lean:208-223` (none)
and `Algo/Soundness.lean:313-330` (some). -/
theorem Term.optionMatch_progress_or_step
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    (scrutinee : Term context (Ty.optionType elementType) scrutineeRaw)
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw) :
    Term.isWHNF (Term.optionMatch scrutinee noneBranch someBranch) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.optionMatch scrutinee noneBranch someBranch) target := by
  cases h : scrutinee.headCtor with
  | optionNone =>
      have rawEq : scrutineeRaw = RawTerm.optionNone :=
        Term.headCtor_optionNone_raw scrutinee h
      cases rawEq
      have scrutEq : scrutinee = Term.optionNone :=
        eq_of_heq (Term.optionNone_unique_sameType scrutinee Term.optionNone)
      rw [scrutEq]
      exact Or.inr
        ⟨_, _, _, Step.iotaOptionMatchNone noneBranch someBranch⟩
  | optionSome =>
      obtain ⟨valueRaw, rawEq⟩ := Term.headCtor_optionSome_raw scrutinee h
      cases rawEq
      obtain ⟨valueTerm, scrutHEq⟩ := Term.optionSomeDestruct scrutinee
      have scrutEq : scrutinee = Term.optionSome valueTerm :=
        eq_of_heq scrutHEq
      rw [scrutEq]
      exact Or.inr
        ⟨_, _, _, Step.iotaOptionMatchSome valueTerm noneBranch someBranch⟩
  | var =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | unit =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lam =>
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
  | uaToEquiv =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApply =>
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

/-- Progress or step for `Term.eitherMatch`: when scrutinee head is
`eitherInl`, fires `Step.iotaEitherMatchInl` producing
`Term.app leftBranch valueTerm`; when `eitherInr`, fires
`Step.iotaEitherMatchInr` producing `Term.app rightBranch valueTerm`;
otherwise eitherMatch is WHNF.

M05.D.2 conditional eliminator #18 (final two-firing case for the
M05.D.2 sweep).  Both eitherInl and eitherInr carry a single value
payload, so both firings use destructors — no nullary-uniqueness
lemma needed.  Mirrors `Algo/Soundness.lean:332-350` (inl) and
`Algo/Soundness.lean:352-370` (inr). -/
theorem Term.eitherMatch_progress_or_step
    {context : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    (scrutinee : Term context (Ty.eitherType leftType rightType) scrutineeRaw)
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw) :
    Term.isWHNF (Term.eitherMatch scrutinee leftBranch rightBranch) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.eitherMatch scrutinee leftBranch rightBranch) target := by
  cases h : scrutinee.headCtor with
  | eitherInl =>
      obtain ⟨valueRaw, rawEq⟩ := Term.headCtor_eitherInl_raw scrutinee h
      cases rawEq
      obtain ⟨valueTerm, scrutHEq⟩ := Term.eitherInlDestruct scrutinee
      have scrutEq : scrutinee = Term.eitherInl (rightType := rightType) valueTerm :=
        eq_of_heq scrutHEq
      rw [scrutEq]
      exact Or.inr
        ⟨_, _, _, Step.iotaEitherMatchInl valueTerm leftBranch rightBranch⟩
  | eitherInr =>
      obtain ⟨valueRaw, rawEq⟩ := Term.headCtor_eitherInr_raw scrutinee h
      cases rawEq
      obtain ⟨valueTerm, scrutHEq⟩ := Term.eitherInrDestruct scrutinee
      have scrutEq : scrutinee = Term.eitherInr (leftType := leftType) valueTerm :=
        eq_of_heq scrutHEq
      rw [scrutEq]
      exact Or.inr
        ⟨_, _, _, Step.iotaEitherMatchInr valueTerm leftBranch rightBranch⟩
  | var =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | unit =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | lam =>
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
  | uaToEquiv =>
      apply Or.inl; simp only [Term.isWHNF, h]; rfl
  | equivApply =>
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

/-- Unified Wright-Felleisen progress headline (#1565, #1737 close).

Every well-typed `Term` is either in weak head normal form
(`Term.isWHNF someTerm = true`) or takes a `Step` to some
target.  Covers all 77 Term constructors via a single
`cases someTerm` dispatch:

* 61 always-WHNF / cong-only / value-introduction ctors close
  with `Or.inl rfl` — they evaluate to `Term.isWHNF` by
  definition.
* 16 conditional eliminators (`app`, `appPi`, `fst`, `snd`,
  `boolElim`, `natElim`, `natRec`, `listElim`, `optionMatch`,
  `eitherMatch`, `idJ`, `modElim`, `pathApp`, `glueElim`,
  `recordProj`, `refineElim`) route to their focused
  per-construct helper (each shipped earlier in this file).

Zero-axiom under strict policy: every arm is either a
definitional `Or.inl rfl` or an `exact` invocation of a
zero-axiom helper. -/
theorem Term.progress_or_step
    {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw) :
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
  | hcompPath _ _ _ _ _ => exact Or.inl rfl
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
  | uaToEquiv _ _ _ _ _ _ _ => exact Or.inl rfl
  | equivApp _ _ => exact Or.inl rfl
  | equivApply _ _ => exact Or.inl rfl
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
  | app functionTerm argumentTerm =>
      exact Term.app_progress_or_step functionTerm argumentTerm
  | appPi functionTerm argumentTerm =>
      exact Term.appPi_progress_or_step functionTerm argumentTerm
  | fst pairTerm =>
      exact Term.fst_progress_or_step pairTerm
  | snd pairTerm =>
      exact Term.snd_progress_or_step pairTerm
  | boolElim scrutinee thenBranch elseBranch =>
      exact Term.boolElim_progress_or_step scrutinee thenBranch elseBranch
  | natElim scrutinee zeroBranch succBranch =>
      exact Term.natElim_progress_or_step scrutinee zeroBranch succBranch
  | natRec scrutinee zeroBranch succBranch =>
      exact Term.natRec_progress_or_step scrutinee zeroBranch succBranch
  | listElim scrutinee nilBranch consBranch =>
      exact Term.listElim_progress_or_step scrutinee nilBranch consBranch
  | optionMatch scrutinee noneBranch someBranch =>
      exact Term.optionMatch_progress_or_step scrutinee noneBranch someBranch
  | eitherMatch scrutinee leftBranch rightBranch =>
      exact Term.eitherMatch_progress_or_step scrutinee leftBranch rightBranch
  | idJ baseCase witness =>
      exact Term.idJ_progress_or_step baseCase witness
  | modElim innerTerm =>
      exact Term.modElim_progress_or_step innerTerm
  | pathApp modeIsUnivalent pathTerm intervalTerm =>
      exact Term.pathApp_progress_or_step modeIsUnivalent pathTerm intervalTerm
  | glueElim modeIsUnivalent gluedValue =>
      exact Term.glueElim_progress_or_step modeIsUnivalent gluedValue
  | recordProj recordValue =>
      exact Term.recordProj_progress_or_step recordValue
  | refineElim refinedValue =>
      exact Term.refineElim_progress_or_step refinedValue

end LeanFX2
