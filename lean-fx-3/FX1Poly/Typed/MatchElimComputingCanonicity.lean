import FX1Poly.Typed.ClosedNatCanonicity
import FX1Poly.Core.OptionCanonicalFormsCandidate
import FX1Poly.Core.EitherCanonicalFormsCandidate
import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.HasTypeDescOptionMatch
import FX1Poly.Typed.HasTypeDescEitherMatch

/-! # FX1Poly/Typed/MatchElimComputingCanonicity
    — the NON-RECURSIVE function-branch eliminator-computing canonicity (completes the coverage)

This file completes the typed-engine eliminator-computing-canonicity coverage across all four structural
eliminator shapes:

  * **projection / value-branch** — `boolElim` (`BoolElimValueCanonicity`): branches are values, one ι-step.
  * **recursive function-branch** — `natElim` / `listElim` (`NatElimComputingCanonicity` /
    `ListElimComputingCanonicity`): the branch is a curried function, the recursive call reappears in the reduct.
  * **non-recursive function-branch** — `optionMatch` / `eitherMatch`, HERE.

`optionMatch` / `eitherMatch` are the non-recursive eliminators whose firing branch is a FUNCTION applied to the
wrapped value — their ι-rules are 1-argument app-chains:

    optionMatch m n s (optionSome v)  ↝  app s v        eitherMatch m l r (eitherInl v)  ↝  app l v
    optionMatch m n s optionNone      ↝  n              eitherMatch m l r (eitherInr v)  ↝  app r v

So there is no recursion (no IH) but, unlike `boolElim`, the some/inl/inr branch is a function whose application
to the wrapped value must itself compute — the genuine new content over the value-branch bool case.

## What this ships

  * `optionMatchCell` / `eitherMatchCell` — the `gen_optionMatch` / `gen_eitherMatch` cells.
  * **`optionMatchComputesToValue` (★)** — a closed `optionMatch(s, n, branch)` with a result-valued none-branch
    and a some-branch producing a result value from the wrapped (normal) payload (`stepProduces`) computes to a
    result value, for every closed option VALUE.  Case split on `isOptionValue` (a disjunction): `none` projects
    the none-branch (`iotaOptionMatchNone`); `some payload` fires `iotaOptionMatchSome` to `app branch payload`,
    then `stepProduces` finishes.  General over the result predicate.
  * **`eitherMatchComputesToValue` (★)** — the either twin, with `leftProduces` / `rightProduces` for the two
    injections (`iotaEitherMatchInl` / `iotaEitherMatchInr`).
  * **`optionMatchConstComputesToNumeral`** — the constant fold `λ_. natZero` collapses every option to `natZero`.
  * **`optionMatchIdComputesToValue` (★)** — the identity some-branch `λx. x` USES the wrapped payload, returning
    it; the closed result is the payload itself (a normal form).  The non-recursive analogue of the length/copy
    folds — the branch threads the wrapped data out.
  * **`eitherMatchConstComputesToNumeral`** + `*.smoke` non-vacuity witnesses.

## What remains (honest)

This completes the eliminator-computing-canonicity COVERAGE for #1138 across every structural eliminator shape.
The remaining integration (shared with the other eliminators) is the standalone typed `HasType*Match` judgment
whose branch is grown-typed at the function type, feeding the grown typing into `stepProduces` unconditionally —
the GTL combined-engine follow-on (#832/#1138).  Here the branch's value-production is supplied explicitly and
discharged for the constant and identity branches.

## Zero-axiom verification

Each abstract theorem is an `rcases` on the value disjunction composing `StepStar.single` ι-steps with the
branch's `StepStar` chain via `StepStar.trans_compose`; the concrete folds discharge `stepProduces` by one
`Step.beta` (`subst0` computes definitionally on the closed / identity body).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

-- The `optionMatchCell` / `eitherMatchCell` constructors are provided by `HasTypeDescOptionMatch` /
-- `HasTypeDescEitherMatch` (the DI-5 eliminator-judgment files); we reuse them so the ι-rules line up.

/-- **★ Non-recursive option-eliminator computing canonicity.**  A closed `optionMatch(s, none, branch)` with a
result-valued none-branch and a some-branch that produces a result value from the wrapped (normal) payload
(`stepProduces`) computes (`↝*`) to a result value, for every closed option value `s`.

Case split on `isOptionValue s` (a disjunction): `none` ι-projects the none-branch (`Step.iotaOptionMatchNone`);
`some payload` (with `payload` normal) ι-fires to `app branch payload` (`Step.iotaOptionMatchSome`), then the
branch's `stepProduces` on the normal payload finishes.  No recursion — but the some-branch is a function whose
application must compute (the content the value-branch bool case lacked). -/
theorem optionMatchComputesToValue {isResultValue : RawTerm 0 → Prop}
    {motive : RawTerm 1}
    {noneBranch someBranch : RawTerm 0}
    (noneBranchValue : isResultValue noneBranch)
    (stepProduces : ∀ payload : RawTerm 0, RawTerm.isStepNormalForm payload →
        ∃ out : RawTerm 0, StepStar (appCell someBranch payload) out ∧ isResultValue out)
    {scrutinee : RawTerm 0} (scrutineeValue : isOptionValue scrutinee) :
    ∃ out : RawTerm 0,
      StepStar (optionMatchCell motive noneBranch someBranch scrutinee) out ∧ isResultValue out := by
  rcases scrutineeValue with noneEq | ⟨payload, someEq, payloadNormal⟩
  · subst noneEq
    exact ⟨noneBranch, StepStar.single Step.iotaOptionMatchNone, noneBranchValue⟩
  · subst someEq
    obtain ⟨out, appChain, outValue⟩ := stepProduces payload payloadNormal
    exact ⟨out, StepStar.trans_compose (StepStar.single Step.iotaOptionMatchSome) appChain, outValue⟩

/-- **★ Non-recursive either-eliminator computing canonicity.**  The either twin of
`optionMatchComputesToValue`: a closed `eitherMatch(s, left, right)` whose two branches each produce a result
value from the wrapped (normal) payload (`leftProduces` / `rightProduces`) computes to a result value, for every
closed either value `s` (`inl` fires `Step.iotaEitherMatchInl`, `inr` fires `Step.iotaEitherMatchInr`). -/
theorem eitherMatchComputesToValue {isResultValue : RawTerm 0 → Prop}
    {motive : RawTerm 1}
    {leftBranch rightBranch : RawTerm 0}
    (leftProduces : ∀ payload : RawTerm 0, RawTerm.isStepNormalForm payload →
        ∃ out : RawTerm 0, StepStar (appCell leftBranch payload) out ∧ isResultValue out)
    (rightProduces : ∀ payload : RawTerm 0, RawTerm.isStepNormalForm payload →
        ∃ out : RawTerm 0, StepStar (appCell rightBranch payload) out ∧ isResultValue out)
    {scrutinee : RawTerm 0} (scrutineeValue : isEitherValue scrutinee) :
    ∃ out : RawTerm 0,
      StepStar (eitherMatchCell motive leftBranch rightBranch scrutinee) out ∧ isResultValue out := by
  rcases scrutineeValue with ⟨payload, inlEq, payloadNormal⟩ | ⟨payload, inrEq, payloadNormal⟩
  · subst inlEq
    obtain ⟨out, appChain, outValue⟩ := leftProduces payload payloadNormal
    exact ⟨out, StepStar.trans_compose (StepStar.single Step.iotaEitherMatchInl) appChain, outValue⟩
  · subst inrEq
    obtain ⟨out, appChain, outValue⟩ := rightProduces payload payloadNormal
    exact ⟨out, StepStar.trans_compose (StepStar.single Step.iotaEitherMatchInr) appChain, outValue⟩

/-! ## Concrete instance 1: the constant fold (`λ_. natZero`, ignores the wrapped payload) -/

/-- **Constant option fold canonicity.**  `optionMatch(s, natZero, λ_.natZero)` computes to a numeral (in fact
`natZero`) for every closed option value `s` — the constant some-branch β-reduces to `natZero` regardless of the
wrapped payload (`subst0 natZero payload = natZero` definitionally). -/
theorem optionMatchConstComputesToNumeral {scrutinee : RawTerm 0} (scrutineeValue : isOptionValue scrutinee) :
    ∃ out : RawTerm 0,
      StepStar
        (optionMatchCell (variableCell (⟨0, by decide⟩ : Fin 1)) natZeroCell
          (lamCell natZeroCell (natZeroCell : RawTerm 1)) scrutinee) out ∧
      IsNatNumeral out :=
  optionMatchComputesToValue (isResultValue := IsNatNumeral)
    IsNatNumeral.zero
    (fun payload _payloadNormal => by
      refine ⟨natZeroCell, ?_, IsNatNumeral.zero⟩
      have betaStep : Step (appCell (lamCell natZeroCell (natZeroCell : RawTerm 1)) payload) natZeroCell := Step.beta
      exact StepStar.single betaStep)
    scrutineeValue

/-- **Constant either fold canonicity.**  `eitherMatch(s, λ_.natZero, λ_.natZero)` computes to a numeral for
every closed either value `s`. -/
theorem eitherMatchConstComputesToNumeral {scrutinee : RawTerm 0} (scrutineeValue : isEitherValue scrutinee) :
    ∃ out : RawTerm 0,
      StepStar
        (eitherMatchCell (variableCell (⟨0, by decide⟩ : Fin 1))
          (lamCell natZeroCell (natZeroCell : RawTerm 1)) (lamCell natZeroCell (natZeroCell : RawTerm 1)) scrutinee)
        out ∧ IsNatNumeral out :=
  eitherMatchComputesToValue (isResultValue := IsNatNumeral)
    (fun payload _payloadNormal => by
      refine ⟨natZeroCell, ?_, IsNatNumeral.zero⟩
      have betaStep : Step (appCell (lamCell natZeroCell (natZeroCell : RawTerm 1)) payload) natZeroCell := Step.beta
      exact StepStar.single betaStep)
    (fun payload _payloadNormal => by
      refine ⟨natZeroCell, ?_, IsNatNumeral.zero⟩
      have betaStep : Step (appCell (lamCell natZeroCell (natZeroCell : RawTerm 1)) payload) natZeroCell := Step.beta
      exact StepStar.single betaStep)
    scrutineeValue

/-! ## Concrete instance 2: the identity fold (`λx. x`, USES the wrapped payload) -/

/-- **★ Identity option fold canonicity (wrapped payload USED).**  `optionMatch(s, boolTrue, λx.x)` computes to a
normal form for every closed option value `s` — the identity some-branch β-reduces `app (λx.x) payload` to the
wrapped `payload`, which is normal (from `isOptionValue`), so the eliminator threads the wrapped data OUT.  The
non-recursive analogue of the length/copy folds — the branch genuinely uses its argument. -/
theorem optionMatchIdComputesToValue {scrutinee : RawTerm 0} (scrutineeValue : isOptionValue scrutinee) :
    ∃ out : RawTerm 0,
      StepStar
        (optionMatchCell (variableCell (⟨0, by decide⟩ : Fin 1)) boolTrueCell
          (lamCell natZeroCell (variableCell (⟨0, by decide⟩ : Fin 1))) scrutinee) out ∧
      RawTerm.isStepNormalForm out :=
  optionMatchComputesToValue (isResultValue := RawTerm.isStepNormalForm)
    (by decide)
    (fun payload payloadNormal => by
      refine ⟨payload, ?_, payloadNormal⟩
      have betaStep :
          Step (appCell (lamCell natZeroCell (variableCell (⟨0, by decide⟩ : Fin 1))) payload) payload := Step.beta
      exact StepStar.single betaStep)
    scrutineeValue

/-- **Non-vacuity (option)**: the identity fold over `some boolTrue` computes to a normal form (namely
`boolTrue`). -/
theorem optionMatchIdComputesToValue.smoke :
    ∃ out : RawTerm 0,
      StepStar
        (optionMatchCell (variableCell (⟨0, by decide⟩ : Fin 1)) boolTrueCell
          (lamCell natZeroCell (variableCell (⟨0, by decide⟩ : Fin 1))) (optionSomeCell boolTrueCell)) out ∧
      RawTerm.isStepNormalForm out :=
  optionMatchIdComputesToValue (Or.inr ⟨boolTrueCell, rfl, by decide⟩)

/-- **Non-vacuity (either)**: the constant fold over `inl boolTrue` computes to a numeral. -/
theorem eitherMatchConstComputesToNumeral.smoke :
    ∃ out : RawTerm 0,
      StepStar
        (eitherMatchCell (variableCell (⟨0, by decide⟩ : Fin 1))
          (lamCell natZeroCell (natZeroCell : RawTerm 1))
          (lamCell natZeroCell (natZeroCell : RawTerm 1)) (eitherInlCell boolTrueCell)) out ∧
      IsNatNumeral out :=
  eitherMatchConstComputesToNumeral (Or.inl ⟨boolTrueCell, rfl, by decide⟩)

end FX1Poly.Typed
