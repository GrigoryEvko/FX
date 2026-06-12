import FX1Poly.Core.OptionCanonicalFormsCandidate
import FX1Poly.Core.EitherCanonicalFormsCandidate
import FX1Poly.Core.WeakHeadStepCommute
import FX1Poly.Core.IotaHeadStep

/-! # FX1Poly/Core/OptionEitherMatchCanonicalComputation
    — closed `optionMatch` / `eitherMatch` on a canonical scrutinee COMPUTE to a branch (the match computation core)

`OptionCanonicalFormsCandidate.lean` / `EitherCanonicalFormsCandidate.lean` ship option/sum data canonicity: a
closed member of the option / either candidate reduces to a `none` / `some` / `inl` / `inr` constructor.  This
file pushes that into the MATCH eliminators: a closed `optionMatch` / `eitherMatch` on a canonical scrutinee
reduces to the corresponding branch.  These are the NON-RECURSIVE data eliminators (option / either are
non-recursive types), so — like `boolElim` (branch selection), `fst`/`snd` (projection), and `idJ`/`idStrictRec`
(base selection) — their ι fires once with NO recursive sub-term reappearing: it selects the `none`-branch or
APPLIES the `some` / `inl` / `inr` branch to the wrapped payload (`app branch payload`).  Completing these closes
the canonical-computation track for ALL non-recursive eliminators; only the recursive `natElim`/`natRec`/
`listElim` (whose ι reappears the eliminator on a smaller scrutinee) remain, and those need full Tait
reducibility.  Fundamental-free.

* `StepStar.optionMatchScrutinee` / `StepStar.eitherMatchScrutinee` — the scrutinee-position (head-child) chain
  congruences (`StepStar.congAt` + `Step.cong … (StepChildren.here …)`, as for `boolElim`).
* `optionMatchCanonicalScrutineeReduces` — closed `optionMatch` on a canonical option scrutinee reduces to the
  `none`-branch (scrutinee `→* none`) or to `app someBranch payload` (scrutinee `→* some payload`).
* `eitherMatchCanonicalScrutineeReduces` — closed `eitherMatch` on a canonical either scrutinee reduces to
  `app leftBranch payload` (scrutinee `→* inl payload`) or `app rightBranch payload` (scrutinee `→* inr payload`).

## Zero-axiom verification

`StepStar.congAt` (chain induction), `optionClosedReducesToValue` / `eitherClosedReducesToValue` (data canonicity
via the candidates), `Step.cong` / `StepChildren.here` (the scrutinee congruence step), and the
`IotaHeadStep.iotaOptionMatchNone.toStep` / `iotaOptionMatchSome` / `iotaEitherMatchInl` / `iotaEitherMatchInr` ι constructors,
chained by `StepStar.transLast`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- The application cell `app function argument` — the shape an `optionMatch`/`eitherMatch` ι produces when it
applies a branch to the wrapped payload. -/
private abbrev applyCell {scope : Nat} (function argument : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_app () (.childCons function (.childCons argument .childNil))

/-- The Phase-Z `optionMatch` cell over its four children — spine `(motive, noneBranch, someBranch, scrutinee)`
with the motive a term under one binder (`RawTerm (scope + 1)`) and the scrutinee LAST. -/
private abbrev optionMatchCellOn {scope : Nat} (motive : RawTerm (scope + 1))
    (scrutinee noneBranch someBranch : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_optionMatch ()
    (.childCons motive
      (.childCons noneBranch
        (.childCons someBranch
          (.childCons scrutinee .childNil))))

/-- The Phase-Z `eitherMatch` cell over its four children — spine `(motive, leftBranch, rightBranch, scrutinee)`
with the motive a term under one binder (`RawTerm (scope + 1)`) and the scrutinee LAST. -/
private abbrev eitherMatchCellOn {scope : Nat} (motive : RawTerm (scope + 1))
    (scrutinee leftBranch rightBranch : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_eitherMatch ()
    (.childCons motive
      (.childCons leftBranch
        (.childCons rightBranch
          (.childCons scrutinee .childNil))))

/-- **Scrutinee-position chain congruence for `optionMatch`.**  A reduction chain in the scrutinee lifts to the
whole `optionMatch` cell (motive + branches fixed), via `StepStar.congAt` + `Step.cong …` drilled by a
`there`-chain to the scrutinee child (the LAST child of the 4-child spine, past the motive + both branches). -/
theorem StepStar.optionMatchScrutinee {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {scrutinee scrutineeReduct noneBranch someBranch : RawTerm scope}
    (scrutineeChain : StepStar scrutinee scrutineeReduct) :
    StepStar (optionMatchCellOn motive scrutinee noneBranch someBranch)
      (optionMatchCellOn motive scrutineeReduct noneBranch someBranch) :=
  StepStar.congAt
    (fun hole => optionMatchCellOn motive hole noneBranch someBranch)
    (fun stepInScrutinee =>
      Step.cong .gen_optionMatch ()
        (StepChildren.there _
          (StepChildren.there _
            (StepChildren.there _
              (StepChildren.here _ stepInScrutinee)))))
    scrutineeChain

/-- **Scrutinee-position chain congruence for `eitherMatch`.**  Symmetric to `StepStar.optionMatchScrutinee`. -/
theorem StepStar.eitherMatchScrutinee {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {scrutinee scrutineeReduct leftBranch rightBranch : RawTerm scope}
    (scrutineeChain : StepStar scrutinee scrutineeReduct) :
    StepStar (eitherMatchCellOn motive scrutinee leftBranch rightBranch)
      (eitherMatchCellOn motive scrutineeReduct leftBranch rightBranch) :=
  StepStar.congAt
    (fun hole => eitherMatchCellOn motive hole leftBranch rightBranch)
    (fun stepInScrutinee =>
      Step.cong .gen_eitherMatch ()
        (StepChildren.there _
          (StepChildren.there _
            (StepChildren.there _
              (StepChildren.here _ stepInScrutinee)))))
    scrutineeChain

/-- **Closed `optionMatch` on a canonical scrutinee computes to a branch.**  The non-recursive-data-eliminator
analog of closed-bool elimination canonicity: a closed `optionMatch` whose scrutinee is a member of the option
candidate `StepStar`-reduces to its none-branch (if the scrutinee evaluates to `none`) or to `someBranch`
applied to the wrapped payload (if it evaluates to `some payload`).  The scrutinee reduces to a `none`/`some`
value (`optionClosedReducesToValue`), `StepStar.optionMatchScrutinee` carries that under the `optionMatch`, and
`IotaHeadStep.iotaOptionMatchNone.toStep` / `IotaHeadStep.iotaOptionMatchSome.toStep` fire to select the branch.  Fundamental-free — no fundamental
theorem. -/
theorem optionMatchCanonicalScrutineeReduces {motive : RawTerm 1}
    {scrutinee noneBranch someBranch : RawTerm 0}
    (scrutineeMember : CanonicalFormsPredicate isOptionValue scrutinee) :
    StepStar (optionMatchCellOn motive scrutinee noneBranch someBranch) noneBranch ∨
      ∃ payload : RawTerm 0,
        StepStar scrutinee (optionSomeCell payload) ∧
          StepStar (optionMatchCellOn motive scrutinee noneBranch someBranch)
            (applyCell someBranch payload) := by
  obtain ⟨value, scrutineeReducesToValue, valueIsOption⟩ := optionClosedReducesToValue scrutineeMember
  cases valueIsOption with
  | inl valueIsNone =>
      subst valueIsNone
      exact Or.inl
        (StepStar.transLast (StepStar.optionMatchScrutinee scrutineeReducesToValue) IotaHeadStep.iotaOptionMatchNone.toStep)
  | inr valueIsSome =>
      obtain ⟨payload, valueIsSomePayload, _payloadNormal⟩ := valueIsSome
      subst valueIsSomePayload
      exact Or.inr ⟨payload, scrutineeReducesToValue,
        StepStar.transLast (StepStar.optionMatchScrutinee scrutineeReducesToValue) IotaHeadStep.iotaOptionMatchSome.toStep⟩

/-- **Closed `eitherMatch` on a canonical scrutinee computes to a branch.**  Symmetric to
`optionMatchCanonicalScrutineeReduces`: a closed `eitherMatch` whose scrutinee is a member of the either
candidate `StepStar`-reduces to `leftBranch` applied to the wrapped payload (if the scrutinee evaluates to
`inl payload`) or to `rightBranch` applied to the wrapped payload (if it evaluates to `inr payload`), via
`eitherClosedReducesToValue` + `StepStar.eitherMatchScrutinee` + `IotaHeadStep.iotaEitherMatchInl.toStep` /
`IotaHeadStep.iotaEitherMatchInr.toStep`.  Fundamental-free. -/
theorem eitherMatchCanonicalScrutineeReduces {motive : RawTerm 1}
    {scrutinee leftBranch rightBranch : RawTerm 0}
    (scrutineeMember : CanonicalFormsPredicate isEitherValue scrutinee) :
    (∃ payload : RawTerm 0,
        StepStar scrutinee (eitherInlCell payload) ∧
          StepStar (eitherMatchCellOn motive scrutinee leftBranch rightBranch)
            (applyCell leftBranch payload)) ∨
      ∃ payload : RawTerm 0,
        StepStar scrutinee (eitherInrCell payload) ∧
          StepStar (eitherMatchCellOn motive scrutinee leftBranch rightBranch)
            (applyCell rightBranch payload) := by
  obtain ⟨value, scrutineeReducesToValue, valueIsEither⟩ := eitherClosedReducesToValue scrutineeMember
  cases valueIsEither with
  | inl valueIsInl =>
      obtain ⟨payload, valueIsInlPayload, _payloadNormal⟩ := valueIsInl
      subst valueIsInlPayload
      exact Or.inl ⟨payload, scrutineeReducesToValue,
        StepStar.transLast (StepStar.eitherMatchScrutinee scrutineeReducesToValue) IotaHeadStep.iotaEitherMatchInl.toStep⟩
  | inr valueIsInr =>
      obtain ⟨payload, valueIsInrPayload, _payloadNormal⟩ := valueIsInr
      subst valueIsInrPayload
      exact Or.inr ⟨payload, scrutineeReducesToValue,
        StepStar.transLast (StepStar.eitherMatchScrutinee scrutineeReducesToValue) IotaHeadStep.iotaEitherMatchInr.toStep⟩

end FX1Poly.Core
