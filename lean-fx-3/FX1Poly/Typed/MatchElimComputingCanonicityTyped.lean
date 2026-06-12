import FX1Poly.Typed.MatchElimComputingCanonicity
import FX1Poly.Core.OptionEitherMatchCanonicalComputation
import FX1Poly.Core.IotaHeadStep
import FX1Poly.Core.HeadStep

/-! # FX1Poly/Typed/MatchElimComputingCanonicityTyped
    — TYPED option/either MATCH eliminator-computing canonicity, extending firing-63's bool result to the
    payload-carrying match family via the scrutinee congruence

`BoolElimComputingCanonicity` (`closedBoolElimComputesToValue`) established the eliminator-layer analogue of
value-layer canonicity for `boolElim`: a closed `boolElim` whose scrutinee is typed at `boolType` computes by
`↝*` to `boolTrue`/`boolFalse`.  Bool's eliminator has NO payload — every branch is a value, selected directly
by the ι rule.

The option/either MATCH eliminators DO carry a payload: `optionMatch(m, n, s, some v) ↝ι app s v` and
`eitherMatch(m, l, r, inl v) ↝ι app l v` feed the constructor's stored payload `v` into a *function* branch.  The
general operational `optionMatchComputesToValue` (firing-56) therefore requires the some-branch to produce a
value *from a NORMAL payload* — and a canonical scrutinee reduces to `some inner` with `inner` not necessarily
normal, so that operational lemma does not compose directly with scrutinee canonicity.

This file lands the genuinely-non-vacuous result for **concrete constant bool branches**, where the
payload obstruction dissolves: a constant branch `λ_. boolTrue` β-reduces to `boolTrue` *regardless* of the
payload (`subst0` of a nullary cell ignores its argument), so the eliminator computes past ANY `inner`:

  **`closedOptionMatchIntoBoolComputes` / `closedEitherMatchIntoBoolComputes` (★)** — a closed
  `optionMatch(m, boolTrue, λ_.boolTrue, scrutinee)` / `eitherMatch(m, λ_.boolTrue, λ_.boolFalse, scrutinee)` whose
  *scrutinee* reduces to a constructor value reduces by `↝*` to a canonical bool.

The scrutinee-canonicity HYPOTHESIS (`∃ v, scrutinee ↝* v ∧ v is a constructor`) is the OPERATIONAL
re-shape of the NATIVE-42 retirement: the original statement took a zoo-intro-OR-grown TYPING disjunction
and derived the canonicity via the (retired) `closedOptionCanonicalForms` / `closedEitherCanonicalForms`;
stating the operational content directly frees this file from every typing engine — any typing route that
yields scrutinee canonicity (the union arc once its SR/SN lands; a constructor-headed scrutinee by `refl`)
discharges the hypothesis.  The scrutinee congruence
(`StepStar.optionMatchScrutinee` / `StepStar.eitherMatchScrutinee`) carries that reduction under the match; the
matching ι rule fires to select+apply the branch; and the constant branch β-reduces to the canonical bool
irrespective of the SOME/INL/INR payload.  So the eliminator genuinely COMPUTES — the option/either MATCH
analogue of `closedBoolElimComputesToValue`.

## Honest scope — the deferred general-branch case

The branches here are concrete constant bool-producers, so the eliminator computes for *any* payload.  For a
GENERAL (payload-using) some/inl/inr branch, the payload-normality requirement returns: the eliminator's
computation depends on the stored payload reaching a normal form (which a typed scrutinee's SN supplies, but
threading SN-of-the-payload through the application is the broader eliminator-canonicity integration — CANON-1
/ the combined intro/elim typing judgment).  This file closes the constant-branch corner cleanly; the
general-branch corner stays the named follow-on.

## Zero-axiom verification

The scrutinee-canonicity hypothesis (operational) +
`StepStar.optionMatchScrutinee` / `StepStar.eitherMatchScrutinee` (congruence) + `StepStar.transLast` with
`IotaHeadStep.iotaOptionMatch*` / `IotaHeadStep.iotaEitherMatch*` via `toStep` (ι) + `Step.beta` (constant-branch β).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ Option-match eliminator-computing canonicity (constant bool branches).**  A closed
`optionMatch(scrutinee, boolTrue, λ_.boolTrue)` whose scrutinee reduces to an option constructor value
reduces by `↝*` to `boolTrue`/`boolFalse`.  The scrutinee congruence carries the scrutinee reduction
under the match; the ι rule selects+applies the branch; and the constant some-branch β-reduces to `boolTrue`
regardless of `inner`.  The option-match analogue of `closedBoolElimComputesToValue`.  (NATIVE-42 re-shape:
the hypothesis is the OPERATIONAL scrutinee canonicity the retired zoo statement used to derive.) -/
theorem closedOptionMatchIntoBoolComputes
    {motive : RawTerm 1}
    {scrutinee : RawTerm 0}
    (scrutineeCanonical : ∃ scrutValue : RawTerm 0, StepStar scrutinee scrutValue ∧
      (scrutValue = optionNoneCell ∨ ∃ inner : RawTerm 0, scrutValue = optionSomeCell inner)) :
    ∃ out : RawTerm 0,
      StepStar (optionMatchCell motive boolTrueCell (lamCell boolTrueCell (boolTrueCell : RawTerm 1)) scrutinee) out ∧
      (out = boolTrueCell ∨ out = boolFalseCell) := by
  obtain ⟨scrutValue, scrutReduces, scrutIsOption⟩ := scrutineeCanonical
  rcases scrutIsOption with noneEq | ⟨inner, someEq⟩
  · subst noneEq
    exact ⟨boolTrueCell,
      StepStar.transLast (StepStar.optionMatchScrutinee scrutReduces) IotaHeadStep.iotaOptionMatchNone.toStep,
      Or.inl rfl⟩
  · subst someEq
    have betaStep : Step (appCell (lamCell boolTrueCell (boolTrueCell : RawTerm 1)) inner) boolTrueCell := HeadStep.beta.toStep
    exact ⟨boolTrueCell,
      StepStar.transLast
        (StepStar.transLast (StepStar.optionMatchScrutinee scrutReduces) IotaHeadStep.iotaOptionMatchSome.toStep)
        betaStep,
      Or.inl rfl⟩

/-- **★ Either-match eliminator-computing canonicity (constant bool branches).**  A closed
`eitherMatch(scrutinee, λ_.boolTrue, λ_.boolFalse)` whose scrutinee reduces to an either injection value
reduces by `↝*` to `boolTrue`/`boolFalse`.  The `inl` payload selects+applies the left branch (β to `boolTrue`),
the `inr` payload the right (β to `boolFalse`) — irrespective of the stored payload.  The either-match analogue
of `closedBoolElimComputesToValue`.  (NATIVE-42 re-shape: operational scrutinee-canonicity hypothesis.) -/
theorem closedEitherMatchIntoBoolComputes
    {motive : RawTerm 1}
    {scrutinee : RawTerm 0}
    (scrutineeCanonical : ∃ scrutValue : RawTerm 0, StepStar scrutinee scrutValue ∧
      ((∃ inner : RawTerm 0, scrutValue = eitherInlCell inner) ∨
        (∃ inner : RawTerm 0, scrutValue = eitherInrCell inner))) :
    ∃ out : RawTerm 0,
      StepStar (eitherMatchCell motive (lamCell boolTrueCell (boolTrueCell : RawTerm 1))
        (lamCell boolTrueCell (boolFalseCell : RawTerm 1)) scrutinee) out ∧
      (out = boolTrueCell ∨ out = boolFalseCell) := by
  obtain ⟨scrutValue, scrutReduces, scrutIsEither⟩ := scrutineeCanonical
  rcases scrutIsEither with ⟨inner, inlEq⟩ | ⟨inner, inrEq⟩
  · subst inlEq
    have betaStep : Step (appCell (lamCell boolTrueCell (boolTrueCell : RawTerm 1)) inner) boolTrueCell := HeadStep.beta.toStep
    exact ⟨boolTrueCell,
      StepStar.transLast
        (StepStar.transLast (StepStar.eitherMatchScrutinee scrutReduces) IotaHeadStep.iotaEitherMatchInl.toStep)
        betaStep,
      Or.inl rfl⟩
  · subst inrEq
    have betaStep : Step (appCell (lamCell boolTrueCell (boolFalseCell : RawTerm 1)) inner) boolFalseCell := HeadStep.beta.toStep
    exact ⟨boolFalseCell,
      StepStar.transLast
        (StepStar.transLast (StepStar.eitherMatchScrutinee scrutReduces) IotaHeadStep.iotaEitherMatchInr.toStep)
        betaStep,
      Or.inr rfl⟩

/-- **Non-vacuity smoke (option).**  The concrete `optionMatch(optionNone, boolTrue, λ_.boolTrue)` — a
constructor-headed `None` scrutinee (canonical by `StepStar.refl`) — computes to a canonical bool.
Witnesses `closedOptionMatchIntoBoolComputes` is non-vacuous on a real option value. -/
theorem closedOptionMatchIntoBoolComputes.smoke :
    ∃ out : RawTerm 0,
      StepStar (optionMatchCell (variableCell (⟨0, by decide⟩ : Fin 1)) boolTrueCell
        (lamCell boolTrueCell (boolTrueCell : RawTerm 1)) optionNoneCell) out ∧
      (out = boolTrueCell ∨ out = boolFalseCell) :=
  closedOptionMatchIntoBoolComputes
    ⟨optionNoneCell, StepStar.refl _, Or.inl rfl⟩

/-- **Non-vacuity smoke (either).**  The concrete `eitherMatch(eitherInl(Type@0), λ_.boolTrue, λ_.boolFalse)` —
a constructor-headed `Inl` scrutinee (canonical by `StepStar.refl`) — computes to `boolTrue` (the left
branch).  Witnesses `closedEitherMatchIntoBoolComputes` is non-vacuous on a real either injection. -/
theorem closedEitherMatchIntoBoolComputes.smoke (flag : UniverseFlag) :
    ∃ out : RawTerm 0,
      StepStar (eitherMatchCell (variableCell (⟨0, by decide⟩ : Fin 1))
        (lamCell boolTrueCell (boolTrueCell : RawTerm 1)) (lamCell boolTrueCell (boolFalseCell : RawTerm 1))
        (eitherInlCell (universeCodeCell LevelExpr.lzero flag))) out ∧
      (out = boolTrueCell ∨ out = boolFalseCell) :=
  closedEitherMatchIntoBoolComputes
    ⟨eitherInlCell (universeCodeCell LevelExpr.lzero flag), StepStar.refl _,
      Or.inl ⟨universeCodeCell LevelExpr.lzero flag, rfl⟩⟩

end FX1Poly.Typed
