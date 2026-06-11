import FX1Poly.Typed.ClosedDataCanonicity
import FX1Poly.Typed.MatchElimComputingCanonicity
import FX1Poly.Typed.HasTypeDescOptionIntro
import FX1Poly.Typed.HasTypeDescEitherIntro
import FX1Poly.Core.OptionEitherMatchCanonicalComputation

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
value *from a NORMAL payload* — and a typed scrutinee reduces to `some inner` with `inner` not necessarily
normal, so that operational lemma does not compose directly with `closedOptionCanonicalForms`.

This file lands the genuinely-non-vacuous TYPED result for **concrete constant bool branches**, where the
payload obstruction dissolves: a constant branch `λ_. boolTrue` β-reduces to `boolTrue` *regardless* of the
payload (`subst0` of a nullary cell ignores its argument), so the eliminator computes past ANY `inner`:

  **`closedOptionMatchIntoBoolComputes` / `closedEitherMatchIntoBoolComputes` (★)** — a closed
  `optionMatch(m, boolTrue, λ_.boolTrue, scrutinee)` / `eitherMatch(m, λ_.boolTrue, λ_.boolFalse, scrutinee)` whose
  *scrutinee* is typed at the option/either type (by the data-intro engine or vacuously by the grown engine)
  reduces by `↝*` to a canonical bool.

The scrutinee, being a closed option/either, reduces to a constructor value (`closedOptionCanonicalForms` /
`closedEitherCanonicalForms`, the syntactic route); the scrutinee congruence
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

`closedOptionCanonicalForms` / `closedEitherCanonicalForms` (scrutinee, syntactic route) +
`StepStar.optionMatchScrutinee` / `StepStar.eitherMatchScrutinee` (congruence) + `StepStar.transLast` with
`Step.iotaOptionMatch*` / `Step.iotaEitherMatch*` (ι) + `Step.beta` (constant-branch β).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ TYPED option-match eliminator-computing canonicity (constant bool branches).**  A closed
`optionMatch(scrutinee, boolTrue, λ_.boolTrue)` whose scrutinee is typed at `option(elementType)` (by the
data-intro engine, or vacuously by the grown engine) reduces by `↝*` to `boolTrue`/`boolFalse`.  The scrutinee
reduces to `optionNone`/`optionSome inner` (`closedOptionCanonicalForms`); the scrutinee congruence carries it
under the match; the ι rule selects+applies the branch; and the constant some-branch β-reduces to `boolTrue`
regardless of `inner`.  The option-match analogue of `closedBoolElimComputesToValue`. -/
theorem closedOptionMatchIntoBoolComputes {profile : PolyProfile}
    {motive : RawTerm 1}
    {scrutinee elementType : RawTerm 0}
    (scrutineeTyped :
      HasTypeDescOptionIntro profile (TypingContext.empty : TypingContext profile 0) scrutinee
        (optionTypeCell elementType) ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) scrutinee
        (optionTypeCell elementType)) :
    ∃ out : RawTerm 0,
      StepStar (optionMatchCell motive boolTrueCell (lamCell boolTrueCell (boolTrueCell : RawTerm 1)) scrutinee) out ∧
      (out = boolTrueCell ∨ out = boolFalseCell) := by
  obtain ⟨scrutValue, scrutReduces, scrutIsOption⟩ := closedOptionCanonicalForms scrutineeTyped
  rcases scrutIsOption with noneEq | ⟨inner, someEq⟩
  · subst noneEq
    exact ⟨boolTrueCell,
      StepStar.transLast (StepStar.optionMatchScrutinee scrutReduces) Step.iotaOptionMatchNone,
      Or.inl rfl⟩
  · subst someEq
    have betaStep : Step (appCell (lamCell boolTrueCell (boolTrueCell : RawTerm 1)) inner) boolTrueCell := Step.beta
    exact ⟨boolTrueCell,
      StepStar.transLast
        (StepStar.transLast (StepStar.optionMatchScrutinee scrutReduces) Step.iotaOptionMatchSome)
        betaStep,
      Or.inl rfl⟩

/-- **★ TYPED either-match eliminator-computing canonicity (constant bool branches).**  A closed
`eitherMatch(scrutinee, λ_.boolTrue, λ_.boolFalse)` whose scrutinee is typed at `either(leftType, rightType)`
reduces by `↝*` to `boolTrue`/`boolFalse`.  The `inl` payload selects+applies the left branch (β to `boolTrue`),
the `inr` payload the right (β to `boolFalse`) — irrespective of the stored payload.  The either-match analogue
of `closedBoolElimComputesToValue`. -/
theorem closedEitherMatchIntoBoolComputes {profile : PolyProfile}
    {motive : RawTerm 1}
    {scrutinee leftType rightType : RawTerm 0}
    (scrutineeTyped :
      HasTypeDescEitherIntro profile (TypingContext.empty : TypingContext profile 0) scrutinee
        (eitherTypeCell leftType rightType) ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) scrutinee
        (eitherTypeCell leftType rightType)) :
    ∃ out : RawTerm 0,
      StepStar (eitherMatchCell motive (lamCell boolTrueCell (boolTrueCell : RawTerm 1))
        (lamCell boolTrueCell (boolFalseCell : RawTerm 1)) scrutinee) out ∧
      (out = boolTrueCell ∨ out = boolFalseCell) := by
  obtain ⟨scrutValue, scrutReduces, scrutIsEither⟩ := closedEitherCanonicalForms scrutineeTyped
  rcases scrutIsEither with ⟨inner, inlEq⟩ | ⟨inner, inrEq⟩
  · subst inlEq
    have betaStep : Step (appCell (lamCell boolTrueCell (boolTrueCell : RawTerm 1)) inner) boolTrueCell := Step.beta
    exact ⟨boolTrueCell,
      StepStar.transLast
        (StepStar.transLast (StepStar.eitherMatchScrutinee scrutReduces) Step.iotaEitherMatchInl)
        betaStep,
      Or.inl rfl⟩
  · subst inrEq
    have betaStep : Step (appCell (lamCell boolTrueCell (boolFalseCell : RawTerm 1)) inner) boolFalseCell := Step.beta
    exact ⟨boolFalseCell,
      StepStar.transLast
        (StepStar.transLast (StepStar.eitherMatchScrutinee scrutReduces) Step.iotaEitherMatchInr)
        betaStep,
      Or.inr rfl⟩

/-- **Non-vacuity smoke (option).**  The concrete `optionMatch(optionNone, boolTrue, λ_.boolTrue)` — a typed
`None` scrutinee — computes to a canonical bool.  Witnesses `closedOptionMatchIntoBoolComputes` is non-vacuous
on a real typed option (`optionNone : option(Type@0)`). -/
theorem closedOptionMatchIntoBoolComputes.smoke {profile : PolyProfile} (flag : UniverseFlag) :
    ∃ out : RawTerm 0,
      StepStar (optionMatchCell (variableCell (⟨0, by decide⟩ : Fin 1)) boolTrueCell
        (lamCell boolTrueCell (boolTrueCell : RawTerm 1)) optionNoneCell) out ∧
      (out = boolTrueCell ∨ out = boolFalseCell) :=
  closedOptionMatchIntoBoolComputes (profile := profile)
    (Or.inl (HasTypeDescOptionIntro.optionNoneOfUniverseCodeTyped flag))

/-- **Non-vacuity smoke (either).**  The concrete `eitherMatch(eitherInl(Type@0), λ_.boolTrue, λ_.boolFalse)` —
a typed `Inl` scrutinee — computes to `boolTrue` (the left branch).  Witnesses
`closedEitherMatchIntoBoolComputes` is non-vacuous on a real typed either. -/
theorem closedEitherMatchIntoBoolComputes.smoke {profile : PolyProfile} (flag : UniverseFlag) :
    ∃ out : RawTerm 0,
      StepStar (eitherMatchCell (variableCell (⟨0, by decide⟩ : Fin 1))
        (lamCell boolTrueCell (boolTrueCell : RawTerm 1)) (lamCell boolTrueCell (boolFalseCell : RawTerm 1))
        (eitherInlCell (universeCodeCell LevelExpr.lzero flag))) out ∧
      (out = boolTrueCell ∨ out = boolFalseCell) :=
  closedEitherMatchIntoBoolComputes (profile := profile)
    (Or.inl (HasTypeDescEitherIntro.eitherInlOfUniverseCodeTyped flag))

end FX1Poly.Typed
