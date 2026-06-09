import FX1Poly.Typed.ClosedBoolCanonicity
import FX1Poly.Typed.HasTypeDescBoolElim
import FX1Poly.Core.BoolElimCanonicalComputation

/-! # FX1Poly/Typed/BoolElimComputingCanonicity
    — genuinely-NON-VACUOUS eliminator-computing bool canonicity, via the COMPONENT-typing route

`BoolElimArbitrarySubjectCanonicity` recorded the honest limitation: the standalone bool-elim judgment
`HasTypeDescBoolElim` requires its branches to be GROWN-typed, so `boolElim b true false : Bool` (branches the
data VALUES `true`/`false`) is NOT typeable by it — the eliminator is VACUOUS at `boolCode`, and "eliminator
computes to the selected value" was the deferred follow-on (needing a combined intro/elim engine, CANON-1 /
GTL table-residency).

This file lands the genuinely-non-vacuous result WITHOUT building that combined engine, by stating canonicity
over the eliminator's COMPONENT typings rather than over a single unified `boolElim : boolType` derivation:

  **`closedBoolElimComputesToValue` (★)** — a closed `boolElim(scrutinee, thenBranch, elseBranch)` whose
  *scrutinee* is typed at `boolType` by any of the three value/formation engines AND whose *branches* are
  data-VALUE-typed at `boolType` reduces by `↝*` to `boolTrue`/`boolFalse`.

The scrutinee, being a closed bool, reduces to `boolTrue`/`boolFalse` (`closedBoolCanonicalForms`, the
syntactic route); the scrutinee congruence (`StepStar.boolElimScrutinee`) carries that reduction under the
`boolElim`; the matching ι rule (`Step.iotaBoolTrue`/`Step.iotaBoolFalse`) fires to select the branch; and the
selected branch, being data-value-typed, IS `boolTrue`/`boolFalse` (`standaloneBoolCanonicalForms`).  So the
eliminator genuinely COMPUTES to a canonical bool — non-vacuously (the scrutinee may be any closed bool, the
branches are real data values).  This is the eliminator-layer analogue of the value-layer
`closedBoolCanonicalForms`; the smoke witnesses non-vacuity on a concrete `boolElim(true, true, false)`.

The component-typing framing is exactly what canonicity needs operationally — it does not require a
HasTypeDescBoolElim derivation with value branches (which is the vacuous one), only that the scrutinee and the
branches are independently well-typed at `boolType`.  Folding this into a single combined intro/elim typing
judgment (so `boolElim … : Bool` is a first-class derivation) remains the CANON-1 follow-on.

## Zero-axiom verification

`closedBoolCanonicalForms` (scrutinee) + `StepStar.boolElimScrutinee` (congruence) + `StepStar.transLast` with
`Step.iotaBoolTrue`/`Step.iotaBoolFalse` (ι) + `standaloneBoolCanonicalForms` (branch value).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ Genuinely-non-vacuous eliminator-computing bool canonicity (component-typing route).**  A closed
`boolElim(scrutinee, thenBranch, elseBranch)` whose scrutinee is typed at `boolType` (by the data-intro,
base-type, or grown engine) and whose branches are data-VALUE-typed at `boolType` reduces by `↝*` to
`boolTrue`/`boolFalse`.  The eliminator COMPUTES: the scrutinee reduces to a value (`closedBoolCanonicalForms`),
the scrutinee congruence carries it under the `boolElim`, the ι rule selects the branch, and the branch IS a
value (`standaloneBoolCanonicalForms`).  The eliminator-layer analogue of `closedBoolCanonicalForms`. -/
theorem closedBoolElimComputesToValue {profile : PolyProfile}
    {scrutinee thenBranch elseBranch : RawTerm 0}
    (scrutineeTyped :
      HasTypeDescDataIntro profile (TypingContext.empty : TypingContext profile 0) scrutinee boolTypeCell ∨
      HasTypeDescBaseType profile (TypingContext.empty : TypingContext profile 0) scrutinee boolTypeCell ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) scrutinee boolTypeCell)
    (thenTyped : HasTypeDescDataIntro profile (TypingContext.empty : TypingContext profile 0)
      thenBranch boolTypeCell)
    (elseTyped : HasTypeDescDataIntro profile (TypingContext.empty : TypingContext profile 0)
      elseBranch boolTypeCell) :
    ∃ value : RawTerm 0, StepStar (boolElimCell scrutinee thenBranch elseBranch) value ∧
      (value = boolTrueCell ∨ value = boolFalseCell) := by
  obtain ⟨scrutValue, scrutReduces, scrutIsBool⟩ := closedBoolCanonicalForms scrutineeTyped
  cases scrutIsBool with
  | inl scrutIsTrue =>
      subst scrutIsTrue
      exact ⟨thenBranch,
        StepStar.transLast (StepStar.boolElimScrutinee scrutReduces) Step.iotaBoolTrue,
        standaloneBoolCanonicalForms (Or.inl thenTyped)⟩
  | inr scrutIsFalse =>
      subst scrutIsFalse
      exact ⟨elseBranch,
        StepStar.transLast (StepStar.boolElimScrutinee scrutReduces) Step.iotaBoolFalse,
        standaloneBoolCanonicalForms (Or.inl elseTyped)⟩

/-- **Non-vacuity smoke.**  The concrete `boolElim(boolTrue, boolTrue, boolFalse)` — a value scrutinee and two
data-VALUE branches, none grown-typed — computes to a canonical bool.  Witnesses
`closedBoolElimComputesToValue` is non-vacuous on exactly the eliminator the vacuous standalone judgment
`HasTypeDescBoolElim` cannot type (data-value branches). -/
theorem closedBoolElimComputesToValue.smoke {profile : PolyProfile} :
    ∃ value : RawTerm 0,
      StepStar (boolElimCell boolTrueCell boolTrueCell boolFalseCell) value ∧
      (value = boolTrueCell ∨ value = boolFalseCell) :=
  closedBoolElimComputesToValue
    (Or.inl (HasTypeDescDataIntro.boolTrueTyped (TypingContext.empty : TypingContext profile 0)))
    (HasTypeDescDataIntro.boolTrueTyped (TypingContext.empty : TypingContext profile 0))
    (HasTypeDescDataIntro.boolFalseTyped (TypingContext.empty : TypingContext profile 0))

end FX1Poly.Typed
