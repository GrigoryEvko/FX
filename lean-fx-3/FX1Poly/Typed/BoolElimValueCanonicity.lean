import FX1Poly.Typed.HasTypeDescBoolElim
import FX1Poly.Typed.CombinedBoolCanonicalForms

/-! # FX1Poly/Typed/BoolElimValueCanonicity
    — the FIRST genuinely-NON-VACUOUS eliminator-computing canonicity (the eliminator COMPUTES to a value)

The four prior canonicity firings (45-48) all found the eliminator engine VACUOUS at a data type: the existing
`HasTypeDescBoolElim` (#1070) types its branches with the GROWN engine (`HasTypeDescPi`), which has no closed
inhabitant of `boolCode`, so `boolElim b true false : Bool` — the textbook non-dependent elimination INTO Bool —
is NOT typeable by it.  Eliminator-computing canonicity AT a data type was therefore vacuous.

This file closes that gap with the genuinely-non-vacuous case: a standalone bool eliminator whose branches are
DATA-VALUE typed (the data-intro engine at `boolCode`), so `boolElim b true false : Bool` IS typeable, and whose
closed instances COMPUTE by a single ι-step to a bool value.

  * **`HasTypeDescBoolElimValue`** — the bool eliminator INTO Bool (constant Bool motive): scrutinee and both
    branches data-intro-typed at `boolCode`.  Standalone (NOT mutual / NOT an arm), the data-value-branch twin of
    `HasTypeDescBoolElim`.
  * **`HasTypeDescBoolElimValue.smoke`** — non-vacuous typing: `boolElim(boolTrue, boolTrue, boolFalse) : Bool`.
  * **`boolElimValueTrueIotaTyped` / `boolElimValueFalseIotaTyped`** — typed ι-computation (the value case): the
    eliminator on `boolTrue`/`boolFalse` ι-reduces to the then/else branch, which stays data-intro-typed at
    `boolCode` (SR for the eliminator's computation step).
  * **`boolElimValueCanonicity` (★)** — the headline: a closed `boolElim b t e : Bool` COMPUTES by `↝*` (one
    ι-step) to a bool value.  The scrutinee is `boolTrue`/`boolFalse` (`standaloneBoolCanonicalForms`), so the
    eliminator FIRES to the selected branch, itself a bool value.  The FIRST eliminator-computing canonicity where
    the eliminator genuinely COMPUTES — not a vacuity.

## What this is and what remains

This is the concrete demonstration that eliminator-computing canonicity is achievable at a data type: the
eliminator term reduces to a constructor.  It does NOT need SN/SR over a combined engine — the branches are
already values (data-intro, hence normal), so a single ι-step lands the value.  The PRINCIPLED unification (one
combined intro/elim engine where the branches are typed by the unified "closed term at T" judgment, so a general
eliminator with arbitrary nested computation in its branches normalizes) remains the deferred GTL table-residency
work (#832/#1138); this file proves the canonicity STORY works for the eliminator-into-data case with a clean
standalone judgment.

## Zero-axiom verification

A single-arm positive inductive; the smoke is a direct construction; the typed-ι theorems are
`Step.iotaBoolTrue`/`iotaBoolFalse` paired with the branch typing; the canonicity is `cases` + two
`standaloneBoolCanonicalForms` + `StepStar.single`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The bool eliminator INTO Bool** (constant Bool motive): `boolElim(scrutinee, thenBranch, elseBranch) : Bool`
when the scrutinee and both branches are data-intro values at `boolCode`.  Standalone (NOT mutual with / NOT an
arm of any engine), the data-value-branch twin of `HasTypeDescBoolElim` (whose branches are grown-typed).  Types
`boolElim b true false : Bool`, which the grown-branch engine cannot. -/
inductive HasTypeDescBoolElimValue (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  | boolElimValueIntro {scope : Nat} (context : TypingContext profile scope)
      (scrutinee thenBranch elseBranch : RawTerm scope)
      (scrutineeTyped : HasTypeDescDataIntro profile context scrutinee boolTypeCell)
      (thenTyped : HasTypeDescDataIntro profile context thenBranch boolTypeCell)
      (elseTyped : HasTypeDescDataIntro profile context elseBranch boolTypeCell) :
      HasTypeDescBoolElimValue profile context
        (boolElimCell scrutinee thenBranch elseBranch) boolTypeCell

/-- **Non-vacuous typing smoke**: `boolElim(boolTrue, boolTrue, boolFalse) : Bool` — the first eliminator the
kernel types INTO a data type with data-value branches. -/
theorem HasTypeDescBoolElimValue.smoke {profile : PolyProfile} :
    HasTypeDescBoolElimValue profile (TypingContext.empty : TypingContext profile 0)
      (boolElimCell boolTrueCell boolTrueCell boolFalseCell) boolTypeCell :=
  HasTypeDescBoolElimValue.boolElimValueIntro TypingContext.empty boolTrueCell boolTrueCell boolFalseCell
    (HasTypeDescDataIntro.boolTrueTyped TypingContext.empty)
    (HasTypeDescDataIntro.boolTrueTyped TypingContext.empty)
    (HasTypeDescDataIntro.boolFalseTyped TypingContext.empty)

/-- **Typed ι-computation (true case)**: `boolElim(boolTrue, t, e)` ι-reduces to the then-branch `t`
(`Step.iotaBoolTrue`), and `t` stays data-intro-typed at `boolCode` — SR for the eliminator's value-case
computation step. -/
theorem boolElimValueTrueIotaTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (thenBranch elseBranch : RawTerm scope)
    (thenTyped : HasTypeDescDataIntro profile context thenBranch boolTypeCell) :
    Step (boolElimCell boolTrueCell thenBranch elseBranch) thenBranch ∧
    HasTypeDescDataIntro profile context thenBranch boolTypeCell :=
  ⟨Step.iotaBoolTrue, thenTyped⟩

/-- **Typed ι-computation (false case)**: the `boolFalse` mirror — `boolElim(boolFalse, t, e)` ι-reduces to the
else-branch `e` (`Step.iotaBoolFalse`), typed at `boolCode`. -/
theorem boolElimValueFalseIotaTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (thenBranch elseBranch : RawTerm scope)
    (elseTyped : HasTypeDescDataIntro profile context elseBranch boolTypeCell) :
    Step (boolElimCell boolFalseCell thenBranch elseBranch) elseBranch ∧
    HasTypeDescDataIntro profile context elseBranch boolTypeCell :=
  ⟨Step.iotaBoolFalse, elseTyped⟩

/-- **★ NON-VACUOUS eliminator-computing canonicity.**  A closed `boolElim b t e : Bool` (data-value branches)
COMPUTES by a single ι-step to a bool VALUE.  The scrutinee is `boolTrue`/`boolFalse`
(`standaloneBoolCanonicalForms`), so the eliminator FIRES (`Step.iotaBoolTrue`/`iotaBoolFalse`) to the selected
branch, itself a bool value (the branch is data-intro-typed at `boolCode`).  The FIRST canonicity in which the
eliminator genuinely computes — the eliminator-into-data case the four prior firings found vacuous for the
grown-branch engine. -/
theorem boolElimValueCanonicity {profile : PolyProfile} {subject : RawTerm 0}
    (derivation : HasTypeDescBoolElimValue profile (TypingContext.empty : TypingContext profile 0)
      subject boolTypeCell) :
    ∃ value : RawTerm 0, StepStar subject value ∧ (value = boolTrueCell ∨ value = boolFalseCell) := by
  cases derivation with
  | boolElimValueIntro scrutinee thenBranch elseBranch scrutineeTyped thenTyped elseTyped =>
      rcases standaloneBoolCanonicalForms (Or.inl scrutineeTyped) with scrutEq | scrutEq
      · subst scrutEq
        rcases standaloneBoolCanonicalForms (Or.inl thenTyped) with branchEq | branchEq
        · subst branchEq; exact ⟨boolTrueCell, StepStar.single Step.iotaBoolTrue, Or.inl rfl⟩
        · subst branchEq; exact ⟨boolFalseCell, StepStar.single Step.iotaBoolTrue, Or.inr rfl⟩
      · subst scrutEq
        rcases standaloneBoolCanonicalForms (Or.inl elseTyped) with branchEq | branchEq
        · subst branchEq; exact ⟨boolTrueCell, StepStar.single Step.iotaBoolFalse, Or.inl rfl⟩
        · subst branchEq; exact ⟨boolFalseCell, StepStar.single Step.iotaBoolFalse, Or.inr rfl⟩

end FX1Poly.Typed
