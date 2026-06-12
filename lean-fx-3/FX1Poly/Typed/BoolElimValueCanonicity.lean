import FX1Poly.Typed.ClosedBoolCanonicity
import FX1Poly.Core.IotaHeadStep

/-! # FX1Poly/Typed/BoolElimValueCanonicity
    — the FIRST genuinely-NON-VACUOUS eliminator-computing canonicity (the eliminator COMPUTES to a value)

The four prior canonicity firings (45-48) all found the eliminator engine VACUOUS at a data type: the existing
`HasTypeDescBoolElim` (#1070) types its branches with the GROWN engine (`HasTypeDescPi`), which has no closed
inhabitant of `boolCode`, so `boolElim b true false : Bool` — the textbook non-dependent elimination INTO Bool —
is NOT typeable by it.  Eliminator-computing canonicity AT a data type was therefore vacuous.

This file closes that gap with the genuinely-non-vacuous case: a standalone bool eliminator whose branches are
DATA-VALUE typed (the union's `dataIntroNullary` row at `boolCode`), so `boolElim b true false : Bool` IS typeable, and whose
closed instances COMPUTE by a single ι-step to a bool value.

  * **`HasTypeDescBoolElimValue`** — the bool eliminator INTO Bool (constant Bool motive): scrutinee and both
    branches standalone-value-typed at `boolCode` (`boolStandaloneRowTyped`).  Standalone (NOT mutual / NOT an
    arm), the data-value-branch twin of `HasTypeDescBoolElim`.
  * **`HasTypeDescBoolElimValue.smoke`** — non-vacuous typing: `boolElim(boolTrue, boolTrue, boolFalse) : Bool`.
  * **`boolElimValueTrueIotaTyped` / `boolElimValueFalseIotaTyped`** — typed ι-computation (the value case): the
    eliminator on `boolTrue`/`boolFalse` ι-reduces to the then/else branch, which stays standalone-value-typed at
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
`IotaHeadStep.iotaBoolTrue.toStep`/`iotaBoolFalse` paired with the branch typing; the canonicity is `cases` + two
`standaloneBoolCanonicalForms` + `StepStar.single`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The bool eliminator INTO Bool** (constant Bool motive): `boolElim(motive, scrutinee, thenBranch,
elseBranch) : Bool` when the scrutinee and both branches are standalone-row values at `boolCode`.  Standalone (NOT
mutual with / NOT an arm of any engine), the data-value-branch twin of `HasTypeDescBoolElim` (whose branches are
grown-typed).  Types `boolElim b true false : Bool`, which the grown-branch engine cannot.  The stored motive
child (Phase-Z shape) is carried structurally with no premise (the constant Bool motive, e.g. `boolTypeCell`). -/
inductive HasTypeDescBoolElimValue (profile : PolyProfile) :
    TypingContext profile 0 → RawTerm 0 → RawTerm 0 → Prop where
  | boolElimValueIntro (context : TypingContext profile 0)
      (motive : RawTerm 1) (scrutinee thenBranch elseBranch : RawTerm 0)
      (scrutineeTyped : boolStandaloneRowTyped scrutinee)
      (thenTyped : boolStandaloneRowTyped thenBranch)
      (elseTyped : boolStandaloneRowTyped elseBranch) :
      HasTypeDescBoolElimValue profile context
        (boolElimCell motive scrutinee thenBranch elseBranch) boolTypeCell

/-- `boolTrue` inhabits the standalone value layer at `boolTypeCell` — the union's `dataIntroNullary` row witness
for `gen_boolTrue`. -/
theorem boolTrueStandaloneRowTyped : boolStandaloneRowTyped (boolTrueCell : RawTerm 0) :=
  Or.inl ⟨.gen_boolTrue, (), .childNil, { outputTypeCode := fun _ => boolTypeCell }, rfl, rfl, rfl⟩

/-- `boolFalse` inhabits the standalone value layer at `boolTypeCell` — the `gen_boolFalse` row witness. -/
theorem boolFalseStandaloneRowTyped : boolStandaloneRowTyped (boolFalseCell : RawTerm 0) :=
  Or.inl ⟨.gen_boolFalse, (), .childNil, { outputTypeCode := fun _ => boolTypeCell }, rfl, rfl, rfl⟩

/-- **Non-vacuous typing smoke**: `boolElim(boolTrue, boolTrue, boolFalse) : Bool` — the first eliminator the
kernel types INTO a data type with data-value branches. -/
theorem HasTypeDescBoolElimValue.smoke {profile : PolyProfile} :
    HasTypeDescBoolElimValue profile (TypingContext.empty : TypingContext profile 0)
      (boolElimCell boolTypeCell boolTrueCell boolTrueCell boolFalseCell) boolTypeCell :=
  HasTypeDescBoolElimValue.boolElimValueIntro TypingContext.empty boolTypeCell
    boolTrueCell boolTrueCell boolFalseCell
    boolTrueStandaloneRowTyped boolTrueStandaloneRowTyped boolFalseStandaloneRowTyped

/-- **Typed ι-computation (true case)**: `boolElim(boolTrue, t, e)` ι-reduces to the then-branch `t`
(`IotaHeadStep.iotaBoolTrue.toStep`), and `t` stays standalone-value-typed at `boolCode` — SR for the eliminator's value-case
computation step. -/
theorem boolElimValueTrueIotaTyped
    (motive : RawTerm 1) (thenBranch elseBranch : RawTerm 0)
    (thenTyped : boolStandaloneRowTyped thenBranch) :
    Step (boolElimCell motive boolTrueCell thenBranch elseBranch) thenBranch ∧
    boolStandaloneRowTyped thenBranch :=
  ⟨IotaHeadStep.iotaBoolTrue.toStep, thenTyped⟩

/-- **Typed ι-computation (false case)**: the `boolFalse` mirror — `boolElim(boolFalse, t, e)` ι-reduces to the
else-branch `e` (`IotaHeadStep.iotaBoolFalse.toStep`), typed at `boolCode`. -/
theorem boolElimValueFalseIotaTyped
    (motive : RawTerm 1) (thenBranch elseBranch : RawTerm 0)
    (elseTyped : boolStandaloneRowTyped elseBranch) :
    Step (boolElimCell motive boolFalseCell thenBranch elseBranch) elseBranch ∧
    boolStandaloneRowTyped elseBranch :=
  ⟨IotaHeadStep.iotaBoolFalse.toStep, elseTyped⟩

/-- A subject typed by the standalone value layer at `boolTypeCell` IS a bool value cell. -/
private theorem standaloneBoolValueCell {subject : RawTerm 0}
    (typed : boolStandaloneRowTyped subject) :
    subject = boolTrueCell ∨ subject = boolFalseCell := by
  rcases typed with
      ⟨generator, payload, children, rule, subjectEq, isDataIntro, classifierEq⟩
    | ⟨generator, payload, children, rule, subjectEq, isBaseType, classifierEq⟩
  · subst subjectEq
    exact standaloneBoolCanonicalForms (generator := generator) (payload := payload)
      (children := children) (Or.inl ⟨rule, isDataIntro, classifierEq⟩)
  · subst subjectEq
    exact standaloneBoolCanonicalForms (generator := generator) (payload := payload)
      (children := children) (Or.inr ⟨rule, isBaseType, classifierEq⟩)

/-- **★ NON-VACUOUS eliminator-computing canonicity.**  A closed `boolElim b t e : Bool` (data-value branches)
COMPUTES by a single ι-step to a bool VALUE.  The scrutinee is `boolTrue`/`boolFalse`
(`standaloneBoolCanonicalForms`), so the eliminator FIRES (`IotaHeadStep.iotaBoolTrue.toStep`/`iotaBoolFalse`) to the selected
branch, itself a bool value (the branch is standalone-value-typed at `boolCode`).  The FIRST canonicity in which the
eliminator genuinely computes — the eliminator-into-data case the four prior firings found vacuous for the
grown-branch engine. -/
theorem boolElimValueCanonicity {profile : PolyProfile} {subject : RawTerm 0}
    (derivation : HasTypeDescBoolElimValue profile (TypingContext.empty : TypingContext profile 0)
      subject boolTypeCell) :
    ∃ value : RawTerm 0, StepStar subject value ∧ (value = boolTrueCell ∨ value = boolFalseCell) := by
  cases derivation with
  | boolElimValueIntro motive scrutinee thenBranch elseBranch scrutineeTyped thenTyped elseTyped =>
      rcases standaloneBoolValueCell scrutineeTyped with scrutEq | scrutEq
      · subst scrutEq
        rcases standaloneBoolValueCell thenTyped with branchEq | branchEq
        · subst branchEq; exact ⟨boolTrueCell, StepStar.single IotaHeadStep.iotaBoolTrue.toStep, Or.inl rfl⟩
        · subst branchEq; exact ⟨boolFalseCell, StepStar.single IotaHeadStep.iotaBoolTrue.toStep, Or.inr rfl⟩
      · subst scrutEq
        rcases standaloneBoolValueCell elseTyped with branchEq | branchEq
        · subst branchEq; exact ⟨boolTrueCell, StepStar.single IotaHeadStep.iotaBoolFalse.toStep, Or.inl rfl⟩
        · subst branchEq; exact ⟨boolFalseCell, StepStar.single IotaHeadStep.iotaBoolFalse.toStep, Or.inr rfl⟩

end FX1Poly.Typed
