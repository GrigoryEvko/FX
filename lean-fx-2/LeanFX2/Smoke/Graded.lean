import LeanFX2.Graded.Rules
import LeanFX2.Graded.Term
import LeanFX2.Graded.Instances.Usage
import LeanFX2.Graded.Dimensions21
import LeanFX2.Tools.DependencyAudit

/-! # Smoke/Graded — Atkey-2018 witness rejection + canonical examples.

```lean
-- The Atkey-2018 unsoundness witness:
-- fn higher_order(f: i64 -> i64) : i64 -> i64 = fn(x) => f(f(x))
-- This SHOULD NOT typecheck under Wood/Atkey's corrected rule.
example : ¬ ∃ wellTypedTerm,
    Graded.WellTyped Γ (RawTerm.lam (RawTerm.lam
        (RawTerm.app (RawTerm.var 1) (RawTerm.app (RawTerm.var 1) (RawTerm.var 0)))))
        wellTypedTerm UsageGrade.one
  := by ...

-- Canonical linear example: fn(x) => x typechecks at grade 1
example : Graded.WellTyped Γ (RawTerm.lam (RawTerm.var 0)) ... UsageGrade.one := ...

-- Canonical unrestricted example: fn(x) => x typechecks at grade ω
example : Graded.WellTyped Γ (RawTerm.lam (RawTerm.var 0)) ... UsageGrade.omega := ...
```

## Dependencies

* `Graded/Rules.lean`, `Graded/Instances/Usage.lean`

## Implementation plan (Layer 14)

1. Atkey-2018 witness rejection
2. Canonical linear / affine / unrestricted examples
3. Effect grade examples (Tot, IO, IO+Async)
4. Security grade examples (unclassified flow / classified flow)
-/

namespace LeanFX2.Smoke

/-- The D5.4 aggregate semiring projection feeds the corrected Lam rule.

This is intentionally modest: it does not claim `FXGradeVector21` is wired
into typed `Term`.  It does force the 21-slot registry's semiring payload
to instantiate the existing Wood/Atkey rule surface. -/
theorem dimensions21_lamRule_zeroProjection_smoke :
    Graded.IsLamCompatible
      (paramGrade := Graded.FXGradeVector21.bottom.semiringGrades)
      (closureGrade := Graded.FXGradeVector21.one.semiringGrades)
      (bodyAttr :=
        (Graded.GradeAttribution.zero :
          Graded.GradeAttribution Graded.semiringDimensions21 1))
      (lamAttr :=
        (Graded.GradeAttribution.zero :
          Graded.GradeAttribution Graded.semiringDimensions21 0)) :=
  Graded.IsLamCompatible.allZero
    Graded.FXGradeVector21.one.semiringGrades

/-- The D5.4 aggregate semiring projection feeds Lam divided-availability
monotonicity. -/
theorem dimensions21_lamAvailable_mono_zeroProjection_smoke :
    Graded.IsLamCompatibleWithAvailable
      (paramGrade := Graded.FXGradeVector21.bottom.semiringGrades)
      (availableAttr :=
        (Graded.GradeAttribution.zero :
          Graded.GradeAttribution Graded.semiringDimensions21 0))
      (bodyAttr :=
        (Graded.GradeAttribution.zero :
          Graded.GradeAttribution Graded.semiringDimensions21 1)) :=
  Graded.IsLamCompatibleWithAvailable.available_mono
    Graded.FXGradeVector21.bottom.semiringGrades
    (Graded.GradeAttribution.zero :
      Graded.GradeAttribution Graded.semiringDimensions21 0)
    (Graded.GradeAttribution.zero :
      Graded.GradeAttribution Graded.semiringDimensions21 0)
    (Graded.GradeAttribution.zero :
      Graded.GradeAttribution Graded.semiringDimensions21 1)
    (Graded.GradeAttribution.le_refl Graded.GradeAttribution.zero)
    Graded.IsLamCompatibleWithAvailable.allZeroAtZero

/-- The D5.4 aggregate semiring projection feeds the App rule. -/
theorem dimensions21_appRule_zeroProjection_smoke :
    Graded.IsAppCompatible
      Graded.FXGradeVector21.one.semiringGrades
      (functionAttr :=
        (Graded.GradeAttribution.zero :
          Graded.GradeAttribution Graded.semiringDimensions21 0))
      (argumentAttr :=
        (Graded.GradeAttribution.zero :
          Graded.GradeAttribution Graded.semiringDimensions21 0))
      (resultAttr :=
        (Graded.GradeAttribution.zero :
          Graded.GradeAttribution Graded.semiringDimensions21 0)) :=
  Graded.IsAppCompatible.allZero
    Graded.FXGradeVector21.one.semiringGrades

/-- The D5.4 aggregate semiring projection also feeds App subsumption
monotonicity.  This compiles only if `FXGradeVector21`'s semiring payload
still matches the generic attribution/rule surface. -/
theorem dimensions21_appRule_mono_zeroProjection_smoke :
    Graded.GradeAttribution.le
      ((Graded.GradeAttribution.zero :
        Graded.GradeAttribution Graded.semiringDimensions21 0))
      ((Graded.GradeAttribution.zero :
        Graded.GradeAttribution Graded.semiringDimensions21 0)) :=
  Graded.IsAppCompatible.mono
    Graded.FXGradeVector21.one.semiringGrades
    Graded.FXGradeVector21.one.semiringGrades
    (Graded.GradeAttribution.zero :
      Graded.GradeAttribution Graded.semiringDimensions21 0)
    (Graded.GradeAttribution.zero :
      Graded.GradeAttribution Graded.semiringDimensions21 0)
    (Graded.GradeAttribution.zero :
      Graded.GradeAttribution Graded.semiringDimensions21 0)
    (Graded.GradeAttribution.zero :
      Graded.GradeAttribution Graded.semiringDimensions21 0)
    (Graded.GradeAttribution.zero :
      Graded.GradeAttribution Graded.semiringDimensions21 0)
    (Graded.GradeAttribution.zero :
      Graded.GradeAttribution Graded.semiringDimensions21 0)
    (Graded.GradeVector.le_refl Graded.FXGradeVector21.one.semiringGrades)
    (Graded.GradeAttribution.le_refl Graded.GradeAttribution.zero)
    (Graded.GradeAttribution.le_refl Graded.GradeAttribution.zero)
    dimensions21_appRule_zeroProjection_smoke
    dimensions21_appRule_zeroProjection_smoke

/-- The D5.4 aggregate semiring projection feeds the Let rule. -/
theorem dimensions21_letRule_zeroProjection_smoke :
    Graded.IsLetCompatible
      Graded.FXGradeVector21.bottom.semiringGrades
      (boundAttr :=
        (Graded.GradeAttribution.zero :
          Graded.GradeAttribution Graded.semiringDimensions21 0))
      (bodyAttr :=
        (Graded.GradeAttribution.zero :
          Graded.GradeAttribution Graded.semiringDimensions21 1))
      (resultAttr :=
        (Graded.GradeAttribution.zero :
          Graded.GradeAttribution Graded.semiringDimensions21 0)) := by
  constructor
  · rfl
  · rfl

/-- The D5.4 aggregate semiring projection feeds Let subsumption
monotonicity through the existing rule surface. -/
theorem dimensions21_letRule_mono_zeroProjection_smoke :
    Graded.GradeAttribution.le
      ((Graded.GradeAttribution.zero :
        Graded.GradeAttribution Graded.semiringDimensions21 0))
      ((Graded.GradeAttribution.zero :
        Graded.GradeAttribution Graded.semiringDimensions21 0)) :=
  Graded.IsLetCompatible.mono
    Graded.FXGradeVector21.bottom.semiringGrades
    Graded.FXGradeVector21.bottom.semiringGrades
    (Graded.GradeAttribution.zero :
      Graded.GradeAttribution Graded.semiringDimensions21 0)
    (Graded.GradeAttribution.zero :
      Graded.GradeAttribution Graded.semiringDimensions21 0)
    (Graded.GradeAttribution.zero :
      Graded.GradeAttribution Graded.semiringDimensions21 1)
    (Graded.GradeAttribution.zero :
      Graded.GradeAttribution Graded.semiringDimensions21 1)
    (Graded.GradeAttribution.zero :
      Graded.GradeAttribution Graded.semiringDimensions21 0)
    (Graded.GradeAttribution.zero :
      Graded.GradeAttribution Graded.semiringDimensions21 0)
    (Graded.GradeVector.le_refl Graded.FXGradeVector21.bottom.semiringGrades)
    (Graded.GradeAttribution.le_refl Graded.GradeAttribution.zero)
    (Graded.GradeAttribution.le_refl Graded.GradeAttribution.zero)
    dimensions21_letRule_zeroProjection_smoke
    dimensions21_letRule_zeroProjection_smoke

/-- The D5.4 aggregate semiring projection feeds If/Match subsumption
monotonicity through the existing rule surface. -/
theorem dimensions21_ifRule_mono_zeroProjection_smoke :
    Graded.GradeAttribution.le
      ((Graded.GradeAttribution.zero :
        Graded.GradeAttribution Graded.semiringDimensions21 0))
      ((Graded.GradeAttribution.zero :
        Graded.GradeAttribution Graded.semiringDimensions21 0)) :=
  Graded.IsIfCompatible.mono
    (Graded.GradeAttribution.zero :
      Graded.GradeAttribution Graded.semiringDimensions21 0)
    (Graded.GradeAttribution.zero :
      Graded.GradeAttribution Graded.semiringDimensions21 0)
    (Graded.GradeAttribution.zero :
      Graded.GradeAttribution Graded.semiringDimensions21 0)
    (Graded.GradeAttribution.zero :
      Graded.GradeAttribution Graded.semiringDimensions21 0)
    (Graded.GradeAttribution.zero :
      Graded.GradeAttribution Graded.semiringDimensions21 0)
    (Graded.GradeAttribution.zero :
      Graded.GradeAttribution Graded.semiringDimensions21 0)
    (Graded.GradeAttribution.zero :
      Graded.GradeAttribution Graded.semiringDimensions21 0)
    (Graded.GradeAttribution.zero :
      Graded.GradeAttribution Graded.semiringDimensions21 0)
    (Graded.GradeAttribution.le_refl Graded.GradeAttribution.zero)
    (Graded.GradeAttribution.le_refl Graded.GradeAttribution.zero)
    (Graded.GradeAttribution.le_refl Graded.GradeAttribution.zero)
    rfl
    rfl

/-- The shadow graded-term layer can build a closed unit value over the
21-dimension semiring registry.  This forces the aggregate registry,
graded context erasure, and the typed `Term.unit` constructor to agree. -/
def dimensions21_gradedTerm_unit_smoke :
    Graded.GradedTerm
      (Graded.GradedCtx.empty
        (mode := Mode.software) (level := 0)
        (dimensions := Graded.semiringDimensions21))
      Ty.unit
      RawTerm.unit
      (Graded.GradeAttribution.zero :
        Graded.GradeAttribution Graded.semiringDimensions21 0) :=
  Graded.GradedTerm.unit

/-- The shadow graded-term layer can build a closed ignored-argument
lambda, guarded by the corrected Lam compatibility predicate. -/
def dimensions21_gradedTerm_lam_smoke :
    Graded.GradedTerm
      (Graded.GradedCtx.empty
        (mode := Mode.software) (level := 0)
        (dimensions := Graded.semiringDimensions21))
      (Ty.arrow Ty.unit Ty.unit)
      (RawTerm.lam RawTerm.unit)
      (Graded.GradeAttribution.zero :
        Graded.GradeAttribution Graded.semiringDimensions21 0) :=
  Graded.GradedTerm.lam
    (paramGrade := Graded.FXGradeVector21.bottom.semiringGrades)
    (closureGrade := Graded.FXGradeVector21.one.semiringGrades)
    (bodyAttr :=
      (Graded.GradeAttribution.zero :
        Graded.GradeAttribution Graded.semiringDimensions21 1))
    (lamAttr :=
      (Graded.GradeAttribution.zero :
        Graded.GradeAttribution Graded.semiringDimensions21 0))
    Graded.GradedTerm.unit
    (Graded.IsLamCompatible.allZero
      Graded.FXGradeVector21.one.semiringGrades)

/-- The shadow graded-term layer can apply a graded closed function to a
graded closed argument, guarded by the App compatibility predicate. -/
def dimensions21_gradedTerm_app_smoke :
    Graded.GradedTerm
      (Graded.GradedCtx.empty
        (mode := Mode.software) (level := 0)
        (dimensions := Graded.semiringDimensions21))
      Ty.unit
      (RawTerm.app (RawTerm.lam RawTerm.unit) RawTerm.unit)
      (Graded.GradeAttribution.zero :
        Graded.GradeAttribution Graded.semiringDimensions21 0) :=
  Graded.GradedTerm.app
    Graded.FXGradeVector21.bottom.semiringGrades
    dimensions21_gradedTerm_lam_smoke
    dimensions21_gradedTerm_unit_smoke
    (Graded.IsAppCompatible.allZero
      Graded.FXGradeVector21.bottom.semiringGrades)

/-- Grade-only subsumption preserves the underlying typed term while
checking the 21-dimension attribution preorder. -/
def dimensions21_gradedTerm_subsume_smoke :
    Graded.GradedTerm
      (Graded.GradedCtx.empty
        (mode := Mode.software) (level := 0)
        (dimensions := Graded.semiringDimensions21))
      Ty.unit
      RawTerm.unit
      (Graded.GradeAttribution.zero :
        Graded.GradeAttribution Graded.semiringDimensions21 0) :=
  Graded.GradedTerm.subsumeGrade
    dimensions21_gradedTerm_unit_smoke
    (Graded.IsSubsumptionCompatible.refl
      (Graded.GradeAttribution.zero :
        Graded.GradeAttribution Graded.semiringDimensions21 0))

#assert_no_axioms LeanFX2.Smoke.dimensions21_lamRule_zeroProjection_smoke
#assert_no_axioms LeanFX2.Smoke.dimensions21_lamAvailable_mono_zeroProjection_smoke
#assert_no_axioms LeanFX2.Smoke.dimensions21_appRule_zeroProjection_smoke
#assert_no_axioms LeanFX2.Smoke.dimensions21_appRule_mono_zeroProjection_smoke
#assert_no_axioms LeanFX2.Smoke.dimensions21_letRule_zeroProjection_smoke
#assert_no_axioms LeanFX2.Smoke.dimensions21_letRule_mono_zeroProjection_smoke
#assert_no_axioms LeanFX2.Smoke.dimensions21_ifRule_mono_zeroProjection_smoke
#assert_no_axioms LeanFX2.Smoke.dimensions21_gradedTerm_unit_smoke
#assert_no_axioms LeanFX2.Smoke.dimensions21_gradedTerm_lam_smoke
#assert_no_axioms LeanFX2.Smoke.dimensions21_gradedTerm_app_smoke
#assert_no_axioms LeanFX2.Smoke.dimensions21_gradedTerm_subsume_smoke

end LeanFX2.Smoke
