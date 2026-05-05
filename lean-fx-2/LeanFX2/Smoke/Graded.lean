import LeanFX2.Graded.Rules
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

#assert_no_axioms LeanFX2.Smoke.dimensions21_lamRule_zeroProjection_smoke
#assert_no_axioms LeanFX2.Smoke.dimensions21_appRule_zeroProjection_smoke

end LeanFX2.Smoke
