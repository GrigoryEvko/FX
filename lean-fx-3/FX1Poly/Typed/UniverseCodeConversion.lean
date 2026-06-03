import FX1Poly.Typed.UniverseCodeShape
import FX1Poly.Core.RawConfluence

/-! # FX1Poly/Typed/UniverseCodeConversion
    — universe-code conversion injectivity (a no-Type-in-Type-under-conversion fact)

`universeCodeCell_inj` (`UniverseCodeShape.lean`) decides syntactic equality of universe codes.  The totalBridge
conv arm (SN-027/#662) needs the CONVERSION version: two CONVERTIBLE universe codes have equal levels and flags.
This holds because universe codes are step normal forms (no redex root, `childNil` spine — `noStep_universeCode`),
so global confluence (`Conv.iff_normalForms_eq_of_confluence`, the #420/#716 harvest, no SN premise) collapses
`Conv` between them to syntactic equality, which `universeCodeCell_inj` then splits.

This sits one layer above `UniverseCodeShape` precisely because it consumes the confluence proof — keeping the
shape file free of the heavy `RawConfluence` dependency.

## Zero-axiom verification

`isStepNormalForm (universeCodeCell …)` is `rfl` (the structural normality Bool computes to `true`);
`Conv.iff_normalForms_eq_of_confluence` is the confluence harvest; `universeCodeCell_inj` is propext-free `cases`
injectivity.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Universe-code conversion injectivity.**  Two convertible universe codes have equal levels and flags.  Both
are step normal forms, so `Conv.iff_normalForms_eq_of_confluence` (global confluence, no SN premise) reduces
their convertibility to syntactic equality, then `universeCodeCell_inj` splits it.  The conversion-level
no-Type-in-Type fact the totalBridge conv arm reads to align a universe-code reclassifier's level with the
classifier it was converted from. -/
theorem universeCodeCell_inj_of_conv {scope : Nat}
    {leftLevel rightLevel : LevelExpr} {leftFlag rightFlag : UniverseFlag}
    (conv : Conv (universeCodeCell leftLevel leftFlag : RawTerm scope)
      (universeCodeCell rightLevel rightFlag)) :
    leftLevel = rightLevel ∧ leftFlag = rightFlag := by
  have leftIsNormal : RawTerm.isStepNormalForm (universeCodeCell leftLevel leftFlag : RawTerm scope) := rfl
  have rightIsNormal : RawTerm.isStepNormalForm (universeCodeCell rightLevel rightFlag : RawTerm scope) := rfl
  have codesEqual :
      (universeCodeCell leftLevel leftFlag : RawTerm scope) = universeCodeCell rightLevel rightFlag :=
    (Conv.iff_normalForms_eq_of_confluence (StepStar.refl _) leftIsNormal (StepStar.refl _) rightIsNormal).mp conv
  exact universeCodeCell_inj codesEqual

end FX1Poly.Typed
