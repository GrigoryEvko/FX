import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.DependentElimObligationsDriftBounded

/-! # FX1PolyAudit/.../DependentElimObligationsDriftBounded — zero-axiom gate for the bounded dependent-match drift

Per-declaration zero-axiom gate for the fuel-bounded `ObligationsDriftBelow` builders of the dependent-match
eliminators plus the nullary constructor typings.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.boolTrueTypedInContext
#assert_no_axioms FX1Poly.Typed.boolFalseTypedInContext
#assert_no_axioms FX1Poly.Typed.optionNoneTypedInContext
#assert_no_axioms FX1Poly.Typed.listNilTypedInContext
#assert_no_axioms FX1Poly.Typed.boolElimObligationsDriftUnderArgStepBounded

end FX1PolyAudit
