import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Fib.DisplayFibre

/-! # FX1PolyAudit.Typed.Fib.DisplayFibre — zero-axiom gate (fib-1a/1b)

Per-declaration zero-axiom gate for the display-fibre ⋈ type-axis-code connection (fib-1a) and the union-level
total-space admission (fib-1b). Must be free of propext, Quot.sound, Classical, sorry, native_decide, omega. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.Fib.unionClassifierIsType_iff_typedAtAxisCode
#assert_no_axioms FX1Poly.Core.Fib.axisCodeToCell_unionClassifierIsType
#assert_no_axioms FX1Poly.Axis.ClassifiedCell.IsAdmittedByUnion
#assert_no_axioms FX1Poly.Core.Fib.classifiedCellOfUnionTyping
#assert_no_axioms FX1Poly.Core.Fib.displayClassifier_classifiedCellOfUnionTyping
#assert_no_axioms FX1Poly.Core.Fib.genericClassifiedCell_admittedByUnion

end FX1PolyAudit
