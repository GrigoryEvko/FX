import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Fib.ModeFibration

/-! # FX1PolyAudit.Core.Fib.ModeFibration — zero-axiom gate (fib-3 keystone)

Per-declaration zero-axiom gate for the mode-fibration realization capstone: the assembled
`affineModeFibrationRealized` (fib-3a unpointable lock + fib-3c derived inaccessibility + fib-3b faithful
ObligationModality embedding) and the mode-dec re-export `affineModeFibration_modalityEqualityDecidable`.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.Fib.affineModeFibrationRealized
#assert_no_axioms FX1Poly.Core.Fib.affineModeFibration_modalityEqualityDecidable

end FX1PolyAudit
