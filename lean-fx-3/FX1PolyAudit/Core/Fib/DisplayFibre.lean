import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Fib.DisplayFibre

/-! # FX1PolyAudit.Core.Fib.DisplayFibre — zero-axiom gate (fib-1a)

Per-declaration zero-axiom gate for the display-fibre ⋈ type-axis-code connection: the fibre is indexed by the
type-axis universe codes, and every bridged code populates its fibre. Must be free of propext, Quot.sound,
Classical, sorry, native_decide, omega. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.Fib.unionClassifierIsType_iff_typedAtAxisCode
#assert_no_axioms FX1Poly.Core.Fib.axisCodeToCell_unionClassifierIsType

end FX1PolyAudit
