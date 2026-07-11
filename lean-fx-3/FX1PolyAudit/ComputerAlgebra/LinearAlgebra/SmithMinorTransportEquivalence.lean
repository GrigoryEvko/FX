import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithMinorTransportEquivalence

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithMinorTransportEquivalence — zero-axiom gate
    (H2-SMITH reconnection — Parts A1/A2/A3 adjudication + the inverse-transport equivalence)

Per-declaration zero-axiom gate for the exit-divides ⟺ input-divides equivalence and the A1/A2/A3
truth-probes.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

/- The sweep-output abbreviation + the A2 exit-cross-clear truth-probe (the diagonal/cross-clear
   adjudication fixture). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithPivotClearingOutput
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearingSweepExitCrossClearOnConcreteWindow

end FX1PolyAudit
