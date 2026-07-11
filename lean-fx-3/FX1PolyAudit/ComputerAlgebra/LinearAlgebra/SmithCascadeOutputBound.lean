import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithCascadeOutputBound

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithCascadeOutputBound — zero-axiom gate
    (H2-SMITH r30, #2261 — the inner Euclid cascade's OUTPUT pivot bound)

Per-declaration zero-axiom gate for route R2's first real theorem: `smithCascadeSweepOutputPivotLeInputPivot`
(the never-raises invariant — the cascade output pivot magnitude is `≤` the positive input pivot's) and
`smithCascadeSweepOutputPivotBounded` (the witness form — recon brick 1: the output pivot is `≤` any
nonzero minor witness, under fuel-adequacy).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`.  Both the fuel-based `#assert_no_axioms` AND the independent (non-fuel)
`#print axioms` are run on every declaration (the project macro is fuel-based — not trusted alone). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.smithCascadeSweepOutputPivotLeInputPivot
#assert_no_axioms FX1Poly.ComputerAlgebra.smithCascadeSweepOutputPivotBounded

-- Independent (non-fuel) axiom prints on every declaration.
#print axioms FX1Poly.ComputerAlgebra.smithCascadeSweepOutputPivotLeInputPivot
#print axioms FX1Poly.ComputerAlgebra.smithCascadeSweepOutputPivotBounded

end FX1PolyAudit
