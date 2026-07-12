import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithPrefixSettledDescentInsufficient

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithPrefixSettledDescentInsufficient — zero-axiom gate
    (H2-SMITH r39, #2261 — the `SmithPrefixSettled`-guarded one-round descent is FALSE; the corrected
    lever is `belowPivotColumnConfined`)

Per-declaration zero-axiom gate for the r39 gate-correction round: the corrected lever
`belowPivotColumnConfined`, the design's proposed gate `SmithFoldDescendsOnPrefixSettledNonzeroPivot`,
its refutation `smithFoldDescendsOnPrefixSettledNonzeroPivotIsRefuted` (the GRAVEYARD — the gate is
VACUOUS at pivot 0 and re-admits the r31 refuter), the confinement-separation battery
(`smithConfinedGuardExcludesRefuter`, `smithDriverWitnessConfined`,
`smithConfinedFoldDescendsOnDriverWitness`), the corrected candidate
`SmithFoldDescendsOnConfinedNonzeroPivot`, and the D3 instantiation
`smithClearingOutputFindNoneFromConfinedFoldDescent`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`.  Both the fuel-based `#assert_no_axioms` AND the independent (non-fuel)
`#print axioms` are run on every declaration (the project macro is fuel-based — not trusted alone). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.belowPivotColumnConfined
#assert_no_axioms FX1Poly.ComputerAlgebra.SmithFoldDescendsOnPrefixSettledNonzeroPivot
#assert_no_axioms FX1Poly.ComputerAlgebra.smithFoldDescendsOnPrefixSettledNonzeroPivotIsRefuted
#assert_no_axioms FX1Poly.ComputerAlgebra.smithConfinedGuardExcludesRefuter
#assert_no_axioms FX1Poly.ComputerAlgebra.smithDriverWitnessConfined
#assert_no_axioms FX1Poly.ComputerAlgebra.smithConfinedFoldDescendsOnDriverWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.SmithFoldDescendsOnConfinedNonzeroPivot
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearingOutputFindNoneFromConfinedFoldDescent

-- Independent (non-fuel) axiom prints on every declaration.
#print axioms FX1Poly.ComputerAlgebra.belowPivotColumnConfined
#print axioms FX1Poly.ComputerAlgebra.SmithFoldDescendsOnPrefixSettledNonzeroPivot
#print axioms FX1Poly.ComputerAlgebra.smithFoldDescendsOnPrefixSettledNonzeroPivotIsRefuted
#print axioms FX1Poly.ComputerAlgebra.smithConfinedGuardExcludesRefuter
#print axioms FX1Poly.ComputerAlgebra.smithDriverWitnessConfined
#print axioms FX1Poly.ComputerAlgebra.smithConfinedFoldDescendsOnDriverWitness
#print axioms FX1Poly.ComputerAlgebra.SmithFoldDescendsOnConfinedNonzeroPivot
#print axioms FX1Poly.ComputerAlgebra.smithClearingOutputFindNoneFromConfinedFoldDescent

end FX1PolyAudit
