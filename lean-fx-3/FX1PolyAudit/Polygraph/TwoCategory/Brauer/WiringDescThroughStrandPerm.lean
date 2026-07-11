import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescThroughStrandPerm

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescThroughStrandPerm — zero-axiom gate (BRAUER r25 GAP γ witness)

Per-declaration zero-axiom gate for the GAP γ `throughStrandPerm` range-permutation witness: the `IsPermutationOfRange`
bundle (`throughStrandPerm_isPermutationOfRange`), the corrected `middle` decode (`correctedMiddle_decodesReadOff`),
their 3-through firings, and the ingredient marker (`fxBrauer_hasThroughStrandPermPerm`).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.throughStrandPerm_isPermutationOfRange
#assert_no_axioms FX1Poly.Polygraph.correctedMiddle_decodesReadOff
#assert_no_axioms FX1Poly.Polygraph.isBoundaryInvolution_threeThroughCrossing
#assert_no_axioms FX1Poly.Polygraph.throughStrandPerm_isPermutationOfRange_fires3Through
#assert_no_axioms FX1Poly.Polygraph.correctedMiddle_decodesReadOff_fires3Through
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasThroughStrandPermPerm

end FX1PolyAudit
