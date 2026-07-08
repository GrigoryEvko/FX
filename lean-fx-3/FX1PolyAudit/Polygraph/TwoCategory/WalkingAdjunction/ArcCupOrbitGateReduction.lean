import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupOrbitGateReduction

/-! # FX1PolyAudit/…/ArcCupOrbitGateReduction — zero-axiom gate

Per-declaration zero-axiom gate for the final wiring: `ArcCellReconstruction adjunctionModeSignature`
reduces to EXACTLY the general orbit witness, collapsing the whole reduction chain to one grep-able
proposition (the mixed cup/cap leg-aligned re-selection, open beyond the pure-cup base).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.adjunctionArcCellReconstruction_ofOrbitWitness
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupOrbitGateReduction

end FX1PolyAudit
