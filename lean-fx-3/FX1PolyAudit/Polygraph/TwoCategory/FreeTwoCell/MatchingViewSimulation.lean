import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingViewSimulation

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingViewSimulation — zero-axiom gate

Per-declaration zero-axiom gate for the bundled connectivity-view simulation: the relation,
reflexivity, the per-atom cup/cap dispatch, the disciplined spine fold, and the honesty
marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.MatchingConnectivityViewSim
#assert_no_axioms FX1Poly.Polygraph.matchingConnectivityViewSim_refl
#assert_no_axioms FX1Poly.Polygraph.matchingConnectivityViewSim_stepAtom
#assert_no_axioms FX1Poly.Polygraph.matchingConnectivityViewSim_processSpine
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingConnectivityViewSim

end FX1PolyAudit
