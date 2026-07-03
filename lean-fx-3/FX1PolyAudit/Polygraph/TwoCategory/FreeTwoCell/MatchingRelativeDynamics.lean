import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRelativeDynamics

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingRelativeDynamics — zero-axiom gate

Per-declaration zero-axiom gate for the relative-run dynamics package (MODE3-D brick D4a):
the generic-sigma links/loops/wires read-offs, the mid-state provenance package, the
mid-state instantiations, and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.processSpine_links_ofRelativeSim
#assert_no_axioms FX1Poly.Polygraph.processSpine_loops_ofRelativeSim
#assert_no_axioms FX1Poly.Polygraph.processSpine_openWires_ofRelativeSim
#assert_no_axioms FX1Poly.Polygraph.canonicalMatchingSeed_wireStateFresh
#assert_no_axioms FX1Poly.Polygraph.processSpine_fromSeed_wireStateFresh
#assert_no_axioms FX1Poly.Polygraph.processSpine_fromSeed_nextFresh_pos
#assert_no_axioms FX1Poly.Polygraph.processSpine_links_ofMidState
#assert_no_axioms FX1Poly.Polygraph.processSpine_loops_ofMidState
#assert_no_axioms FX1Poly.Polygraph.processSpine_openWires_ofMidState
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingRelativeDynamics

end FX1PolyAudit
