import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Homology.SquierNoGoRestingFrontier

/-! # FX1PolyAudit/Polygraph/Homology/SquierNoGoRestingFrontier -- zero-axiom gate for the H2-SQUIER-NOGO r8
    honest resting adjudication (the Squier no-go frontier, #2139)

Per-declaration zero-axiom gate: the frontier-status inductive `SquierNoGoFrontierStatus`, the resting
record `SquierNoGoRestingFrontier` with its filled value, the six no-flip pin facts (the three r7 delivery
markers, the r6 general-H2 wall, the leg-2 carrier-finiteness wall at the r7 head, and the r1 honesty
marker -- all byte-identical, no fabricated flip), and the resting marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`.  The record / marker layer is pure inductive / structure / `rfl` on literal `Bool` and enum
constructors; the carrier-finiteness pin is a direct application of the shipped generic
`carrierDegreeThreeChainIsAlwaysFinite` (itself `fun _ => rfl`), so it adds no axiom surface. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Homology.SquierNoGoFrontierStatus
#assert_no_axioms FX1Poly.Polygraph.Homology.SquierNoGoRestingFrontier
#assert_no_axioms FX1Poly.Polygraph.Homology.squierNoGoRestingFrontier
#assert_no_axioms FX1Poly.Polygraph.Homology.squierNoGoRestPinsType2H2VindicatedAtInstance
#assert_no_axioms FX1Poly.Polygraph.Homology.squierNoGoRestPinsTautologicalCollapseNote
#assert_no_axioms FX1Poly.Polygraph.Homology.squierNoGoRestPinsLedgerResidual
#assert_no_axioms FX1Poly.Polygraph.Homology.squierNoGoRestPinsGeneralH2WallStands
#assert_no_axioms FX1Poly.Polygraph.Homology.squierNoGoRestPinsCarrierFinitenessAtCompletedHead
#assert_no_axioms FX1Poly.Polygraph.Homology.squierNoGoRestPinsOpenedButNotClosed
#assert_no_axioms FX1Poly.Polygraph.Homology.squierNoGoWalkerRestsAtHonestFrontier

/-! ### Independent `#print axioms` cross-check for the load-bearing decls (not trusting the fuel-based
`#assert_no_axioms`; the core `#print axioms` command does not truncate). -/

#print axioms FX1Poly.Polygraph.Homology.squierNoGoRestingFrontier
#print axioms FX1Poly.Polygraph.Homology.squierNoGoRestPinsType2H2VindicatedAtInstance
#print axioms FX1Poly.Polygraph.Homology.squierNoGoRestPinsGeneralH2WallStands
#print axioms FX1Poly.Polygraph.Homology.squierNoGoRestPinsCarrierFinitenessAtCompletedHead
#print axioms FX1Poly.Polygraph.Homology.squierNoGoRestPinsOpenedButNotClosed
#print axioms FX1Poly.Polygraph.Homology.squierNoGoWalkerRestsAtHonestFrontier

end FX1PolyAudit
