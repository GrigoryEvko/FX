import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcWireDistinct

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/ArcWireDistinct — zero-axiom gate

Per-declaration zero-axiom gate for the ARC-fold open-wire distinctness invariant: the
per-step preservation (cup / cap / generic box over the shared public splice/removal kit),
the `ArcStateFresh`-threaded fold invariant, and the canonical-initial-state instances.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.wireListDistinct_insertFreshBlockAnyPosition
#assert_no_axioms FX1Poly.Polygraph.wireListDistinct_cupLegs
#assert_no_axioms FX1Poly.Polygraph.wireListDistinct_freshBlock
#assert_no_axioms FX1Poly.Polygraph.wireListDistinct_droppedWires
#assert_no_axioms FX1Poly.Polygraph.stepCupArc_wireListDistinct
#assert_no_axioms FX1Poly.Polygraph.stepCapArc_wireListDistinct
#assert_no_axioms FX1Poly.Polygraph.stepArcAtom_wireListDistinct
#assert_no_axioms FX1Poly.Polygraph.processArcSpine_wireListDistinct
#assert_no_axioms FX1Poly.Polygraph.arcInitialState_wireListDistinct
#assert_no_axioms FX1Poly.Polygraph.processArcSpine_fromInitial_wireListDistinct
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcWireDistinctness

end FX1PolyAudit
