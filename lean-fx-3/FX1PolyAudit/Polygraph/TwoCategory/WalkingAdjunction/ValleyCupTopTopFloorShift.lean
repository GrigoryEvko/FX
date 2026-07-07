import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCupTopTopFloorShift

/-! # FX1PolyAudit/…/ValleyCupTopTopFloorShift — zero-axiom gate

Per-declaration zero-axiom gate for the offset-space floor-equivariance of `freshShiftAbove` (Piece II tail,
top-top cup-arc partner arithmetic core): the value/offset/list-map floor shift-out that lets the floor factor out
of the floor-parametric per-cup partner transport `diagramPartner_stepCupArc`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.freshShiftAbove_floorEquivariant
#assert_no_axioms FX1Poly.Polygraph.freshShiftAbove_floorEquivariant_offset
#assert_no_axioms FX1Poly.Polygraph.freshShiftAbove_map_floorEquivariant
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasCupTopTopFloorShiftCore

end FX1PolyAudit
