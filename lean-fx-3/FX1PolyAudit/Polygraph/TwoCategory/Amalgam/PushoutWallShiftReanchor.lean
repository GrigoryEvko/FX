import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallShiftReanchor

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutWallShiftReanchor — zero-axiom gate for the r18 ordinal-0
re-anchoring + the S-frame merge through a wire-changing body (WP-AMALG-2 r18, B2)

Per-declaration zero-axiom gate for the ordinal-0 definitional re-anchoring, the extreme-ordinal shift contrast, the
wire-changing S-frame merge witness + its slot-count probe, and the two honesty markers (the definitional re-anchoring
and the wall-shift NARROWING that does NOT flip the leg-2 wall).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.ordinalZeroReanchorDefinitional
#assert_no_axioms FX1Poly.Polygraph.Amalgam.ordinalZeroShiftFreeTrailingShifts
#assert_no_axioms FX1Poly.Polygraph.Amalgam.muWireChangeMergeWitness
#assert_no_axioms FX1Poly.Polygraph.Amalgam.muWireChangeMergeSlotCount
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_ordinalZeroReanchorDefinitional
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_ordinalAnchorNarrowsWallShift

end FX1PolyAudit
