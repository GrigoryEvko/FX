import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallShiftOffset

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutWallShiftOffset — zero-axiom gate for the r18 wall-offset
function + the propext-safe shift-composition law (WP-AMALG-2 r18, B1)

Per-declaration zero-axiom gate for the per-ordinal wall offsets (`wallOffsetDom` / `wallOffsetCod`), the gap-length
sums, the layout-length connections, the pure-`Nat` `shiftPairing`, the shift-composition law
`pushoutWallShiftComposes`, the concrete `mu`-firing wire-changing block + its probes, and the honesty marker.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.wallOffsetDom
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wallOffsetCod
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapDomLenSum
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapCodLenSum
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapDomLayout_length
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gapCodLayout_length
#assert_no_axioms FX1Poly.Polygraph.Amalgam.shiftPairing
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutWallShiftComposes
#assert_no_axioms FX1Poly.Polygraph.Amalgam.muWallShiftBlock
#assert_no_axioms FX1Poly.Polygraph.Amalgam.muWallShiftBlock_domOffset
#assert_no_axioms FX1Poly.Polygraph.Amalgam.muWallShiftBlock_codOffset
#assert_no_axioms FX1Poly.Polygraph.Amalgam.muWallShiftComposes
#assert_no_axioms FX1Poly.Polygraph.Amalgam.muWallShiftBlock_domLayoutLength
#assert_no_axioms FX1Poly.Polygraph.Amalgam.muWallShiftBlock_codLayoutLength
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasWallShiftOffset

end FX1PolyAudit
