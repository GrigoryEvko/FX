import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallFreeCellConverse

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutWallFreeCellConverse — zero-axiom gate for the wall-free cell
converse prerequisites (WP-AMALG-2 r11, B4)

Per-declaration zero-axiom gate for the wall-free / wall-count bridge (both directions), the dom-to-cod stability
lemma, the concrete probe, and the two honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.wallCountZero_of_pathWallFree
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pathWallFree_of_wallCountZero
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wallFreeMiddleOfCell
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wallFreeMiddleOfCell_probe
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasWallFreeCellConversePrereqs
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_wallFreeCellInvertStaysWalled

end FX1PolyAudit
