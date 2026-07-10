import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Table.PresentationOpDuality

/-! # FX1PolyAudit.Polygraph.TwoCategory.Table.PresentationOpDuality — zero-axiom gate for the `op` involution
on the presentation carrier (WALKER-DUALITY B1).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Table.opSignature
#assert_no_axioms FX1Poly.Polygraph.Table.opSignature_involutive
#assert_no_axioms FX1Poly.Polygraph.Table.opCell
#assert_no_axioms FX1Poly.Polygraph.Table.opCell_involutive
#assert_no_axioms FX1Poly.Polygraph.Table.opCellRel
#assert_no_axioms FX1Poly.Polygraph.Table.opCellRel_ofCells
#assert_no_axioms FX1Poly.Polygraph.Table.fxTab_hasOpInvolution

end FX1PolyAudit
