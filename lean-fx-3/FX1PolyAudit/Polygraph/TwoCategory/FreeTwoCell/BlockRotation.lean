import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.BlockRotation

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.BlockRotation — zero-axiom gate (matching keystone, arithmetic core)

Per-declaration zero-axiom gate for the block-rotation permutation: the definition, its branch read-offs, the
left inverse, INJECTIVITY, and the below/above fixing facts.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  NOT registered in
`AuditAll` (the parent does the unified registration). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.blockRotate
#assert_no_axioms FX1Poly.Polygraph.blockRotate_below
#assert_no_axioms FX1Poly.Polygraph.blockRotate_firstBlock
#assert_no_axioms FX1Poly.Polygraph.blockRotate_secondBlock
#assert_no_axioms FX1Poly.Polygraph.blockRotate_above
#assert_no_axioms FX1Poly.Polygraph.blockRotate_fixesBelow
#assert_no_axioms FX1Poly.Polygraph.blockRotate_fixesAbove
#assert_no_axioms FX1Poly.Polygraph.addSubCancelRight
#assert_no_axioms FX1Poly.Polygraph.subAddCancel
#assert_no_axioms FX1Poly.Polygraph.blockRotate_leftInverse
#assert_no_axioms FX1Poly.Polygraph.blockRotate_inj
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasBlockRotationArithmetic

end FX1PolyAudit
