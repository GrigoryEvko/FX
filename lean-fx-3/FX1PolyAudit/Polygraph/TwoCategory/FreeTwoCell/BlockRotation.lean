import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.BlockRotation

/-! # FX1PolyAudit.Tier0.Mode.FreeTwoCellBlockRotation — zero-axiom gate (matching keystone, arithmetic core)

Per-declaration zero-axiom gate for the block-rotation permutation: the definition, its branch read-offs, the
left inverse, INJECTIVITY, and the below/above fixing facts.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  NOT registered in
`AuditAll` (the parent does the unified registration). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.blockRotate
#assert_no_axioms FX1Poly.Tier0.blockRotate_below
#assert_no_axioms FX1Poly.Tier0.blockRotate_firstBlock
#assert_no_axioms FX1Poly.Tier0.blockRotate_secondBlock
#assert_no_axioms FX1Poly.Tier0.blockRotate_above
#assert_no_axioms FX1Poly.Tier0.blockRotate_fixesBelow
#assert_no_axioms FX1Poly.Tier0.blockRotate_fixesAbove
#assert_no_axioms FX1Poly.Tier0.addSubCancelRight
#assert_no_axioms FX1Poly.Tier0.subAddCancel
#assert_no_axioms FX1Poly.Tier0.blockRotate_leftInverse
#assert_no_axioms FX1Poly.Tier0.blockRotate_inj
#assert_no_axioms FX1Poly.Tier0.fxMode_hasBlockRotationArithmetic

end FX1PolyAudit
