import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.RealizedChain

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.RealizedChain — zero-axiom gate (mode-3 floor)

Per-declaration zero-axiom gate for the boundary-coherent realized-spine chain: the chain datatype
(`RealizedSpineChain`), its total cast-free readback (`chainToCell`), the underlying atom list / singleton /
concatenation (`chainAtoms` / `singletonRealizedChain` / `concatRealizedChain`), the readback smokes
(`chainToCell_nil` / `chainToCell_cons`), the faithfulness roundtrip (`atomFrame_spineDiff` /
`atomFrame_spineDiff_top` / `chainToCell_spine`), the readback homomorphism (`chainToCell_concat`), and the
machine-checked obstruction witness (`adjunctionUnitSpineAtom` / `adjunctionUnitSpineAtom_isUnitSpine` /
`adjunctionUnitFrame_isInterchangeNormal` / `adjunctionUnitFrame_spine_eq_unit` /
`adjunctionUnitFrame_normalForm_ne_unit`).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.RealizedSpineChain
#assert_no_axioms FX1Poly.Polygraph.chainToCell
#assert_no_axioms FX1Poly.Polygraph.chainAtoms
#assert_no_axioms FX1Poly.Polygraph.singletonRealizedChain
#assert_no_axioms FX1Poly.Polygraph.concatRealizedChain
#assert_no_axioms FX1Poly.Polygraph.chainToCell_nil
#assert_no_axioms FX1Poly.Polygraph.chainToCell_cons
#assert_no_axioms FX1Poly.Polygraph.atomFrame_spineDiff
#assert_no_axioms FX1Poly.Polygraph.atomFrame_spineDiff_top
#assert_no_axioms FX1Poly.Polygraph.chainToCell_spine
#assert_no_axioms FX1Poly.Polygraph.chainToCell_concat
#assert_no_axioms FX1Poly.Polygraph.adjunctionUnitSpineAtom
#assert_no_axioms FX1Poly.Polygraph.adjunctionUnitSpineAtom_isUnitSpine
#assert_no_axioms FX1Poly.Polygraph.adjunctionUnitFrame_isInterchangeNormal
#assert_no_axioms FX1Poly.Polygraph.adjunctionUnitFrame_spine_eq_unit
#assert_no_axioms FX1Poly.Polygraph.adjunctionUnitFrame_normalForm_ne_unit
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasRealizedChainCellBridge

end FX1PolyAudit
