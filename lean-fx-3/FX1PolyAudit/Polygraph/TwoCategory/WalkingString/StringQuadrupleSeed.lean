import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringQuadrupleSeed

/-! # FX1PolyAudit.…WalkingString.StringQuadrupleSeed — zero-axiom gate (FC-4 r2, brick R1 seed)

Per-declaration zero-axiom gate for the `k = 3` adjoint-quadruple seed: the quiver (two modes, four letters), the six
endo-words, the six-generator `StringQuadTwoCell`, the mode signature, the faithful index abstraction
(`quadLabelIndex` / `quadIndexWord`), the freeness smokes, and the `k = 3` census-carrier bridge
(`quadCupCods_eq_carrierAtThree` / `quadCapDoms_eq_carrierAtThree`).  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.AdjointQuadrupleMode
#assert_no_axioms FX1Poly.Polygraph.AdjointQuadrupleModality
#assert_no_axioms FX1Poly.Polygraph.adjointQuadrupleGraph
#assert_no_axioms FX1Poly.Polygraph.quadL1L2
#assert_no_axioms FX1Poly.Polygraph.quadL2L1
#assert_no_axioms FX1Poly.Polygraph.quadL2L3
#assert_no_axioms FX1Poly.Polygraph.quadL3L2
#assert_no_axioms FX1Poly.Polygraph.quadL3L4
#assert_no_axioms FX1Poly.Polygraph.quadL4L3
#assert_no_axioms FX1Poly.Polygraph.StringQuadTwoCell
#assert_no_axioms FX1Poly.Polygraph.adjointQuadrupleModeSignature
#assert_no_axioms FX1Poly.Polygraph.quadLabelIndex
#assert_no_axioms FX1Poly.Polygraph.quadIndexWord
#assert_no_axioms FX1Poly.Polygraph.quadL1L2_length
#assert_no_axioms FX1Poly.Polygraph.quadL2L1_length
#assert_no_axioms FX1Poly.Polygraph.quadL2L3_length
#assert_no_axioms FX1Poly.Polygraph.quadL3L2_length
#assert_no_axioms FX1Poly.Polygraph.quadL3L4_length
#assert_no_axioms FX1Poly.Polygraph.quadL4L3_length
#assert_no_axioms FX1Poly.Polygraph.quad_letterOne_ne_letterThree
#assert_no_axioms FX1Poly.Polygraph.quad_letterTwo_ne_letterFour
#assert_no_axioms FX1Poly.Polygraph.quadIndexWord_quadL1L2
#assert_no_axioms FX1Poly.Polygraph.quadIndexWord_quadL2L1
#assert_no_axioms FX1Poly.Polygraph.quadIndexWord_quadL2L3
#assert_no_axioms FX1Poly.Polygraph.quadIndexWord_quadL3L2
#assert_no_axioms FX1Poly.Polygraph.quadIndexWord_quadL3L4
#assert_no_axioms FX1Poly.Polygraph.quadIndexWord_quadL4L3
#assert_no_axioms FX1Poly.Polygraph.quadCupCods_eq_carrierAtThree
#assert_no_axioms FX1Poly.Polygraph.quadCapDoms_eq_carrierAtThree
#assert_no_axioms FX1Poly.Polygraph.fxString_hasAdjointQuadrupleSeed

end FX1PolyAudit
