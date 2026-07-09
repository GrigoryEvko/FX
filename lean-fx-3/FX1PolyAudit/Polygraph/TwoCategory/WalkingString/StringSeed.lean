import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringSeed — zero-axiom gate (the walking-adjoint-triple seed)

Per-declaration zero-axiom gate for the walking-adjoint-triple seed: the quiver, the four endo-paths, the four
generating 2-cells, the mode signature, and the freeness smokes.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.adjointTripleGraph
#assert_no_axioms FX1Poly.Polygraph.stringFG
#assert_no_axioms FX1Poly.Polygraph.stringGF
#assert_no_axioms FX1Poly.Polygraph.stringGH
#assert_no_axioms FX1Poly.Polygraph.stringHG
#assert_no_axioms FX1Poly.Polygraph.StringTwoCell
#assert_no_axioms FX1Poly.Polygraph.adjointTripleModeSignature
#assert_no_axioms FX1Poly.Polygraph.stringFG_length
#assert_no_axioms FX1Poly.Polygraph.stringGF_length
#assert_no_axioms FX1Poly.Polygraph.stringGH_length
#assert_no_axioms FX1Poly.Polygraph.stringHG_length
#assert_no_axioms FX1Poly.Polygraph.string_left_ne_coLeft

end FX1PolyAudit
