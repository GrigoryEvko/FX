import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingBraid.BraidThreeSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingBraid.BraidThreeSeed — zero-axiom gate (the walking braid `B_3^+` signature + relation)

Per-declaration zero-axiom gate for the walking positive braid `B_3^+ = ⟨σ1, σ2 | σ1σ2σ1 = σ2σ1σ2⟩` seed: the
mode / modality generators, the quiver, the `nil` / `σ1` / `σ2` free 1-cells and the two length-3 braid words,
the degenerate 2-signature and its smokes, and the braid `σ1.σ2.σ1 = σ2.σ1.σ2` 1-cell convertibility with its
law witnesses.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.BraidThreeMode
#assert_no_axioms FX1Poly.Polygraph.BraidThreeModality
#assert_no_axioms FX1Poly.Polygraph.braidThreeGraph
#assert_no_axioms FX1Poly.Polygraph.braidThreeNil
#assert_no_axioms FX1Poly.Polygraph.braidThreeSigma1
#assert_no_axioms FX1Poly.Polygraph.braidThreeSigma2
#assert_no_axioms FX1Poly.Polygraph.braidThreeBraidLeft
#assert_no_axioms FX1Poly.Polygraph.braidThreeBraidRight
#assert_no_axioms FX1Poly.Polygraph.braidThreeModeSignature
#assert_no_axioms FX1Poly.Polygraph.braidThreeSigma1_length
#assert_no_axioms FX1Poly.Polygraph.braidThreeSigma2_length
#assert_no_axioms FX1Poly.Polygraph.braidThreeBraidLeft_length
#assert_no_axioms FX1Poly.Polygraph.braidThreeBraidRight_length
#assert_no_axioms FX1Poly.Polygraph.braidThree_no_two_generators
#assert_no_axioms FX1Poly.Polygraph.BraidThreeOneCellConv
#assert_no_axioms FX1Poly.Polygraph.braidThreeLawHolds
#assert_no_axioms FX1Poly.Polygraph.braidThreeLawWhiskeredHolds

end FX1PolyAudit
