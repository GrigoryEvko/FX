import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingCyclicThree.CyclicThreeDecision

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingCyclicThree.CyclicThreeDecision — zero-axiom gate (the walking cyclic-3 `s.s.s = id` decision)

Per-declaration zero-axiom gate for the walking cyclic-3 1-cell word problem: the seed (mode / modality
generators, quiver, `id` / `s` / `s.s` / `s.s.s` free 1-cells, the degenerate 2-signature), the `s.s.s = id`
1-cell convertibility and its law witnesses, the `Z/3` residue type + arithmetic + manual `DecidableEq`, the
`Z/3` model and its equations, SOUNDNESS, the three-element normal form, COMPLETENESS, the total decider and its
instance, the non-vacuity witnesses / decider smokes, and the established marker.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.CyclicThreeMode
#assert_no_axioms FX1Poly.Polygraph.CyclicThreeModality
#assert_no_axioms FX1Poly.Polygraph.cyclicThreeGraph
#assert_no_axioms FX1Poly.Polygraph.cyclicThreeNil
#assert_no_axioms FX1Poly.Polygraph.cyclicThreeS
#assert_no_axioms FX1Poly.Polygraph.cyclicThreeSS
#assert_no_axioms FX1Poly.Polygraph.cyclicThreeSSS
#assert_no_axioms FX1Poly.Polygraph.cyclicThreeModeSignature
#assert_no_axioms FX1Poly.Polygraph.cyclicThreeS_length
#assert_no_axioms FX1Poly.Polygraph.cyclicThreeSSS_length
#assert_no_axioms FX1Poly.Polygraph.cyclicThree_no_two_generators
#assert_no_axioms FX1Poly.Polygraph.CyclicThreeOneCellConv
#assert_no_axioms FX1Poly.Polygraph.cyclicThreeLawHolds
#assert_no_axioms FX1Poly.Polygraph.cyclicThreeLawWhiskeredHolds
#assert_no_axioms FX1Poly.Polygraph.CyclicThreeResidue
#assert_no_axioms FX1Poly.Polygraph.shiftResidue
#assert_no_axioms FX1Poly.Polygraph.shiftResidueTripleIsIdentity
#assert_no_axioms FX1Poly.Polygraph.cyclicThreeResidueDecEq
#assert_no_axioms FX1Poly.Polygraph.instDecidableEqCyclicThreeResidue
#assert_no_axioms FX1Poly.Polygraph.natMod3
#assert_no_axioms FX1Poly.Polygraph.cyclicThreeResidueOf
#assert_no_axioms FX1Poly.Polygraph.cyclicThreeResidueOf_nil
#assert_no_axioms FX1Poly.Polygraph.cyclicThreeResidueOf_cons
#assert_no_axioms FX1Poly.Polygraph.cyclicThreeResidueOf_cyclicThreeS
#assert_no_axioms FX1Poly.Polygraph.cyclicThreeResidueOf_cyclicThreeSS
#assert_no_axioms FX1Poly.Polygraph.cyclicThreeResidueOf_cyclicThreeSSS
#assert_no_axioms FX1Poly.Polygraph.cyclicThreeResidueOf_congr_of_conv
#assert_no_axioms FX1Poly.Polygraph.residueNF
#assert_no_axioms FX1Poly.Polygraph.consCongr_residueNF
#assert_no_axioms FX1Poly.Polygraph.conv_toResidueNF_ofLength
#assert_no_axioms FX1Poly.Polygraph.conv_toResidueNF
#assert_no_axioms FX1Poly.Polygraph.cyclicThreeOneCellConv_of_residue_eq
#assert_no_axioms FX1Poly.Polygraph.decideCyclicThreeOneCellConv
#assert_no_axioms FX1Poly.Polygraph.instDecidableCyclicThreeOneCellConv
#assert_no_axioms FX1Poly.Polygraph.cyclicThreeConv_triple_nil
#assert_no_axioms FX1Poly.Polygraph.cyclicThreeNotConv_single_nil
#assert_no_axioms FX1Poly.Polygraph.cyclicThreeNotConv_double_nil
#assert_no_axioms FX1Poly.Polygraph.cyclicThreeDecide_true_on_triple
#assert_no_axioms FX1Poly.Polygraph.cyclicThreeDecide_false_on_single
#assert_no_axioms FX1Poly.Polygraph.cyclicThreeDecide_false_on_double
#assert_no_axioms FX1Poly.Polygraph.fxCyclicThree_hasOneCellWordProblemDecided

end FX1PolyAudit
