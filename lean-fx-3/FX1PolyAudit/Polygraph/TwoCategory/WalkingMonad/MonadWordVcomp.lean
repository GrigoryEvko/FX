import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWordVcomp

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadWordVcomp — zero-axiom gate (vertical word mult)

Per-declaration zero-axiom gate for the vertical word multiplicativity `wordMul_vcomp` (the sole open
`normalizeCell` case) and its supporting infrastructure: the cons-only sum / take / drop primitives, the
domain-path bridge, the word-gadget collapse, the block-sum composition `composeCounts`, and the assembled
`vcomp` normalization + the completeness FLIP.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.MonadSaturatedTwoCellConv.ofEq
#assert_no_axioms FX1Poly.Polygraph.natAddSubCancelLeft
#assert_no_axioms FX1Poly.Polygraph.consAppend_consTake_consDrop
#assert_no_axioms FX1Poly.Polygraph.consTake_length_of_le
#assert_no_axioms FX1Poly.Polygraph.consDrop_length
#assert_no_axioms FX1Poly.Polygraph.listSum_consAppend
#assert_no_axioms FX1Poly.Polygraph.countsDomainPath_eq_monadTPower_listSum
#assert_no_axioms FX1Poly.Polygraph.countsDomainPath_length_eq_listSum
#assert_no_axioms FX1Poly.Polygraph.gadgetTailCollapse
#assert_no_axioms FX1Poly.Polygraph.wordGadgetCollapse
#assert_no_axioms FX1Poly.Polygraph.consTake_consAppend
#assert_no_axioms FX1Poly.Polygraph.consDrop_consAppend
#assert_no_axioms FX1Poly.Polygraph.composeCounts_length
#assert_no_axioms FX1Poly.Polygraph.listSum_composeCounts
#assert_no_axioms FX1Poly.Polygraph.wordMul_vcomp_hmid
#assert_no_axioms FX1Poly.Polygraph.wordMul_vcomp_hdom
#assert_no_axioms FX1Poly.Polygraph.fxMonad_hasWordGadgetCollapseAndComposeCounts
#assert_no_axioms FX1Poly.Polygraph.fxMonad_hasVcompWordMultiplicativity

end FX1PolyAudit
