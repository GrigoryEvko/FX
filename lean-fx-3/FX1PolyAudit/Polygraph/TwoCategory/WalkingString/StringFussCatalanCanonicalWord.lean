import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanCanonicalWord

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringFussCatalanCanonicalWord — zero-axiom gate (FC-2 C)

Per-declaration zero-axiom gate for the four Fuss–Catalan insertion modes (CANCEL / EXTEND / COMMUTE / INTERLEAVE),
the fueled CANCEL fold, and the r9-shaped insertion residual.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringCancelSnakeF
#assert_no_axioms FX1Poly.Polygraph.stringCancelSnakeGlo
#assert_no_axioms FX1Poly.Polygraph.stringCancelSnakeGhi
#assert_no_axioms FX1Poly.Polygraph.stringCancelSnakeH
#assert_no_axioms FX1Poly.Polygraph.stringCancelSnakeF_dropsTwo
#assert_no_axioms FX1Poly.Polygraph.stringExtendByIdentity
#assert_no_axioms FX1Poly.Polygraph.stringExtend_opensArc
#assert_no_axioms FX1Poly.Polygraph.stringCommuteDisjoint
#assert_no_axioms FX1Poly.Polygraph.stringInterleaveCrossColour
#assert_no_axioms FX1Poly.Polygraph.stringSnakeStackF
#assert_no_axioms FX1Poly.Polygraph.stringSnakeStackF_generatorCount
#assert_no_axioms FX1Poly.Polygraph.stringSnakeStackF_conv_identity
#assert_no_axioms FX1Poly.Polygraph.StringSnakeInsertionResidual
#assert_no_axioms FX1Poly.Polygraph.stringSnakeInsertionResidual_reflexive
#assert_no_axioms FX1Poly.Polygraph.stringCrossLevel_fc_ne_identityG
#assert_no_axioms FX1Poly.Polygraph.fxString_hasFcInsertionModes
#assert_no_axioms FX1Poly.Polygraph.fxString_hasFcCancelFold
#assert_no_axioms FX1Poly.Polygraph.fxString_hasParallelFcSeparationWitness

end FX1PolyAudit
