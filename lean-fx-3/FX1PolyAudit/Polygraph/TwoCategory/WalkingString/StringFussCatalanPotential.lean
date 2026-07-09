import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanPotential

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringFussCatalanPotential — zero-axiom gate (FC-3b, piece B)

Per-declaration zero-axiom gate for the COMMUTE potential `p2`: the inversion count (`countLess`, `countInversions`,
`commutePotential`), the core swap-drops-one descent, the lex-priority order + its three descent lemmas, and the
term-level CANCEL / EXTEND / COMMUTE-INTERLEAVE wiring.  Must be free of `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.countLess
#assert_no_axioms FX1Poly.Polygraph.commutePotential
#assert_no_axioms FX1Poly.Polygraph.countInversions_nil
#assert_no_axioms FX1Poly.Polygraph.countInversions_swapAdjacent_dropsOne
#assert_no_axioms FX1Poly.Polygraph.stringLexLt3
#assert_no_axioms FX1Poly.Polygraph.stringLexLt3_of_fst
#assert_no_axioms FX1Poly.Polygraph.stringLexLt3_of_snd
#assert_no_axioms FX1Poly.Polygraph.stringLexLt3_of_thd
#assert_no_axioms FX1Poly.Polygraph.stringLexDescent_cancelF
#assert_no_axioms FX1Poly.Polygraph.stringLexDescent_extend
#assert_no_axioms FX1Poly.Polygraph.stringLexDescent_commute
#assert_no_axioms FX1Poly.Polygraph.fxString_hasCommutePotential
#assert_no_axioms FX1Poly.Polygraph.fxString_hasStaircaseFoldFromPotential

end FX1PolyAudit
