import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanGeneric

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringFussCatalanGeneric — zero-axiom gate (FC-2 B)

Per-declaration zero-axiom gate for the colour-generic Fuss–Catalan parameterization, the generic `k`-colour
number, the generic mode-table facts, and the two-colour instance bridges.  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.fussCatalanNumberK
#assert_no_axioms FX1Poly.Polygraph.fussCatalanNumberK_two_eq
#assert_no_axioms FX1Poly.Polygraph.fussCatalanNumberK_one_values
#assert_no_axioms FX1Poly.Polygraph.fussCatalanNumberK_two_values
#assert_no_axioms FX1Poly.Polygraph.fussCatalanNumberK_three_values
#assert_no_axioms FX1Poly.Polygraph.AdjointStringColouring
#assert_no_axioms FX1Poly.Polygraph.adjointTripleColouring
#assert_no_axioms FX1Poly.Polygraph.colouring_capWord_distinctFromCup
#assert_no_axioms FX1Poly.Polygraph.colouring_interleaveFree
#assert_no_axioms FX1Poly.Polygraph.colouring_arcColour_faithful
#assert_no_axioms FX1Poly.Polygraph.adjointTripleColouring_isCupWordOrdered
#assert_no_axioms FX1Poly.Polygraph.adjointTripleColouring_isCapWordOrdered
#assert_no_axioms FX1Poly.Polygraph.adjointTripleColouring_arcColour
#assert_no_axioms FX1Poly.Polygraph.adjointTripleColouring_capWord_distinctFromCup
#assert_no_axioms FX1Poly.Polygraph.fxString_hasColourGenericParameterization
#assert_no_axioms FX1Poly.Polygraph.fxString_hasGenericFussCatalanNumber
#assert_no_axioms FX1Poly.Polygraph.fxString_hasNormalFormDesignLock

end FX1PolyAudit
