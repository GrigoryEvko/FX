import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringCommuteWordFactorData

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringCommuteWordFactorData — zero-axiom gate (FC-3 r5, B2)

Per-declaration zero-axiom gate for the Type-valued COMMUTE factorization data (both directions): the RIGHT-of and
LEFT-of builders, the non-vacuity witness, and the honesty marker.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.disjointWordWindowFactorData_of_disjointWordWindows
#assert_no_axioms FX1Poly.Polygraph.disjointWordWindowFactorDataLeft_of_disjointWordWindows
#assert_no_axioms FX1Poly.Polygraph.stringCommuteWordFactorData_equalLengthDistinctWord
#assert_no_axioms FX1Poly.Polygraph.fxString_hasCommuteWordFactorData

end FX1PolyAudit
