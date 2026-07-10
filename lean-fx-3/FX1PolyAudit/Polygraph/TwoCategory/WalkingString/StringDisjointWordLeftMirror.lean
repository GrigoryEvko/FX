import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDisjointWordLeftMirror

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringDisjointWordLeftMirror — zero-axiom gate (FC-3 r5, B3)

Per-declaration zero-axiom gate for the LEFT-of word-indexed disjoint-window factorization, the reversed swap
(existential + consuming forms), the equal-length-distinct-word non-vacuity witness, and the honesty marker.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.spineAtom_contextsFactorLeft_of_disjointWordWindows
#assert_no_axioms FX1Poly.Polygraph.spineAtomSwapLeft_of_disjointWordWindows
#assert_no_axioms FX1Poly.Polygraph.spineAtomSwapLeft_of_wordFactorization
#assert_no_axioms FX1Poly.Polygraph.stringDisjointWordLeftMirror_equalLengthDistinctWord
#assert_no_axioms FX1Poly.Polygraph.fxString_hasDisjointWordLeftMirror

end FX1PolyAudit
