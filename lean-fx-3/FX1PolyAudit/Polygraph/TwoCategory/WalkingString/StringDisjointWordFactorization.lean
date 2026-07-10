import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDisjointWordFactorization

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringDisjointWordFactorization — zero-axiom gate (FC-3 r4, B1)

Per-declaration zero-axiom gate for the word-indexed disjoint-window whisker factorization: the shared-word
extractor, the factorization theorem, the equal-length-distinct-word non-vacuity witness, and the honesty
marker.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.spineBoundaryWordChained_pairSharedWord
#assert_no_axioms FX1Poly.Polygraph.spineAtom_contextsFactor_of_disjointWordWindows
#assert_no_axioms FX1Poly.Polygraph.stringDisjointWordFactorization_equalLengthDistinctWord
#assert_no_axioms FX1Poly.Polygraph.fxString_hasDisjointWordFactorization

end FX1PolyAudit
