import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDisjointWordSwap

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringDisjointWordSwap — zero-axiom gate (FC-3 r4, B1/B2)

Per-declaration zero-axiom gate for the realized word-indexed swap and its word-chain preservation: the swap
producer, the chain-preservation theorem, the both-bricks non-vacuity witness, and the two honesty markers.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.spineAtomSwap_of_disjointWordWindows
#assert_no_axioms FX1Poly.Polygraph.spineBoundaryWordChained_swappedPair
#assert_no_axioms FX1Poly.Polygraph.stringDisjointWordSwap_equalLengthDistinctWord
#assert_no_axioms FX1Poly.Polygraph.fxString_hasDisjointWordSwap
#assert_no_axioms FX1Poly.Polygraph.fxString_hasWordSwapChainPreservation

end FX1PolyAudit
