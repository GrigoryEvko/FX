import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.DisjointWindowSwap

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/DisjointWindowSwap — zero-axiom gate

Per-declaration zero-axiom gate for the realized disjoint-window swap: the adjacent
transposition fired from the whisker factorization, plus the chain-preservation invariant
that lets the peel's bubbling iterate.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.adjunctionSpineAtomSwap_of_disjointWindows
#assert_no_axioms FX1Poly.Polygraph.adjunctionSwappedPair_isBoundaryChained
#assert_no_axioms FX1Poly.Polygraph.adjunctionSpineAtomSwapLeft_of_disjointWindows

end FX1PolyAudit
