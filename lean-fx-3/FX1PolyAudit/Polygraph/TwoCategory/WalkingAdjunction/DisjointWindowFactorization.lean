import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.DisjointWindowFactorization

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/DisjointWindowFactorization — zero-axiom gate

Per-declaration zero-axiom gate for the disjoint-window whisker factorizations (right-of and
mirrored left-of): the inert middle path with both context decompositions and the gap-length pin.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.adjunctionSpineAtom_contextsFactor_of_disjointWindows
#assert_no_axioms FX1Poly.Polygraph.adjunctionSpineAtom_contextsFactorLeft_of_disjointWindows

end FX1PolyAudit
