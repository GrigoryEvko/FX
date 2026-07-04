import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.BoundedPathEnumeration

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/BoundedPathEnumeration — zero-axiom gate

Per-declaration zero-axiom gate for the bounded path enumeration: the nil candidate,
the per-letter cons candidates, the fuel enumerator, the two membership layers, and
the completeness theorem.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.nilPathCandidates
#assert_no_axioms FX1Poly.Polygraph.consEdgeCandidates
#assert_no_axioms FX1Poly.Polygraph.enumeratePathsUpTo
#assert_no_axioms FX1Poly.Polygraph.nilPath_mem_nilPathCandidates
#assert_no_axioms FX1Poly.Polygraph.consEdgeCandidates_containsCons
#assert_no_axioms FX1Poly.Polygraph.enumeratePathsUpTo_containsPath

end FX1PolyAudit
