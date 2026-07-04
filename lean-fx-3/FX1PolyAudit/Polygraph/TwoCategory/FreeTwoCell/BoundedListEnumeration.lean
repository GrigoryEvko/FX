import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.BoundedListEnumeration

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/BoundedListEnumeration — zero-axiom gate

Per-declaration zero-axiom gate for the generic bounded-length list enumeration: the
one-step conser, the fuel enumerator, the block-membership layer, and the completeness
theorem.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.consEachCandidateOnto
#assert_no_axioms FX1Poly.Polygraph.allListsOfLength
#assert_no_axioms FX1Poly.Polygraph.consEachCandidateOnto_containsCons
#assert_no_axioms FX1Poly.Polygraph.allListsOfLength_containsList

end FX1PolyAudit
