import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TaggedReplay

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/TaggedReplay — zero-axiom gate

Per-declaration zero-axiom gate for the certified replay layer: the two length
projections, the certified replay structure and function, the tag-order enumeration with
its completeness, and the candidate class enumeration with its unconditional soundness
half.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.spineTagList_length
#assert_no_axioms FX1Poly.Polygraph.untagSpineAtoms_length
#assert_no_axioms FX1Poly.Polygraph.TaggedReplay
#assert_no_axioms FX1Poly.Polygraph.replayTagOrder?
#assert_no_axioms FX1Poly.Polygraph.consEachTagOnto
#assert_no_axioms FX1Poly.Polygraph.allTagOrdersOfLength
#assert_no_axioms FX1Poly.Polygraph.consEachTagOnto_containsCons
#assert_no_axioms FX1Poly.Polygraph.allTagOrdersOfLength_containsOrder
#assert_no_axioms FX1Poly.Polygraph.classEnumerationCandidate
#assert_no_axioms FX1Poly.Polygraph.classEnumerationCandidate_isSound

end FX1PolyAudit
