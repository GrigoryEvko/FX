import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TaggedSwap

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/TaggedSwap — zero-axiom gate

Per-declaration zero-axiom gate for the occurrence-tagged swap layer: the tagged atom with
its two projections, the seed tagging with its round-trip, the tagged swap and closure, the
ctor-for-ctor atom projections, the tag counter with its transposition and the class-level
count invariant, and the free chain transfer.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.TaggedSpineAtom
#assert_no_axioms FX1Poly.Polygraph.untagSpineAtoms
#assert_no_axioms FX1Poly.Polygraph.spineTagList
#assert_no_axioms FX1Poly.Polygraph.tagSpineAtomsFrom
#assert_no_axioms FX1Poly.Polygraph.untagSpineAtoms_tagSpineAtomsFrom
#assert_no_axioms FX1Poly.Polygraph.TaggedSpineAtomSwap
#assert_no_axioms FX1Poly.Polygraph.TaggedTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.TaggedSpineAtomSwap.untagged
#assert_no_axioms FX1Poly.Polygraph.TaggedTraceEquiv.untagged
#assert_no_axioms FX1Poly.Polygraph.natCount
#assert_no_axioms FX1Poly.Polygraph.natCount_transpose
#assert_no_axioms FX1Poly.Polygraph.TaggedSpineAtomSwap.preservesTagCount
#assert_no_axioms FX1Poly.Polygraph.TaggedTraceEquiv.preservesTagCount
#assert_no_axioms FX1Poly.Polygraph.TaggedTraceEquiv.pathChainedTransfer

end FX1PolyAudit
