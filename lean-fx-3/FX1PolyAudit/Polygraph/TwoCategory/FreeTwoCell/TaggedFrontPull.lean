import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TaggedFrontPull

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/TaggedFrontPull — zero-axiom gate

Per-declaration zero-axiom gate for the certified pull-by-tag extraction: the two
recognizer-certificate lifts into the tagged swap, the certified pull structure, and the
computable pull itself.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.AdjacentSwapWitness.toTaggedSwap
#assert_no_axioms FX1Poly.Polygraph.ReverseAdjacentSwapWitness.toTaggedSwap
#assert_no_axioms FX1Poly.Polygraph.TaggedFrontPull
#assert_no_axioms FX1Poly.Polygraph.pullTagToFront?

end FX1PolyAudit
