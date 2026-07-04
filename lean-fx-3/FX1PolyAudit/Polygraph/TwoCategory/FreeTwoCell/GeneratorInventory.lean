import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.GeneratorInventory

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/GeneratorInventory — zero-axiom gate

Per-declaration zero-axiom gate for the packed-generator inventory invariance: the
packed occurrence structure and projection, the inventory list with its atom-membership
projection, the two membership movers, the class invariance, and the universe-facing
corollary.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.PackedSpineGenerator
#assert_no_axioms FX1Poly.Polygraph.SpineAtom.packedGenerator
#assert_no_axioms FX1Poly.Polygraph.spinePackedGenerators
#assert_no_axioms FX1Poly.Polygraph.spinePackedGenerators_containsAtomGenerator
#assert_no_axioms FX1Poly.Polygraph.listMemSwapHeadsIff
#assert_no_axioms FX1Poly.Polygraph.listMemConsCongrIff
#assert_no_axioms FX1Poly.Polygraph.AtomicTraceEquiv.packedGeneratorMemIff
#assert_no_axioms FX1Poly.Polygraph.packedGenerator_memOfSeed_ofTraceEquiv

end FX1PolyAudit
