import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.LetterInventory

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/LetterInventory — zero-axiom gate

Per-declaration zero-axiom gate for the letter-inventory invariance: the packed letter
entry, the path/atom/trace disciplines with the composite factor kit, the member-atom
projection, the class invariance, and the universe-facing corollary.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.PackedModality
#assert_no_axioms FX1Poly.Polygraph.pathUsesOnly
#assert_no_axioms FX1Poly.Polygraph.pathUsesOnly_composePath_split
#assert_no_axioms FX1Poly.Polygraph.pathUsesOnly_composePath_join
#assert_no_axioms FX1Poly.Polygraph.AtomUsesOnly
#assert_no_axioms FX1Poly.Polygraph.TraceUsesOnly
#assert_no_axioms FX1Poly.Polygraph.traceUsesOnly_projectAtom
#assert_no_axioms FX1Poly.Polygraph.AtomicTraceEquiv.usesOnlyIff
#assert_no_axioms FX1Poly.Polygraph.atomUsesOnly_ofSeed_ofTraceEquiv

end FX1PolyAudit
