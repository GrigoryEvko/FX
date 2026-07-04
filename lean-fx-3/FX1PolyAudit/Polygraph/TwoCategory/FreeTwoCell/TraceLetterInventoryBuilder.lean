import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TraceLetterInventoryBuilder

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/TraceLetterInventoryBuilder — zero-axiom gate

Per-declaration zero-axiom gate for the seed letter-inventory builder: the three
collectors, the three monotonicity lemmas, the three self-containment layers, and the
concrete universe-facing member fact.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.pathLetters
#assert_no_axioms FX1Poly.Polygraph.atomLetters
#assert_no_axioms FX1Poly.Polygraph.traceLetterInventory
#assert_no_axioms FX1Poly.Polygraph.pathUsesOnly_monotone
#assert_no_axioms FX1Poly.Polygraph.atomUsesOnly_monotone
#assert_no_axioms FX1Poly.Polygraph.traceUsesOnly_monotone
#assert_no_axioms FX1Poly.Polygraph.pathUsesOnly_ownLetters
#assert_no_axioms FX1Poly.Polygraph.atomUsesOnly_ownLetters
#assert_no_axioms FX1Poly.Polygraph.traceUsesOnly_ownInventory
#assert_no_axioms FX1Poly.Polygraph.memberAtomUsesOnly_seedInventory

end FX1PolyAudit
