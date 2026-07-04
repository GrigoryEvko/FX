import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicMove

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/AtomicMove — zero-axiom gate

Per-declaration zero-axiom gate for the atom move lemma — one generator atom past an
arbitrary cell's spine block inside the atomic swap closure.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.AtomicTraceEquiv.moveGeneratorPastCell

end FX1PolyAudit
