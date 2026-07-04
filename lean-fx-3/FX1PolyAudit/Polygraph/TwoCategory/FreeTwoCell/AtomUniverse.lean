import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomUniverse

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/AtomUniverse — zero-axiom gate

Per-declaration zero-axiom gate for the atom universe: the three product layers, the
two membership layers, and the universe-completeness capstone.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.atomCandidatesOverLefts
#assert_no_axioms FX1Poly.Polygraph.atomCandidatesForGenerator
#assert_no_axioms FX1Poly.Polygraph.atomUniverse
#assert_no_axioms FX1Poly.Polygraph.atomCandidatesOverLefts_containsMk
#assert_no_axioms FX1Poly.Polygraph.atomUniverse_containsAtom
#assert_no_axioms FX1Poly.Polygraph.memberAtom_mem_atomUniverse

end FX1PolyAudit
