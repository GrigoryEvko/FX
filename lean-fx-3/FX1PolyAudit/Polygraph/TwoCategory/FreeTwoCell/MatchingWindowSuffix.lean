import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingWindowSuffix — zero-axiom gate

Per-declaration zero-axiom gate for the atom layer of the suffix shift: the append/splice/pair-removal
suffix primitives, the cup/cap arity discipline, the per-atom suffix invariant, and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.natListGetAt_append_pastBlock
#assert_no_axioms FX1Poly.Polygraph.natListGetAt_natListInsertAt_pastBlock
#assert_no_axioms FX1Poly.Polygraph.natListGetAt_natListRemoveTwoAt_pastPair
#assert_no_axioms FX1Poly.Polygraph.natListRemoveTwoAt_length
#assert_no_axioms FX1Poly.Polygraph.AtomHasCupOrCapArity
#assert_no_axioms FX1Poly.Polygraph.stepAtom_openWiresSuffix_invariant
#assert_no_axioms FX1Poly.Polygraph.composePath_length
#assert_no_axioms FX1Poly.Polygraph.runMatchingCell_vcomp
#assert_no_axioms FX1Poly.Polygraph.CellHasCupCapGenerators
#assert_no_axioms FX1Poly.Polygraph.runMatchingCell_openWiresSuffix_invariant
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingAtomSuffixShift
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingBlockSuffixShift

end FX1PolyAudit
