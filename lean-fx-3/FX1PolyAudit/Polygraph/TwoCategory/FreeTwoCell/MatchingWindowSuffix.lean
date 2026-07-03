import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingWindowSuffix — zero-axiom gate

Per-declaration zero-axiom gate for the atom layer of the suffix shift: the append/splice/pair-removal
suffix primitives, the cup/cap arity discipline, the per-atom suffix invariant, and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.natListGetAt_append_pastBlock
#assert_no_axioms FX1Poly.Tier0.natListGetAt_natListInsertAt_pastBlock
#assert_no_axioms FX1Poly.Tier0.natListGetAt_natListRemoveTwoAt_pastPair
#assert_no_axioms FX1Poly.Tier0.natListRemoveTwoAt_length
#assert_no_axioms FX1Poly.Tier0.AtomHasCupOrCapArity
#assert_no_axioms FX1Poly.Tier0.stepAtom_openWiresSuffix_invariant
#assert_no_axioms FX1Poly.Tier0.fxMode_hasMatchingAtomSuffixShift

end FX1PolyAudit
