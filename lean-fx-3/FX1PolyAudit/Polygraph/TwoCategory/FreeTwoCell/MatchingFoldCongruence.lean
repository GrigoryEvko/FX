import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFoldCongruence

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingFoldCongruence — zero-axiom gate

Per-declaration zero-axiom gate for the wire/partition split of the matching fold: the cup projections, the
cup/cap arity characterizations, the wire-half congruences (per atom / spine / cell), the partition-half
congruences with the loops accumulator-swap law, and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stepCup_openWires
#assert_no_axioms FX1Poly.Polygraph.stepCup_nextFresh
#assert_no_axioms FX1Poly.Polygraph.stepCup_links
#assert_no_axioms FX1Poly.Polygraph.stepCup_loops
#assert_no_axioms FX1Poly.Polygraph.stepAtom_ofCupArity
#assert_no_axioms FX1Poly.Polygraph.stepAtom_ofCapArity
#assert_no_axioms FX1Poly.Polygraph.stepAtom_wireView_congr
#assert_no_axioms FX1Poly.Polygraph.processSpine_wireView_congr
#assert_no_axioms FX1Poly.Polygraph.runMatchingCell_wireView_congr
#assert_no_axioms FX1Poly.Polygraph.stepAtom_partitionView_congr
#assert_no_axioms FX1Poly.Polygraph.processSpine_partitionView_congr
#assert_no_axioms FX1Poly.Polygraph.runMatchingCell_partitionView_congr
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingFoldWirePartitionSplit

end FX1PolyAudit
