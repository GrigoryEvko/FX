import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SquiggleOfMatching

/-! # FX1PolyAudit/…/WalkingAdjunction/SquiggleOfMatching — zero-axiom gate (SQ-2 / SQ-3 / SQ-7)

Per-declaration zero-axiom gate for the GLOBAL squiggle populator: the per-index side and open/close
reading (`portSideOfIndex`, `arcOpensAtIndex`), the rectangle boundary order (`rectangleBoundaryOrder`),
the height-function worker and the populator (`squiggleLettersFrom`, `squiggleOfMatching`,
`squiggleOfCell`), the smoke / well-formedness facts, the SQ-3 soundness congruences, the SQ-7 decidable
witness-agreement facts, and the three SQ-9 ledger markers.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.portSideOfIndex
#assert_no_axioms FX1Poly.Polygraph.arcOpensAtIndex
#assert_no_axioms FX1Poly.Polygraph.rectangleBoundaryOrder
#assert_no_axioms FX1Poly.Polygraph.squiggleLettersFrom
#assert_no_axioms FX1Poly.Polygraph.squiggleOfMatching
#assert_no_axioms FX1Poly.Polygraph.squiggleOfCell
#assert_no_axioms FX1Poly.Polygraph.squiggleOfMatching_unit
#assert_no_axioms FX1Poly.Polygraph.squiggleOfMatching_counit
#assert_no_axioms FX1Poly.Polygraph.squiggleOfMatching_throughStrand
#assert_no_axioms FX1Poly.Polygraph.squiggleOfMatching_parallelUnits
#assert_no_axioms FX1Poly.Polygraph.isStrictlyUndulating_squiggleOfMatching_unit
#assert_no_axioms FX1Poly.Polygraph.isStrictlyUndulating_squiggleOfMatching_counit
#assert_no_axioms FX1Poly.Polygraph.isStrictlyUndulating_squiggleOfMatching_throughStrand
#assert_no_axioms FX1Poly.Polygraph.isStrictlyUndulating_squiggleOfMatching_parallelUnits
#assert_no_axioms FX1Poly.Polygraph.squiggleOfCell_congr_of_matchingOf_eq
#assert_no_axioms FX1Poly.Polygraph.squiggleOfCell_congr_of_spine_eq
#assert_no_axioms FX1Poly.Polygraph.squiggleOfCell_eq_of_interchangeFreeStep
#assert_no_axioms FX1Poly.Polygraph.squiggleOfMatching_unit_ne_counit
#assert_no_axioms FX1Poly.Polygraph.squiggleOfMatching_unit_ne_throughStrand
#assert_no_axioms FX1Poly.Polygraph.squiggleOfMatching_unit_ne_parallelUnits
#assert_no_axioms FX1Poly.Polygraph.squiggleOfMatching_throughStrand_ne_counit
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasGlobalSquigglePopulator
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSquiggleMatchingSoundness
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSquiggleMatchingFaithfulness

end FX1PolyAudit
