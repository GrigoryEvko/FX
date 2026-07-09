import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanNonCrossing

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringFussCatalanNonCrossing — zero-axiom gate (FC-3b, CUP non-crossing)

Per-declaration zero-axiom gate for the CUP non-crossing (planarity) fold invariance: the old-index reads under
`cupUnmap`, the strict monotonicity on old indices, the non-adjacent-arc-both-old classification, and the CUP case
`stringNonCrossing_stepCup`.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringStepCup_read_oldIndex
#assert_no_axioms FX1Poly.Polygraph.cupUnmap_strictMono
#assert_no_axioms FX1Poly.Polygraph.stringStepCup_arc_bothOld
#assert_no_axioms FX1Poly.Polygraph.stringNonCrossing_stepCup

end FX1PolyAudit
