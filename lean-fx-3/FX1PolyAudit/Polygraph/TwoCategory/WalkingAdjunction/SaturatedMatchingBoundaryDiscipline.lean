import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingBoundaryDiscipline

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/SaturatedMatchingBoundaryDiscipline —
zero-axiom gate

Per-declaration zero-axiom gate for the boundary-disciplined saturated soundness: the universal
walking-adjunction cup/cap discipline, the re-gated saturated soundness, the keystone assembly,
and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.cellHasCupCapGenerators_ofAdjunctionSignature
#assert_no_axioms FX1Poly.Polygraph.saturatedConv_matchingOf_eq_ofBoundaryDiscipline
#assert_no_axioms FX1Poly.Polygraph.saturatedMatchingCanonicalization_ofBoundaryDiscipline
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSaturatedSoundnessOnBoundaryDiscipline

end FX1PolyAudit
