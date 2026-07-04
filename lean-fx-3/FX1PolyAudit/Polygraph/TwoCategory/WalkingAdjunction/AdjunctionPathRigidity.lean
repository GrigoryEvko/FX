import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionPathRigidity

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/AdjunctionPathRigidity — zero-axiom gate

Per-declaration zero-axiom gate for seed path rigidity: modality uniqueness, the heterogeneous
target-mode determination, and the parallel path equality.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.adjunctionModality_unique
#assert_no_axioms FX1Poly.Polygraph.adjunctionPathTargets_eq_of_length_eq
#assert_no_axioms FX1Poly.Polygraph.adjunctionPath_eq_of_length_eq

end FX1PolyAudit
