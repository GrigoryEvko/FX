import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Eliminators.Nat.NatShapedRecursorCellStrongNormalization

/-! # FX1PolyAudit.Core.Eliminators.Nat.NatShapedRecursorCellStrongNormalization

Zero-axiom audit shard mirroring kernel module
`FX1Poly.Core.Eliminators.Nat.NatShapedRecursorCellStrongNormalization`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.StepStar.NatShapedSpineInversion

#assert_no_axioms FX1Poly.Core.StepStar.NatShapedContractumCongruence

#assert_no_axioms FX1Poly.Core.StepStar.natShapedCellSpine_isStronglyNormalizing_of_normalScrutinee

#assert_no_axioms
  FX1Poly.Core.StepStar.natShapedCellSpine_isStronglyNormalizing_of_normalScrutinee_viaReachability

#assert_no_axioms
  FX1Poly.Core.StepStar.natShapedCellSpine_isStronglyNormalizing_of_scrutineeReducing_fromOriginalContractumSN

end FX1PolyAudit
