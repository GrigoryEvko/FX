import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Eliminators.Nat.NatElimReductTrackingStrongNormalization

/-! # FX1PolyAudit.Core.Eliminators.Nat.NatElimReductTrackingStrongNormalization

Zero-axiom audit shard mirroring kernel module
`FX1Poly.Core.Eliminators.Nat.NatElimReductTrackingStrongNormalization` — the six reduct-tracking
`natElim` / `natRec` cell-SN theorems (the reachability engines, the member-discharged connectors, and the
scrutinee-reducing roots).  This shard closes a pre-existing audit gap: the module carried no per-declaration
gate file.

Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms
  FX1Poly.Core.StepStar.natElimCellSpine_isStronglyNormalizing_of_normalScrutinee_viaReachability

#assert_no_axioms
  FX1Poly.Core.StepStar.natRecCellSpine_isStronglyNormalizing_of_normalScrutinee_viaReachability

#assert_no_axioms
  FX1Poly.Core.StepStar.natElimCellSpine_isStronglyNormalizing_of_normalScrutinee_fromOriginalContractumSN

#assert_no_axioms
  FX1Poly.Core.StepStar.natRecCellSpine_isStronglyNormalizing_of_normalScrutinee_fromOriginalContractumSN

#assert_no_axioms
  FX1Poly.Core.StepStar.natElimCellSpine_isStronglyNormalizing_of_scrutineeReducing_fromOriginalContractumSN

#assert_no_axioms
  FX1Poly.Core.StepStar.natRecCellSpine_isStronglyNormalizing_of_scrutineeReducing_fromOriginalContractumSN

end FX1PolyAudit
