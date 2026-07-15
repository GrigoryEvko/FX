import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Eliminators.Nat.NatElimNumeralStrongNormalization

/-! # FX1PolyAudit.Core.Eliminators.Nat.NatElimNumeralStrongNormalization

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Eliminators.Nat.NatElimNumeralStrongNormalization`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.StepStar.natElimCellSpine_isStronglyNormalizing_of_normalScrutinee

#assert_no_axioms FX1Poly.Core.StepStar.natSuccCell_inj

#assert_no_axioms FX1Poly.Core.StepStar.natShapedCellSpine_isStronglyNormalizing_of_natValueScrutinee

#assert_no_axioms FX1Poly.Core.StepStar.natElimCellSpine_isStronglyNormalizing_of_natValueScrutinee

#assert_no_axioms FX1Poly.Core.StepStar.natRecCellSpine_isStronglyNormalizing_of_normalScrutinee

#assert_no_axioms FX1Poly.Core.StepStar.natRecCellSpine_isStronglyNormalizing_of_natValueScrutinee

end FX1PolyAudit
