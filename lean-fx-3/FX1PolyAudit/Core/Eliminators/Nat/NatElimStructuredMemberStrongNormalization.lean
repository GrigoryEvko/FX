import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Eliminators.Nat.NatElimStructuredMemberStrongNormalization

/-! # FX1PolyAudit.Core.Eliminators.Nat.NatElimStructuredMemberStrongNormalization

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Eliminators.Nat.NatElimStructuredMemberStrongNormalization`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.StepStar.natElimCellSpine_isStronglyNormalizing_of_structuredMemberReaching

#assert_no_axioms FX1Poly.Core.StepStar.natElimCellSpine_isStronglyNormalizing_of_structuredMember

#assert_no_axioms FX1Poly.Core.StepStar.natRecCellSpine_isStronglyNormalizing_of_structuredMemberReaching

#assert_no_axioms FX1Poly.Core.StepStar.natRecCellSpine_isStronglyNormalizing_of_structuredMember

end FX1PolyAudit
