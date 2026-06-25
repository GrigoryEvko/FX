import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Eliminators.List.ListElimStructuredMemberStrongNormalization

/-! # FX1PolyAudit.Core.Eliminators.List.ListElimStructuredMemberStrongNormalization

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Eliminators.List.ListElimStructuredMemberStrongNormalization`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- FTGEN-13.1: the residue-free membership-based listElim cell SN — the binary recursor's structured-member combine
-- (app-spine cons-ι), completing the recursive-eliminator combine family (natElim/natRec/listElim).
#assert_no_axioms FX1Poly.Core.StepStar.listElimCellSpine_isStronglyNormalizing_of_structuredMemberReaching

#assert_no_axioms FX1Poly.Core.StepStar.listElimCellSpine_isStronglyNormalizing_of_structuredMember

end FX1PolyAudit
