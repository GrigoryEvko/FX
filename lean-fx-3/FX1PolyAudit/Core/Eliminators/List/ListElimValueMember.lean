import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Eliminators.List.ListElimValueMember

/-! # FX1PolyAudit.Core.Eliminators.List.ListElimValueMember

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Eliminators.List.ListElimValueMember`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Value-case listElim reducibility with the recursor-SN obligation discharged (the twin of
-- natElimValueMember): CR1 + CR2 + consBranchTerminates replace the bespoke redexStronglyNormalizing, via the
-- listElim scrutinee-fixed cell-SN recursor.  The cons branch is the three-deep app (head + tail), recovered by
-- two childCons injection drills; otherwise identical to the Nat recursor discharge.
#assert_no_axioms FX1Poly.Core.listElimNormalScrutineeCellStronglyNormalizing

#assert_no_axioms FX1Poly.Core.listElimValueMember

end FX1PolyAudit
