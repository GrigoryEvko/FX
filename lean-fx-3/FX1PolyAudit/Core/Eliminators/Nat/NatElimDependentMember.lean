import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Eliminators.Nat.NatElimDependentMember

/-! # FX1PolyAudit.Core.Eliminators.Nat.NatElimDependentMember

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Eliminators.Nat.NatElimDependentMember`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- DEP-NAT-CORE: the FULL recursive dependent member — the scrutinee arrives only as a `dataTaitCandidate
-- IsNatStructured` member (not already a value), landing the cell in an arbitrary motive candidate.  Wraps the
-- shared `dependentDataEliminatorMemberFromValueDispatch` skeleton in a STRUCTURAL recursion on the structured
-- value the scrutinee reaches: the `natSucc`-ι's substituted reduct (which needs the eliminator cell AT the
-- predecessor) is discharged from the OUTER inductive hypothesis, realigned by confluence + the `natSucc`
-- congruence inversion.  This is the recursive-eliminator analogue of `boolElimDependentReducibleMember`, the
-- keystone of the dependent Nat fundamental theorem.
#assert_no_axioms FX1Poly.Core.natElimDependentReducibleMember

#assert_no_axioms FX1Poly.Core.natRecDependentReducibleMember

end FX1PolyAudit
