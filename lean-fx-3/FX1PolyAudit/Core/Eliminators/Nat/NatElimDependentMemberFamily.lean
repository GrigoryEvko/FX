import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Eliminators.Nat.NatElimDependentMemberFamily

/-! # FX1PolyAudit.Core.Eliminators.Nat.NatElimDependentMemberFamily

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Eliminators.Nat.NatElimDependentMemberFamily`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The value-indexed candidate-FAMILY generalization of the keystone: the result candidate is a family
-- `resultCandidateAt : value -> term -> Prop` (morally the candidate of `subst0 motive value`) carrying a
-- reduction-stability conversion `candidateStable`.  The dependent bounded bridge cannot use the fixed-candidate
-- keystone (the recursive predecessor cell lives at `subst0 motive predecessor`, NOT `subst0 motive scrutinee`);
-- this family threads stability at the three structural seams (scrutinee->value, predecessor descent, natSucc
-- congruence), so the bridge instantiates `resultCandidateAt v := IsReducibleMemberAtBounded env bound (subst0
-- motive v)`.  The genuine frontier construction for recursive dependent-eliminator reducibility.
#assert_no_axioms FX1Poly.Core.natElimDependentReducibleMemberFamily

#assert_no_axioms FX1Poly.Core.natRecDependentReducibleMemberFamily

end FX1PolyAudit
