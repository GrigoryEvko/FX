import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationReflection

/-! # FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationReflection

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationReflection`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- genFormationPi codomain-SN extraction: the relation-agnostic pure-SN binder reconciliation, the
-- substitution-algebra core of openBodyOfConsSubstMember.  SN of the lifted-substitution body from SN of its
-- cons-instantiation (binder-split keystone + ofSubst0Body); it mentions no reducibility relation, so the fuel
-- (IsReducibleMemberAt) and denote (IsReducibleMemberAtDenote) routes both reduce the codomain-under-binder
-- SN obligation to this one fact once their CR1 supplies the member's SN.
#assert_no_axioms FX1Poly.Core.IsStronglyNormalizing.openBodyOfConsSubst

end FX1PolyAudit
