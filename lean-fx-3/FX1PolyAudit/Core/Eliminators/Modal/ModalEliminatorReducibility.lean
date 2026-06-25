import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Eliminators.Modal.ModalEliminatorReducibility

/-! # FX1PolyAudit.Core.Eliminators.Modal.ModalEliminatorReducibility

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Eliminators.Modal.ModalEliminatorReducibility`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The reflection direction + reducibility-framing completing modElim/subsume reducibility.
-- isStronglyNormalizing_child_of_oneChildCong is the reusable converse of the forward one-child-cong SN
-- closure (SN reflects through a congruence wrapper).  modElim/subsume being non-neutral with no iota rule (by
-- design), the SN candidate is the ceiling: the operators send candidate members to SN-candidate members; the
-- box-member capstone ties modElim back to modIntroCanonicalFormsCandidate.
#assert_no_axioms FX1Poly.Core.StepStar.isStronglyNormalizing_child_of_oneChildCong

#assert_no_axioms FX1Poly.Core.StepStar.modElim_isStronglyNormalizing_child_of_parent

#assert_no_axioms FX1Poly.Core.StepStar.subsume_isStronglyNormalizing_child_of_parent

#assert_no_axioms FX1Poly.Core.StepStar.modElim_isStronglyNormalizing_iff

#assert_no_axioms FX1Poly.Core.StepStar.subsume_isStronglyNormalizing_iff

#assert_no_axioms FX1Poly.Core.StepStar.modElim_isStronglyNormalizing_of_candidateMember

#assert_no_axioms FX1Poly.Core.StepStar.subsume_isStronglyNormalizing_of_candidateMember

#assert_no_axioms FX1Poly.Core.StepStar.modElim_isStronglyNormalizing_ofBoxMember

end FX1PolyAudit
