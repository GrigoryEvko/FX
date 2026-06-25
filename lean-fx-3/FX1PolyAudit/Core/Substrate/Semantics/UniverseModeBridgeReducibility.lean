import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Substrate.Semantics.UniverseModeBridgeReducibility

/-! # FX1PolyAudit.Core.Substrate.Semantics.UniverseModeBridgeReducibility

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Substrate.Semantics.UniverseModeBridgeReducibility`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The 2LTT universe-mode bridge twin of the modal-eliminator reducibility.  The lift (one child) + lower
-- (two children: outer + cofibrancy) are congruence-only/non-neutral with no beta+iota iota-rule (their
-- lower(lift x) collapse is not in the current substrate), so the SN candidate is the ceiling.  The lower's
-- two child reflections each slice the two-child operator into a one-child congruence wrapper, reusing the
-- generic isStronglyNormalizing_child_of_oneChildCong (the cofibrancy slice threads StepChildren.there past the
-- held outer child, as in listCons's tail projection).  Biconditionals + candidate-framing complete the picture.
#assert_no_axioms FX1Poly.Core.StepStar.liftInnerToOuter_isStronglyNormalizing_child_of_parent

#assert_no_axioms FX1Poly.Core.StepStar.lowerOuterToInner_outer_isStronglyNormalizing_of_parent

#assert_no_axioms FX1Poly.Core.StepStar.lowerOuterToInner_cofibrancy_isStronglyNormalizing_of_parent

#assert_no_axioms FX1Poly.Core.StepStar.liftInnerToOuter_isStronglyNormalizing_iff

#assert_no_axioms FX1Poly.Core.StepStar.lowerOuterToInner_isStronglyNormalizing_iff

#assert_no_axioms FX1Poly.Core.StepStar.liftInnerToOuter_isStronglyNormalizing_of_candidateMember

#assert_no_axioms FX1Poly.Core.StepStar.lowerOuterToInner_isStronglyNormalizing_of_candidateMembers

end FX1PolyAudit
