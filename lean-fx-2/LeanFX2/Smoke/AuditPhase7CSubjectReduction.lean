import LeanFX2.Term.SubjectReduction

/-! Phase 7.C — Subject reduction at closed types audit.

For each closed type (`Ty.nat`, `Ty.unit`, `Ty.bool`), `Step`
preserves the source type — extended to `StepStar` chains.

The substitution-raw-invariance helpers handle the dep-β case
where the source type is `someType.subst0 _ raw` (the raw is
irrelevant when the result is a closed type, since closed types
are fixed points of `Ty.subst`).
-/

namespace LeanFX2.SmokePhase7CSubjectReduction

#print axioms LeanFX2.Ty.subst0_raw_invariance_nat
#print axioms LeanFX2.Ty.subst0_raw_invariance_unit
#print axioms LeanFX2.Ty.subst0_raw_invariance_bool
#print axioms LeanFX2.Step.preserves_ty_nat
#print axioms LeanFX2.Step.preserves_ty_unit
#print axioms LeanFX2.Step.preserves_ty_bool
#print axioms LeanFX2.StepStar.preserves_ty_nat
#print axioms LeanFX2.StepStar.preserves_ty_unit
#print axioms LeanFX2.StepStar.preserves_ty_bool
#print axioms LeanFX2.StepStar.natSucc_lift
#print axioms LeanFX2.StepStar.natSucc_lift_general

end LeanFX2.SmokePhase7CSubjectReduction
