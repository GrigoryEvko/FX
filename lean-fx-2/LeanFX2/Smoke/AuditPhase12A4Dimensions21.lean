import LeanFX2.Graded.Dimensions21

/-! # AuditPhase12A4Dimensions21 — D5.4 twenty-one dimension registry

The D5.4 registry must expose all twenty-one FX dimension slots without
collapsing their algebraic structure.  Semiring dimensions feed
`GradeVector`; join-only dimensions feed `JoinGradeVector`; structural
dimensions are registered as slots and remain kernel typing data.

Every declaration listed must report "does not depend on any axioms".
-/

#print axioms LeanFX2.Graded.DimensionSlot
#print axioms LeanFX2.Graded.DimensionAlgebraKind
#print axioms LeanFX2.Graded.DimensionSlot.number
#print axioms LeanFX2.Graded.DimensionSlot.displayName
#print axioms LeanFX2.Graded.DimensionSlot.algebraKind
#print axioms LeanFX2.Graded.allDimensionSlots
#print axioms LeanFX2.Graded.allDimensionSlots_length

#print axioms LeanFX2.Graded.JoinDimension
#print axioms LeanFX2.Graded.JoinGradeVector
#print axioms LeanFX2.Graded.JoinGradeVector.bottom
#print axioms LeanFX2.Graded.JoinGradeVector.join
#print axioms LeanFX2.Graded.JoinGradeVector.le
#print axioms LeanFX2.Graded.JoinGradeVector.le_refl
#print axioms LeanFX2.Graded.JoinGradeVector.le_trans
#print axioms LeanFX2.Graded.JoinGradeVector.bottom_le
#print axioms LeanFX2.Graded.JoinGradeVector.le_join_left
#print axioms LeanFX2.Graded.JoinGradeVector.le_join_right

#print axioms LeanFX2.Graded.SemiringDimensionEntry
#print axioms LeanFX2.Graded.JoinDimensionEntry
#print axioms LeanFX2.Graded.StructuralDimensionEntry

#print axioms LeanFX2.Graded.usageDimension
#print axioms LeanFX2.Graded.securityDimension
#print axioms LeanFX2.Graded.trustDimension
#print axioms LeanFX2.Graded.representationDimension
#print axioms LeanFX2.Graded.observabilityDimension
#print axioms LeanFX2.Graded.complexityDimension
#print axioms LeanFX2.Graded.spaceDimension
#print axioms LeanFX2.Graded.fpOrderDimension
#print axioms LeanFX2.Graded.mutationDimension
#print axioms LeanFX2.Graded.reentrancyDimension
#print axioms LeanFX2.Graded.sizeDimension

#print axioms LeanFX2.Graded.effectJoinDimension
#print axioms LeanFX2.Graded.lifetimeJoinDimension
#print axioms LeanFX2.Graded.provenanceJoinDimension
#print axioms LeanFX2.Graded.clockDomainJoinDimension
#print axioms LeanFX2.Graded.precisionJoinDimension
#print axioms LeanFX2.Graded.overflowJoinDimension
#print axioms LeanFX2.Graded.versionJoinDimension

#print axioms LeanFX2.Graded.semiringDimensionEntries21
#print axioms LeanFX2.Graded.joinDimensionEntries21
#print axioms LeanFX2.Graded.structuralDimensionEntries21
#print axioms LeanFX2.Graded.semiringDimensions21
#print axioms LeanFX2.Graded.semiringDimensionSlots21
#print axioms LeanFX2.Graded.joinDimensions21
#print axioms LeanFX2.Graded.joinDimensionSlots21
#print axioms LeanFX2.Graded.structuralDimensionSlots21
#print axioms LeanFX2.Graded.semiringDimensionEntries21_length
#print axioms LeanFX2.Graded.joinDimensionEntries21_length
#print axioms LeanFX2.Graded.structuralDimensionEntries21_length
#print axioms LeanFX2.Graded.semiringDimensions21_length
#print axioms LeanFX2.Graded.semiringDimensionSlots21_length
#print axioms LeanFX2.Graded.joinDimensions21_length
#print axioms LeanFX2.Graded.joinDimensionSlots21_length
#print axioms LeanFX2.Graded.structuralDimensionSlots21_length
#print axioms LeanFX2.Graded.semiringDimensions21_slots_length_match
#print axioms LeanFX2.Graded.joinDimensions21_slots_length_match

#print axioms LeanFX2.Graded.FXGradeVector21
#print axioms LeanFX2.Graded.FXGradeVector21.bottom
#print axioms LeanFX2.Graded.FXGradeVector21.join
#print axioms LeanFX2.Graded.FXGradeVector21.le
#print axioms LeanFX2.Graded.FXGradeVector21.le_refl
#print axioms LeanFX2.Graded.FXGradeVector21.le_trans
#print axioms LeanFX2.Graded.FXGradeVector21.joinGrades_bottom_le
