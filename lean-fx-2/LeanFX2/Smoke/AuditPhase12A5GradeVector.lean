import LeanFX2.Graded.GradeVector

/-! # Phase 12.A.5 audit: GradeVector zero-axiom

GradeVector implements pointwise composition of FX's graded
dimensions.  Verifies the lifted algebra laws (add:
assoc/comm/identity/monotone, mul: assoc/identity/annihilation/monotone,
le: refl/trans) plus the base operations (zero/one) plus the helper
(prodMkEq) plus the type itself.  All zero-axiom under strict policy. -/

#print axioms LeanFX2.Graded.Dimension
#print axioms LeanFX2.Graded.GradeVector
#print axioms LeanFX2.Graded.GradeVector.zero
#print axioms LeanFX2.Graded.GradeVector.one
#print axioms LeanFX2.Graded.GradeVector.add
#print axioms LeanFX2.Graded.GradeVector.mul
#print axioms LeanFX2.Graded.GradeVector.le
#print axioms LeanFX2.Graded.prodMkEq
#print axioms LeanFX2.Graded.GradeVector.add_assoc
#print axioms LeanFX2.Graded.GradeVector.add_comm
#print axioms LeanFX2.Graded.GradeVector.add_zero_left
#print axioms LeanFX2.Graded.GradeVector.add_zero_right
#print axioms LeanFX2.Graded.GradeVector.mul_assoc
#print axioms LeanFX2.Graded.GradeVector.mul_one_left
#print axioms LeanFX2.Graded.GradeVector.mul_one_right
#print axioms LeanFX2.Graded.GradeVector.mul_zero_left
#print axioms LeanFX2.Graded.GradeVector.mul_zero_right
#print axioms LeanFX2.Graded.GradeVector.le_refl
#print axioms LeanFX2.Graded.GradeVector.le_trans
#print axioms LeanFX2.Graded.GradeVector.add_mono
#print axioms LeanFX2.Graded.GradeVector.mul_mono
