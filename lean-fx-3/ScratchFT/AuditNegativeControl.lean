import FX1Poly.Modal.GradedComposition

/-! Negative controls: confirm graded SR is GENUINELY CONSTRAINING, not vacuously true.
    If any of these `WRONG` claims type-checked, SR would be meaningless. They must FAIL. -/

namespace FX1Poly.Modal

abbrev gType : GType := .arrow UsageGrade.one GType.base (.arrow UsageGrade.one GType.base GType.base)
abbrev dupBody : GradedLambda := .app (.app (.var 2) (.var 0)) (.var 0)

-- NEGATIVE CONTROL 1: claim the contractum (g z) z has grade [z↦1, g↦1] (i.e. as if scaling were
-- by 1 not ω, or + instead of scaled-add). This is the bug-shape grade. It MUST be rejected
-- because the var rule forces z's uses to ADD to ω.  We assert it and expect an ERROR.
theorem WRONG_contractum_grade_one :
    HasUsage [GType.base, gType]
      (GradeVector.cons UsageGrade.one (GradeVector.cons UsageGrade.one GradeVector.nil))
      (.app (.app (.var 1) (.var 0)) (.var 0)) GType.base := by
  apply HasUsage.app [GType.base, gType] UsageGrade.one GType.base GType.base
    (GradeVector.add (GradeVector.single 2 1 UsageGrade.one)
      (GradeVector.scale UsageGrade.one (GradeVector.single 2 0 UsageGrade.one)))
    (GradeVector.single 2 0 UsageGrade.one)
  · exact HasUsage.app [GType.base, gType] UsageGrade.one GType.base
      (.arrow UsageGrade.one GType.base GType.base)
      (GradeVector.single 2 1 UsageGrade.one) (GradeVector.single 2 0 UsageGrade.one)
      (.var 1) (.var 0)
      (HasUsage.var [GType.base, gType] 1 gType rfl)
      (HasUsage.var [GType.base, gType] 0 GType.base rfl)
  · exact HasUsage.var [GType.base, gType] 0 GType.base rfl

end FX1Poly.Modal
