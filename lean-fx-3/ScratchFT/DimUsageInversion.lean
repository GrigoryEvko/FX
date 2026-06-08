import FX1Poly.Modal.GradedTyping

/-! Scratch probe: inversion lemmas for HasUsage (the first SR brick).  Watch for the indexed-
inductive propext trap — casing on a CONSTRUCTOR term-index (`.var i` / `.lam b` / `.app f a`) may
route the ▸ cast through propext.  Test direct `cases` first; if it leaks, use the
generalize-the-index + thread-an-equation recipe. -/

namespace FX1Poly.Modal

/-- Inversion for a variable: its type is the context lookup, its grades the singleton. -/
theorem invertVar_direct {typeContext : List GType} {grades : GradeVector} {index : Nat}
    {resultType : GType} (typed : HasUsage typeContext grades (.var index) resultType) :
    GType.lookup typeContext index = some resultType ∧
      grades = GradeVector.single typeContext.length index UsageGrade.one := by
  cases typed with
  | var _ _ _ lookupOk => exact ⟨lookupOk, rfl⟩

/-- Inversion for a lambda: the type is a graded arrow, the body typed in the extended context. -/
theorem invertLam_direct {typeContext : List GType} {grades : GradeVector} {body : GradedLambda}
    {resultType : GType} (typed : HasUsage typeContext grades (.lam body) resultType) :
    ∃ (binderGrade : UsageGrade) (domain codomain : GType),
      resultType = .arrow binderGrade domain codomain ∧
        HasUsage (domain :: typeContext) (GradeVector.cons binderGrade grades) body codomain := by
  cases typed with
  | lam _ binderGrade domain codomain _ _ bodyTyped =>
      exact ⟨binderGrade, domain, codomain, rfl, bodyTyped⟩

/-- Inversion for an application: function and argument typed, grades the scaled sum. -/
theorem invertApp_direct {typeContext : List GType} {grades : GradeVector}
    {function argument : GradedLambda} {resultType : GType}
    (typed : HasUsage typeContext grades (.app function argument) resultType) :
    ∃ (binderGrade : UsageGrade) (domain : GType) (functionGrades argumentGrades : GradeVector),
      HasUsage typeContext functionGrades function (.arrow binderGrade domain resultType) ∧
        HasUsage typeContext argumentGrades argument domain ∧
          grades = GradeVector.add functionGrades (GradeVector.scale binderGrade argumentGrades) := by
  cases typed with
  | app _ binderGrade domain codomain functionGrades argumentGrades _ _ functionTyped argumentTyped =>
      exact ⟨binderGrade, domain, functionGrades, argumentGrades, functionTyped, argumentTyped, rfl⟩

#print axioms invertVar_direct
#print axioms invertLam_direct
#print axioms invertApp_direct

end FX1Poly.Modal
