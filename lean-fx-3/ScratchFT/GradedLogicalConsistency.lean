import FX1Poly.Modal.GradedEvaluation

/-! Probe: the graded λ-calculus is a CONSISTENT logic — the base atom is uninhabited by closed
    terms (over any semiring R), and every closed graded-typed term is a function (arrow type). -/

namespace FX1Poly.Modal

/-- The base type has NO closed inhabitant, over any graded dimension R. A closed base-typed term
evaluates to a λ (`closedReducesToLam`), that λ stays base-typed along the reduction (SR-over-↝*), but
a λ is only ever arrow-typed (`invertLam`) — contradiction. The Curry-Howard consistency of the
graded calculus: its atomic proposition has no closed proof. -/
theorem closedBaseTypeUninhabited {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) {grades : GradeVectorOver R}
    {term : GradedLambda} (typed : HasGradeOver R [] grades term GTypeOver.base) : False := by
  obtain ⟨body, reducesStar⟩ := closedReducesToLam lawful typed
  have lamTyped : HasGradeOver R [] grades (.lam body) GTypeOver.base :=
    hasGradeOver_reducesStarPreservation lawful reducesStar typed
  obtain ⟨binderGrade, domain, codomain, baseEq, _⟩ := HasGradeOver.invertLam lamTyped
  cases baseEq

/-- Every CLOSED graded-typed term has ARROW type — it is a function. The base case is impossible by
`closedBaseTypeUninhabited`; the only other type former is the arrow. -/
theorem closedTermIsArrowTyped {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) {grades : GradeVectorOver R}
    {term : GradedLambda} {resultType : GTypeOver R}
    (typed : HasGradeOver R [] grades term resultType) :
    ∃ binderGrade domain codomain, resultType = GTypeOver.arrow binderGrade domain codomain := by
  cases resultType with
  | base => exact (closedBaseTypeUninhabited lawful typed).elim
  | arrow binderGrade domain codomain => exact ⟨binderGrade, domain, codomain, rfl⟩

end FX1Poly.Modal

#print axioms FX1Poly.Modal.closedBaseTypeUninhabited
#print axioms FX1Poly.Modal.closedTermIsArrowTyped
