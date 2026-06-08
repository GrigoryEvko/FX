import FX1Poly.Modal.GradedTypingGeneric

/-! Probe: (λx. x x) is UNTYPABLE in the generic graded engine HasGradeOver R, in EVERY dimension.
The occurs-check: self-application needs D = (D -> C), impossible for the finite type inductive. -/

namespace FX1Poly.Modal

/-- A graded type cannot equal an arrow with itself as the domain (no infinite/recursive types). -/
theorem gTypeOver_ne_self_arrow {R : OrderedGradeSemiring} :
    ∀ (someType : GTypeOver R) (binderGrade : R.Carrier) (codomain : GTypeOver R),
      someType ≠ .arrow binderGrade someType codomain := by
  intro someType
  induction someType with
  | base => intro binderGrade codomain selfEq; nomatch selfEq
  | arrow innerGrade innerDomain innerCodomain innerDomainIH _ =>
      intro binderGrade codomain selfEq
      injection selfEq with _ domainEq _
      exact innerDomainIH innerGrade innerCodomain domainEq

/-- (λx. x x) has NO typing derivation in the generic graded engine, in any dimension `R`:
self-application would force the binder's type `D` to satisfy `D = (D -> codomain)`. -/
theorem selfApplicationLambda_untypableOver {R : OrderedGradeSemiring} :
    ¬ ∃ (typeContext : List (GTypeOver R)) (grades : GradeVectorOver R) (resultType : GTypeOver R),
        HasGradeOver R typeContext grades (.lam (.app (.var 0) (.var 0))) resultType := by
  rintro ⟨typeContext, grades, resultType, typed⟩
  obtain ⟨binderGrade, domain, codomain, _, bodyTyped⟩ := HasGradeOver.invertLam typed
  obtain ⟨functionBinderGrade, argumentType, functionGrades, argumentGrades,
    functionTyped, argumentTyped, _⟩ := HasGradeOver.invertApp bodyTyped
  obtain ⟨functionLookup, _⟩ := HasGradeOver.invertVar functionTyped
  obtain ⟨argumentLookup, _⟩ := HasGradeOver.invertVar argumentTyped
  have functionEq : domain = .arrow functionBinderGrade argumentType codomain :=
    Option.some.inj functionLookup
  have argumentEq : domain = argumentType := Option.some.inj argumentLookup
  rw [← argumentEq] at functionEq
  exact gTypeOver_ne_self_arrow domain functionBinderGrade codomain functionEq

/-- The omega combinator `Ω = (λx. x x) (λx. x x)` is untypable: its function part `(λx. x x)` is
untypable, and `invertApp` would demand a typing of it. -/
theorem omegaCombinator_untypableOver {R : OrderedGradeSemiring} :
    ¬ ∃ (typeContext : List (GTypeOver R)) (grades : GradeVectorOver R) (resultType : GTypeOver R),
        HasGradeOver R typeContext grades
          (.app (.lam (.app (.var 0) (.var 0))) (.lam (.app (.var 0) (.var 0)))) resultType := by
  rintro ⟨typeContext, grades, resultType, typed⟩
  obtain ⟨binderGrade, domain, functionGrades, argumentGrades, functionTyped, _, _⟩ :=
    HasGradeOver.invertApp typed
  exact selfApplicationLambda_untypableOver
    ⟨typeContext, functionGrades, .arrow binderGrade domain resultType, functionTyped⟩

/-- Usage-dimension instantiation: untypable at `fxUsageSemiring`. -/
theorem usageSelfApp_untypable :
    ¬ ∃ (typeContext : List (GTypeOver fxUsageSemiring)) (grades : GradeVectorOver fxUsageSemiring)
        (resultType : GTypeOver fxUsageSemiring),
        HasGradeOver fxUsageSemiring typeContext grades (.lam (.app (.var 0) (.var 0))) resultType :=
  selfApplicationLambda_untypableOver

/-- Security-dimension instantiation: untypable at `fxSecuritySemiring` — the SAME occurs-check. -/
theorem securitySelfApp_untypable :
    ¬ ∃ (typeContext : List (GTypeOver fxSecuritySemiring))
        (grades : GradeVectorOver fxSecuritySemiring) (resultType : GTypeOver fxSecuritySemiring),
        HasGradeOver fxSecuritySemiring typeContext grades (.lam (.app (.var 0) (.var 0)))
          resultType :=
  selfApplicationLambda_untypableOver

end FX1Poly.Modal

#print axioms FX1Poly.Modal.gTypeOver_ne_self_arrow
#print axioms FX1Poly.Modal.selfApplicationLambda_untypableOver
#print axioms FX1Poly.Modal.omegaCombinator_untypableOver
#print axioms FX1Poly.Modal.usageSelfApp_untypable
#print axioms FX1Poly.Modal.securitySelfApp_untypable
