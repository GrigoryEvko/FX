import FX1Poly.Modal.GradedComposition

/-! Confirm the SR-breaking term (λx. x x) is UNTYPABLE in HasUsage. -/

namespace FX1Poly.Modal

abbrev selfAppLam : GradedLambda := .lam (.app (.var 0) (.var 0))

/-- A GType cannot equal an arrow with itself as the domain (no infinite types). -/
theorem gType_ne_self_arrow : ∀ (someType : GType) (bg : UsageGrade) (cod : GType),
    someType ≠ .arrow bg someType cod := by
  intro someType
  induction someType with
  | base => intro bg cod h; exact GType.noConfusion h
  | arrow bg0 dom0 cod0 domIH _ =>
      intro bg cod h
      injection h with _ domEq _
      exact domIH bg0 cod0 domEq

/-- (λx. x x) is untypable: self-application needs an infinite type. -/
theorem selfAppLam_untypable :
    ¬ ∃ (ctx : List GType) (grades : GradeVector) (resultType : GType),
        HasUsage ctx grades selfAppLam resultType := by
  rintro ⟨ctx, grades, resultType, typed⟩
  obtain ⟨binderGrade, domain, codomain, _, bodyTyped⟩ := HasUsage.invertLam typed
  obtain ⟨bg2, dom2, fnGrades, argGrades, fnTyped, argTyped, _⟩ := HasUsage.invertApp bodyTyped
  obtain ⟨fnLookup, _⟩ := HasUsage.invertVar fnTyped
  obtain ⟨argLookup, _⟩ := HasUsage.invertVar argTyped
  -- lookup (domain::ctx) 0 = some domain definitionally; so:
  have e1 : domain = .arrow bg2 dom2 codomain := Option.some.inj fnLookup
  have e2 : domain = dom2 := Option.some.inj argLookup
  rw [← e2] at e1
  exact absurd e1 (gType_ne_self_arrow domain bg2 codomain)

-- Also confirm the SPECIFIC naive counterexample (λx. x x) g is untypable as a whole.
theorem dupRedex_untypable :
    ¬ ∃ (ctx : List GType) (grades : GradeVector) (resultType : GType),
        HasUsage ctx grades (.app selfAppLam (.var 0)) resultType := by
  rintro ⟨ctx, grades, resultType, typed⟩
  obtain ⟨bg, dom, fnGrades, argGrades, fnTyped, _, _⟩ := HasUsage.invertApp typed
  -- fnTyped : HasUsage ctx fnGrades (λx. x x) (arrow bg dom resultType) — but λx.xx is untypable
  exact selfAppLam_untypable ⟨ctx, fnGrades, .arrow bg dom resultType, fnTyped⟩

end FX1Poly.Modal
