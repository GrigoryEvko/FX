import FX1Poly.Modal.UsageDiscipline

/-! Scratch probe: the occurrence-usage check is NOT subject-reduction-closed.
GradedLambda substitution + root β + the `(λx. x x) g` counterexample (well-graded redex, ill-graded
reduct), motivating the Wood/Atkey binder-grade discipline. -/

namespace FX1Poly.Modal

/-- de Bruijn lift: increment every free index `≥ cutoff`. -/
def GradedLambda.shift (cutoff : Nat) : GradedLambda → GradedLambda
  | .var index => if index < cutoff then .var index else .var (index + 1)
  | .lam body => .lam (GradedLambda.shift (cutoff + 1) body)
  | .app function argument =>
      .app (GradedLambda.shift cutoff function) (GradedLambda.shift cutoff argument)

/-- de Bruijn substitution: replace variable `index` by `replacement`, decrementing higher indices
(shifting `replacement` under each binder).  `substAt 0` is the β-substitution `b[0 := a]`. -/
def GradedLambda.substAt (index : Nat) (replacement : GradedLambda) : GradedLambda → GradedLambda
  | .var varIndex =>
      if varIndex < index then .var varIndex
      else if varIndex = index then replacement
      else .var (varIndex - 1)
  | .lam body =>
      .lam (GradedLambda.substAt (index + 1) (GradedLambda.shift 0 replacement) body)
  | .app function argument =>
      .app (GradedLambda.substAt index replacement function)
        (GradedLambda.substAt index replacement argument)

/-- Root β-reduction `(λ. b) a ↝ b[0 := a]`. -/
inductive GradedLambda.BetaStep : GradedLambda → GradedLambda → Prop where
  | beta (body argument : GradedLambda) :
      GradedLambda.BetaStep (.app (.lam body) argument) (GradedLambda.substAt 0 argument body)

-- ===== the counterexample: (λx. x x) g, with g declared linear =====

/-- `(λx. x x) g` — `g` (de Bruijn `0`) fed to a self-duplicating function. -/
def dupRedex : GradedLambda := .app (.lam (.app (.var 0) (.var 0))) (.var 0)

/-- Its β-reduct `g g`. -/
def dupReduct : GradedLambda := .app (.var 0) (.var 0)

/-- The declared-linear context `g :_1`. -/
def linearG : GradeVector := GradeVector.cons UsageGrade.one GradeVector.nil

theorem dupRedex_beta : GradedLambda.BetaStep dupRedex dupReduct :=
  GradedLambda.BetaStep.beta (.app (.var 0) (.var 0)) (.var 0)

/-- The redex IS well-graded: `g` is used ONCE syntactically (its two uses are hidden inside the
function, which only the binder grade would expose). -/
theorem dupRedex_wellGraded : GradedLambda.WellGraded 1 dupRedex linearG :=
  ⟨rfl, True.intro⟩

/-- The reduct is NOT well-graded: after β, `g` is used twice (`ω`), exceeding its linear `1`. -/
theorem dupReduct_illGraded : ¬ GradedLambda.WellGraded 1 dupReduct linearG := by
  intro wellGraded
  obtain ⟨headBelow, _⟩ := wellGraded
  exact Bool.noConfusion headBelow

/-- **The occurrence-usage check is NOT subject-reduction-closed.**  There is a well-graded term
whose β-reduct is ill-graded: `(λx. x x) g ↝ g g` with `g` linear.  The naive `usage ≤ Γ` check
under-counts a linear resource consumed multiply INSIDE a function — which is exactly the unsoundness
the Wood/Atkey discipline fixes by tracking the binder grade and scaling the argument in App. -/
theorem usage_check_fails_subject_reduction :
    ∃ (redex reduct : GradedLambda) (declared : GradeVector),
      GradedLambda.BetaStep redex reduct ∧
        GradedLambda.WellGraded 1 redex declared ∧
        ¬ GradedLambda.WellGraded 1 reduct declared :=
  ⟨dupRedex, dupReduct, linearG, dupRedex_beta, dupRedex_wellGraded, dupReduct_illGraded⟩

#print axioms GradedLambda.shift
#print axioms GradedLambda.substAt
#print axioms GradedLambda.BetaStep
#print axioms dupRedex_beta
#print axioms dupRedex_wellGraded
#print axioms dupReduct_illGraded
#print axioms usage_check_fails_subject_reduction

end FX1Poly.Modal
