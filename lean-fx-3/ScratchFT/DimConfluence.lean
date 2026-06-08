import FX1Poly.Modal.GradedFundamentalTheorem
import FX1Poly.Core.Newman

/-! Scratch probe (GradedLambda β-confluence, stage 1): the reduction-substitutivity infrastructure —
reduction under renaming/shift (corollary of the shipped `Reduces.applySubstitution`), multi-step
congruence closures, and argument-substitutivity (`substReducedArg`).  Toward local confluence +
`newmanAux` (per-SN-term confluence) → unique normal forms for the simply-typed fragment. -/

namespace FX1Poly.Modal

open FX1Poly.Core (ReflTransClosure)

/-- Multi-step β-reduction: the reflexive-transitive closure of `Reduces`. -/
abbrev GradedLambda.ReducesStar : GradedLambda → GradedLambda → Prop :=
  ReflTransClosure GradedLambda.Reduces

/-- A renaming is the parallel substitution sending each variable to the renamed variable. -/
theorem GradedLambda.renameTerm_eq_applySubstitution_var (term : GradedLambda) :
    ∀ (indexRenaming : IndexRenaming),
      GradedLambda.renameTerm indexRenaming term
        = GradedLambda.applySubstitution (fun index => GradedLambda.var (indexRenaming index)) term := by
  induction term with
  | var index => intro _; rfl
  | lam body bodyIH =>
      intro indexRenaming
      show GradedLambda.lam (GradedLambda.renameTerm (liftRenaming indexRenaming) body)
        = GradedLambda.lam (GradedLambda.applySubstitution
            (liftSubstitution (fun index => GradedLambda.var (indexRenaming index))) body)
      rw [bodyIH (liftRenaming indexRenaming)]
      apply congrArg GradedLambda.lam
      apply GradedLambda.applySubstitution_congr
      intro index
      cases index with
      | zero => rfl
      | succ _ => rfl
  | app function argument functionIH argumentIH =>
      intro indexRenaming
      show GradedLambda.app _ _ = GradedLambda.app _ _
      rw [functionIH indexRenaming, argumentIH indexRenaming]

/-- **Reduction is preserved under renaming** (a corollary of `Reduces.applySubstitution`: a renaming
is a var-substitution). -/
theorem GradedLambda.Reduces.renameTerm {source reduct : GradedLambda}
    (step : GradedLambda.Reduces source reduct) (indexRenaming : IndexRenaming) :
    GradedLambda.Reduces (GradedLambda.renameTerm indexRenaming source)
      (GradedLambda.renameTerm indexRenaming reduct) := by
  rw [GradedLambda.renameTerm_eq_applySubstitution_var source indexRenaming,
    GradedLambda.renameTerm_eq_applySubstitution_var reduct indexRenaming]
  exact step.applySubstitution (fun index => GradedLambda.var (indexRenaming index))

/-- **Reduction is preserved under `shift 0`** (renaming at `incrementIndex`). -/
theorem GradedLambda.Reduces.shift {source reduct : GradedLambda}
    (step : GradedLambda.Reduces source reduct) :
    GradedLambda.Reduces (GradedLambda.shift 0 source) (GradedLambda.shift 0 reduct) := by
  rw [shift_zero_eq_renameTerm source, shift_zero_eq_renameTerm reduct]
  exact step.renameTerm incrementIndex

/-- Multi-step congruence: a lambda's body reducing many steps reduces the lambda. -/
theorem GradedLambda.ReducesStar.congLam {body body' : GradedLambda}
    (bodyStar : GradedLambda.ReducesStar body body') :
    GradedLambda.ReducesStar (GradedLambda.lam body) (GradedLambda.lam body') := by
  induction bodyStar with
  | refl _ => exact ReflTransClosure.refl _
  | head first _ inductionHypothesis =>
      exact ReflTransClosure.head (GradedLambda.Reduces.congLam _ _ first) inductionHypothesis

/-- Multi-step congruence: reducing the function part of an application. -/
theorem GradedLambda.ReducesStar.congAppLeft {function function' argument : GradedLambda}
    (functionStar : GradedLambda.ReducesStar function function') :
    GradedLambda.ReducesStar (GradedLambda.app function argument) (GradedLambda.app function' argument) := by
  induction functionStar with
  | refl _ => exact ReflTransClosure.refl _
  | head first _ inductionHypothesis =>
      exact ReflTransClosure.head (GradedLambda.Reduces.congAppLeft _ _ argument first) inductionHypothesis

/-- Multi-step congruence: reducing the argument part of an application. -/
theorem GradedLambda.ReducesStar.congAppRight {function argument argument' : GradedLambda}
    (argumentStar : GradedLambda.ReducesStar argument argument') :
    GradedLambda.ReducesStar (GradedLambda.app function argument) (GradedLambda.app function argument') := by
  induction argumentStar with
  | refl _ => exact ReflTransClosure.refl _
  | head first _ inductionHypothesis =>
      exact ReflTransClosure.head (GradedLambda.Reduces.congAppRight function _ _ first) inductionHypothesis

/-- **Argument-substitutivity**: reducing the substituted argument reduces the substitution result
(many steps, since the body may have several occurrences of the substituted variable). -/
theorem GradedLambda.Reduces.substReducedArg {replacement replacement' : GradedLambda}
    (step : GradedLambda.Reduces replacement replacement') :
    ∀ (cut : Nat) (body : GradedLambda),
      GradedLambda.ReducesStar (GradedLambda.substAt cut replacement body)
        (GradedLambda.substAt cut replacement' body) := by
  intro cut body
  induction body generalizing cut replacement replacement' with
  | var index =>
      by_cases hlt : index < cut
      · have lhs : GradedLambda.substAt cut replacement (GradedLambda.var index) = GradedLambda.var index := by
          rw [GradedLambda.substAt, if_pos hlt]
        have rhs : GradedLambda.substAt cut replacement' (GradedLambda.var index) = GradedLambda.var index := by
          rw [GradedLambda.substAt, if_pos hlt]
        rw [lhs, rhs]; exact ReflTransClosure.refl _
      · by_cases heq : index = cut
        · have lhs : GradedLambda.substAt cut replacement (GradedLambda.var index) = replacement := by
            rw [GradedLambda.substAt, if_neg hlt, if_pos heq]
          have rhs : GradedLambda.substAt cut replacement' (GradedLambda.var index) = replacement' := by
            rw [GradedLambda.substAt, if_neg hlt, if_pos heq]
          rw [lhs, rhs]; exact ReflTransClosure.single step
        · have lhs : GradedLambda.substAt cut replacement (GradedLambda.var index) = GradedLambda.var (index - 1) := by
            rw [GradedLambda.substAt, if_neg hlt, if_neg heq]
          have rhs : GradedLambda.substAt cut replacement' (GradedLambda.var index) = GradedLambda.var (index - 1) := by
            rw [GradedLambda.substAt, if_neg hlt, if_neg heq]
          rw [lhs, rhs]; exact ReflTransClosure.refl _
  | lam innerBody bodyIH =>
      show GradedLambda.ReducesStar (GradedLambda.lam (GradedLambda.substAt (cut + 1) (GradedLambda.shift 0 replacement) innerBody))
        (GradedLambda.lam (GradedLambda.substAt (cut + 1) (GradedLambda.shift 0 replacement') innerBody))
      exact GradedLambda.ReducesStar.congLam (bodyIH step.shift (cut + 1))
  | app function argument functionIH argumentIH =>
      show GradedLambda.ReducesStar (GradedLambda.app (GradedLambda.substAt cut replacement function) (GradedLambda.substAt cut replacement argument))
        (GradedLambda.app (GradedLambda.substAt cut replacement' function) (GradedLambda.substAt cut replacement' argument))
      exact (GradedLambda.ReducesStar.congAppLeft (functionIH step cut)).trans
        (GradedLambda.ReducesStar.congAppRight (argumentIH step cut))

#print axioms GradedLambda.renameTerm_eq_applySubstitution_var
#print axioms GradedLambda.Reduces.renameTerm
#print axioms GradedLambda.Reduces.shift
#print axioms GradedLambda.ReducesStar.congLam
#print axioms GradedLambda.ReducesStar.congAppLeft
#print axioms GradedLambda.ReducesStar.congAppRight
#print axioms GradedLambda.Reduces.substReducedArg

end FX1Poly.Modal
