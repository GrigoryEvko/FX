import FX1Poly.Modal.GradedFundamentalTheorem
import FX1Poly.Core.Newman

/-! # FX1Poly/Modal/GradedReductionConfluence — β-confluence for GradedLambda (CONF, stage 1)

Completing the DIM2 `GradedLambda` STLC substrate into a full reference calculus: alongside strong
normalization (DIM2-5) and subject reduction (DIM2-3/7), β-reduction is CONFLUENT on the strongly-
normalizing (= simply-typed) fragment — so every term has a UNIQUE normal form (toward decidable
definitional equality).  This reuses the abstract, relation-generic Newman's lemma
`FX1Poly.Core.newmanAux` (per-term confluence from local confluence + the term's `Acc`, which is
exactly `IsStronglyNormalizing`), so untyped Ω is no obstacle — confluence is derived FROM SN.

**This first installment is the reduction-substitutivity infrastructure** the local-confluence
critical-pair analysis consumes:

  * `GradedLambda.ReducesStar` — multi-step β-reduction (the `ReflTransClosure` of `Reduces`).
  * `renameTerm_eq_applySubstitution_var` + `Reduces.renameTerm` / `Reduces.shift` — reduction is
    preserved under renaming/shift (a corollary of the shipped `Reduces.applySubstitution`, since a
    renaming is just a variable-substitution).
  * `ReducesStar.congLam` / `congAppLeft` / `congAppRight` — multi-step congruence closures.
  * `Reduces.substReducedArg` — reducing the substituted argument multi-reduces the substitution
    result (many steps: the body may have several occurrences of the substituted variable).  The
    binder case shifts the argument (`Reduces.shift`) and re-substitutes under the bumped index.

Still to come (next installments): local confluence (`WeaklyConfluent Reduces`, the 9-case β
critical-pair analysis), confluence for SN terms via `newmanAux`, and unique normal forms / decidable
`Conv` on the `HasSimpleType` fragment.

## Zero-axiom verification

`Reduces.renameTerm`/`shift` are `rw` + the shipped substitution lemma; the cong-stars are inductions
on `ReflTransClosure` (propext-clean — its indices are free variables); `substReducedArg` is a term
induction with explicit `if`-reduction (`rw [if_pos]`/`if_neg]`, never `simp` on `ite`).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditModal.lean`.
-/

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
      show GradedLambda.ReducesStar
        (GradedLambda.lam (GradedLambda.substAt (cut + 1) (GradedLambda.shift 0 replacement) innerBody))
        (GradedLambda.lam (GradedLambda.substAt (cut + 1) (GradedLambda.shift 0 replacement') innerBody))
      exact GradedLambda.ReducesStar.congLam (bodyIH step.shift (cut + 1))
  | app function argument functionIH argumentIH =>
      show GradedLambda.ReducesStar
        (GradedLambda.app (GradedLambda.substAt cut replacement function) (GradedLambda.substAt cut replacement argument))
        (GradedLambda.app (GradedLambda.substAt cut replacement' function) (GradedLambda.substAt cut replacement' argument))
      exact (GradedLambda.ReducesStar.congAppLeft (functionIH step cut)).trans
        (GradedLambda.ReducesStar.congAppRight (argumentIH step cut))

end FX1Poly.Modal
