import FX1Poly.Modal.GradeErasure

/-! # FX1Poly/Modal/SimpleStrongNormalization — STLC strong normalization (DIM2-5 / SN-056)

The orthogonal-composition thesis (DIM2): the usage dimension does NOT need its own strong-
normalization argument; graded-SN rides on the TYPE dimension's SN through grade erasure
(`HasUsage.erase`, DIM2-4), because the term and the β-reduction are grade-AGNOSTIC.  So the only
SN obligation is the TYPE dimension's: `HasSimpleType Γ t T → IsStronglyNormalizing t` (the classic
STLC Tait result), proved ONCE.  Graded-SN is then the trivial corollary `HasUsage → erase → SN`.

This file builds that STLC-SN.  **This first installment is the reduction + SN substrate** the Tait
reducibility argument consumes:

  * `GradedLambda.Reduces` — full one-step β (root β + congruence everywhere).
  * `GradedLambda.IsStronglyNormalizing` — accessibility under reduction (no infinite reduction
    sequence), mirroring the kernel's RawTerm `IsStronglyNormalizing`.
  * `GradedLambda.IsNeutral` — non-introduction forms (var / app); the CR3 head-expansion condition
    is stated for neutral terms.
  * SN structural lemmas: a variable is SN (`var`); SN passes to subterms (`ofAppLeft` / `ofAppRight`
    / `ofLam`); SN is forward-closed under reduction (`ofReduces`).

Still to come (next installments): the type-indexed reducibility predicate + the candidate
conditions CR1/CR2/CR3, the fundamental theorem under a closing substitution, the SN corollary, and
the trivial transfer to graded-SN.

## Zero-axiom verification

`Reduces` is a plain inductive; `IsStronglyNormalizing` is `Acc`; the structural lemmas are
`Acc`-eliminator inductions with the `subst`-an-equation generalization (NOT `brecOn`); `var` uses
`cases` on the indexed reduction, which is propext-free because `GradedLambda` is a plain inductive
(cross-constructor discrimination via `GradedLambda.noConfusion`).  Per-declaration gated in
`FX1PolyAudit/AuditModal.lean`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.
-/

namespace FX1Poly.Modal

/-- Full one-step β-reduction on `GradedLambda` (root β + congruence everywhere). -/
inductive GradedLambda.Reduces : GradedLambda → GradedLambda → Prop where
  | beta (body argument : GradedLambda) :
      GradedLambda.Reduces (.app (.lam body) argument) (GradedLambda.substAt 0 argument body)
  | congLam (body body' : GradedLambda) (step : GradedLambda.Reduces body body') :
      GradedLambda.Reduces (.lam body) (.lam body')
  | congAppLeft (function function' argument : GradedLambda)
      (step : GradedLambda.Reduces function function') :
      GradedLambda.Reduces (.app function argument) (.app function' argument)
  | congAppRight (function argument argument' : GradedLambda)
      (step : GradedLambda.Reduces argument argument') :
      GradedLambda.Reduces (.app function argument) (.app function argument')

/-- Strong normalization: accessibility under reduction (no infinite reduction sequence). -/
def GradedLambda.IsStronglyNormalizing (term : GradedLambda) : Prop :=
  Acc (fun reduct source => GradedLambda.Reduces source reduct) term

/-- Neutral terms (not an introduction form): variable or application.  The CR3 head-expansion
condition is stated for neutral terms. -/
def GradedLambda.IsNeutral : GradedLambda → Prop
  | .var _ => True
  | .lam _ => False
  | .app _ _ => True

/-- A variable is strongly normalizing (it has no reducts). -/
theorem GradedLambda.IsStronglyNormalizing.var (index : Nat) :
    GradedLambda.IsStronglyNormalizing (GradedLambda.var index) := by
  apply Acc.intro
  intro reduct step
  cases step

/-- SN of an application's function part. -/
theorem GradedLambda.IsStronglyNormalizing.ofAppLeft {function argument : GradedLambda}
    (snApp : GradedLambda.IsStronglyNormalizing (.app function argument)) :
    GradedLambda.IsStronglyNormalizing function := by
  have generalized : ∀ (term : GradedLambda), GradedLambda.IsStronglyNormalizing term →
      ∀ (fn arg : GradedLambda), term = GradedLambda.app fn arg →
        GradedLambda.IsStronglyNormalizing fn := by
    intro term snTerm
    induction snTerm with
    | intro term _ reductIH =>
        intro fn arg termEq
        subst termEq
        exact Acc.intro fn (fun fn' stepFn =>
          reductIH (GradedLambda.app fn' arg)
            (GradedLambda.Reduces.congAppLeft fn fn' arg stepFn) fn' arg rfl)
  exact generalized (GradedLambda.app function argument) snApp function argument rfl

/-- SN of an application's argument part. -/
theorem GradedLambda.IsStronglyNormalizing.ofAppRight {function argument : GradedLambda}
    (snApp : GradedLambda.IsStronglyNormalizing (.app function argument)) :
    GradedLambda.IsStronglyNormalizing argument := by
  have generalized : ∀ (term : GradedLambda), GradedLambda.IsStronglyNormalizing term →
      ∀ (fn arg : GradedLambda), term = GradedLambda.app fn arg →
        GradedLambda.IsStronglyNormalizing arg := by
    intro term snTerm
    induction snTerm with
    | intro term _ reductIH =>
        intro fn arg termEq
        subst termEq
        exact Acc.intro arg (fun arg' stepArg =>
          reductIH (GradedLambda.app fn arg')
            (GradedLambda.Reduces.congAppRight fn arg arg' stepArg) fn arg' rfl)
  exact generalized (GradedLambda.app function argument) snApp function argument rfl

/-- SN of a lambda's body. -/
theorem GradedLambda.IsStronglyNormalizing.ofLam {body : GradedLambda}
    (snLam : GradedLambda.IsStronglyNormalizing (.lam body)) :
    GradedLambda.IsStronglyNormalizing body := by
  have generalized : ∀ (term : GradedLambda), GradedLambda.IsStronglyNormalizing term →
      ∀ (innerBody : GradedLambda), term = GradedLambda.lam innerBody →
        GradedLambda.IsStronglyNormalizing innerBody := by
    intro term snTerm
    induction snTerm with
    | intro term _ reductIH =>
        intro innerBody termEq
        subst termEq
        exact Acc.intro innerBody (fun body' stepBody =>
          reductIH (GradedLambda.lam body') (GradedLambda.Reduces.congLam innerBody body' stepBody)
            body' rfl)
  exact generalized (GradedLambda.lam body) snLam body rfl

/-- SN is forward-closed under reduction (a reduct of an SN term is SN). -/
theorem GradedLambda.IsStronglyNormalizing.ofReduces {source reduct : GradedLambda}
    (snSource : GradedLambda.IsStronglyNormalizing source)
    (step : GradedLambda.Reduces source reduct) :
    GradedLambda.IsStronglyNormalizing reduct :=
  snSource.inv step

end FX1Poly.Modal
