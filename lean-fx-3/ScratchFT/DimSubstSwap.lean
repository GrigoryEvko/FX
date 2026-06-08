import FX1Poly.Modal.SimpleStrongNormalization

/-! Scratch probe (DIM2-5 iii-a): the de Bruijn substitution-commutation tower for `GradedLambda`
(`shift`/`substAt`), culminating in the substitution-swap, then `Reduces.substAt` (reduction is
preserved under substitution) and `IsStronglyNormalizing.ofSubstAt` (SN reflection). Funext-free:
every conclusion is a term equation with explicit Nat indices; index arithmetic via explicit Nat
lemmas, never `omega`; `ite` reduced via `rw [if_pos]`/`rw [if_neg]` (NOT `simp only`, which pulls
propext through the `ite` congruence). -/

namespace FX1Poly.Modal

/-- **CANCEL**: substituting at index `cut` immediately after shifting at `cut` is the identity (the
shifted term has no occurrence of `cut`, and every index it bumped gets decremented back). -/
theorem substAt_shift_cancel (replacement : GradedLambda) :
    ∀ (cut : Nat) (other : GradedLambda),
      GradedLambda.substAt cut other (GradedLambda.shift cut replacement) = replacement := by
  induction replacement with
  | var index =>
      intro cut other
      rw [GradedLambda.shift]
      by_cases hlt : index < cut
      · rw [if_pos hlt, GradedLambda.substAt, if_pos hlt]
      · rw [if_neg hlt, GradedLambda.substAt]
        have hnlt : ¬ (index + 1 < cut) := fun hc => hlt (Nat.lt_of_succ_lt hc)
        have hne : ¬ (index + 1 = cut) := fun hc => hlt (by rw [← hc]; exact Nat.lt_succ_self index)
        rw [if_neg hnlt, if_neg hne, Nat.succ_sub_one]
  | lam body bodyIH =>
      intro cut other
      rw [GradedLambda.shift, GradedLambda.substAt, bodyIH (cut + 1) (GradedLambda.shift 0 other)]
  | app function argument functionIH argumentIH =>
      intro cut other
      rw [GradedLambda.shift, GradedLambda.substAt, functionIH cut other, argumentIH cut other]

#print axioms substAt_shift_cancel

end FX1Poly.Modal
