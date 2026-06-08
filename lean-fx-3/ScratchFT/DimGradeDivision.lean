import FX1Poly.Modal.GradeVector

/-! Scratch probe for the grade-division residual (toward DIM2-3's corrected Lam rule, §6.2/§27.1).
`div a b = max { d : d * b ≤ a }`: the residual (right adjoint) of multiplication.  The defining
fact `1 / ω = 0` is the Wood/Atkey 2022 correction. -/

namespace FX1Poly.Modal

/-- Grade division `div a b = max { d : d * b ≤ a }` — the residual of `* b`.  Full 3×3
enumeration; propext-free. -/
def UsageGrade.div : UsageGrade → UsageGrade → UsageGrade
  | .zero,  .zero  => .omega
  | .one,   .zero  => .omega
  | .omega, .zero  => .omega
  | .zero,  .one   => .zero
  | .one,   .one   => .one
  | .omega, .one   => .omega
  | .zero,  .omega => .zero
  | .one,   .omega => .zero
  | .omega, .omega => .omega

/-- Residuation: `d * b ≤ a ↔ d ≤ a / b` — division is the right adjoint of multiplication. -/
theorem UsageGrade.div_residuation (dividendGrade divisorGrade quotientCandidate : UsageGrade) :
    (UsageGrade.le (UsageGrade.mul quotientCandidate divisorGrade) dividendGrade = true) ↔
      (UsageGrade.le quotientCandidate (UsageGrade.div dividendGrade divisorGrade) = true) := by
  cases dividendGrade <;> cases divisorGrade <;> cases quotientCandidate <;> exact Iff.rfl

/-- The Wood/Atkey 2022 correction: `1 / ω = 0`.  A linear variable divided by a replicable
closure's ω-grade erases to 0 — exactly what makes the corrected Lam rule reject capturing a linear
variable in an unrestricted closure (§27.1). -/
theorem UsageGrade.one_div_omega : UsageGrade.div UsageGrade.one UsageGrade.omega = UsageGrade.zero :=
  rfl

/-- Division by the unit is the identity: `a / 1 = a`. -/
theorem UsageGrade.div_one (someGrade : UsageGrade) :
    UsageGrade.div someGrade UsageGrade.one = someGrade := by
  cases someGrade <;> rfl

/-- Counit / soundness: `b * (a / b) ≤ a` — you can never recover more than you had.  The fact the
Lam rule relies on: scaling the divided context back up (the scalar `b` on the left, matching
`GradeVector.scale`) stays below the original. -/
theorem UsageGrade.mul_div_le (divisorGrade dividendGrade : UsageGrade) :
    UsageGrade.le (UsageGrade.mul divisorGrade (UsageGrade.div dividendGrade divisorGrade))
      dividendGrade = true := by
  cases divisorGrade <;> cases dividendGrade <;> rfl

-- ===== vector-level context division =====

/-- Context division `G / p`: divide every binding's grade by the scalar `p` (§6.2 — the corrected
Lam rule's capture discipline).  Pointwise `div · p`. -/
def GradeVector.contextDivide (divisorGrade : UsageGrade) : GradeVector → GradeVector
  | .nil => .nil
  | .cons headGrade restGrades =>
      .cons (UsageGrade.div headGrade divisorGrade) (GradeVector.contextDivide divisorGrade restGrades)

theorem GradeVector.contextDivide_length (divisorGrade : UsageGrade) (someVector : GradeVector) :
    (GradeVector.contextDivide divisorGrade someVector).length = someVector.length := by
  induction someVector with
  | nil => rfl
  | cons headGrade restGrades restIH =>
      show (GradeVector.contextDivide divisorGrade restGrades).length + 1 = restGrades.length + 1
      rw [restIH]

/-- Vector counit: `scale b (contextDivide b G) ≤ G` pointwise — the soundness of context division,
lifting `UsageGrade.div_mul_le` to the whole context.  Stated with a pointwise-`≤` predicate so it
needs no new vector order. -/
def GradeVector.IsPointwiseBelow : GradeVector → GradeVector → Prop
  | .nil, .nil => True
  | .nil, .cons _ _ => False
  | .cons _ _, .nil => False
  | .cons firstHead firstRest, .cons secondHead secondRest =>
      (UsageGrade.le firstHead secondHead = true) ∧
        GradeVector.IsPointwiseBelow firstRest secondRest

theorem GradeVector.scale_contextDivide_below (divisorGrade : UsageGrade) (someVector : GradeVector) :
    GradeVector.IsPointwiseBelow
      (GradeVector.scale divisorGrade (GradeVector.contextDivide divisorGrade someVector))
      someVector := by
  induction someVector with
  | nil => exact True.intro
  | cons headGrade restGrades restIH =>
      exact ⟨UsageGrade.mul_div_le divisorGrade headGrade, restIH⟩

#print axioms UsageGrade.div
#print axioms UsageGrade.div_residuation
#print axioms UsageGrade.one_div_omega
#print axioms UsageGrade.div_one
#print axioms UsageGrade.mul_div_le
#print axioms GradeVector.contextDivide
#print axioms GradeVector.contextDivide_length
#print axioms GradeVector.IsPointwiseBelow
#print axioms GradeVector.scale_contextDivide_below

end FX1Poly.Modal
