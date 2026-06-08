import FX1Poly.Modal.GradeVector

/-! Scratch probe: the usage-dimension grade check (occurrence-counting co-effect realization) +
the Atkey-2018 broken-Lam rejection (§27.1/§27.2).  A minimal graded λ-calculus, the per-free-var
occurrence usage, and the well-gradedness check `usage ≤ Γ` (via IsPointwiseBelow). -/

namespace FX1Poly.Modal

/-- A singleton grade vector of length `scope`: `grade` at `position`, `0` elsewhere (`0` if
`position ≥ scope`).  The var rule's usage vector. -/
def GradeVector.single : (scope : Nat) → (position : Nat) → UsageGrade → GradeVector
  | 0, _, _ => .nil
  | scope + 1, 0, grade => .cons grade (GradeVector.zero scope)
  | scope + 1, pos + 1, grade => .cons UsageGrade.zero (GradeVector.single scope pos grade)

/-- Drop the newest binding's grade (the head): the outer-context usage of a λ from its body. -/
def GradeVector.tail : GradeVector → GradeVector
  | .nil => .nil
  | .cons _ restGrades => restGrades

theorem GradeVector.single_length (scope position : Nat) (grade : UsageGrade) :
    (GradeVector.single scope position grade).length = scope := by
  induction scope generalizing position with
  | zero => rfl
  | succ scope restIH =>
      cases position with
      | zero => show (GradeVector.zero scope).length + 1 = scope + 1; rw [GradeVector.zero_length]
      | succ position => show (GradeVector.single scope position grade).length + 1 = scope + 1; rw [restIH]

/-- A minimal graded λ-calculus (de Bruijn): the carrier for the usage discipline. -/
inductive GradedLambda where
  | var : Nat → GradedLambda
  | lam : GradedLambda → GradedLambda
  | app : GradedLambda → GradedLambda → GradedLambda
  deriving DecidableEq, Repr

/-- Per-free-variable occurrence usage of a term in `scope` free variables (length-`scope` grade
vector).  A variable contributes grade `1`; applications ADD their operands' usages (so two uses of
the same variable combine `1 + 1 = ω` — the FX usage semiring §6.1); a λ drops its binder's grade
(`tail`), leaving the outer-context usage. -/
def GradedLambda.usage : Nat → GradedLambda → GradeVector
  | scope, .var index => GradeVector.single scope index UsageGrade.one
  | scope, .app function argument =>
      GradeVector.add (GradedLambda.usage scope function) (GradedLambda.usage scope argument)
  | scope, .lam body => GradeVector.tail (GradedLambda.usage (scope + 1) body)

/-- Well-gradedness: every free variable is used no more than its declared grade
(`usage ≤ declaredGrades`, pointwise).  The decidable usage check; a linear (`1`) variable used
`ω` times is rejected. -/
def GradedLambda.WellGraded (scope : Nat) (term : GradedLambda) (declaredGrades : GradeVector) : Prop :=
  GradeVector.IsPointwiseBelow (GradedLambda.usage scope term) declaredGrades

-- ===== the §27.1/§27.2 demonstration =====

/-- The Atkey-2018 counterexample inner closure `λx. f (f x)` with `f` free (`f` = de Bruijn 1 under
the `λx`).  `f` is used TWICE in the body. -/
def atkeyClosure : GradedLambda := .lam (.app (.var 1) (.app (.var 1) (.var 0)))

/-- The linear-discipline-respecting `λx. f x` with `f` free: `f` is used ONCE. -/
def linearClosure : GradedLambda := .lam (.app (.var 1) (.var 0))

/-- The declared-linear context for one free variable: `f :_1`. -/
def linearContext : GradeVector := GradeVector.cons UsageGrade.one GradeVector.nil

/-- Computed: `f`'s occurrence usage in the Atkey closure is `ω` (used twice). -/
theorem atkey_usage : GradedLambda.usage 1 atkeyClosure = GradeVector.cons UsageGrade.omega GradeVector.nil :=
  rfl

/-- Computed: `f`'s occurrence usage in the linear closure is `1` (used once). -/
theorem linear_usage : GradedLambda.usage 1 linearClosure = GradeVector.cons UsageGrade.one GradeVector.nil :=
  rfl

/-- **The Atkey-2018 broken-Lam rejection (§27.1/§27.2).**  `λx. f (f x)` is NOT well-graded when
`f` is declared linear: `f`'s occurrence usage is `ω`, and `ω ≤ 1` is false — the corrected usage
discipline rejects capturing a linear variable in a closure that uses it twice.  The broken
Atkey-2018 rule would have accepted it. -/
theorem atkey_rejected : ¬ GradedLambda.WellGraded 1 atkeyClosure linearContext := by
  intro wellGraded
  obtain ⟨headBelow, _⟩ := wellGraded
  exact Bool.noConfusion headBelow

/-- **The linear use is accepted.**  `λx. f x` IS well-graded with `f` declared linear: `f`'s
occurrence usage is `1`, and `1 ≤ 1`. -/
theorem linear_accepted : GradedLambda.WellGraded 1 linearClosure linearContext :=
  ⟨rfl, True.intro⟩

#print axioms GradeVector.single
#print axioms GradeVector.tail
#print axioms GradeVector.single_length
#print axioms GradedLambda
#print axioms GradedLambda.usage
#print axioms GradedLambda.WellGraded
#print axioms atkeyClosure
#print axioms linearClosure
#print axioms linearContext
#print axioms atkey_usage
#print axioms linear_usage
#print axioms atkey_rejected
#print axioms linear_accepted

end FX1Poly.Modal
