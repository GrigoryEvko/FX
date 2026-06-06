import FX1Poly.Modal.GradeVector

/-! # FX1Poly/Modal/UsageDiscipline — the usage grade check + the Atkey-2018 broken-Lam rejection
   (DIM2-3 occurrence realization; DIM2-6 / §27.1 / §27.2)

The usage dimension's job is to reject programs that use a resource more than its declared grade
allows.  FX's usage semiring `{0, 1, ω}` (§6.1) with `1 + 1 = ω` IS occurrence-counting: a variable
used twice has grade `1 + 1 = ω`, which exceeds a linear (`1`) declaration.  So the usage check has
an unambiguous, computational realization — the *co-effect* reading, dual to the McBride
context-division presentation whose adjunction `GradeVector.contextDivide_residuation` was shipped
separately:

  * `GradedLambda` — a minimal graded λ-calculus (var / lam / app, de Bruijn).
  * `GradedLambda.usage` — the per-free-variable occurrence multiplicity (a length-`scope` grade
    vector): a variable contributes `1`; application ADDS its operands' usages (so two uses of one
    variable combine to `1 + 1 = ω`); a λ drops its binder's grade (`tail`).
  * `GradedLambda.WellGraded` — the check `usage ≤ declaredGrades` (pointwise, via the partial order
    `GradeVector.IsPointwiseBelow`): every free variable is used no more than its declared grade.

## The §27.1/§27.2 demonstration (the headline)

The Atkey-2018 broken Lam rule allowed capturing a linear variable in a closure that uses it
twice — `λf. λx. f (f x)` — which is unsound (a linear resource consumed twice).  The Wood/Atkey
2022 correction rejects it.  Here that rejection is COMPUTED, not postulated:

  * `atkey_rejected` — `λx. f (f x)` (with `f` free and declared linear) is NOT `WellGraded`: `f`'s
    occurrence usage is `ω`, and `ω ≤ 1` is false.  This is the permanent `test_theory` corpus
    entry for the Atkey-2018 grade bug (§27.2).
  * `linear_accepted` — `λx. f x` (with `f` declared linear) IS `WellGraded`: `f` is used once,
    `1 ≤ 1`.

The two together show the check is non-trivial: it accepts the linear use and rejects the
double-use, exactly distinguishing the sound program from the unsound one.

## Zero-axiom verification

`GradedLambda` is a plain inductive; `usage` is structural; the checks reduce to concrete `Bool`
comparisons closed by `rfl` / `Bool.noConfusion`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega` (verified by `#print axioms` in scratch before landing).
Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- A minimal graded λ-calculus (de Bruijn indices): the carrier on which the usage discipline is
demonstrated.  Distinct from the kernel's `RawTerm` — this is the focused object of study for the
usage dimension's metatheory; connecting the two (grade erasure) is DIM2-4. -/
inductive GradedLambda where
  | var : Nat → GradedLambda
  | lam : GradedLambda → GradedLambda
  | app : GradedLambda → GradedLambda → GradedLambda
  deriving DecidableEq, Repr

/-- Per-free-variable occurrence usage of a term over `scope` free variables (a length-`scope` grade
vector).  A variable contributes grade `1` at its position; applications ADD their operands' usages
(two uses of one variable combine `1 + 1 = ω`, the §6.1 usage semiring); a λ drops its binder's own
grade (`tail`), leaving the outer-context usage of the closure. -/
def GradedLambda.usage : Nat → GradedLambda → GradeVector
  | scope, .var index => GradeVector.single scope index UsageGrade.one
  | scope, .app function argument =>
      GradeVector.add (GradedLambda.usage scope function) (GradedLambda.usage scope argument)
  | scope, .lam body => GradeVector.tail (GradedLambda.usage (scope + 1) body)

/-- **The usage check.**  A term is well-graded in a context of declared grades iff every free
variable is used no more than its declared grade — `usage ≤ declaredGrades` pointwise, via the
partial order `GradeVector.IsPointwiseBelow`.  Decidable in principle (the order is decidable on the
finite grade lattice); the concrete witnesses below exhibit it accepting / rejecting. -/
def GradedLambda.WellGraded (scope : Nat) (term : GradedLambda)
    (declaredGrades : GradeVector) : Prop :=
  GradeVector.IsPointwiseBelow (GradedLambda.usage scope term) declaredGrades

/-! ## The §27.1 / §27.2 Atkey-2018 demonstration -/

/-- The Atkey-2018 counterexample's inner closure `λx. f (f x)` with `f` free (`f` is de Bruijn `1`
under the inner `λx`).  `f` is used TWICE in the body — the unsound double-use of a linear resource
the broken Lam rule permitted. -/
def atkeyClosure : GradedLambda := .lam (.app (.var 1) (.app (.var 1) (.var 0)))

/-- The linear-discipline-respecting closure `λx. f x` with `f` free: `f` is used ONCE. -/
def linearClosure : GradedLambda := .lam (.app (.var 1) (.var 0))

/-- The declared-linear context for a single free variable `f :_1`. -/
def linearContext : GradeVector := GradeVector.cons UsageGrade.one GradeVector.nil

/-- Computed: `f`'s occurrence usage in the Atkey closure is `ω` (it is used twice). -/
theorem atkey_usage :
    GradedLambda.usage 1 atkeyClosure = GradeVector.cons UsageGrade.omega GradeVector.nil :=
  rfl

/-- Computed: `f`'s occurrence usage in the linear closure is `1` (it is used once). -/
theorem linear_usage :
    GradedLambda.usage 1 linearClosure = GradeVector.cons UsageGrade.one GradeVector.nil :=
  rfl

/-- **The Atkey-2018 broken-Lam rejection (§27.1 / §27.2).**  `λx. f (f x)` is NOT well-graded when
`f` is declared linear: `f`'s occurrence usage is `ω`, and `ω ≤ 1` is false.  The Wood/Atkey 2022
corrected discipline rejects capturing a linear variable in a closure that uses it twice — the
permanent regression witness for the Atkey-2018 grade-corpus bug. -/
theorem atkey_rejected : ¬ GradedLambda.WellGraded 1 atkeyClosure linearContext := by
  intro wellGraded
  obtain ⟨headBelow, _⟩ := wellGraded
  exact Bool.noConfusion headBelow

/-- **The linear use is accepted.**  `λx. f x` IS well-graded with `f` declared linear: `f`'s
occurrence usage is `1`, and `1 ≤ 1`.  Paired with `atkey_rejected`, this shows the check is
non-vacuous — it draws the line exactly between the sound and unsound programs. -/
theorem linear_accepted : GradedLambda.WellGraded 1 linearClosure linearContext :=
  ⟨rfl, True.intro⟩

/-! ## The usage check as a verified decision procedure -/

/-- The usage check as a computable Boolean: `usage ≤ declaredGrades`.  This is what a grade-checker
actually runs (the `Prop`-valued `WellGraded` is its specification). -/
def GradedLambda.wellGradedCheck (scope : Nat) (term : GradedLambda)
    (declaredGrades : GradeVector) : Bool :=
  GradeVector.isPointwiseBelowBool (GradedLambda.usage scope term) declaredGrades

/-- **Correctness of the usage check:** `wellGradedCheck = true ↔ WellGraded` — the computable check
decides well-gradedness.  A direct corollary of `GradeVector.isPointwiseBelowBool_correct`, so the
usage dimension's check is a genuine, verified decision procedure (not just a `Prop`). -/
theorem GradedLambda.wellGradedCheck_correct (scope : Nat) (term : GradedLambda)
    (declaredGrades : GradeVector) :
    GradedLambda.wellGradedCheck scope term declaredGrades = true ↔
      GradedLambda.WellGraded scope term declaredGrades :=
  GradeVector.isPointwiseBelowBool_correct (GradedLambda.usage scope term) declaredGrades

/-- The check COMPUTES `false` on the Atkey closure (`f` used at `ω`, declared linear) — the
decision procedure agrees with `atkey_rejected`, by `rfl`. -/
theorem atkey_check_false :
    GradedLambda.wellGradedCheck 1 atkeyClosure linearContext = false := rfl

/-- The check COMPUTES `true` on the linear closure (`f` used once, declared linear) — the decision
procedure agrees with `linear_accepted`, by `rfl`. -/
theorem linear_check_true :
    GradedLambda.wellGradedCheck 1 linearClosure linearContext = true := rfl

/-! ## The occurrence check is NOT subject-reduction-closed (§27.2 / §27.3)

The check correctly DECIDES well-gradedness — but well-gradedness is not preserved under
β-reduction.  The witness is the classic linearity violation `(λx. x x) g`: a linear `g` fed to a
self-duplicating function is well-graded (`g` appears ONCE syntactically), yet its β-reduct `g g`
uses `g` twice (`ω`).  The naive `usage ≤ Γ` check under-counts a linear resource that a function
consumes multiply INSIDE its body — precisely the unsoundness the Wood/Atkey discipline fixes by
tracking the lambda's binder grade and scaling the argument's usage by it in the App rule (which
this occurrence check omits).  So a sound graded judgment CANNOT be the bare occurrence check; this
is the concrete reason the corrected Lam rule (DIM2-3, the contextDivide/`1/ω=0` machinery) is
needed.  `substAt` + `BetaStep` below are the de Bruijn machinery that lets the β-reduct be a
THEOREM rather than an assertion. -/

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

/-- `(λx. x x) g` — `g` (de Bruijn `0`) fed to a self-duplicating function. -/
def dupRedex : GradedLambda := .app (.lam (.app (.var 0) (.var 0))) (.var 0)

/-- Its β-reduct `g g`. -/
def dupReduct : GradedLambda := .app (.var 0) (.var 0)

/-- The declared-linear context `g :_1`. -/
def linearG : GradeVector := GradeVector.cons UsageGrade.one GradeVector.nil

/-- `(λx. x x) g` really does β-reduce to `g g` (the reduct is the computed substitution). -/
theorem dupRedex_beta : GradedLambda.BetaStep dupRedex dupReduct :=
  GradedLambda.BetaStep.beta (.app (.var 0) (.var 0)) (.var 0)

/-- The redex IS well-graded: `g` is used ONCE syntactically — its two uses are hidden inside the
function, which only the binder grade would expose. -/
theorem dupRedex_wellGraded : GradedLambda.WellGraded 1 dupRedex linearG :=
  ⟨rfl, True.intro⟩

/-- The reduct is NOT well-graded: after β, `g` is used twice (`ω`), exceeding its linear `1`. -/
theorem dupReduct_illGraded : ¬ GradedLambda.WellGraded 1 dupReduct linearG := by
  intro wellGraded
  obtain ⟨headBelow, _⟩ := wellGraded
  exact Bool.noConfusion headBelow

/-- **The occurrence-usage check is NOT subject-reduction-closed.**  There is a well-graded term
whose β-reduct is ill-graded: `(λx. x x) g ↝ g g` with `g` linear.  Hence the bare occurrence check
is unsound under reduction; a sound graded judgment must track binder grades and scale arguments in
App (the Wood/Atkey correction).  The permanent regression witness for this naive-grade-check
limitation (§27.2 / §27.3). -/
theorem usage_check_fails_subject_reduction :
    ∃ (redex reduct : GradedLambda) (declared : GradeVector),
      GradedLambda.BetaStep redex reduct ∧
        GradedLambda.WellGraded 1 redex declared ∧
        ¬ GradedLambda.WellGraded 1 reduct declared :=
  ⟨dupRedex, dupReduct, linearG, dupRedex_beta, dupRedex_wellGraded, dupReduct_illGraded⟩

end FX1Poly.Modal
