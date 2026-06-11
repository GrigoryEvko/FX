import FX1Poly.Modal.GradedTypingGeneric
import FX1Poly.Modal.GradedReductionConfluence
import FX1Poly.Modal.ResourceGraded

/-! # FX1Poly/Modal/GradedBinaryParametricity — binary parametricity over the grade discipline (OP1-M0)

The Milestone-0 crux of the OP1 (univalent parametricity) arc: a BINARY logical relation over
`GradedLambda`, indexed by the GRADED simple types `GTypeOver R`, with the fundamental theorem proved
over the GRADED judgment `HasGradeOver R` — answering whether the grade discipline (the co-effect Lam
rule that records the binder grade, the App scaling) obstructs the relational interpretation at the
function former.

**The M0 verdict: GO.**  The relational arrow interpretation threads through the graded Lam/App rules
with the binder grade carried INERTLY — recorded in the arrow type, never consumed by the relation.
Binary parametricity composes with EVERY graded dimension exactly the way SN did (DIM2-5/DIM5-4): the
relation is grade-blind at Milestone 0, and the fundamental theorem holds for any ordered grade
semiring `R` with no per-dimension work.  The grade-AWARE refinement — relations that scale by the
binder grade, the relation-grade scaling laws — is OP1-M1's content, for which this file is the
template.

  * `RespectsExpansion baseRel` — the base-observation relation is closed under head β-expansion on
    either side (the one obligation the lam arm of the fundamental theorem imposes).
  * `ParametricRel baseRel : GTypeOver R → GradedLambda → GradedLambda → Prop` — the relation, by
    structural recursion on the type: `base` is `baseRel`; `arrow _ dom cod` relates two terms when
    they map `dom`-related arguments to `cod`-related applications.  The binder grade is DISCARDED.
  * `ParametricRel.expandLeft` / `expandRight` — head-expansion closure, lifted from the base
    obligation through the arrow by induction on the type (the left/right `congAppLeft` step).
  * `ParametricSubstitution` + `cons` — pointwise-related closing substitution pairs (the binary twin
    of the unary fundamental theorem's `ReducibleSubstitution`).
  * `HasGradeOver.parametric` — ★ **the binary fundamental theorem over the GRADED judgment**: a
    graded-typed term maps related closing substitutions to related instances.  The lam arm composes
    the two β-expansions with the β-composition bridge `substAt_zero_applySubstitution_lift` into the
    extended related environment — the graded binder grade flows through untouched.
  * `HasGradeOver.parametricClosed` — the closed abstraction theorem: every CLOSED graded-typed term
    is parametrically related to ITSELF, for every expansion-closed observation (vacuous environment
    + the identity-substitution collapse).  (At base type this is non-degenerate only because the
    graded calculus is a consistent logic — `GRADED-CONSISTENCY` — there are no closed base atoms.)
  * `joinabilityRespectsExpansion` + `linearUsageFunction_mapsJoinable` — ★ the LINEAR-usage free
    theorem demo: every closed function of the linear arrow `base -(1)-> base` (over
    `fxUsageSemiring`) maps β-joinable arguments to β-joinable results.  No assumption on the
    function beyond its graded typing — the abstraction theorem at the task's pinned instance.

## Zero-axiom verification

`ParametricRel` is structural recursion on a plain inductive (`GTypeOver`); the expansion closures
are `induction` on the type with `Reduces.congAppLeft/Right`; the fundamental theorem is `induction`
on the judgment with the β-composition rewrite (the unary fundamental theorem's lam-arm recipe,
doubled); the closed corollary refutes the empty-context lookup with `Option.noConfusion` and
collapses the identity substitution with `applySubstitution_id`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditModal.lean`. -/

namespace FX1Poly.Modal

open FX1Poly.Core (ReflTransClosure Joinable)

/-- The base-observation relation is closed under head β-expansion on either side — the one
obligation the fundamental theorem's lam arm imposes on the observation. -/
structure RespectsExpansion (baseRel : GradedLambda → GradedLambda → Prop) : Prop where
  expandLeft : ∀ {leftSource leftReduct rightTerm : GradedLambda},
    GradedLambda.Reduces leftSource leftReduct → baseRel leftReduct rightTerm →
    baseRel leftSource rightTerm
  expandRight : ∀ {leftTerm rightSource rightReduct : GradedLambda},
    GradedLambda.Reduces rightSource rightReduct → baseRel leftTerm rightReduct →
    baseRel leftTerm rightSource

/-- **The binary parametricity relation** over the graded types, by structural recursion: at `base`
the observation itself; at `arrow _ dom cod` the map-related-to-related condition.  The binder grade
is DISCARDED — the Milestone-0 relation is grade-blind (the grade-aware scaling refinement is
OP1-M1). -/
def ParametricRel {R : OrderedGradeSemiring} (baseRel : GradedLambda → GradedLambda → Prop) :
    GTypeOver R → GradedLambda → GradedLambda → Prop
  | .base, leftTerm, rightTerm => baseRel leftTerm rightTerm
  | .arrow _binderGrade domain codomain, leftTerm, rightTerm =>
      ∀ (leftArgument rightArgument : GradedLambda),
        ParametricRel baseRel domain leftArgument rightArgument →
        ParametricRel baseRel codomain (.app leftTerm leftArgument) (.app rightTerm rightArgument)

/-- Head-expansion closure on the LEFT side, lifted from the base obligation through the arrow by
induction on the type. -/
theorem ParametricRel.expandLeft {R : OrderedGradeSemiring}
    {baseRel : GradedLambda → GradedLambda → Prop} (respects : RespectsExpansion baseRel)
    (resultType : GTypeOver R) :
    ∀ {leftSource leftReduct rightTerm : GradedLambda},
      GradedLambda.Reduces leftSource leftReduct →
      ParametricRel baseRel resultType leftReduct rightTerm →
      ParametricRel baseRel resultType leftSource rightTerm := by
  induction resultType with
  | base =>
      intro _ _ _ step related
      exact respects.expandLeft step related
  | arrow binderGrade domain codomain _domainIH codomainIH =>
      intro leftSource leftReduct rightTerm step related
      intro leftArgument rightArgument argumentRelated
      exact codomainIH
        (GradedLambda.Reduces.congAppLeft leftSource leftReduct leftArgument step)
        (related leftArgument rightArgument argumentRelated)

/-- Head-expansion closure on the RIGHT side (mirror of `expandLeft`). -/
theorem ParametricRel.expandRight {R : OrderedGradeSemiring}
    {baseRel : GradedLambda → GradedLambda → Prop} (respects : RespectsExpansion baseRel)
    (resultType : GTypeOver R) :
    ∀ {leftTerm rightSource rightReduct : GradedLambda},
      GradedLambda.Reduces rightSource rightReduct →
      ParametricRel baseRel resultType leftTerm rightReduct →
      ParametricRel baseRel resultType leftTerm rightSource := by
  induction resultType with
  | base =>
      intro _ _ _ step related
      exact respects.expandRight step related
  | arrow binderGrade domain codomain _domainIH codomainIH =>
      intro leftTerm rightSource rightReduct step related
      intro leftArgument rightArgument argumentRelated
      exact codomainIH
        (GradedLambda.Reduces.congAppLeft rightSource rightReduct rightArgument step)
        (related leftArgument rightArgument argumentRelated)

/-- A PAIR of closing substitutions is parametrically related at a context when every variable's two
images are related at its declared type — the binary twin of `ReducibleSubstitution`. -/
def ParametricSubstitution {R : OrderedGradeSemiring}
    (baseRel : GradedLambda → GradedLambda → Prop) (typeContext : List (GTypeOver R))
    (leftSubstitution rightSubstitution : TermSubstitution) : Prop :=
  ∀ (index : Nat) (varType : GTypeOver R),
    GTypeOver.lookup typeContext index = some varType →
    ParametricRel baseRel varType (leftSubstitution index) (rightSubstitution index)

/-- Extend a related substitution pair under a binder (the lam-arm environment extension). -/
theorem ParametricSubstitution.cons {R : OrderedGradeSemiring}
    {baseRel : GradedLambda → GradedLambda → Prop} {domain : GTypeOver R}
    {leftHead rightHead : GradedLambda} {typeContext : List (GTypeOver R)}
    {leftTail rightTail : TermSubstitution}
    (headRelated : ParametricRel baseRel domain leftHead rightHead)
    (tailRelated : ParametricSubstitution baseRel typeContext leftTail rightTail) :
    ParametricSubstitution baseRel (domain :: typeContext)
      (consSubstitution leftHead leftTail) (consSubstitution rightHead rightTail) := by
  intro index varType lookupEq
  cases index with
  | zero =>
      have domainEq : domain = varType := Option.some.inj lookupEq
      rw [← domainEq]
      exact headRelated
  | succ predecessor => exact tailRelated predecessor varType lookupEq

/-- ★ **The binary fundamental theorem over the GRADED judgment**: a term typed by `HasGradeOver R`
maps parametrically related closing substitutions to parametrically related instances — for EVERY
ordered grade semiring `R`.  The lam arm composes two β-expansions (one per side) with the
β-composition bridge into the extended related environment; the binder grade recorded by the graded
Lam rule flows through INERTLY.  This is the Milestone-0 GO verdict: the grade discipline does not
obstruct binary parametricity at the function former. -/
theorem HasGradeOver.parametric {R : OrderedGradeSemiring}
    {baseRel : GradedLambda → GradedLambda → Prop} (respects : RespectsExpansion baseRel)
    {typeContext : List (GTypeOver R)} {grades : GradeVectorOver R} {term : GradedLambda}
    {resultType : GTypeOver R} (typed : HasGradeOver R typeContext grades term resultType) :
    ∀ (leftSubstitution rightSubstitution : TermSubstitution),
      ParametricSubstitution baseRel typeContext leftSubstitution rightSubstitution →
      ParametricRel baseRel resultType
        (GradedLambda.applySubstitution leftSubstitution term)
        (GradedLambda.applySubstitution rightSubstitution term) := by
  induction typed with
  | var typeContext index varType lookupOk =>
      intro leftSubstitution rightSubstitution relatedSubst
      exact relatedSubst index varType lookupOk
  | lam typeContext binderGrade domain codomain outerGrades body _bodyTyped bodyIH =>
      intro leftSubstitution rightSubstitution relatedSubst
      show ParametricRel baseRel (.arrow binderGrade domain codomain)
        (GradedLambda.lam
          (GradedLambda.applySubstitution (liftSubstitution leftSubstitution) body))
        (GradedLambda.lam
          (GradedLambda.applySubstitution (liftSubstitution rightSubstitution) body))
      intro leftArgument rightArgument argumentRelated
      apply ParametricRel.expandLeft respects codomain
        (GradedLambda.Reduces.beta
          (GradedLambda.applySubstitution (liftSubstitution leftSubstitution) body) leftArgument)
      apply ParametricRel.expandRight respects codomain
        (GradedLambda.Reduces.beta
          (GradedLambda.applySubstitution (liftSubstitution rightSubstitution) body) rightArgument)
      rw [substAt_zero_applySubstitution_lift body leftArgument leftSubstitution,
        substAt_zero_applySubstitution_lift body rightArgument rightSubstitution]
      exact bodyIH (consSubstitution leftArgument leftSubstitution)
        (consSubstitution rightArgument rightSubstitution)
        (ParametricSubstitution.cons argumentRelated relatedSubst)
  | app typeContext binderGrade domain codomain functionGrades argumentGrades function argument
      _functionTyped _argumentTyped functionIH argumentIH =>
      intro leftSubstitution rightSubstitution relatedSubst
      show ParametricRel baseRel codomain
        (.app (GradedLambda.applySubstitution leftSubstitution function)
          (GradedLambda.applySubstitution leftSubstitution argument))
        (.app (GradedLambda.applySubstitution rightSubstitution function)
          (GradedLambda.applySubstitution rightSubstitution argument))
      exact functionIH leftSubstitution rightSubstitution relatedSubst
        (GradedLambda.applySubstitution leftSubstitution argument)
        (GradedLambda.applySubstitution rightSubstitution argument)
        (argumentIH leftSubstitution rightSubstitution relatedSubst)

/-- ★ **The closed abstraction theorem**: every CLOSED graded-typed term is parametrically related
to ITSELF, for every expansion-closed observation — the empty-context environment is vacuous and the
identity substitution collapses.  (Non-degenerate at base type only because the graded calculus has
no closed base atoms — `GRADED-CONSISTENCY`.) -/
theorem HasGradeOver.parametricClosed {R : OrderedGradeSemiring}
    {baseRel : GradedLambda → GradedLambda → Prop} (respects : RespectsExpansion baseRel)
    {grades : GradeVectorOver R} {term : GradedLambda} {resultType : GTypeOver R}
    (typed : HasGradeOver R [] grades term resultType) :
    ParametricRel baseRel resultType term term := by
  have emptyRelated : ParametricSubstitution baseRel ([] : List (GTypeOver R))
      (fun index => GradedLambda.var index) (fun index => GradedLambda.var index) := by
    intro index varType lookupEq
    cases index with
    | zero => nomatch lookupEq
    | succ _ => nomatch lookupEq
  have related := typed.parametric respects
    (fun index => GradedLambda.var index) (fun index => GradedLambda.var index) emptyRelated
  rw [GradedLambda.applySubstitution_id] at related
  exact related

/-! ## The linear-usage free-theorem demonstration -/

/-- β-joinability respects head expansion on either side — prepend the step to the star leg. -/
theorem joinabilityRespectsExpansion :
    RespectsExpansion (Joinable GradedLambda.Reduces) where
  expandLeft := fun step joined =>
    match joined with
    | ⟨commonReduct, leftStar, rightStar⟩ =>
        ⟨commonReduct, ReflTransClosure.head step leftStar, rightStar⟩
  expandRight := fun step joined =>
    match joined with
    | ⟨commonReduct, leftStar, rightStar⟩ =>
        ⟨commonReduct, leftStar, ReflTransClosure.head step rightStar⟩

/-- ★ **The linear-usage free theorem** (the OP1-M0 pinned instance): every CLOSED function typed at
the LINEAR graded arrow `base -(1)-> base` over the usage semiring maps β-joinable arguments to
β-joinable results — with NO assumption on the function beyond its graded typing.  The abstraction
theorem instantiated at the task's "linear usage, function former" crux. -/
theorem linearUsageFunction_mapsJoinable
    {grades : GradeVectorOver fxUsageSemiring} {functionTerm : GradedLambda}
    (typed : HasGradeOver fxUsageSemiring [] grades functionTerm
      (.arrow UsageGrade.one .base .base))
    {leftArgument rightArgument : GradedLambda}
    (argumentsJoinable : Joinable GradedLambda.Reduces leftArgument rightArgument) :
    Joinable GradedLambda.Reduces
      (.app functionTerm leftArgument) (.app functionTerm rightArgument) :=
  typed.parametricClosed joinabilityRespectsExpansion
    leftArgument rightArgument argumentsJoinable

end FX1Poly.Modal
