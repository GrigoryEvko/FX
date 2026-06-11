import FX1Poly.Modal.GradedBinaryParametricity

/-! # FX1Poly/Modal/GradedRelationScaling — grade-AWARE binary parametricity (OP1-M1)

The grade-aware refinement of the Milestone-0 binary parametricity: RELATIONS now scale by the
binder grade.  Where OP1-M0's relation discarded the grade, here each grade acts on the relation
lattice — `zero` collapses the relation to TOTAL (an unused argument imposes NO relatedness
obligation), `one` and `omega` keep it — and the graded arrow `dom -(r)-> cod` relates two
functions when they map `r`-SCALED-related arguments to related applications.

  * `RelationGradeAction R` — the abstract relation-grade scaling laws: identity at `one`, total at
    `zero`, and SPLITTING along `add` (an environment shared by two subderivations at grade `p + q`
    serves each at its own grade — the substructural accounting the App rule's
    `functionGrades + r · argumentGrades` demands).
  * `usageRelationScale` + `usageRelationScaleAction` — the lawful USAGE instance: `zero ↦ total`,
    `one ↦ id`, `omega ↦ id`; the splitting law is the 9-case `add` table check.
  * `UsageParametricRel baseRel : GTypeOver fxUsageSemiring → …` — the grade-aware relation; the
    arrow case quantifies over `usageRelationScale binderGrade`-related arguments.
  * `GradedParametricSubstitution` — the GRADE-VECTOR-indexed related environment: each binding's
    two images are related at the binding's OWN grade (cons takes an `act headGrade`-related head).
  * Environment algebra: `lookupRelated` (the var arm — the `single … one` vector yields plain
    relatedness at the looked-up index), `splitAdd` (the App accounting — env at `add p q` splits
    into env at `p` and env at `q`, via the action's splitting law), `collapseScaleNonzero` (env at
    `scale r g` collapses to env at `g` for `r ≠ zero` — the usage absorption `r·h ≈ h` on the
    relation side).
  * ★ `HasGradeOver.parametricGraded` — the GRADE-AWARE fundamental theorem over the usage
    judgment.  The lam arm threads the binder grade DIRECTLY into the environment cons (the graded
    co-effect Lam is exactly the env extension); the app arm splits the environment and cases on
    the binder grade: at `zero` the argument needs NO relatedness (the function relation's
    obligation is total — the argument IH is never consulted); at `one`/`omega` the scaled
    environment collapses and the argument IH supplies plain relatedness.
  * ★ `zeroUsageFunction_mapsAnythingToJoinable` — the flagship grade-aware FREE THEOREM,
    impossible at M0: a closed function typed at the ZERO-graded arrow `base -(0)-> base` maps
    ARBITRARY (unrelated!) arguments to β-joinable results — the type system's "argument unused"
    grade becomes a relational guarantee.  `linearUsageFunction_mapsJoinableGraded` re-derives the
    M0 linear free theorem through the graded relation (the `one`-grade instance).

## Zero-axiom verification

The action laws are 9-case `UsageGrade` enumerations closing by `trivial`/`exact`; the environment
algebra is induction over the inductive environment with defeq vector-index retyping (`add`/`scale`
whnf to `cons` before `cases`); the fundamental theorem doubles the M0 lam-arm recipe and cases the
binder grade at the app arm.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditModalGradedSubstitution.lean`. -/

namespace FX1Poly.Modal

open FX1Poly.Core (ReflTransClosure Joinable)

/-- **The abstract relation-grade scaling laws** over an ordered grade semiring: a grade action on
binary term relations with identity at `one`, totality at `zero`, and splitting along `add`. -/
structure RelationGradeAction (R : OrderedGradeSemiring) where
  act : R.Carrier → (GradedLambda → GradedLambda → Prop) →
    GradedLambda → GradedLambda → Prop
  actAtOne : ∀ (relation : GradedLambda → GradedLambda → Prop)
    (leftTerm rightTerm : GradedLambda),
    act R.one relation leftTerm rightTerm ↔ relation leftTerm rightTerm
  actAtZeroTotal : ∀ (relation : GradedLambda → GradedLambda → Prop)
    (leftTerm rightTerm : GradedLambda), act R.zero relation leftTerm rightTerm
  actAddSplit : ∀ (firstGrade secondGrade : R.Carrier)
    (relation : GradedLambda → GradedLambda → Prop) (leftTerm rightTerm : GradedLambda),
    act (R.add firstGrade secondGrade) relation leftTerm rightTerm →
    act firstGrade relation leftTerm rightTerm ∧ act secondGrade relation leftTerm rightTerm

/-- The USAGE relation-grade scaling: `zero` imposes nothing (total), `one` and `omega` keep the
relation.  The {0,1,ω} shape of "how related must an argument be that is used this often". -/
def usageRelationScale : UsageGrade → (GradedLambda → GradedLambda → Prop) →
    GradedLambda → GradedLambda → Prop
  | .zero, _ => fun _ _ => True
  | .one, relation => relation
  | .omega, relation => relation

/-- The usage scaling is a lawful `RelationGradeAction` — the splitting law is the 9-case `add`
table check (`1+1 = ω` keeps the relation on both sides; any `zero` summand contributes the
total obligation). -/
def usageRelationScaleAction : RelationGradeAction fxUsageSemiring where
  act := usageRelationScale
  actAtOne := fun _ _ _ => Iff.rfl
  actAtZeroTotal := fun _ _ _ => True.intro
  actAddSplit := fun firstGrade secondGrade _ _ _ scaledRelated => by
    cases firstGrade <;> cases secondGrade <;>
      first
        | exact ⟨scaledRelated, scaledRelated⟩
        | exact ⟨True.intro, scaledRelated⟩
        | exact ⟨scaledRelated, True.intro⟩

/-- **The grade-aware binary parametricity relation** over the usage-graded types: `base` is the
observation; `arrow r dom cod` relates two functions when they map `r`-SCALED-related arguments to
related applications.  The binder grade now genuinely participates. -/
def UsageParametricRel (baseRel : GradedLambda → GradedLambda → Prop) :
    GTypeOver fxUsageSemiring → GradedLambda → GradedLambda → Prop
  | .base, leftTerm, rightTerm => baseRel leftTerm rightTerm
  | .arrow binderGrade domain codomain, leftTerm, rightTerm =>
      ∀ (leftArgument rightArgument : GradedLambda),
        usageRelationScale binderGrade
          (UsageParametricRel baseRel domain) leftArgument rightArgument →
        UsageParametricRel baseRel codomain
          (.app leftTerm leftArgument) (.app rightTerm rightArgument)

/-- Left head-expansion closure for the grade-aware relation (the scaled argument hypothesis
passes through unchanged). -/
theorem UsageParametricRel.expandLeft
    {baseRel : GradedLambda → GradedLambda → Prop} (respects : RespectsExpansion baseRel)
    (resultType : GTypeOver fxUsageSemiring) :
    ∀ {leftSource leftReduct rightTerm : GradedLambda},
      GradedLambda.Reduces leftSource leftReduct →
      UsageParametricRel baseRel resultType leftReduct rightTerm →
      UsageParametricRel baseRel resultType leftSource rightTerm := by
  induction resultType with
  | base =>
      intro _ _ _ step related
      exact respects.expandLeft step related
  | arrow binderGrade domain codomain _domainIH codomainIH =>
      intro leftSource leftReduct rightTerm step related
      intro leftArgument rightArgument argumentScaledRelated
      exact codomainIH
        (GradedLambda.Reduces.congAppLeft leftSource leftReduct leftArgument step)
        (related leftArgument rightArgument argumentScaledRelated)

/-- Right head-expansion closure (mirror). -/
theorem UsageParametricRel.expandRight
    {baseRel : GradedLambda → GradedLambda → Prop} (respects : RespectsExpansion baseRel)
    (resultType : GTypeOver fxUsageSemiring) :
    ∀ {leftTerm rightSource rightReduct : GradedLambda},
      GradedLambda.Reduces rightSource rightReduct →
      UsageParametricRel baseRel resultType leftTerm rightReduct →
      UsageParametricRel baseRel resultType leftTerm rightSource := by
  induction resultType with
  | base =>
      intro _ _ _ step related
      exact respects.expandRight step related
  | arrow binderGrade domain codomain _domainIH codomainIH =>
      intro leftTerm rightSource rightReduct step related
      intro leftArgument rightArgument argumentScaledRelated
      exact codomainIH
        (GradedLambda.Reduces.congAppLeft rightSource rightReduct rightArgument step)
        (related leftArgument rightArgument argumentScaledRelated)

/-- **The grade-vector-indexed related environment**: each binding's two images are related at the
binding's OWN grade — the cons takes an `act headGrade`-related head, mirroring the graded Lam
rule's vector cons. -/
inductive GradedParametricSubstitution (baseRel : GradedLambda → GradedLambda → Prop) :
    List (GTypeOver fxUsageSemiring) → GradeVectorOver fxUsageSemiring →
    TermSubstitution → TermSubstitution → Prop where
  | nil (leftSubstitution rightSubstitution : TermSubstitution) :
      GradedParametricSubstitution baseRel [] .nil leftSubstitution rightSubstitution
  | cons {domain : GTypeOver fxUsageSemiring} {typeContext : List (GTypeOver fxUsageSemiring)}
      {headGrade : UsageGrade} {restGrades : GradeVectorOver fxUsageSemiring}
      {leftHead rightHead : GradedLambda} {leftTail rightTail : TermSubstitution}
      (headRelated : usageRelationScale headGrade
        (UsageParametricRel baseRel domain) leftHead rightHead)
      (tailRelated : GradedParametricSubstitution baseRel typeContext restGrades
        leftTail rightTail) :
      GradedParametricSubstitution baseRel (domain :: typeContext) (.cons headGrade restGrades)
        (consSubstitution leftHead leftTail) (consSubstitution rightHead rightTail)

/-- The var arm's environment lookup: at the `single … one` vector the looked-up binding's images
are PLAINLY related (act at `one` is the identity), and every other binding imposed nothing. -/
theorem GradedParametricSubstitution.lookupRelated
    {baseRel : GradedLambda → GradedLambda → Prop} :
    ∀ {typeContext : List (GTypeOver fxUsageSemiring)} {index : Nat}
      {varType : GTypeOver fxUsageSemiring}
      {leftSubstitution rightSubstitution : TermSubstitution},
      GTypeOver.lookup typeContext index = some varType →
      GradedParametricSubstitution baseRel typeContext
        (GradeVectorOver.single fxUsageSemiring typeContext.length index UsageGrade.one)
        leftSubstitution rightSubstitution →
      UsageParametricRel baseRel varType
        (leftSubstitution index) (rightSubstitution index)
  | headType :: restTypes, 0, varType, _, _, lookupEq, relatedEnv => by
      have envCons : GradedParametricSubstitution baseRel (headType :: restTypes)
          (.cons UsageGrade.one
            (GradeVectorOver.zero fxUsageSemiring restTypes.length))
          _ _ := relatedEnv
      cases envCons with
      | cons headRelated _ =>
          have varTypeEq : headType = varType := Option.some.inj lookupEq
          rw [← varTypeEq]
          exact headRelated
  | headType :: restTypes, index + 1, varType, _, _, lookupEq, relatedEnv => by
      have envCons : GradedParametricSubstitution baseRel (headType :: restTypes)
          (.cons UsageGrade.zero
            (GradeVectorOver.single fxUsageSemiring restTypes.length index UsageGrade.one))
          _ _ := relatedEnv
      cases envCons with
      | cons _ tailRelated =>
          have lookupTail : GTypeOver.lookup restTypes index = some varType := lookupEq
          exact GradedParametricSubstitution.lookupRelated
            (typeContext := restTypes) (index := index) (varType := varType)
            lookupTail tailRelated

/-- The App accounting: an environment related at `add firstGrades secondGrades` splits into one
related at `firstGrades` and one at `secondGrades` (the action's splitting law, threaded through
the telescope).  The length hypotheses rule out the truncating `add` arms. -/
theorem GradedParametricSubstitution.splitAdd
    {baseRel : GradedLambda → GradedLambda → Prop} :
    ∀ {typeContext : List (GTypeOver fxUsageSemiring)}
      (firstGrades secondGrades : GradeVectorOver fxUsageSemiring)
      {leftSubstitution rightSubstitution : TermSubstitution},
      firstGrades.length = typeContext.length →
      secondGrades.length = typeContext.length →
      GradedParametricSubstitution baseRel typeContext
        (GradeVectorOver.add firstGrades secondGrades) leftSubstitution rightSubstitution →
      GradedParametricSubstitution baseRel typeContext firstGrades
          leftSubstitution rightSubstitution ∧
        GradedParametricSubstitution baseRel typeContext secondGrades
          leftSubstitution rightSubstitution
  | [], .nil, .nil, leftSubstitution, rightSubstitution, _, _, _ =>
      ⟨.nil leftSubstitution rightSubstitution, .nil leftSubstitution rightSubstitution⟩
  | [], .nil, .cons _ _, _, _, _, secondLength, _ => Nat.noConfusion secondLength
  | [], .cons _ _, _, _, _, firstLength, _, _ => Nat.noConfusion firstLength
  | _ :: _, .nil, _, _, _, firstLength, _, _ => Nat.noConfusion firstLength
  | _ :: _, .cons _ _, .nil, _, _, _, secondLength, _ => Nat.noConfusion secondLength
  | headType :: restTypes, .cons firstHead firstRest, .cons secondHead secondRest,
      _, _, firstLength, secondLength, relatedEnv => by
      have envCons : GradedParametricSubstitution baseRel (headType :: restTypes)
          (.cons (UsageGrade.add firstHead secondHead)
            (GradeVectorOver.add firstRest secondRest)) _ _ := relatedEnv
      cases envCons with
      | cons headRelated tailRelated =>
          have headSplit := usageRelationScaleAction.actAddSplit firstHead secondHead
            (UsageParametricRel baseRel headType) _ _ headRelated
          have tailSplit := GradedParametricSubstitution.splitAdd firstRest secondRest
            (Nat.succ.inj firstLength) (Nat.succ.inj secondLength) tailRelated
          exact ⟨.cons headSplit.1 tailSplit.1, .cons headSplit.2 tailSplit.2⟩

/-- Scaling absorption at a NONZERO scalar: for `r ∈ {one, omega}` the usage product `r · h`
imposes the SAME relational obligation as `h` itself (`1·h = h`; `ω·0 = 0`, `ω·1 = ω` and
`act omega = act one` on relations), so an environment related at `scale r grades` is related at
`grades`. -/
theorem GradedParametricSubstitution.collapseScaleNonzero
    {baseRel : GradedLambda → GradedLambda → Prop} (scalar : UsageGrade)
    (scalarNonzero : scalar ≠ UsageGrade.zero) :
    ∀ {typeContext : List (GTypeOver fxUsageSemiring)}
      (grades : GradeVectorOver fxUsageSemiring)
      {leftSubstitution rightSubstitution : TermSubstitution},
      GradedParametricSubstitution baseRel typeContext
        (GradeVectorOver.scale scalar grades) leftSubstitution rightSubstitution →
      GradedParametricSubstitution baseRel typeContext grades
        leftSubstitution rightSubstitution
  | [], .nil, leftSubstitution, rightSubstitution, _ =>
      .nil leftSubstitution rightSubstitution
  | [], .cons _ _, _, _, scaledEnv => by
      have envAtCons : GradedParametricSubstitution baseRel []
          (.cons _ _) _ _ := scaledEnv
      cases envAtCons
  | _ :: _, .nil, _, _, scaledEnv => by
      have envAtNil : GradedParametricSubstitution baseRel (_ :: _) .nil _ _ := scaledEnv
      cases envAtNil
  | headType :: restTypes, .cons headGrade restGrades, _, _, scaledEnv => by
      have envCons : GradedParametricSubstitution baseRel (headType :: restTypes)
          (.cons (UsageGrade.mul scalar headGrade)
            (GradeVectorOver.scale scalar restGrades)) _ _ := scaledEnv
      cases envCons with
      | cons headRelated tailRelated =>
          have tailCollapsed := GradedParametricSubstitution.collapseScaleNonzero
            scalar scalarNonzero restGrades tailRelated
          cases scalar with
          | zero => exact absurd rfl scalarNonzero
          | one =>
              cases headGrade with
              | zero => exact .cons headRelated tailCollapsed
              | one => exact .cons headRelated tailCollapsed
              | omega => exact .cons headRelated tailCollapsed
          | omega =>
              cases headGrade with
              | zero => exact .cons headRelated tailCollapsed
              | one => exact .cons headRelated tailCollapsed
              | omega => exact .cons headRelated tailCollapsed

/-- ★ **The grade-aware fundamental theorem** over the usage-graded judgment: a graded-typed term
maps grade-vector-related closing substitutions to related instances — where each free variable's
relatedness obligation is scaled by ITS OWN usage grade.  The lam arm threads the binder grade
directly into the environment cons; the app arm splits the environment along the App accounting
and cases the binder grade (`zero`: the argument needs no relatedness at all; `one`/`omega`: the
scaled environment collapses and the argument IH fires). -/
theorem HasGradeOver.parametricGraded
    {baseRel : GradedLambda → GradedLambda → Prop} (respects : RespectsExpansion baseRel)
    {typeContext : List (GTypeOver fxUsageSemiring)} {grades : GradeVectorOver fxUsageSemiring}
    {term : GradedLambda} {resultType : GTypeOver fxUsageSemiring}
    (typed : HasGradeOver fxUsageSemiring typeContext grades term resultType) :
    ∀ (leftSubstitution rightSubstitution : TermSubstitution),
      GradedParametricSubstitution baseRel typeContext grades
        leftSubstitution rightSubstitution →
      UsageParametricRel baseRel resultType
        (GradedLambda.applySubstitution leftSubstitution term)
        (GradedLambda.applySubstitution rightSubstitution term) := by
  induction typed with
  | var typeContext index varType lookupOk =>
      intro leftSubstitution rightSubstitution relatedEnv
      exact GradedParametricSubstitution.lookupRelated lookupOk relatedEnv
  | lam typeContext binderGrade domain codomain outerGrades body _bodyTyped bodyIH =>
      intro leftSubstitution rightSubstitution relatedEnv
      show UsageParametricRel baseRel (.arrow binderGrade domain codomain)
        (GradedLambda.lam
          (GradedLambda.applySubstitution (liftSubstitution leftSubstitution) body))
        (GradedLambda.lam
          (GradedLambda.applySubstitution (liftSubstitution rightSubstitution) body))
      intro leftArgument rightArgument argumentScaledRelated
      apply UsageParametricRel.expandLeft respects codomain
        (GradedLambda.Reduces.beta
          (GradedLambda.applySubstitution (liftSubstitution leftSubstitution) body)
          leftArgument)
      apply UsageParametricRel.expandRight respects codomain
        (GradedLambda.Reduces.beta
          (GradedLambda.applySubstitution (liftSubstitution rightSubstitution) body)
          rightArgument)
      rw [substAt_zero_applySubstitution_lift body leftArgument leftSubstitution,
        substAt_zero_applySubstitution_lift body rightArgument rightSubstitution]
      exact bodyIH (consSubstitution leftArgument leftSubstitution)
        (consSubstitution rightArgument rightSubstitution)
        (GradedParametricSubstitution.cons argumentScaledRelated relatedEnv)
  | app typeContext binderGrade domain codomain functionGrades argumentGrades function argument
      functionTyped argumentTyped functionIH argumentIH =>
      intro leftSubstitution rightSubstitution relatedEnv
      show UsageParametricRel baseRel codomain
        (.app (GradedLambda.applySubstitution leftSubstitution function)
          (GradedLambda.applySubstitution leftSubstitution argument))
        (.app (GradedLambda.applySubstitution rightSubstitution function)
          (GradedLambda.applySubstitution rightSubstitution argument))
      have functionLength : functionGrades.length = typeContext.length :=
        hasGradeOver_length functionTyped
      have argumentLength : argumentGrades.length = typeContext.length :=
        hasGradeOver_length argumentTyped
      have scaledLength :
          (GradeVectorOver.scale binderGrade argumentGrades).length = typeContext.length := by
        rw [GradeVectorOver.scale_length]
        exact argumentLength
      have envSplit := GradedParametricSubstitution.splitAdd functionGrades
        (GradeVectorOver.scale binderGrade argumentGrades)
        functionLength scaledLength relatedEnv
      have functionRelated := functionIH leftSubstitution rightSubstitution envSplit.1
      cases binderGrade with
      | zero =>
          exact functionRelated
            (GradedLambda.applySubstitution leftSubstitution argument)
            (GradedLambda.applySubstitution rightSubstitution argument)
            True.intro
      | one =>
          have argumentEnv := GradedParametricSubstitution.collapseScaleNonzero
            UsageGrade.one (fun absurdEq => UsageGrade.noConfusion absurdEq)
            argumentGrades envSplit.2
          exact functionRelated
            (GradedLambda.applySubstitution leftSubstitution argument)
            (GradedLambda.applySubstitution rightSubstitution argument)
            (argumentIH leftSubstitution rightSubstitution argumentEnv)
      | omega =>
          have argumentEnv := GradedParametricSubstitution.collapseScaleNonzero
            UsageGrade.omega (fun absurdEq => UsageGrade.noConfusion absurdEq)
            argumentGrades envSplit.2
          exact functionRelated
            (GradedLambda.applySubstitution leftSubstitution argument)
            (GradedLambda.applySubstitution rightSubstitution argument)
            (argumentIH leftSubstitution rightSubstitution argumentEnv)

/-- The closed grade-aware abstraction theorem (vacuous empty environment + the
identity-substitution collapse). -/
theorem HasGradeOver.parametricGradedClosed
    {baseRel : GradedLambda → GradedLambda → Prop} (respects : RespectsExpansion baseRel)
    {grades : GradeVectorOver fxUsageSemiring} {term : GradedLambda}
    {resultType : GTypeOver fxUsageSemiring}
    (typed : HasGradeOver fxUsageSemiring [] grades term resultType) :
    UsageParametricRel baseRel resultType term term := by
  have gradesNil : grades = .nil := by
    have lengthZero : grades.length = 0 := hasGradeOver_length typed
    cases grades with
    | nil => rfl
    | cons _ _ => exact Nat.noConfusion lengthZero
  rw [gradesNil] at typed
  have related := typed.parametricGraded respects
    (fun index => GradedLambda.var index) (fun index => GradedLambda.var index)
    (.nil _ _)
  rw [GradedLambda.applySubstitution_id] at related
  exact related

/-- ★ **The ZERO-grade free theorem** (impossible at grade-blind M0): a closed function typed at
the zero-graded arrow `base -(0)-> base` maps ARBITRARY — entirely UNRELATED — arguments to
β-joinable results.  The type system's "argument unused" grade is a relational guarantee. -/
theorem zeroUsageFunction_mapsAnythingToJoinable
    {grades : GradeVectorOver fxUsageSemiring} {functionTerm : GradedLambda}
    (typed : HasGradeOver fxUsageSemiring [] grades functionTerm
      (.arrow UsageGrade.zero .base .base))
    (leftArgument rightArgument : GradedLambda) :
    Joinable GradedLambda.Reduces
      (.app functionTerm leftArgument) (.app functionTerm rightArgument) :=
  typed.parametricGradedClosed joinabilityRespectsExpansion
    leftArgument rightArgument True.intro

/-- The linear free theorem re-derived through the GRADE-AWARE relation (the `one`-grade
instance) — joinable arguments map to joinable results. -/
theorem linearUsageFunction_mapsJoinableGraded
    {grades : GradeVectorOver fxUsageSemiring} {functionTerm : GradedLambda}
    (typed : HasGradeOver fxUsageSemiring [] grades functionTerm
      (.arrow UsageGrade.one .base .base))
    {leftArgument rightArgument : GradedLambda}
    (argumentsJoinable : Joinable GradedLambda.Reduces leftArgument rightArgument) :
    Joinable GradedLambda.Reduces
      (.app functionTerm leftArgument) (.app functionTerm rightArgument) :=
  typed.parametricGradedClosed joinabilityRespectsExpansion
    leftArgument rightArgument argumentsJoinable

end FX1Poly.Modal
