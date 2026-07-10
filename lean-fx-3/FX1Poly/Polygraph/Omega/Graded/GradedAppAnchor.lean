import FX1Poly.Polygraph.Omega.Graded.GradedCell
import FX1Poly.Dimensions.Graded.GradedTypingGeneric
import FX1Poly.Dimensions.Graded.GradedCompositionGeneric

/-! # Polygraph/Omega/Graded/GradedAppAnchor — the App rule IS the sequential graded composite
(OMEGA-5 r1, B2) — THE HEADLINE

The task's central identification: the §6.2 kernel App rule's grade accounting `p1 + r · p2` is not
merely ANALOGOUS to enriched (graded) composition — it IS the sequential graded composite
`gradeCompose r p q` (`GradedCell.lean`).  This file states that as the theorem it is, on the REAL
graded typing judgment `HasGradeOver` (`GradedTypingGeneric.lean`), machine-checked by `rfl`/defeq — not
a paper cite.

The App constructor of `HasGradeOver` concludes at grade
`GradeVectorOver.add functionGrades (GradeVectorOver.scale binderGrade argumentGrades)`
(`GradedTypingGeneric.lean`, the `app` rule).  `gradeCompose binderGrade functionGrades argumentGrades`
is DEFINITIONALLY that expression.  Hence:

  * **`appGrade_eq_gradeCompose`** — the forward anchor: for any function derivation at
    `dom -(r)-> cod` and argument derivation at `dom`, the application is typed at exactly
    `gradeCompose r functionGrades argumentGrades`.  Proof: the `HasGradeOver.app` constructor itself
    (its conclusion grade is defeq the `gradeCompose` expression).
  * **`appGrade_invert_gradeCompose`** — the inverse anchor: ANY application derivation exhibits its
    grade as `gradeCompose r functionGrades argumentGrades` for the witnessed pieces (from `invertApp`;
    the recorded equation is defeq the `gradeCompose` form).

Both directions pin the identity: the App rule's grade slot and the sequential graded composite are the
SAME term, up to unfolding `gradeCompose`.

## The worked demos — the identification reused on REAL typed terms (no rebuild)

The shipped composition witnesses (`GradedCompositionGeneric.lean`) are re-expressed through the anchor,
each by supplying the SAME proof term under a `gradeCompose`-shaped type ascription (defeq):

  * **`appliedIdentity_typedViaGradeCompose`** — `(λx. x) z` typed at `gradeCompose R.one [z↦0] [z↦1]`,
    in ANY dimension, reusing `appliedIdentityOver_typed`.
  * **`usageOmegaScalingRedex_typedViaGradeCompose`** — THE DECISIVE `r = ω` case: the redex
    `(λx. (g x) x) z` typed at `gradeCompose ω [z↦0, g↦1] [z↦1, g↦0]`, which computes to `[z↦ω, g↦1]`,
    reusing `usageOmegaScalingRedex_typed`.  This is the non-trivial-scaling witness: the identity would
    FAIL if the App rule used `+`-only or scale-by-1 rather than `p + r·q`.

## The k-uniformity caveat (honest)

The App / sequential composite is the OBJECT composite (`*_0`, composing along the lowest cells); the
polygraph `vcomp` composes `(dim+1)`-cells along their `dim`-boundary.  What this file identifies is the
grade ARITHMETIC (`add ∘ scale`), which is dimension/k-uniform because `GradeVectorOver.add`/`scale`
never mention `k`.  The specific `k = 0` label is polygraph bookkeeping pinned by the demos, not a
load-bearing theorem this round; the general cell-level "App = graded 2-composite WITH boundaries" is
the deferred remainder (see the r1 ledger).

## Zero-axiom verification

`appGrade_eq_gradeCompose` is the App constructor (no axiom); `appGrade_invert_gradeCompose` destructures
`HasGradeOver.invertApp` (itself axiom-free) and re-packs the witnesses; the demos are the shipped
axiom-free typed terms under a defeq type ascription.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega.Graded

open FX1Poly.Modal

/-! ## The anchor — App = sequential graded composite -/

/-- **THE APP ANCHOR (forward).**  The kernel App rule concludes at EXACTLY the sequential graded
composite `gradeCompose binderGrade functionGrades argumentGrades`: given `function : dom -(r)-> cod`
at grade `functionGrades` and `argument : dom` at grade `argumentGrades`, the application `function
argument : cod` is typed at `gradeCompose r functionGrades argumentGrades`.  The proof IS the
`HasGradeOver.app` constructor — its conclusion grade `add functionGrades (scale binderGrade
argumentGrades)` is definitionally `gradeCompose …`.  The §6.2 typing rule IS enriched composition. -/
theorem appGrade_eq_gradeCompose {R : OrderedGradeSemiring} (typeContext : List (GTypeOver R))
    (binderGrade : R.Carrier) (domain codomain : GTypeOver R)
    (functionGrades argumentGrades : GradeVectorOver R) (function argument : GradedLambda)
    (functionTyped : HasGradeOver R typeContext functionGrades function
      (.arrow binderGrade domain codomain))
    (argumentTyped : HasGradeOver R typeContext argumentGrades argument domain) :
    HasGradeOver R typeContext (gradeCompose binderGrade functionGrades argumentGrades)
      (.app function argument) codomain :=
  HasGradeOver.app (R := R) typeContext binderGrade domain codomain functionGrades argumentGrades
    function argument functionTyped argumentTyped

/-- **THE APP ANCHOR (inverse).**  ANY application derivation exhibits its grade as the sequential
graded composite: from `function argument : resultType` at grade `grades`, there are a binder grade `r`,
a domain, and function/argument grades with `function : dom -(r)-> resultType`, `argument : dom`, and
`grades = gradeCompose r functionGrades argumentGrades`.  From `HasGradeOver.invertApp`; the recorded
equation `grades = add … (scale …)` is defeq the `gradeCompose` form. -/
theorem appGrade_invert_gradeCompose {R : OrderedGradeSemiring} {typeContext : List (GTypeOver R)}
    {grades : GradeVectorOver R} {function argument : GradedLambda} {resultType : GTypeOver R}
    (typed : HasGradeOver R typeContext grades (.app function argument) resultType) :
    ∃ (binderGrade : R.Carrier) (domain : GTypeOver R)
      (functionGrades argumentGrades : GradeVectorOver R),
      HasGradeOver R typeContext functionGrades function (.arrow binderGrade domain resultType) ∧
        HasGradeOver R typeContext argumentGrades argument domain ∧
          grades = gradeCompose binderGrade functionGrades argumentGrades := by
  obtain ⟨binderGrade, domain, functionGrades, argumentGrades, functionTyped, argumentTyped, gradesEq⟩ :=
    typed.invertApp
  exact ⟨binderGrade, domain, functionGrades, argumentGrades, functionTyped, argumentTyped, gradesEq⟩

/-! ## The worked demos — real typed terms re-expressed through the anchor -/

/-- **`(λx. x) z` typed through the anchor, in ANY dimension.**  The applied linear identity is typed
at `gradeCompose R.one [z↦0] [z↦1]` (the App-rule grade of the once-used argument), by reusing the
shipped `appliedIdentityOver_typed` under a `gradeCompose`-shaped ascription (defeq). -/
theorem appliedIdentity_typedViaGradeCompose (R : OrderedGradeSemiring) :
    HasGradeOver R [GTypeOver.base]
      (gradeCompose R.one (GradeVectorOver.cons R.zero GradeVectorOver.nil)
        (GradeVectorOver.single R 1 0 R.one))
      (.app (.lam (.var 0)) (.var 0)) GTypeOver.base :=
  appliedIdentityOver_typed R

/-- **THE DECISIVE `r = ω` demo through the anchor.**  The ω-scaling redex `(λx. (g x) x) z` is typed at
`gradeCompose ω [z↦0, g↦1] [z↦1, g↦0]`, which computes to `[z↦ω, g↦1]` — the once-occurring argument `z`
scaled to `ω` by the ω-using binder.  Reuses the shipped `usageOmegaScalingRedex_typed` under a
`gradeCompose`-shaped ascription (defeq): the real typed term's grade IS a sequential graded composite,
and the non-trivial scaling is faithful. -/
theorem usageOmegaScalingRedex_typedViaGradeCompose :
    HasGradeOver fxUsageSemiring [GTypeOver.base, omegaScalingBinaryTypeUsage]
      (gradeCompose UsageGrade.omega
        (GradeVectorOver.cons UsageGrade.zero (GradeVectorOver.cons UsageGrade.one GradeVectorOver.nil))
        (GradeVectorOver.single fxUsageSemiring 2 0 UsageGrade.one))
      (.app (.lam (.app (.app (.var 2) (.var 0)) (.var 0))) (.var 0)) GTypeOver.base :=
  usageOmegaScalingRedex_typed

end FX1Poly.Polygraph.Omega.Graded
