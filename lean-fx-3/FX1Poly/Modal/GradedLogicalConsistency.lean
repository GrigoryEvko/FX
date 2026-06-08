import FX1Poly.Modal.GradedEvaluation

/-! # FX1Poly/Modal/GradedLogicalConsistency — the graded calculus is a CONSISTENT logic

The type-safety story for the generic graded engine `HasGradeOver R` is complete: PRESERVATION
(`hasGradeOver_reducesPreservation`), PROGRESS (`closedWellTypedProgress`), TERMINATION
(`HasGradeOver.stronglyNormalizing`), and the EVALUATION capstone (`closedReducesToLam` — every closed
well-typed term reduces to a `.lam`).  This file draws the LOGICAL conclusion via Curry-Howard: read a
`GTypeOver R` as a proposition and `HasGradeOver R [] grades term T` as a closed proof of `T`; then the
calculus is CONSISTENT — its atomic proposition `GTypeOver.base` has no closed proof.

`GradedProgress.closedBaseTypeAlwaysSteps` already showed a closed base-typed term always *steps* (base
has no closed *values*).  That is the one-step fact; it does not by itself rule out a hypothetical
base-typed term that reduces forever.  Strong normalization closes that gap: the term cannot reduce
forever, so "always steps" becomes a contradiction.  The clean assembly reuses the shipped evaluation
theorem directly.

  * **`closedBaseTypeUninhabited`** — ★ CONSISTENCY: no closed term has type `GTypeOver.base`, over ANY
    graded dimension `R`.  A closed base-typed term reduces to a `.lam` (`closedReducesToLam` = SN +
    progress + canonical forms); that `.lam` is still base-typed along the chain (full-β SR
    `hasGradeOver_reducesStarPreservation`); but a `.lam` is only ever arrow-typed (`invertLam`), so
    `base = arrow …` — a constructor clash.  This is the graded analogue of the grown engine's SN-050
    consistency (`HasTypeDescPi .empty t EmptyType → False`): there, a dedicated `EmptyType`; here, the
    uninterpreted atom of the pure simply-typed fragment.  It holds for every one of the 21 dimensions
    at once, since `R` is arbitrary.

  * **`closedTermIsArrowTyped`** — every CLOSED graded-typed term has ARROW type — it is a function.
    The `base` case is refuted by `closedBaseTypeUninhabited`; the arrow is the only other `GTypeOver`
    former.  The positive reading of consistency: closed inhabitants live only at arrow types.

  * **`usageBaseTypeUninhabited`** — the concrete usage-dimension (linear `{0,1,ω}`) instance: there is
    no closed linear term of base type.  A §27-flavoured corpus witness that the generic consistency
    fires at a real semiring.

## Zero-axiom verification

`closedReducesToLam` + `hasGradeOver_reducesStarPreservation` + `HasGradeOver.invertLam` (all shipped
zero-axiom) and a `cases` on the `base = arrow …` constructor clash (propext-clean discrimination on a
plain inductive); the corollary `cases` on `GTypeOver`; the smoke `rintro` + the headline.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega` (every declaration probed
with `#print axioms` before landing).  Per-declaration audit-gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- ★ **Consistency.**  No closed term has type `GTypeOver.base`, over ANY graded dimension `R`.  A
closed base-typed term evaluates to a `.lam` (`closedReducesToLam`), that `.lam` stays base-typed along
the reduction (full-β SR over `↝*`), but a `.lam` inhabits only an arrow (`invertLam`) — so
`base = arrow …`, a constructor clash.  The Curry-Howard consistency of the graded calculus: its atomic
proposition has no closed proof.  Graded analogue of the grown SN-050 `EmptyType` consistency. -/
theorem closedBaseTypeUninhabited {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) {grades : GradeVectorOver R}
    {term : GradedLambda} (typed : HasGradeOver R [] grades term GTypeOver.base) : False := by
  obtain ⟨body, reducesStar⟩ := closedReducesToLam lawful typed
  have lamTyped : HasGradeOver R [] grades (.lam body) GTypeOver.base :=
    hasGradeOver_reducesStarPreservation lawful reducesStar typed
  obtain ⟨binderGrade, domain, codomain, baseEq, _⟩ := HasGradeOver.invertLam lamTyped
  cases baseEq

/-- Every CLOSED graded-typed term has ARROW type — it is a function.  The `base` case is impossible by
`closedBaseTypeUninhabited`; the arrow is the only other `GTypeOver` former.  The positive reading of
consistency: closed inhabitants live only at arrow types. -/
theorem closedTermIsArrowTyped {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) {grades : GradeVectorOver R}
    {term : GradedLambda} {resultType : GTypeOver R}
    (typed : HasGradeOver R [] grades term resultType) :
    ∃ binderGrade domain codomain, resultType = GTypeOver.arrow binderGrade domain codomain := by
  cases resultType with
  | base => exact (closedBaseTypeUninhabited lawful typed).elim
  | arrow binderGrade domain codomain => exact ⟨binderGrade, domain, codomain, rfl⟩

/-- Concrete usage-dimension instance: there is no closed LINEAR term of base type.  The generic
consistency `closedBaseTypeUninhabited` fired at the verified usage semiring `fxUsageSemiring`
(`{0,1,ω}`) — a §27-flavoured corpus witness that the metatheorem is non-vacuous at a real dimension. -/
theorem usageBaseTypeUninhabited :
    ¬ ∃ (grades : GradeVectorOver fxUsageSemiring) (term : GradedLambda),
        HasGradeOver fxUsageSemiring [] grades term GTypeOver.base := by
  rintro ⟨grades, term, typed⟩
  exact closedBaseTypeUninhabited fxUsageSemiring_isLawful typed

end FX1Poly.Modal
