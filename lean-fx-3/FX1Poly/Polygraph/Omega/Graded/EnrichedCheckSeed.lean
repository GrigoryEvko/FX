import FX1Poly.Polygraph.Omega.Graded.GradedCell
import FX1Poly.Dimensions.Graded.GradeVectorGeneric

/-! # Polygraph/Omega/Graded/EnrichedCheckSeed — the enriched-functor seed at the grade-vector level
(OMEGA-5 r1, B3)

The task's third identification: the 21-dimension grade CHECKER is one enriched ω-functor
`check : CellExpr computad n → AmalgamatedProduct(dimensionWalkers)`, grade-preserving and functorial
(`check (a *_k b) = check a ⊗_k check b`).  The full walker-product codomain needs a type that does not
yet exist (the amalgamated-product / dispatch arrow, AMALG-2 — deferred, see the r1 ledger).  So r1
seeds the functor on the ONE dimension whose algebra is already complete: the USAGE grade `{0, 1, ω}`,
end-to-end at the GRADE-VECTOR level.

## What ships (the usage factor, end-to-end)

  * **`enrichedCheckOnGrades`** — the grade-checker's actual decision procedure on a factor: `grades` is
    admissible against `budget` iff pointwise below.  This is the shipped `isPointwiseBelowBool` (the
    computable pointwise-`≤`), read AS the functor's evaluation on a single dimension.
  * **`enrichedCheckOnGrades_correct`** — soundness + completeness: the Boolean decision is faithful to
    the semantic pointwise order `IsPointwiseBelow`.  The check is a DECISION, not a heuristic.
  * **`checkUsageFactor`** — the usage-dimension instance: `enrichedCheckOnGrades` at `fxUsageSemiring`.
    The functor's evaluation on the usage factor.

## The functoriality-on-grades legs are FREE (from the shipped semimodule laws)

  * **`gradeCompose_mono` / `gradeComposePar_mono`** — the enriched composites are MONOTONE in their
    operands (from `add_mono` + `scale_mono`): the check preserves the admissibility ORDER, so the
    functor sends composable admissible cells to admissible composites.  This is functoriality read on
    the order: `check` respects `⊗`.
  * **`gradeCompose_scaleHom`** — the scalar action is a HOMOMORPHISM over the sequential composite:
    `s · (gradeCompose r p q) = gradeCompose (s·r) (s·p) q` (from `scale_add` + `scale_scale`).  Scaling
    a composite factors through scaling the pieces — the enriched-composition arithmetic is stable under
    the semimodule action, the functor's compatibility law on grades.

No new law is proven — every leg discharges into `GradeVectorGeneric`'s shipped semimodule / order
lemmas, exactly the "recognition, not construction" character of r1.

## Deferred (honestly named, r1 ledger)

The CELL side — mapping `CellExpr computad n` into actual walker word problems, and the walker-product
codomain `⊗_k` — needs the amalgamated-product type (AMALG-2, arrow uninhabited).  The
dimension-generic MODE-ADMIT promotion ("a grade vector is admissible iff each dimension's presentation
is admitted; decidability inherited component-wise") states its shape here but wires nothing into the
Amalgam lane's `ModeAdmit.lean` this round.

## Zero-axiom verification

`enrichedCheckOnGrades` is the shipped `isPointwiseBelowBool`; `enrichedCheckOnGrades_correct` reuses
`isPointwiseBelowBool_correct`; the functoriality legs are `add_mono` / `scale_mono` / `scale_add` /
`scale_scale` applications; the non-vacuity witnesses compute (`rfl`).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration `#assert_no_axioms` gated in the
audit twin. -/

namespace FX1Poly.Polygraph.Omega.Graded

open FX1Poly.Modal

/-! ## The usage-factor evaluation of the enriched functor -/

/-- **The enriched functor's evaluation on one graded dimension.**  A grade vector `grades` is
admissible against `budget` iff it is pointwise below — the grade-checker's actual decision procedure
(the shipped computable pointwise-`≤`), read as `check` restricted to a single factor. -/
def enrichedCheckOnGrades {R : OrderedGradeSemiring} (grades budget : GradeVectorOver R) : Bool :=
  GradeVectorOver.isPointwiseBelowBool grades budget

/-- **Soundness + completeness of the factor check**: the Boolean decision equals the semantic
pointwise order.  The enriched functor's per-dimension evaluation is a faithful DECISION.  Reuses the
shipped `isPointwiseBelowBool_correct`. -/
theorem enrichedCheckOnGrades_correct {R : OrderedGradeSemiring} (grades budget : GradeVectorOver R) :
    enrichedCheckOnGrades grades budget = true ↔
      GradeVectorOver.IsPointwiseBelow grades budget :=
  GradeVectorOver.isPointwiseBelowBool_correct grades budget

/-- **The usage-dimension instance of the functor** — `enrichedCheckOnGrades` at the usage semiring
`{0, 1, ω}`.  The concrete factor the graded round evaluates. -/
def checkUsageFactor (grades budget : GradeVectorOver fxUsageSemiring) : Bool :=
  enrichedCheckOnGrades grades budget

/-! ## Functoriality on grades — the free legs -/

/-- **The sequential composite is monotone in both operands** (from `add_mono` + `scale_mono`): if the
function and argument grades are each within their bounds, the sequential graded composite is within the
composite bound.  The functor respects `⊗` on the admissibility order. -/
theorem gradeCompose_mono {R : OrderedGradeSemiring} (lawful : IsLawfulOrderedGradeSemiring R)
    (binderGrade : R.Carrier)
    {functionGrades functionBound argumentGrades argumentBound : GradeVectorOver R}
    (functionBelow : GradeVectorOver.IsPointwiseBelow functionGrades functionBound)
    (argumentBelow : GradeVectorOver.IsPointwiseBelow argumentGrades argumentBound) :
    GradeVectorOver.IsPointwiseBelow (gradeCompose binderGrade functionGrades argumentGrades)
      (gradeCompose binderGrade functionBound argumentBound) :=
  GradeVectorOver.IsPointwiseBelow.add_mono lawful functionBelow
    (GradeVectorOver.IsPointwiseBelow.scale_mono lawful binderGrade argumentBelow)

/-- **The parallel composite is monotone in both operands** (from `add_mono`): the context-split
composite of within-budget grades is within budget. -/
theorem gradeComposePar_mono {R : OrderedGradeSemiring} (lawful : IsLawfulOrderedGradeSemiring R)
    {leftGrades leftBound rightGrades rightBound : GradeVectorOver R}
    (leftBelow : GradeVectorOver.IsPointwiseBelow leftGrades leftBound)
    (rightBelow : GradeVectorOver.IsPointwiseBelow rightGrades rightBound) :
    GradeVectorOver.IsPointwiseBelow (gradeComposePar leftGrades rightGrades)
      (gradeComposePar leftBound rightBound) :=
  GradeVectorOver.IsPointwiseBelow.add_mono lawful leftBelow rightBelow

/-- **The scalar action is a homomorphism over the sequential composite** (from `scale_add` +
`scale_scale`): scaling a graded composite by `outerScale` factors through scaling the function grade by
`outerScale` and the binder grade to `outerScale · binderGrade`.  The functor's compatibility of the
enriched composition with the semimodule action. -/
theorem gradeCompose_scaleHom {R : OrderedGradeSemiring} (lawful : IsLawfulOrderedGradeSemiring R)
    (outerScale binderGrade : R.Carrier) (functionGrades argumentGrades : GradeVectorOver R) :
    GradeVectorOver.scale outerScale (gradeCompose binderGrade functionGrades argumentGrades) =
      gradeCompose (R.mul outerScale binderGrade)
        (GradeVectorOver.scale outerScale functionGrades) argumentGrades := by
  dsimp only [gradeCompose]
  rw [GradeVectorOver.scale_add lawful, GradeVectorOver.scale_scale lawful]

/-! ## Non-vacuity — the usage factor decides, on grades AND on composites -/

/-- The usage factor ADMITS a within-budget grade: `[1] ≤ [ω]` is `true`. -/
theorem enrichedCheck_usageAdmits :
    enrichedCheckOnGrades (R := fxUsageSemiring)
        (GradeVectorOver.cons UsageGrade.one GradeVectorOver.nil)
        (GradeVectorOver.cons UsageGrade.omega GradeVectorOver.nil) = true :=
  rfl

/-- The usage factor REJECTS an over-budget grade: `[ω] ≤ [1]` is `false`. -/
theorem enrichedCheck_usageRejectsOverBudget :
    enrichedCheckOnGrades (R := fxUsageSemiring)
        (GradeVectorOver.cons UsageGrade.omega GradeVectorOver.nil)
        (GradeVectorOver.cons UsageGrade.one GradeVectorOver.nil) = false :=
  rfl

/-- The functor evaluates on a SEQUENTIAL COMPOSITE: `gradeCompose 1 [0] [1] = [1]` is admissible
against budget `[1]`.  The `check`-on-a-composite non-vacuity. -/
theorem checkUsageFactor_onSequentialComposite :
    checkUsageFactor
        (gradeCompose UsageGrade.one (GradeVectorOver.cons UsageGrade.zero GradeVectorOver.nil)
          (GradeVectorOver.cons UsageGrade.one GradeVectorOver.nil))
        (GradeVectorOver.cons UsageGrade.one GradeVectorOver.nil) = true :=
  rfl

end FX1Poly.Polygraph.Omega.Graded
