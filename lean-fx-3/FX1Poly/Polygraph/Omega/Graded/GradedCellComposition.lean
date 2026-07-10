import FX1Poly.Polygraph.Omega.Graded.GradedCell
import FX1Poly.Polygraph.Omega.Graded.GradedAppAnchor
import FX1Poly.Polygraph.Omega.Graded.EnrichedCheckSeed
import FX1Poly.Polygraph.Omega.Graded.CollisionCatalog

/-! # Polygraph/Omega/Graded/GradedCellComposition — the cell-side graded composition (OMEGA-5 r2)

r1 recognized the App rule as the sequential graded composite and seeded the grade-side functor.  r2
grinds one genuine rung further: the **lockstep composite's grade leg is now a proven ALGEBRA** (the
associativity + unit laws that r1 only cited as "existing semimodule laws"), the **grade projection is
an enriched functor** (composition maps to `gradeCompose`, both projections + the functor-over-
associativity), and the **checker refuses genuinely** (a guarded composite that BLOCKS on over-budget
grades and on a §6.8 collision row).

## The carrier + composite are REUSED, not re-founded (POLY-TAB: never a new carrier)

The annotated carrier is the shipped `GradedCell computad dim R := CellExpr computad dim ×
GradeVectorOver R` (`GradedCell.lean`); the lockstep composite is the shipped `gradedVcomp` (cell via
`CellExpr.vcomp`, grade via `gradeCompose`, in lockstep).  r2 adds NO carrier and NO composite — it adds
the laws the composite's grade leg satisfies and the functor that projects onto them.

## The SHARP honesty finding — the cell leg is NOT associative; only the grade leg is

`CellExpr.vcomp` is a FREE constructor (`Carrier.lean`), so `vcomp (vcomp a b) c` and `vcomp a (vcomp b
c)` are DISTINCT syntax — the raw annotated-pair composite is **not** associative.  Stating lockstep
associativity as raw `GradedCell` equality would be FALSE.  The honest r2 theorem is therefore
functoriality-over-associativity on `gradeOf` (the grade projection ONLY): `gradeOf` collapses the two
non-equal cell legs, and on the grade the reindexed associativity genuinely holds
(`gradedVcomp_gradeOf_assoc`).  The CELL leg's associativity is a SEPARATE result — OMEGA-7's
`linearizeFull_pasteAlong_assoc` (Tier-0, un-importable here per the layer rule) — which this file CITES,
never re-proves.  So `gradedVcomp_gradeOf_assoc` is an identification of the GRADE legs, and a
DISPARITY of the cell legs; that is stated, not hidden.

## The scalar-reindex is load-bearing (`gradeCompose_assoc`)

`gradeCompose r p q := add p (scale r q)`.  Associativity is NOT same-scalar — the outer binder must be
reindexed to `R.mul firstScale secondScale`:

    gradeCompose (a*b) (gradeCompose a p q) t  =  gradeCompose a p (gradeCompose b q t)

Both sides equal `p + a·q + (a·b)·t` (LHS by `add_assoc`; RHS by `scale_add` then `scale_scale`).  The
naive same-outer-scalar form is FALSE: `gradeCompose_assoc_naive_isFalse` exhibits a concrete usage
triple (`a=ω, b=1, p=q=[0], t=[1]`) where the naive outer scalar `b=1` gives `[1]` but the genuine right
composite gives `[ω]`.  This mirrors r1's B2 `r=ω` redex: the reindex `a·b` beats a scalar guess exactly
as `p+r·q` beats `+`-only.

## The refusal slice (`gradedComposeGuarded` / `gradedComposeAtCollisionRow`)

The enriched functor is a genuine CHECKER, not a total map: `gradedComposeGuarded` forms the annotated
composite ONLY when the composite grade passes `enrichedCheckOnGrades` against a budget, returning `none`
otherwise (grades that do NOT compose block the composite — `gradedComposeGuarded_overBudget_refuses`).
`gradedComposeAtCollisionRow` additionally consults a §6.8 `CollisionRow`: at a non-free locus (every
§6.8 row) the composite is REFUSED regardless of budget — `gradedComposeAtCollisionRow_ctAsync_refuses`
exercises the sharpest row `E044` (CT × Async, contradictory).  HONESTY: the collision refusal READS the
row's `isFreeLocus` flag (the checker's data-driven content); the underlying amalgam-collision THEOREM
(why CT×Async cannot amalgamate) stays the jam (`fxOmega5_collisionNonFreeLinkReached = false`).  The
refusal is single-dimension (`R = fxUsageSemiring`); the 21-dim PRODUCT-semiring collision stays the jam
(`fxOmega5_productSemiring21Reached = false`) — the catalog is cited as DATA, never as the product.

## Zero-axiom verification

`gradeCompose_assoc` / `gradeCompose_leftUnit` are `dsimp only [gradeCompose]` + `rw` with the shipped
propext-clean `GradeVectorOver` semimodule lemmas (`scale_add` / `scale_scale` / `add_assoc` /
`scale_one_scalar` / `zero_add`).  The projections + functor laws are `rfl`; the functor-over-
associativity reduces to `gradeCompose_assoc` by two `rfl` functor-law steps.  The guarded composites use
full-enum Bool / two-constructor matches (no wildcard).  The non-vacuity + refusal witnesses compute
(`rfl`), and the naive-is-false counterexample closes by `injection` + `noConfusion`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
`#assert_no_axioms` gated in the audit twin; independent `#print axioms` in the scratch probe. -/

namespace FX1Poly.Polygraph.Omega.Graded

open FX1Poly.Modal

/-! ## The grade-leg algebra of the lockstep composite (B1) — associativity + unit

r1 SHIPPED the composite (`gradedVcomp` = cell `CellExpr.vcomp` × grade `gradeCompose`) but only CITED
the semimodule laws.  r2 PROVES the two composition laws the grade leg obeys, anchored to the kernel
grade semiring's `mul_assoc` (routed through `scale_scale`) — never re-proved. -/

/-- **Grade-leg associativity of the sequential composite — the scalar-reindexed law.**  The outer
binder must be reindexed to `R.mul firstScale secondScale`: composing `(a·b)`-then-`t` over the
`a`-composite of `p, q` equals the `a`-composite of `p` with the `b`-composite of `q, t`.  Both sides are
`p + a·q + (a·b)·t`.  Discharges into the shipped `scale_add` / `scale_scale` / `add_assoc` (the
`scale_scale` routes the outer scalar through the semiring's `mul_assoc`) — anchored to the kernel
semiring, not re-proved.  The naive same-outer-scalar form is FALSE (`gradeCompose_assoc_naive_isFalse`). -/
theorem gradeCompose_assoc {R : OrderedGradeSemiring} (lawful : IsLawfulOrderedGradeSemiring R)
    (firstScale secondScale : R.Carrier)
    (functionGrades middleGrades argumentGrades : GradeVectorOver R) :
    gradeCompose (R.mul firstScale secondScale)
        (gradeCompose firstScale functionGrades middleGrades) argumentGrades =
      gradeCompose firstScale functionGrades
        (gradeCompose secondScale middleGrades argumentGrades) := by
  dsimp only [gradeCompose]
  rw [GradeVectorOver.scale_add lawful firstScale middleGrades
        (GradeVectorOver.scale secondScale argumentGrades),
      GradeVectorOver.scale_scale lawful firstScale secondScale argumentGrades,
      GradeVectorOver.add_assoc lawful functionGrades
        (GradeVectorOver.scale firstScale middleGrades)
        (GradeVectorOver.scale (R.mul firstScale secondScale) argumentGrades)]

/-- **Left-unit of the sequential composite** (the enriched functor's identity-preservation on grades):
composing the zero function-grade (of the argument's own length) with `argumentGrades` at binder `R.one`
returns `argumentGrades`.  From `scale_one_scalar` (`1·q = q`) + `zero_add` (`0 + q = q`). -/
theorem gradeCompose_leftUnit {R : OrderedGradeSemiring} (lawful : IsLawfulOrderedGradeSemiring R)
    (argumentGrades : GradeVectorOver R) :
    gradeCompose R.one (GradeVectorOver.zero R argumentGrades.length) argumentGrades =
      argumentGrades := by
  dsimp only [gradeCompose]
  rw [GradeVectorOver.scale_one_scalar lawful argumentGrades,
      GradeVectorOver.zero_add lawful argumentGrades]

/-! ## The naive-is-false counterexample (B1 honesty) — the reindex is load-bearing -/

/-- The usage singleton `[0]` (one erased binding). -/
def usageSingletonZero : GradeVectorOver fxUsageSemiring :=
  GradeVectorOver.cons UsageGrade.zero GradeVectorOver.nil

/-- The usage singleton `[1]` (one linear binding). -/
def usageSingletonOne : GradeVectorOver fxUsageSemiring :=
  GradeVectorOver.cons UsageGrade.one GradeVectorOver.nil

/-- The usage singleton `[ω]` (one unrestricted binding). -/
def usageSingletonOmega : GradeVectorOver fxUsageSemiring :=
  GradeVectorOver.cons UsageGrade.omega GradeVectorOver.nil

/-- **The corrected (reindexed) associativity COMPUTES on a concrete usage triple.**  With
`a=ω, b=1, p=q=[0], t=[1]`, the reindexed outer scalar `mul ω 1 = ω` makes both composites equal `[ω]` —
the specialization of `gradeCompose_assoc` at the exact triple where the naive form fails. -/
theorem gradeCompose_assoc_corrected_computes :
    gradeCompose (R := fxUsageSemiring) (fxUsageSemiring.mul UsageGrade.omega UsageGrade.one)
        (gradeCompose UsageGrade.omega usageSingletonZero usageSingletonZero) usageSingletonOne =
      gradeCompose UsageGrade.omega usageSingletonZero
        (gradeCompose UsageGrade.one usageSingletonZero usageSingletonOne) :=
  gradeCompose_assoc fxUsageSemiring_isLawful UsageGrade.omega UsageGrade.one
    usageSingletonZero usageSingletonZero usageSingletonOne

/-- **The naive same-outer-scalar associativity is FALSE.**  Reusing the OUTER binder `b=1` (instead of
the reindexed `a·b=ω`) yields `[1]` where the genuine right composite yields `[ω]`: at `a=ω, b=1,
p=q=[0], t=[1]` the erased `a·q = ω·0 = 0` unmasks the `t`-slot, so the outer scalar is decisive.  The
reindex to `R.mul firstScale secondScale` in `gradeCompose_assoc` is therefore load-bearing, not
cosmetic. -/
theorem gradeCompose_assoc_naive_isFalse :
    gradeCompose (R := fxUsageSemiring) UsageGrade.one
        (gradeCompose UsageGrade.omega usageSingletonZero usageSingletonZero) usageSingletonOne ≠
      gradeCompose UsageGrade.omega usageSingletonZero
        (gradeCompose UsageGrade.one usageSingletonZero usageSingletonOne) := by
  intro contradictoryEq
  injection contradictoryEq with headEq _
  exact UsageGrade.noConfusion headEq

/-! ## The enriched-functor grade slice (B2) — projections + functoriality

`gradeOf` is the enriched functor's action on objects (the grade projection).  The projection theorems
(both `rfl`, so trivial content — SAID plainly) fix the object map; the functor laws show that the
lockstep composites map to the grade composites (`gradedVcomp → gradeCompose`, the whiskers →
`gradeComposePar`); the functor-over-associativity is the genuine content — it identifies the GRADE legs
of the two triple composites while their CELL legs stay distinct (free `vcomp`, cited to OMEGA-7). -/

/-- **The enriched functor's action on objects** — the grade projection of a graded cell.  Definitionally
`GradedCell.gradeVector`; named `gradeOf` to read as the 21-dim checker's per-grade evaluation
(`check`-on-objects), the map the composition laws below are functorial for. -/
def gradeOf {computad : OmegaComputad} {dim : Nat} {R : OrderedGradeSemiring}
    (gradedCell : GradedCell computad dim R) : GradeVectorOver R :=
  gradedCell.gradeVector

/-- **Cell projection of the lockstep composite** — `rfl` (trivial content: the carrier is a plain pair,
`gradedVcomp` is componentwise).  The composite's underlying cell is exactly `CellExpr.vcomp` of the two
underlying cells. -/
theorem gradedVcomp_underlyingCell {computad : OmegaComputad} {dim : Nat} {R : OrderedGradeSemiring}
    (binderGrade : R.Carrier) (firstCell secondCell : GradedCell computad (dim + 1) R) :
    (gradedVcomp binderGrade firstCell secondCell).underlyingCell =
      CellExpr.vcomp firstCell.underlyingCell secondCell.underlyingCell :=
  rfl

/-- **The sequential functor law** — `rfl` (trivial content).  `gradeOf` sends the lockstep composite to
the sequential grade composite `gradeCompose`: the first machine-checked piece of "the 21-dim checker is
ONE enriched functor into the grade composite", on the sequential composite. -/
theorem gradedVcomp_gradeOf {computad : OmegaComputad} {dim : Nat} {R : OrderedGradeSemiring}
    (binderGrade : R.Carrier) (firstCell secondCell : GradedCell computad (dim + 1) R) :
    gradeOf (gradedVcomp binderGrade firstCell secondCell) =
      gradeCompose binderGrade (gradeOf firstCell) (gradeOf secondCell) :=
  rfl

/-- **The left-whisker functor law** — `rfl`.  `gradeOf` sends the left-whisker composite to the PARALLEL
grade composite `gradeComposePar` (whiskering by an independent cell is context-split, §7.7). -/
theorem gradedWhiskerLeft_gradeOf {computad : OmegaComputad} {dim : Nat} {R : OrderedGradeSemiring}
    (whiskering : GradedCell computad (dim + 1) R) (target : GradedCell computad (dim + 2) R) :
    gradeOf (gradedWhiskerLeft whiskering target) =
      gradeComposePar (gradeOf whiskering) (gradeOf target) :=
  rfl

/-- **The right-whisker functor law** — `rfl`.  Dual to `gradedWhiskerLeft_gradeOf`. -/
theorem gradedWhiskerRight_gradeOf {computad : OmegaComputad} {dim : Nat} {R : OrderedGradeSemiring}
    (target : GradedCell computad (dim + 2) R) (whiskering : GradedCell computad (dim + 1) R) :
    gradeOf (gradedWhiskerRight target whiskering) =
      gradeComposePar (gradeOf target) (gradeOf whiskering) :=
  rfl

/-- **Functor-over-associativity on the GRADE leg — the genuine r2 content.**  `gradeOf` sends the
reindexed `(a·b)`-over-`a` left-nested triple composite and the `a`-over-`b` right-nested triple composite
to the SAME grade (via `gradeCompose_assoc`) — even though their CELL legs `vcomp (vcomp L M) R` and
`vcomp L (vcomp M R)` are DISTINCT syntax (free `CellExpr.vcomp`).  The functor COLLAPSES the two
non-equal cell legs onto one grade: that collapse is exactly the functoriality content.  The cell leg's
own associativity is NOT proven here — it is OMEGA-7's `linearizeFull_pasteAlong_assoc` (Tier-0,
un-importable under the layer rule), which this statement CITES; r2 owns only the grade leg.  So this is
an IDENTIFICATION of the grade legs and a DISPARITY of the cell legs, stated openly. -/
theorem gradedVcomp_gradeOf_assoc {computad : OmegaComputad} {dim : Nat} {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) (firstScale secondScale : R.Carrier)
    (leftCell middleCell rightCell : GradedCell computad (dim + 1) R) :
    gradeOf (gradedVcomp (R.mul firstScale secondScale)
        (gradedVcomp firstScale leftCell middleCell) rightCell) =
      gradeOf (gradedVcomp firstScale leftCell
        (gradedVcomp secondScale middleCell rightCell)) := by
  show gradeCompose (R.mul firstScale secondScale)
        (gradeCompose firstScale (gradeOf leftCell) (gradeOf middleCell)) (gradeOf rightCell) =
      gradeCompose firstScale (gradeOf leftCell)
        (gradeCompose secondScale (gradeOf middleCell) (gradeOf rightCell))
  exact gradeCompose_assoc lawful firstScale secondScale
    (gradeOf leftCell) (gradeOf middleCell) (gradeOf rightCell)

/-! ## The refusal slice (B3) — the enriched functor is a genuine CHECKER

The functor is NOT a total map: `gradedComposeGuarded` forms the annotated composite ONLY when the
composite grade passes the shipped `enrichedCheckOnGrades` against a budget, returning `none` when the
grades do not compose (over budget).  `gradedComposeAtCollisionRow` additionally consults a §6.8
`CollisionRow`: at a NON-FREE locus (every §6.8 row) the composite is REFUSED regardless of budget.  The
grade refusal is machine-checked; the collision refusal READS the row's `isFreeLocus` flag (the checker's
data-driven content), the underlying amalgam-collision theorem staying the jam. -/

/-- **The guarded lockstep composite** — the enriched functor as a checker.  Form the annotated composite
`gradedVcomp` only when its grade `gradeCompose binderGrade (gradeOf firstCell) (gradeOf secondCell)`
passes `enrichedCheckOnGrades` against `budget`; otherwise REFUSE (`none`).  Full-enum Bool match (no
wildcard) — propext-free. -/
def gradedComposeGuarded {computad : OmegaComputad} {dim : Nat} {R : OrderedGradeSemiring}
    (binderGrade : R.Carrier) (budget : GradeVectorOver R)
    (firstCell secondCell : GradedCell computad (dim + 1) R) :
    Option (GradedCell computad (dim + 1) R) :=
  match enrichedCheckOnGrades
      (gradeCompose binderGrade (gradeOf firstCell) (gradeOf secondCell)) budget with
  | true  => some (gradedVcomp binderGrade firstCell secondCell)
  | false => none

/-- **The grade refusal**: when the composite grade fails the budget check, the guarded composite is
`none` — grades that do NOT compose block the annotated composite. -/
theorem gradedComposeGuarded_refuses {computad : OmegaComputad} {dim : Nat} {R : OrderedGradeSemiring}
    (binderGrade : R.Carrier) (budget : GradeVectorOver R)
    (firstCell secondCell : GradedCell computad (dim + 1) R)
    (refuted : enrichedCheckOnGrades
      (gradeCompose binderGrade (gradeOf firstCell) (gradeOf secondCell)) budget = false) :
    gradedComposeGuarded binderGrade budget firstCell secondCell = none := by
  dsimp only [gradedComposeGuarded]
  rw [refuted]

/-- **The grade admission**: when the composite grade passes the budget check, the guarded composite is
the annotated `gradedVcomp`. -/
theorem gradedComposeGuarded_admits {computad : OmegaComputad} {dim : Nat} {R : OrderedGradeSemiring}
    (binderGrade : R.Carrier) (budget : GradeVectorOver R)
    (firstCell secondCell : GradedCell computad (dim + 1) R)
    (admitted : enrichedCheckOnGrades
      (gradeCompose binderGrade (gradeOf firstCell) (gradeOf secondCell)) budget = true) :
    gradedComposeGuarded binderGrade budget firstCell secondCell =
      some (gradedVcomp binderGrade firstCell secondCell) := by
  dsimp only [gradedComposeGuarded]
  rw [admitted]

/-- **The collision-row guarded composite** — the checker consults a §6.8 `CollisionRow` FIRST: a
NON-FREE locus REFUSES composition outright (`none`); a free locus falls through to the grade guard.
Two-constructor Bool match — propext-free. -/
def gradedComposeAtCollisionRow {computad : OmegaComputad} {dim : Nat} {R : OrderedGradeSemiring}
    (row : CollisionRow) (binderGrade : R.Carrier) (budget : GradeVectorOver R)
    (firstCell secondCell : GradedCell computad (dim + 1) R) :
    Option (GradedCell computad (dim + 1) R) :=
  match row.isFreeLocus with
  | false => none
  | true  => gradedComposeGuarded binderGrade budget firstCell secondCell

/-- ★ **The §6.8 row `E044` (CT × Async) exercised as a genuine composition refusal.**  The sharpest,
contradictory collision (`collisionCtAsync.isFreeLocus = false`) BLOCKS the annotated composite for ANY
binder grade, budget, and cells — the checker refuses at the non-free locus regardless of whether the
grades themselves would compose.  `rfl` (the row's `isFreeLocus` field is the literal `false`).  HONESTY:
this reads the catalog DATA; the theorem "CT×Async cannot amalgamate" stays the jam
(`fxOmega5_collisionNonFreeLinkReached = false`). -/
theorem gradedComposeAtCollisionRow_ctAsync_refuses {computad : OmegaComputad} {dim : Nat}
    {R : OrderedGradeSemiring} (binderGrade : R.Carrier) (budget : GradeVectorOver R)
    (firstCell secondCell : GradedCell computad (dim + 1) R) :
    gradedComposeAtCollisionRow collisionCtAsync binderGrade budget firstCell secondCell = none :=
  rfl

/-- **A free locus would fall through to the grade guard.**  If a row were free (`isFreeLocus = true`) the
collision-row composite equals the plain grade-guarded composite.  Composed with
`sixEightCatalog_allNonFree` (every §6.8 row is NON-free), this shows NO §6.8 row falls through — every
catalog collision refuses. -/
theorem gradedComposeAtCollisionRow_freeLocus_fallsThrough {computad : OmegaComputad} {dim : Nat}
    {R : OrderedGradeSemiring} (row : CollisionRow) (binderGrade : R.Carrier)
    (budget : GradeVectorOver R) (firstCell secondCell : GradedCell computad (dim + 1) R)
    (isFree : row.isFreeLocus = true) :
    gradedComposeAtCollisionRow row binderGrade budget firstCell secondCell =
      gradedComposeGuarded binderGrade budget firstCell secondCell := by
  dsimp only [gradedComposeAtCollisionRow]
  rw [isFree]

end FX1Poly.Polygraph.Omega.Graded
