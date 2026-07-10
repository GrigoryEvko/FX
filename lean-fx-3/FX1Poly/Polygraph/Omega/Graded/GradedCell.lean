import FX1Poly.Polygraph.Omega.Carrier
import FX1Poly.Dimensions.Graded.GradeVectorGeneric

/-! # Polygraph/Omega/Graded/GradedCell — the semiring-parameterized graded cell + the composition
arithmetic (OMEGA-5 r1, B1)

The graded rung of the omega staircase: attach a §6.1 grade vector to an omega-cell.  The prime
directive (POLY-TAB: **never a new carrier**; OMEGA-1: **extrinsic beats intrinsic**) forces the
design — the grade is a DECORATION, exactly as globularity is an extrinsic `Prop`/`Bool` and never an
index.  So a graded cell is the EXTRINSIC PRODUCT of the shipped free-cell carrier and the shipped
generic grade vector, fused by nothing more than `×`:

    GradedCell computad dim R := CellExpr computad dim × GradeVectorOver R

`CellExpr` (`Carrier.lean`) is the dimension-indexed free omega-cell carrier; `GradeVectorOver R`
(`GradeVectorGeneric.lean`) is the flat cons-list grade vector generic over any ordered semiring `R`
(the grade analogue of `SteinerCell = List Int`).  Pairing them adds no inductive, no new constructor
set, no index — the candidate-i mistake (baking the grade into a new cell inductive) is refused one
layer up.

## The composition arithmetic (anchored on the §6.1/§6.2 App rule)

Two composites, both built from the shipped semimodule ops `GradeVectorOver.add` / `GradeVectorOver.scale`:

  * **Sequential composition** (the App rule `p1 + r · p2`, §6.2; vcomp ALONG a fed boundary) = MULTIPLY
    then ADD: `gradeCompose r p q := add p (scale r q)`.  The argument grade `q` is SCALED by the binder
    grade `r` (the `*`), then ADDED to the function grade `p` (the `+`) — `p1 + r·p2` verbatim.
  * **Parallel composition** (context split §7.7; whisker of INDEPENDENT cells) = ADD only:
    `gradeComposePar p q := add p q`, no scaling.

`gradedVcomp` / `gradedWhiskerLeft` / `gradedWhiskerRight` combine two graded cells: the CELL via
`CellExpr.vcomp` / `CellExpr.whiskerLeft` / `CellExpr.whiskerRight`, the GRADE via `gradeCompose`
(sequential) / `gradeComposePar` (parallel).  The whole graded-vcomp algebra is DEFINED here; the
associativity / distributivity that make it well-behaved are the shipped `GradeVectorOver` semimodule
laws (`scale_add` / `scale_scale` / `add_assoc`), so no new law is proven this round — r1 recognizes an
existing formula, it does not reconstruct one.  The identification of this arithmetic with the KERNEL
App rule is the anchor theorem (`GradedAppAnchor.lean`, B2); the grade-side enriched functor is the seed
(`EnrichedCheckSeed.lean`, B3).

The grade law `add p (scale r q)` mentions no dimension index `k` — it is dimension/k-uniform (the
App/object composite is `*_0`, but the arithmetic is the same at every codimension).

## Zero-axiom verification

`GradedCell` is a plain `×`; `gradeCompose` / `gradeComposePar` / the graded composites are `def`s over
the shipped structural ops; the non-vacuity witnesses compute (`UsageGrade` is a finite structural
enumeration, so the composites are defeq their concrete literals — closed by `rfl`).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega.Graded

open FX1Poly.Modal

/-! ## The graded cell — the extrinsic product -/

/-- A **graded cell**: a `dim`-cell over `computad` decorated with a §6.1 grade vector over the ordered
semiring `R`.  The EXTRINSIC PRODUCT `CellExpr computad dim × GradeVectorOver R` — the grade is a
decoration, never an index (POLY-TAB: never a new carrier). -/
def GradedCell (computad : OmegaComputad) (dim : Nat) (R : OrderedGradeSemiring) : Type :=
  CellExpr computad dim × GradeVectorOver R

/-- The underlying free omega-cell of a graded cell (the first projection). -/
def GradedCell.underlyingCell {computad : OmegaComputad} {dim : Nat} {R : OrderedGradeSemiring}
    (gradedCell : GradedCell computad dim R) : CellExpr computad dim :=
  gradedCell.1

/-- The grade vector decorating a graded cell (the second projection). -/
def GradedCell.gradeVector {computad : OmegaComputad} {dim : Nat} {R : OrderedGradeSemiring}
    (gradedCell : GradedCell computad dim R) : GradeVectorOver R :=
  gradedCell.2

/-! ## The composition arithmetic -/

/-- **Sequential graded composition** — the App rule `p1 + r · p2` (§6.2): scale the argument grade
`argumentGrades` by the binder grade `binderGrade`, then add the function grade `functionGrades`.  This
is the grade law of the KERNEL App constructor (`GradedAppAnchor.lean` proves the identity by `rfl`). -/
def gradeCompose {R : OrderedGradeSemiring} (binderGrade : R.Carrier)
    (functionGrades argumentGrades : GradeVectorOver R) : GradeVectorOver R :=
  GradeVectorOver.add functionGrades (GradeVectorOver.scale binderGrade argumentGrades)

/-- **Parallel graded composition** — context split (§7.7) / whisker of INDEPENDENT cells: add the two
grade vectors, no scaling. -/
def gradeComposePar {R : OrderedGradeSemiring} (leftGrades rightGrades : GradeVectorOver R) :
    GradeVectorOver R :=
  GradeVectorOver.add leftGrades rightGrades

/-- **Graded vertical composition**: the cell via `CellExpr.vcomp`, the grade via the SEQUENTIAL
`gradeCompose` (vcomp composes along a fed boundary — the App rule reading). -/
def gradedVcomp {computad : OmegaComputad} {dim : Nat} {R : OrderedGradeSemiring}
    (binderGrade : R.Carrier) (firstCell secondCell : GradedCell computad (dim + 1) R) :
    GradedCell computad (dim + 1) R :=
  (CellExpr.vcomp firstCell.1 secondCell.1, gradeCompose binderGrade firstCell.2 secondCell.2)

/-- **Graded left whiskering**: the cell via `CellExpr.whiskerLeft`, the grade via the PARALLEL
`gradeComposePar` (whiskering by an independent cell). -/
def gradedWhiskerLeft {computad : OmegaComputad} {dim : Nat} {R : OrderedGradeSemiring}
    (whiskering : GradedCell computad (dim + 1) R) (target : GradedCell computad (dim + 2) R) :
    GradedCell computad (dim + 2) R :=
  (CellExpr.whiskerLeft whiskering.1 target.1, gradeComposePar whiskering.2 target.2)

/-- **Graded right whiskering**: the cell via `CellExpr.whiskerRight`, the grade via the PARALLEL
`gradeComposePar`. -/
def gradedWhiskerRight {computad : OmegaComputad} {dim : Nat} {R : OrderedGradeSemiring}
    (target : GradedCell computad (dim + 2) R) (whiskering : GradedCell computad (dim + 1) R) :
    GradedCell computad (dim + 2) R :=
  (CellExpr.whiskerRight target.1 whiskering.1, gradeComposePar target.2 whiskering.2)

/-! ## Non-vacuity — the arithmetic COMPUTES (usage semiring `{0,1,ω}`) -/

/-- Sequential composition of the applied-identity grades computes to `[z ↦ 1]`: `gradeCompose 1 [0] [1]
= [0 + 1·1] = [1]`.  The `(λx. x) z` App grade at usage. -/
theorem gradeCompose_usageIdentity_computes :
    gradeCompose (R := fxUsageSemiring) UsageGrade.one
        (GradeVectorOver.cons UsageGrade.zero GradeVectorOver.nil)
        (GradeVectorOver.cons UsageGrade.one GradeVectorOver.nil) =
      GradeVectorOver.cons UsageGrade.one GradeVectorOver.nil :=
  rfl

/-- **The decisive `r = ω` case** computes to `[z ↦ ω, g ↦ 1]`: `gradeCompose ω [0, 1] [1, 0]
= [0 + ω·1, 1 + ω·0] = [ω, 1]`.  This is the App grade of the ω-scaling redex `(λx. (g x) x) z` — it
would FAIL if sequential composition used `+`-only or scale-by-1 instead of the correct `p + r·q`. -/
theorem gradeCompose_usageOmega_computes :
    gradeCompose (R := fxUsageSemiring) UsageGrade.omega
        (GradeVectorOver.cons UsageGrade.zero (GradeVectorOver.cons UsageGrade.one GradeVectorOver.nil))
        (GradeVectorOver.cons UsageGrade.one (GradeVectorOver.cons UsageGrade.zero GradeVectorOver.nil)) =
      GradeVectorOver.cons UsageGrade.omega (GradeVectorOver.cons UsageGrade.one GradeVectorOver.nil) :=
  rfl

/-- Parallel composition of two linear grades saturates: `gradeComposePar [1] [1] = [1 + 1] = [ω]` —
the §7.7 context-split fact (a linear binding used in two parallel positions becomes unrestricted). -/
theorem gradeComposePar_usageLinearSplit_computes :
    gradeComposePar (R := fxUsageSemiring)
        (GradeVectorOver.cons UsageGrade.one GradeVectorOver.nil)
        (GradeVectorOver.cons UsageGrade.one GradeVectorOver.nil) =
      GradeVectorOver.cons UsageGrade.omega GradeVectorOver.nil :=
  rfl

/-! ## Non-vacuity — a concrete graded vcomp of dim-3 usage-graded cells -/

/-- A trivial demonstrator computad: one mode, one label per dimension. -/
def demoComputad : OmegaComputad where
  modeCarrier := Unit
  genLabel := fun _ => Unit

/-- A concrete dim-3 cell over `demoComputad`: the triple identity on the base object. -/
def demoCellThree : CellExpr demoComputad 3 :=
  CellExpr.id (CellExpr.id (CellExpr.id (CellExpr.ofMode ())))

/-- A concrete usage-graded dim-3 cell: `demoCellThree` decorated with the linear grade `[1]`. -/
def demoGradedCellThree : GradedCell demoComputad 3 fxUsageSemiring :=
  (demoCellThree, GradeVectorOver.cons UsageGrade.one GradeVectorOver.nil)

/-- The graded vcomp of `demoGradedCellThree` with itself produces the composite CELL `vcomp c c`. -/
theorem demoGradedVcomp_cellComputes :
    (gradedVcomp (R := fxUsageSemiring) (dim := 2) UsageGrade.one
        demoGradedCellThree demoGradedCellThree).underlyingCell =
      CellExpr.vcomp demoCellThree demoCellThree :=
  rfl

/-- The graded vcomp of `demoGradedCellThree` with itself produces the composite GRADE `[ω]`
(`gradeCompose 1 [1] [1] = [1 + 1·1] = [ω]`) — both the cell and its grade are computed by one datum. -/
theorem demoGradedVcomp_gradeComputes :
    (gradedVcomp (R := fxUsageSemiring) (dim := 2) UsageGrade.one
        demoGradedCellThree demoGradedCellThree).gradeVector =
      GradeVectorOver.cons UsageGrade.omega GradeVectorOver.nil :=
  rfl

end FX1Poly.Polygraph.Omega.Graded
