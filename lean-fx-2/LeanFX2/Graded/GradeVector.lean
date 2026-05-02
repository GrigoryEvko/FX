import LeanFX2.Graded.Semiring

/-! # Graded/GradeVector — pointwise grade product

A `GradeVector dimensions` is a dependent record carrying one
grade per registered dimension.  Pointwise `+`, `*`, `≤` lift from
each dimension's `GradeSemiring`.

## Definition

```lean
def GradeVector (dimensions : List (Σ R, GradeSemiring R)) : Type :=
  ∀ (i : Fin dimensions.length), (dimensions.get i).1
```

Each position `i` carries the grade for dimension `i`.  Pointwise
ops use each position's typeclass instance.

## Pointwise operations

```lean
def GradeVector.add (g1 g2 : GradeVector dims) : GradeVector dims :=
  fun i => GradeSemiring.add (g1 i) (g2 i)

def GradeVector.mul (g1 g2 : GradeVector dims) : GradeVector dims :=
  fun i => GradeSemiring.mul (g1 i) (g2 i)

def GradeVector.le (g1 g2 : GradeVector dims) : Prop :=
  ∀ i, GradeSemiring.le (g1 i) (g2 i)

def GradeVector.zero : GradeVector dims :=
  fun i => GradeSemiring.zero
```

## The 19 registered dimensions (per fx_design.md §6.3)

The registered dimensions list determines the grade vector's shape.
For lean-fx-2 v0.1:
* `Usage : {0, 1, ω}`
* `Effect : (set of effect labels, ⊆)`
* `Security : {unclassified, classified}`

Future versions add: Protocol, Lifetime, Provenance, Trust, Repr,
Observability, Clock, Complexity, Precision, Space, Overflow, FP order,
Mutation, Reentrancy, Size, Version.

## Decidable equality + comparison

When all dimension semirings are decidable, `GradeVector.le` is
decidable position-by-position.  Used by elab/checker for grade
sub-typing.

## Dependencies

* `Graded/Semiring.lean`

## Downstream

* `Graded/Ctx.lean` — Ctx bindings carry GradeVector
* `Graded/Rules.lean` — typing rules use GradeVector arithmetic

## Implementation plan (Phase 8)

1. Define GradeVector as dep function type
2. Define pointwise ops + lawfulness in terms of per-position laws
3. Smoke: 0-dim and 1-dim trivial vectors

Target: ~100 lines.
-/

namespace LeanFX2.Graded

-- TODO Phase 8: GradeVector dep function type
-- TODO Phase 8: pointwise add/mul/le/zero
-- TODO Phase 8: per-position lawfulness lifted to vector level

end LeanFX2.Graded
