import LeanFX2.Graded.GradeVector
import LeanFX2.Foundation.Context

/-! # Graded/Ctx — graded contexts

`GradedCtx` extends `Ctx` with one `GradeVector` per binding,
recording the (entire 19-dim) grade vector for each variable.

## Definition

```lean
structure GradedBinding (level scope : Nat) (dimensions : ...) where
  ty    : Ty level scope
  grade : GradeVector dimensions

def GradedCtx (mode : Mode) (level scope : Nat) (dimensions : ...) : Type :=
  -- a sequence of GradedBindings, one per scope position
  ...
```

## Context division `Γ / p`

The Wood/Atkey corrected lambda rule uses **context division**:
divide every binding's grade vector by `p`.  Per `fx_design.md`
§6.2: `pi/p = max { d : d * p ≤ pi }`.

```lean
def GradedCtx.div (Γ : GradedCtx ...) (p : GradeVector dims) : GradedCtx ... := ...
```

For usage semiring's `1/ω = 0`: when constructing replicable
closure (lambda with grade ω), every linearly-graded binding in
the captured context becomes erased (grade 0).  This rejects:

```lean
fn higher_order(f: i64 -> i64) : i64 -> i64
  = fn(x) => f(f(x))   -- f has grade 1, but lambda has grade ω
                       --   so f's available grade in body = 1/ω = 0
                       --   → f cannot be used → REJECTED
```

This is the Atkey 2018 / Wood-Atkey 2022 distinction (lean-fx
memory `feedback_lean_zero_axiom_match.md` notes the witness).

## Pointwise grade addition

Sequential composition of operations adds grades:

```lean
def GradedCtx.add (Γ1 Γ2 : GradedCtx ...) : GradedCtx ... := ...
```

When checking `e1; e2`, `Γ.add (cost e1) (cost e2)` accumulates
both costs.  Grade arithmetic on vectors is pointwise per
`Graded/GradeVector.lean`.

## Dependencies

* `Graded/GradeVector.lean`
* `Foundation/Context.lean` — base Ctx structure

## Downstream

* `Graded/Rules.lean` — typing rules use GradedCtx
* `Term.lean` (graded variant or extension) — Term over GradedCtx

## Implementation plan (Phase 8)

1. Define `GradedBinding` and `GradedCtx`
2. Define context division `Γ / p` per Wood-Atkey
3. Define pointwise context addition for sequential composition
4. Decidable equality / sub-typing on GradedCtx

Target: ~200 lines.
-/

namespace LeanFX2.Graded

-- TODO Phase 8: GradedBinding and GradedCtx structures
-- TODO Phase 8: context division `Γ / p`
-- TODO Phase 8: pointwise addition

end LeanFX2.Graded
